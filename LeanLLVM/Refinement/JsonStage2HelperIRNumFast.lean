/-
`num_fast_el1`'s emitted body, pinned at every block: the AST the fixture parses
to, the two hundred and fifty-five blocks `findBlock` resolves, and the fourteen
instruction lists the loop and the straight-line runs read.

`JsonStage2HelperIR` pins this body *by shape*: the parsed block count, the
instruction count, the parameter count, and the two strip rewrites `numFastSrc`
carries.  A shape pin does not say what any block holds, so a run placed against
it could only be written from the text by hand — which is the transcription this
module removes.  The pins below are **generated from the parse**, not copied
from the fixture: `capture-stage2-helpers.sh --emit-pins` parses
`stage2.helper.num_fast_el1.ll` under `numFastLayout` and prints the block
literals, the instruction lists and the `findBlock` equations, in the spelling
this module uses.  The whole body literal (`numFastBody`) and the fourteen
instruction lists are that output; the `#guard` beneath the literal is what holds
the two together, so a regeneration that drifts from the fixture fails the build
rather than pinning a body the text no longer has.

**The controls.**  A pin is worth the discrimination it shows.  Four here:

* the same bytes parsed under a *different* declared struct extent are not this
  body (`numFastSrc` is refused with no layout at all, which
  `JsonStage2HelperIR` pins; 1 572 bytes parses and is not `numFastBody`), so the
  1 568-byte extent is load-bearing rather than decorative;
* one immediate changed in the text still parses and is not `numFastBody`;
* a block name the sibling `s2_string_body` has and this body does not resolves
  to `none`;
* two of the body's own blocks are distinct, so `findBlock` is a lookup and not a
  constant function.

**What the pins are for.**  The runs and the scan's `BoundLoop` in
`JsonStage2NumFastBody` rewrite with the `*Instrs_eq` theorems below (a
`findBlock` equation projected to its instruction list), exactly as the sibling
bodies' steps do; every other block keeps its literal inside its `findBlock`
equation, so the whole body is pinned without a second copy of the text.

Two facts about the body that the pin makes checkable rather than assertable:
its `alloca %struct.Stk` is `Ty.struct "Stk" 1568` (the layout the pin supplies,
the number the body's own lifetime marker names), and its two globals
(`@NUMF_EL1_P10`, `@NUMF_EL1_POW10`) and two counter words (`@g_nume1_el`,
`@g_nume1_slow`) are `Operand.global` in the parse — the operand form is read
from a staged `Globals` assignment, not from the text.  The conversion path that
touches them is outside this module's proof; see `JsonStage2NumFastBody`'s header
for what is and is not closed.
-/
import LeanLLVM.Refinement.JsonStage2HelperIR

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM

/- The pins are `decide`s on closed literals; the reducer's default depth is set
below what the longest block's comparison needs, so it is raised here rather than
per theorem. -/
set_option maxRecDepth 20000

/-! ### The body, as the fixture parses

The literal is the parser's own result, printed by
`capture-stage2-helpers.sh --emit-pins`; the `#guard` asserts that parsing the
fixture under the declared layout returns exactly it.  A `#guard` rather than an
`rfl` proposition because the parser runs on `String` primitives, which the
kernel does not reduce. -/

/-- `@num_fast_el1`, as `probes/install/ir/stage2.helper.num_fast_el1.ll`
parses under `numFastLayout`. -/
def numFastBody : Function :=
{ name := "num_fast_el1",
  retTy := (Ty.int 32),
  params := [("%p", Ty.ptr),
             ("%n", (Ty.int 64)),
             ("%out", Ty.ptr),
             ("%err", Ty.ptr)],
  blocks := [
    { name := "entry",
      instrs := [
        Instr.alloca "%dig.i.i" (Ty.array 768 (Ty.int 8)) 0,
        Instr.alloca "%v.i.i" (Ty.struct "Stk" 1568) 0,
        Instr.alloca "%v8" (Ty.int 32) 0,
        Instr.alloca "%v8101" (Ty.int 32) 0,
        Instr.alloca "%d269" Ty.double 0,
        Instr.icmp "%cmp.not" (IPred.eq) 64 (Operand.reg "%n") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%cmp.not") "if.end" "land.lhs.true" },
    { name := "land.lhs.true",
      instrs := [
        Instr.load "%0" (Ty.int 8) (Operand.reg "%p"),
        Instr.icmp "%cmp1" (IPred.ne) 8 (Operand.reg "%0") (Operand.imm (Const.int 8 0x2d#8)),
        Instr.binop "%not.cmp1" (BinOp.xor) 1 (Operand.reg "%cmp1") (Operand.imm (Const.int 1 0x1#1)),
        Instr.zext "%spec.select439" 1 64 (Operand.reg "%not.cmp1")
      ],
      term := Term.br "if.end" },
    { name := "if.end",
      instrs := [
        Instr.phi "%tobool274.not" (Ty.int 1) [("entry", (Operand.imm (Const.int 1 0x1#1))),
                                       ("land.lhs.true", (Operand.reg "%cmp1"))],
        Instr.phi "%i.0" (Ty.int 64) [("entry", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("land.lhs.true", (Operand.reg "%spec.select439"))],
        Instr.icmp "%cmp3.not" (IPred.ult) 64 (Operand.reg "%i.0") (Operand.reg "%n")
      ],
      term := Term.condbr (Operand.reg "%cmp3.not") "if.end6" "if.then5" },
    { name := "if.then5",
      instrs := [
        Instr.store (Ty.int 64) (Operand.reg "%i.0") (Operand.reg "%err")
      ],
      term := Term.br "cleanup300" },
    { name := "if.end6",
      instrs := [
        Instr.gep "%arrayidx7" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.0"),
        Instr.load "%1" (Ty.int 8) (Operand.reg "%arrayidx7"),
        Instr.icmp "%cmp9" (IPred.eq) 8 (Operand.reg "%1") (Operand.imm (Const.int 8 0x30#8))
      ],
      term := Term.condbr (Operand.reg "%cmp9") "if.then11" "if.else" },
    { name := "if.then11",
      instrs := [
        Instr.binop "%inc12" (BinOp.add) 64 (Operand.reg "%i.0") (Operand.imm (Const.int 64 0x0000000000000001#64))
      ],
      term := Term.br "if.end68" },
    { name := "if.else",
      instrs := [
        Instr.binop "%2" (BinOp.add) 8 (Operand.reg "%1") (Operand.imm (Const.int 8 0xcf#8)),
        Instr.icmp "%or.cond" (IPred.ult) 8 (Operand.reg "%2") (Operand.imm (Const.int 8 0x09#8))
      ],
      term := Term.condbr (Operand.reg "%or.cond") "if.then22" "if.else66" },
    { name := "if.then22",
      instrs := [
        Instr.binop "%3" (BinOp.and) 8 (Operand.reg "%1") (Operand.imm (Const.int 8 0x0f#8)),
        Instr.zext "%conv25" 8 64 (Operand.reg "%3"),
        Instr.binop "%inc26" (BinOp.add) 64 (Operand.reg "%i.0") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.binop "%add563" (BinOp.add) 64 (Operand.reg "%i.0") (Operand.imm (Const.int 64 0x0000000000000009#64)),
        Instr.icmp "%cmp27564.not" (IPred.ugt) 64 (Operand.reg "%add563") (Operand.reg "%n")
      ],
      term := Term.condbr (Operand.reg "%cmp27564.not") "while.end" "while.body.preheader" },
    { name := "while.body.preheader",
      instrs := [
        Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
                             (Ty.ptr, (Operand.reg "%v8"))],
        Instr.gep "%add.ptr930" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%inc26"),
        Instr.call "%call931" (Ty.int 32) "num_d8_el1" [(Ty.ptr, (Operand.reg "%add.ptr930")),
                             (Ty.ptr, (Operand.reg "%v8"))],
        Instr.icmp "%tobool.not932" (IPred.eq) 32 (Operand.reg "%call931") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%tobool.not932") "cleanup.thread" "cleanup" },
    { name := "while.body",
      instrs := [
        Instr.binop "%add29" (BinOp.add) 64 (Operand.reg "%add29569933") (Operand.imm (Const.int 64 0x0000000000000008#64)),
        Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
                             (Ty.ptr, (Operand.reg "%v8"))],
        Instr.gep "%add.ptr" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%add568934"),
        Instr.call "%call" (Ty.int 32) "num_d8_el1" [(Ty.ptr, (Operand.reg "%add.ptr")),
                             (Ty.ptr, (Operand.reg "%v8"))],
        Instr.icmp "%tobool.not" (IPred.eq) 32 (Operand.reg "%call") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%tobool.not") "cleanup.thread" "cleanup" },
    { name := "cleanup.thread",
      instrs := [
        Instr.phi "%i.1567.lcssa" (Ty.int 64) [("while.body.preheader", (Operand.reg "%inc26")),
                                       ("while.body", (Operand.reg "%add568934"))],
        Instr.phi "%idig.0566.lcssa" (Ty.int 64) [("while.body.preheader", (Operand.imm (Const.int 64 0x0000000000000001#64))),
                                       ("while.body", (Operand.reg "%add29569933"))],
        Instr.phi "%ip.0565.lcssa" (Ty.int 64) [("while.body.preheader", (Operand.reg "%conv25")),
                                       ("while.body", (Operand.reg "%add35"))],
        Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
                             (Ty.ptr, (Operand.reg "%v8"))]
      ],
      term := Term.br "while.end" },
    { name := "cleanup",
      instrs := [
        Instr.phi "%ip.0565935" (Ty.int 64) [("while.body", (Operand.reg "%add35")),
                                       ("while.body.preheader", (Operand.reg "%conv25"))],
        Instr.phi "%add568934" (Ty.int 64) [("while.body", (Operand.reg "%add")),
                                       ("while.body.preheader", (Operand.reg "%add563"))],
        Instr.phi "%add29569933" (Ty.int 64) [("while.body", (Operand.reg "%add29")),
                                       ("while.body.preheader", (Operand.imm (Const.int 64 0x0000000000000009#64)))],
        Instr.binop "%mul" (BinOp.mul) 64 (Operand.reg "%ip.0565935") (Operand.imm (Const.int 64 0x0000000005f5e100#64)),
        Instr.load "%4" (Ty.int 32) (Operand.reg "%v8"),
        Instr.zext "%conv34" 32 64 (Operand.reg "%4"),
        Instr.binop "%add35" (BinOp.add) 64 (Operand.reg "%mul") (Operand.reg "%conv34"),
        Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
                             (Ty.ptr, (Operand.reg "%v8"))],
        Instr.binop "%add" (BinOp.add) 64 (Operand.reg "%add568934") (Operand.imm (Const.int 64 0x0000000000000008#64)),
        Instr.icmp "%cmp27" (IPred.ule) 64 (Operand.reg "%add") (Operand.reg "%n"),
        Instr.icmp "%cmp30" (IPred.ult) 64 (Operand.reg "%add29569933") (Operand.imm (Const.int 64 0x000000000000000c#64)),
        Instr.select "%5" (Ty.int 1) (Operand.reg "%cmp27") (Operand.reg "%cmp30") (Operand.imm (Const.int 1 0x0#1))
      ],
      term := Term.condbr (Operand.reg "%5") "while.body" "while.end" },
    { name := "while.end",
      instrs := [
        Instr.phi "%ip.0562" (Ty.int 64) [("cleanup.thread", (Operand.reg "%ip.0565.lcssa")),
                                       ("if.then22", (Operand.reg "%conv25")),
                                       ("cleanup", (Operand.reg "%add35"))],
        Instr.phi "%idig.0560" (Ty.int 64) [("cleanup.thread", (Operand.reg "%idig.0566.lcssa")),
                                       ("if.then22", (Operand.imm (Const.int 64 0x0000000000000001#64))),
                                       ("cleanup", (Operand.reg "%add29569933"))],
        Instr.phi "%i.1558" (Ty.int 64) [("cleanup.thread", (Operand.reg "%i.1567.lcssa")),
                                       ("if.then22", (Operand.reg "%inc26")),
                                       ("cleanup", (Operand.reg "%add568934"))],
        Instr.icmp "%cmp39572" (IPred.ult) 64 (Operand.reg "%i.1558") (Operand.reg "%n")
      ],
      term := Term.condbr (Operand.reg "%cmp39572") "land.lhs.true41.preheader" "if.end68" },
    { name := "land.lhs.true41.preheader",
      instrs := [
        Instr.binop "%6" (BinOp.add) 64 (Operand.reg "%idig.0560") (Operand.reg "%n"),
        Instr.binop "%7" (BinOp.sub) 64 (Operand.reg "%6") (Operand.reg "%i.1558")
      ],
      term := Term.br "land.lhs.true41" },
    { name := "land.lhs.true41",
      instrs := [
        Instr.phi "%i.4575" (Ty.int 64) [("if.end62", (Operand.reg "%inc64")),
                                       ("land.lhs.true41.preheader", (Operand.reg "%i.1558"))],
        Instr.phi "%idig.3574" (Ty.int 64) [("if.end62", (Operand.reg "%inc63")),
                                       ("land.lhs.true41.preheader", (Operand.reg "%idig.0560"))],
        Instr.phi "%ip.3573" (Ty.int 64) [("if.end62", (Operand.reg "%ip.4")),
                                       ("land.lhs.true41.preheader", (Operand.reg "%ip.0562"))],
        Instr.gep "%arrayidx42" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.4575"),
        Instr.load "%8" (Ty.int 8) (Operand.reg "%arrayidx42"),
        Instr.binop "%9" (BinOp.add) 8 (Operand.reg "%8") (Operand.imm (Const.int 8 0xd0#8)),
        Instr.icmp "%or.cond440" (IPred.ult) 8 (Operand.reg "%9") (Operand.imm (Const.int 8 0x0a#8))
      ],
      term := Term.condbr (Operand.reg "%or.cond440") "while.body52" "if.end68" },
    { name := "while.body52",
      instrs := [
        Instr.icmp "%cmp53" (IPred.ult) 64 (Operand.reg "%idig.3574") (Operand.imm (Const.int 64 0x0000000000000013#64))
      ],
      term := Term.condbr (Operand.reg "%cmp53") "if.then55" "if.end62" },
    { name := "if.then55",
      instrs := [
        Instr.binop "%mul56" (BinOp.mul) 64 (Operand.reg "%ip.3573") (Operand.imm (Const.int 64 0x000000000000000a#64)),
        Instr.binop "%10" (BinOp.and) 8 (Operand.reg "%8") (Operand.imm (Const.int 8 0x0f#8)),
        Instr.zext "%conv60" 8 64 (Operand.reg "%10"),
        Instr.binop "%add61" (BinOp.add) 64 (Operand.reg "%mul56") (Operand.reg "%conv60")
      ],
      term := Term.br "if.end62" },
    { name := "if.end62",
      instrs := [
        Instr.phi "%ip.4" (Ty.int 64) [("if.then55", (Operand.reg "%add61")),
                                       ("while.body52", (Operand.reg "%ip.3573"))],
        Instr.binop "%inc63" (BinOp.add) 64 (Operand.reg "%idig.3574") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.binop "%inc64" (BinOp.add) 64 (Operand.reg "%i.4575") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%exitcond.not" (IPred.eq) 64 (Operand.reg "%inc64") (Operand.reg "%n")
      ],
      term := Term.condbr (Operand.reg "%exitcond.not") "if.end230" "land.lhs.true41" },
    { name := "if.else66",
      instrs := [
        Instr.store (Ty.int 64) (Operand.reg "%i.0") (Operand.reg "%err")
      ],
      term := Term.br "cleanup300" },
    { name := "if.end68",
      instrs := [
        Instr.phi "%ip.5" (Ty.int 64) [("if.then11", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("while.end", (Operand.reg "%ip.0562")),
                                       ("land.lhs.true41", (Operand.reg "%ip.3573"))],
        Instr.phi "%idig.4" (Ty.int 64) [("if.then11", (Operand.imm (Const.int 64 0x0000000000000001#64))),
                                       ("while.end", (Operand.reg "%idig.0560")),
                                       ("land.lhs.true41", (Operand.reg "%idig.3574"))],
        Instr.phi "%i.5" (Ty.int 64) [("if.then11", (Operand.reg "%inc12")),
                                       ("while.end", (Operand.reg "%i.1558")),
                                       ("land.lhs.true41", (Operand.reg "%i.4575"))],
        Instr.icmp "%cmp69" (IPred.ult) 64 (Operand.reg "%i.5") (Operand.reg "%n")
      ],
      term := Term.condbr (Operand.reg "%cmp69") "land.lhs.true71" "if.end144" },
    { name := "land.lhs.true71",
      instrs := [
        Instr.gep "%arrayidx72" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.5"),
        Instr.load "%11" (Ty.int 8) (Operand.reg "%arrayidx72"),
        Instr.icmp "%cmp74" (IPred.eq) 8 (Operand.reg "%11") (Operand.imm (Const.int 8 0x2e#8))
      ],
      term := Term.condbr (Operand.reg "%cmp74") "if.then76" "if.end144" },
    { name := "if.then76",
      instrs := [
        Instr.binop "%inc77" (BinOp.add) 64 (Operand.reg "%i.5") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%cmp78.not" (IPred.ult) 64 (Operand.reg "%inc77") (Operand.reg "%n")
      ],
      term := Term.condbr (Operand.reg "%cmp78.not") "lor.lhs.false" "if.then89" },
    { name := "lor.lhs.false",
      instrs := [
        Instr.gep "%arrayidx80" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%inc77"),
        Instr.load "%12" (Ty.int 8) (Operand.reg "%arrayidx80"),
        Instr.binop "%13" (BinOp.add) 8 (Operand.reg "%12") (Operand.imm (Const.int 8 0xc6#8)),
        Instr.icmp "%or.cond441" (IPred.ult) 8 (Operand.reg "%13") (Operand.imm (Const.int 8 0xf6#8))
      ],
      term := Term.condbr (Operand.reg "%or.cond441") "if.then89" "while.cond91.preheader" },
    { name := "while.cond91.preheader",
      instrs := [
        Instr.binop "%add92582" (BinOp.add) 64 (Operand.reg "%i.5") (Operand.imm (Const.int 64 0x0000000000000009#64)),
        Instr.icmp "%cmp93583.not" (IPred.ugt) 64 (Operand.reg "%add92582") (Operand.reg "%n")
      ],
      term := Term.condbr (Operand.reg "%cmp93583.not") "while.end115" "while.body100.preheader" },
    { name := "while.body100.preheader",
      instrs := [
        Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
                             (Ty.ptr, (Operand.reg "%v8101"))],
        Instr.gep "%add.ptr102938" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%inc77"),
        Instr.call "%call103939" (Ty.int 32) "num_d8_el1" [(Ty.ptr, (Operand.reg "%add.ptr102938")),
                             (Ty.ptr, (Operand.reg "%v8101"))],
        Instr.icmp "%tobool104.not940" (IPred.eq) 32 (Operand.reg "%call103939") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%tobool104.not940") "cleanup112.thread" "cleanup112" },
    { name := "if.then89",
      instrs := [
        Instr.store (Ty.int 64) (Operand.reg "%inc77") (Operand.reg "%err")
      ],
      term := Term.br "cleanup300" },
    { name := "while.body100",
      instrs := [
        Instr.binop "%add96" (BinOp.add) 64 (Operand.reg "%add96588941") (Operand.imm (Const.int 64 0x0000000000000008#64)),
        Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
                             (Ty.ptr, (Operand.reg "%v8101"))],
        Instr.gep "%add.ptr102" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%add92587942"),
        Instr.call "%call103" (Ty.int 32) "num_d8_el1" [(Ty.ptr, (Operand.reg "%add.ptr102")),
                             (Ty.ptr, (Operand.reg "%v8101"))],
        Instr.icmp "%tobool104.not" (IPred.eq) 32 (Operand.reg "%call103") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%tobool104.not") "cleanup112.thread" "cleanup112" },
    { name := "cleanup112.thread",
      instrs := [
        Instr.phi "%i.6586.lcssa" (Ty.int 64) [("while.body100.preheader", (Operand.reg "%inc77")),
                                       ("while.body100", (Operand.reg "%add92587942"))],
        Instr.phi "%fdig.0585.lcssa" (Ty.int 64) [("while.body100.preheader", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("while.body100", (Operand.reg "%add96588941"))],
        Instr.phi "%fr.0584.lcssa" (Ty.int 64) [("while.body100.preheader", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("while.body100", (Operand.reg "%add109"))],
        Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
                             (Ty.ptr, (Operand.reg "%v8101"))]
      ],
      term := Term.br "while.end115" },
    { name := "cleanup112",
      instrs := [
        Instr.phi "%fr.0584943" (Ty.int 64) [("while.body100", (Operand.reg "%add109")),
                                       ("while.body100.preheader", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.phi "%add92587942" (Ty.int 64) [("while.body100", (Operand.reg "%add92")),
                                       ("while.body100.preheader", (Operand.reg "%add92582"))],
        Instr.phi "%add96588941" (Ty.int 64) [("while.body100", (Operand.reg "%add96")),
                                       ("while.body100.preheader", (Operand.imm (Const.int 64 0x0000000000000008#64)))],
        Instr.binop "%mul107" (BinOp.mul) 64 (Operand.reg "%fr.0584943") (Operand.imm (Const.int 64 0x0000000005f5e100#64)),
        Instr.load "%14" (Ty.int 32) (Operand.reg "%v8101"),
        Instr.zext "%conv108" 32 64 (Operand.reg "%14"),
        Instr.binop "%add109" (BinOp.add) 64 (Operand.reg "%mul107") (Operand.reg "%conv108"),
        Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
                             (Ty.ptr, (Operand.reg "%v8101"))],
        Instr.binop "%add92" (BinOp.add) 64 (Operand.reg "%add92587942") (Operand.imm (Const.int 64 0x0000000000000008#64)),
        Instr.icmp "%cmp93" (IPred.ule) 64 (Operand.reg "%add92") (Operand.reg "%n"),
        Instr.icmp "%cmp97" (IPred.ult) 64 (Operand.reg "%add96588941") (Operand.imm (Const.int 64 0x000000000000000c#64)),
        Instr.select "%15" (Ty.int 1) (Operand.reg "%cmp93") (Operand.reg "%cmp97") (Operand.imm (Const.int 1 0x0#1))
      ],
      term := Term.condbr (Operand.reg "%15") "while.body100" "while.end115" },
    { name := "while.end115",
      instrs := [
        Instr.phi "%fr.0556" (Ty.int 64) [("cleanup112.thread", (Operand.reg "%fr.0584.lcssa")),
                                       ("while.cond91.preheader", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("cleanup112", (Operand.reg "%add109"))],
        Instr.phi "%fdig.0554" (Ty.int 64) [("cleanup112.thread", (Operand.reg "%fdig.0585.lcssa")),
                                       ("while.cond91.preheader", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("cleanup112", (Operand.reg "%add96588941"))],
        Instr.phi "%i.6552" (Ty.int 64) [("cleanup112.thread", (Operand.reg "%i.6586.lcssa")),
                                       ("while.cond91.preheader", (Operand.reg "%inc77")),
                                       ("cleanup112", (Operand.reg "%add92587942"))],
        Instr.icmp "%cmp117592" (IPred.ult) 64 (Operand.reg "%i.6552") (Operand.reg "%n")
      ],
      term := Term.condbr (Operand.reg "%cmp117592") "land.lhs.true119.preheader" "if.end144" },
    { name := "land.lhs.true119.preheader",
      instrs := [
        Instr.binop "%16" (BinOp.add) 64 (Operand.reg "%fdig.0554") (Operand.reg "%n"),
        Instr.binop "%17" (BinOp.sub) 64 (Operand.reg "%16") (Operand.reg "%i.6552")
      ],
      term := Term.br "land.lhs.true119" },
    { name := "land.lhs.true119",
      instrs := [
        Instr.phi "%i.9595" (Ty.int 64) [("if.end140", (Operand.reg "%inc142")),
                                       ("land.lhs.true119.preheader", (Operand.reg "%i.6552"))],
        Instr.phi "%fdig.3594" (Ty.int 64) [("if.end140", (Operand.reg "%inc141")),
                                       ("land.lhs.true119.preheader", (Operand.reg "%fdig.0554"))],
        Instr.phi "%fr.3593" (Ty.int 64) [("if.end140", (Operand.reg "%fr.4")),
                                       ("land.lhs.true119.preheader", (Operand.reg "%fr.0556"))],
        Instr.gep "%arrayidx120" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.9595"),
        Instr.load "%18" (Ty.int 8) (Operand.reg "%arrayidx120"),
        Instr.binop "%19" (BinOp.add) 8 (Operand.reg "%18") (Operand.imm (Const.int 8 0xd0#8)),
        Instr.icmp "%or.cond443" (IPred.ult) 8 (Operand.reg "%19") (Operand.imm (Const.int 8 0x0a#8))
      ],
      term := Term.condbr (Operand.reg "%or.cond443") "while.body130" "if.end144" },
    { name := "while.body130",
      instrs := [
        Instr.icmp "%cmp131" (IPred.ult) 64 (Operand.reg "%fdig.3594") (Operand.imm (Const.int 64 0x0000000000000013#64))
      ],
      term := Term.condbr (Operand.reg "%cmp131") "if.then133" "if.end140" },
    { name := "if.then133",
      instrs := [
        Instr.binop "%mul134" (BinOp.mul) 64 (Operand.reg "%fr.3593") (Operand.imm (Const.int 64 0x000000000000000a#64)),
        Instr.binop "%20" (BinOp.and) 8 (Operand.reg "%18") (Operand.imm (Const.int 8 0x0f#8)),
        Instr.zext "%conv138" 8 64 (Operand.reg "%20"),
        Instr.binop "%add139" (BinOp.add) 64 (Operand.reg "%mul134") (Operand.reg "%conv138")
      ],
      term := Term.br "if.end140" },
    { name := "if.end140",
      instrs := [
        Instr.phi "%fr.4" (Ty.int 64) [("if.then133", (Operand.reg "%add139")),
                                       ("while.body130", (Operand.reg "%fr.3593"))],
        Instr.binop "%inc141" (BinOp.add) 64 (Operand.reg "%fdig.3594") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.binop "%inc142" (BinOp.add) 64 (Operand.reg "%i.9595") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%exitcond702.not" (IPred.eq) 64 (Operand.reg "%inc142") (Operand.reg "%n")
      ],
      term := Term.condbr (Operand.reg "%exitcond702.not") "if.end230" "land.lhs.true119" },
    { name := "if.end144",
      instrs := [
        Instr.phi "%fr.5" (Ty.int 64) [("land.lhs.true71", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("if.end68", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("while.end115", (Operand.reg "%fr.0556")),
                                       ("land.lhs.true119", (Operand.reg "%fr.3593"))],
        Instr.phi "%fdig.4" (Ty.int 64) [("land.lhs.true71", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("if.end68", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("while.end115", (Operand.reg "%fdig.0554")),
                                       ("land.lhs.true119", (Operand.reg "%fdig.3594"))],
        Instr.phi "%i.10" (Ty.int 64) [("land.lhs.true71", (Operand.reg "%i.5")),
                                       ("if.end68", (Operand.reg "%i.5")),
                                       ("while.end115", (Operand.reg "%i.6552")),
                                       ("land.lhs.true119", (Operand.reg "%i.9595"))],
        Instr.icmp "%cmp145" (IPred.ult) 64 (Operand.reg "%i.10") (Operand.reg "%n")
      ],
      term := Term.condbr (Operand.reg "%cmp145") "land.lhs.true147" "if.end226" },
    { name := "land.lhs.true147",
      instrs := [
        Instr.gep "%arrayidx148" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.10"),
        Instr.load "%21" (Ty.int 8) (Operand.reg "%arrayidx148")
      ],
      term := Term.br "NodeBlock" },
    { name := "NodeBlock",
      instrs := [
        Instr.icmp "%Pivot" (IPred.slt) 8 (Operand.reg "%21") (Operand.imm (Const.int 8 0x65#8))
      ],
      term := Term.condbr (Operand.reg "%Pivot") "LeafBlock" "LeafBlock1" },
    { name := "LeafBlock1",
      instrs := [
        Instr.icmp "%SwitchLeaf2" (IPred.eq) 8 (Operand.reg "%21") (Operand.imm (Const.int 8 0x65#8))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf2") "if.then157" "if.end226" },
    { name := "LeafBlock",
      instrs := [
        Instr.icmp "%SwitchLeaf" (IPred.eq) 8 (Operand.reg "%21") (Operand.imm (Const.int 8 0x45#8))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf") "if.then157" "if.end226" },
    { name := "if.then157",
      instrs := [
        Instr.binop "%inc158" (BinOp.add) 64 (Operand.reg "%i.10") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%cmp159" (IPred.ult) 64 (Operand.reg "%inc158") (Operand.reg "%n")
      ],
      term := Term.condbr (Operand.reg "%cmp159") "land.lhs.true161" "if.end177" },
    { name := "land.lhs.true161",
      instrs := [
        Instr.gep "%arrayidx162" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%inc158"),
        Instr.load "%22" (Ty.int 8) (Operand.reg "%arrayidx162")
      ],
      term := Term.br "NodeBlock7" },
    { name := "NodeBlock7",
      instrs := [
        Instr.icmp "%Pivot8" (IPred.slt) 8 (Operand.reg "%22") (Operand.imm (Const.int 8 0x2d#8))
      ],
      term := Term.condbr (Operand.reg "%Pivot8") "LeafBlock3" "LeafBlock5" },
    { name := "LeafBlock5",
      instrs := [
        Instr.icmp "%SwitchLeaf6" (IPred.eq) 8 (Operand.reg "%22") (Operand.imm (Const.int 8 0x2d#8))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf6") "if.then171" "if.end177" },
    { name := "LeafBlock3",
      instrs := [
        Instr.icmp "%SwitchLeaf4" (IPred.eq) 8 (Operand.reg "%22") (Operand.imm (Const.int 8 0x2b#8))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf4") "if.then171" "if.end177" },
    { name := "if.then171",
      instrs := [
        Instr.icmp "%cmp174" (IPred.ne) 8 (Operand.reg "%22") (Operand.imm (Const.int 8 0x2d#8)),
        Instr.binop "%inc176" (BinOp.add) 64 (Operand.reg "%i.10") (Operand.imm (Const.int 64 0x0000000000000002#64))
      ],
      term := Term.br "if.end177" },
    { name := "if.end177",
      instrs := [
        Instr.phi "%esign.0" (Ty.int 1) [("if.then171", (Operand.reg "%cmp174")),
                                       ("if.then157", (Operand.imm (Const.int 1 0x1#1))),
                                       ("LeafBlock3", (Operand.imm (Const.int 1 0x1#1))),
                                       ("LeafBlock5", (Operand.imm (Const.int 1 0x1#1)))],
        Instr.phi "%i.11" (Ty.int 64) [("if.then171", (Operand.reg "%inc176")),
                                       ("if.then157", (Operand.reg "%inc158")),
                                       ("LeafBlock3", (Operand.reg "%inc158")),
                                       ("LeafBlock5", (Operand.reg "%inc158"))],
        Instr.icmp "%cmp178.not" (IPred.ult) 64 (Operand.reg "%i.11") (Operand.reg "%n")
      ],
      term := Term.condbr (Operand.reg "%cmp178.not") "lor.lhs.false180" "cleanup223" },
    { name := "lor.lhs.false180",
      instrs := [
        Instr.gep "%arrayidx181" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.11"),
        Instr.load "%23" (Ty.int 8) (Operand.reg "%arrayidx181"),
        Instr.binop "%24" (BinOp.add) 8 (Operand.reg "%23") (Operand.imm (Const.int 8 0xc6#8)),
        Instr.icmp "%or.cond444" (IPred.ult) 8 (Operand.reg "%24") (Operand.imm (Const.int 8 0xf6#8))
      ],
      term := Term.condbr (Operand.reg "%or.cond444") "cleanup223" "land.lhs.true195" },
    { name := "land.lhs.true195",
      instrs := [
        Instr.phi "%i.12604" (Ty.int 64) [("if.end216", (Operand.reg "%inc217")),
                                       ("lor.lhs.false180", (Operand.reg "%i.11"))],
        Instr.phi "%exp10.0603" (Ty.int 64) [("if.end216", (Operand.reg "%exp10.1")),
                                       ("lor.lhs.false180", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.gep "%arrayidx196" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.12604"),
        Instr.load "%25" (Ty.int 8) (Operand.reg "%arrayidx196"),
        Instr.binop "%26" (BinOp.add) 8 (Operand.reg "%25") (Operand.imm (Const.int 8 0xd0#8)),
        Instr.icmp "%or.cond445" (IPred.ult) 8 (Operand.reg "%26") (Operand.imm (Const.int 8 0x0a#8))
      ],
      term := Term.condbr (Operand.reg "%or.cond445") "while.body206" "cleanup223.thread" },
    { name := "while.body206",
      instrs := [
        Instr.icmp "%cmp207" (IPred.slt) 64 (Operand.reg "%exp10.0603") (Operand.imm (Const.int 64 0x00000000000186a0#64))
      ],
      term := Term.condbr (Operand.reg "%cmp207") "if.then209" "if.end216" },
    { name := "if.then209",
      instrs := [
        Instr.binop "%mul210" (BinOp.mul) 64 (Operand.reg "%exp10.0603") (Operand.imm (Const.int 64 0x000000000000000a#64)),
        Instr.binop "%27" (BinOp.and) 8 (Operand.reg "%25") (Operand.imm (Const.int 8 0x0f#8)),
        Instr.zext "%conv214" 8 64 (Operand.reg "%27"),
        Instr.binop "%add215" (BinOp.add) 64 (Operand.reg "%mul210") (Operand.reg "%conv214")
      ],
      term := Term.br "if.end216" },
    { name := "if.end216",
      instrs := [
        Instr.phi "%exp10.1" (Ty.int 64) [("if.then209", (Operand.reg "%add215")),
                                       ("while.body206", (Operand.reg "%exp10.0603"))],
        Instr.binop "%inc217" (BinOp.add) 64 (Operand.reg "%i.12604") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%exitcond703.not" (IPred.eq) 64 (Operand.reg "%inc217") (Operand.reg "%n")
      ],
      term := Term.condbr (Operand.reg "%exitcond703.not") "cleanup223.thread" "land.lhs.true195" },
    { name := "cleanup223.thread",
      instrs := [
        Instr.phi "%exp10.0.lcssa.ph" (Ty.int 64) [("land.lhs.true195", (Operand.reg "%exp10.0603")),
                                       ("if.end216", (Operand.reg "%exp10.1"))],
        Instr.phi "%i.12.lcssa.ph" (Ty.int 64) [("land.lhs.true195", (Operand.reg "%i.12604")),
                                       ("if.end216", (Operand.reg "%n"))],
        Instr.binop "%sub221" (BinOp.sub) 64 (Operand.imm (Const.int 64 0x0000000000000000#64)) (Operand.reg "%exp10.0.lcssa.ph"),
        Instr.select "%spec.select446" (Ty.int 64) (Operand.reg "%esign.0") (Operand.reg "%exp10.0.lcssa.ph") (Operand.reg "%sub221")
      ],
      term := Term.br "if.end226" },
    { name := "cleanup223",
      instrs := [
        Instr.store (Ty.int 64) (Operand.reg "%i.11") (Operand.reg "%err")
      ],
      term := Term.br "cleanup300" },
    { name := "if.end226",
      instrs := [
        Instr.phi "%exp10.4" (Ty.int 64) [("if.end144", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("cleanup223.thread", (Operand.reg "%spec.select446")),
                                       ("LeafBlock", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("LeafBlock1", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.phi "%i.14" (Ty.int 64) [("if.end144", (Operand.reg "%i.10")),
                                       ("cleanup223.thread", (Operand.reg "%i.12.lcssa.ph")),
                                       ("LeafBlock", (Operand.reg "%i.10")),
                                       ("LeafBlock1", (Operand.reg "%i.10"))],
        Instr.icmp "%cmp227.not" (IPred.eq) 64 (Operand.reg "%i.14") (Operand.reg "%n")
      ],
      term := Term.condbr (Operand.reg "%cmp227.not") "if.end230" "if.then229" },
    { name := "if.then229",
      instrs := [
        Instr.store (Ty.int 64) (Operand.reg "%i.14") (Operand.reg "%err")
      ],
      term := Term.br "cleanup300" },
    { name := "if.end230",
      instrs := [
        Instr.phi "%exp10.4731" (Ty.int 64) [("if.end226", (Operand.reg "%exp10.4")),
                                       ("if.end140", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("if.end62", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.phi "%idig.4709716730" (Ty.int 64) [("if.end226", (Operand.reg "%idig.4")),
                                       ("if.end140", (Operand.reg "%idig.4")),
                                       ("if.end62", (Operand.reg "%7"))],
        Instr.phi "%ip.5708717729" (Ty.int 64) [("if.end226", (Operand.reg "%ip.5")),
                                       ("if.end140", (Operand.reg "%ip.5")),
                                       ("if.end62", (Operand.reg "%ip.4"))],
        Instr.phi "%fr.5718728" (Ty.int 64) [("if.end226", (Operand.reg "%fr.5")),
                                       ("if.end140", (Operand.reg "%fr.4")),
                                       ("if.end62", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.phi "%fdig.4719727" (Ty.int 64) [("if.end226", (Operand.reg "%fdig.4")),
                                       ("if.end140", (Operand.reg "%17")),
                                       ("if.end62", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.binop "%sub231" (BinOp.sub) 64 (Operand.reg "%exp10.4731") (Operand.reg "%fdig.4719727"),
        Instr.binop "%add232" (BinOp.add) 64 (Operand.reg "%fdig.4719727") (Operand.reg "%idig.4709716730"),
        Instr.icmp "%cmp233" (IPred.ult) 64 (Operand.reg "%add232") (Operand.imm (Const.int 64 0x0000000000000014#64)),
        Instr.binop "%28" (BinOp.add) 64 (Operand.reg "%sub231") (Operand.imm (Const.int 64 0x000000000000002d#64)),
        Instr.icmp "%29" (IPred.ult) 64 (Operand.reg "%28") (Operand.imm (Const.int 64 0x000000000000005b#64)),
        Instr.select "%or.cond304" (Ty.int 1) (Operand.reg "%cmp233") (Operand.reg "%29") (Operand.imm (Const.int 1 0x0#1))
      ],
      term := Term.condbr (Operand.reg "%or.cond304") "if.then241" "if.end285" },
    { name := "if.then241",
      instrs := [
        Instr.gep "%arrayidx242" (Ty.int 64) (Operand.global "@NUMF_EL1_P10") (Operand.reg "%fdig.4719727"),
        Instr.load "%30" (Ty.int 64) (Operand.reg "%arrayidx242"),
        Instr.binop "%mul243" (BinOp.mul) 64 (Operand.reg "%30") (Operand.reg "%ip.5708717729"),
        Instr.binop "%add244" (BinOp.add) 64 (Operand.reg "%mul243") (Operand.reg "%fr.5718728"),
        Instr.icmp "%cmp245" (IPred.ult) 64 (Operand.reg "%add232") (Operand.imm (Const.int 64 0x0000000000000010#64)),
        Instr.binop "%31" (BinOp.add) 64 (Operand.reg "%sub231") (Operand.imm (Const.int 64 0x0000000000000016#64)),
        Instr.icmp "%32" (IPred.ult) 64 (Operand.reg "%31") (Operand.imm (Const.int 64 0x000000000000002d#64)),
        Instr.select "%or.cond306" (Ty.int 1) (Operand.reg "%cmp245") (Operand.reg "%32") (Operand.imm (Const.int 1 0x0#1))
      ],
      term := Term.condbr (Operand.reg "%or.cond306") "if.then253" "if.end268" },
    { name := "if.then253",
      instrs := [
        Instr.icmp "%cmp254" (IPred.sgt) 64 (Operand.reg "%sub231") (Operand.imm (Const.int 64 0xffffffffffffffff#64)),
        Instr.uitofp "%conv256" 64 (Operand.reg "%add244")
      ],
      term := Term.condbr (Operand.reg "%cmp254") "cond.true" "cond.false" },
    { name := "cond.true",
      instrs := [
        Instr.gep "%arrayidx257" Ty.double (Operand.global "@NUMF_EL1_POW10") (Operand.reg "%sub231"),
        Instr.load "%33" Ty.double (Operand.reg "%arrayidx257"),
        Instr.fmul "%mul258" (Operand.reg "%33") (Operand.reg "%conv256")
      ],
      term := Term.br "cleanup282.thread" },
    { name := "cond.false",
      instrs := [
        Instr.binop "%sub260" (BinOp.sub) 64 (Operand.imm (Const.int 64 0x0000000000000000#64)) (Operand.reg "%sub231"),
        Instr.gep "%arrayidx261" Ty.double (Operand.global "@NUMF_EL1_POW10") (Operand.reg "%sub260"),
        Instr.load "%34" Ty.double (Operand.reg "%arrayidx261"),
        Instr.fdiv "%div" (Operand.reg "%conv256") (Operand.reg "%34")
      ],
      term := Term.br "cleanup282.thread" },
    { name := "cleanup282.thread",
      instrs := [
        Instr.phi "%cond" Ty.double [("cond.true", (Operand.reg "%mul258")),
                                       ("cond.false", (Operand.reg "%div"))],
        Instr.fneg "%fneg" (Operand.reg "%cond"),
        Instr.select "%cond266" Ty.double (Operand.reg "%tobool274.not") (Operand.reg "%cond") (Operand.reg "%fneg"),
        Instr.store Ty.double (Operand.reg "%cond266") (Operand.reg "%out")
      ],
      term := Term.br "cleanup300" },
    { name := "if.end268",
      instrs := [
        Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000008#64))),
                             (Ty.ptr, (Operand.reg "%d269"))],
        Instr.call "%call270" (Ty.int 32) "num_el_el1" [((Ty.int 64), (Operand.reg "%add244")),
                             ((Ty.int 64), (Operand.reg "%sub231")),
                             (Ty.ptr, (Operand.reg "%d269"))],
        Instr.icmp "%tobool271.not" (IPred.eq) 32 (Operand.reg "%call270") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%tobool271.not") "cleanup282.thread462" "cleanup282" },
    { name := "cleanup282.thread462",
      instrs := [
        Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000008#64))),
                             (Ty.ptr, (Operand.reg "%d269"))]
      ],
      term := Term.br "if.end285" },
    { name := "cleanup282",
      instrs := [
        Instr.load "%35" (Ty.int 64) (Operand.global "@g_nume1_el"),
        Instr.binop "%inc273" (BinOp.add) 64 (Operand.reg "%35") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.store (Ty.int 64) (Operand.reg "%inc273") (Operand.global "@g_nume1_el"),
        Instr.load "%36" Ty.double (Operand.reg "%d269"),
        Instr.fneg "%fneg276" (Operand.reg "%36"),
        Instr.select "%cond279" Ty.double (Operand.reg "%tobool274.not") (Operand.reg "%36") (Operand.reg "%fneg276"),
        Instr.store Ty.double (Operand.reg "%cond279") (Operand.reg "%out"),
        Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000008#64))),
                             (Ty.ptr, (Operand.reg "%d269"))]
      ],
      term := Term.br "cleanup300" },
    { name := "if.end285",
      instrs := [
        Instr.load "%37" (Ty.int 64) (Operand.global "@g_nume1_slow"),
        Instr.binop "%inc287" (BinOp.add) 64 (Operand.reg "%37") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.store (Ty.int 64) (Operand.reg "%inc287") (Operand.global "@g_nume1_slow"),
        Instr.load "%38" (Ty.int 8) (Operand.reg "%p"),
        Instr.icmp "%cmp1.i" (IPred.eq) 8 (Operand.reg "%38") (Operand.imm (Const.int 8 0x2d#8)),
        Instr.zext "%i.0.i" 1 64 (Operand.reg "%cmp1.i"),
        Instr.icmp "%cmp3.not.i" (IPred.ugt) 64 (Operand.reg "%n") (Operand.reg "%i.0.i")
      ],
      term := Term.condbr (Operand.reg "%cmp3.not.i") "if.end6.i" "if.then5.i" },
    { name := "if.then5.i",
      instrs := [
        Instr.store (Ty.int 64) (Operand.imm (Const.int 64 0x0000000000000001#64)) (Operand.reg "%err")
      ],
      term := Term.br "cleanup300" },
    { name := "if.end6.i",
      instrs := [
        Instr.gep "%arrayidx7.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.0.i"),
        Instr.load "%39" (Ty.int 8) (Operand.reg "%arrayidx7.i"),
        Instr.icmp "%cmp9.i" (IPred.eq) 8 (Operand.reg "%39") (Operand.imm (Const.int 8 0x30#8))
      ],
      term := Term.condbr (Operand.reg "%cmp9.i") "if.then11.i" "if.else.i" },
    { name := "if.then11.i",
      instrs := [
        Instr.select "%inc12.i" (Ty.int 64) (Operand.reg "%cmp1.i") (Operand.imm (Const.int 64 0x0000000000000002#64)) (Operand.imm (Const.int 64 0x0000000000000001#64))
      ],
      term := Term.br "if.end37.i" },
    { name := "if.else.i",
      instrs := [
        Instr.binop "%40" (BinOp.add) 8 (Operand.reg "%39") (Operand.imm (Const.int 8 0xcf#8)),
        Instr.icmp "%or.cond.i" (IPred.ult) 8 (Operand.reg "%40") (Operand.imm (Const.int 8 0x09#8))
      ],
      term := Term.condbr (Operand.reg "%or.cond.i") "land.lhs.true25.i" "if.else35.i" },
    { name := "land.lhs.true25.i",
      instrs := [
        Instr.phi "%i.1262.i" (Ty.int 64) [("while.body.i", (Operand.reg "%inc34.i")),
                                       ("if.else.i", (Operand.reg "%i.0.i"))],
        Instr.gep "%arrayidx26.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.1262.i"),
        Instr.load "%41" (Ty.int 8) (Operand.reg "%arrayidx26.i"),
        Instr.binop "%42" (BinOp.add) 8 (Operand.reg "%41") (Operand.imm (Const.int 8 0xd0#8)),
        Instr.icmp "%or.cond222.i" (IPred.ult) 8 (Operand.reg "%42") (Operand.imm (Const.int 8 0x0a#8))
      ],
      term := Term.condbr (Operand.reg "%or.cond222.i") "while.body.i" "if.end37.i" },
    { name := "while.body.i",
      instrs := [
        Instr.binop "%inc34.i" (BinOp.add) 64 (Operand.reg "%i.1262.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%exitcond.not.i" (IPred.eq) 64 (Operand.reg "%inc34.i") (Operand.reg "%n")
      ],
      term := Term.condbr (Operand.reg "%exitcond.not.i") "if.then143.i" "land.lhs.true25.i" },
    { name := "if.else35.i",
      instrs := [
        Instr.store (Ty.int 64) (Operand.reg "%i.0.i") (Operand.reg "%err")
      ],
      term := Term.br "cleanup300" },
    { name := "if.end37.i",
      instrs := [
        Instr.phi "%i.2.i" (Ty.int 64) [("if.then11.i", (Operand.reg "%inc12.i")),
                                       ("land.lhs.true25.i", (Operand.reg "%i.1262.i"))],
        Instr.icmp "%cmp38.i" (IPred.ult) 64 (Operand.reg "%i.2.i") (Operand.reg "%n")
      ],
      term := Term.condbr (Operand.reg "%cmp38.i") "land.lhs.true40.i" "if.end77.i" },
    { name := "land.lhs.true40.i",
      instrs := [
        Instr.gep "%arrayidx41.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.2.i"),
        Instr.load "%43" (Ty.int 8) (Operand.reg "%arrayidx41.i"),
        Instr.icmp "%cmp43.i" (IPred.eq) 8 (Operand.reg "%43") (Operand.imm (Const.int 8 0x2e#8))
      ],
      term := Term.condbr (Operand.reg "%cmp43.i") "if.then45.i" "if.end77.i" },
    { name := "if.then45.i",
      instrs := [
        Instr.binop "%inc46.i" (BinOp.add) 64 (Operand.reg "%i.2.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%cmp47.not.i" (IPred.ult) 64 (Operand.reg "%inc46.i") (Operand.reg "%n")
      ],
      term := Term.condbr (Operand.reg "%cmp47.not.i") "lor.lhs.false.i" "if.then58.i" },
    { name := "lor.lhs.false.i",
      instrs := [
        Instr.gep "%arrayidx49.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%inc46.i"),
        Instr.load "%44" (Ty.int 8) (Operand.reg "%arrayidx49.i"),
        Instr.binop "%45" (BinOp.add) 8 (Operand.reg "%44") (Operand.imm (Const.int 8 0xc6#8)),
        Instr.icmp "%or.cond223.i" (IPred.ult) 8 (Operand.reg "%45") (Operand.imm (Const.int 8 0xf6#8))
      ],
      term := Term.condbr (Operand.reg "%or.cond223.i") "if.then58.i" "land.lhs.true63.i" },
    { name := "if.then58.i",
      instrs := [
        Instr.store (Ty.int 64) (Operand.reg "%inc46.i") (Operand.reg "%err")
      ],
      term := Term.br "cleanup300" },
    { name := "land.lhs.true63.i",
      instrs := [
        Instr.phi "%i.3265.i" (Ty.int 64) [("while.body74.i", (Operand.reg "%inc75.i")),
                                       ("lor.lhs.false.i", (Operand.reg "%inc46.i"))],
        Instr.gep "%arrayidx64.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.3265.i"),
        Instr.load "%46" (Ty.int 8) (Operand.reg "%arrayidx64.i"),
        Instr.binop "%47" (BinOp.add) 8 (Operand.reg "%46") (Operand.imm (Const.int 8 0xd0#8)),
        Instr.icmp "%or.cond224.i" (IPred.ult) 8 (Operand.reg "%47") (Operand.imm (Const.int 8 0x0a#8))
      ],
      term := Term.condbr (Operand.reg "%or.cond224.i") "while.body74.i" "if.end77.i" },
    { name := "while.body74.i",
      instrs := [
        Instr.binop "%inc75.i" (BinOp.add) 64 (Operand.reg "%i.3265.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%exitcond306.not.i" (IPred.eq) 64 (Operand.reg "%inc75.i") (Operand.reg "%n")
      ],
      term := Term.condbr (Operand.reg "%exitcond306.not.i") "if.then143.i" "land.lhs.true63.i" },
    { name := "if.end77.i",
      instrs := [
        Instr.phi "%i.4.i" (Ty.int 64) [("land.lhs.true40.i", (Operand.reg "%i.2.i")),
                                       ("if.end37.i", (Operand.reg "%i.2.i")),
                                       ("land.lhs.true63.i", (Operand.reg "%i.3265.i"))],
        Instr.icmp "%cmp78.i" (IPred.ult) 64 (Operand.reg "%i.4.i") (Operand.reg "%n")
      ],
      term := Term.condbr (Operand.reg "%cmp78.i") "land.lhs.true80.i" "if.end138.i" },
    { name := "land.lhs.true80.i",
      instrs := [
        Instr.gep "%arrayidx81.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.4.i"),
        Instr.load "%48" (Ty.int 8) (Operand.reg "%arrayidx81.i")
      ],
      term := Term.br "NodeBlock13" },
    { name := "NodeBlock13",
      instrs := [
        Instr.icmp "%Pivot14" (IPred.slt) 8 (Operand.reg "%48") (Operand.imm (Const.int 8 0x65#8))
      ],
      term := Term.condbr (Operand.reg "%Pivot14") "LeafBlock9" "LeafBlock11" },
    { name := "LeafBlock11",
      instrs := [
        Instr.icmp "%SwitchLeaf12" (IPred.eq) 8 (Operand.reg "%48") (Operand.imm (Const.int 8 0x65#8))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf12") "if.then90.i" "if.end138.i" },
    { name := "LeafBlock9",
      instrs := [
        Instr.icmp "%SwitchLeaf10" (IPred.eq) 8 (Operand.reg "%48") (Operand.imm (Const.int 8 0x45#8))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf10") "if.then90.i" "if.end138.i" },
    { name := "if.then90.i",
      instrs := [
        Instr.binop "%inc91.i" (BinOp.add) 64 (Operand.reg "%i.4.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%cmp92.i" (IPred.ult) 64 (Operand.reg "%inc91.i") (Operand.reg "%n")
      ],
      term := Term.condbr (Operand.reg "%cmp92.i") "land.lhs.true94.i" "if.end106.i" },
    { name := "land.lhs.true94.i",
      instrs := [
        Instr.gep "%arrayidx95.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%inc91.i"),
        Instr.load "%49" (Ty.int 8) (Operand.reg "%arrayidx95.i")
      ],
      term := Term.br "NodeBlock19" },
    { name := "NodeBlock19",
      instrs := [
        Instr.icmp "%Pivot20" (IPred.slt) 8 (Operand.reg "%49") (Operand.imm (Const.int 8 0x2d#8))
      ],
      term := Term.condbr (Operand.reg "%Pivot20") "LeafBlock15" "LeafBlock17" },
    { name := "LeafBlock17",
      instrs := [
        Instr.icmp "%SwitchLeaf18" (IPred.eq) 8 (Operand.reg "%49") (Operand.imm (Const.int 8 0x2d#8))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf18") "if.then104.i" "if.end106.i" },
    { name := "LeafBlock15",
      instrs := [
        Instr.icmp "%SwitchLeaf16" (IPred.eq) 8 (Operand.reg "%49") (Operand.imm (Const.int 8 0x2b#8))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf16") "if.then104.i" "if.end106.i" },
    { name := "if.then104.i",
      instrs := [
        Instr.binop "%inc105.i" (BinOp.add) 64 (Operand.reg "%i.4.i") (Operand.imm (Const.int 64 0x0000000000000002#64))
      ],
      term := Term.br "if.end106.i" },
    { name := "if.end106.i",
      instrs := [
        Instr.phi "%i.5.i" (Ty.int 64) [("if.then104.i", (Operand.reg "%inc105.i")),
                                       ("if.then90.i", (Operand.reg "%inc91.i")),
                                       ("LeafBlock15", (Operand.reg "%inc91.i")),
                                       ("LeafBlock17", (Operand.reg "%inc91.i"))],
        Instr.icmp "%cmp107.not.i" (IPred.ult) 64 (Operand.reg "%i.5.i") (Operand.reg "%n")
      ],
      term := Term.condbr (Operand.reg "%cmp107.not.i") "lor.lhs.false109.i" "if.then119.i" },
    { name := "lor.lhs.false109.i",
      instrs := [
        Instr.gep "%arrayidx110.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.5.i"),
        Instr.load "%50" (Ty.int 8) (Operand.reg "%arrayidx110.i"),
        Instr.binop "%51" (BinOp.add) 8 (Operand.reg "%50") (Operand.imm (Const.int 8 0xc6#8)),
        Instr.icmp "%or.cond225.i" (IPred.ult) 8 (Operand.reg "%51") (Operand.imm (Const.int 8 0xf6#8))
      ],
      term := Term.condbr (Operand.reg "%or.cond225.i") "if.then119.i" "land.lhs.true124.i" },
    { name := "if.then119.i",
      instrs := [
        Instr.store (Ty.int 64) (Operand.reg "%i.5.i") (Operand.reg "%err")
      ],
      term := Term.br "cleanup300" },
    { name := "land.lhs.true124.i",
      instrs := [
        Instr.phi "%i.6269.i" (Ty.int 64) [("while.body135.i", (Operand.reg "%inc136.i")),
                                       ("lor.lhs.false109.i", (Operand.reg "%i.5.i"))],
        Instr.gep "%arrayidx125.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.6269.i"),
        Instr.load "%52" (Ty.int 8) (Operand.reg "%arrayidx125.i"),
        Instr.binop "%53" (BinOp.add) 8 (Operand.reg "%52") (Operand.imm (Const.int 8 0xd0#8)),
        Instr.icmp "%or.cond226.i" (IPred.ult) 8 (Operand.reg "%53") (Operand.imm (Const.int 8 0x0a#8))
      ],
      term := Term.condbr (Operand.reg "%or.cond226.i") "while.body135.i" "if.end138.i" },
    { name := "while.body135.i",
      instrs := [
        Instr.binop "%inc136.i" (BinOp.add) 64 (Operand.reg "%i.6269.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%exitcond307.not.i" (IPred.eq) 64 (Operand.reg "%inc136.i") (Operand.reg "%n")
      ],
      term := Term.condbr (Operand.reg "%exitcond307.not.i") "if.then143.i" "land.lhs.true124.i" },
    { name := "if.end138.i",
      instrs := [
        Instr.phi "%i.7.i" (Ty.int 64) [("if.end77.i", (Operand.reg "%i.4.i")),
                                       ("land.lhs.true124.i", (Operand.reg "%i.6269.i")),
                                       ("LeafBlock9", (Operand.reg "%i.4.i")),
                                       ("LeafBlock11", (Operand.reg "%i.4.i"))],
        Instr.icmp "%cmp139.not.i" (IPred.eq) 64 (Operand.reg "%i.7.i") (Operand.reg "%n")
      ],
      term := Term.condbr (Operand.reg "%cmp139.not.i") "if.then143.i" "if.then141.i" },
    { name := "if.then141.i",
      instrs := [
        Instr.store (Ty.int 64) (Operand.reg "%i.7.i") (Operand.reg "%err")
      ],
      term := Term.br "cleanup300" },
    { name := "if.then143.i",
      instrs := [
        Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000300#64))),
                             (Ty.ptr, (Operand.reg "%dig.i.i"))]
      ],
      term := Term.br "for.body.outer.i.outer.i" },
    { name := "for.body.outer.i.outer.i",
      instrs := [
        Instr.phi "%i.1725.ph.i.ph.i" (Ty.int 64) [("if.then143.i", (Operand.reg "%i.0.i")),
                                       ("for.inc.i.i", (Operand.reg "%inc57.i.i"))],
        Instr.phi "%R.0724.ph.i.ph.i" (Ty.int 64) [("if.then143.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.inc.i.i", (Operand.reg "%R.4.ph.i.i"))],
        Instr.phi "%T.0723.ph.i.ph.i" (Ty.int 64) [("if.then143.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.inc.i.i", (Operand.reg "%T.2.ph.i.i"))],
        Instr.phi "%F.0722.ph.i.ph.i" (Ty.int 64) [("if.then143.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.inc.i.i", (Operand.reg "%F.3.ph.i.i"))],
        Instr.phi "%lead.0721.ph.i.ph.i" (Ty.int 64) [("if.then143.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.inc.i.i", (Operand.reg "%lead.0721.i287.i"))],
        Instr.phi "%top.0720.ph.i.ph.i" (Ty.int 64) [("if.then143.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.inc.i.i", (Operand.reg "%top.4.ph.i.i"))],
        Instr.phi "%topn.0719.ph.i.ph.i" (Ty.int 64) [("if.then143.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.inc.i.i", (Operand.reg "%topn.4.ph.i.i"))],
        Instr.phi "%in_frac.0718.ph.i.ph.i" (Ty.int 32) [("if.then143.i", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("for.inc.i.i", (Operand.reg "%in_frac.2.ph.i.i"))],
        Instr.phi "%seen.0717.ph.i.ph.i" (Ty.int 32) [("if.then143.i", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("for.inc.i.i", (Operand.reg "%seen.4.ph.i.i"))],
        Instr.phi "%sticky.0716.ph.i.ph.i" (Ty.int 32) [("if.then143.i", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("for.inc.i.i", (Operand.reg "%sticky.4.ph.i.i"))]
      ],
      term := Term.br "for.body.outer.i.i" },
    { name := "for.body.outer.i.i",
      instrs := [
        Instr.phi "%i.1725.ph.i.i" (Ty.int 64) [("for.body.outer.i.outer.i", (Operand.reg "%i.1725.ph.i.ph.i")),
                                       ("if.else46.i.thread.i", (Operand.reg "%inc57.i344.i"))],
        Instr.phi "%T.0723.ph.i.i" (Ty.int 64) [("for.body.outer.i.outer.i", (Operand.reg "%T.0723.ph.i.ph.i")),
                                       ("if.else46.i.thread.i", (Operand.reg "%T.0723.i.i"))],
        Instr.phi "%F.0722.ph.i.i" (Ty.int 64) [("for.body.outer.i.outer.i", (Operand.reg "%F.0722.ph.i.ph.i")),
                                       ("if.else46.i.thread.i", (Operand.reg "%F.0722.i.i"))],
        Instr.phi "%lead.0721.ph.i.i" (Ty.int 64) [("for.body.outer.i.outer.i", (Operand.reg "%lead.0721.ph.i.ph.i")),
                                       ("if.else46.i.thread.i", (Operand.reg "%lead.0721.i.i"))],
        Instr.phi "%in_frac.0718.ph.i.i" (Ty.int 32) [("for.body.outer.i.outer.i", (Operand.reg "%in_frac.0718.ph.i.ph.i")),
                                       ("if.else46.i.thread.i", (Operand.imm (Const.int 32 0x00000001#32)))],
        Instr.phi "%seen.0717.ph.i.i" (Ty.int 32) [("for.body.outer.i.outer.i", (Operand.reg "%seen.0717.ph.i.ph.i")),
                                       ("if.else46.i.thread.i", (Operand.imm (Const.int 32 0x00000000#32)))],
        Instr.icmp "%tobool.not.i.i" (IPred.ne) 32 (Operand.reg "%in_frac.0718.ph.i.i") (Operand.imm (Const.int 32 0x00000000#32)),
        Instr.zext "%inc18.i.i" 1 64 (Operand.reg "%tobool.not.i.i"),
        Instr.gep "%arrayidx5.i.peel.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.1725.ph.i.i"),
        Instr.load "%54" (Ty.int 8) (Operand.reg "%arrayidx5.i.peel.i"),
        Instr.binop "%55" (BinOp.add) 8 (Operand.reg "%54") (Operand.imm (Const.int 8 0xd0#8)),
        Instr.icmp "%or.cond.i.peel.i" (IPred.ult) 8 (Operand.reg "%55") (Operand.imm (Const.int 8 0x0a#8))
      ],
      term := Term.condbr (Operand.reg "%or.cond.i.peel.i") "if.then13.i.peel.i" "if.else46.i.i" },
    { name := "if.then13.i.peel.i",
      instrs := [
        Instr.binop "%inc16.i.peel.i" (BinOp.add) 64 (Operand.reg "%T.0723.ph.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.binop "%spec.select.i.peel.i" (BinOp.add) 64 (Operand.reg "%F.0722.ph.i.i") (Operand.reg "%inc18.i.i"),
        Instr.icmp "%tobool20.not.i.peel.i" (IPred.eq) 32 (Operand.reg "%seen.0717.ph.i.i") (Operand.imm (Const.int 32 0x00000000#32)),
        Instr.icmp "%cmp23.i.peel.i" (IPred.eq) 8 (Operand.reg "%55") (Operand.imm (Const.int 8 0x00#8)),
        Instr.binop "%or.cond510.i.peel.i" (BinOp.and) 1 (Operand.reg "%tobool20.not.i.peel.i") (Operand.reg "%cmp23.i.peel.i")
      ],
      term := Term.condbr (Operand.reg "%or.cond510.i.peel.i") "for.inc.thread.i.peel.i" "if.end28.i.i.loopexit609" },
    { name := "for.inc.thread.i.peel.i",
      instrs := [
        Instr.binop "%inc57798.i.peel.i" (BinOp.add) 64 (Operand.reg "%i.1725.ph.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%exitcond.not799.i.peel.i" (IPred.eq) 64 (Operand.reg "%inc57798.i.peel.i") (Operand.reg "%n")
      ],
      term := Term.condbr (Operand.reg "%exitcond.not799.i.peel.i") "if.then59.i.i" "for.body.i.i" },
    { name := "for.body.i.i",
      instrs := [
        Instr.phi "%i.1725.i.i" (Ty.int 64) [("for.inc.thread.i.i", (Operand.reg "%inc57798.i.i")),
                                       ("for.inc.thread.i.peel.i", (Operand.reg "%inc57798.i.peel.i"))],
        Instr.phi "%T.0723.i.i" (Ty.int 64) [("for.inc.thread.i.i", (Operand.reg "%inc16.i.i")),
                                       ("for.inc.thread.i.peel.i", (Operand.reg "%inc16.i.peel.i"))],
        Instr.phi "%F.0722.i.i" (Ty.int 64) [("for.inc.thread.i.i", (Operand.reg "%spec.select.i.i")),
                                       ("for.inc.thread.i.peel.i", (Operand.reg "%spec.select.i.peel.i"))],
        Instr.phi "%lead.0721.i.in.i" (Ty.int 64) [("for.inc.thread.i.i", (Operand.reg "%lead.0721.i.i")),
                                       ("for.inc.thread.i.peel.i", (Operand.reg "%lead.0721.ph.i.i"))],
        Instr.binop "%lead.0721.i.i" (BinOp.add) 64 (Operand.reg "%lead.0721.i.in.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.gep "%arrayidx5.i.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.1725.i.i"),
        Instr.load "%56" (Ty.int 8) (Operand.reg "%arrayidx5.i.i"),
        Instr.binop "%57" (BinOp.add) 8 (Operand.reg "%56") (Operand.imm (Const.int 8 0xd0#8)),
        Instr.icmp "%or.cond.i.i" (IPred.ult) 8 (Operand.reg "%57") (Operand.imm (Const.int 8 0x0a#8))
      ],
      term := Term.condbr (Operand.reg "%or.cond.i.i") "if.then13.i.i" "if.else46.i.thread.i" },
    { name := "if.then13.i.i",
      instrs := [
        Instr.binop "%inc16.i.i" (BinOp.add) 64 (Operand.reg "%T.0723.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.binop "%spec.select.i.i" (BinOp.add) 64 (Operand.reg "%F.0722.i.i") (Operand.reg "%inc18.i.i"),
        Instr.icmp "%cmp23.i.i" (IPred.eq) 8 (Operand.reg "%57") (Operand.imm (Const.int 8 0x00#8))
      ],
      term := Term.condbr (Operand.reg "%cmp23.i.i") "for.inc.thread.i.i" "if.end28.i.i" },
    { name := "if.end28.i.i.loopexit609",
      instrs := [
        Instr.select "%58" (Ty.int 32) (Operand.reg "%cmp23.i.peel.i") (Operand.reg "%sticky.0716.ph.i.ph.i") (Operand.imm (Const.int 32 0x00000001#32))
      ],
      term := Term.br "if.end28.i.i" },
    { name := "if.end28.i.i",
      instrs := [
        Instr.phi "%inc16.i.lcssa.i" (Ty.int 64) [("if.end28.i.i.loopexit609", (Operand.reg "%inc16.i.peel.i")),
                                       ("if.then13.i.i", (Operand.reg "%inc16.i.i"))],
        Instr.phi "%spec.select.i.lcssa.i" (Ty.int 64) [("if.end28.i.i.loopexit609", (Operand.reg "%spec.select.i.peel.i")),
                                       ("if.then13.i.i", (Operand.reg "%spec.select.i.i"))],
        Instr.phi "%cmp23.i.lcssa.i" (Ty.int 32) [("if.end28.i.i.loopexit609", (Operand.reg "%58")),
                                       ("if.then13.i.i", (Operand.imm (Const.int 32 0x00000001#32)))],
        Instr.phi "%i.1725.i.lcssa292.i" (Ty.int 64) [("if.end28.i.i.loopexit609", (Operand.reg "%i.1725.ph.i.i")),
                                       ("if.then13.i.i", (Operand.reg "%i.1725.i.i"))],
        Instr.phi "%lead.0721.i.lcssa284.i" (Ty.int 64) [("if.end28.i.i.loopexit609", (Operand.reg "%lead.0721.ph.i.i")),
                                       ("if.then13.i.i", (Operand.reg "%lead.0721.i.i"))],
        Instr.phi "%.lcssa277.i" (Ty.int 8) [("if.end28.i.i.loopexit609", (Operand.reg "%55")),
                                       ("if.then13.i.i", (Operand.reg "%57"))],
        Instr.icmp "%cmp29.i.i" (IPred.ult) 64 (Operand.reg "%R.0724.ph.i.ph.i") (Operand.imm (Const.int 64 0x0000000000000300#64))
      ],
      term := Term.condbr (Operand.reg "%cmp29.i.i") "if.then31.i.i" "for.inc.i.i" },
    { name := "if.then31.i.i",
      instrs := [
        Instr.binop "%inc32.i.i" (BinOp.add) 64 (Operand.reg "%R.0724.ph.i.ph.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.gep "%arrayidx33.i.i" (Ty.int 8) (Operand.reg "%dig.i.i") (Operand.reg "%R.0724.ph.i.ph.i"),
        Instr.store (Ty.int 8) (Operand.reg "%.lcssa277.i") (Operand.reg "%arrayidx33.i.i"),
        Instr.icmp "%cmp34.i.i" (IPred.ult) 64 (Operand.reg "%topn.0719.ph.i.ph.i") (Operand.imm (Const.int 64 0x0000000000000013#64))
      ],
      term := Term.condbr (Operand.reg "%cmp34.i.i") "if.then36.i.i" "for.inc.i.i" },
    { name := "if.then36.i.i",
      instrs := [
        Instr.binop "%mul.i.i" (BinOp.mul) 64 (Operand.reg "%top.0720.ph.i.ph.i") (Operand.imm (Const.int 64 0x000000000000000a#64)),
        Instr.zext "%conv37.i.i" 8 64 (Operand.reg "%.lcssa277.i"),
        Instr.binop "%add.i.i" (BinOp.add) 64 (Operand.reg "%mul.i.i") (Operand.reg "%conv37.i.i"),
        Instr.binop "%inc38.i.i" (BinOp.add) 64 (Operand.reg "%topn.0719.ph.i.ph.i") (Operand.imm (Const.int 64 0x0000000000000001#64))
      ],
      term := Term.br "for.inc.i.i" },
    { name := "if.else46.i.i",
      instrs := [
        Instr.icmp "%cmp48.i.i" (IPred.eq) 8 (Operand.reg "%54") (Operand.imm (Const.int 8 0x2e#8))
      ],
      term := Term.condbr (Operand.reg "%cmp48.i.i") "for.inc.i.i" "for.end.i.i" },
    { name := "if.else46.i.thread.i",
      instrs := [
        Instr.icmp "%cmp48.i322.i" (IPred.ne) 8 (Operand.reg "%56") (Operand.imm (Const.int 8 0x2e#8)),
        Instr.binop "%inc57.i344.i" (BinOp.add) 64 (Operand.reg "%i.1725.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%exitcond.not.i345.i" (IPred.eq) 64 (Operand.reg "%inc57.i344.i") (Operand.reg "%n"),
        Instr.binop "%or.cond447.i" (BinOp.or) 1 (Operand.reg "%exitcond.not.i345.i") (Operand.reg "%cmp48.i322.i")
      ],
      term := Term.condbr (Operand.reg "%or.cond447.i") "if.then59.i.i" "for.body.outer.i.i" },
    { name := "for.inc.i.i",
      instrs := [
        Instr.phi "%i.1725.i294.i" (Ty.int 64) [("if.then31.i.i", (Operand.reg "%i.1725.i.lcssa292.i")),
                                       ("if.then36.i.i", (Operand.reg "%i.1725.i.lcssa292.i")),
                                       ("if.else46.i.i", (Operand.reg "%i.1725.ph.i.i")),
                                       ("if.end28.i.i", (Operand.reg "%i.1725.i.lcssa292.i"))],
        Instr.phi "%lead.0721.i287.i" (Ty.int 64) [("if.then31.i.i", (Operand.reg "%lead.0721.i.lcssa284.i")),
                                       ("if.then36.i.i", (Operand.reg "%lead.0721.i.lcssa284.i")),
                                       ("if.else46.i.i", (Operand.reg "%lead.0721.ph.i.i")),
                                       ("if.end28.i.i", (Operand.reg "%lead.0721.i.lcssa284.i"))],
        Instr.phi "%sticky.4.ph.i.i" (Ty.int 32) [("if.then31.i.i", (Operand.reg "%sticky.0716.ph.i.ph.i")),
                                       ("if.then36.i.i", (Operand.reg "%sticky.0716.ph.i.ph.i")),
                                       ("if.else46.i.i", (Operand.reg "%sticky.0716.ph.i.ph.i")),
                                       ("if.end28.i.i", (Operand.reg "%cmp23.i.lcssa.i"))],
        Instr.phi "%seen.4.ph.i.i" (Ty.int 32) [("if.then31.i.i", (Operand.imm (Const.int 32 0x00000001#32))),
                                       ("if.then36.i.i", (Operand.imm (Const.int 32 0x00000001#32))),
                                       ("if.else46.i.i", (Operand.reg "%seen.0717.ph.i.i")),
                                       ("if.end28.i.i", (Operand.imm (Const.int 32 0x00000001#32)))],
        Instr.phi "%in_frac.2.ph.i.i" (Ty.int 32) [("if.then31.i.i", (Operand.reg "%in_frac.0718.ph.i.i")),
                                       ("if.then36.i.i", (Operand.reg "%in_frac.0718.ph.i.i")),
                                       ("if.else46.i.i", (Operand.imm (Const.int 32 0x00000001#32))),
                                       ("if.end28.i.i", (Operand.reg "%in_frac.0718.ph.i.i"))],
        Instr.phi "%topn.4.ph.i.i" (Ty.int 64) [("if.then31.i.i", (Operand.reg "%topn.0719.ph.i.ph.i")),
                                       ("if.then36.i.i", (Operand.reg "%inc38.i.i")),
                                       ("if.else46.i.i", (Operand.reg "%topn.0719.ph.i.ph.i")),
                                       ("if.end28.i.i", (Operand.reg "%topn.0719.ph.i.ph.i"))],
        Instr.phi "%top.4.ph.i.i" (Ty.int 64) [("if.then31.i.i", (Operand.reg "%top.0720.ph.i.ph.i")),
                                       ("if.then36.i.i", (Operand.reg "%add.i.i")),
                                       ("if.else46.i.i", (Operand.reg "%top.0720.ph.i.ph.i")),
                                       ("if.end28.i.i", (Operand.reg "%top.0720.ph.i.ph.i"))],
        Instr.phi "%F.3.ph.i.i" (Ty.int 64) [("if.then31.i.i", (Operand.reg "%spec.select.i.lcssa.i")),
                                       ("if.then36.i.i", (Operand.reg "%spec.select.i.lcssa.i")),
                                       ("if.else46.i.i", (Operand.reg "%F.0722.ph.i.i")),
                                       ("if.end28.i.i", (Operand.reg "%spec.select.i.lcssa.i"))],
        Instr.phi "%T.2.ph.i.i" (Ty.int 64) [("if.then31.i.i", (Operand.reg "%inc16.i.lcssa.i")),
                                       ("if.then36.i.i", (Operand.reg "%inc16.i.lcssa.i")),
                                       ("if.else46.i.i", (Operand.reg "%T.0723.ph.i.i")),
                                       ("if.end28.i.i", (Operand.reg "%inc16.i.lcssa.i"))],
        Instr.phi "%R.4.ph.i.i" (Ty.int 64) [("if.then31.i.i", (Operand.reg "%inc32.i.i")),
                                       ("if.then36.i.i", (Operand.reg "%inc32.i.i")),
                                       ("if.else46.i.i", (Operand.reg "%R.0724.ph.i.ph.i")),
                                       ("if.end28.i.i", (Operand.reg "%R.0724.ph.i.ph.i"))],
        Instr.binop "%inc57.i.i" (BinOp.add) 64 (Operand.reg "%i.1725.i294.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%exitcond.not.i.i" (IPred.eq) 64 (Operand.reg "%inc57.i.i") (Operand.reg "%n")
      ],
      term := Term.condbr (Operand.reg "%exitcond.not.i.i") "for.end.thread.i.i" "for.body.outer.i.outer.i" },
    { name := "for.inc.thread.i.i",
      instrs := [
        Instr.binop "%inc57798.i.i" (BinOp.add) 64 (Operand.reg "%i.1725.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%exitcond.not799.i.i" (IPred.eq) 64 (Operand.reg "%inc57798.i.i") (Operand.reg "%n")
      ],
      term := Term.condbr (Operand.reg "%exitcond.not799.i.i") "if.then59.i.i" "for.body.i.i" },
    { name := "for.end.i.i",
      instrs := [
        Instr.icmp "%tobool58.not.i.i" (IPred.eq) 32 (Operand.reg "%seen.0717.ph.i.i") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%tobool58.not.i.i") "if.then59.i.i" "if.then64.i.i" },
    { name := "for.end.thread.i.i",
      instrs := [
        Instr.icmp "%59" (IPred.eq) 32 (Operand.reg "%seen.4.ph.i.i") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%59") "if.then59.i.i" "if.end104.i.i" },
    { name := "if.then59.i.i",
      instrs := [
        Instr.select "%cond.i.i" Ty.double (Operand.reg "%cmp1.i") (Operand.imm (Const.float 0x8000000000000000#64)) (Operand.imm (Const.float 0x0000000000000000#64))
      ],
      term := Term.br "if.end291" },
    { name := "if.then64.i.i",
      instrs := [
        Instr.binop "%inc65.i.i" (BinOp.add) 64 (Operand.reg "%i.1725.ph.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%cmp66.i.i" (IPred.ult) 64 (Operand.reg "%inc65.i.i") (Operand.reg "%n")
      ],
      term := Term.condbr (Operand.reg "%cmp66.i.i") "land.lhs.true68.i.i" "if.end83.i.i" },
    { name := "land.lhs.true68.i.i",
      instrs := [
        Instr.gep "%arrayidx69.i.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%inc65.i.i"),
        Instr.load "%60" (Ty.int 8) (Operand.reg "%arrayidx69.i.i")
      ],
      term := Term.br "NodeBlock25" },
    { name := "NodeBlock25",
      instrs := [
        Instr.icmp "%Pivot26" (IPred.slt) 8 (Operand.reg "%60") (Operand.imm (Const.int 8 0x2d#8))
      ],
      term := Term.condbr (Operand.reg "%Pivot26") "LeafBlock21" "LeafBlock23" },
    { name := "LeafBlock23",
      instrs := [
        Instr.icmp "%SwitchLeaf24" (IPred.eq) 8 (Operand.reg "%60") (Operand.imm (Const.int 8 0x2d#8))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf24") "if.then77.i.i" "if.end83.i.i" },
    { name := "LeafBlock21",
      instrs := [
        Instr.icmp "%SwitchLeaf22" (IPred.eq) 8 (Operand.reg "%60") (Operand.imm (Const.int 8 0x2b#8))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf22") "if.then77.i.i" "if.end83.i.i" },
    { name := "if.then77.i.i",
      instrs := [
        Instr.icmp "%cmp80.i.i" (IPred.ne) 8 (Operand.reg "%60") (Operand.imm (Const.int 8 0x2d#8)),
        Instr.binop "%inc82.i.i" (BinOp.add) 64 (Operand.reg "%i.1725.ph.i.i") (Operand.imm (Const.int 64 0x0000000000000002#64))
      ],
      term := Term.br "if.end83.i.i" },
    { name := "if.end83.i.i",
      instrs := [
        Instr.phi "%esign.0.i.i" (Ty.int 1) [("if.then77.i.i", (Operand.reg "%cmp80.i.i")),
                                       ("if.then64.i.i", (Operand.imm (Const.int 1 0x1#1))),
                                       ("LeafBlock21", (Operand.imm (Const.int 1 0x1#1))),
                                       ("LeafBlock23", (Operand.imm (Const.int 1 0x1#1)))],
        Instr.phi "%i.2.i.i" (Ty.int 64) [("if.then77.i.i", (Operand.reg "%inc82.i.i")),
                                       ("if.then64.i.i", (Operand.reg "%inc65.i.i")),
                                       ("LeafBlock21", (Operand.reg "%inc65.i.i")),
                                       ("LeafBlock23", (Operand.reg "%inc65.i.i"))],
        Instr.icmp "%cmp85733.i.i" (IPred.ult) 64 (Operand.reg "%i.2.i.i") (Operand.reg "%n")
      ],
      term := Term.condbr (Operand.reg "%cmp85733.i.i") "for.body87.i.i.preheader" "for.end100.i.i" },
    { name := "for.body87.i.i.preheader",
      instrs := [
        Instr.binop "%61" (BinOp.sub) 64 (Operand.reg "%n") (Operand.reg "%i.2.i.i"),
        Instr.binop "%xtraiter" (BinOp.and) 64 (Operand.reg "%61") (Operand.imm (Const.int 64 0x0000000000000003#64)),
        Instr.binop "%62" (BinOp.sub) 64 (Operand.reg "%i.2.i.i") (Operand.reg "%n"),
        Instr.icmp "%63" (IPred.ugt) 64 (Operand.reg "%62") (Operand.imm (Const.int 64 0xfffffffffffffffc#64))
      ],
      term := Term.condbr (Operand.reg "%63") "for.end100.i.i.loopexit.unr-lcssa" "for.body87.i.i.preheader.new" },
    { name := "for.body87.i.i.preheader.new",
      instrs := [
        Instr.binop "%unroll_iter" (BinOp.and) 64 (Operand.reg "%61") (Operand.imm (Const.int 64 0xfffffffffffffffc#64)),
        Instr.gep "%invariant.gep" (Ty.int 8) (Operand.reg "%p") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.gep "%invariant.gep1191" (Ty.int 8) (Operand.reg "%p") (Operand.imm (Const.int 64 0x0000000000000002#64)),
        Instr.gep "%invariant.gep1193" (Ty.int 8) (Operand.reg "%p") (Operand.imm (Const.int 64 0x0000000000000003#64))
      ],
      term := Term.br "for.body87.i.i" },
    { name := "for.body87.i.i",
      instrs := [
        Instr.phi "%i.3735.i.i" (Ty.int 64) [("for.body87.i.i.preheader.new", (Operand.reg "%i.2.i.i")),
                                       ("for.inc98.i.i.3", (Operand.reg "%inc99.i.i.3"))],
        Instr.phi "%e.0734.i.i" (Ty.int 64) [("for.body87.i.i.preheader.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.inc98.i.i.3", (Operand.reg "%e.1.i.i.3"))],
        Instr.phi "%niter" (Ty.int 64) [("for.body87.i.i.preheader.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.inc98.i.i.3", (Operand.reg "%niter.next.3"))],
        Instr.icmp "%cmp88.i.i" (IPred.slt) 64 (Operand.reg "%e.0734.i.i") (Operand.imm (Const.int 64 0x00000000000f4240#64))
      ],
      term := Term.condbr (Operand.reg "%cmp88.i.i") "if.then90.i.i" "for.inc98.i.i" },
    { name := "if.then90.i.i",
      instrs := [
        Instr.binop "%mul91.i.i" (BinOp.mul) 64 (Operand.reg "%e.0734.i.i") (Operand.imm (Const.int 64 0x000000000000000a#64)),
        Instr.gep "%arrayidx92.i.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.3735.i.i"),
        Instr.load "%64" (Ty.int 8) (Operand.reg "%arrayidx92.i.i"),
        Instr.zext "%conv93.i.i" 8 64 (Operand.reg "%64"),
        Instr.binop "%sub94.i.i" (BinOp.add) 64 (Operand.reg "%mul91.i.i") (Operand.imm (Const.int 64 0xffffffffffffffd0#64)),
        Instr.binop "%add96.i.i" (BinOp.add) 64 (Operand.reg "%sub94.i.i") (Operand.reg "%conv93.i.i")
      ],
      term := Term.br "for.inc98.i.i" },
    { name := "for.inc98.i.i",
      instrs := [
        Instr.phi "%e.1.i.i" (Ty.int 64) [("if.then90.i.i", (Operand.reg "%add96.i.i")),
                                       ("for.body87.i.i", (Operand.reg "%e.0734.i.i"))],
        Instr.icmp "%cmp88.i.i.1" (IPred.slt) 64 (Operand.reg "%e.1.i.i") (Operand.imm (Const.int 64 0x00000000000f4240#64))
      ],
      term := Term.condbr (Operand.reg "%cmp88.i.i.1") "if.then90.i.i.1" "for.inc98.i.i.1" },
    { name := "if.then90.i.i.1",
      instrs := [
        Instr.binop "%mul91.i.i.1" (BinOp.mul) 64 (Operand.reg "%e.1.i.i") (Operand.imm (Const.int 64 0x000000000000000a#64)),
        Instr.gep "%gep" (Ty.int 8) (Operand.reg "%invariant.gep") (Operand.reg "%i.3735.i.i"),
        Instr.load "%65" (Ty.int 8) (Operand.reg "%gep"),
        Instr.zext "%conv93.i.i.1" 8 64 (Operand.reg "%65"),
        Instr.binop "%sub94.i.i.1" (BinOp.add) 64 (Operand.reg "%mul91.i.i.1") (Operand.imm (Const.int 64 0xffffffffffffffd0#64)),
        Instr.binop "%add96.i.i.1" (BinOp.add) 64 (Operand.reg "%sub94.i.i.1") (Operand.reg "%conv93.i.i.1")
      ],
      term := Term.br "for.inc98.i.i.1" },
    { name := "for.inc98.i.i.1",
      instrs := [
        Instr.phi "%e.1.i.i.1" (Ty.int 64) [("if.then90.i.i.1", (Operand.reg "%add96.i.i.1")),
                                       ("for.inc98.i.i", (Operand.reg "%e.1.i.i"))],
        Instr.icmp "%cmp88.i.i.2" (IPred.slt) 64 (Operand.reg "%e.1.i.i.1") (Operand.imm (Const.int 64 0x00000000000f4240#64))
      ],
      term := Term.condbr (Operand.reg "%cmp88.i.i.2") "if.then90.i.i.2" "for.inc98.i.i.2" },
    { name := "if.then90.i.i.2",
      instrs := [
        Instr.binop "%mul91.i.i.2" (BinOp.mul) 64 (Operand.reg "%e.1.i.i.1") (Operand.imm (Const.int 64 0x000000000000000a#64)),
        Instr.gep "%gep1192" (Ty.int 8) (Operand.reg "%invariant.gep1191") (Operand.reg "%i.3735.i.i"),
        Instr.load "%66" (Ty.int 8) (Operand.reg "%gep1192"),
        Instr.zext "%conv93.i.i.2" 8 64 (Operand.reg "%66"),
        Instr.binop "%sub94.i.i.2" (BinOp.add) 64 (Operand.reg "%mul91.i.i.2") (Operand.imm (Const.int 64 0xffffffffffffffd0#64)),
        Instr.binop "%add96.i.i.2" (BinOp.add) 64 (Operand.reg "%sub94.i.i.2") (Operand.reg "%conv93.i.i.2")
      ],
      term := Term.br "for.inc98.i.i.2" },
    { name := "for.inc98.i.i.2",
      instrs := [
        Instr.phi "%e.1.i.i.2" (Ty.int 64) [("if.then90.i.i.2", (Operand.reg "%add96.i.i.2")),
                                       ("for.inc98.i.i.1", (Operand.reg "%e.1.i.i.1"))],
        Instr.icmp "%cmp88.i.i.3" (IPred.slt) 64 (Operand.reg "%e.1.i.i.2") (Operand.imm (Const.int 64 0x00000000000f4240#64))
      ],
      term := Term.condbr (Operand.reg "%cmp88.i.i.3") "if.then90.i.i.3" "for.inc98.i.i.3" },
    { name := "if.then90.i.i.3",
      instrs := [
        Instr.binop "%mul91.i.i.3" (BinOp.mul) 64 (Operand.reg "%e.1.i.i.2") (Operand.imm (Const.int 64 0x000000000000000a#64)),
        Instr.gep "%gep1194" (Ty.int 8) (Operand.reg "%invariant.gep1193") (Operand.reg "%i.3735.i.i"),
        Instr.load "%67" (Ty.int 8) (Operand.reg "%gep1194"),
        Instr.zext "%conv93.i.i.3" 8 64 (Operand.reg "%67"),
        Instr.binop "%sub94.i.i.3" (BinOp.add) 64 (Operand.reg "%mul91.i.i.3") (Operand.imm (Const.int 64 0xffffffffffffffd0#64)),
        Instr.binop "%add96.i.i.3" (BinOp.add) 64 (Operand.reg "%sub94.i.i.3") (Operand.reg "%conv93.i.i.3")
      ],
      term := Term.br "for.inc98.i.i.3" },
    { name := "for.inc98.i.i.3",
      instrs := [
        Instr.phi "%e.1.i.i.3" (Ty.int 64) [("if.then90.i.i.3", (Operand.reg "%add96.i.i.3")),
                                       ("for.inc98.i.i.2", (Operand.reg "%e.1.i.i.2"))],
        Instr.binop "%inc99.i.i.3" (BinOp.add) 64 (Operand.reg "%i.3735.i.i") (Operand.imm (Const.int 64 0x0000000000000004#64)),
        Instr.binop "%niter.next.3" (BinOp.add) 64 (Operand.reg "%niter") (Operand.imm (Const.int 64 0x0000000000000004#64)),
        Instr.icmp "%niter.ncmp.3" (IPred.eq) 64 (Operand.reg "%niter.next.3") (Operand.reg "%unroll_iter")
      ],
      term := Term.condbr (Operand.reg "%niter.ncmp.3") "for.end100.i.i.loopexit.unr-lcssa" "for.body87.i.i" },
    { name := "for.end100.i.i.loopexit.unr-lcssa",
      instrs := [
        Instr.phi "%e.1.i.i.lcssa.ph" (Ty.int 64) [("for.body87.i.i.preheader", (Operand.imm Const.poison)),
                                       ("for.inc98.i.i.3", (Operand.reg "%e.1.i.i.3"))],
        Instr.phi "%i.3735.i.i.unr" (Ty.int 64) [("for.body87.i.i.preheader", (Operand.reg "%i.2.i.i")),
                                       ("for.inc98.i.i.3", (Operand.reg "%inc99.i.i.3"))],
        Instr.phi "%e.0734.i.i.unr" (Ty.int 64) [("for.body87.i.i.preheader", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.inc98.i.i.3", (Operand.reg "%e.1.i.i.3"))],
        Instr.icmp "%lcmp.mod.not" (IPred.eq) 64 (Operand.reg "%xtraiter") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%lcmp.mod.not") "for.end100.i.i" "for.body87.i.i.epil" },
    { name := "for.body87.i.i.epil",
      instrs := [
        Instr.phi "%i.3735.i.i.epil" (Ty.int 64) [("for.inc98.i.i.epil", (Operand.reg "%inc99.i.i.epil")),
                                       ("for.end100.i.i.loopexit.unr-lcssa", (Operand.reg "%i.3735.i.i.unr"))],
        Instr.phi "%e.0734.i.i.epil" (Ty.int 64) [("for.inc98.i.i.epil", (Operand.reg "%e.1.i.i.epil")),
                                       ("for.end100.i.i.loopexit.unr-lcssa", (Operand.reg "%e.0734.i.i.unr"))],
        Instr.phi "%epil.iter" (Ty.int 64) [("for.inc98.i.i.epil", (Operand.reg "%epil.iter.next")),
                                       ("for.end100.i.i.loopexit.unr-lcssa", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.icmp "%cmp88.i.i.epil" (IPred.slt) 64 (Operand.reg "%e.0734.i.i.epil") (Operand.imm (Const.int 64 0x00000000000f4240#64))
      ],
      term := Term.condbr (Operand.reg "%cmp88.i.i.epil") "if.then90.i.i.epil" "for.inc98.i.i.epil" },
    { name := "if.then90.i.i.epil",
      instrs := [
        Instr.binop "%mul91.i.i.epil" (BinOp.mul) 64 (Operand.reg "%e.0734.i.i.epil") (Operand.imm (Const.int 64 0x000000000000000a#64)),
        Instr.gep "%arrayidx92.i.i.epil" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.3735.i.i.epil"),
        Instr.load "%68" (Ty.int 8) (Operand.reg "%arrayidx92.i.i.epil"),
        Instr.zext "%conv93.i.i.epil" 8 64 (Operand.reg "%68"),
        Instr.binop "%sub94.i.i.epil" (BinOp.add) 64 (Operand.reg "%mul91.i.i.epil") (Operand.imm (Const.int 64 0xffffffffffffffd0#64)),
        Instr.binop "%add96.i.i.epil" (BinOp.add) 64 (Operand.reg "%sub94.i.i.epil") (Operand.reg "%conv93.i.i.epil")
      ],
      term := Term.br "for.inc98.i.i.epil" },
    { name := "for.inc98.i.i.epil",
      instrs := [
        Instr.phi "%e.1.i.i.epil" (Ty.int 64) [("if.then90.i.i.epil", (Operand.reg "%add96.i.i.epil")),
                                       ("for.body87.i.i.epil", (Operand.reg "%e.0734.i.i.epil"))],
        Instr.binop "%inc99.i.i.epil" (BinOp.add) 64 (Operand.reg "%i.3735.i.i.epil") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.binop "%epil.iter.next" (BinOp.add) 64 (Operand.reg "%epil.iter") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%epil.iter.cmp.not" (IPred.eq) 64 (Operand.reg "%epil.iter.next") (Operand.reg "%xtraiter")
      ],
      term := Term.condbr (Operand.reg "%epil.iter.cmp.not") "for.end100.i.i" "for.body87.i.i.epil" },
    { name := "for.end100.i.i",
      instrs := [
        Instr.phi "%e.0.lcssa.i.i" (Ty.int 64) [("if.end83.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.end100.i.i.loopexit.unr-lcssa", (Operand.reg "%e.1.i.i.lcssa.ph")),
                                       ("for.inc98.i.i.epil", (Operand.reg "%e.1.i.i.epil"))],
        Instr.binop "%sub102.i.i" (BinOp.sub) 64 (Operand.imm (Const.int 64 0x0000000000000000#64)) (Operand.reg "%e.0.lcssa.i.i"),
        Instr.select "%cond103.i.i" (Ty.int 64) (Operand.reg "%esign.0.i.i") (Operand.reg "%e.0.lcssa.i.i") (Operand.reg "%sub102.i.i")
      ],
      term := Term.br "if.end104.i.i" },
    { name := "if.end104.i.i",
      instrs := [
        Instr.phi "%lead.0721.i286.i" (Ty.int 64) [("for.end100.i.i", (Operand.reg "%lead.0721.ph.i.i")),
                                       ("for.end.thread.i.i", (Operand.reg "%lead.0721.i287.i"))],
        Instr.phi "%sticky.0714.i.i" (Ty.int 32) [("for.end100.i.i", (Operand.reg "%sticky.0716.ph.i.ph.i")),
                                       ("for.end.thread.i.i", (Operand.reg "%sticky.4.ph.i.i"))],
        Instr.phi "%topn.0711.i.i" (Ty.int 64) [("for.end100.i.i", (Operand.reg "%topn.0719.ph.i.ph.i")),
                                       ("for.end.thread.i.i", (Operand.reg "%topn.4.ph.i.i"))],
        Instr.phi "%top.0709.i.i" (Ty.int 64) [("for.end100.i.i", (Operand.reg "%top.0720.ph.i.ph.i")),
                                       ("for.end.thread.i.i", (Operand.reg "%top.4.ph.i.i"))],
        Instr.phi "%F.0705.i.i" (Ty.int 64) [("for.end100.i.i", (Operand.reg "%F.0722.ph.i.i")),
                                       ("for.end.thread.i.i", (Operand.reg "%F.3.ph.i.i"))],
        Instr.phi "%T.0703.i.i" (Ty.int 64) [("for.end100.i.i", (Operand.reg "%T.0723.ph.i.i")),
                                       ("for.end.thread.i.i", (Operand.reg "%T.2.ph.i.i"))],
        Instr.phi "%R.0701.i.i" (Ty.int 64) [("for.end100.i.i", (Operand.reg "%R.0724.ph.i.ph.i")),
                                       ("for.end.thread.i.i", (Operand.reg "%R.4.ph.i.i"))],
        Instr.phi "%exp10.0.i.i" (Ty.int 64) [("for.end100.i.i", (Operand.reg "%cond103.i.i")),
                                       ("for.end.thread.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.binop "%sub105.i.i" (BinOp.sub) 64 (Operand.reg "%exp10.0.i.i") (Operand.reg "%F.0705.i.i"),
        Instr.binop "%69" (BinOp.add) 64 (Operand.reg "%lead.0721.i286.i") (Operand.reg "%R.0701.i.i"),
        Instr.binop "%sub107.i.i" (BinOp.sub) 64 (Operand.reg "%T.0703.i.i") (Operand.reg "%69"),
        Instr.binop "%add108.i.i" (BinOp.add) 64 (Operand.reg "%sub107.i.i") (Operand.reg "%sub105.i.i"),
        Instr.binop "%sub109.i.i" (BinOp.add) 64 (Operand.reg "%R.0701.i.i") (Operand.imm (Const.int 64 0xffffffffffffffff#64)),
        Instr.binop "%add110.i.i" (BinOp.add) 64 (Operand.reg "%sub109.i.i") (Operand.reg "%add108.i.i"),
        Instr.icmp "%cmp111.i.i" (IPred.sgt) 64 (Operand.reg "%add110.i.i") (Operand.imm (Const.int 64 0x0000000000000134#64))
      ],
      term := Term.condbr (Operand.reg "%cmp111.i.i") "if.then113.i.i" "if.end120.i.i" },
    { name := "if.then113.i.i",
      instrs := [
        Instr.select "%spec.select694.i.i" Ty.double (Operand.reg "%cmp1.i") (Operand.imm (Const.float 0xfff0000000000000#64)) (Operand.imm (Const.float 0x7ff0000000000000#64))
      ],
      term := Term.br "if.end291" },
    { name := "if.end120.i.i",
      instrs := [
        Instr.icmp "%cmp121.i.i" (IPred.slt) 64 (Operand.reg "%add110.i.i") (Operand.imm (Const.int 64 0xfffffffffffffebc#64))
      ],
      term := Term.condbr (Operand.reg "%cmp121.i.i") "if.then123.i.i" "if.end126.i.i" },
    { name := "if.then123.i.i",
      instrs := [
        Instr.select "%cond125.i.i" Ty.double (Operand.reg "%cmp1.i") (Operand.imm (Const.float 0x8000000000000000#64)) (Operand.imm (Const.float 0x0000000000000000#64))
      ],
      term := Term.br "if.end291" },
    { name := "if.end126.i.i",
      instrs := [
        Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000620#64))),
                             (Ty.ptr, (Operand.reg "%v.i.i"))],
        Instr.gep "%sticky127.i.i" (Ty.int 8) (Operand.reg "%v.i.i") (Operand.imm (Const.int 64 0x0000000000000618#64)),
        Instr.store (Ty.int 32) (Operand.reg "%sticky.0714.i.i") (Operand.reg "%sticky127.i.i"),
        Instr.gep "%S128.i.i" (Ty.int 8) (Operand.reg "%v.i.i") (Operand.imm (Const.int 64 0x0000000000000610#64)),
        Instr.store (Ty.int 64) (Operand.reg "%add108.i.i") (Operand.reg "%S128.i.i"),
        Instr.gep "%n.i.i.i" (Ty.int 8) (Operand.reg "%v.i.i") (Operand.imm (Const.int 64 0x0000000000000300#64)),
        Instr.icmp "%cmp130737.not.i.i" (IPred.eq) 64 (Operand.reg "%R.0701.i.i") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%cmp130737.not.i.i") "if.end151.i.i.sink.split" "for.body132.i.i" },
    { name := "for.cond.cleanup.i.i",
      instrs := [
        Instr.store (Ty.int 32) (Operand.reg "%78") (Operand.reg "%n.i.i.i"),
        Instr.icmp "%tobool147.not.i.i" (IPred.eq) 32 (Operand.reg "%cn.1.i.i") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%tobool147.not.i.i") "if.end151.i.i" "if.then148.i.i" },
    { name := "for.body132.i.i",
      instrs := [
        Instr.phi "%j.0740.i.i" (Ty.int 64) [("for.inc143.i.i", (Operand.reg "%inc144.i.i")),
                                       ("if.end126.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.phi "%cn.0739.i.i" (Ty.int 32) [("for.inc143.i.i", (Operand.reg "%cn.1.i.i")),
                                       ("if.end126.i.i", (Operand.imm (Const.int 32 0x00000000#32)))],
        Instr.phi "%chunk.0738.i.i" (Ty.int 64) [("for.inc143.i.i", (Operand.reg "%chunk.1.i.i")),
                                       ("if.end126.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.phi "%70" (Ty.int 32) [("for.inc143.i.i", (Operand.reg "%78")),
                                       ("if.end126.i.i", (Operand.imm (Const.int 32 0x00000000#32)))],
        Instr.binop "%mul133.i.i" (BinOp.mul) 64 (Operand.reg "%chunk.0738.i.i") (Operand.imm (Const.int 64 0x000000000000000a#64)),
        Instr.gep "%arrayidx134.i.i" (Ty.int 8) (Operand.reg "%dig.i.i") (Operand.reg "%j.0740.i.i"),
        Instr.load "%71" (Ty.int 8) (Operand.reg "%arrayidx134.i.i"),
        Instr.zext "%conv135.i.i" 8 64 (Operand.reg "%71"),
        Instr.binop "%add136.i.i" (BinOp.add) 64 (Operand.reg "%mul133.i.i") (Operand.reg "%conv135.i.i"),
        Instr.binop "%inc137.i.i" (BinOp.add) 32 (Operand.reg "%cn.0739.i.i") (Operand.imm (Const.int 32 0x00000001#32)),
        Instr.icmp "%cmp138.i.i" (IPred.eq) 32 (Operand.reg "%inc137.i.i") (Operand.imm (Const.int 32 0x00000013#32))
      ],
      term := Term.condbr (Operand.reg "%cmp138.i.i") "if.then140.i.i" "for.inc143.i.i" },
    { name := "if.then140.i.i",
      instrs := [
        Instr.zext "%conv.i.i.i" 64 128 (Operand.reg "%add136.i.i"),
        Instr.icmp "%cmp28.i.i.i" (IPred.sgt) 32 (Operand.reg "%70") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%cmp28.i.i.i") "for.body.lr.ph.i.i.i" "while.cond.preheader.i.i.i" },
    { name := "for.body.lr.ph.i.i.i",
      instrs := [
        Instr.zext "%wide.trip.count.i.i.i" 32 64 (Operand.reg "%70"),
        Instr.binop "%xtraiter1043" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
        Instr.icmp "%72" (IPred.ult) 32 (Operand.reg "%70") (Operand.imm (Const.int 32 0x00000004#32))
      ],
      term := Term.condbr (Operand.reg "%72") "while.cond.preheader.i.i.i.loopexit.unr-lcssa" "for.body.lr.ph.i.i.i.new" },
    { name := "for.body.lr.ph.i.i.i.new",
      instrs := [
        Instr.binop "%unroll_iter1047" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i.i.i") (Operand.imm (Const.int 64 0x000000007ffffffc#64))
      ],
      term := Term.br "for.body.i.i.i" },
    { name := "while.cond.preheader.i.i.i.loopexit.unr-lcssa",
      instrs := [
        Instr.phi "%shr.i.i.i.lcssa.ph" (Ty.int 128) [("for.body.lr.ph.i.i.i", (Operand.imm Const.poison)),
                                       ("for.body.i.i.i", (Operand.reg "%shr.i.i.i.3"))],
        Instr.phi "%indvars.iv.i.i.i.unr" (Ty.int 64) [("for.body.lr.ph.i.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i.i.i", (Operand.reg "%indvars.iv.next.i.i.i.3"))],
        Instr.phi "%carry.029.i.i.i.unr" (Ty.int 128) [("for.body.lr.ph.i.i.i", (Operand.reg "%conv.i.i.i")),
                                       ("for.body.i.i.i", (Operand.reg "%shr.i.i.i.3"))],
        Instr.icmp "%lcmp.mod1045.not" (IPred.eq) 64 (Operand.reg "%xtraiter1043") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%lcmp.mod1045.not") "while.cond.preheader.i.i.i" "for.body.i.i.i.epil" },
    { name := "for.body.i.i.i.epil",
      instrs := [
        Instr.phi "%indvars.iv.i.i.i.epil" (Ty.int 64) [("for.body.i.i.i.epil", (Operand.reg "%indvars.iv.next.i.i.i.epil")),
                                       ("while.cond.preheader.i.i.i.loopexit.unr-lcssa", (Operand.reg "%indvars.iv.i.i.i.unr"))],
        Instr.phi "%carry.029.i.i.i.epil" (Ty.int 128) [("for.body.i.i.i.epil", (Operand.reg "%shr.i.i.i.epil")),
                                       ("while.cond.preheader.i.i.i.loopexit.unr-lcssa", (Operand.reg "%carry.029.i.i.i.unr"))],
        Instr.phi "%epil.iter1044" (Ty.int 64) [("for.body.i.i.i.epil", (Operand.reg "%epil.iter1044.next")),
                                       ("while.cond.preheader.i.i.i.loopexit.unr-lcssa", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.gep "%arrayidx.i.i.i.epil" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.i.i.i.epil"),
        Instr.load "%73" (Ty.int 64) (Operand.reg "%arrayidx.i.i.i.epil"),
        Instr.zext "%conv2.i.i.i.epil" 64 128 (Operand.reg "%73"),
        Instr.binop "%mul.i.i.i.epil" (BinOp.mul) 128 (Operand.reg "%conv2.i.i.i.epil") (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
        Instr.binop "%add4.i.i.i.epil" (BinOp.add) 128 (Operand.reg "%mul.i.i.i.epil") (Operand.reg "%carry.029.i.i.i.epil"),
        Instr.trunc "%conv5.i.i.i.epil" 128 64 (Operand.reg "%add4.i.i.i.epil"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i.i.epil") (Operand.reg "%arrayidx.i.i.i.epil"),
        Instr.binop "%shr.i.i.i.epil" (BinOp.lshr) 128 (Operand.reg "%add4.i.i.i.epil") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.i.i.epil" (BinOp.add) 64 (Operand.reg "%indvars.iv.i.i.i.epil") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.binop "%epil.iter1044.next" (BinOp.add) 64 (Operand.reg "%epil.iter1044") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%epil.iter1044.cmp.not" (IPred.eq) 64 (Operand.reg "%epil.iter1044.next") (Operand.reg "%xtraiter1043")
      ],
      term := Term.condbr (Operand.reg "%epil.iter1044.cmp.not") "while.cond.preheader.i.i.i" "for.body.i.i.i.epil" },
    { name := "while.cond.preheader.i.i.i",
      instrs := [
        Instr.phi "%carry.0.lcssa.i.i.i" (Ty.int 128) [("if.then140.i.i", (Operand.reg "%conv.i.i.i")),
                                       ("while.cond.preheader.i.i.i.loopexit.unr-lcssa", (Operand.reg "%shr.i.i.i.lcssa.ph")),
                                       ("for.body.i.i.i.epil", (Operand.reg "%shr.i.i.i.epil"))],
        Instr.icmp "%tobool.not31.i.i.i" (IPred.eq) 128 (Operand.reg "%carry.0.lcssa.i.i.i") (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))
      ],
      term := Term.condbr (Operand.reg "%tobool.not31.i.i.i") "for.inc143.i.i" "while.body.us.i.i.i" },
    { name := "while.body.us.i.i.i",
      instrs := [
        Instr.trunc "%conv9.us.i.i.i" 128 64 (Operand.reg "%carry.0.lcssa.i.i.i"),
        Instr.binop "%inc12.us.i.i.i" (BinOp.add) 32 (Operand.reg "%70") (Operand.imm (Const.int 32 0x00000001#32)),
        Instr.sext "%idxprom13.us.i.i.i" 32 64 (Operand.reg "%70"),
        Instr.gep "%arrayidx14.us.i.i.i" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%idxprom13.us.i.i.i"),
        Instr.store (Ty.int 64) (Operand.reg "%conv9.us.i.i.i") (Operand.reg "%arrayidx14.us.i.i.i")
      ],
      term := Term.br "for.inc143.i.i" },
    { name := "for.body.i.i.i",
      instrs := [
        Instr.phi "%indvars.iv.i.i.i" (Ty.int 64) [("for.body.lr.ph.i.i.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i.i.i", (Operand.reg "%indvars.iv.next.i.i.i.3"))],
        Instr.phi "%carry.029.i.i.i" (Ty.int 128) [("for.body.lr.ph.i.i.i.new", (Operand.reg "%conv.i.i.i")),
                                       ("for.body.i.i.i", (Operand.reg "%shr.i.i.i.3"))],
        Instr.phi "%niter1048" (Ty.int 64) [("for.body.lr.ph.i.i.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i.i.i", (Operand.reg "%niter1048.next.3"))],
        Instr.gep "%arrayidx.i.i.i" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.i.i.i"),
        Instr.load "%74" (Ty.int 64) (Operand.reg "%arrayidx.i.i.i"),
        Instr.zext "%conv2.i.i.i" 64 128 (Operand.reg "%74"),
        Instr.binop "%mul.i.i.i" (BinOp.mul) 128 (Operand.reg "%conv2.i.i.i") (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
        Instr.binop "%add4.i.i.i" (BinOp.add) 128 (Operand.reg "%mul.i.i.i") (Operand.reg "%carry.029.i.i.i"),
        Instr.trunc "%conv5.i.i.i" 128 64 (Operand.reg "%add4.i.i.i"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i.i") (Operand.reg "%arrayidx.i.i.i"),
        Instr.binop "%shr.i.i.i" (BinOp.lshr) 128 (Operand.reg "%add4.i.i.i") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.i.i" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.gep "%arrayidx.i.i.i.1" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.next.i.i.i"),
        Instr.load "%75" (Ty.int 64) (Operand.reg "%arrayidx.i.i.i.1"),
        Instr.zext "%conv2.i.i.i.1" 64 128 (Operand.reg "%75"),
        Instr.binop "%mul.i.i.i.1" (BinOp.mul) 128 (Operand.reg "%conv2.i.i.i.1") (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
        Instr.binop "%add4.i.i.i.1" (BinOp.add) 128 (Operand.reg "%mul.i.i.i.1") (Operand.reg "%shr.i.i.i"),
        Instr.trunc "%conv5.i.i.i.1" 128 64 (Operand.reg "%add4.i.i.i.1"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i.i.1") (Operand.reg "%arrayidx.i.i.i.1"),
        Instr.binop "%shr.i.i.i.1" (BinOp.lshr) 128 (Operand.reg "%add4.i.i.i.1") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.i.i.1" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i.i") (Operand.imm (Const.int 64 0x0000000000000002#64)),
        Instr.gep "%arrayidx.i.i.i.2" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.next.i.i.i.1"),
        Instr.load "%76" (Ty.int 64) (Operand.reg "%arrayidx.i.i.i.2"),
        Instr.zext "%conv2.i.i.i.2" 64 128 (Operand.reg "%76"),
        Instr.binop "%mul.i.i.i.2" (BinOp.mul) 128 (Operand.reg "%conv2.i.i.i.2") (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
        Instr.binop "%add4.i.i.i.2" (BinOp.add) 128 (Operand.reg "%mul.i.i.i.2") (Operand.reg "%shr.i.i.i.1"),
        Instr.trunc "%conv5.i.i.i.2" 128 64 (Operand.reg "%add4.i.i.i.2"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i.i.2") (Operand.reg "%arrayidx.i.i.i.2"),
        Instr.binop "%shr.i.i.i.2" (BinOp.lshr) 128 (Operand.reg "%add4.i.i.i.2") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.i.i.2" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
        Instr.gep "%arrayidx.i.i.i.3" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.next.i.i.i.2"),
        Instr.load "%77" (Ty.int 64) (Operand.reg "%arrayidx.i.i.i.3"),
        Instr.zext "%conv2.i.i.i.3" 64 128 (Operand.reg "%77"),
        Instr.binop "%mul.i.i.i.3" (BinOp.mul) 128 (Operand.reg "%conv2.i.i.i.3") (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
        Instr.binop "%add4.i.i.i.3" (BinOp.add) 128 (Operand.reg "%mul.i.i.i.3") (Operand.reg "%shr.i.i.i.2"),
        Instr.trunc "%conv5.i.i.i.3" 128 64 (Operand.reg "%add4.i.i.i.3"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i.i.3") (Operand.reg "%arrayidx.i.i.i.3"),
        Instr.binop "%shr.i.i.i.3" (BinOp.lshr) 128 (Operand.reg "%add4.i.i.i.3") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.i.i.3" (BinOp.add) 64 (Operand.reg "%indvars.iv.i.i.i") (Operand.imm (Const.int 64 0x0000000000000004#64)),
        Instr.binop "%niter1048.next.3" (BinOp.add) 64 (Operand.reg "%niter1048") (Operand.imm (Const.int 64 0x0000000000000004#64)),
        Instr.icmp "%niter1048.ncmp.3" (IPred.eq) 64 (Operand.reg "%niter1048.next.3") (Operand.reg "%unroll_iter1047")
      ],
      term := Term.condbr (Operand.reg "%niter1048.ncmp.3") "while.cond.preheader.i.i.i.loopexit.unr-lcssa" "for.body.i.i.i" },
    { name := "for.inc143.i.i",
      instrs := [
        Instr.phi "%78" (Ty.int 32) [("for.body132.i.i", (Operand.reg "%70")),
                                       ("while.cond.preheader.i.i.i", (Operand.reg "%70")),
                                       ("while.body.us.i.i.i", (Operand.reg "%inc12.us.i.i.i"))],
        Instr.phi "%chunk.1.i.i" (Ty.int 64) [("for.body132.i.i", (Operand.reg "%add136.i.i")),
                                       ("while.cond.preheader.i.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("while.body.us.i.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.phi "%cn.1.i.i" (Ty.int 32) [("for.body132.i.i", (Operand.reg "%inc137.i.i")),
                                       ("while.cond.preheader.i.i.i", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("while.body.us.i.i.i", (Operand.imm (Const.int 32 0x00000000#32)))],
        Instr.binop "%inc144.i.i" (BinOp.add) 64 (Operand.reg "%j.0740.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%exitcond780.not.i.i" (IPred.eq) 64 (Operand.reg "%inc144.i.i") (Operand.reg "%R.0701.i.i")
      ],
      term := Term.condbr (Operand.reg "%exitcond780.not.i.i") "for.cond.cleanup.i.i" "for.body132.i.i" },
    { name := "if.then148.i.i",
      instrs := [
        Instr.zext "%conv.i514.i.i" 64 128 (Operand.reg "%chunk.1.i.i"),
        Instr.icmp "%cmp28.i516.i.i" (IPred.sgt) 32 (Operand.reg "%78") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%cmp28.i516.i.i") "for.body.lr.ph.i525.i.i" "while.cond.preheader.i517.i.i" },
    { name := "for.body.lr.ph.i525.i.i",
      instrs := [
        Instr.sext "%idxprom.i.i" 32 64 (Operand.reg "%cn.1.i.i"),
        Instr.gep "%arrayidx150.i.i" (Ty.int 64) (Operand.global "@NUMF_EL1_P10") (Operand.reg "%idxprom.i.i"),
        Instr.load "%79" (Ty.int 64) (Operand.reg "%arrayidx150.i.i"),
        Instr.zext "%conv3.i.i.i" 64 128 (Operand.reg "%79"),
        Instr.zext "%wide.trip.count.i526.i.i" 32 64 (Operand.reg "%78"),
        Instr.binop "%xtraiter1049" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i526.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
        Instr.icmp "%80" (IPred.ult) 32 (Operand.reg "%78") (Operand.imm (Const.int 32 0x00000004#32))
      ],
      term := Term.condbr (Operand.reg "%80") "while.cond.preheader.i517.i.i.loopexit.unr-lcssa" "for.body.lr.ph.i525.i.i.new" },
    { name := "for.body.lr.ph.i525.i.i.new",
      instrs := [
        Instr.binop "%unroll_iter1053" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i526.i.i") (Operand.imm (Const.int 64 0x000000007ffffffc#64))
      ],
      term := Term.br "for.body.i527.i.i" },
    { name := "while.cond.preheader.i517.i.i.loopexit.unr-lcssa",
      instrs := [
        Instr.phi "%shr.i535.i.i.lcssa.ph" (Ty.int 128) [("for.body.lr.ph.i525.i.i", (Operand.imm Const.poison)),
                                       ("for.body.i527.i.i", (Operand.reg "%shr.i535.i.i.3"))],
        Instr.phi "%indvars.iv.i528.i.i.unr" (Ty.int 64) [("for.body.lr.ph.i525.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i527.i.i", (Operand.reg "%indvars.iv.next.i536.i.i.3"))],
        Instr.phi "%carry.029.i529.i.i.unr" (Ty.int 128) [("for.body.lr.ph.i525.i.i", (Operand.reg "%conv.i514.i.i")),
                                       ("for.body.i527.i.i", (Operand.reg "%shr.i535.i.i.3"))],
        Instr.icmp "%lcmp.mod1051.not" (IPred.eq) 64 (Operand.reg "%xtraiter1049") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%lcmp.mod1051.not") "while.cond.preheader.i517.i.i" "for.body.i527.i.i.epil" },
    { name := "for.body.i527.i.i.epil",
      instrs := [
        Instr.phi "%indvars.iv.i528.i.i.epil" (Ty.int 64) [("for.body.i527.i.i.epil", (Operand.reg "%indvars.iv.next.i536.i.i.epil")),
                                       ("while.cond.preheader.i517.i.i.loopexit.unr-lcssa", (Operand.reg "%indvars.iv.i528.i.i.unr"))],
        Instr.phi "%carry.029.i529.i.i.epil" (Ty.int 128) [("for.body.i527.i.i.epil", (Operand.reg "%shr.i535.i.i.epil")),
                                       ("while.cond.preheader.i517.i.i.loopexit.unr-lcssa", (Operand.reg "%carry.029.i529.i.i.unr"))],
        Instr.phi "%epil.iter1050" (Ty.int 64) [("for.body.i527.i.i.epil", (Operand.reg "%epil.iter1050.next")),
                                       ("while.cond.preheader.i517.i.i.loopexit.unr-lcssa", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.gep "%arrayidx.i530.i.i.epil" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.i528.i.i.epil"),
        Instr.load "%81" (Ty.int 64) (Operand.reg "%arrayidx.i530.i.i.epil"),
        Instr.zext "%conv2.i531.i.i.epil" 64 128 (Operand.reg "%81"),
        Instr.binop "%mul.i532.i.i.epil" (BinOp.mul) 128 (Operand.reg "%conv2.i531.i.i.epil") (Operand.reg "%conv3.i.i.i"),
        Instr.binop "%add4.i533.i.i.epil" (BinOp.add) 128 (Operand.reg "%mul.i532.i.i.epil") (Operand.reg "%carry.029.i529.i.i.epil"),
        Instr.trunc "%conv5.i534.i.i.epil" 128 64 (Operand.reg "%add4.i533.i.i.epil"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i534.i.i.epil") (Operand.reg "%arrayidx.i530.i.i.epil"),
        Instr.binop "%shr.i535.i.i.epil" (BinOp.lshr) 128 (Operand.reg "%add4.i533.i.i.epil") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i536.i.i.epil" (BinOp.add) 64 (Operand.reg "%indvars.iv.i528.i.i.epil") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.binop "%epil.iter1050.next" (BinOp.add) 64 (Operand.reg "%epil.iter1050") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%epil.iter1050.cmp.not" (IPred.eq) 64 (Operand.reg "%epil.iter1050.next") (Operand.reg "%xtraiter1049")
      ],
      term := Term.condbr (Operand.reg "%epil.iter1050.cmp.not") "while.cond.preheader.i517.i.i" "for.body.i527.i.i.epil" },
    { name := "while.cond.preheader.i517.i.i",
      instrs := [
        Instr.phi "%carry.0.lcssa.i518.i.i" (Ty.int 128) [("if.then148.i.i", (Operand.reg "%conv.i514.i.i")),
                                       ("while.cond.preheader.i517.i.i.loopexit.unr-lcssa", (Operand.reg "%shr.i535.i.i.lcssa.ph")),
                                       ("for.body.i527.i.i.epil", (Operand.reg "%shr.i535.i.i.epil"))],
        Instr.icmp "%tobool.not31.i519.i.i" (IPred.eq) 128 (Operand.reg "%carry.0.lcssa.i518.i.i") (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))
      ],
      term := Term.condbr (Operand.reg "%tobool.not31.i519.i.i") "if.end151.i.i" "while.body.us.i520.i.i" },
    { name := "while.body.us.i520.i.i",
      instrs := [
        Instr.trunc "%conv9.us.i521.i.i" 128 64 (Operand.reg "%carry.0.lcssa.i518.i.i"),
        Instr.binop "%inc12.us.i522.i.i" (BinOp.add) 32 (Operand.reg "%78") (Operand.imm (Const.int 32 0x00000001#32)),
        Instr.sext "%idxprom13.us.i523.i.i" 32 64 (Operand.reg "%78"),
        Instr.gep "%arrayidx14.us.i524.i.i" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%idxprom13.us.i523.i.i"),
        Instr.store (Ty.int 64) (Operand.reg "%conv9.us.i521.i.i") (Operand.reg "%arrayidx14.us.i524.i.i")
      ],
      term := Term.br "if.end151.i.i.sink.split" },
    { name := "for.body.i527.i.i",
      instrs := [
        Instr.phi "%indvars.iv.i528.i.i" (Ty.int 64) [("for.body.lr.ph.i525.i.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i527.i.i", (Operand.reg "%indvars.iv.next.i536.i.i.3"))],
        Instr.phi "%carry.029.i529.i.i" (Ty.int 128) [("for.body.lr.ph.i525.i.i.new", (Operand.reg "%conv.i514.i.i")),
                                       ("for.body.i527.i.i", (Operand.reg "%shr.i535.i.i.3"))],
        Instr.phi "%niter1054" (Ty.int 64) [("for.body.lr.ph.i525.i.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i527.i.i", (Operand.reg "%niter1054.next.3"))],
        Instr.gep "%arrayidx.i530.i.i" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.i528.i.i"),
        Instr.load "%82" (Ty.int 64) (Operand.reg "%arrayidx.i530.i.i"),
        Instr.zext "%conv2.i531.i.i" 64 128 (Operand.reg "%82"),
        Instr.binop "%mul.i532.i.i" (BinOp.mul) 128 (Operand.reg "%conv2.i531.i.i") (Operand.reg "%conv3.i.i.i"),
        Instr.binop "%add4.i533.i.i" (BinOp.add) 128 (Operand.reg "%mul.i532.i.i") (Operand.reg "%carry.029.i529.i.i"),
        Instr.trunc "%conv5.i534.i.i" 128 64 (Operand.reg "%add4.i533.i.i"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i534.i.i") (Operand.reg "%arrayidx.i530.i.i"),
        Instr.binop "%shr.i535.i.i" (BinOp.lshr) 128 (Operand.reg "%add4.i533.i.i") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i536.i.i" (BinOp.or) 64 (Operand.reg "%indvars.iv.i528.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.gep "%arrayidx.i530.i.i.1" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.next.i536.i.i"),
        Instr.load "%83" (Ty.int 64) (Operand.reg "%arrayidx.i530.i.i.1"),
        Instr.zext "%conv2.i531.i.i.1" 64 128 (Operand.reg "%83"),
        Instr.binop "%mul.i532.i.i.1" (BinOp.mul) 128 (Operand.reg "%conv2.i531.i.i.1") (Operand.reg "%conv3.i.i.i"),
        Instr.binop "%add4.i533.i.i.1" (BinOp.add) 128 (Operand.reg "%mul.i532.i.i.1") (Operand.reg "%shr.i535.i.i"),
        Instr.trunc "%conv5.i534.i.i.1" 128 64 (Operand.reg "%add4.i533.i.i.1"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i534.i.i.1") (Operand.reg "%arrayidx.i530.i.i.1"),
        Instr.binop "%shr.i535.i.i.1" (BinOp.lshr) 128 (Operand.reg "%add4.i533.i.i.1") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i536.i.i.1" (BinOp.or) 64 (Operand.reg "%indvars.iv.i528.i.i") (Operand.imm (Const.int 64 0x0000000000000002#64)),
        Instr.gep "%arrayidx.i530.i.i.2" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.next.i536.i.i.1"),
        Instr.load "%84" (Ty.int 64) (Operand.reg "%arrayidx.i530.i.i.2"),
        Instr.zext "%conv2.i531.i.i.2" 64 128 (Operand.reg "%84"),
        Instr.binop "%mul.i532.i.i.2" (BinOp.mul) 128 (Operand.reg "%conv2.i531.i.i.2") (Operand.reg "%conv3.i.i.i"),
        Instr.binop "%add4.i533.i.i.2" (BinOp.add) 128 (Operand.reg "%mul.i532.i.i.2") (Operand.reg "%shr.i535.i.i.1"),
        Instr.trunc "%conv5.i534.i.i.2" 128 64 (Operand.reg "%add4.i533.i.i.2"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i534.i.i.2") (Operand.reg "%arrayidx.i530.i.i.2"),
        Instr.binop "%shr.i535.i.i.2" (BinOp.lshr) 128 (Operand.reg "%add4.i533.i.i.2") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i536.i.i.2" (BinOp.or) 64 (Operand.reg "%indvars.iv.i528.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
        Instr.gep "%arrayidx.i530.i.i.3" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.next.i536.i.i.2"),
        Instr.load "%85" (Ty.int 64) (Operand.reg "%arrayidx.i530.i.i.3"),
        Instr.zext "%conv2.i531.i.i.3" 64 128 (Operand.reg "%85"),
        Instr.binop "%mul.i532.i.i.3" (BinOp.mul) 128 (Operand.reg "%conv2.i531.i.i.3") (Operand.reg "%conv3.i.i.i"),
        Instr.binop "%add4.i533.i.i.3" (BinOp.add) 128 (Operand.reg "%mul.i532.i.i.3") (Operand.reg "%shr.i535.i.i.2"),
        Instr.trunc "%conv5.i534.i.i.3" 128 64 (Operand.reg "%add4.i533.i.i.3"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i534.i.i.3") (Operand.reg "%arrayidx.i530.i.i.3"),
        Instr.binop "%shr.i535.i.i.3" (BinOp.lshr) 128 (Operand.reg "%add4.i533.i.i.3") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i536.i.i.3" (BinOp.add) 64 (Operand.reg "%indvars.iv.i528.i.i") (Operand.imm (Const.int 64 0x0000000000000004#64)),
        Instr.binop "%niter1054.next.3" (BinOp.add) 64 (Operand.reg "%niter1054") (Operand.imm (Const.int 64 0x0000000000000004#64)),
        Instr.icmp "%niter1054.ncmp.3" (IPred.eq) 64 (Operand.reg "%niter1054.next.3") (Operand.reg "%unroll_iter1053")
      ],
      term := Term.condbr (Operand.reg "%niter1054.ncmp.3") "while.cond.preheader.i517.i.i.loopexit.unr-lcssa" "for.body.i527.i.i" },
    { name := "if.end151.i.i.sink.split",
      instrs := [
        Instr.phi "%inc12.us.i522.i.i.sink" (Ty.int 32) [("while.body.us.i520.i.i", (Operand.reg "%inc12.us.i522.i.i")),
                                       ("if.end126.i.i", (Operand.imm (Const.int 32 0x00000000#32)))],
        Instr.store (Ty.int 32) (Operand.reg "%inc12.us.i522.i.i.sink") (Operand.reg "%n.i.i.i")
      ],
      term := Term.br "if.end151.i.i" },
    { name := "if.end151.i.i",
      instrs := [
        Instr.gep "%pow.i.i" (Ty.int 8) (Operand.reg "%v.i.i") (Operand.imm (Const.int 64 0x0000000000000308#64)),
        Instr.store (Ty.int 64) (Operand.imm (Const.int 64 0x0000000000000001#64)) (Operand.reg "%pow.i.i"),
        Instr.gep "%n.i539.i.i" (Ty.int 8) (Operand.reg "%v.i.i") (Operand.imm (Const.int 64 0x0000000000000608#64)),
        Instr.store (Ty.int 32) (Operand.imm (Const.int 32 0x00000001#32)) (Operand.reg "%n.i539.i.i"),
        Instr.icmp "%tobool152.not.i.i" (IPred.eq) 32 (Operand.reg "%sticky.0714.i.i") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%tobool152.not.i.i") "if.else164.i.i" "if.then153.i.i" },
    { name := "if.then153.i.i",
      instrs := [
        Instr.binop "%sub154.i.i" (BinOp.sub) 64 (Operand.imm (Const.int 64 0x0000000000000000#64)) (Operand.reg "%add108.i.i"),
        Instr.icmp "%cmp155746.i.i" (IPred.sgt) 64 (Operand.reg "%sub154.i.i") (Operand.imm (Const.int 64 0x000000000000001a#64))
      ],
      term := Term.condbr (Operand.reg "%cmp155746.i.i") "while.body.i.i" "while.end.thread.i.i" },
    { name := "while.body.i.i",
      instrs := [
        Instr.phi "%k.0748.i.i" (Ty.int 64) [("stk_mul_u64.exit.i.i", (Operand.reg "%sub158.i.i")),
                                       ("if.then153.i.i", (Operand.reg "%sub154.i.i"))],
        Instr.phi "%inc12.us.i.i745747.i.i" (Ty.int 32) [("stk_mul_u64.exit.i.i", (Operand.reg "%inc12.us.i.i744.i.i")),
                                       ("if.then153.i.i", (Operand.imm (Const.int 32 0x00000001#32)))],
        Instr.icmp "%cmp28.i.i.i.i" (IPred.sgt) 32 (Operand.reg "%inc12.us.i.i745747.i.i") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%cmp28.i.i.i.i") "for.body.lr.ph.i.i.i.i" "stk_mul_u64.exit.i.i" },
    { name := "for.body.lr.ph.i.i.i.i",
      instrs := [
        Instr.zext "%wide.trip.count.i.i.i.i" 32 64 (Operand.reg "%inc12.us.i.i745747.i.i"),
        Instr.binop "%xtraiter1055" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i.i.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
        Instr.icmp "%86" (IPred.ult) 32 (Operand.reg "%inc12.us.i.i745747.i.i") (Operand.imm (Const.int 32 0x00000004#32))
      ],
      term := Term.condbr (Operand.reg "%86") "while.cond.preheader.i.i.i.i.unr-lcssa" "for.body.lr.ph.i.i.i.i.new" },
    { name := "for.body.lr.ph.i.i.i.i.new",
      instrs := [
        Instr.binop "%unroll_iter1060" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i.i.i.i") (Operand.imm (Const.int 64 0x000000007ffffffc#64))
      ],
      term := Term.br "for.body.i.i.i.i" },
    { name := "while.cond.preheader.i.i.i.i.unr-lcssa.loopexit",
      instrs := [
        Instr.trunc "%extract.t1091" 128 64 (Operand.reg "%shr.i.i.i.i.3")
      ],
      term := Term.br "while.cond.preheader.i.i.i.i.unr-lcssa" },
    { name := "while.cond.preheader.i.i.i.i.unr-lcssa",
      instrs := [
        Instr.phi "%add4.i.i.i.i.lcssa.ph" (Ty.int 128) [("for.body.lr.ph.i.i.i.i", (Operand.imm Const.poison)),
                                       ("while.cond.preheader.i.i.i.i.unr-lcssa.loopexit", (Operand.reg "%add4.i.i.i.i.3"))],
        Instr.phi "%shr.i.i.i.i.lcssa.ph.off0" (Ty.int 64) [("for.body.lr.ph.i.i.i.i", (Operand.imm Const.poison)),
                                       ("while.cond.preheader.i.i.i.i.unr-lcssa.loopexit", (Operand.reg "%extract.t1091"))],
        Instr.phi "%indvars.iv.i.i.i.i.unr" (Ty.int 64) [("for.body.lr.ph.i.i.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("while.cond.preheader.i.i.i.i.unr-lcssa.loopexit", (Operand.reg "%indvars.iv.next.i.i.i.i.3"))],
        Instr.phi "%carry.029.i.i.i.i.unr" (Ty.int 128) [("for.body.lr.ph.i.i.i.i", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
                                       ("while.cond.preheader.i.i.i.i.unr-lcssa.loopexit", (Operand.reg "%shr.i.i.i.i.3"))],
        Instr.icmp "%lcmp.mod1057.not" (IPred.eq) 64 (Operand.reg "%xtraiter1055") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%lcmp.mod1057.not") "while.cond.preheader.i.i.i.i" "for.body.i.i.i.i.epil" },
    { name := "for.body.i.i.i.i.epil",
      instrs := [
        Instr.phi "%indvars.iv.i.i.i.i.epil" (Ty.int 64) [("for.body.i.i.i.i.epil", (Operand.reg "%indvars.iv.next.i.i.i.i.epil")),
                                       ("while.cond.preheader.i.i.i.i.unr-lcssa", (Operand.reg "%indvars.iv.i.i.i.i.unr"))],
        Instr.phi "%carry.029.i.i.i.i.epil" (Ty.int 128) [("for.body.i.i.i.i.epil", (Operand.reg "%shr.i.i.i.i.epil")),
                                       ("while.cond.preheader.i.i.i.i.unr-lcssa", (Operand.reg "%carry.029.i.i.i.i.unr"))],
        Instr.phi "%epil.iter1056" (Ty.int 64) [("for.body.i.i.i.i.epil", (Operand.reg "%epil.iter1056.next")),
                                       ("while.cond.preheader.i.i.i.i.unr-lcssa", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.gep "%arrayidx.i.i.i.i.epil" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%indvars.iv.i.i.i.i.epil"),
        Instr.load "%87" (Ty.int 64) (Operand.reg "%arrayidx.i.i.i.i.epil"),
        Instr.zext "%conv2.i.i.i.i.epil" 64 128 (Operand.reg "%87"),
        Instr.binop "%mul.i.i.i.i.epil" (BinOp.mul) 128 (Operand.reg "%conv2.i.i.i.i.epil") (Operand.imm (Const.int 128 0x00000000000000006765c793fa10079d#128)),
        Instr.binop "%add4.i.i.i.i.epil" (BinOp.add) 128 (Operand.reg "%mul.i.i.i.i.epil") (Operand.reg "%carry.029.i.i.i.i.epil"),
        Instr.trunc "%conv5.i.i.i.i.epil" 128 64 (Operand.reg "%add4.i.i.i.i.epil"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i.i.i.epil") (Operand.reg "%arrayidx.i.i.i.i.epil"),
        Instr.binop "%shr.i.i.i.i.epil" (BinOp.lshr) 128 (Operand.reg "%add4.i.i.i.i.epil") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.i.i.i.epil" (BinOp.add) 64 (Operand.reg "%indvars.iv.i.i.i.i.epil") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.binop "%epil.iter1056.next" (BinOp.add) 64 (Operand.reg "%epil.iter1056") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%epil.iter1056.cmp.not" (IPred.eq) 64 (Operand.reg "%epil.iter1056.next") (Operand.reg "%xtraiter1055")
      ],
      term := Term.condbr (Operand.reg "%epil.iter1056.cmp.not") "while.cond.preheader.i.i.i.i.epilog-lcssa" "for.body.i.i.i.i.epil" },
    { name := "while.cond.preheader.i.i.i.i.epilog-lcssa",
      instrs := [
        Instr.trunc "%extract.t1090" 128 64 (Operand.reg "%shr.i.i.i.i.epil")
      ],
      term := Term.br "while.cond.preheader.i.i.i.i" },
    { name := "while.cond.preheader.i.i.i.i",
      instrs := [
        Instr.phi "%add4.i.i.i.i.lcssa" (Ty.int 128) [("while.cond.preheader.i.i.i.i.unr-lcssa", (Operand.reg "%add4.i.i.i.i.lcssa.ph")),
                                       ("while.cond.preheader.i.i.i.i.epilog-lcssa", (Operand.reg "%add4.i.i.i.i.epil"))],
        Instr.phi "%shr.i.i.i.i.lcssa.off0" (Ty.int 64) [("while.cond.preheader.i.i.i.i.unr-lcssa", (Operand.reg "%shr.i.i.i.i.lcssa.ph.off0")),
                                       ("while.cond.preheader.i.i.i.i.epilog-lcssa", (Operand.reg "%extract.t1090"))],
        Instr.icmp "%tobool.not31.i.i.i.i" (IPred.ult) 128 (Operand.reg "%add4.i.i.i.i.lcssa") (Operand.imm (Const.int 128 0x00000000000000010000000000000000#128))
      ],
      term := Term.condbr (Operand.reg "%tobool.not31.i.i.i.i") "stk_mul_u64.exit.i.i" "while.body.us.i.i.i.i" },
    { name := "while.body.us.i.i.i.i",
      instrs := [
        Instr.binop "%inc12.us.i.i.i.i" (BinOp.add) 32 (Operand.reg "%inc12.us.i.i745747.i.i") (Operand.imm (Const.int 32 0x00000001#32)),
        Instr.gep "%arrayidx14.us.i.i.i.i" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%wide.trip.count.i.i.i.i"),
        Instr.store (Ty.int 64) (Operand.reg "%shr.i.i.i.i.lcssa.off0") (Operand.reg "%arrayidx14.us.i.i.i.i")
      ],
      term := Term.br "stk_mul_u64.exit.i.i" },
    { name := "for.body.i.i.i.i",
      instrs := [
        Instr.phi "%indvars.iv.i.i.i.i" (Ty.int 64) [("for.body.lr.ph.i.i.i.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i.i.i.i", (Operand.reg "%indvars.iv.next.i.i.i.i.3"))],
        Instr.phi "%carry.029.i.i.i.i" (Ty.int 128) [("for.body.lr.ph.i.i.i.i.new", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
                                       ("for.body.i.i.i.i", (Operand.reg "%shr.i.i.i.i.3"))],
        Instr.phi "%niter1061" (Ty.int 64) [("for.body.lr.ph.i.i.i.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i.i.i.i", (Operand.reg "%niter1061.next.3"))],
        Instr.gep "%arrayidx.i.i.i.i" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%indvars.iv.i.i.i.i"),
        Instr.load "%88" (Ty.int 64) (Operand.reg "%arrayidx.i.i.i.i"),
        Instr.zext "%conv2.i.i.i.i" 64 128 (Operand.reg "%88"),
        Instr.binop "%mul.i.i.i.i" (BinOp.mul) 128 (Operand.reg "%conv2.i.i.i.i") (Operand.imm (Const.int 128 0x00000000000000006765c793fa10079d#128)),
        Instr.binop "%add4.i.i.i.i" (BinOp.add) 128 (Operand.reg "%mul.i.i.i.i") (Operand.reg "%carry.029.i.i.i.i"),
        Instr.trunc "%conv5.i.i.i.i" 128 64 (Operand.reg "%add4.i.i.i.i"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i.i.i") (Operand.reg "%arrayidx.i.i.i.i"),
        Instr.binop "%shr.i.i.i.i" (BinOp.lshr) 128 (Operand.reg "%add4.i.i.i.i") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.i.i.i" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.gep "%arrayidx.i.i.i.i.1" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%indvars.iv.next.i.i.i.i"),
        Instr.load "%89" (Ty.int 64) (Operand.reg "%arrayidx.i.i.i.i.1"),
        Instr.zext "%conv2.i.i.i.i.1" 64 128 (Operand.reg "%89"),
        Instr.binop "%mul.i.i.i.i.1" (BinOp.mul) 128 (Operand.reg "%conv2.i.i.i.i.1") (Operand.imm (Const.int 128 0x00000000000000006765c793fa10079d#128)),
        Instr.binop "%add4.i.i.i.i.1" (BinOp.add) 128 (Operand.reg "%mul.i.i.i.i.1") (Operand.reg "%shr.i.i.i.i"),
        Instr.trunc "%conv5.i.i.i.i.1" 128 64 (Operand.reg "%add4.i.i.i.i.1"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i.i.i.1") (Operand.reg "%arrayidx.i.i.i.i.1"),
        Instr.binop "%shr.i.i.i.i.1" (BinOp.lshr) 128 (Operand.reg "%add4.i.i.i.i.1") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.i.i.i.1" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i.i.i") (Operand.imm (Const.int 64 0x0000000000000002#64)),
        Instr.gep "%arrayidx.i.i.i.i.2" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%indvars.iv.next.i.i.i.i.1"),
        Instr.load "%90" (Ty.int 64) (Operand.reg "%arrayidx.i.i.i.i.2"),
        Instr.zext "%conv2.i.i.i.i.2" 64 128 (Operand.reg "%90"),
        Instr.binop "%mul.i.i.i.i.2" (BinOp.mul) 128 (Operand.reg "%conv2.i.i.i.i.2") (Operand.imm (Const.int 128 0x00000000000000006765c793fa10079d#128)),
        Instr.binop "%add4.i.i.i.i.2" (BinOp.add) 128 (Operand.reg "%mul.i.i.i.i.2") (Operand.reg "%shr.i.i.i.i.1"),
        Instr.trunc "%conv5.i.i.i.i.2" 128 64 (Operand.reg "%add4.i.i.i.i.2"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i.i.i.2") (Operand.reg "%arrayidx.i.i.i.i.2"),
        Instr.binop "%shr.i.i.i.i.2" (BinOp.lshr) 128 (Operand.reg "%add4.i.i.i.i.2") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.i.i.i.2" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
        Instr.gep "%arrayidx.i.i.i.i.3" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%indvars.iv.next.i.i.i.i.2"),
        Instr.load "%91" (Ty.int 64) (Operand.reg "%arrayidx.i.i.i.i.3"),
        Instr.zext "%conv2.i.i.i.i.3" 64 128 (Operand.reg "%91"),
        Instr.binop "%mul.i.i.i.i.3" (BinOp.mul) 128 (Operand.reg "%conv2.i.i.i.i.3") (Operand.imm (Const.int 128 0x00000000000000006765c793fa10079d#128)),
        Instr.binop "%add4.i.i.i.i.3" (BinOp.add) 128 (Operand.reg "%mul.i.i.i.i.3") (Operand.reg "%shr.i.i.i.i.2"),
        Instr.trunc "%conv5.i.i.i.i.3" 128 64 (Operand.reg "%add4.i.i.i.i.3"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i.i.i.3") (Operand.reg "%arrayidx.i.i.i.i.3"),
        Instr.binop "%shr.i.i.i.i.3" (BinOp.lshr) 128 (Operand.reg "%add4.i.i.i.i.3") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.i.i.i.3" (BinOp.add) 64 (Operand.reg "%indvars.iv.i.i.i.i") (Operand.imm (Const.int 64 0x0000000000000004#64)),
        Instr.binop "%niter1061.next.3" (BinOp.add) 64 (Operand.reg "%niter1061") (Operand.imm (Const.int 64 0x0000000000000004#64)),
        Instr.icmp "%niter1061.ncmp.3" (IPred.eq) 64 (Operand.reg "%niter1061.next.3") (Operand.reg "%unroll_iter1060")
      ],
      term := Term.condbr (Operand.reg "%niter1061.ncmp.3") "while.cond.preheader.i.i.i.i.unr-lcssa.loopexit" "for.body.i.i.i.i" },
    { name := "stk_mul_u64.exit.i.i",
      instrs := [
        Instr.phi "%inc12.us.i.i744.i.i" (Ty.int 32) [("while.body.i.i", (Operand.reg "%inc12.us.i.i745747.i.i")),
                                       ("while.cond.preheader.i.i.i.i", (Operand.reg "%inc12.us.i.i745747.i.i")),
                                       ("while.body.us.i.i.i.i", (Operand.reg "%inc12.us.i.i.i.i"))],
        Instr.binop "%sub158.i.i" (BinOp.add) 64 (Operand.reg "%k.0748.i.i") (Operand.imm (Const.int 64 0xffffffffffffffe5#64)),
        Instr.icmp "%cmp155.i.i" (IPred.sgt) 64 (Operand.reg "%k.0748.i.i") (Operand.imm (Const.int 64 0x0000000000000035#64))
      ],
      term := Term.condbr (Operand.reg "%cmp155.i.i") "while.body.i.i" "while.end.i.i" },
    { name := "while.end.i.i",
      instrs := [
        Instr.store (Ty.int 32) (Operand.reg "%inc12.us.i.i744.i.i") (Operand.reg "%n.i539.i.i"),
        Instr.icmp "%tobool159.not.i.i" (IPred.ne) 64 (Operand.reg "%sub158.i.i") (Operand.imm (Const.int 64 0x0000000000000000#64)),
        Instr.icmp "%cmp28.i.i541.i.i" (IPred.sgt) 32 (Operand.reg "%inc12.us.i.i744.i.i") (Operand.imm (Const.int 32 0x00000000#32)),
        Instr.select "%or.cond864.i.i" (Ty.int 1) (Operand.reg "%tobool159.not.i.i") (Operand.reg "%cmp28.i.i541.i.i") (Operand.imm (Const.int 1 0x0#1))
      ],
      term := Term.condbr (Operand.reg "%or.cond864.i.i") "for.body.lr.ph.i.i542.i.i" "if.end198.i.i" },
    { name := "while.end.thread.i.i",
      instrs := [
        Instr.store (Ty.int 32) (Operand.imm (Const.int 32 0x00000001#32)) (Operand.reg "%n.i539.i.i"),
        Instr.icmp "%tobool159.not821.i.i" (IPred.eq) 64 (Operand.reg "%add108.i.i") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%tobool159.not821.i.i") "if.end198.i.i" "for.body.lr.ph.i.i542.i.i" },
    { name := "for.body.lr.ph.i.i542.i.i",
      instrs := [
        Instr.phi "%92" (Ty.int 32) [("while.end.thread.i.i", (Operand.imm (Const.int 32 0x00000001#32))),
                                       ("while.end.i.i", (Operand.reg "%inc12.us.i.i744.i.i"))],
        Instr.phi "%k.0.lcssa822825.i.i" (Ty.int 64) [("while.end.thread.i.i", (Operand.reg "%sub154.i.i")),
                                       ("while.end.i.i", (Operand.reg "%sub158.i.i"))],
        Instr.gep "%arrayidx162.i.i" (Ty.int 64) (Operand.global "@STK_P5") (Operand.reg "%k.0.lcssa822825.i.i"),
        Instr.load "%93" (Ty.int 64) (Operand.reg "%arrayidx162.i.i"),
        Instr.zext "%conv3.i.i.i.i" 64 128 (Operand.reg "%93"),
        Instr.zext "%wide.trip.count.i.i543.i.i" 32 64 (Operand.reg "%92"),
        Instr.binop "%xtraiter1062" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i.i543.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
        Instr.binop "%94" (BinOp.add) 32 (Operand.reg "%92") (Operand.imm (Const.int 32 0xffffffff#32)),
        Instr.icmp "%95" (IPred.ult) 32 (Operand.reg "%94") (Operand.imm (Const.int 32 0x00000003#32))
      ],
      term := Term.condbr (Operand.reg "%95") "while.cond.preheader.i.i555.i.i.unr-lcssa" "for.body.lr.ph.i.i542.i.i.new" },
    { name := "for.body.lr.ph.i.i542.i.i.new",
      instrs := [
        Instr.binop "%unroll_iter1067" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i.i543.i.i") (Operand.imm (Const.int 64 0x000000007ffffffc#64))
      ],
      term := Term.br "for.body.i.i544.i.i" },
    { name := "while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit",
      instrs := [
        Instr.trunc "%extract.t1093" 128 64 (Operand.reg "%shr.i.i552.i.i.3")
      ],
      term := Term.br "while.cond.preheader.i.i555.i.i.unr-lcssa" },
    { name := "while.cond.preheader.i.i555.i.i.unr-lcssa",
      instrs := [
        Instr.phi "%add4.i.i550.i.i.lcssa.ph" (Ty.int 128) [("for.body.lr.ph.i.i542.i.i", (Operand.imm Const.poison)),
                                       ("while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit", (Operand.reg "%add4.i.i550.i.i.3"))],
        Instr.phi "%shr.i.i552.i.i.lcssa.ph.off0" (Ty.int 64) [("for.body.lr.ph.i.i542.i.i", (Operand.imm Const.poison)),
                                       ("while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit", (Operand.reg "%extract.t1093"))],
        Instr.phi "%indvars.iv.i.i545.i.i.unr" (Ty.int 64) [("for.body.lr.ph.i.i542.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit", (Operand.reg "%indvars.iv.next.i.i553.i.i.3"))],
        Instr.phi "%carry.029.i.i546.i.i.unr" (Ty.int 128) [("for.body.lr.ph.i.i542.i.i", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
                                       ("while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit", (Operand.reg "%shr.i.i552.i.i.3"))],
        Instr.icmp "%lcmp.mod1064.not" (IPred.eq) 64 (Operand.reg "%xtraiter1062") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%lcmp.mod1064.not") "while.cond.preheader.i.i555.i.i" "for.body.i.i544.i.i.epil" },
    { name := "for.body.i.i544.i.i.epil",
      instrs := [
        Instr.phi "%indvars.iv.i.i545.i.i.epil" (Ty.int 64) [("for.body.i.i544.i.i.epil", (Operand.reg "%indvars.iv.next.i.i553.i.i.epil")),
                                       ("while.cond.preheader.i.i555.i.i.unr-lcssa", (Operand.reg "%indvars.iv.i.i545.i.i.unr"))],
        Instr.phi "%carry.029.i.i546.i.i.epil" (Ty.int 128) [("for.body.i.i544.i.i.epil", (Operand.reg "%shr.i.i552.i.i.epil")),
                                       ("while.cond.preheader.i.i555.i.i.unr-lcssa", (Operand.reg "%carry.029.i.i546.i.i.unr"))],
        Instr.phi "%epil.iter1063" (Ty.int 64) [("for.body.i.i544.i.i.epil", (Operand.reg "%epil.iter1063.next")),
                                       ("while.cond.preheader.i.i555.i.i.unr-lcssa", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.gep "%arrayidx.i.i547.i.i.epil" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%indvars.iv.i.i545.i.i.epil"),
        Instr.load "%96" (Ty.int 64) (Operand.reg "%arrayidx.i.i547.i.i.epil"),
        Instr.zext "%conv2.i.i548.i.i.epil" 64 128 (Operand.reg "%96"),
        Instr.binop "%mul.i.i549.i.i.epil" (BinOp.mul) 128 (Operand.reg "%conv2.i.i548.i.i.epil") (Operand.reg "%conv3.i.i.i.i"),
        Instr.binop "%add4.i.i550.i.i.epil" (BinOp.add) 128 (Operand.reg "%mul.i.i549.i.i.epil") (Operand.reg "%carry.029.i.i546.i.i.epil"),
        Instr.trunc "%conv5.i.i551.i.i.epil" 128 64 (Operand.reg "%add4.i.i550.i.i.epil"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i551.i.i.epil") (Operand.reg "%arrayidx.i.i547.i.i.epil"),
        Instr.binop "%shr.i.i552.i.i.epil" (BinOp.lshr) 128 (Operand.reg "%add4.i.i550.i.i.epil") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.i553.i.i.epil" (BinOp.add) 64 (Operand.reg "%indvars.iv.i.i545.i.i.epil") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.binop "%epil.iter1063.next" (BinOp.add) 64 (Operand.reg "%epil.iter1063") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%epil.iter1063.cmp.not" (IPred.eq) 64 (Operand.reg "%epil.iter1063.next") (Operand.reg "%xtraiter1062")
      ],
      term := Term.condbr (Operand.reg "%epil.iter1063.cmp.not") "while.cond.preheader.i.i555.i.i.epilog-lcssa" "for.body.i.i544.i.i.epil" },
    { name := "while.cond.preheader.i.i555.i.i.epilog-lcssa",
      instrs := [
        Instr.trunc "%extract.t1092" 128 64 (Operand.reg "%shr.i.i552.i.i.epil")
      ],
      term := Term.br "while.cond.preheader.i.i555.i.i" },
    { name := "while.cond.preheader.i.i555.i.i",
      instrs := [
        Instr.phi "%add4.i.i550.i.i.lcssa" (Ty.int 128) [("while.cond.preheader.i.i555.i.i.unr-lcssa", (Operand.reg "%add4.i.i550.i.i.lcssa.ph")),
                                       ("while.cond.preheader.i.i555.i.i.epilog-lcssa", (Operand.reg "%add4.i.i550.i.i.epil"))],
        Instr.phi "%shr.i.i552.i.i.lcssa.off0" (Ty.int 64) [("while.cond.preheader.i.i555.i.i.unr-lcssa", (Operand.reg "%shr.i.i552.i.i.lcssa.ph.off0")),
                                       ("while.cond.preheader.i.i555.i.i.epilog-lcssa", (Operand.reg "%extract.t1092"))],
        Instr.icmp "%tobool.not31.i.i556.i.i" (IPred.ult) 128 (Operand.reg "%add4.i.i550.i.i.lcssa") (Operand.imm (Const.int 128 0x00000000000000010000000000000000#128))
      ],
      term := Term.condbr (Operand.reg "%tobool.not31.i.i556.i.i") "if.end198.i.i" "while.body.us.i.i557.i.i" },
    { name := "while.body.us.i.i557.i.i",
      instrs := [
        Instr.binop "%inc12.us.i.i559.i.i" (BinOp.add) 32 (Operand.reg "%92") (Operand.imm (Const.int 32 0x00000001#32)),
        Instr.gep "%arrayidx14.us.i.i560.i.i" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%wide.trip.count.i.i543.i.i"),
        Instr.store (Ty.int 64) (Operand.reg "%shr.i.i552.i.i.lcssa.off0") (Operand.reg "%arrayidx14.us.i.i560.i.i"),
        Instr.store (Ty.int 32) (Operand.reg "%inc12.us.i.i559.i.i") (Operand.reg "%n.i539.i.i")
      ],
      term := Term.br "if.end198.i.i" },
    { name := "for.body.i.i544.i.i",
      instrs := [
        Instr.phi "%indvars.iv.i.i545.i.i" (Ty.int 64) [("for.body.lr.ph.i.i542.i.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i.i544.i.i", (Operand.reg "%indvars.iv.next.i.i553.i.i.3"))],
        Instr.phi "%carry.029.i.i546.i.i" (Ty.int 128) [("for.body.lr.ph.i.i542.i.i.new", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
                                       ("for.body.i.i544.i.i", (Operand.reg "%shr.i.i552.i.i.3"))],
        Instr.phi "%niter1068" (Ty.int 64) [("for.body.lr.ph.i.i542.i.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i.i544.i.i", (Operand.reg "%niter1068.next.3"))],
        Instr.gep "%arrayidx.i.i547.i.i" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%indvars.iv.i.i545.i.i"),
        Instr.load "%97" (Ty.int 64) (Operand.reg "%arrayidx.i.i547.i.i"),
        Instr.zext "%conv2.i.i548.i.i" 64 128 (Operand.reg "%97"),
        Instr.binop "%mul.i.i549.i.i" (BinOp.mul) 128 (Operand.reg "%conv2.i.i548.i.i") (Operand.reg "%conv3.i.i.i.i"),
        Instr.binop "%add4.i.i550.i.i" (BinOp.add) 128 (Operand.reg "%mul.i.i549.i.i") (Operand.reg "%carry.029.i.i546.i.i"),
        Instr.trunc "%conv5.i.i551.i.i" 128 64 (Operand.reg "%add4.i.i550.i.i"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i551.i.i") (Operand.reg "%arrayidx.i.i547.i.i"),
        Instr.binop "%shr.i.i552.i.i" (BinOp.lshr) 128 (Operand.reg "%add4.i.i550.i.i") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.i553.i.i" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i545.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.gep "%arrayidx.i.i547.i.i.1" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%indvars.iv.next.i.i553.i.i"),
        Instr.load "%98" (Ty.int 64) (Operand.reg "%arrayidx.i.i547.i.i.1"),
        Instr.zext "%conv2.i.i548.i.i.1" 64 128 (Operand.reg "%98"),
        Instr.binop "%mul.i.i549.i.i.1" (BinOp.mul) 128 (Operand.reg "%conv2.i.i548.i.i.1") (Operand.reg "%conv3.i.i.i.i"),
        Instr.binop "%add4.i.i550.i.i.1" (BinOp.add) 128 (Operand.reg "%mul.i.i549.i.i.1") (Operand.reg "%shr.i.i552.i.i"),
        Instr.trunc "%conv5.i.i551.i.i.1" 128 64 (Operand.reg "%add4.i.i550.i.i.1"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i551.i.i.1") (Operand.reg "%arrayidx.i.i547.i.i.1"),
        Instr.binop "%shr.i.i552.i.i.1" (BinOp.lshr) 128 (Operand.reg "%add4.i.i550.i.i.1") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.i553.i.i.1" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i545.i.i") (Operand.imm (Const.int 64 0x0000000000000002#64)),
        Instr.gep "%arrayidx.i.i547.i.i.2" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%indvars.iv.next.i.i553.i.i.1"),
        Instr.load "%99" (Ty.int 64) (Operand.reg "%arrayidx.i.i547.i.i.2"),
        Instr.zext "%conv2.i.i548.i.i.2" 64 128 (Operand.reg "%99"),
        Instr.binop "%mul.i.i549.i.i.2" (BinOp.mul) 128 (Operand.reg "%conv2.i.i548.i.i.2") (Operand.reg "%conv3.i.i.i.i"),
        Instr.binop "%add4.i.i550.i.i.2" (BinOp.add) 128 (Operand.reg "%mul.i.i549.i.i.2") (Operand.reg "%shr.i.i552.i.i.1"),
        Instr.trunc "%conv5.i.i551.i.i.2" 128 64 (Operand.reg "%add4.i.i550.i.i.2"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i551.i.i.2") (Operand.reg "%arrayidx.i.i547.i.i.2"),
        Instr.binop "%shr.i.i552.i.i.2" (BinOp.lshr) 128 (Operand.reg "%add4.i.i550.i.i.2") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.i553.i.i.2" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i545.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
        Instr.gep "%arrayidx.i.i547.i.i.3" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%indvars.iv.next.i.i553.i.i.2"),
        Instr.load "%100" (Ty.int 64) (Operand.reg "%arrayidx.i.i547.i.i.3"),
        Instr.zext "%conv2.i.i548.i.i.3" 64 128 (Operand.reg "%100"),
        Instr.binop "%mul.i.i549.i.i.3" (BinOp.mul) 128 (Operand.reg "%conv2.i.i548.i.i.3") (Operand.reg "%conv3.i.i.i.i"),
        Instr.binop "%add4.i.i550.i.i.3" (BinOp.add) 128 (Operand.reg "%mul.i.i549.i.i.3") (Operand.reg "%shr.i.i552.i.i.2"),
        Instr.trunc "%conv5.i.i551.i.i.3" 128 64 (Operand.reg "%add4.i.i550.i.i.3"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i551.i.i.3") (Operand.reg "%arrayidx.i.i547.i.i.3"),
        Instr.binop "%shr.i.i552.i.i.3" (BinOp.lshr) 128 (Operand.reg "%add4.i.i550.i.i.3") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.i553.i.i.3" (BinOp.add) 64 (Operand.reg "%indvars.iv.i.i545.i.i") (Operand.imm (Const.int 64 0x0000000000000004#64)),
        Instr.binop "%niter1068.next.3" (BinOp.add) 64 (Operand.reg "%niter1068") (Operand.imm (Const.int 64 0x0000000000000004#64)),
        Instr.icmp "%niter1068.ncmp.3" (IPred.eq) 64 (Operand.reg "%niter1068.next.3") (Operand.reg "%unroll_iter1067")
      ],
      term := Term.condbr (Operand.reg "%niter1068.ncmp.3") "while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit" "for.body.i.i544.i.i" },
    { name := "if.else164.i.i",
      instrs := [
        Instr.icmp "%cmp165.i.i" (IPred.slt) 64 (Operand.reg "%add108.i.i") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%cmp165.i.i") "if.then167.i.i" "while.cond184.preheader.i.i" },
    { name := "while.cond184.preheader.i.i",
      instrs := [
        Instr.load "%n.i.promoted751.i.i" (Ty.int 32) (Operand.reg "%n.i.i.i"),
        Instr.icmp "%cmp185753.i.i" (IPred.ugt) 64 (Operand.reg "%add108.i.i") (Operand.imm (Const.int 64 0x0000000000000012#64))
      ],
      term := Term.condbr (Operand.reg "%cmp185753.i.i") "while.body187.i.i" "while.end190.i.i" },
    { name := "if.then167.i.i",
      instrs := [
        Instr.binop "%sub169.i.i" (BinOp.sub) 64 (Operand.imm (Const.int 64 0x0000000000000000#64)) (Operand.reg "%add108.i.i"),
        Instr.icmp "%cmp171760.i.i" (IPred.sgt) 64 (Operand.reg "%sub169.i.i") (Operand.imm (Const.int 64 0x0000000000000012#64))
      ],
      term := Term.condbr (Operand.reg "%cmp171760.i.i") "while.body173.i.i" "while.end176.thread.i.i" },
    { name := "while.end176.thread.i.i",
      instrs := [
        Instr.store (Ty.int 32) (Operand.imm (Const.int 32 0x00000001#32)) (Operand.reg "%n.i539.i.i")
      ],
      term := Term.br "if.then178.i.i" },
    { name := "while.body173.i.i",
      instrs := [
        Instr.phi "%k168.0762.i.i" (Ty.int 64) [("stk_mul_u64.exit583.i.i", (Operand.reg "%sub175.i.i")),
                                       ("if.then167.i.i", (Operand.reg "%sub169.i.i"))],
        Instr.phi "%inc12.us.i.i581759761.i.i" (Ty.int 32) [("stk_mul_u64.exit583.i.i", (Operand.reg "%inc12.us.i.i581758.i.i")),
                                       ("if.then167.i.i", (Operand.imm (Const.int 32 0x00000001#32)))],
        Instr.icmp "%cmp28.i.i563.i.i" (IPred.sgt) 32 (Operand.reg "%inc12.us.i.i581759761.i.i") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%cmp28.i.i563.i.i") "for.body.lr.ph.i.i564.i.i" "stk_mul_u64.exit583.i.i" },
    { name := "for.body.lr.ph.i.i564.i.i",
      instrs := [
        Instr.zext "%wide.trip.count.i.i565.i.i" 32 64 (Operand.reg "%inc12.us.i.i581759761.i.i"),
        Instr.binop "%xtraiter1083" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i.i565.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
        Instr.icmp "%101" (IPred.ult) 32 (Operand.reg "%inc12.us.i.i581759761.i.i") (Operand.imm (Const.int 32 0x00000004#32))
      ],
      term := Term.condbr (Operand.reg "%101") "while.cond.preheader.i.i577.i.i.unr-lcssa" "for.body.lr.ph.i.i564.i.i.new" },
    { name := "for.body.lr.ph.i.i564.i.i.new",
      instrs := [
        Instr.binop "%unroll_iter1088" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i.i565.i.i") (Operand.imm (Const.int 64 0x000000007ffffffc#64))
      ],
      term := Term.br "for.body.i.i566.i.i" },
    { name := "while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit",
      instrs := [
        Instr.trunc "%extract.t1099" 128 64 (Operand.reg "%shr.i.i574.i.i.3")
      ],
      term := Term.br "while.cond.preheader.i.i577.i.i.unr-lcssa" },
    { name := "while.cond.preheader.i.i577.i.i.unr-lcssa",
      instrs := [
        Instr.phi "%add4.i.i572.i.i.lcssa.ph" (Ty.int 128) [("for.body.lr.ph.i.i564.i.i", (Operand.imm Const.poison)),
                                       ("while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit", (Operand.reg "%add4.i.i572.i.i.3"))],
        Instr.phi "%shr.i.i574.i.i.lcssa.ph.off0" (Ty.int 64) [("for.body.lr.ph.i.i564.i.i", (Operand.imm Const.poison)),
                                       ("while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit", (Operand.reg "%extract.t1099"))],
        Instr.phi "%indvars.iv.i.i567.i.i.unr" (Ty.int 64) [("for.body.lr.ph.i.i564.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit", (Operand.reg "%indvars.iv.next.i.i575.i.i.3"))],
        Instr.phi "%carry.029.i.i568.i.i.unr" (Ty.int 128) [("for.body.lr.ph.i.i564.i.i", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
                                       ("while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit", (Operand.reg "%shr.i.i574.i.i.3"))],
        Instr.icmp "%lcmp.mod1085.not" (IPred.eq) 64 (Operand.reg "%xtraiter1083") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%lcmp.mod1085.not") "while.cond.preheader.i.i577.i.i" "for.body.i.i566.i.i.epil" },
    { name := "for.body.i.i566.i.i.epil",
      instrs := [
        Instr.phi "%indvars.iv.i.i567.i.i.epil" (Ty.int 64) [("for.body.i.i566.i.i.epil", (Operand.reg "%indvars.iv.next.i.i575.i.i.epil")),
                                       ("while.cond.preheader.i.i577.i.i.unr-lcssa", (Operand.reg "%indvars.iv.i.i567.i.i.unr"))],
        Instr.phi "%carry.029.i.i568.i.i.epil" (Ty.int 128) [("for.body.i.i566.i.i.epil", (Operand.reg "%shr.i.i574.i.i.epil")),
                                       ("while.cond.preheader.i.i577.i.i.unr-lcssa", (Operand.reg "%carry.029.i.i568.i.i.unr"))],
        Instr.phi "%epil.iter1084" (Ty.int 64) [("for.body.i.i566.i.i.epil", (Operand.reg "%epil.iter1084.next")),
                                       ("while.cond.preheader.i.i577.i.i.unr-lcssa", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.gep "%arrayidx.i.i569.i.i.epil" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%indvars.iv.i.i567.i.i.epil"),
        Instr.load "%102" (Ty.int 64) (Operand.reg "%arrayidx.i.i569.i.i.epil"),
        Instr.zext "%conv2.i.i570.i.i.epil" 64 128 (Operand.reg "%102"),
        Instr.binop "%mul.i.i571.i.i.epil" (BinOp.mul) 128 (Operand.reg "%conv2.i.i570.i.i.epil") (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
        Instr.binop "%add4.i.i572.i.i.epil" (BinOp.add) 128 (Operand.reg "%mul.i.i571.i.i.epil") (Operand.reg "%carry.029.i.i568.i.i.epil"),
        Instr.trunc "%conv5.i.i573.i.i.epil" 128 64 (Operand.reg "%add4.i.i572.i.i.epil"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i573.i.i.epil") (Operand.reg "%arrayidx.i.i569.i.i.epil"),
        Instr.binop "%shr.i.i574.i.i.epil" (BinOp.lshr) 128 (Operand.reg "%add4.i.i572.i.i.epil") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.i575.i.i.epil" (BinOp.add) 64 (Operand.reg "%indvars.iv.i.i567.i.i.epil") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.binop "%epil.iter1084.next" (BinOp.add) 64 (Operand.reg "%epil.iter1084") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%epil.iter1084.cmp.not" (IPred.eq) 64 (Operand.reg "%epil.iter1084.next") (Operand.reg "%xtraiter1083")
      ],
      term := Term.condbr (Operand.reg "%epil.iter1084.cmp.not") "while.cond.preheader.i.i577.i.i.epilog-lcssa" "for.body.i.i566.i.i.epil" },
    { name := "while.cond.preheader.i.i577.i.i.epilog-lcssa",
      instrs := [
        Instr.trunc "%extract.t1098" 128 64 (Operand.reg "%shr.i.i574.i.i.epil")
      ],
      term := Term.br "while.cond.preheader.i.i577.i.i" },
    { name := "while.cond.preheader.i.i577.i.i",
      instrs := [
        Instr.phi "%add4.i.i572.i.i.lcssa" (Ty.int 128) [("while.cond.preheader.i.i577.i.i.unr-lcssa", (Operand.reg "%add4.i.i572.i.i.lcssa.ph")),
                                       ("while.cond.preheader.i.i577.i.i.epilog-lcssa", (Operand.reg "%add4.i.i572.i.i.epil"))],
        Instr.phi "%shr.i.i574.i.i.lcssa.off0" (Ty.int 64) [("while.cond.preheader.i.i577.i.i.unr-lcssa", (Operand.reg "%shr.i.i574.i.i.lcssa.ph.off0")),
                                       ("while.cond.preheader.i.i577.i.i.epilog-lcssa", (Operand.reg "%extract.t1098"))],
        Instr.icmp "%tobool.not31.i.i578.i.i" (IPred.ult) 128 (Operand.reg "%add4.i.i572.i.i.lcssa") (Operand.imm (Const.int 128 0x00000000000000010000000000000000#128))
      ],
      term := Term.condbr (Operand.reg "%tobool.not31.i.i578.i.i") "stk_mul_u64.exit583.i.i" "while.body.us.i.i579.i.i" },
    { name := "while.body.us.i.i579.i.i",
      instrs := [
        Instr.binop "%inc12.us.i.i581.i.i" (BinOp.add) 32 (Operand.reg "%inc12.us.i.i581759761.i.i") (Operand.imm (Const.int 32 0x00000001#32)),
        Instr.gep "%arrayidx14.us.i.i582.i.i" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%wide.trip.count.i.i565.i.i"),
        Instr.store (Ty.int 64) (Operand.reg "%shr.i.i574.i.i.lcssa.off0") (Operand.reg "%arrayidx14.us.i.i582.i.i")
      ],
      term := Term.br "stk_mul_u64.exit583.i.i" },
    { name := "for.body.i.i566.i.i",
      instrs := [
        Instr.phi "%indvars.iv.i.i567.i.i" (Ty.int 64) [("for.body.lr.ph.i.i564.i.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i.i566.i.i", (Operand.reg "%indvars.iv.next.i.i575.i.i.3"))],
        Instr.phi "%carry.029.i.i568.i.i" (Ty.int 128) [("for.body.lr.ph.i.i564.i.i.new", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
                                       ("for.body.i.i566.i.i", (Operand.reg "%shr.i.i574.i.i.3"))],
        Instr.phi "%niter1089" (Ty.int 64) [("for.body.lr.ph.i.i564.i.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i.i566.i.i", (Operand.reg "%niter1089.next.3"))],
        Instr.gep "%arrayidx.i.i569.i.i" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%indvars.iv.i.i567.i.i"),
        Instr.load "%103" (Ty.int 64) (Operand.reg "%arrayidx.i.i569.i.i"),
        Instr.zext "%conv2.i.i570.i.i" 64 128 (Operand.reg "%103"),
        Instr.binop "%mul.i.i571.i.i" (BinOp.mul) 128 (Operand.reg "%conv2.i.i570.i.i") (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
        Instr.binop "%add4.i.i572.i.i" (BinOp.add) 128 (Operand.reg "%mul.i.i571.i.i") (Operand.reg "%carry.029.i.i568.i.i"),
        Instr.trunc "%conv5.i.i573.i.i" 128 64 (Operand.reg "%add4.i.i572.i.i"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i573.i.i") (Operand.reg "%arrayidx.i.i569.i.i"),
        Instr.binop "%shr.i.i574.i.i" (BinOp.lshr) 128 (Operand.reg "%add4.i.i572.i.i") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.i575.i.i" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i567.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.gep "%arrayidx.i.i569.i.i.1" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%indvars.iv.next.i.i575.i.i"),
        Instr.load "%104" (Ty.int 64) (Operand.reg "%arrayidx.i.i569.i.i.1"),
        Instr.zext "%conv2.i.i570.i.i.1" 64 128 (Operand.reg "%104"),
        Instr.binop "%mul.i.i571.i.i.1" (BinOp.mul) 128 (Operand.reg "%conv2.i.i570.i.i.1") (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
        Instr.binop "%add4.i.i572.i.i.1" (BinOp.add) 128 (Operand.reg "%mul.i.i571.i.i.1") (Operand.reg "%shr.i.i574.i.i"),
        Instr.trunc "%conv5.i.i573.i.i.1" 128 64 (Operand.reg "%add4.i.i572.i.i.1"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i573.i.i.1") (Operand.reg "%arrayidx.i.i569.i.i.1"),
        Instr.binop "%shr.i.i574.i.i.1" (BinOp.lshr) 128 (Operand.reg "%add4.i.i572.i.i.1") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.i575.i.i.1" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i567.i.i") (Operand.imm (Const.int 64 0x0000000000000002#64)),
        Instr.gep "%arrayidx.i.i569.i.i.2" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%indvars.iv.next.i.i575.i.i.1"),
        Instr.load "%105" (Ty.int 64) (Operand.reg "%arrayidx.i.i569.i.i.2"),
        Instr.zext "%conv2.i.i570.i.i.2" 64 128 (Operand.reg "%105"),
        Instr.binop "%mul.i.i571.i.i.2" (BinOp.mul) 128 (Operand.reg "%conv2.i.i570.i.i.2") (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
        Instr.binop "%add4.i.i572.i.i.2" (BinOp.add) 128 (Operand.reg "%mul.i.i571.i.i.2") (Operand.reg "%shr.i.i574.i.i.1"),
        Instr.trunc "%conv5.i.i573.i.i.2" 128 64 (Operand.reg "%add4.i.i572.i.i.2"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i573.i.i.2") (Operand.reg "%arrayidx.i.i569.i.i.2"),
        Instr.binop "%shr.i.i574.i.i.2" (BinOp.lshr) 128 (Operand.reg "%add4.i.i572.i.i.2") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.i575.i.i.2" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i567.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
        Instr.gep "%arrayidx.i.i569.i.i.3" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%indvars.iv.next.i.i575.i.i.2"),
        Instr.load "%106" (Ty.int 64) (Operand.reg "%arrayidx.i.i569.i.i.3"),
        Instr.zext "%conv2.i.i570.i.i.3" 64 128 (Operand.reg "%106"),
        Instr.binop "%mul.i.i571.i.i.3" (BinOp.mul) 128 (Operand.reg "%conv2.i.i570.i.i.3") (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
        Instr.binop "%add4.i.i572.i.i.3" (BinOp.add) 128 (Operand.reg "%mul.i.i571.i.i.3") (Operand.reg "%shr.i.i574.i.i.2"),
        Instr.trunc "%conv5.i.i573.i.i.3" 128 64 (Operand.reg "%add4.i.i572.i.i.3"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i573.i.i.3") (Operand.reg "%arrayidx.i.i569.i.i.3"),
        Instr.binop "%shr.i.i574.i.i.3" (BinOp.lshr) 128 (Operand.reg "%add4.i.i572.i.i.3") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.i575.i.i.3" (BinOp.add) 64 (Operand.reg "%indvars.iv.i.i567.i.i") (Operand.imm (Const.int 64 0x0000000000000004#64)),
        Instr.binop "%niter1089.next.3" (BinOp.add) 64 (Operand.reg "%niter1089") (Operand.imm (Const.int 64 0x0000000000000004#64)),
        Instr.icmp "%niter1089.ncmp.3" (IPred.eq) 64 (Operand.reg "%niter1089.next.3") (Operand.reg "%unroll_iter1088")
      ],
      term := Term.condbr (Operand.reg "%niter1089.ncmp.3") "while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit" "for.body.i.i566.i.i" },
    { name := "stk_mul_u64.exit583.i.i",
      instrs := [
        Instr.phi "%inc12.us.i.i581758.i.i" (Ty.int 32) [("while.body173.i.i", (Operand.reg "%inc12.us.i.i581759761.i.i")),
                                       ("while.cond.preheader.i.i577.i.i", (Operand.reg "%inc12.us.i.i581759761.i.i")),
                                       ("while.body.us.i.i579.i.i", (Operand.reg "%inc12.us.i.i581.i.i"))],
        Instr.binop "%sub175.i.i" (BinOp.add) 64 (Operand.reg "%k168.0762.i.i") (Operand.imm (Const.int 64 0xffffffffffffffed#64)),
        Instr.icmp "%cmp171.i.i" (IPred.sgt) 64 (Operand.reg "%k168.0762.i.i") (Operand.imm (Const.int 64 0x0000000000000025#64))
      ],
      term := Term.condbr (Operand.reg "%cmp171.i.i") "while.body173.i.i" "while.end176.i.i" },
    { name := "while.end176.i.i",
      instrs := [
        Instr.store (Ty.int 32) (Operand.reg "%inc12.us.i.i581758.i.i") (Operand.reg "%n.i539.i.i"),
        Instr.icmp "%tobool177.not.i.i" (IPred.eq) 64 (Operand.reg "%sub175.i.i") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%tobool177.not.i.i") "if.end198.i.i" "if.then178.i.i" },
    { name := "if.then178.i.i",
      instrs := [
        Instr.phi "%k168.0.lcssa829.i.i" (Ty.int 64) [("while.end176.thread.i.i", (Operand.reg "%sub169.i.i")),
                                       ("while.end176.i.i", (Operand.reg "%sub175.i.i"))],
        Instr.gep "%arrayidx180.i.i" (Ty.int 64) (Operand.global "@NUMF_EL1_P10") (Operand.reg "%k168.0.lcssa829.i.i"),
        Instr.load "%107" (Ty.int 64) (Operand.reg "%arrayidx180.i.i"),
        Instr.callVoid "stk_mul_u64" [(Ty.ptr, (Operand.reg "%pow.i.i")),
                             ((Ty.int 64), (Operand.reg "%107"))]
      ],
      term := Term.br "if.end198.i.i" },
    { name := "while.body187.i.i",
      instrs := [
        Instr.phi "%k183.0754.i.i" (Ty.int 64) [("stk_mul_u64.exit605.i.i", (Operand.reg "%sub189.i.i")),
                                       ("while.cond184.preheader.i.i", (Operand.reg "%add108.i.i"))],
        Instr.phi "%108" (Ty.int 32) [("stk_mul_u64.exit605.i.i", (Operand.reg "%115")),
                                       ("while.cond184.preheader.i.i", (Operand.reg "%n.i.promoted751.i.i"))],
        Instr.icmp "%cmp28.i.i585.i.i" (IPred.sgt) 32 (Operand.reg "%108") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%cmp28.i.i585.i.i") "for.body.lr.ph.i.i586.i.i" "stk_mul_u64.exit605.i.i" },
    { name := "for.body.lr.ph.i.i586.i.i",
      instrs := [
        Instr.zext "%wide.trip.count.i.i587.i.i" 32 64 (Operand.reg "%108"),
        Instr.binop "%xtraiter1069" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i.i587.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
        Instr.icmp "%109" (IPred.ult) 32 (Operand.reg "%108") (Operand.imm (Const.int 32 0x00000004#32))
      ],
      term := Term.condbr (Operand.reg "%109") "while.cond.preheader.i.i599.i.i.unr-lcssa" "for.body.lr.ph.i.i586.i.i.new" },
    { name := "for.body.lr.ph.i.i586.i.i.new",
      instrs := [
        Instr.binop "%unroll_iter1074" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i.i587.i.i") (Operand.imm (Const.int 64 0x000000007ffffffc#64))
      ],
      term := Term.br "for.body.i.i588.i.i" },
    { name := "while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit",
      instrs := [
        Instr.trunc "%extract.t1095" 128 64 (Operand.reg "%shr.i.i596.i.i.3")
      ],
      term := Term.br "while.cond.preheader.i.i599.i.i.unr-lcssa" },
    { name := "while.cond.preheader.i.i599.i.i.unr-lcssa",
      instrs := [
        Instr.phi "%add4.i.i594.i.i.lcssa.ph" (Ty.int 128) [("for.body.lr.ph.i.i586.i.i", (Operand.imm Const.poison)),
                                       ("while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit", (Operand.reg "%add4.i.i594.i.i.3"))],
        Instr.phi "%shr.i.i596.i.i.lcssa.ph.off0" (Ty.int 64) [("for.body.lr.ph.i.i586.i.i", (Operand.imm Const.poison)),
                                       ("while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit", (Operand.reg "%extract.t1095"))],
        Instr.phi "%indvars.iv.i.i589.i.i.unr" (Ty.int 64) [("for.body.lr.ph.i.i586.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit", (Operand.reg "%indvars.iv.next.i.i597.i.i.3"))],
        Instr.phi "%carry.029.i.i590.i.i.unr" (Ty.int 128) [("for.body.lr.ph.i.i586.i.i", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
                                       ("while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit", (Operand.reg "%shr.i.i596.i.i.3"))],
        Instr.icmp "%lcmp.mod1071.not" (IPred.eq) 64 (Operand.reg "%xtraiter1069") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%lcmp.mod1071.not") "while.cond.preheader.i.i599.i.i" "for.body.i.i588.i.i.epil" },
    { name := "for.body.i.i588.i.i.epil",
      instrs := [
        Instr.phi "%indvars.iv.i.i589.i.i.epil" (Ty.int 64) [("for.body.i.i588.i.i.epil", (Operand.reg "%indvars.iv.next.i.i597.i.i.epil")),
                                       ("while.cond.preheader.i.i599.i.i.unr-lcssa", (Operand.reg "%indvars.iv.i.i589.i.i.unr"))],
        Instr.phi "%carry.029.i.i590.i.i.epil" (Ty.int 128) [("for.body.i.i588.i.i.epil", (Operand.reg "%shr.i.i596.i.i.epil")),
                                       ("while.cond.preheader.i.i599.i.i.unr-lcssa", (Operand.reg "%carry.029.i.i590.i.i.unr"))],
        Instr.phi "%epil.iter1070" (Ty.int 64) [("for.body.i.i588.i.i.epil", (Operand.reg "%epil.iter1070.next")),
                                       ("while.cond.preheader.i.i599.i.i.unr-lcssa", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.gep "%arrayidx.i.i591.i.i.epil" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.i.i589.i.i.epil"),
        Instr.load "%110" (Ty.int 64) (Operand.reg "%arrayidx.i.i591.i.i.epil"),
        Instr.zext "%conv2.i.i592.i.i.epil" 64 128 (Operand.reg "%110"),
        Instr.binop "%mul.i.i593.i.i.epil" (BinOp.mul) 128 (Operand.reg "%conv2.i.i592.i.i.epil") (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
        Instr.binop "%add4.i.i594.i.i.epil" (BinOp.add) 128 (Operand.reg "%mul.i.i593.i.i.epil") (Operand.reg "%carry.029.i.i590.i.i.epil"),
        Instr.trunc "%conv5.i.i595.i.i.epil" 128 64 (Operand.reg "%add4.i.i594.i.i.epil"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i595.i.i.epil") (Operand.reg "%arrayidx.i.i591.i.i.epil"),
        Instr.binop "%shr.i.i596.i.i.epil" (BinOp.lshr) 128 (Operand.reg "%add4.i.i594.i.i.epil") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.i597.i.i.epil" (BinOp.add) 64 (Operand.reg "%indvars.iv.i.i589.i.i.epil") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.binop "%epil.iter1070.next" (BinOp.add) 64 (Operand.reg "%epil.iter1070") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%epil.iter1070.cmp.not" (IPred.eq) 64 (Operand.reg "%epil.iter1070.next") (Operand.reg "%xtraiter1069")
      ],
      term := Term.condbr (Operand.reg "%epil.iter1070.cmp.not") "while.cond.preheader.i.i599.i.i.epilog-lcssa" "for.body.i.i588.i.i.epil" },
    { name := "while.cond.preheader.i.i599.i.i.epilog-lcssa",
      instrs := [
        Instr.trunc "%extract.t1094" 128 64 (Operand.reg "%shr.i.i596.i.i.epil")
      ],
      term := Term.br "while.cond.preheader.i.i599.i.i" },
    { name := "while.cond.preheader.i.i599.i.i",
      instrs := [
        Instr.phi "%add4.i.i594.i.i.lcssa" (Ty.int 128) [("while.cond.preheader.i.i599.i.i.unr-lcssa", (Operand.reg "%add4.i.i594.i.i.lcssa.ph")),
                                       ("while.cond.preheader.i.i599.i.i.epilog-lcssa", (Operand.reg "%add4.i.i594.i.i.epil"))],
        Instr.phi "%shr.i.i596.i.i.lcssa.off0" (Ty.int 64) [("while.cond.preheader.i.i599.i.i.unr-lcssa", (Operand.reg "%shr.i.i596.i.i.lcssa.ph.off0")),
                                       ("while.cond.preheader.i.i599.i.i.epilog-lcssa", (Operand.reg "%extract.t1094"))],
        Instr.icmp "%tobool.not31.i.i600.i.i" (IPred.ult) 128 (Operand.reg "%add4.i.i594.i.i.lcssa") (Operand.imm (Const.int 128 0x00000000000000010000000000000000#128))
      ],
      term := Term.condbr (Operand.reg "%tobool.not31.i.i600.i.i") "stk_mul_u64.exit605.i.i" "while.body.us.i.i601.i.i" },
    { name := "while.body.us.i.i601.i.i",
      instrs := [
        Instr.binop "%inc12.us.i.i603.i.i" (BinOp.add) 32 (Operand.reg "%108") (Operand.imm (Const.int 32 0x00000001#32)),
        Instr.gep "%arrayidx14.us.i.i604.i.i" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%wide.trip.count.i.i587.i.i"),
        Instr.store (Ty.int 64) (Operand.reg "%shr.i.i596.i.i.lcssa.off0") (Operand.reg "%arrayidx14.us.i.i604.i.i")
      ],
      term := Term.br "stk_mul_u64.exit605.i.i" },
    { name := "for.body.i.i588.i.i",
      instrs := [
        Instr.phi "%indvars.iv.i.i589.i.i" (Ty.int 64) [("for.body.lr.ph.i.i586.i.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i.i588.i.i", (Operand.reg "%indvars.iv.next.i.i597.i.i.3"))],
        Instr.phi "%carry.029.i.i590.i.i" (Ty.int 128) [("for.body.lr.ph.i.i586.i.i.new", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
                                       ("for.body.i.i588.i.i", (Operand.reg "%shr.i.i596.i.i.3"))],
        Instr.phi "%niter1075" (Ty.int 64) [("for.body.lr.ph.i.i586.i.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i.i588.i.i", (Operand.reg "%niter1075.next.3"))],
        Instr.gep "%arrayidx.i.i591.i.i" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.i.i589.i.i"),
        Instr.load "%111" (Ty.int 64) (Operand.reg "%arrayidx.i.i591.i.i"),
        Instr.zext "%conv2.i.i592.i.i" 64 128 (Operand.reg "%111"),
        Instr.binop "%mul.i.i593.i.i" (BinOp.mul) 128 (Operand.reg "%conv2.i.i592.i.i") (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
        Instr.binop "%add4.i.i594.i.i" (BinOp.add) 128 (Operand.reg "%mul.i.i593.i.i") (Operand.reg "%carry.029.i.i590.i.i"),
        Instr.trunc "%conv5.i.i595.i.i" 128 64 (Operand.reg "%add4.i.i594.i.i"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i595.i.i") (Operand.reg "%arrayidx.i.i591.i.i"),
        Instr.binop "%shr.i.i596.i.i" (BinOp.lshr) 128 (Operand.reg "%add4.i.i594.i.i") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.i597.i.i" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i589.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.gep "%arrayidx.i.i591.i.i.1" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.next.i.i597.i.i"),
        Instr.load "%112" (Ty.int 64) (Operand.reg "%arrayidx.i.i591.i.i.1"),
        Instr.zext "%conv2.i.i592.i.i.1" 64 128 (Operand.reg "%112"),
        Instr.binop "%mul.i.i593.i.i.1" (BinOp.mul) 128 (Operand.reg "%conv2.i.i592.i.i.1") (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
        Instr.binop "%add4.i.i594.i.i.1" (BinOp.add) 128 (Operand.reg "%mul.i.i593.i.i.1") (Operand.reg "%shr.i.i596.i.i"),
        Instr.trunc "%conv5.i.i595.i.i.1" 128 64 (Operand.reg "%add4.i.i594.i.i.1"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i595.i.i.1") (Operand.reg "%arrayidx.i.i591.i.i.1"),
        Instr.binop "%shr.i.i596.i.i.1" (BinOp.lshr) 128 (Operand.reg "%add4.i.i594.i.i.1") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.i597.i.i.1" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i589.i.i") (Operand.imm (Const.int 64 0x0000000000000002#64)),
        Instr.gep "%arrayidx.i.i591.i.i.2" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.next.i.i597.i.i.1"),
        Instr.load "%113" (Ty.int 64) (Operand.reg "%arrayidx.i.i591.i.i.2"),
        Instr.zext "%conv2.i.i592.i.i.2" 64 128 (Operand.reg "%113"),
        Instr.binop "%mul.i.i593.i.i.2" (BinOp.mul) 128 (Operand.reg "%conv2.i.i592.i.i.2") (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
        Instr.binop "%add4.i.i594.i.i.2" (BinOp.add) 128 (Operand.reg "%mul.i.i593.i.i.2") (Operand.reg "%shr.i.i596.i.i.1"),
        Instr.trunc "%conv5.i.i595.i.i.2" 128 64 (Operand.reg "%add4.i.i594.i.i.2"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i595.i.i.2") (Operand.reg "%arrayidx.i.i591.i.i.2"),
        Instr.binop "%shr.i.i596.i.i.2" (BinOp.lshr) 128 (Operand.reg "%add4.i.i594.i.i.2") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.i597.i.i.2" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i589.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
        Instr.gep "%arrayidx.i.i591.i.i.3" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.next.i.i597.i.i.2"),
        Instr.load "%114" (Ty.int 64) (Operand.reg "%arrayidx.i.i591.i.i.3"),
        Instr.zext "%conv2.i.i592.i.i.3" 64 128 (Operand.reg "%114"),
        Instr.binop "%mul.i.i593.i.i.3" (BinOp.mul) 128 (Operand.reg "%conv2.i.i592.i.i.3") (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
        Instr.binop "%add4.i.i594.i.i.3" (BinOp.add) 128 (Operand.reg "%mul.i.i593.i.i.3") (Operand.reg "%shr.i.i596.i.i.2"),
        Instr.trunc "%conv5.i.i595.i.i.3" 128 64 (Operand.reg "%add4.i.i594.i.i.3"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i595.i.i.3") (Operand.reg "%arrayidx.i.i591.i.i.3"),
        Instr.binop "%shr.i.i596.i.i.3" (BinOp.lshr) 128 (Operand.reg "%add4.i.i594.i.i.3") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.i597.i.i.3" (BinOp.add) 64 (Operand.reg "%indvars.iv.i.i589.i.i") (Operand.imm (Const.int 64 0x0000000000000004#64)),
        Instr.binop "%niter1075.next.3" (BinOp.add) 64 (Operand.reg "%niter1075") (Operand.imm (Const.int 64 0x0000000000000004#64)),
        Instr.icmp "%niter1075.ncmp.3" (IPred.eq) 64 (Operand.reg "%niter1075.next.3") (Operand.reg "%unroll_iter1074")
      ],
      term := Term.condbr (Operand.reg "%niter1075.ncmp.3") "while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit" "for.body.i.i588.i.i" },
    { name := "stk_mul_u64.exit605.i.i",
      instrs := [
        Instr.phi "%115" (Ty.int 32) [("while.body187.i.i", (Operand.reg "%108")),
                                       ("while.cond.preheader.i.i599.i.i", (Operand.reg "%108")),
                                       ("while.body.us.i.i601.i.i", (Operand.reg "%inc12.us.i.i603.i.i"))],
        Instr.binop "%sub189.i.i" (BinOp.add) 64 (Operand.reg "%k183.0754.i.i") (Operand.imm (Const.int 64 0xffffffffffffffed#64)),
        Instr.icmp "%cmp185.i.i" (IPred.sgt) 64 (Operand.reg "%k183.0754.i.i") (Operand.imm (Const.int 64 0x0000000000000025#64))
      ],
      term := Term.condbr (Operand.reg "%cmp185.i.i") "while.body187.i.i" "while.end190.i.i" },
    { name := "while.end190.i.i",
      instrs := [
        Instr.phi "%116" (Ty.int 32) [("while.cond184.preheader.i.i", (Operand.reg "%n.i.promoted751.i.i")),
                                       ("stk_mul_u64.exit605.i.i", (Operand.reg "%115"))],
        Instr.phi "%k183.0.lcssa.i.i" (Ty.int 64) [("while.cond184.preheader.i.i", (Operand.reg "%add108.i.i")),
                                       ("stk_mul_u64.exit605.i.i", (Operand.reg "%sub189.i.i"))],
        Instr.store (Ty.int 32) (Operand.reg "%116") (Operand.reg "%n.i.i.i"),
        Instr.icmp "%tobool191.not.i.i" (IPred.ne) 64 (Operand.reg "%k183.0.lcssa.i.i") (Operand.imm (Const.int 64 0x0000000000000000#64)),
        Instr.icmp "%cmp28.i.i607.i.i" (IPred.sgt) 32 (Operand.reg "%116") (Operand.imm (Const.int 32 0x00000000#32)),
        Instr.select "%or.cond865.i.i" (Ty.int 1) (Operand.reg "%tobool191.not.i.i") (Operand.reg "%cmp28.i.i607.i.i") (Operand.imm (Const.int 1 0x0#1))
      ],
      term := Term.condbr (Operand.reg "%or.cond865.i.i") "for.body.lr.ph.i.i608.i.i" "if.end195.i.i" },
    { name := "for.body.lr.ph.i.i608.i.i",
      instrs := [
        Instr.gep "%arrayidx194.i.i" (Ty.int 64) (Operand.global "@NUMF_EL1_P10") (Operand.reg "%k183.0.lcssa.i.i"),
        Instr.load "%117" (Ty.int 64) (Operand.reg "%arrayidx194.i.i"),
        Instr.zext "%conv3.i.i609.i.i" 64 128 (Operand.reg "%117"),
        Instr.zext "%wide.trip.count.i.i610.i.i" 32 64 (Operand.reg "%116"),
        Instr.binop "%xtraiter1076" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i.i610.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
        Instr.icmp "%118" (IPred.ult) 32 (Operand.reg "%116") (Operand.imm (Const.int 32 0x00000004#32))
      ],
      term := Term.condbr (Operand.reg "%118") "while.cond.preheader.i.i622.i.i.unr-lcssa" "for.body.lr.ph.i.i608.i.i.new" },
    { name := "for.body.lr.ph.i.i608.i.i.new",
      instrs := [
        Instr.binop "%unroll_iter1081" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i.i610.i.i") (Operand.imm (Const.int 64 0x000000007ffffffc#64))
      ],
      term := Term.br "for.body.i.i611.i.i" },
    { name := "while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit",
      instrs := [
        Instr.trunc "%extract.t1097" 128 64 (Operand.reg "%shr.i.i619.i.i.3")
      ],
      term := Term.br "while.cond.preheader.i.i622.i.i.unr-lcssa" },
    { name := "while.cond.preheader.i.i622.i.i.unr-lcssa",
      instrs := [
        Instr.phi "%add4.i.i617.i.i.lcssa.ph" (Ty.int 128) [("for.body.lr.ph.i.i608.i.i", (Operand.imm Const.poison)),
                                       ("while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit", (Operand.reg "%add4.i.i617.i.i.3"))],
        Instr.phi "%shr.i.i619.i.i.lcssa.ph.off0" (Ty.int 64) [("for.body.lr.ph.i.i608.i.i", (Operand.imm Const.poison)),
                                       ("while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit", (Operand.reg "%extract.t1097"))],
        Instr.phi "%indvars.iv.i.i612.i.i.unr" (Ty.int 64) [("for.body.lr.ph.i.i608.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit", (Operand.reg "%indvars.iv.next.i.i620.i.i.3"))],
        Instr.phi "%carry.029.i.i613.i.i.unr" (Ty.int 128) [("for.body.lr.ph.i.i608.i.i", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
                                       ("while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit", (Operand.reg "%shr.i.i619.i.i.3"))],
        Instr.icmp "%lcmp.mod1078.not" (IPred.eq) 64 (Operand.reg "%xtraiter1076") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%lcmp.mod1078.not") "while.cond.preheader.i.i622.i.i" "for.body.i.i611.i.i.epil" },
    { name := "for.body.i.i611.i.i.epil",
      instrs := [
        Instr.phi "%indvars.iv.i.i612.i.i.epil" (Ty.int 64) [("for.body.i.i611.i.i.epil", (Operand.reg "%indvars.iv.next.i.i620.i.i.epil")),
                                       ("while.cond.preheader.i.i622.i.i.unr-lcssa", (Operand.reg "%indvars.iv.i.i612.i.i.unr"))],
        Instr.phi "%carry.029.i.i613.i.i.epil" (Ty.int 128) [("for.body.i.i611.i.i.epil", (Operand.reg "%shr.i.i619.i.i.epil")),
                                       ("while.cond.preheader.i.i622.i.i.unr-lcssa", (Operand.reg "%carry.029.i.i613.i.i.unr"))],
        Instr.phi "%epil.iter1077" (Ty.int 64) [("for.body.i.i611.i.i.epil", (Operand.reg "%epil.iter1077.next")),
                                       ("while.cond.preheader.i.i622.i.i.unr-lcssa", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.gep "%arrayidx.i.i614.i.i.epil" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.i.i612.i.i.epil"),
        Instr.load "%119" (Ty.int 64) (Operand.reg "%arrayidx.i.i614.i.i.epil"),
        Instr.zext "%conv2.i.i615.i.i.epil" 64 128 (Operand.reg "%119"),
        Instr.binop "%mul.i.i616.i.i.epil" (BinOp.mul) 128 (Operand.reg "%conv2.i.i615.i.i.epil") (Operand.reg "%conv3.i.i609.i.i"),
        Instr.binop "%add4.i.i617.i.i.epil" (BinOp.add) 128 (Operand.reg "%mul.i.i616.i.i.epil") (Operand.reg "%carry.029.i.i613.i.i.epil"),
        Instr.trunc "%conv5.i.i618.i.i.epil" 128 64 (Operand.reg "%add4.i.i617.i.i.epil"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i618.i.i.epil") (Operand.reg "%arrayidx.i.i614.i.i.epil"),
        Instr.binop "%shr.i.i619.i.i.epil" (BinOp.lshr) 128 (Operand.reg "%add4.i.i617.i.i.epil") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.i620.i.i.epil" (BinOp.add) 64 (Operand.reg "%indvars.iv.i.i612.i.i.epil") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.binop "%epil.iter1077.next" (BinOp.add) 64 (Operand.reg "%epil.iter1077") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%epil.iter1077.cmp.not" (IPred.eq) 64 (Operand.reg "%epil.iter1077.next") (Operand.reg "%xtraiter1076")
      ],
      term := Term.condbr (Operand.reg "%epil.iter1077.cmp.not") "while.cond.preheader.i.i622.i.i.epilog-lcssa" "for.body.i.i611.i.i.epil" },
    { name := "while.cond.preheader.i.i622.i.i.epilog-lcssa",
      instrs := [
        Instr.trunc "%extract.t1096" 128 64 (Operand.reg "%shr.i.i619.i.i.epil")
      ],
      term := Term.br "while.cond.preheader.i.i622.i.i" },
    { name := "while.cond.preheader.i.i622.i.i",
      instrs := [
        Instr.phi "%add4.i.i617.i.i.lcssa" (Ty.int 128) [("while.cond.preheader.i.i622.i.i.unr-lcssa", (Operand.reg "%add4.i.i617.i.i.lcssa.ph")),
                                       ("while.cond.preheader.i.i622.i.i.epilog-lcssa", (Operand.reg "%add4.i.i617.i.i.epil"))],
        Instr.phi "%shr.i.i619.i.i.lcssa.off0" (Ty.int 64) [("while.cond.preheader.i.i622.i.i.unr-lcssa", (Operand.reg "%shr.i.i619.i.i.lcssa.ph.off0")),
                                       ("while.cond.preheader.i.i622.i.i.epilog-lcssa", (Operand.reg "%extract.t1096"))],
        Instr.icmp "%tobool.not31.i.i623.i.i" (IPred.ult) 128 (Operand.reg "%add4.i.i617.i.i.lcssa") (Operand.imm (Const.int 128 0x00000000000000010000000000000000#128))
      ],
      term := Term.condbr (Operand.reg "%tobool.not31.i.i623.i.i") "if.end195.i.i" "while.body.us.i.i624.i.i" },
    { name := "while.body.us.i.i624.i.i",
      instrs := [
        Instr.binop "%inc12.us.i.i626.i.i" (BinOp.add) 32 (Operand.reg "%116") (Operand.imm (Const.int 32 0x00000001#32)),
        Instr.gep "%arrayidx14.us.i.i627.i.i" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%wide.trip.count.i.i610.i.i"),
        Instr.store (Ty.int 64) (Operand.reg "%shr.i.i619.i.i.lcssa.off0") (Operand.reg "%arrayidx14.us.i.i627.i.i"),
        Instr.store (Ty.int 32) (Operand.reg "%inc12.us.i.i626.i.i") (Operand.reg "%n.i.i.i")
      ],
      term := Term.br "if.end195.i.i" },
    { name := "for.body.i.i611.i.i",
      instrs := [
        Instr.phi "%indvars.iv.i.i612.i.i" (Ty.int 64) [("for.body.lr.ph.i.i608.i.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i.i611.i.i", (Operand.reg "%indvars.iv.next.i.i620.i.i.3"))],
        Instr.phi "%carry.029.i.i613.i.i" (Ty.int 128) [("for.body.lr.ph.i.i608.i.i.new", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
                                       ("for.body.i.i611.i.i", (Operand.reg "%shr.i.i619.i.i.3"))],
        Instr.phi "%niter1082" (Ty.int 64) [("for.body.lr.ph.i.i608.i.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i.i611.i.i", (Operand.reg "%niter1082.next.3"))],
        Instr.gep "%arrayidx.i.i614.i.i" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.i.i612.i.i"),
        Instr.load "%120" (Ty.int 64) (Operand.reg "%arrayidx.i.i614.i.i"),
        Instr.zext "%conv2.i.i615.i.i" 64 128 (Operand.reg "%120"),
        Instr.binop "%mul.i.i616.i.i" (BinOp.mul) 128 (Operand.reg "%conv2.i.i615.i.i") (Operand.reg "%conv3.i.i609.i.i"),
        Instr.binop "%add4.i.i617.i.i" (BinOp.add) 128 (Operand.reg "%mul.i.i616.i.i") (Operand.reg "%carry.029.i.i613.i.i"),
        Instr.trunc "%conv5.i.i618.i.i" 128 64 (Operand.reg "%add4.i.i617.i.i"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i618.i.i") (Operand.reg "%arrayidx.i.i614.i.i"),
        Instr.binop "%shr.i.i619.i.i" (BinOp.lshr) 128 (Operand.reg "%add4.i.i617.i.i") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.i620.i.i" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i612.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.gep "%arrayidx.i.i614.i.i.1" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.next.i.i620.i.i"),
        Instr.load "%121" (Ty.int 64) (Operand.reg "%arrayidx.i.i614.i.i.1"),
        Instr.zext "%conv2.i.i615.i.i.1" 64 128 (Operand.reg "%121"),
        Instr.binop "%mul.i.i616.i.i.1" (BinOp.mul) 128 (Operand.reg "%conv2.i.i615.i.i.1") (Operand.reg "%conv3.i.i609.i.i"),
        Instr.binop "%add4.i.i617.i.i.1" (BinOp.add) 128 (Operand.reg "%mul.i.i616.i.i.1") (Operand.reg "%shr.i.i619.i.i"),
        Instr.trunc "%conv5.i.i618.i.i.1" 128 64 (Operand.reg "%add4.i.i617.i.i.1"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i618.i.i.1") (Operand.reg "%arrayidx.i.i614.i.i.1"),
        Instr.binop "%shr.i.i619.i.i.1" (BinOp.lshr) 128 (Operand.reg "%add4.i.i617.i.i.1") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.i620.i.i.1" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i612.i.i") (Operand.imm (Const.int 64 0x0000000000000002#64)),
        Instr.gep "%arrayidx.i.i614.i.i.2" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.next.i.i620.i.i.1"),
        Instr.load "%122" (Ty.int 64) (Operand.reg "%arrayidx.i.i614.i.i.2"),
        Instr.zext "%conv2.i.i615.i.i.2" 64 128 (Operand.reg "%122"),
        Instr.binop "%mul.i.i616.i.i.2" (BinOp.mul) 128 (Operand.reg "%conv2.i.i615.i.i.2") (Operand.reg "%conv3.i.i609.i.i"),
        Instr.binop "%add4.i.i617.i.i.2" (BinOp.add) 128 (Operand.reg "%mul.i.i616.i.i.2") (Operand.reg "%shr.i.i619.i.i.1"),
        Instr.trunc "%conv5.i.i618.i.i.2" 128 64 (Operand.reg "%add4.i.i617.i.i.2"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i618.i.i.2") (Operand.reg "%arrayidx.i.i614.i.i.2"),
        Instr.binop "%shr.i.i619.i.i.2" (BinOp.lshr) 128 (Operand.reg "%add4.i.i617.i.i.2") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.i620.i.i.2" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i612.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
        Instr.gep "%arrayidx.i.i614.i.i.3" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.next.i.i620.i.i.2"),
        Instr.load "%123" (Ty.int 64) (Operand.reg "%arrayidx.i.i614.i.i.3"),
        Instr.zext "%conv2.i.i615.i.i.3" 64 128 (Operand.reg "%123"),
        Instr.binop "%mul.i.i616.i.i.3" (BinOp.mul) 128 (Operand.reg "%conv2.i.i615.i.i.3") (Operand.reg "%conv3.i.i609.i.i"),
        Instr.binop "%add4.i.i617.i.i.3" (BinOp.add) 128 (Operand.reg "%mul.i.i616.i.i.3") (Operand.reg "%shr.i.i619.i.i.2"),
        Instr.trunc "%conv5.i.i618.i.i.3" 128 64 (Operand.reg "%add4.i.i617.i.i.3"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i618.i.i.3") (Operand.reg "%arrayidx.i.i614.i.i.3"),
        Instr.binop "%shr.i.i619.i.i.3" (BinOp.lshr) 128 (Operand.reg "%add4.i.i617.i.i.3") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.i620.i.i.3" (BinOp.add) 64 (Operand.reg "%indvars.iv.i.i612.i.i") (Operand.imm (Const.int 64 0x0000000000000004#64)),
        Instr.binop "%niter1082.next.3" (BinOp.add) 64 (Operand.reg "%niter1082") (Operand.imm (Const.int 64 0x0000000000000004#64)),
        Instr.icmp "%niter1082.ncmp.3" (IPred.eq) 64 (Operand.reg "%niter1082.next.3") (Operand.reg "%unroll_iter1081")
      ],
      term := Term.condbr (Operand.reg "%niter1082.ncmp.3") "while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit" "for.body.i.i611.i.i" },
    { name := "if.end195.i.i",
      instrs := [
        Instr.store (Ty.int 64) (Operand.imm (Const.int 64 0x0000000000000000#64)) (Operand.reg "%S128.i.i")
      ],
      term := Term.br "if.end198.i.i" },
    { name := "if.end198.i.i",
      instrs := [
        Instr.binop "%reass.sub" (BinOp.sub) 64 (Operand.reg "%add110.i.i") (Operand.reg "%topn.0711.i.i"),
        Instr.binop "%sub200.i.i" (BinOp.add) 64 (Operand.reg "%reass.sub") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.uitofp "%conv202.i.i" 64 (Operand.reg "%top.0709.i.i")
      ],
      term := Term.br "while.cond203.i.i" },
    { name := "while.cond203.i.i",
      instrs := [
        Instr.phi "%e10.0.i.i" (Ty.int 64) [("if.end198.i.i", (Operand.reg "%sub200.i.i")),
                                       ("while.body206.i.i", (Operand.reg "%sub219.i.i"))],
        Instr.phi "%d201.0.i.i" Ty.double [("if.end198.i.i", (Operand.reg "%conv202.i.i")),
                                       ("while.body206.i.i", (Operand.reg "%mul217.i.i"))],
        Instr.icmp "%cmp204.i.i" (IPred.sgt) 64 (Operand.reg "%e10.0.i.i") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%cmp204.i.i") "while.body206.i.i" "while.cond229.i.i.preheader" },
    { name := "while.body206.i.i",
      instrs := [
        Instr.icmp "%124.min" (IPred.ult) 64 (Operand.reg "%e10.0.i.i") (Operand.imm (Const.int 64 0x0000000000000016#64)),
        Instr.select "%124" (Ty.int 64) (Operand.reg "%124.min") (Operand.reg "%e10.0.i.i") (Operand.imm (Const.int 64 0x0000000000000016#64)),
        Instr.gep "%arrayidx216.i.i" Ty.double (Operand.global "@NUMF_EL1_POW10") (Operand.reg "%124"),
        Instr.load "%125" Ty.double (Operand.reg "%arrayidx216.i.i"),
        Instr.fmul "%mul217.i.i" (Operand.reg "%d201.0.i.i") (Operand.reg "%125"),
        Instr.binop "%sub219.i.i" (BinOp.sub) 64 (Operand.reg "%e10.0.i.i") (Operand.reg "%124"),
        Instr.bitcastToInt "%.cast.i.i.i" (Operand.reg "%mul217.i.i"),
        Instr.icmp "%cmp221.i.i" (IPred.ugt) 64 (Operand.reg "%.cast.i.i.i") (Operand.imm (Const.int 64 0x7fefffffffffffff#64))
      ],
      term := Term.condbr (Operand.reg "%cmp221.i.i") "while.cond229.i.i.preheader" "while.cond203.i.i" },
    { name := "while.cond229.i.i.preheader",
      instrs := [
        Instr.phi "%e10.2.i.i.ph" (Ty.int 64) [("while.cond203.i.i", (Operand.reg "%e10.0.i.i")),
                                       ("while.body206.i.i", (Operand.reg "%sub219.i.i"))],
        Instr.phi "%d201.2.i.i.ph" Ty.double [("while.cond203.i.i", (Operand.reg "%d201.0.i.i")),
                                       ("while.body206.i.i", (Operand.reg "%mul217.i.i"))]
      ],
      term := Term.br "while.cond229.i.i" },
    { name := "while.cond229.i.i",
      instrs := [
        Instr.phi "%e10.2.i.i" (Ty.int 64) [("while.body232.i.i", (Operand.reg "%add245.i.i")),
                                       ("while.cond229.i.i.preheader", (Operand.reg "%e10.2.i.i.ph"))],
        Instr.phi "%d201.2.i.i" Ty.double [("while.body232.i.i", (Operand.reg "%div.i.i")),
                                       ("while.cond229.i.i.preheader", (Operand.reg "%d201.2.i.i.ph"))],
        Instr.icmp "%cmp230.i.i" (IPred.slt) 64 (Operand.reg "%e10.2.i.i") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%cmp230.i.i") "while.body232.i.i" "while.end253.i.i" },
    { name := "while.body232.i.i",
      instrs := [
        Instr.icmp "%cmp234.i.i" (IPred.ult) 64 (Operand.reg "%e10.2.i.i") (Operand.imm (Const.int 64 0xffffffffffffffea#64)),
        Instr.binop "%.neg.i.i" (BinOp.mul) 64 (Operand.reg "%e10.2.i.i") (Operand.imm (Const.int 64 0xffffffff00000000#64)),
        Instr.binop "%126" (BinOp.ashr) 64 (Operand.reg "%.neg.i.i") (Operand.imm (Const.int 64 0x0000000000000020#64)),
        Instr.select "%idxprom242.i.i" (Ty.int 64) (Operand.reg "%cmp234.i.i") (Operand.imm (Const.int 64 0x0000000000000016#64)) (Operand.reg "%126"),
        Instr.gep "%arrayidx243.i.i" Ty.double (Operand.global "@NUMF_EL1_POW10") (Operand.reg "%idxprom242.i.i"),
        Instr.load "%127" Ty.double (Operand.reg "%arrayidx243.i.i"),
        Instr.fdiv "%div.i.i" (Operand.reg "%d201.2.i.i") (Operand.reg "%127"),
        Instr.binop "%add245.i.i" (BinOp.add) 64 (Operand.reg "%idxprom242.i.i") (Operand.reg "%e10.2.i.i"),
        Instr.fcmp "%cmp246.i.i" (FPred.oeq) (Operand.reg "%div.i.i") (Operand.imm (Const.float 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%cmp246.i.i") "while.end253.i.i" "while.cond229.i.i" },
    { name := "while.end253.i.i",
      instrs := [
        Instr.phi "%d201.3.i.i" Ty.double [("while.body232.i.i", (Operand.reg "%div.i.i")),
                                       ("while.cond229.i.i", (Operand.reg "%d201.2.i.i"))],
        Instr.bitcastToInt "%.cast.i629.i.i" (Operand.reg "%d201.3.i.i")
      ],
      term := Term.br "for.cond255.i.i" },
    { name := "for.cond255.i.i",
      instrs := [
        Instr.phi "%b.0.i.i" (Ty.int 64) [("while.end253.i.i", (Operand.reg "%.cast.i629.i.i")),
                                       ("for.cond255.i.i.backedge", (Operand.reg "%b.0.i.i.be"))],
        Instr.icmp "%cmp256.i.i" (IPred.eq) 64 (Operand.reg "%b.0.i.i") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%cmp256.i.i") "if.then258.i.i" "if.end264.i.i" },
    { name := "if.then258.i.i",
      instrs := [
        Instr.call "%call259.i.i" (Ty.int 32) "stk_cmp" [(Ty.ptr, (Operand.reg "%v.i.i")),
                             ((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000001#64))),
                             ((Ty.int 64), (Operand.imm (Const.int 64 0xfffffffffffffbcd#64)))],
        Instr.icmp "%cmp260.i.i" (IPred.sgt) 32 (Operand.reg "%call259.i.i") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%cmp260.i.i") "for.cond255.i.i.backedge" "for.end359.i.i" },
    { name := "if.end264.i.i",
      instrs := [
        Instr.icmp "%cmp265.i.i" (IPred.ugt) 64 (Operand.reg "%b.0.i.i") (Operand.imm (Const.int 64 0x7fefffffffffffff#64))
      ],
      term := Term.condbr (Operand.reg "%cmp265.i.i") "if.then267.i.i" "if.end273.i.i" },
    { name := "if.then267.i.i",
      instrs := [
        Instr.call "%call268.i.i" (Ty.int 32) "stk_cmp" [(Ty.ptr, (Operand.reg "%v.i.i")),
                             ((Ty.int 64), (Operand.imm (Const.int 64 0x003fffffffffffff#64))),
                             ((Ty.int 64), (Operand.imm (Const.int 64 0x00000000000003ca#64)))],
        Instr.icmp "%cmp269.i.i" (IPred.slt) 32 (Operand.reg "%call268.i.i") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%cmp269.i.i") "for.cond255.i.i.backedge" "for.end359.i.i" },
    { name := "if.end273.i.i",
      instrs := [
        Instr.binop "%shr.i.i" (BinOp.lshr) 64 (Operand.reg "%b.0.i.i") (Operand.imm (Const.int 64 0x0000000000000034#64)),
        Instr.icmp "%cmp275.i.i" (IPred.ult) 64 (Operand.reg "%b.0.i.i") (Operand.imm (Const.int 64 0x0010000000000000#64)),
        Instr.binop "%and280.i.i" (BinOp.and) 64 (Operand.reg "%b.0.i.i") (Operand.imm (Const.int 64 0x000fffffffffffff#64)),
        Instr.binop "%or.i.i" (BinOp.or) 64 (Operand.reg "%and280.i.i") (Operand.imm (Const.int 64 0x0010000000000000#64)),
        Instr.select "%cond282.i.i" (Ty.int 64) (Operand.reg "%cmp275.i.i") (Operand.reg "%b.0.i.i") (Operand.reg "%or.i.i"),
        Instr.binop "%sub288.i.i" (BinOp.add) 64 (Operand.reg "%shr.i.i") (Operand.imm (Const.int 64 0xfffffffffffffbcd#64)),
        Instr.select "%cond290.i.i" (Ty.int 64) (Operand.reg "%cmp275.i.i") (Operand.imm (Const.int 64 0xfffffffffffffbce#64)) (Operand.reg "%sub288.i.i"),
        Instr.call "%call291.i.i" (Ty.int 32) "stk_cmp" [(Ty.ptr, (Operand.reg "%v.i.i")),
                             ((Ty.int 64), (Operand.reg "%cond282.i.i")),
                             ((Ty.int 64), (Operand.reg "%cond290.i.i"))],
        Instr.icmp "%cmp292.i.i" (IPred.eq) 32 (Operand.reg "%call291.i.i") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%cmp292.i.i") "for.end359.i.i" "if.end295.i.i" },
    { name := "if.end295.i.i",
      instrs := [
        Instr.icmp "%cmp296.i.i" (IPred.sgt) 32 (Operand.reg "%call291.i.i") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%cmp296.i.i") "if.then298.i.i" "if.end318.i.i" },
    { name := "if.then298.i.i",
      instrs := [
        Instr.binop "%mul299.i.i" (BinOp.shl) 64 (Operand.reg "%cond282.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.binop "%add300.i.i" (BinOp.or) 64 (Operand.reg "%mul299.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.binop "%sub301.i.i" (BinOp.add) 64 (Operand.reg "%cond290.i.i") (Operand.imm (Const.int 64 0xffffffffffffffff#64)),
        Instr.call "%call302.i.i" (Ty.int 32) "stk_cmp" [(Ty.ptr, (Operand.reg "%v.i.i")),
                             ((Ty.int 64), (Operand.reg "%add300.i.i")),
                             ((Ty.int 64), (Operand.reg "%sub301.i.i"))],
        Instr.icmp "%cmp303.i.i" (IPred.slt) 32 (Operand.reg "%call302.i.i") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%cmp303.i.i") "for.end359.i.i" "if.end306.i.i" },
    { name := "if.end306.i.i",
      instrs := [
        Instr.icmp "%cmp307.i.i" (IPred.eq) 32 (Operand.reg "%call302.i.i") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%cmp307.i.i") "if.then309.i.i" "if.end315.i.i" },
    { name := "if.then309.i.i",
      instrs := [
        Instr.binop "%and310.i.i" (BinOp.and) 64 (Operand.reg "%cond282.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.binop "%spec.select507.i.i" (BinOp.add) 64 (Operand.reg "%and310.i.i") (Operand.reg "%b.0.i.i")
      ],
      term := Term.br "for.end359.i.i" },
    { name := "if.end315.i.i",
      instrs := [
        Instr.binop "%inc316.i.i" (BinOp.add) 64 (Operand.reg "%b.0.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64))
      ],
      term := Term.br "for.cond255.i.i.backedge" },
    { name := "if.end318.i.i",
      instrs := [
        Instr.icmp "%cmp322.i.i" (IPred.ugt) 64 (Operand.reg "%cond282.i.i") (Operand.imm (Const.int 64 0x0010000000000000#64)),
        Instr.binop "%or.cond391.i.i" (BinOp.or) 1 (Operand.reg "%cmp275.i.i") (Operand.reg "%cmp322.i.i")
      ],
      term := Term.condbr (Operand.reg "%or.cond391.i.i") "if.then324.i.i" "if.else328.i.i" },
    { name := "if.then324.i.i",
      instrs := [
        Instr.binop "%mul325.i.i" (BinOp.shl) 64 (Operand.reg "%cond282.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.binop "%sub326.i.i" (BinOp.add) 64 (Operand.reg "%mul325.i.i") (Operand.imm (Const.int 64 0xffffffffffffffff#64)),
        Instr.binop "%sub327.i.i" (BinOp.add) 64 (Operand.reg "%cond290.i.i") (Operand.imm (Const.int 64 0xffffffffffffffff#64))
      ],
      term := Term.br "if.end335.i.i" },
    { name := "if.else328.i.i",
      instrs := [
        Instr.icmp "%cmp329.i.i" (IPred.eq) 64 (Operand.reg "%shr.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.binop "%sub333.i.i" (BinOp.add) 64 (Operand.reg "%shr.i.i") (Operand.imm (Const.int 64 0xfffffffffffffbcb#64)),
        Instr.select "%spec.select511.i.i" (Ty.int 64) (Operand.reg "%cmp329.i.i") (Operand.imm (Const.int 64 0x001fffffffffffff#64)) (Operand.imm (Const.int 64 0x003fffffffffffff#64)),
        Instr.select "%spec.select512.i.i" (Ty.int 64) (Operand.reg "%cmp329.i.i") (Operand.imm (Const.int 64 0xfffffffffffffbcd#64)) (Operand.reg "%sub333.i.i")
      ],
      term := Term.br "if.end335.i.i" },
    { name := "if.end335.i.i",
      instrs := [
        Instr.phi "%J.0.i.i" (Ty.int 64) [("if.then324.i.i", (Operand.reg "%sub326.i.i")),
                                       ("if.else328.i.i", (Operand.reg "%spec.select511.i.i"))],
        Instr.phi "%eB.0.i.i" (Ty.int 64) [("if.then324.i.i", (Operand.reg "%sub327.i.i")),
                                       ("if.else328.i.i", (Operand.reg "%spec.select512.i.i"))],
        Instr.call "%call336.i.i" (Ty.int 32) "stk_cmp" [(Ty.ptr, (Operand.reg "%v.i.i")),
                             ((Ty.int 64), (Operand.reg "%J.0.i.i")),
                             ((Ty.int 64), (Operand.reg "%eB.0.i.i"))],
        Instr.icmp "%cmp337.i.i" (IPred.sgt) 32 (Operand.reg "%call336.i.i") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%cmp337.i.i") "for.end359.i.i" "if.end340.i.i" },
    { name := "if.end340.i.i",
      instrs := [
        Instr.icmp "%cmp341.i.i" (IPred.eq) 32 (Operand.reg "%call336.i.i") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%cmp341.i.i") "if.then343.i.i" "if.end348.i.i" },
    { name := "if.then343.i.i",
      instrs := [
        Instr.binop "%128" (BinOp.and) 64 (Operand.reg "%cond282.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.binop "%spec.select508.i.i" (BinOp.sub) 64 (Operand.reg "%b.0.i.i") (Operand.reg "%128")
      ],
      term := Term.br "for.end359.i.i" },
    { name := "if.end348.i.i",
      instrs := [
        Instr.binop "%dec349.i.i" (BinOp.add) 64 (Operand.reg "%b.0.i.i") (Operand.imm (Const.int 64 0xffffffffffffffff#64))
      ],
      term := Term.br "for.cond255.i.i.backedge" },
    { name := "for.cond255.i.i.backedge",
      instrs := [
        Instr.phi "%b.0.i.i.be" (Ty.int 64) [("if.then258.i.i", (Operand.imm (Const.int 64 0x0000000000000001#64))),
                                       ("if.then267.i.i", (Operand.imm (Const.int 64 0x7fefffffffffffff#64))),
                                       ("if.end315.i.i", (Operand.reg "%inc316.i.i")),
                                       ("if.end348.i.i", (Operand.reg "%dec349.i.i"))]
      ],
      term := Term.br "for.cond255.i.i" },
    { name := "for.end359.i.i",
      instrs := [
        Instr.phi "%b.6.i.i" (Ty.int 64) [("if.then343.i.i", (Operand.reg "%spec.select508.i.i")),
                                       ("if.then309.i.i", (Operand.reg "%spec.select507.i.i")),
                                       ("if.end273.i.i", (Operand.reg "%b.0.i.i")),
                                       ("if.then298.i.i", (Operand.reg "%b.0.i.i")),
                                       ("if.end335.i.i", (Operand.reg "%b.0.i.i")),
                                       ("if.then267.i.i", (Operand.imm (Const.int 64 0x7ff0000000000000#64))),
                                       ("if.then258.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.bitcastToDouble "%.cast.i630.i.i" (Operand.reg "%b.6.i.i"),
        Instr.fneg "%fneg363.i.i" (Operand.reg "%.cast.i630.i.i"),
        Instr.select "%cond366.i.i" Ty.double (Operand.reg "%cmp1.i") (Operand.reg "%fneg363.i.i") (Operand.reg "%.cast.i630.i.i"),
        Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000620#64))),
                             (Ty.ptr, (Operand.reg "%v.i.i"))]
      ],
      term := Term.br "if.end291" },
    { name := "if.end291",
      instrs := [
        Instr.phi "%retval.1.i.i" Ty.double [("if.then59.i.i", (Operand.reg "%cond.i.i")),
                                       ("if.then123.i.i", (Operand.reg "%cond125.i.i")),
                                       ("for.end359.i.i", (Operand.reg "%cond366.i.i")),
                                       ("if.then113.i.i", (Operand.reg "%spec.select694.i.i"))],
        Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000300#64))),
                             (Ty.ptr, (Operand.reg "%dig.i.i"))],
        Instr.store Ty.double (Operand.reg "%retval.1.i.i") (Operand.reg "%out")
      ],
      term := Term.br "cleanup300" },
    { name := "cleanup300",
      instrs := [
        Instr.phi "%retval.8" (Ty.int 32) [("if.then5", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("if.then89", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("if.else66", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("if.then229", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("cleanup223", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("cleanup282", (Operand.imm (Const.int 32 0x00000001#32))),
                                       ("cleanup282.thread", (Operand.imm (Const.int 32 0x00000001#32))),
                                       ("if.end291", (Operand.imm (Const.int 32 0x00000001#32))),
                                       ("if.then5.i", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("if.then58.i", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("if.then119.i", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("if.then141.i", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("if.else35.i", (Operand.imm (Const.int 32 0x00000000#32)))]
      ],
      term := Term.ret (Ty.int 32) (some (Operand.reg "%retval.8")) }] }

-- Parsing the fixture under the declared layout returns `numFastBody`.
#guard decide (firstFunctionWith numFastLayout numFastSrc = some numFastBody)

/-! #### The controls

The extent and the text, each beside the assertion that it is not decoration. -/
-- The same bytes under a different struct extent are not this body.
#guard decide (firstFunctionWith [("Stk", 1572)] numFastSrc ≠ some numFastBody)
-- One immediate changed still parses, and is not this body.
def numFastSrcMutated : String := numFastSrc.replace "icmp eq i64 %n, 0" "icmp eq i64 %n, 1"
#guard decide (firstFunctionWith numFastLayout numFastSrcMutated ≠ some numFastBody)

-- The body's blocks are a parse of the text, not of a search that accepts
-- anything: `land.rhs` is the sibling `s2_string_body`'s block and is absent
-- here, and two of this body's blocks are distinct.
#guard decide (numFastBody.findBlock "land.rhs" = none)
#guard decide (numFastBody.findBlock "entry" ≠ numFastBody.findBlock "if.end")

/-! ### The blocks the runs read, as instruction lists

Each is the literal the generated pin below resolves the name to, named once so a
step theorem can rewrite with it; `*Instrs_eq` is the projection that keeps the
list tied to `findBlock`. -/
def numFastEntryInstrs : List Instr :=
  [
    Instr.alloca "%dig.i.i" (Ty.array 768 (Ty.int 8)) 0,
    Instr.alloca "%v.i.i" (Ty.struct "Stk" 1568) 0,
    Instr.alloca "%v8" (Ty.int 32) 0,
    Instr.alloca "%v8101" (Ty.int 32) 0,
    Instr.alloca "%d269" Ty.double 0,
    Instr.icmp "%cmp.not" (IPred.eq) 64 (Operand.reg "%n") (Operand.imm (Const.int 64 0x0000000000000000#64))]

def numFastLandLhsTrueInstrs : List Instr :=
  [
    Instr.load "%0" (Ty.int 8) (Operand.reg "%p"),
    Instr.icmp "%cmp1" (IPred.ne) 8 (Operand.reg "%0") (Operand.imm (Const.int 8 0x2d#8)),
    Instr.binop "%not.cmp1" (BinOp.xor) 1 (Operand.reg "%cmp1") (Operand.imm (Const.int 1 0x1#1)),
    Instr.zext "%spec.select439" 1 64 (Operand.reg "%not.cmp1")]

def numFastIfEndInstrs : List Instr :=
  [
    Instr.phi "%tobool274.not" (Ty.int 1) [("entry", (Operand.imm (Const.int 1 0x1#1))),
                                       ("land.lhs.true", (Operand.reg "%cmp1"))],
    Instr.phi "%i.0" (Ty.int 64) [("entry", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("land.lhs.true", (Operand.reg "%spec.select439"))],
    Instr.icmp "%cmp3.not" (IPred.ult) 64 (Operand.reg "%i.0") (Operand.reg "%n")]

def numFastIfThen5Instrs : List Instr :=
  [
    Instr.store (Ty.int 64) (Operand.reg "%i.0") (Operand.reg "%err")]

def numFastIfEnd6Instrs : List Instr :=
  [
    Instr.gep "%arrayidx7" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.0"),
    Instr.load "%1" (Ty.int 8) (Operand.reg "%arrayidx7"),
    Instr.icmp "%cmp9" (IPred.eq) 8 (Operand.reg "%1") (Operand.imm (Const.int 8 0x30#8))]

def numFastIfElseInstrs : List Instr :=
  [
    Instr.binop "%2" (BinOp.add) 8 (Operand.reg "%1") (Operand.imm (Const.int 8 0xcf#8)),
    Instr.icmp "%or.cond" (IPred.ult) 8 (Operand.reg "%2") (Operand.imm (Const.int 8 0x09#8))]

def numFastLandLhsTrue41Instrs : List Instr :=
  [
    Instr.phi "%i.4575" (Ty.int 64) [("if.end62", (Operand.reg "%inc64")),
                                       ("land.lhs.true41.preheader", (Operand.reg "%i.1558"))],
    Instr.phi "%idig.3574" (Ty.int 64) [("if.end62", (Operand.reg "%inc63")),
                                       ("land.lhs.true41.preheader", (Operand.reg "%idig.0560"))],
    Instr.phi "%ip.3573" (Ty.int 64) [("if.end62", (Operand.reg "%ip.4")),
                                       ("land.lhs.true41.preheader", (Operand.reg "%ip.0562"))],
    Instr.gep "%arrayidx42" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.4575"),
    Instr.load "%8" (Ty.int 8) (Operand.reg "%arrayidx42"),
    Instr.binop "%9" (BinOp.add) 8 (Operand.reg "%8") (Operand.imm (Const.int 8 0xd0#8)),
    Instr.icmp "%or.cond440" (IPred.ult) 8 (Operand.reg "%9") (Operand.imm (Const.int 8 0x0a#8))]

def numFastWhileBody52Instrs : List Instr :=
  [
    Instr.icmp "%cmp53" (IPred.ult) 64 (Operand.reg "%idig.3574") (Operand.imm (Const.int 64 0x0000000000000013#64))]

def numFastIfThen55Instrs : List Instr :=
  [
    Instr.binop "%mul56" (BinOp.mul) 64 (Operand.reg "%ip.3573") (Operand.imm (Const.int 64 0x000000000000000a#64)),
    Instr.binop "%10" (BinOp.and) 8 (Operand.reg "%8") (Operand.imm (Const.int 8 0x0f#8)),
    Instr.zext "%conv60" 8 64 (Operand.reg "%10"),
    Instr.binop "%add61" (BinOp.add) 64 (Operand.reg "%mul56") (Operand.reg "%conv60")]

def numFastIfEnd62Instrs : List Instr :=
  [
    Instr.phi "%ip.4" (Ty.int 64) [("if.then55", (Operand.reg "%add61")),
                                       ("while.body52", (Operand.reg "%ip.3573"))],
    Instr.binop "%inc63" (BinOp.add) 64 (Operand.reg "%idig.3574") (Operand.imm (Const.int 64 0x0000000000000001#64)),
    Instr.binop "%inc64" (BinOp.add) 64 (Operand.reg "%i.4575") (Operand.imm (Const.int 64 0x0000000000000001#64)),
    Instr.icmp "%exitcond.not" (IPred.eq) 64 (Operand.reg "%inc64") (Operand.reg "%n")]

def numFastIfElse66Instrs : List Instr :=
  [
    Instr.store (Ty.int 64) (Operand.reg "%i.0") (Operand.reg "%err")]

def numFastIfEnd68Instrs : List Instr :=
  [
    Instr.phi "%ip.5" (Ty.int 64) [("if.then11", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("while.end", (Operand.reg "%ip.0562")),
                                       ("land.lhs.true41", (Operand.reg "%ip.3573"))],
    Instr.phi "%idig.4" (Ty.int 64) [("if.then11", (Operand.imm (Const.int 64 0x0000000000000001#64))),
                                       ("while.end", (Operand.reg "%idig.0560")),
                                       ("land.lhs.true41", (Operand.reg "%idig.3574"))],
    Instr.phi "%i.5" (Ty.int 64) [("if.then11", (Operand.reg "%inc12")),
                                       ("while.end", (Operand.reg "%i.1558")),
                                       ("land.lhs.true41", (Operand.reg "%i.4575"))],
    Instr.icmp "%cmp69" (IPred.ult) 64 (Operand.reg "%i.5") (Operand.reg "%n")]

def numFastIfEnd230Instrs : List Instr :=
  [
    Instr.phi "%exp10.4731" (Ty.int 64) [("if.end226", (Operand.reg "%exp10.4")),
                                       ("if.end140", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("if.end62", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
    Instr.phi "%idig.4709716730" (Ty.int 64) [("if.end226", (Operand.reg "%idig.4")),
                                       ("if.end140", (Operand.reg "%idig.4")),
                                       ("if.end62", (Operand.reg "%7"))],
    Instr.phi "%ip.5708717729" (Ty.int 64) [("if.end226", (Operand.reg "%ip.5")),
                                       ("if.end140", (Operand.reg "%ip.5")),
                                       ("if.end62", (Operand.reg "%ip.4"))],
    Instr.phi "%fr.5718728" (Ty.int 64) [("if.end226", (Operand.reg "%fr.5")),
                                       ("if.end140", (Operand.reg "%fr.4")),
                                       ("if.end62", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
    Instr.phi "%fdig.4719727" (Ty.int 64) [("if.end226", (Operand.reg "%fdig.4")),
                                       ("if.end140", (Operand.reg "%17")),
                                       ("if.end62", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
    Instr.binop "%sub231" (BinOp.sub) 64 (Operand.reg "%exp10.4731") (Operand.reg "%fdig.4719727"),
    Instr.binop "%add232" (BinOp.add) 64 (Operand.reg "%fdig.4719727") (Operand.reg "%idig.4709716730"),
    Instr.icmp "%cmp233" (IPred.ult) 64 (Operand.reg "%add232") (Operand.imm (Const.int 64 0x0000000000000014#64)),
    Instr.binop "%28" (BinOp.add) 64 (Operand.reg "%sub231") (Operand.imm (Const.int 64 0x000000000000002d#64)),
    Instr.icmp "%29" (IPred.ult) 64 (Operand.reg "%28") (Operand.imm (Const.int 64 0x000000000000005b#64)),
    Instr.select "%or.cond304" (Ty.int 1) (Operand.reg "%cmp233") (Operand.reg "%29") (Operand.imm (Const.int 1 0x0#1))]

def numFastCleanup300Instrs : List Instr :=
  [
    Instr.phi "%retval.8" (Ty.int 32) [("if.then5", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("if.then89", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("if.else66", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("if.then229", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("cleanup223", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("cleanup282", (Operand.imm (Const.int 32 0x00000001#32))),
                                       ("cleanup282.thread", (Operand.imm (Const.int 32 0x00000001#32))),
                                       ("if.end291", (Operand.imm (Const.int 32 0x00000001#32))),
                                       ("if.then5.i", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("if.then58.i", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("if.then119.i", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("if.then141.i", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("if.else35.i", (Operand.imm (Const.int 32 0x00000000#32)))]]


/-! ### The pins: every block `findBlock` answers

Two hundred and fifty-five `decide`d equations, one per block, generated from the
parse.  The fourteen blocks above are named by their instruction-list `def`; the
rest carry the list inline, so no block's contents reach this module only through
a comment. -/
theorem numFast_findBlock_entry :
    numFastBody.findBlock "entry" = some ⟨"entry", numFastEntryInstrs, Term.condbr (Operand.reg "%cmp.not") "if.end" "land.lhs.true"⟩ := by decide

theorem numFast_findBlock_land_lhs_true :
    numFastBody.findBlock "land.lhs.true" = some ⟨"land.lhs.true", numFastLandLhsTrueInstrs, Term.br "if.end"⟩ := by decide

theorem numFast_findBlock_if_end :
    numFastBody.findBlock "if.end" = some ⟨"if.end", numFastIfEndInstrs, Term.condbr (Operand.reg "%cmp3.not") "if.end6" "if.then5"⟩ := by decide

theorem numFast_findBlock_if_then5 :
    numFastBody.findBlock "if.then5" = some ⟨"if.then5", numFastIfThen5Instrs, Term.br "cleanup300"⟩ := by decide

theorem numFast_findBlock_if_end6 :
    numFastBody.findBlock "if.end6" = some ⟨"if.end6", numFastIfEnd6Instrs, Term.condbr (Operand.reg "%cmp9") "if.then11" "if.else"⟩ := by decide

theorem numFast_findBlock_if_then11 :
    numFastBody.findBlock "if.then11" = some ⟨"if.then11", [
          Instr.binop "%inc12" (BinOp.add) 64 (Operand.reg "%i.0") (Operand.imm (Const.int 64 0x0000000000000001#64))], Term.br "if.end68"⟩ := by decide

theorem numFast_findBlock_if_else :
    numFastBody.findBlock "if.else" = some ⟨"if.else", numFastIfElseInstrs, Term.condbr (Operand.reg "%or.cond") "if.then22" "if.else66"⟩ := by decide

theorem numFast_findBlock_if_then22 :
    numFastBody.findBlock "if.then22" = some ⟨"if.then22", [
          Instr.binop "%3" (BinOp.and) 8 (Operand.reg "%1") (Operand.imm (Const.int 8 0x0f#8)),
          Instr.zext "%conv25" 8 64 (Operand.reg "%3"),
          Instr.binop "%inc26" (BinOp.add) 64 (Operand.reg "%i.0") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.binop "%add563" (BinOp.add) 64 (Operand.reg "%i.0") (Operand.imm (Const.int 64 0x0000000000000009#64)),
          Instr.icmp "%cmp27564.not" (IPred.ugt) 64 (Operand.reg "%add563") (Operand.reg "%n")], Term.condbr (Operand.reg "%cmp27564.not") "while.end" "while.body.preheader"⟩ := by decide

theorem numFast_findBlock_while_body_preheader :
    numFastBody.findBlock "while.body.preheader" = some ⟨"while.body.preheader", [
          Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
                             (Ty.ptr, (Operand.reg "%v8"))],
          Instr.gep "%add.ptr930" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%inc26"),
          Instr.call "%call931" (Ty.int 32) "num_d8_el1" [(Ty.ptr, (Operand.reg "%add.ptr930")),
                             (Ty.ptr, (Operand.reg "%v8"))],
          Instr.icmp "%tobool.not932" (IPred.eq) 32 (Operand.reg "%call931") (Operand.imm (Const.int 32 0x00000000#32))], Term.condbr (Operand.reg "%tobool.not932") "cleanup.thread" "cleanup"⟩ := by decide

theorem numFast_findBlock_while_body :
    numFastBody.findBlock "while.body" = some ⟨"while.body", [
          Instr.binop "%add29" (BinOp.add) 64 (Operand.reg "%add29569933") (Operand.imm (Const.int 64 0x0000000000000008#64)),
          Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
                             (Ty.ptr, (Operand.reg "%v8"))],
          Instr.gep "%add.ptr" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%add568934"),
          Instr.call "%call" (Ty.int 32) "num_d8_el1" [(Ty.ptr, (Operand.reg "%add.ptr")),
                             (Ty.ptr, (Operand.reg "%v8"))],
          Instr.icmp "%tobool.not" (IPred.eq) 32 (Operand.reg "%call") (Operand.imm (Const.int 32 0x00000000#32))], Term.condbr (Operand.reg "%tobool.not") "cleanup.thread" "cleanup"⟩ := by decide

theorem numFast_findBlock_cleanup_thread :
    numFastBody.findBlock "cleanup.thread" = some ⟨"cleanup.thread", [
          Instr.phi "%i.1567.lcssa" (Ty.int 64) [("while.body.preheader", (Operand.reg "%inc26")),
                                       ("while.body", (Operand.reg "%add568934"))],
          Instr.phi "%idig.0566.lcssa" (Ty.int 64) [("while.body.preheader", (Operand.imm (Const.int 64 0x0000000000000001#64))),
                                       ("while.body", (Operand.reg "%add29569933"))],
          Instr.phi "%ip.0565.lcssa" (Ty.int 64) [("while.body.preheader", (Operand.reg "%conv25")),
                                       ("while.body", (Operand.reg "%add35"))],
          Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
                             (Ty.ptr, (Operand.reg "%v8"))]], Term.br "while.end"⟩ := by decide

theorem numFast_findBlock_cleanup :
    numFastBody.findBlock "cleanup" = some ⟨"cleanup", [
          Instr.phi "%ip.0565935" (Ty.int 64) [("while.body", (Operand.reg "%add35")),
                                       ("while.body.preheader", (Operand.reg "%conv25"))],
          Instr.phi "%add568934" (Ty.int 64) [("while.body", (Operand.reg "%add")),
                                       ("while.body.preheader", (Operand.reg "%add563"))],
          Instr.phi "%add29569933" (Ty.int 64) [("while.body", (Operand.reg "%add29")),
                                       ("while.body.preheader", (Operand.imm (Const.int 64 0x0000000000000009#64)))],
          Instr.binop "%mul" (BinOp.mul) 64 (Operand.reg "%ip.0565935") (Operand.imm (Const.int 64 0x0000000005f5e100#64)),
          Instr.load "%4" (Ty.int 32) (Operand.reg "%v8"),
          Instr.zext "%conv34" 32 64 (Operand.reg "%4"),
          Instr.binop "%add35" (BinOp.add) 64 (Operand.reg "%mul") (Operand.reg "%conv34"),
          Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
                             (Ty.ptr, (Operand.reg "%v8"))],
          Instr.binop "%add" (BinOp.add) 64 (Operand.reg "%add568934") (Operand.imm (Const.int 64 0x0000000000000008#64)),
          Instr.icmp "%cmp27" (IPred.ule) 64 (Operand.reg "%add") (Operand.reg "%n"),
          Instr.icmp "%cmp30" (IPred.ult) 64 (Operand.reg "%add29569933") (Operand.imm (Const.int 64 0x000000000000000c#64)),
          Instr.select "%5" (Ty.int 1) (Operand.reg "%cmp27") (Operand.reg "%cmp30") (Operand.imm (Const.int 1 0x0#1))], Term.condbr (Operand.reg "%5") "while.body" "while.end"⟩ := by decide

theorem numFast_findBlock_while_end :
    numFastBody.findBlock "while.end" = some ⟨"while.end", [
          Instr.phi "%ip.0562" (Ty.int 64) [("cleanup.thread", (Operand.reg "%ip.0565.lcssa")),
                                       ("if.then22", (Operand.reg "%conv25")),
                                       ("cleanup", (Operand.reg "%add35"))],
          Instr.phi "%idig.0560" (Ty.int 64) [("cleanup.thread", (Operand.reg "%idig.0566.lcssa")),
                                       ("if.then22", (Operand.imm (Const.int 64 0x0000000000000001#64))),
                                       ("cleanup", (Operand.reg "%add29569933"))],
          Instr.phi "%i.1558" (Ty.int 64) [("cleanup.thread", (Operand.reg "%i.1567.lcssa")),
                                       ("if.then22", (Operand.reg "%inc26")),
                                       ("cleanup", (Operand.reg "%add568934"))],
          Instr.icmp "%cmp39572" (IPred.ult) 64 (Operand.reg "%i.1558") (Operand.reg "%n")], Term.condbr (Operand.reg "%cmp39572") "land.lhs.true41.preheader" "if.end68"⟩ := by decide

theorem numFast_findBlock_land_lhs_true41_preheader :
    numFastBody.findBlock "land.lhs.true41.preheader" = some ⟨"land.lhs.true41.preheader", [
          Instr.binop "%6" (BinOp.add) 64 (Operand.reg "%idig.0560") (Operand.reg "%n"),
          Instr.binop "%7" (BinOp.sub) 64 (Operand.reg "%6") (Operand.reg "%i.1558")], Term.br "land.lhs.true41"⟩ := by decide

theorem numFast_findBlock_land_lhs_true41 :
    numFastBody.findBlock "land.lhs.true41" = some ⟨"land.lhs.true41", numFastLandLhsTrue41Instrs, Term.condbr (Operand.reg "%or.cond440") "while.body52" "if.end68"⟩ := by decide

theorem numFast_findBlock_while_body52 :
    numFastBody.findBlock "while.body52" = some ⟨"while.body52", numFastWhileBody52Instrs, Term.condbr (Operand.reg "%cmp53") "if.then55" "if.end62"⟩ := by decide

theorem numFast_findBlock_if_then55 :
    numFastBody.findBlock "if.then55" = some ⟨"if.then55", numFastIfThen55Instrs, Term.br "if.end62"⟩ := by decide

theorem numFast_findBlock_if_end62 :
    numFastBody.findBlock "if.end62" = some ⟨"if.end62", numFastIfEnd62Instrs, Term.condbr (Operand.reg "%exitcond.not") "if.end230" "land.lhs.true41"⟩ := by decide

theorem numFast_findBlock_if_else66 :
    numFastBody.findBlock "if.else66" = some ⟨"if.else66", numFastIfElse66Instrs, Term.br "cleanup300"⟩ := by decide

theorem numFast_findBlock_if_end68 :
    numFastBody.findBlock "if.end68" = some ⟨"if.end68", numFastIfEnd68Instrs, Term.condbr (Operand.reg "%cmp69") "land.lhs.true71" "if.end144"⟩ := by decide

theorem numFast_findBlock_land_lhs_true71 :
    numFastBody.findBlock "land.lhs.true71" = some ⟨"land.lhs.true71", [
          Instr.gep "%arrayidx72" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.5"),
          Instr.load "%11" (Ty.int 8) (Operand.reg "%arrayidx72"),
          Instr.icmp "%cmp74" (IPred.eq) 8 (Operand.reg "%11") (Operand.imm (Const.int 8 0x2e#8))], Term.condbr (Operand.reg "%cmp74") "if.then76" "if.end144"⟩ := by decide

theorem numFast_findBlock_if_then76 :
    numFastBody.findBlock "if.then76" = some ⟨"if.then76", [
          Instr.binop "%inc77" (BinOp.add) 64 (Operand.reg "%i.5") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.icmp "%cmp78.not" (IPred.ult) 64 (Operand.reg "%inc77") (Operand.reg "%n")], Term.condbr (Operand.reg "%cmp78.not") "lor.lhs.false" "if.then89"⟩ := by decide

theorem numFast_findBlock_lor_lhs_false :
    numFastBody.findBlock "lor.lhs.false" = some ⟨"lor.lhs.false", [
          Instr.gep "%arrayidx80" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%inc77"),
          Instr.load "%12" (Ty.int 8) (Operand.reg "%arrayidx80"),
          Instr.binop "%13" (BinOp.add) 8 (Operand.reg "%12") (Operand.imm (Const.int 8 0xc6#8)),
          Instr.icmp "%or.cond441" (IPred.ult) 8 (Operand.reg "%13") (Operand.imm (Const.int 8 0xf6#8))], Term.condbr (Operand.reg "%or.cond441") "if.then89" "while.cond91.preheader"⟩ := by decide

theorem numFast_findBlock_while_cond91_preheader :
    numFastBody.findBlock "while.cond91.preheader" = some ⟨"while.cond91.preheader", [
          Instr.binop "%add92582" (BinOp.add) 64 (Operand.reg "%i.5") (Operand.imm (Const.int 64 0x0000000000000009#64)),
          Instr.icmp "%cmp93583.not" (IPred.ugt) 64 (Operand.reg "%add92582") (Operand.reg "%n")], Term.condbr (Operand.reg "%cmp93583.not") "while.end115" "while.body100.preheader"⟩ := by decide

theorem numFast_findBlock_while_body100_preheader :
    numFastBody.findBlock "while.body100.preheader" = some ⟨"while.body100.preheader", [
          Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
                             (Ty.ptr, (Operand.reg "%v8101"))],
          Instr.gep "%add.ptr102938" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%inc77"),
          Instr.call "%call103939" (Ty.int 32) "num_d8_el1" [(Ty.ptr, (Operand.reg "%add.ptr102938")),
                             (Ty.ptr, (Operand.reg "%v8101"))],
          Instr.icmp "%tobool104.not940" (IPred.eq) 32 (Operand.reg "%call103939") (Operand.imm (Const.int 32 0x00000000#32))], Term.condbr (Operand.reg "%tobool104.not940") "cleanup112.thread" "cleanup112"⟩ := by decide

theorem numFast_findBlock_if_then89 :
    numFastBody.findBlock "if.then89" = some ⟨"if.then89", [
          Instr.store (Ty.int 64) (Operand.reg "%inc77") (Operand.reg "%err")], Term.br "cleanup300"⟩ := by decide

theorem numFast_findBlock_while_body100 :
    numFastBody.findBlock "while.body100" = some ⟨"while.body100", [
          Instr.binop "%add96" (BinOp.add) 64 (Operand.reg "%add96588941") (Operand.imm (Const.int 64 0x0000000000000008#64)),
          Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
                             (Ty.ptr, (Operand.reg "%v8101"))],
          Instr.gep "%add.ptr102" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%add92587942"),
          Instr.call "%call103" (Ty.int 32) "num_d8_el1" [(Ty.ptr, (Operand.reg "%add.ptr102")),
                             (Ty.ptr, (Operand.reg "%v8101"))],
          Instr.icmp "%tobool104.not" (IPred.eq) 32 (Operand.reg "%call103") (Operand.imm (Const.int 32 0x00000000#32))], Term.condbr (Operand.reg "%tobool104.not") "cleanup112.thread" "cleanup112"⟩ := by decide

theorem numFast_findBlock_cleanup112_thread :
    numFastBody.findBlock "cleanup112.thread" = some ⟨"cleanup112.thread", [
          Instr.phi "%i.6586.lcssa" (Ty.int 64) [("while.body100.preheader", (Operand.reg "%inc77")),
                                       ("while.body100", (Operand.reg "%add92587942"))],
          Instr.phi "%fdig.0585.lcssa" (Ty.int 64) [("while.body100.preheader", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("while.body100", (Operand.reg "%add96588941"))],
          Instr.phi "%fr.0584.lcssa" (Ty.int 64) [("while.body100.preheader", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("while.body100", (Operand.reg "%add109"))],
          Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
                             (Ty.ptr, (Operand.reg "%v8101"))]], Term.br "while.end115"⟩ := by decide

theorem numFast_findBlock_cleanup112 :
    numFastBody.findBlock "cleanup112" = some ⟨"cleanup112", [
          Instr.phi "%fr.0584943" (Ty.int 64) [("while.body100", (Operand.reg "%add109")),
                                       ("while.body100.preheader", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
          Instr.phi "%add92587942" (Ty.int 64) [("while.body100", (Operand.reg "%add92")),
                                       ("while.body100.preheader", (Operand.reg "%add92582"))],
          Instr.phi "%add96588941" (Ty.int 64) [("while.body100", (Operand.reg "%add96")),
                                       ("while.body100.preheader", (Operand.imm (Const.int 64 0x0000000000000008#64)))],
          Instr.binop "%mul107" (BinOp.mul) 64 (Operand.reg "%fr.0584943") (Operand.imm (Const.int 64 0x0000000005f5e100#64)),
          Instr.load "%14" (Ty.int 32) (Operand.reg "%v8101"),
          Instr.zext "%conv108" 32 64 (Operand.reg "%14"),
          Instr.binop "%add109" (BinOp.add) 64 (Operand.reg "%mul107") (Operand.reg "%conv108"),
          Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
                             (Ty.ptr, (Operand.reg "%v8101"))],
          Instr.binop "%add92" (BinOp.add) 64 (Operand.reg "%add92587942") (Operand.imm (Const.int 64 0x0000000000000008#64)),
          Instr.icmp "%cmp93" (IPred.ule) 64 (Operand.reg "%add92") (Operand.reg "%n"),
          Instr.icmp "%cmp97" (IPred.ult) 64 (Operand.reg "%add96588941") (Operand.imm (Const.int 64 0x000000000000000c#64)),
          Instr.select "%15" (Ty.int 1) (Operand.reg "%cmp93") (Operand.reg "%cmp97") (Operand.imm (Const.int 1 0x0#1))], Term.condbr (Operand.reg "%15") "while.body100" "while.end115"⟩ := by decide

theorem numFast_findBlock_while_end115 :
    numFastBody.findBlock "while.end115" = some ⟨"while.end115", [
          Instr.phi "%fr.0556" (Ty.int 64) [("cleanup112.thread", (Operand.reg "%fr.0584.lcssa")),
                                       ("while.cond91.preheader", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("cleanup112", (Operand.reg "%add109"))],
          Instr.phi "%fdig.0554" (Ty.int 64) [("cleanup112.thread", (Operand.reg "%fdig.0585.lcssa")),
                                       ("while.cond91.preheader", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("cleanup112", (Operand.reg "%add96588941"))],
          Instr.phi "%i.6552" (Ty.int 64) [("cleanup112.thread", (Operand.reg "%i.6586.lcssa")),
                                       ("while.cond91.preheader", (Operand.reg "%inc77")),
                                       ("cleanup112", (Operand.reg "%add92587942"))],
          Instr.icmp "%cmp117592" (IPred.ult) 64 (Operand.reg "%i.6552") (Operand.reg "%n")], Term.condbr (Operand.reg "%cmp117592") "land.lhs.true119.preheader" "if.end144"⟩ := by decide

theorem numFast_findBlock_land_lhs_true119_preheader :
    numFastBody.findBlock "land.lhs.true119.preheader" = some ⟨"land.lhs.true119.preheader", [
          Instr.binop "%16" (BinOp.add) 64 (Operand.reg "%fdig.0554") (Operand.reg "%n"),
          Instr.binop "%17" (BinOp.sub) 64 (Operand.reg "%16") (Operand.reg "%i.6552")], Term.br "land.lhs.true119"⟩ := by decide

theorem numFast_findBlock_land_lhs_true119 :
    numFastBody.findBlock "land.lhs.true119" = some ⟨"land.lhs.true119", [
          Instr.phi "%i.9595" (Ty.int 64) [("if.end140", (Operand.reg "%inc142")),
                                       ("land.lhs.true119.preheader", (Operand.reg "%i.6552"))],
          Instr.phi "%fdig.3594" (Ty.int 64) [("if.end140", (Operand.reg "%inc141")),
                                       ("land.lhs.true119.preheader", (Operand.reg "%fdig.0554"))],
          Instr.phi "%fr.3593" (Ty.int 64) [("if.end140", (Operand.reg "%fr.4")),
                                       ("land.lhs.true119.preheader", (Operand.reg "%fr.0556"))],
          Instr.gep "%arrayidx120" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.9595"),
          Instr.load "%18" (Ty.int 8) (Operand.reg "%arrayidx120"),
          Instr.binop "%19" (BinOp.add) 8 (Operand.reg "%18") (Operand.imm (Const.int 8 0xd0#8)),
          Instr.icmp "%or.cond443" (IPred.ult) 8 (Operand.reg "%19") (Operand.imm (Const.int 8 0x0a#8))], Term.condbr (Operand.reg "%or.cond443") "while.body130" "if.end144"⟩ := by decide

theorem numFast_findBlock_while_body130 :
    numFastBody.findBlock "while.body130" = some ⟨"while.body130", [
          Instr.icmp "%cmp131" (IPred.ult) 64 (Operand.reg "%fdig.3594") (Operand.imm (Const.int 64 0x0000000000000013#64))], Term.condbr (Operand.reg "%cmp131") "if.then133" "if.end140"⟩ := by decide

theorem numFast_findBlock_if_then133 :
    numFastBody.findBlock "if.then133" = some ⟨"if.then133", [
          Instr.binop "%mul134" (BinOp.mul) 64 (Operand.reg "%fr.3593") (Operand.imm (Const.int 64 0x000000000000000a#64)),
          Instr.binop "%20" (BinOp.and) 8 (Operand.reg "%18") (Operand.imm (Const.int 8 0x0f#8)),
          Instr.zext "%conv138" 8 64 (Operand.reg "%20"),
          Instr.binop "%add139" (BinOp.add) 64 (Operand.reg "%mul134") (Operand.reg "%conv138")], Term.br "if.end140"⟩ := by decide

theorem numFast_findBlock_if_end140 :
    numFastBody.findBlock "if.end140" = some ⟨"if.end140", [
          Instr.phi "%fr.4" (Ty.int 64) [("if.then133", (Operand.reg "%add139")),
                                       ("while.body130", (Operand.reg "%fr.3593"))],
          Instr.binop "%inc141" (BinOp.add) 64 (Operand.reg "%fdig.3594") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.binop "%inc142" (BinOp.add) 64 (Operand.reg "%i.9595") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.icmp "%exitcond702.not" (IPred.eq) 64 (Operand.reg "%inc142") (Operand.reg "%n")], Term.condbr (Operand.reg "%exitcond702.not") "if.end230" "land.lhs.true119"⟩ := by decide

theorem numFast_findBlock_if_end144 :
    numFastBody.findBlock "if.end144" = some ⟨"if.end144", [
          Instr.phi "%fr.5" (Ty.int 64) [("land.lhs.true71", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("if.end68", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("while.end115", (Operand.reg "%fr.0556")),
                                       ("land.lhs.true119", (Operand.reg "%fr.3593"))],
          Instr.phi "%fdig.4" (Ty.int 64) [("land.lhs.true71", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("if.end68", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("while.end115", (Operand.reg "%fdig.0554")),
                                       ("land.lhs.true119", (Operand.reg "%fdig.3594"))],
          Instr.phi "%i.10" (Ty.int 64) [("land.lhs.true71", (Operand.reg "%i.5")),
                                       ("if.end68", (Operand.reg "%i.5")),
                                       ("while.end115", (Operand.reg "%i.6552")),
                                       ("land.lhs.true119", (Operand.reg "%i.9595"))],
          Instr.icmp "%cmp145" (IPred.ult) 64 (Operand.reg "%i.10") (Operand.reg "%n")], Term.condbr (Operand.reg "%cmp145") "land.lhs.true147" "if.end226"⟩ := by decide

theorem numFast_findBlock_land_lhs_true147 :
    numFastBody.findBlock "land.lhs.true147" = some ⟨"land.lhs.true147", [
          Instr.gep "%arrayidx148" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.10"),
          Instr.load "%21" (Ty.int 8) (Operand.reg "%arrayidx148")], Term.br "NodeBlock"⟩ := by decide

theorem numFast_findBlock_NodeBlock :
    numFastBody.findBlock "NodeBlock" = some ⟨"NodeBlock", [
          Instr.icmp "%Pivot" (IPred.slt) 8 (Operand.reg "%21") (Operand.imm (Const.int 8 0x65#8))], Term.condbr (Operand.reg "%Pivot") "LeafBlock" "LeafBlock1"⟩ := by decide

theorem numFast_findBlock_LeafBlock1 :
    numFastBody.findBlock "LeafBlock1" = some ⟨"LeafBlock1", [
          Instr.icmp "%SwitchLeaf2" (IPred.eq) 8 (Operand.reg "%21") (Operand.imm (Const.int 8 0x65#8))], Term.condbr (Operand.reg "%SwitchLeaf2") "if.then157" "if.end226"⟩ := by decide

theorem numFast_findBlock_LeafBlock :
    numFastBody.findBlock "LeafBlock" = some ⟨"LeafBlock", [
          Instr.icmp "%SwitchLeaf" (IPred.eq) 8 (Operand.reg "%21") (Operand.imm (Const.int 8 0x45#8))], Term.condbr (Operand.reg "%SwitchLeaf") "if.then157" "if.end226"⟩ := by decide

theorem numFast_findBlock_if_then157 :
    numFastBody.findBlock "if.then157" = some ⟨"if.then157", [
          Instr.binop "%inc158" (BinOp.add) 64 (Operand.reg "%i.10") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.icmp "%cmp159" (IPred.ult) 64 (Operand.reg "%inc158") (Operand.reg "%n")], Term.condbr (Operand.reg "%cmp159") "land.lhs.true161" "if.end177"⟩ := by decide

theorem numFast_findBlock_land_lhs_true161 :
    numFastBody.findBlock "land.lhs.true161" = some ⟨"land.lhs.true161", [
          Instr.gep "%arrayidx162" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%inc158"),
          Instr.load "%22" (Ty.int 8) (Operand.reg "%arrayidx162")], Term.br "NodeBlock7"⟩ := by decide

theorem numFast_findBlock_NodeBlock7 :
    numFastBody.findBlock "NodeBlock7" = some ⟨"NodeBlock7", [
          Instr.icmp "%Pivot8" (IPred.slt) 8 (Operand.reg "%22") (Operand.imm (Const.int 8 0x2d#8))], Term.condbr (Operand.reg "%Pivot8") "LeafBlock3" "LeafBlock5"⟩ := by decide

theorem numFast_findBlock_LeafBlock5 :
    numFastBody.findBlock "LeafBlock5" = some ⟨"LeafBlock5", [
          Instr.icmp "%SwitchLeaf6" (IPred.eq) 8 (Operand.reg "%22") (Operand.imm (Const.int 8 0x2d#8))], Term.condbr (Operand.reg "%SwitchLeaf6") "if.then171" "if.end177"⟩ := by decide

theorem numFast_findBlock_LeafBlock3 :
    numFastBody.findBlock "LeafBlock3" = some ⟨"LeafBlock3", [
          Instr.icmp "%SwitchLeaf4" (IPred.eq) 8 (Operand.reg "%22") (Operand.imm (Const.int 8 0x2b#8))], Term.condbr (Operand.reg "%SwitchLeaf4") "if.then171" "if.end177"⟩ := by decide

theorem numFast_findBlock_if_then171 :
    numFastBody.findBlock "if.then171" = some ⟨"if.then171", [
          Instr.icmp "%cmp174" (IPred.ne) 8 (Operand.reg "%22") (Operand.imm (Const.int 8 0x2d#8)),
          Instr.binop "%inc176" (BinOp.add) 64 (Operand.reg "%i.10") (Operand.imm (Const.int 64 0x0000000000000002#64))], Term.br "if.end177"⟩ := by decide

theorem numFast_findBlock_if_end177 :
    numFastBody.findBlock "if.end177" = some ⟨"if.end177", [
          Instr.phi "%esign.0" (Ty.int 1) [("if.then171", (Operand.reg "%cmp174")),
                                       ("if.then157", (Operand.imm (Const.int 1 0x1#1))),
                                       ("LeafBlock3", (Operand.imm (Const.int 1 0x1#1))),
                                       ("LeafBlock5", (Operand.imm (Const.int 1 0x1#1)))],
          Instr.phi "%i.11" (Ty.int 64) [("if.then171", (Operand.reg "%inc176")),
                                       ("if.then157", (Operand.reg "%inc158")),
                                       ("LeafBlock3", (Operand.reg "%inc158")),
                                       ("LeafBlock5", (Operand.reg "%inc158"))],
          Instr.icmp "%cmp178.not" (IPred.ult) 64 (Operand.reg "%i.11") (Operand.reg "%n")], Term.condbr (Operand.reg "%cmp178.not") "lor.lhs.false180" "cleanup223"⟩ := by decide

theorem numFast_findBlock_lor_lhs_false180 :
    numFastBody.findBlock "lor.lhs.false180" = some ⟨"lor.lhs.false180", [
          Instr.gep "%arrayidx181" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.11"),
          Instr.load "%23" (Ty.int 8) (Operand.reg "%arrayidx181"),
          Instr.binop "%24" (BinOp.add) 8 (Operand.reg "%23") (Operand.imm (Const.int 8 0xc6#8)),
          Instr.icmp "%or.cond444" (IPred.ult) 8 (Operand.reg "%24") (Operand.imm (Const.int 8 0xf6#8))], Term.condbr (Operand.reg "%or.cond444") "cleanup223" "land.lhs.true195"⟩ := by decide

theorem numFast_findBlock_land_lhs_true195 :
    numFastBody.findBlock "land.lhs.true195" = some ⟨"land.lhs.true195", [
          Instr.phi "%i.12604" (Ty.int 64) [("if.end216", (Operand.reg "%inc217")),
                                       ("lor.lhs.false180", (Operand.reg "%i.11"))],
          Instr.phi "%exp10.0603" (Ty.int 64) [("if.end216", (Operand.reg "%exp10.1")),
                                       ("lor.lhs.false180", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
          Instr.gep "%arrayidx196" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.12604"),
          Instr.load "%25" (Ty.int 8) (Operand.reg "%arrayidx196"),
          Instr.binop "%26" (BinOp.add) 8 (Operand.reg "%25") (Operand.imm (Const.int 8 0xd0#8)),
          Instr.icmp "%or.cond445" (IPred.ult) 8 (Operand.reg "%26") (Operand.imm (Const.int 8 0x0a#8))], Term.condbr (Operand.reg "%or.cond445") "while.body206" "cleanup223.thread"⟩ := by decide

theorem numFast_findBlock_while_body206 :
    numFastBody.findBlock "while.body206" = some ⟨"while.body206", [
          Instr.icmp "%cmp207" (IPred.slt) 64 (Operand.reg "%exp10.0603") (Operand.imm (Const.int 64 0x00000000000186a0#64))], Term.condbr (Operand.reg "%cmp207") "if.then209" "if.end216"⟩ := by decide

theorem numFast_findBlock_if_then209 :
    numFastBody.findBlock "if.then209" = some ⟨"if.then209", [
          Instr.binop "%mul210" (BinOp.mul) 64 (Operand.reg "%exp10.0603") (Operand.imm (Const.int 64 0x000000000000000a#64)),
          Instr.binop "%27" (BinOp.and) 8 (Operand.reg "%25") (Operand.imm (Const.int 8 0x0f#8)),
          Instr.zext "%conv214" 8 64 (Operand.reg "%27"),
          Instr.binop "%add215" (BinOp.add) 64 (Operand.reg "%mul210") (Operand.reg "%conv214")], Term.br "if.end216"⟩ := by decide

theorem numFast_findBlock_if_end216 :
    numFastBody.findBlock "if.end216" = some ⟨"if.end216", [
          Instr.phi "%exp10.1" (Ty.int 64) [("if.then209", (Operand.reg "%add215")),
                                       ("while.body206", (Operand.reg "%exp10.0603"))],
          Instr.binop "%inc217" (BinOp.add) 64 (Operand.reg "%i.12604") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.icmp "%exitcond703.not" (IPred.eq) 64 (Operand.reg "%inc217") (Operand.reg "%n")], Term.condbr (Operand.reg "%exitcond703.not") "cleanup223.thread" "land.lhs.true195"⟩ := by decide

theorem numFast_findBlock_cleanup223_thread :
    numFastBody.findBlock "cleanup223.thread" = some ⟨"cleanup223.thread", [
          Instr.phi "%exp10.0.lcssa.ph" (Ty.int 64) [("land.lhs.true195", (Operand.reg "%exp10.0603")),
                                       ("if.end216", (Operand.reg "%exp10.1"))],
          Instr.phi "%i.12.lcssa.ph" (Ty.int 64) [("land.lhs.true195", (Operand.reg "%i.12604")),
                                       ("if.end216", (Operand.reg "%n"))],
          Instr.binop "%sub221" (BinOp.sub) 64 (Operand.imm (Const.int 64 0x0000000000000000#64)) (Operand.reg "%exp10.0.lcssa.ph"),
          Instr.select "%spec.select446" (Ty.int 64) (Operand.reg "%esign.0") (Operand.reg "%exp10.0.lcssa.ph") (Operand.reg "%sub221")], Term.br "if.end226"⟩ := by decide

theorem numFast_findBlock_cleanup223 :
    numFastBody.findBlock "cleanup223" = some ⟨"cleanup223", [
          Instr.store (Ty.int 64) (Operand.reg "%i.11") (Operand.reg "%err")], Term.br "cleanup300"⟩ := by decide

theorem numFast_findBlock_if_end226 :
    numFastBody.findBlock "if.end226" = some ⟨"if.end226", [
          Instr.phi "%exp10.4" (Ty.int 64) [("if.end144", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("cleanup223.thread", (Operand.reg "%spec.select446")),
                                       ("LeafBlock", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("LeafBlock1", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
          Instr.phi "%i.14" (Ty.int 64) [("if.end144", (Operand.reg "%i.10")),
                                       ("cleanup223.thread", (Operand.reg "%i.12.lcssa.ph")),
                                       ("LeafBlock", (Operand.reg "%i.10")),
                                       ("LeafBlock1", (Operand.reg "%i.10"))],
          Instr.icmp "%cmp227.not" (IPred.eq) 64 (Operand.reg "%i.14") (Operand.reg "%n")], Term.condbr (Operand.reg "%cmp227.not") "if.end230" "if.then229"⟩ := by decide

theorem numFast_findBlock_if_then229 :
    numFastBody.findBlock "if.then229" = some ⟨"if.then229", [
          Instr.store (Ty.int 64) (Operand.reg "%i.14") (Operand.reg "%err")], Term.br "cleanup300"⟩ := by decide

theorem numFast_findBlock_if_end230 :
    numFastBody.findBlock "if.end230" = some ⟨"if.end230", numFastIfEnd230Instrs, Term.condbr (Operand.reg "%or.cond304") "if.then241" "if.end285"⟩ := by decide

theorem numFast_findBlock_if_then241 :
    numFastBody.findBlock "if.then241" = some ⟨"if.then241", [
          Instr.gep "%arrayidx242" (Ty.int 64) (Operand.global "@NUMF_EL1_P10") (Operand.reg "%fdig.4719727"),
          Instr.load "%30" (Ty.int 64) (Operand.reg "%arrayidx242"),
          Instr.binop "%mul243" (BinOp.mul) 64 (Operand.reg "%30") (Operand.reg "%ip.5708717729"),
          Instr.binop "%add244" (BinOp.add) 64 (Operand.reg "%mul243") (Operand.reg "%fr.5718728"),
          Instr.icmp "%cmp245" (IPred.ult) 64 (Operand.reg "%add232") (Operand.imm (Const.int 64 0x0000000000000010#64)),
          Instr.binop "%31" (BinOp.add) 64 (Operand.reg "%sub231") (Operand.imm (Const.int 64 0x0000000000000016#64)),
          Instr.icmp "%32" (IPred.ult) 64 (Operand.reg "%31") (Operand.imm (Const.int 64 0x000000000000002d#64)),
          Instr.select "%or.cond306" (Ty.int 1) (Operand.reg "%cmp245") (Operand.reg "%32") (Operand.imm (Const.int 1 0x0#1))], Term.condbr (Operand.reg "%or.cond306") "if.then253" "if.end268"⟩ := by decide

theorem numFast_findBlock_if_then253 :
    numFastBody.findBlock "if.then253" = some ⟨"if.then253", [
          Instr.icmp "%cmp254" (IPred.sgt) 64 (Operand.reg "%sub231") (Operand.imm (Const.int 64 0xffffffffffffffff#64)),
          Instr.uitofp "%conv256" 64 (Operand.reg "%add244")], Term.condbr (Operand.reg "%cmp254") "cond.true" "cond.false"⟩ := by decide

theorem numFast_findBlock_cond_true :
    numFastBody.findBlock "cond.true" = some ⟨"cond.true", [
          Instr.gep "%arrayidx257" Ty.double (Operand.global "@NUMF_EL1_POW10") (Operand.reg "%sub231"),
          Instr.load "%33" Ty.double (Operand.reg "%arrayidx257"),
          Instr.fmul "%mul258" (Operand.reg "%33") (Operand.reg "%conv256")], Term.br "cleanup282.thread"⟩ := by decide

theorem numFast_findBlock_cond_false :
    numFastBody.findBlock "cond.false" = some ⟨"cond.false", [
          Instr.binop "%sub260" (BinOp.sub) 64 (Operand.imm (Const.int 64 0x0000000000000000#64)) (Operand.reg "%sub231"),
          Instr.gep "%arrayidx261" Ty.double (Operand.global "@NUMF_EL1_POW10") (Operand.reg "%sub260"),
          Instr.load "%34" Ty.double (Operand.reg "%arrayidx261"),
          Instr.fdiv "%div" (Operand.reg "%conv256") (Operand.reg "%34")], Term.br "cleanup282.thread"⟩ := by decide

theorem numFast_findBlock_cleanup282_thread :
    numFastBody.findBlock "cleanup282.thread" = some ⟨"cleanup282.thread", [
          Instr.phi "%cond" Ty.double [("cond.true", (Operand.reg "%mul258")),
                                       ("cond.false", (Operand.reg "%div"))],
          Instr.fneg "%fneg" (Operand.reg "%cond"),
          Instr.select "%cond266" Ty.double (Operand.reg "%tobool274.not") (Operand.reg "%cond") (Operand.reg "%fneg"),
          Instr.store Ty.double (Operand.reg "%cond266") (Operand.reg "%out")], Term.br "cleanup300"⟩ := by decide

theorem numFast_findBlock_if_end268 :
    numFastBody.findBlock "if.end268" = some ⟨"if.end268", [
          Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000008#64))),
                             (Ty.ptr, (Operand.reg "%d269"))],
          Instr.call "%call270" (Ty.int 32) "num_el_el1" [((Ty.int 64), (Operand.reg "%add244")),
                             ((Ty.int 64), (Operand.reg "%sub231")),
                             (Ty.ptr, (Operand.reg "%d269"))],
          Instr.icmp "%tobool271.not" (IPred.eq) 32 (Operand.reg "%call270") (Operand.imm (Const.int 32 0x00000000#32))], Term.condbr (Operand.reg "%tobool271.not") "cleanup282.thread462" "cleanup282"⟩ := by decide

theorem numFast_findBlock_cleanup282_thread462 :
    numFastBody.findBlock "cleanup282.thread462" = some ⟨"cleanup282.thread462", [
          Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000008#64))),
                             (Ty.ptr, (Operand.reg "%d269"))]], Term.br "if.end285"⟩ := by decide

theorem numFast_findBlock_cleanup282 :
    numFastBody.findBlock "cleanup282" = some ⟨"cleanup282", [
          Instr.load "%35" (Ty.int 64) (Operand.global "@g_nume1_el"),
          Instr.binop "%inc273" (BinOp.add) 64 (Operand.reg "%35") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.store (Ty.int 64) (Operand.reg "%inc273") (Operand.global "@g_nume1_el"),
          Instr.load "%36" Ty.double (Operand.reg "%d269"),
          Instr.fneg "%fneg276" (Operand.reg "%36"),
          Instr.select "%cond279" Ty.double (Operand.reg "%tobool274.not") (Operand.reg "%36") (Operand.reg "%fneg276"),
          Instr.store Ty.double (Operand.reg "%cond279") (Operand.reg "%out"),
          Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000008#64))),
                             (Ty.ptr, (Operand.reg "%d269"))]], Term.br "cleanup300"⟩ := by decide

theorem numFast_findBlock_if_end285 :
    numFastBody.findBlock "if.end285" = some ⟨"if.end285", [
          Instr.load "%37" (Ty.int 64) (Operand.global "@g_nume1_slow"),
          Instr.binop "%inc287" (BinOp.add) 64 (Operand.reg "%37") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.store (Ty.int 64) (Operand.reg "%inc287") (Operand.global "@g_nume1_slow"),
          Instr.load "%38" (Ty.int 8) (Operand.reg "%p"),
          Instr.icmp "%cmp1.i" (IPred.eq) 8 (Operand.reg "%38") (Operand.imm (Const.int 8 0x2d#8)),
          Instr.zext "%i.0.i" 1 64 (Operand.reg "%cmp1.i"),
          Instr.icmp "%cmp3.not.i" (IPred.ugt) 64 (Operand.reg "%n") (Operand.reg "%i.0.i")], Term.condbr (Operand.reg "%cmp3.not.i") "if.end6.i" "if.then5.i"⟩ := by decide

theorem numFast_findBlock_if_then5_i :
    numFastBody.findBlock "if.then5.i" = some ⟨"if.then5.i", [
          Instr.store (Ty.int 64) (Operand.imm (Const.int 64 0x0000000000000001#64)) (Operand.reg "%err")], Term.br "cleanup300"⟩ := by decide

theorem numFast_findBlock_if_end6_i :
    numFastBody.findBlock "if.end6.i" = some ⟨"if.end6.i", [
          Instr.gep "%arrayidx7.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.0.i"),
          Instr.load "%39" (Ty.int 8) (Operand.reg "%arrayidx7.i"),
          Instr.icmp "%cmp9.i" (IPred.eq) 8 (Operand.reg "%39") (Operand.imm (Const.int 8 0x30#8))], Term.condbr (Operand.reg "%cmp9.i") "if.then11.i" "if.else.i"⟩ := by decide

theorem numFast_findBlock_if_then11_i :
    numFastBody.findBlock "if.then11.i" = some ⟨"if.then11.i", [
          Instr.select "%inc12.i" (Ty.int 64) (Operand.reg "%cmp1.i") (Operand.imm (Const.int 64 0x0000000000000002#64)) (Operand.imm (Const.int 64 0x0000000000000001#64))], Term.br "if.end37.i"⟩ := by decide

theorem numFast_findBlock_if_else_i :
    numFastBody.findBlock "if.else.i" = some ⟨"if.else.i", [
          Instr.binop "%40" (BinOp.add) 8 (Operand.reg "%39") (Operand.imm (Const.int 8 0xcf#8)),
          Instr.icmp "%or.cond.i" (IPred.ult) 8 (Operand.reg "%40") (Operand.imm (Const.int 8 0x09#8))], Term.condbr (Operand.reg "%or.cond.i") "land.lhs.true25.i" "if.else35.i"⟩ := by decide

theorem numFast_findBlock_land_lhs_true25_i :
    numFastBody.findBlock "land.lhs.true25.i" = some ⟨"land.lhs.true25.i", [
          Instr.phi "%i.1262.i" (Ty.int 64) [("while.body.i", (Operand.reg "%inc34.i")),
                                       ("if.else.i", (Operand.reg "%i.0.i"))],
          Instr.gep "%arrayidx26.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.1262.i"),
          Instr.load "%41" (Ty.int 8) (Operand.reg "%arrayidx26.i"),
          Instr.binop "%42" (BinOp.add) 8 (Operand.reg "%41") (Operand.imm (Const.int 8 0xd0#8)),
          Instr.icmp "%or.cond222.i" (IPred.ult) 8 (Operand.reg "%42") (Operand.imm (Const.int 8 0x0a#8))], Term.condbr (Operand.reg "%or.cond222.i") "while.body.i" "if.end37.i"⟩ := by decide

theorem numFast_findBlock_while_body_i :
    numFastBody.findBlock "while.body.i" = some ⟨"while.body.i", [
          Instr.binop "%inc34.i" (BinOp.add) 64 (Operand.reg "%i.1262.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.icmp "%exitcond.not.i" (IPred.eq) 64 (Operand.reg "%inc34.i") (Operand.reg "%n")], Term.condbr (Operand.reg "%exitcond.not.i") "if.then143.i" "land.lhs.true25.i"⟩ := by decide

theorem numFast_findBlock_if_else35_i :
    numFastBody.findBlock "if.else35.i" = some ⟨"if.else35.i", [
          Instr.store (Ty.int 64) (Operand.reg "%i.0.i") (Operand.reg "%err")], Term.br "cleanup300"⟩ := by decide

theorem numFast_findBlock_if_end37_i :
    numFastBody.findBlock "if.end37.i" = some ⟨"if.end37.i", [
          Instr.phi "%i.2.i" (Ty.int 64) [("if.then11.i", (Operand.reg "%inc12.i")),
                                       ("land.lhs.true25.i", (Operand.reg "%i.1262.i"))],
          Instr.icmp "%cmp38.i" (IPred.ult) 64 (Operand.reg "%i.2.i") (Operand.reg "%n")], Term.condbr (Operand.reg "%cmp38.i") "land.lhs.true40.i" "if.end77.i"⟩ := by decide

theorem numFast_findBlock_land_lhs_true40_i :
    numFastBody.findBlock "land.lhs.true40.i" = some ⟨"land.lhs.true40.i", [
          Instr.gep "%arrayidx41.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.2.i"),
          Instr.load "%43" (Ty.int 8) (Operand.reg "%arrayidx41.i"),
          Instr.icmp "%cmp43.i" (IPred.eq) 8 (Operand.reg "%43") (Operand.imm (Const.int 8 0x2e#8))], Term.condbr (Operand.reg "%cmp43.i") "if.then45.i" "if.end77.i"⟩ := by decide

theorem numFast_findBlock_if_then45_i :
    numFastBody.findBlock "if.then45.i" = some ⟨"if.then45.i", [
          Instr.binop "%inc46.i" (BinOp.add) 64 (Operand.reg "%i.2.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.icmp "%cmp47.not.i" (IPred.ult) 64 (Operand.reg "%inc46.i") (Operand.reg "%n")], Term.condbr (Operand.reg "%cmp47.not.i") "lor.lhs.false.i" "if.then58.i"⟩ := by decide

theorem numFast_findBlock_lor_lhs_false_i :
    numFastBody.findBlock "lor.lhs.false.i" = some ⟨"lor.lhs.false.i", [
          Instr.gep "%arrayidx49.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%inc46.i"),
          Instr.load "%44" (Ty.int 8) (Operand.reg "%arrayidx49.i"),
          Instr.binop "%45" (BinOp.add) 8 (Operand.reg "%44") (Operand.imm (Const.int 8 0xc6#8)),
          Instr.icmp "%or.cond223.i" (IPred.ult) 8 (Operand.reg "%45") (Operand.imm (Const.int 8 0xf6#8))], Term.condbr (Operand.reg "%or.cond223.i") "if.then58.i" "land.lhs.true63.i"⟩ := by decide

theorem numFast_findBlock_if_then58_i :
    numFastBody.findBlock "if.then58.i" = some ⟨"if.then58.i", [
          Instr.store (Ty.int 64) (Operand.reg "%inc46.i") (Operand.reg "%err")], Term.br "cleanup300"⟩ := by decide

theorem numFast_findBlock_land_lhs_true63_i :
    numFastBody.findBlock "land.lhs.true63.i" = some ⟨"land.lhs.true63.i", [
          Instr.phi "%i.3265.i" (Ty.int 64) [("while.body74.i", (Operand.reg "%inc75.i")),
                                       ("lor.lhs.false.i", (Operand.reg "%inc46.i"))],
          Instr.gep "%arrayidx64.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.3265.i"),
          Instr.load "%46" (Ty.int 8) (Operand.reg "%arrayidx64.i"),
          Instr.binop "%47" (BinOp.add) 8 (Operand.reg "%46") (Operand.imm (Const.int 8 0xd0#8)),
          Instr.icmp "%or.cond224.i" (IPred.ult) 8 (Operand.reg "%47") (Operand.imm (Const.int 8 0x0a#8))], Term.condbr (Operand.reg "%or.cond224.i") "while.body74.i" "if.end77.i"⟩ := by decide

theorem numFast_findBlock_while_body74_i :
    numFastBody.findBlock "while.body74.i" = some ⟨"while.body74.i", [
          Instr.binop "%inc75.i" (BinOp.add) 64 (Operand.reg "%i.3265.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.icmp "%exitcond306.not.i" (IPred.eq) 64 (Operand.reg "%inc75.i") (Operand.reg "%n")], Term.condbr (Operand.reg "%exitcond306.not.i") "if.then143.i" "land.lhs.true63.i"⟩ := by decide

theorem numFast_findBlock_if_end77_i :
    numFastBody.findBlock "if.end77.i" = some ⟨"if.end77.i", [
          Instr.phi "%i.4.i" (Ty.int 64) [("land.lhs.true40.i", (Operand.reg "%i.2.i")),
                                       ("if.end37.i", (Operand.reg "%i.2.i")),
                                       ("land.lhs.true63.i", (Operand.reg "%i.3265.i"))],
          Instr.icmp "%cmp78.i" (IPred.ult) 64 (Operand.reg "%i.4.i") (Operand.reg "%n")], Term.condbr (Operand.reg "%cmp78.i") "land.lhs.true80.i" "if.end138.i"⟩ := by decide

theorem numFast_findBlock_land_lhs_true80_i :
    numFastBody.findBlock "land.lhs.true80.i" = some ⟨"land.lhs.true80.i", [
          Instr.gep "%arrayidx81.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.4.i"),
          Instr.load "%48" (Ty.int 8) (Operand.reg "%arrayidx81.i")], Term.br "NodeBlock13"⟩ := by decide

theorem numFast_findBlock_NodeBlock13 :
    numFastBody.findBlock "NodeBlock13" = some ⟨"NodeBlock13", [
          Instr.icmp "%Pivot14" (IPred.slt) 8 (Operand.reg "%48") (Operand.imm (Const.int 8 0x65#8))], Term.condbr (Operand.reg "%Pivot14") "LeafBlock9" "LeafBlock11"⟩ := by decide

theorem numFast_findBlock_LeafBlock11 :
    numFastBody.findBlock "LeafBlock11" = some ⟨"LeafBlock11", [
          Instr.icmp "%SwitchLeaf12" (IPred.eq) 8 (Operand.reg "%48") (Operand.imm (Const.int 8 0x65#8))], Term.condbr (Operand.reg "%SwitchLeaf12") "if.then90.i" "if.end138.i"⟩ := by decide

theorem numFast_findBlock_LeafBlock9 :
    numFastBody.findBlock "LeafBlock9" = some ⟨"LeafBlock9", [
          Instr.icmp "%SwitchLeaf10" (IPred.eq) 8 (Operand.reg "%48") (Operand.imm (Const.int 8 0x45#8))], Term.condbr (Operand.reg "%SwitchLeaf10") "if.then90.i" "if.end138.i"⟩ := by decide

theorem numFast_findBlock_if_then90_i :
    numFastBody.findBlock "if.then90.i" = some ⟨"if.then90.i", [
          Instr.binop "%inc91.i" (BinOp.add) 64 (Operand.reg "%i.4.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.icmp "%cmp92.i" (IPred.ult) 64 (Operand.reg "%inc91.i") (Operand.reg "%n")], Term.condbr (Operand.reg "%cmp92.i") "land.lhs.true94.i" "if.end106.i"⟩ := by decide

theorem numFast_findBlock_land_lhs_true94_i :
    numFastBody.findBlock "land.lhs.true94.i" = some ⟨"land.lhs.true94.i", [
          Instr.gep "%arrayidx95.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%inc91.i"),
          Instr.load "%49" (Ty.int 8) (Operand.reg "%arrayidx95.i")], Term.br "NodeBlock19"⟩ := by decide

theorem numFast_findBlock_NodeBlock19 :
    numFastBody.findBlock "NodeBlock19" = some ⟨"NodeBlock19", [
          Instr.icmp "%Pivot20" (IPred.slt) 8 (Operand.reg "%49") (Operand.imm (Const.int 8 0x2d#8))], Term.condbr (Operand.reg "%Pivot20") "LeafBlock15" "LeafBlock17"⟩ := by decide

theorem numFast_findBlock_LeafBlock17 :
    numFastBody.findBlock "LeafBlock17" = some ⟨"LeafBlock17", [
          Instr.icmp "%SwitchLeaf18" (IPred.eq) 8 (Operand.reg "%49") (Operand.imm (Const.int 8 0x2d#8))], Term.condbr (Operand.reg "%SwitchLeaf18") "if.then104.i" "if.end106.i"⟩ := by decide

theorem numFast_findBlock_LeafBlock15 :
    numFastBody.findBlock "LeafBlock15" = some ⟨"LeafBlock15", [
          Instr.icmp "%SwitchLeaf16" (IPred.eq) 8 (Operand.reg "%49") (Operand.imm (Const.int 8 0x2b#8))], Term.condbr (Operand.reg "%SwitchLeaf16") "if.then104.i" "if.end106.i"⟩ := by decide

theorem numFast_findBlock_if_then104_i :
    numFastBody.findBlock "if.then104.i" = some ⟨"if.then104.i", [
          Instr.binop "%inc105.i" (BinOp.add) 64 (Operand.reg "%i.4.i") (Operand.imm (Const.int 64 0x0000000000000002#64))], Term.br "if.end106.i"⟩ := by decide

theorem numFast_findBlock_if_end106_i :
    numFastBody.findBlock "if.end106.i" = some ⟨"if.end106.i", [
          Instr.phi "%i.5.i" (Ty.int 64) [("if.then104.i", (Operand.reg "%inc105.i")),
                                       ("if.then90.i", (Operand.reg "%inc91.i")),
                                       ("LeafBlock15", (Operand.reg "%inc91.i")),
                                       ("LeafBlock17", (Operand.reg "%inc91.i"))],
          Instr.icmp "%cmp107.not.i" (IPred.ult) 64 (Operand.reg "%i.5.i") (Operand.reg "%n")], Term.condbr (Operand.reg "%cmp107.not.i") "lor.lhs.false109.i" "if.then119.i"⟩ := by decide

theorem numFast_findBlock_lor_lhs_false109_i :
    numFastBody.findBlock "lor.lhs.false109.i" = some ⟨"lor.lhs.false109.i", [
          Instr.gep "%arrayidx110.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.5.i"),
          Instr.load "%50" (Ty.int 8) (Operand.reg "%arrayidx110.i"),
          Instr.binop "%51" (BinOp.add) 8 (Operand.reg "%50") (Operand.imm (Const.int 8 0xc6#8)),
          Instr.icmp "%or.cond225.i" (IPred.ult) 8 (Operand.reg "%51") (Operand.imm (Const.int 8 0xf6#8))], Term.condbr (Operand.reg "%or.cond225.i") "if.then119.i" "land.lhs.true124.i"⟩ := by decide

theorem numFast_findBlock_if_then119_i :
    numFastBody.findBlock "if.then119.i" = some ⟨"if.then119.i", [
          Instr.store (Ty.int 64) (Operand.reg "%i.5.i") (Operand.reg "%err")], Term.br "cleanup300"⟩ := by decide

theorem numFast_findBlock_land_lhs_true124_i :
    numFastBody.findBlock "land.lhs.true124.i" = some ⟨"land.lhs.true124.i", [
          Instr.phi "%i.6269.i" (Ty.int 64) [("while.body135.i", (Operand.reg "%inc136.i")),
                                       ("lor.lhs.false109.i", (Operand.reg "%i.5.i"))],
          Instr.gep "%arrayidx125.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.6269.i"),
          Instr.load "%52" (Ty.int 8) (Operand.reg "%arrayidx125.i"),
          Instr.binop "%53" (BinOp.add) 8 (Operand.reg "%52") (Operand.imm (Const.int 8 0xd0#8)),
          Instr.icmp "%or.cond226.i" (IPred.ult) 8 (Operand.reg "%53") (Operand.imm (Const.int 8 0x0a#8))], Term.condbr (Operand.reg "%or.cond226.i") "while.body135.i" "if.end138.i"⟩ := by decide

theorem numFast_findBlock_while_body135_i :
    numFastBody.findBlock "while.body135.i" = some ⟨"while.body135.i", [
          Instr.binop "%inc136.i" (BinOp.add) 64 (Operand.reg "%i.6269.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.icmp "%exitcond307.not.i" (IPred.eq) 64 (Operand.reg "%inc136.i") (Operand.reg "%n")], Term.condbr (Operand.reg "%exitcond307.not.i") "if.then143.i" "land.lhs.true124.i"⟩ := by decide

theorem numFast_findBlock_if_end138_i :
    numFastBody.findBlock "if.end138.i" = some ⟨"if.end138.i", [
          Instr.phi "%i.7.i" (Ty.int 64) [("if.end77.i", (Operand.reg "%i.4.i")),
                                       ("land.lhs.true124.i", (Operand.reg "%i.6269.i")),
                                       ("LeafBlock9", (Operand.reg "%i.4.i")),
                                       ("LeafBlock11", (Operand.reg "%i.4.i"))],
          Instr.icmp "%cmp139.not.i" (IPred.eq) 64 (Operand.reg "%i.7.i") (Operand.reg "%n")], Term.condbr (Operand.reg "%cmp139.not.i") "if.then143.i" "if.then141.i"⟩ := by decide

theorem numFast_findBlock_if_then141_i :
    numFastBody.findBlock "if.then141.i" = some ⟨"if.then141.i", [
          Instr.store (Ty.int 64) (Operand.reg "%i.7.i") (Operand.reg "%err")], Term.br "cleanup300"⟩ := by decide

theorem numFast_findBlock_if_then143_i :
    numFastBody.findBlock "if.then143.i" = some ⟨"if.then143.i", [
          Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000300#64))),
                             (Ty.ptr, (Operand.reg "%dig.i.i"))]], Term.br "for.body.outer.i.outer.i"⟩ := by decide

theorem numFast_findBlock_for_body_outer_i_outer_i :
    numFastBody.findBlock "for.body.outer.i.outer.i" = some ⟨"for.body.outer.i.outer.i", [
          Instr.phi "%i.1725.ph.i.ph.i" (Ty.int 64) [("if.then143.i", (Operand.reg "%i.0.i")),
                                       ("for.inc.i.i", (Operand.reg "%inc57.i.i"))],
          Instr.phi "%R.0724.ph.i.ph.i" (Ty.int 64) [("if.then143.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.inc.i.i", (Operand.reg "%R.4.ph.i.i"))],
          Instr.phi "%T.0723.ph.i.ph.i" (Ty.int 64) [("if.then143.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.inc.i.i", (Operand.reg "%T.2.ph.i.i"))],
          Instr.phi "%F.0722.ph.i.ph.i" (Ty.int 64) [("if.then143.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.inc.i.i", (Operand.reg "%F.3.ph.i.i"))],
          Instr.phi "%lead.0721.ph.i.ph.i" (Ty.int 64) [("if.then143.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.inc.i.i", (Operand.reg "%lead.0721.i287.i"))],
          Instr.phi "%top.0720.ph.i.ph.i" (Ty.int 64) [("if.then143.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.inc.i.i", (Operand.reg "%top.4.ph.i.i"))],
          Instr.phi "%topn.0719.ph.i.ph.i" (Ty.int 64) [("if.then143.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.inc.i.i", (Operand.reg "%topn.4.ph.i.i"))],
          Instr.phi "%in_frac.0718.ph.i.ph.i" (Ty.int 32) [("if.then143.i", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("for.inc.i.i", (Operand.reg "%in_frac.2.ph.i.i"))],
          Instr.phi "%seen.0717.ph.i.ph.i" (Ty.int 32) [("if.then143.i", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("for.inc.i.i", (Operand.reg "%seen.4.ph.i.i"))],
          Instr.phi "%sticky.0716.ph.i.ph.i" (Ty.int 32) [("if.then143.i", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("for.inc.i.i", (Operand.reg "%sticky.4.ph.i.i"))]], Term.br "for.body.outer.i.i"⟩ := by decide

theorem numFast_findBlock_for_body_outer_i_i :
    numFastBody.findBlock "for.body.outer.i.i" = some ⟨"for.body.outer.i.i", [
          Instr.phi "%i.1725.ph.i.i" (Ty.int 64) [("for.body.outer.i.outer.i", (Operand.reg "%i.1725.ph.i.ph.i")),
                                       ("if.else46.i.thread.i", (Operand.reg "%inc57.i344.i"))],
          Instr.phi "%T.0723.ph.i.i" (Ty.int 64) [("for.body.outer.i.outer.i", (Operand.reg "%T.0723.ph.i.ph.i")),
                                       ("if.else46.i.thread.i", (Operand.reg "%T.0723.i.i"))],
          Instr.phi "%F.0722.ph.i.i" (Ty.int 64) [("for.body.outer.i.outer.i", (Operand.reg "%F.0722.ph.i.ph.i")),
                                       ("if.else46.i.thread.i", (Operand.reg "%F.0722.i.i"))],
          Instr.phi "%lead.0721.ph.i.i" (Ty.int 64) [("for.body.outer.i.outer.i", (Operand.reg "%lead.0721.ph.i.ph.i")),
                                       ("if.else46.i.thread.i", (Operand.reg "%lead.0721.i.i"))],
          Instr.phi "%in_frac.0718.ph.i.i" (Ty.int 32) [("for.body.outer.i.outer.i", (Operand.reg "%in_frac.0718.ph.i.ph.i")),
                                       ("if.else46.i.thread.i", (Operand.imm (Const.int 32 0x00000001#32)))],
          Instr.phi "%seen.0717.ph.i.i" (Ty.int 32) [("for.body.outer.i.outer.i", (Operand.reg "%seen.0717.ph.i.ph.i")),
                                       ("if.else46.i.thread.i", (Operand.imm (Const.int 32 0x00000000#32)))],
          Instr.icmp "%tobool.not.i.i" (IPred.ne) 32 (Operand.reg "%in_frac.0718.ph.i.i") (Operand.imm (Const.int 32 0x00000000#32)),
          Instr.zext "%inc18.i.i" 1 64 (Operand.reg "%tobool.not.i.i"),
          Instr.gep "%arrayidx5.i.peel.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.1725.ph.i.i"),
          Instr.load "%54" (Ty.int 8) (Operand.reg "%arrayidx5.i.peel.i"),
          Instr.binop "%55" (BinOp.add) 8 (Operand.reg "%54") (Operand.imm (Const.int 8 0xd0#8)),
          Instr.icmp "%or.cond.i.peel.i" (IPred.ult) 8 (Operand.reg "%55") (Operand.imm (Const.int 8 0x0a#8))], Term.condbr (Operand.reg "%or.cond.i.peel.i") "if.then13.i.peel.i" "if.else46.i.i"⟩ := by decide

theorem numFast_findBlock_if_then13_i_peel_i :
    numFastBody.findBlock "if.then13.i.peel.i" = some ⟨"if.then13.i.peel.i", [
          Instr.binop "%inc16.i.peel.i" (BinOp.add) 64 (Operand.reg "%T.0723.ph.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.binop "%spec.select.i.peel.i" (BinOp.add) 64 (Operand.reg "%F.0722.ph.i.i") (Operand.reg "%inc18.i.i"),
          Instr.icmp "%tobool20.not.i.peel.i" (IPred.eq) 32 (Operand.reg "%seen.0717.ph.i.i") (Operand.imm (Const.int 32 0x00000000#32)),
          Instr.icmp "%cmp23.i.peel.i" (IPred.eq) 8 (Operand.reg "%55") (Operand.imm (Const.int 8 0x00#8)),
          Instr.binop "%or.cond510.i.peel.i" (BinOp.and) 1 (Operand.reg "%tobool20.not.i.peel.i") (Operand.reg "%cmp23.i.peel.i")], Term.condbr (Operand.reg "%or.cond510.i.peel.i") "for.inc.thread.i.peel.i" "if.end28.i.i.loopexit609"⟩ := by decide

theorem numFast_findBlock_for_inc_thread_i_peel_i :
    numFastBody.findBlock "for.inc.thread.i.peel.i" = some ⟨"for.inc.thread.i.peel.i", [
          Instr.binop "%inc57798.i.peel.i" (BinOp.add) 64 (Operand.reg "%i.1725.ph.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.icmp "%exitcond.not799.i.peel.i" (IPred.eq) 64 (Operand.reg "%inc57798.i.peel.i") (Operand.reg "%n")], Term.condbr (Operand.reg "%exitcond.not799.i.peel.i") "if.then59.i.i" "for.body.i.i"⟩ := by decide

theorem numFast_findBlock_for_body_i_i :
    numFastBody.findBlock "for.body.i.i" = some ⟨"for.body.i.i", [
          Instr.phi "%i.1725.i.i" (Ty.int 64) [("for.inc.thread.i.i", (Operand.reg "%inc57798.i.i")),
                                       ("for.inc.thread.i.peel.i", (Operand.reg "%inc57798.i.peel.i"))],
          Instr.phi "%T.0723.i.i" (Ty.int 64) [("for.inc.thread.i.i", (Operand.reg "%inc16.i.i")),
                                       ("for.inc.thread.i.peel.i", (Operand.reg "%inc16.i.peel.i"))],
          Instr.phi "%F.0722.i.i" (Ty.int 64) [("for.inc.thread.i.i", (Operand.reg "%spec.select.i.i")),
                                       ("for.inc.thread.i.peel.i", (Operand.reg "%spec.select.i.peel.i"))],
          Instr.phi "%lead.0721.i.in.i" (Ty.int 64) [("for.inc.thread.i.i", (Operand.reg "%lead.0721.i.i")),
                                       ("for.inc.thread.i.peel.i", (Operand.reg "%lead.0721.ph.i.i"))],
          Instr.binop "%lead.0721.i.i" (BinOp.add) 64 (Operand.reg "%lead.0721.i.in.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.gep "%arrayidx5.i.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.1725.i.i"),
          Instr.load "%56" (Ty.int 8) (Operand.reg "%arrayidx5.i.i"),
          Instr.binop "%57" (BinOp.add) 8 (Operand.reg "%56") (Operand.imm (Const.int 8 0xd0#8)),
          Instr.icmp "%or.cond.i.i" (IPred.ult) 8 (Operand.reg "%57") (Operand.imm (Const.int 8 0x0a#8))], Term.condbr (Operand.reg "%or.cond.i.i") "if.then13.i.i" "if.else46.i.thread.i"⟩ := by decide

theorem numFast_findBlock_if_then13_i_i :
    numFastBody.findBlock "if.then13.i.i" = some ⟨"if.then13.i.i", [
          Instr.binop "%inc16.i.i" (BinOp.add) 64 (Operand.reg "%T.0723.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.binop "%spec.select.i.i" (BinOp.add) 64 (Operand.reg "%F.0722.i.i") (Operand.reg "%inc18.i.i"),
          Instr.icmp "%cmp23.i.i" (IPred.eq) 8 (Operand.reg "%57") (Operand.imm (Const.int 8 0x00#8))], Term.condbr (Operand.reg "%cmp23.i.i") "for.inc.thread.i.i" "if.end28.i.i"⟩ := by decide

theorem numFast_findBlock_if_end28_i_i_loopexit609 :
    numFastBody.findBlock "if.end28.i.i.loopexit609" = some ⟨"if.end28.i.i.loopexit609", [
          Instr.select "%58" (Ty.int 32) (Operand.reg "%cmp23.i.peel.i") (Operand.reg "%sticky.0716.ph.i.ph.i") (Operand.imm (Const.int 32 0x00000001#32))], Term.br "if.end28.i.i"⟩ := by decide

theorem numFast_findBlock_if_end28_i_i :
    numFastBody.findBlock "if.end28.i.i" = some ⟨"if.end28.i.i", [
          Instr.phi "%inc16.i.lcssa.i" (Ty.int 64) [("if.end28.i.i.loopexit609", (Operand.reg "%inc16.i.peel.i")),
                                       ("if.then13.i.i", (Operand.reg "%inc16.i.i"))],
          Instr.phi "%spec.select.i.lcssa.i" (Ty.int 64) [("if.end28.i.i.loopexit609", (Operand.reg "%spec.select.i.peel.i")),
                                       ("if.then13.i.i", (Operand.reg "%spec.select.i.i"))],
          Instr.phi "%cmp23.i.lcssa.i" (Ty.int 32) [("if.end28.i.i.loopexit609", (Operand.reg "%58")),
                                       ("if.then13.i.i", (Operand.imm (Const.int 32 0x00000001#32)))],
          Instr.phi "%i.1725.i.lcssa292.i" (Ty.int 64) [("if.end28.i.i.loopexit609", (Operand.reg "%i.1725.ph.i.i")),
                                       ("if.then13.i.i", (Operand.reg "%i.1725.i.i"))],
          Instr.phi "%lead.0721.i.lcssa284.i" (Ty.int 64) [("if.end28.i.i.loopexit609", (Operand.reg "%lead.0721.ph.i.i")),
                                       ("if.then13.i.i", (Operand.reg "%lead.0721.i.i"))],
          Instr.phi "%.lcssa277.i" (Ty.int 8) [("if.end28.i.i.loopexit609", (Operand.reg "%55")),
                                       ("if.then13.i.i", (Operand.reg "%57"))],
          Instr.icmp "%cmp29.i.i" (IPred.ult) 64 (Operand.reg "%R.0724.ph.i.ph.i") (Operand.imm (Const.int 64 0x0000000000000300#64))], Term.condbr (Operand.reg "%cmp29.i.i") "if.then31.i.i" "for.inc.i.i"⟩ := by decide

theorem numFast_findBlock_if_then31_i_i :
    numFastBody.findBlock "if.then31.i.i" = some ⟨"if.then31.i.i", [
          Instr.binop "%inc32.i.i" (BinOp.add) 64 (Operand.reg "%R.0724.ph.i.ph.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.gep "%arrayidx33.i.i" (Ty.int 8) (Operand.reg "%dig.i.i") (Operand.reg "%R.0724.ph.i.ph.i"),
          Instr.store (Ty.int 8) (Operand.reg "%.lcssa277.i") (Operand.reg "%arrayidx33.i.i"),
          Instr.icmp "%cmp34.i.i" (IPred.ult) 64 (Operand.reg "%topn.0719.ph.i.ph.i") (Operand.imm (Const.int 64 0x0000000000000013#64))], Term.condbr (Operand.reg "%cmp34.i.i") "if.then36.i.i" "for.inc.i.i"⟩ := by decide

theorem numFast_findBlock_if_then36_i_i :
    numFastBody.findBlock "if.then36.i.i" = some ⟨"if.then36.i.i", [
          Instr.binop "%mul.i.i" (BinOp.mul) 64 (Operand.reg "%top.0720.ph.i.ph.i") (Operand.imm (Const.int 64 0x000000000000000a#64)),
          Instr.zext "%conv37.i.i" 8 64 (Operand.reg "%.lcssa277.i"),
          Instr.binop "%add.i.i" (BinOp.add) 64 (Operand.reg "%mul.i.i") (Operand.reg "%conv37.i.i"),
          Instr.binop "%inc38.i.i" (BinOp.add) 64 (Operand.reg "%topn.0719.ph.i.ph.i") (Operand.imm (Const.int 64 0x0000000000000001#64))], Term.br "for.inc.i.i"⟩ := by decide

theorem numFast_findBlock_if_else46_i_i :
    numFastBody.findBlock "if.else46.i.i" = some ⟨"if.else46.i.i", [
          Instr.icmp "%cmp48.i.i" (IPred.eq) 8 (Operand.reg "%54") (Operand.imm (Const.int 8 0x2e#8))], Term.condbr (Operand.reg "%cmp48.i.i") "for.inc.i.i" "for.end.i.i"⟩ := by decide

theorem numFast_findBlock_if_else46_i_thread_i :
    numFastBody.findBlock "if.else46.i.thread.i" = some ⟨"if.else46.i.thread.i", [
          Instr.icmp "%cmp48.i322.i" (IPred.ne) 8 (Operand.reg "%56") (Operand.imm (Const.int 8 0x2e#8)),
          Instr.binop "%inc57.i344.i" (BinOp.add) 64 (Operand.reg "%i.1725.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.icmp "%exitcond.not.i345.i" (IPred.eq) 64 (Operand.reg "%inc57.i344.i") (Operand.reg "%n"),
          Instr.binop "%or.cond447.i" (BinOp.or) 1 (Operand.reg "%exitcond.not.i345.i") (Operand.reg "%cmp48.i322.i")], Term.condbr (Operand.reg "%or.cond447.i") "if.then59.i.i" "for.body.outer.i.i"⟩ := by decide

theorem numFast_findBlock_for_inc_i_i :
    numFastBody.findBlock "for.inc.i.i" = some ⟨"for.inc.i.i", [
          Instr.phi "%i.1725.i294.i" (Ty.int 64) [("if.then31.i.i", (Operand.reg "%i.1725.i.lcssa292.i")),
                                       ("if.then36.i.i", (Operand.reg "%i.1725.i.lcssa292.i")),
                                       ("if.else46.i.i", (Operand.reg "%i.1725.ph.i.i")),
                                       ("if.end28.i.i", (Operand.reg "%i.1725.i.lcssa292.i"))],
          Instr.phi "%lead.0721.i287.i" (Ty.int 64) [("if.then31.i.i", (Operand.reg "%lead.0721.i.lcssa284.i")),
                                       ("if.then36.i.i", (Operand.reg "%lead.0721.i.lcssa284.i")),
                                       ("if.else46.i.i", (Operand.reg "%lead.0721.ph.i.i")),
                                       ("if.end28.i.i", (Operand.reg "%lead.0721.i.lcssa284.i"))],
          Instr.phi "%sticky.4.ph.i.i" (Ty.int 32) [("if.then31.i.i", (Operand.reg "%sticky.0716.ph.i.ph.i")),
                                       ("if.then36.i.i", (Operand.reg "%sticky.0716.ph.i.ph.i")),
                                       ("if.else46.i.i", (Operand.reg "%sticky.0716.ph.i.ph.i")),
                                       ("if.end28.i.i", (Operand.reg "%cmp23.i.lcssa.i"))],
          Instr.phi "%seen.4.ph.i.i" (Ty.int 32) [("if.then31.i.i", (Operand.imm (Const.int 32 0x00000001#32))),
                                       ("if.then36.i.i", (Operand.imm (Const.int 32 0x00000001#32))),
                                       ("if.else46.i.i", (Operand.reg "%seen.0717.ph.i.i")),
                                       ("if.end28.i.i", (Operand.imm (Const.int 32 0x00000001#32)))],
          Instr.phi "%in_frac.2.ph.i.i" (Ty.int 32) [("if.then31.i.i", (Operand.reg "%in_frac.0718.ph.i.i")),
                                       ("if.then36.i.i", (Operand.reg "%in_frac.0718.ph.i.i")),
                                       ("if.else46.i.i", (Operand.imm (Const.int 32 0x00000001#32))),
                                       ("if.end28.i.i", (Operand.reg "%in_frac.0718.ph.i.i"))],
          Instr.phi "%topn.4.ph.i.i" (Ty.int 64) [("if.then31.i.i", (Operand.reg "%topn.0719.ph.i.ph.i")),
                                       ("if.then36.i.i", (Operand.reg "%inc38.i.i")),
                                       ("if.else46.i.i", (Operand.reg "%topn.0719.ph.i.ph.i")),
                                       ("if.end28.i.i", (Operand.reg "%topn.0719.ph.i.ph.i"))],
          Instr.phi "%top.4.ph.i.i" (Ty.int 64) [("if.then31.i.i", (Operand.reg "%top.0720.ph.i.ph.i")),
                                       ("if.then36.i.i", (Operand.reg "%add.i.i")),
                                       ("if.else46.i.i", (Operand.reg "%top.0720.ph.i.ph.i")),
                                       ("if.end28.i.i", (Operand.reg "%top.0720.ph.i.ph.i"))],
          Instr.phi "%F.3.ph.i.i" (Ty.int 64) [("if.then31.i.i", (Operand.reg "%spec.select.i.lcssa.i")),
                                       ("if.then36.i.i", (Operand.reg "%spec.select.i.lcssa.i")),
                                       ("if.else46.i.i", (Operand.reg "%F.0722.ph.i.i")),
                                       ("if.end28.i.i", (Operand.reg "%spec.select.i.lcssa.i"))],
          Instr.phi "%T.2.ph.i.i" (Ty.int 64) [("if.then31.i.i", (Operand.reg "%inc16.i.lcssa.i")),
                                       ("if.then36.i.i", (Operand.reg "%inc16.i.lcssa.i")),
                                       ("if.else46.i.i", (Operand.reg "%T.0723.ph.i.i")),
                                       ("if.end28.i.i", (Operand.reg "%inc16.i.lcssa.i"))],
          Instr.phi "%R.4.ph.i.i" (Ty.int 64) [("if.then31.i.i", (Operand.reg "%inc32.i.i")),
                                       ("if.then36.i.i", (Operand.reg "%inc32.i.i")),
                                       ("if.else46.i.i", (Operand.reg "%R.0724.ph.i.ph.i")),
                                       ("if.end28.i.i", (Operand.reg "%R.0724.ph.i.ph.i"))],
          Instr.binop "%inc57.i.i" (BinOp.add) 64 (Operand.reg "%i.1725.i294.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.icmp "%exitcond.not.i.i" (IPred.eq) 64 (Operand.reg "%inc57.i.i") (Operand.reg "%n")], Term.condbr (Operand.reg "%exitcond.not.i.i") "for.end.thread.i.i" "for.body.outer.i.outer.i"⟩ := by decide

theorem numFast_findBlock_for_inc_thread_i_i :
    numFastBody.findBlock "for.inc.thread.i.i" = some ⟨"for.inc.thread.i.i", [
          Instr.binop "%inc57798.i.i" (BinOp.add) 64 (Operand.reg "%i.1725.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.icmp "%exitcond.not799.i.i" (IPred.eq) 64 (Operand.reg "%inc57798.i.i") (Operand.reg "%n")], Term.condbr (Operand.reg "%exitcond.not799.i.i") "if.then59.i.i" "for.body.i.i"⟩ := by decide

theorem numFast_findBlock_for_end_i_i :
    numFastBody.findBlock "for.end.i.i" = some ⟨"for.end.i.i", [
          Instr.icmp "%tobool58.not.i.i" (IPred.eq) 32 (Operand.reg "%seen.0717.ph.i.i") (Operand.imm (Const.int 32 0x00000000#32))], Term.condbr (Operand.reg "%tobool58.not.i.i") "if.then59.i.i" "if.then64.i.i"⟩ := by decide

theorem numFast_findBlock_for_end_thread_i_i :
    numFastBody.findBlock "for.end.thread.i.i" = some ⟨"for.end.thread.i.i", [
          Instr.icmp "%59" (IPred.eq) 32 (Operand.reg "%seen.4.ph.i.i") (Operand.imm (Const.int 32 0x00000000#32))], Term.condbr (Operand.reg "%59") "if.then59.i.i" "if.end104.i.i"⟩ := by decide

theorem numFast_findBlock_if_then59_i_i :
    numFastBody.findBlock "if.then59.i.i" = some ⟨"if.then59.i.i", [
          Instr.select "%cond.i.i" Ty.double (Operand.reg "%cmp1.i") (Operand.imm (Const.float 0x8000000000000000#64)) (Operand.imm (Const.float 0x0000000000000000#64))], Term.br "if.end291"⟩ := by decide

theorem numFast_findBlock_if_then64_i_i :
    numFastBody.findBlock "if.then64.i.i" = some ⟨"if.then64.i.i", [
          Instr.binop "%inc65.i.i" (BinOp.add) 64 (Operand.reg "%i.1725.ph.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.icmp "%cmp66.i.i" (IPred.ult) 64 (Operand.reg "%inc65.i.i") (Operand.reg "%n")], Term.condbr (Operand.reg "%cmp66.i.i") "land.lhs.true68.i.i" "if.end83.i.i"⟩ := by decide

theorem numFast_findBlock_land_lhs_true68_i_i :
    numFastBody.findBlock "land.lhs.true68.i.i" = some ⟨"land.lhs.true68.i.i", [
          Instr.gep "%arrayidx69.i.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%inc65.i.i"),
          Instr.load "%60" (Ty.int 8) (Operand.reg "%arrayidx69.i.i")], Term.br "NodeBlock25"⟩ := by decide

theorem numFast_findBlock_NodeBlock25 :
    numFastBody.findBlock "NodeBlock25" = some ⟨"NodeBlock25", [
          Instr.icmp "%Pivot26" (IPred.slt) 8 (Operand.reg "%60") (Operand.imm (Const.int 8 0x2d#8))], Term.condbr (Operand.reg "%Pivot26") "LeafBlock21" "LeafBlock23"⟩ := by decide

theorem numFast_findBlock_LeafBlock23 :
    numFastBody.findBlock "LeafBlock23" = some ⟨"LeafBlock23", [
          Instr.icmp "%SwitchLeaf24" (IPred.eq) 8 (Operand.reg "%60") (Operand.imm (Const.int 8 0x2d#8))], Term.condbr (Operand.reg "%SwitchLeaf24") "if.then77.i.i" "if.end83.i.i"⟩ := by decide

theorem numFast_findBlock_LeafBlock21 :
    numFastBody.findBlock "LeafBlock21" = some ⟨"LeafBlock21", [
          Instr.icmp "%SwitchLeaf22" (IPred.eq) 8 (Operand.reg "%60") (Operand.imm (Const.int 8 0x2b#8))], Term.condbr (Operand.reg "%SwitchLeaf22") "if.then77.i.i" "if.end83.i.i"⟩ := by decide

theorem numFast_findBlock_if_then77_i_i :
    numFastBody.findBlock "if.then77.i.i" = some ⟨"if.then77.i.i", [
          Instr.icmp "%cmp80.i.i" (IPred.ne) 8 (Operand.reg "%60") (Operand.imm (Const.int 8 0x2d#8)),
          Instr.binop "%inc82.i.i" (BinOp.add) 64 (Operand.reg "%i.1725.ph.i.i") (Operand.imm (Const.int 64 0x0000000000000002#64))], Term.br "if.end83.i.i"⟩ := by decide

theorem numFast_findBlock_if_end83_i_i :
    numFastBody.findBlock "if.end83.i.i" = some ⟨"if.end83.i.i", [
          Instr.phi "%esign.0.i.i" (Ty.int 1) [("if.then77.i.i", (Operand.reg "%cmp80.i.i")),
                                       ("if.then64.i.i", (Operand.imm (Const.int 1 0x1#1))),
                                       ("LeafBlock21", (Operand.imm (Const.int 1 0x1#1))),
                                       ("LeafBlock23", (Operand.imm (Const.int 1 0x1#1)))],
          Instr.phi "%i.2.i.i" (Ty.int 64) [("if.then77.i.i", (Operand.reg "%inc82.i.i")),
                                       ("if.then64.i.i", (Operand.reg "%inc65.i.i")),
                                       ("LeafBlock21", (Operand.reg "%inc65.i.i")),
                                       ("LeafBlock23", (Operand.reg "%inc65.i.i"))],
          Instr.icmp "%cmp85733.i.i" (IPred.ult) 64 (Operand.reg "%i.2.i.i") (Operand.reg "%n")], Term.condbr (Operand.reg "%cmp85733.i.i") "for.body87.i.i.preheader" "for.end100.i.i"⟩ := by decide

theorem numFast_findBlock_for_body87_i_i_preheader :
    numFastBody.findBlock "for.body87.i.i.preheader" = some ⟨"for.body87.i.i.preheader", [
          Instr.binop "%61" (BinOp.sub) 64 (Operand.reg "%n") (Operand.reg "%i.2.i.i"),
          Instr.binop "%xtraiter" (BinOp.and) 64 (Operand.reg "%61") (Operand.imm (Const.int 64 0x0000000000000003#64)),
          Instr.binop "%62" (BinOp.sub) 64 (Operand.reg "%i.2.i.i") (Operand.reg "%n"),
          Instr.icmp "%63" (IPred.ugt) 64 (Operand.reg "%62") (Operand.imm (Const.int 64 0xfffffffffffffffc#64))], Term.condbr (Operand.reg "%63") "for.end100.i.i.loopexit.unr-lcssa" "for.body87.i.i.preheader.new"⟩ := by decide

theorem numFast_findBlock_for_body87_i_i_preheader_new :
    numFastBody.findBlock "for.body87.i.i.preheader.new" = some ⟨"for.body87.i.i.preheader.new", [
          Instr.binop "%unroll_iter" (BinOp.and) 64 (Operand.reg "%61") (Operand.imm (Const.int 64 0xfffffffffffffffc#64)),
          Instr.gep "%invariant.gep" (Ty.int 8) (Operand.reg "%p") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.gep "%invariant.gep1191" (Ty.int 8) (Operand.reg "%p") (Operand.imm (Const.int 64 0x0000000000000002#64)),
          Instr.gep "%invariant.gep1193" (Ty.int 8) (Operand.reg "%p") (Operand.imm (Const.int 64 0x0000000000000003#64))], Term.br "for.body87.i.i"⟩ := by decide

theorem numFast_findBlock_for_body87_i_i :
    numFastBody.findBlock "for.body87.i.i" = some ⟨"for.body87.i.i", [
          Instr.phi "%i.3735.i.i" (Ty.int 64) [("for.body87.i.i.preheader.new", (Operand.reg "%i.2.i.i")),
                                       ("for.inc98.i.i.3", (Operand.reg "%inc99.i.i.3"))],
          Instr.phi "%e.0734.i.i" (Ty.int 64) [("for.body87.i.i.preheader.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.inc98.i.i.3", (Operand.reg "%e.1.i.i.3"))],
          Instr.phi "%niter" (Ty.int 64) [("for.body87.i.i.preheader.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.inc98.i.i.3", (Operand.reg "%niter.next.3"))],
          Instr.icmp "%cmp88.i.i" (IPred.slt) 64 (Operand.reg "%e.0734.i.i") (Operand.imm (Const.int 64 0x00000000000f4240#64))], Term.condbr (Operand.reg "%cmp88.i.i") "if.then90.i.i" "for.inc98.i.i"⟩ := by decide

theorem numFast_findBlock_if_then90_i_i :
    numFastBody.findBlock "if.then90.i.i" = some ⟨"if.then90.i.i", [
          Instr.binop "%mul91.i.i" (BinOp.mul) 64 (Operand.reg "%e.0734.i.i") (Operand.imm (Const.int 64 0x000000000000000a#64)),
          Instr.gep "%arrayidx92.i.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.3735.i.i"),
          Instr.load "%64" (Ty.int 8) (Operand.reg "%arrayidx92.i.i"),
          Instr.zext "%conv93.i.i" 8 64 (Operand.reg "%64"),
          Instr.binop "%sub94.i.i" (BinOp.add) 64 (Operand.reg "%mul91.i.i") (Operand.imm (Const.int 64 0xffffffffffffffd0#64)),
          Instr.binop "%add96.i.i" (BinOp.add) 64 (Operand.reg "%sub94.i.i") (Operand.reg "%conv93.i.i")], Term.br "for.inc98.i.i"⟩ := by decide

theorem numFast_findBlock_for_inc98_i_i :
    numFastBody.findBlock "for.inc98.i.i" = some ⟨"for.inc98.i.i", [
          Instr.phi "%e.1.i.i" (Ty.int 64) [("if.then90.i.i", (Operand.reg "%add96.i.i")),
                                       ("for.body87.i.i", (Operand.reg "%e.0734.i.i"))],
          Instr.icmp "%cmp88.i.i.1" (IPred.slt) 64 (Operand.reg "%e.1.i.i") (Operand.imm (Const.int 64 0x00000000000f4240#64))], Term.condbr (Operand.reg "%cmp88.i.i.1") "if.then90.i.i.1" "for.inc98.i.i.1"⟩ := by decide

theorem numFast_findBlock_if_then90_i_i_1 :
    numFastBody.findBlock "if.then90.i.i.1" = some ⟨"if.then90.i.i.1", [
          Instr.binop "%mul91.i.i.1" (BinOp.mul) 64 (Operand.reg "%e.1.i.i") (Operand.imm (Const.int 64 0x000000000000000a#64)),
          Instr.gep "%gep" (Ty.int 8) (Operand.reg "%invariant.gep") (Operand.reg "%i.3735.i.i"),
          Instr.load "%65" (Ty.int 8) (Operand.reg "%gep"),
          Instr.zext "%conv93.i.i.1" 8 64 (Operand.reg "%65"),
          Instr.binop "%sub94.i.i.1" (BinOp.add) 64 (Operand.reg "%mul91.i.i.1") (Operand.imm (Const.int 64 0xffffffffffffffd0#64)),
          Instr.binop "%add96.i.i.1" (BinOp.add) 64 (Operand.reg "%sub94.i.i.1") (Operand.reg "%conv93.i.i.1")], Term.br "for.inc98.i.i.1"⟩ := by decide

theorem numFast_findBlock_for_inc98_i_i_1 :
    numFastBody.findBlock "for.inc98.i.i.1" = some ⟨"for.inc98.i.i.1", [
          Instr.phi "%e.1.i.i.1" (Ty.int 64) [("if.then90.i.i.1", (Operand.reg "%add96.i.i.1")),
                                       ("for.inc98.i.i", (Operand.reg "%e.1.i.i"))],
          Instr.icmp "%cmp88.i.i.2" (IPred.slt) 64 (Operand.reg "%e.1.i.i.1") (Operand.imm (Const.int 64 0x00000000000f4240#64))], Term.condbr (Operand.reg "%cmp88.i.i.2") "if.then90.i.i.2" "for.inc98.i.i.2"⟩ := by decide

theorem numFast_findBlock_if_then90_i_i_2 :
    numFastBody.findBlock "if.then90.i.i.2" = some ⟨"if.then90.i.i.2", [
          Instr.binop "%mul91.i.i.2" (BinOp.mul) 64 (Operand.reg "%e.1.i.i.1") (Operand.imm (Const.int 64 0x000000000000000a#64)),
          Instr.gep "%gep1192" (Ty.int 8) (Operand.reg "%invariant.gep1191") (Operand.reg "%i.3735.i.i"),
          Instr.load "%66" (Ty.int 8) (Operand.reg "%gep1192"),
          Instr.zext "%conv93.i.i.2" 8 64 (Operand.reg "%66"),
          Instr.binop "%sub94.i.i.2" (BinOp.add) 64 (Operand.reg "%mul91.i.i.2") (Operand.imm (Const.int 64 0xffffffffffffffd0#64)),
          Instr.binop "%add96.i.i.2" (BinOp.add) 64 (Operand.reg "%sub94.i.i.2") (Operand.reg "%conv93.i.i.2")], Term.br "for.inc98.i.i.2"⟩ := by decide

theorem numFast_findBlock_for_inc98_i_i_2 :
    numFastBody.findBlock "for.inc98.i.i.2" = some ⟨"for.inc98.i.i.2", [
          Instr.phi "%e.1.i.i.2" (Ty.int 64) [("if.then90.i.i.2", (Operand.reg "%add96.i.i.2")),
                                       ("for.inc98.i.i.1", (Operand.reg "%e.1.i.i.1"))],
          Instr.icmp "%cmp88.i.i.3" (IPred.slt) 64 (Operand.reg "%e.1.i.i.2") (Operand.imm (Const.int 64 0x00000000000f4240#64))], Term.condbr (Operand.reg "%cmp88.i.i.3") "if.then90.i.i.3" "for.inc98.i.i.3"⟩ := by decide

theorem numFast_findBlock_if_then90_i_i_3 :
    numFastBody.findBlock "if.then90.i.i.3" = some ⟨"if.then90.i.i.3", [
          Instr.binop "%mul91.i.i.3" (BinOp.mul) 64 (Operand.reg "%e.1.i.i.2") (Operand.imm (Const.int 64 0x000000000000000a#64)),
          Instr.gep "%gep1194" (Ty.int 8) (Operand.reg "%invariant.gep1193") (Operand.reg "%i.3735.i.i"),
          Instr.load "%67" (Ty.int 8) (Operand.reg "%gep1194"),
          Instr.zext "%conv93.i.i.3" 8 64 (Operand.reg "%67"),
          Instr.binop "%sub94.i.i.3" (BinOp.add) 64 (Operand.reg "%mul91.i.i.3") (Operand.imm (Const.int 64 0xffffffffffffffd0#64)),
          Instr.binop "%add96.i.i.3" (BinOp.add) 64 (Operand.reg "%sub94.i.i.3") (Operand.reg "%conv93.i.i.3")], Term.br "for.inc98.i.i.3"⟩ := by decide

theorem numFast_findBlock_for_inc98_i_i_3 :
    numFastBody.findBlock "for.inc98.i.i.3" = some ⟨"for.inc98.i.i.3", [
          Instr.phi "%e.1.i.i.3" (Ty.int 64) [("if.then90.i.i.3", (Operand.reg "%add96.i.i.3")),
                                       ("for.inc98.i.i.2", (Operand.reg "%e.1.i.i.2"))],
          Instr.binop "%inc99.i.i.3" (BinOp.add) 64 (Operand.reg "%i.3735.i.i") (Operand.imm (Const.int 64 0x0000000000000004#64)),
          Instr.binop "%niter.next.3" (BinOp.add) 64 (Operand.reg "%niter") (Operand.imm (Const.int 64 0x0000000000000004#64)),
          Instr.icmp "%niter.ncmp.3" (IPred.eq) 64 (Operand.reg "%niter.next.3") (Operand.reg "%unroll_iter")], Term.condbr (Operand.reg "%niter.ncmp.3") "for.end100.i.i.loopexit.unr-lcssa" "for.body87.i.i"⟩ := by decide

theorem numFast_findBlock_for_end100_i_i_loopexit_unr_lcssa :
    numFastBody.findBlock "for.end100.i.i.loopexit.unr-lcssa" = some ⟨"for.end100.i.i.loopexit.unr-lcssa", [
          Instr.phi "%e.1.i.i.lcssa.ph" (Ty.int 64) [("for.body87.i.i.preheader", (Operand.imm Const.poison)),
                                       ("for.inc98.i.i.3", (Operand.reg "%e.1.i.i.3"))],
          Instr.phi "%i.3735.i.i.unr" (Ty.int 64) [("for.body87.i.i.preheader", (Operand.reg "%i.2.i.i")),
                                       ("for.inc98.i.i.3", (Operand.reg "%inc99.i.i.3"))],
          Instr.phi "%e.0734.i.i.unr" (Ty.int 64) [("for.body87.i.i.preheader", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.inc98.i.i.3", (Operand.reg "%e.1.i.i.3"))],
          Instr.icmp "%lcmp.mod.not" (IPred.eq) 64 (Operand.reg "%xtraiter") (Operand.imm (Const.int 64 0x0000000000000000#64))], Term.condbr (Operand.reg "%lcmp.mod.not") "for.end100.i.i" "for.body87.i.i.epil"⟩ := by decide

theorem numFast_findBlock_for_body87_i_i_epil :
    numFastBody.findBlock "for.body87.i.i.epil" = some ⟨"for.body87.i.i.epil", [
          Instr.phi "%i.3735.i.i.epil" (Ty.int 64) [("for.inc98.i.i.epil", (Operand.reg "%inc99.i.i.epil")),
                                       ("for.end100.i.i.loopexit.unr-lcssa", (Operand.reg "%i.3735.i.i.unr"))],
          Instr.phi "%e.0734.i.i.epil" (Ty.int 64) [("for.inc98.i.i.epil", (Operand.reg "%e.1.i.i.epil")),
                                       ("for.end100.i.i.loopexit.unr-lcssa", (Operand.reg "%e.0734.i.i.unr"))],
          Instr.phi "%epil.iter" (Ty.int 64) [("for.inc98.i.i.epil", (Operand.reg "%epil.iter.next")),
                                       ("for.end100.i.i.loopexit.unr-lcssa", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
          Instr.icmp "%cmp88.i.i.epil" (IPred.slt) 64 (Operand.reg "%e.0734.i.i.epil") (Operand.imm (Const.int 64 0x00000000000f4240#64))], Term.condbr (Operand.reg "%cmp88.i.i.epil") "if.then90.i.i.epil" "for.inc98.i.i.epil"⟩ := by decide

theorem numFast_findBlock_if_then90_i_i_epil :
    numFastBody.findBlock "if.then90.i.i.epil" = some ⟨"if.then90.i.i.epil", [
          Instr.binop "%mul91.i.i.epil" (BinOp.mul) 64 (Operand.reg "%e.0734.i.i.epil") (Operand.imm (Const.int 64 0x000000000000000a#64)),
          Instr.gep "%arrayidx92.i.i.epil" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%i.3735.i.i.epil"),
          Instr.load "%68" (Ty.int 8) (Operand.reg "%arrayidx92.i.i.epil"),
          Instr.zext "%conv93.i.i.epil" 8 64 (Operand.reg "%68"),
          Instr.binop "%sub94.i.i.epil" (BinOp.add) 64 (Operand.reg "%mul91.i.i.epil") (Operand.imm (Const.int 64 0xffffffffffffffd0#64)),
          Instr.binop "%add96.i.i.epil" (BinOp.add) 64 (Operand.reg "%sub94.i.i.epil") (Operand.reg "%conv93.i.i.epil")], Term.br "for.inc98.i.i.epil"⟩ := by decide

theorem numFast_findBlock_for_inc98_i_i_epil :
    numFastBody.findBlock "for.inc98.i.i.epil" = some ⟨"for.inc98.i.i.epil", [
          Instr.phi "%e.1.i.i.epil" (Ty.int 64) [("if.then90.i.i.epil", (Operand.reg "%add96.i.i.epil")),
                                       ("for.body87.i.i.epil", (Operand.reg "%e.0734.i.i.epil"))],
          Instr.binop "%inc99.i.i.epil" (BinOp.add) 64 (Operand.reg "%i.3735.i.i.epil") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.binop "%epil.iter.next" (BinOp.add) 64 (Operand.reg "%epil.iter") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.icmp "%epil.iter.cmp.not" (IPred.eq) 64 (Operand.reg "%epil.iter.next") (Operand.reg "%xtraiter")], Term.condbr (Operand.reg "%epil.iter.cmp.not") "for.end100.i.i" "for.body87.i.i.epil"⟩ := by decide

theorem numFast_findBlock_for_end100_i_i :
    numFastBody.findBlock "for.end100.i.i" = some ⟨"for.end100.i.i", [
          Instr.phi "%e.0.lcssa.i.i" (Ty.int 64) [("if.end83.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.end100.i.i.loopexit.unr-lcssa", (Operand.reg "%e.1.i.i.lcssa.ph")),
                                       ("for.inc98.i.i.epil", (Operand.reg "%e.1.i.i.epil"))],
          Instr.binop "%sub102.i.i" (BinOp.sub) 64 (Operand.imm (Const.int 64 0x0000000000000000#64)) (Operand.reg "%e.0.lcssa.i.i"),
          Instr.select "%cond103.i.i" (Ty.int 64) (Operand.reg "%esign.0.i.i") (Operand.reg "%e.0.lcssa.i.i") (Operand.reg "%sub102.i.i")], Term.br "if.end104.i.i"⟩ := by decide

theorem numFast_findBlock_if_end104_i_i :
    numFastBody.findBlock "if.end104.i.i" = some ⟨"if.end104.i.i", [
          Instr.phi "%lead.0721.i286.i" (Ty.int 64) [("for.end100.i.i", (Operand.reg "%lead.0721.ph.i.i")),
                                       ("for.end.thread.i.i", (Operand.reg "%lead.0721.i287.i"))],
          Instr.phi "%sticky.0714.i.i" (Ty.int 32) [("for.end100.i.i", (Operand.reg "%sticky.0716.ph.i.ph.i")),
                                       ("for.end.thread.i.i", (Operand.reg "%sticky.4.ph.i.i"))],
          Instr.phi "%topn.0711.i.i" (Ty.int 64) [("for.end100.i.i", (Operand.reg "%topn.0719.ph.i.ph.i")),
                                       ("for.end.thread.i.i", (Operand.reg "%topn.4.ph.i.i"))],
          Instr.phi "%top.0709.i.i" (Ty.int 64) [("for.end100.i.i", (Operand.reg "%top.0720.ph.i.ph.i")),
                                       ("for.end.thread.i.i", (Operand.reg "%top.4.ph.i.i"))],
          Instr.phi "%F.0705.i.i" (Ty.int 64) [("for.end100.i.i", (Operand.reg "%F.0722.ph.i.i")),
                                       ("for.end.thread.i.i", (Operand.reg "%F.3.ph.i.i"))],
          Instr.phi "%T.0703.i.i" (Ty.int 64) [("for.end100.i.i", (Operand.reg "%T.0723.ph.i.i")),
                                       ("for.end.thread.i.i", (Operand.reg "%T.2.ph.i.i"))],
          Instr.phi "%R.0701.i.i" (Ty.int 64) [("for.end100.i.i", (Operand.reg "%R.0724.ph.i.ph.i")),
                                       ("for.end.thread.i.i", (Operand.reg "%R.4.ph.i.i"))],
          Instr.phi "%exp10.0.i.i" (Ty.int 64) [("for.end100.i.i", (Operand.reg "%cond103.i.i")),
                                       ("for.end.thread.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
          Instr.binop "%sub105.i.i" (BinOp.sub) 64 (Operand.reg "%exp10.0.i.i") (Operand.reg "%F.0705.i.i"),
          Instr.binop "%69" (BinOp.add) 64 (Operand.reg "%lead.0721.i286.i") (Operand.reg "%R.0701.i.i"),
          Instr.binop "%sub107.i.i" (BinOp.sub) 64 (Operand.reg "%T.0703.i.i") (Operand.reg "%69"),
          Instr.binop "%add108.i.i" (BinOp.add) 64 (Operand.reg "%sub107.i.i") (Operand.reg "%sub105.i.i"),
          Instr.binop "%sub109.i.i" (BinOp.add) 64 (Operand.reg "%R.0701.i.i") (Operand.imm (Const.int 64 0xffffffffffffffff#64)),
          Instr.binop "%add110.i.i" (BinOp.add) 64 (Operand.reg "%sub109.i.i") (Operand.reg "%add108.i.i"),
          Instr.icmp "%cmp111.i.i" (IPred.sgt) 64 (Operand.reg "%add110.i.i") (Operand.imm (Const.int 64 0x0000000000000134#64))], Term.condbr (Operand.reg "%cmp111.i.i") "if.then113.i.i" "if.end120.i.i"⟩ := by decide

theorem numFast_findBlock_if_then113_i_i :
    numFastBody.findBlock "if.then113.i.i" = some ⟨"if.then113.i.i", [
          Instr.select "%spec.select694.i.i" Ty.double (Operand.reg "%cmp1.i") (Operand.imm (Const.float 0xfff0000000000000#64)) (Operand.imm (Const.float 0x7ff0000000000000#64))], Term.br "if.end291"⟩ := by decide

theorem numFast_findBlock_if_end120_i_i :
    numFastBody.findBlock "if.end120.i.i" = some ⟨"if.end120.i.i", [
          Instr.icmp "%cmp121.i.i" (IPred.slt) 64 (Operand.reg "%add110.i.i") (Operand.imm (Const.int 64 0xfffffffffffffebc#64))], Term.condbr (Operand.reg "%cmp121.i.i") "if.then123.i.i" "if.end126.i.i"⟩ := by decide

theorem numFast_findBlock_if_then123_i_i :
    numFastBody.findBlock "if.then123.i.i" = some ⟨"if.then123.i.i", [
          Instr.select "%cond125.i.i" Ty.double (Operand.reg "%cmp1.i") (Operand.imm (Const.float 0x8000000000000000#64)) (Operand.imm (Const.float 0x0000000000000000#64))], Term.br "if.end291"⟩ := by decide

theorem numFast_findBlock_if_end126_i_i :
    numFastBody.findBlock "if.end126.i.i" = some ⟨"if.end126.i.i", [
          Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000620#64))),
                             (Ty.ptr, (Operand.reg "%v.i.i"))],
          Instr.gep "%sticky127.i.i" (Ty.int 8) (Operand.reg "%v.i.i") (Operand.imm (Const.int 64 0x0000000000000618#64)),
          Instr.store (Ty.int 32) (Operand.reg "%sticky.0714.i.i") (Operand.reg "%sticky127.i.i"),
          Instr.gep "%S128.i.i" (Ty.int 8) (Operand.reg "%v.i.i") (Operand.imm (Const.int 64 0x0000000000000610#64)),
          Instr.store (Ty.int 64) (Operand.reg "%add108.i.i") (Operand.reg "%S128.i.i"),
          Instr.gep "%n.i.i.i" (Ty.int 8) (Operand.reg "%v.i.i") (Operand.imm (Const.int 64 0x0000000000000300#64)),
          Instr.icmp "%cmp130737.not.i.i" (IPred.eq) 64 (Operand.reg "%R.0701.i.i") (Operand.imm (Const.int 64 0x0000000000000000#64))], Term.condbr (Operand.reg "%cmp130737.not.i.i") "if.end151.i.i.sink.split" "for.body132.i.i"⟩ := by decide

theorem numFast_findBlock_for_cond_cleanup_i_i :
    numFastBody.findBlock "for.cond.cleanup.i.i" = some ⟨"for.cond.cleanup.i.i", [
          Instr.store (Ty.int 32) (Operand.reg "%78") (Operand.reg "%n.i.i.i"),
          Instr.icmp "%tobool147.not.i.i" (IPred.eq) 32 (Operand.reg "%cn.1.i.i") (Operand.imm (Const.int 32 0x00000000#32))], Term.condbr (Operand.reg "%tobool147.not.i.i") "if.end151.i.i" "if.then148.i.i"⟩ := by decide

theorem numFast_findBlock_for_body132_i_i :
    numFastBody.findBlock "for.body132.i.i" = some ⟨"for.body132.i.i", [
          Instr.phi "%j.0740.i.i" (Ty.int 64) [("for.inc143.i.i", (Operand.reg "%inc144.i.i")),
                                       ("if.end126.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
          Instr.phi "%cn.0739.i.i" (Ty.int 32) [("for.inc143.i.i", (Operand.reg "%cn.1.i.i")),
                                       ("if.end126.i.i", (Operand.imm (Const.int 32 0x00000000#32)))],
          Instr.phi "%chunk.0738.i.i" (Ty.int 64) [("for.inc143.i.i", (Operand.reg "%chunk.1.i.i")),
                                       ("if.end126.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
          Instr.phi "%70" (Ty.int 32) [("for.inc143.i.i", (Operand.reg "%78")),
                                       ("if.end126.i.i", (Operand.imm (Const.int 32 0x00000000#32)))],
          Instr.binop "%mul133.i.i" (BinOp.mul) 64 (Operand.reg "%chunk.0738.i.i") (Operand.imm (Const.int 64 0x000000000000000a#64)),
          Instr.gep "%arrayidx134.i.i" (Ty.int 8) (Operand.reg "%dig.i.i") (Operand.reg "%j.0740.i.i"),
          Instr.load "%71" (Ty.int 8) (Operand.reg "%arrayidx134.i.i"),
          Instr.zext "%conv135.i.i" 8 64 (Operand.reg "%71"),
          Instr.binop "%add136.i.i" (BinOp.add) 64 (Operand.reg "%mul133.i.i") (Operand.reg "%conv135.i.i"),
          Instr.binop "%inc137.i.i" (BinOp.add) 32 (Operand.reg "%cn.0739.i.i") (Operand.imm (Const.int 32 0x00000001#32)),
          Instr.icmp "%cmp138.i.i" (IPred.eq) 32 (Operand.reg "%inc137.i.i") (Operand.imm (Const.int 32 0x00000013#32))], Term.condbr (Operand.reg "%cmp138.i.i") "if.then140.i.i" "for.inc143.i.i"⟩ := by decide

theorem numFast_findBlock_if_then140_i_i :
    numFastBody.findBlock "if.then140.i.i" = some ⟨"if.then140.i.i", [
          Instr.zext "%conv.i.i.i" 64 128 (Operand.reg "%add136.i.i"),
          Instr.icmp "%cmp28.i.i.i" (IPred.sgt) 32 (Operand.reg "%70") (Operand.imm (Const.int 32 0x00000000#32))], Term.condbr (Operand.reg "%cmp28.i.i.i") "for.body.lr.ph.i.i.i" "while.cond.preheader.i.i.i"⟩ := by decide

theorem numFast_findBlock_for_body_lr_ph_i_i_i :
    numFastBody.findBlock "for.body.lr.ph.i.i.i" = some ⟨"for.body.lr.ph.i.i.i", [
          Instr.zext "%wide.trip.count.i.i.i" 32 64 (Operand.reg "%70"),
          Instr.binop "%xtraiter1043" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
          Instr.icmp "%72" (IPred.ult) 32 (Operand.reg "%70") (Operand.imm (Const.int 32 0x00000004#32))], Term.condbr (Operand.reg "%72") "while.cond.preheader.i.i.i.loopexit.unr-lcssa" "for.body.lr.ph.i.i.i.new"⟩ := by decide

theorem numFast_findBlock_for_body_lr_ph_i_i_i_new :
    numFastBody.findBlock "for.body.lr.ph.i.i.i.new" = some ⟨"for.body.lr.ph.i.i.i.new", [
          Instr.binop "%unroll_iter1047" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i.i.i") (Operand.imm (Const.int 64 0x000000007ffffffc#64))], Term.br "for.body.i.i.i"⟩ := by decide

theorem numFast_findBlock_while_cond_preheader_i_i_i_loopexit_unr_lcssa :
    numFastBody.findBlock "while.cond.preheader.i.i.i.loopexit.unr-lcssa" = some ⟨"while.cond.preheader.i.i.i.loopexit.unr-lcssa", [
          Instr.phi "%shr.i.i.i.lcssa.ph" (Ty.int 128) [("for.body.lr.ph.i.i.i", (Operand.imm Const.poison)),
                                       ("for.body.i.i.i", (Operand.reg "%shr.i.i.i.3"))],
          Instr.phi "%indvars.iv.i.i.i.unr" (Ty.int 64) [("for.body.lr.ph.i.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i.i.i", (Operand.reg "%indvars.iv.next.i.i.i.3"))],
          Instr.phi "%carry.029.i.i.i.unr" (Ty.int 128) [("for.body.lr.ph.i.i.i", (Operand.reg "%conv.i.i.i")),
                                       ("for.body.i.i.i", (Operand.reg "%shr.i.i.i.3"))],
          Instr.icmp "%lcmp.mod1045.not" (IPred.eq) 64 (Operand.reg "%xtraiter1043") (Operand.imm (Const.int 64 0x0000000000000000#64))], Term.condbr (Operand.reg "%lcmp.mod1045.not") "while.cond.preheader.i.i.i" "for.body.i.i.i.epil"⟩ := by decide

theorem numFast_findBlock_for_body_i_i_i_epil :
    numFastBody.findBlock "for.body.i.i.i.epil" = some ⟨"for.body.i.i.i.epil", [
          Instr.phi "%indvars.iv.i.i.i.epil" (Ty.int 64) [("for.body.i.i.i.epil", (Operand.reg "%indvars.iv.next.i.i.i.epil")),
                                       ("while.cond.preheader.i.i.i.loopexit.unr-lcssa", (Operand.reg "%indvars.iv.i.i.i.unr"))],
          Instr.phi "%carry.029.i.i.i.epil" (Ty.int 128) [("for.body.i.i.i.epil", (Operand.reg "%shr.i.i.i.epil")),
                                       ("while.cond.preheader.i.i.i.loopexit.unr-lcssa", (Operand.reg "%carry.029.i.i.i.unr"))],
          Instr.phi "%epil.iter1044" (Ty.int 64) [("for.body.i.i.i.epil", (Operand.reg "%epil.iter1044.next")),
                                       ("while.cond.preheader.i.i.i.loopexit.unr-lcssa", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
          Instr.gep "%arrayidx.i.i.i.epil" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.i.i.i.epil"),
          Instr.load "%73" (Ty.int 64) (Operand.reg "%arrayidx.i.i.i.epil"),
          Instr.zext "%conv2.i.i.i.epil" 64 128 (Operand.reg "%73"),
          Instr.binop "%mul.i.i.i.epil" (BinOp.mul) 128 (Operand.reg "%conv2.i.i.i.epil") (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
          Instr.binop "%add4.i.i.i.epil" (BinOp.add) 128 (Operand.reg "%mul.i.i.i.epil") (Operand.reg "%carry.029.i.i.i.epil"),
          Instr.trunc "%conv5.i.i.i.epil" 128 64 (Operand.reg "%add4.i.i.i.epil"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i.i.epil") (Operand.reg "%arrayidx.i.i.i.epil"),
          Instr.binop "%shr.i.i.i.epil" (BinOp.lshr) 128 (Operand.reg "%add4.i.i.i.epil") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i.i.i.epil" (BinOp.add) 64 (Operand.reg "%indvars.iv.i.i.i.epil") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.binop "%epil.iter1044.next" (BinOp.add) 64 (Operand.reg "%epil.iter1044") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.icmp "%epil.iter1044.cmp.not" (IPred.eq) 64 (Operand.reg "%epil.iter1044.next") (Operand.reg "%xtraiter1043")], Term.condbr (Operand.reg "%epil.iter1044.cmp.not") "while.cond.preheader.i.i.i" "for.body.i.i.i.epil"⟩ := by decide

theorem numFast_findBlock_while_cond_preheader_i_i_i :
    numFastBody.findBlock "while.cond.preheader.i.i.i" = some ⟨"while.cond.preheader.i.i.i", [
          Instr.phi "%carry.0.lcssa.i.i.i" (Ty.int 128) [("if.then140.i.i", (Operand.reg "%conv.i.i.i")),
                                       ("while.cond.preheader.i.i.i.loopexit.unr-lcssa", (Operand.reg "%shr.i.i.i.lcssa.ph")),
                                       ("for.body.i.i.i.epil", (Operand.reg "%shr.i.i.i.epil"))],
          Instr.icmp "%tobool.not31.i.i.i" (IPred.eq) 128 (Operand.reg "%carry.0.lcssa.i.i.i") (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))], Term.condbr (Operand.reg "%tobool.not31.i.i.i") "for.inc143.i.i" "while.body.us.i.i.i"⟩ := by decide

theorem numFast_findBlock_while_body_us_i_i_i :
    numFastBody.findBlock "while.body.us.i.i.i" = some ⟨"while.body.us.i.i.i", [
          Instr.trunc "%conv9.us.i.i.i" 128 64 (Operand.reg "%carry.0.lcssa.i.i.i"),
          Instr.binop "%inc12.us.i.i.i" (BinOp.add) 32 (Operand.reg "%70") (Operand.imm (Const.int 32 0x00000001#32)),
          Instr.sext "%idxprom13.us.i.i.i" 32 64 (Operand.reg "%70"),
          Instr.gep "%arrayidx14.us.i.i.i" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%idxprom13.us.i.i.i"),
          Instr.store (Ty.int 64) (Operand.reg "%conv9.us.i.i.i") (Operand.reg "%arrayidx14.us.i.i.i")], Term.br "for.inc143.i.i"⟩ := by decide

theorem numFast_findBlock_for_body_i_i_i :
    numFastBody.findBlock "for.body.i.i.i" = some ⟨"for.body.i.i.i", [
          Instr.phi "%indvars.iv.i.i.i" (Ty.int 64) [("for.body.lr.ph.i.i.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i.i.i", (Operand.reg "%indvars.iv.next.i.i.i.3"))],
          Instr.phi "%carry.029.i.i.i" (Ty.int 128) [("for.body.lr.ph.i.i.i.new", (Operand.reg "%conv.i.i.i")),
                                       ("for.body.i.i.i", (Operand.reg "%shr.i.i.i.3"))],
          Instr.phi "%niter1048" (Ty.int 64) [("for.body.lr.ph.i.i.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i.i.i", (Operand.reg "%niter1048.next.3"))],
          Instr.gep "%arrayidx.i.i.i" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.i.i.i"),
          Instr.load "%74" (Ty.int 64) (Operand.reg "%arrayidx.i.i.i"),
          Instr.zext "%conv2.i.i.i" 64 128 (Operand.reg "%74"),
          Instr.binop "%mul.i.i.i" (BinOp.mul) 128 (Operand.reg "%conv2.i.i.i") (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
          Instr.binop "%add4.i.i.i" (BinOp.add) 128 (Operand.reg "%mul.i.i.i") (Operand.reg "%carry.029.i.i.i"),
          Instr.trunc "%conv5.i.i.i" 128 64 (Operand.reg "%add4.i.i.i"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i.i") (Operand.reg "%arrayidx.i.i.i"),
          Instr.binop "%shr.i.i.i" (BinOp.lshr) 128 (Operand.reg "%add4.i.i.i") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i.i.i" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.gep "%arrayidx.i.i.i.1" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.next.i.i.i"),
          Instr.load "%75" (Ty.int 64) (Operand.reg "%arrayidx.i.i.i.1"),
          Instr.zext "%conv2.i.i.i.1" 64 128 (Operand.reg "%75"),
          Instr.binop "%mul.i.i.i.1" (BinOp.mul) 128 (Operand.reg "%conv2.i.i.i.1") (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
          Instr.binop "%add4.i.i.i.1" (BinOp.add) 128 (Operand.reg "%mul.i.i.i.1") (Operand.reg "%shr.i.i.i"),
          Instr.trunc "%conv5.i.i.i.1" 128 64 (Operand.reg "%add4.i.i.i.1"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i.i.1") (Operand.reg "%arrayidx.i.i.i.1"),
          Instr.binop "%shr.i.i.i.1" (BinOp.lshr) 128 (Operand.reg "%add4.i.i.i.1") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i.i.i.1" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i.i") (Operand.imm (Const.int 64 0x0000000000000002#64)),
          Instr.gep "%arrayidx.i.i.i.2" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.next.i.i.i.1"),
          Instr.load "%76" (Ty.int 64) (Operand.reg "%arrayidx.i.i.i.2"),
          Instr.zext "%conv2.i.i.i.2" 64 128 (Operand.reg "%76"),
          Instr.binop "%mul.i.i.i.2" (BinOp.mul) 128 (Operand.reg "%conv2.i.i.i.2") (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
          Instr.binop "%add4.i.i.i.2" (BinOp.add) 128 (Operand.reg "%mul.i.i.i.2") (Operand.reg "%shr.i.i.i.1"),
          Instr.trunc "%conv5.i.i.i.2" 128 64 (Operand.reg "%add4.i.i.i.2"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i.i.2") (Operand.reg "%arrayidx.i.i.i.2"),
          Instr.binop "%shr.i.i.i.2" (BinOp.lshr) 128 (Operand.reg "%add4.i.i.i.2") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i.i.i.2" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
          Instr.gep "%arrayidx.i.i.i.3" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.next.i.i.i.2"),
          Instr.load "%77" (Ty.int 64) (Operand.reg "%arrayidx.i.i.i.3"),
          Instr.zext "%conv2.i.i.i.3" 64 128 (Operand.reg "%77"),
          Instr.binop "%mul.i.i.i.3" (BinOp.mul) 128 (Operand.reg "%conv2.i.i.i.3") (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
          Instr.binop "%add4.i.i.i.3" (BinOp.add) 128 (Operand.reg "%mul.i.i.i.3") (Operand.reg "%shr.i.i.i.2"),
          Instr.trunc "%conv5.i.i.i.3" 128 64 (Operand.reg "%add4.i.i.i.3"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i.i.3") (Operand.reg "%arrayidx.i.i.i.3"),
          Instr.binop "%shr.i.i.i.3" (BinOp.lshr) 128 (Operand.reg "%add4.i.i.i.3") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i.i.i.3" (BinOp.add) 64 (Operand.reg "%indvars.iv.i.i.i") (Operand.imm (Const.int 64 0x0000000000000004#64)),
          Instr.binop "%niter1048.next.3" (BinOp.add) 64 (Operand.reg "%niter1048") (Operand.imm (Const.int 64 0x0000000000000004#64)),
          Instr.icmp "%niter1048.ncmp.3" (IPred.eq) 64 (Operand.reg "%niter1048.next.3") (Operand.reg "%unroll_iter1047")], Term.condbr (Operand.reg "%niter1048.ncmp.3") "while.cond.preheader.i.i.i.loopexit.unr-lcssa" "for.body.i.i.i"⟩ := by decide

theorem numFast_findBlock_for_inc143_i_i :
    numFastBody.findBlock "for.inc143.i.i" = some ⟨"for.inc143.i.i", [
          Instr.phi "%78" (Ty.int 32) [("for.body132.i.i", (Operand.reg "%70")),
                                       ("while.cond.preheader.i.i.i", (Operand.reg "%70")),
                                       ("while.body.us.i.i.i", (Operand.reg "%inc12.us.i.i.i"))],
          Instr.phi "%chunk.1.i.i" (Ty.int 64) [("for.body132.i.i", (Operand.reg "%add136.i.i")),
                                       ("while.cond.preheader.i.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("while.body.us.i.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
          Instr.phi "%cn.1.i.i" (Ty.int 32) [("for.body132.i.i", (Operand.reg "%inc137.i.i")),
                                       ("while.cond.preheader.i.i.i", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("while.body.us.i.i.i", (Operand.imm (Const.int 32 0x00000000#32)))],
          Instr.binop "%inc144.i.i" (BinOp.add) 64 (Operand.reg "%j.0740.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.icmp "%exitcond780.not.i.i" (IPred.eq) 64 (Operand.reg "%inc144.i.i") (Operand.reg "%R.0701.i.i")], Term.condbr (Operand.reg "%exitcond780.not.i.i") "for.cond.cleanup.i.i" "for.body132.i.i"⟩ := by decide

theorem numFast_findBlock_if_then148_i_i :
    numFastBody.findBlock "if.then148.i.i" = some ⟨"if.then148.i.i", [
          Instr.zext "%conv.i514.i.i" 64 128 (Operand.reg "%chunk.1.i.i"),
          Instr.icmp "%cmp28.i516.i.i" (IPred.sgt) 32 (Operand.reg "%78") (Operand.imm (Const.int 32 0x00000000#32))], Term.condbr (Operand.reg "%cmp28.i516.i.i") "for.body.lr.ph.i525.i.i" "while.cond.preheader.i517.i.i"⟩ := by decide

theorem numFast_findBlock_for_body_lr_ph_i525_i_i :
    numFastBody.findBlock "for.body.lr.ph.i525.i.i" = some ⟨"for.body.lr.ph.i525.i.i", [
          Instr.sext "%idxprom.i.i" 32 64 (Operand.reg "%cn.1.i.i"),
          Instr.gep "%arrayidx150.i.i" (Ty.int 64) (Operand.global "@NUMF_EL1_P10") (Operand.reg "%idxprom.i.i"),
          Instr.load "%79" (Ty.int 64) (Operand.reg "%arrayidx150.i.i"),
          Instr.zext "%conv3.i.i.i" 64 128 (Operand.reg "%79"),
          Instr.zext "%wide.trip.count.i526.i.i" 32 64 (Operand.reg "%78"),
          Instr.binop "%xtraiter1049" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i526.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
          Instr.icmp "%80" (IPred.ult) 32 (Operand.reg "%78") (Operand.imm (Const.int 32 0x00000004#32))], Term.condbr (Operand.reg "%80") "while.cond.preheader.i517.i.i.loopexit.unr-lcssa" "for.body.lr.ph.i525.i.i.new"⟩ := by decide

theorem numFast_findBlock_for_body_lr_ph_i525_i_i_new :
    numFastBody.findBlock "for.body.lr.ph.i525.i.i.new" = some ⟨"for.body.lr.ph.i525.i.i.new", [
          Instr.binop "%unroll_iter1053" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i526.i.i") (Operand.imm (Const.int 64 0x000000007ffffffc#64))], Term.br "for.body.i527.i.i"⟩ := by decide

theorem numFast_findBlock_while_cond_preheader_i517_i_i_loopexit_unr_lcssa :
    numFastBody.findBlock "while.cond.preheader.i517.i.i.loopexit.unr-lcssa" = some ⟨"while.cond.preheader.i517.i.i.loopexit.unr-lcssa", [
          Instr.phi "%shr.i535.i.i.lcssa.ph" (Ty.int 128) [("for.body.lr.ph.i525.i.i", (Operand.imm Const.poison)),
                                       ("for.body.i527.i.i", (Operand.reg "%shr.i535.i.i.3"))],
          Instr.phi "%indvars.iv.i528.i.i.unr" (Ty.int 64) [("for.body.lr.ph.i525.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i527.i.i", (Operand.reg "%indvars.iv.next.i536.i.i.3"))],
          Instr.phi "%carry.029.i529.i.i.unr" (Ty.int 128) [("for.body.lr.ph.i525.i.i", (Operand.reg "%conv.i514.i.i")),
                                       ("for.body.i527.i.i", (Operand.reg "%shr.i535.i.i.3"))],
          Instr.icmp "%lcmp.mod1051.not" (IPred.eq) 64 (Operand.reg "%xtraiter1049") (Operand.imm (Const.int 64 0x0000000000000000#64))], Term.condbr (Operand.reg "%lcmp.mod1051.not") "while.cond.preheader.i517.i.i" "for.body.i527.i.i.epil"⟩ := by decide

theorem numFast_findBlock_for_body_i527_i_i_epil :
    numFastBody.findBlock "for.body.i527.i.i.epil" = some ⟨"for.body.i527.i.i.epil", [
          Instr.phi "%indvars.iv.i528.i.i.epil" (Ty.int 64) [("for.body.i527.i.i.epil", (Operand.reg "%indvars.iv.next.i536.i.i.epil")),
                                       ("while.cond.preheader.i517.i.i.loopexit.unr-lcssa", (Operand.reg "%indvars.iv.i528.i.i.unr"))],
          Instr.phi "%carry.029.i529.i.i.epil" (Ty.int 128) [("for.body.i527.i.i.epil", (Operand.reg "%shr.i535.i.i.epil")),
                                       ("while.cond.preheader.i517.i.i.loopexit.unr-lcssa", (Operand.reg "%carry.029.i529.i.i.unr"))],
          Instr.phi "%epil.iter1050" (Ty.int 64) [("for.body.i527.i.i.epil", (Operand.reg "%epil.iter1050.next")),
                                       ("while.cond.preheader.i517.i.i.loopexit.unr-lcssa", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
          Instr.gep "%arrayidx.i530.i.i.epil" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.i528.i.i.epil"),
          Instr.load "%81" (Ty.int 64) (Operand.reg "%arrayidx.i530.i.i.epil"),
          Instr.zext "%conv2.i531.i.i.epil" 64 128 (Operand.reg "%81"),
          Instr.binop "%mul.i532.i.i.epil" (BinOp.mul) 128 (Operand.reg "%conv2.i531.i.i.epil") (Operand.reg "%conv3.i.i.i"),
          Instr.binop "%add4.i533.i.i.epil" (BinOp.add) 128 (Operand.reg "%mul.i532.i.i.epil") (Operand.reg "%carry.029.i529.i.i.epil"),
          Instr.trunc "%conv5.i534.i.i.epil" 128 64 (Operand.reg "%add4.i533.i.i.epil"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i534.i.i.epil") (Operand.reg "%arrayidx.i530.i.i.epil"),
          Instr.binop "%shr.i535.i.i.epil" (BinOp.lshr) 128 (Operand.reg "%add4.i533.i.i.epil") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i536.i.i.epil" (BinOp.add) 64 (Operand.reg "%indvars.iv.i528.i.i.epil") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.binop "%epil.iter1050.next" (BinOp.add) 64 (Operand.reg "%epil.iter1050") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.icmp "%epil.iter1050.cmp.not" (IPred.eq) 64 (Operand.reg "%epil.iter1050.next") (Operand.reg "%xtraiter1049")], Term.condbr (Operand.reg "%epil.iter1050.cmp.not") "while.cond.preheader.i517.i.i" "for.body.i527.i.i.epil"⟩ := by decide

theorem numFast_findBlock_while_cond_preheader_i517_i_i :
    numFastBody.findBlock "while.cond.preheader.i517.i.i" = some ⟨"while.cond.preheader.i517.i.i", [
          Instr.phi "%carry.0.lcssa.i518.i.i" (Ty.int 128) [("if.then148.i.i", (Operand.reg "%conv.i514.i.i")),
                                       ("while.cond.preheader.i517.i.i.loopexit.unr-lcssa", (Operand.reg "%shr.i535.i.i.lcssa.ph")),
                                       ("for.body.i527.i.i.epil", (Operand.reg "%shr.i535.i.i.epil"))],
          Instr.icmp "%tobool.not31.i519.i.i" (IPred.eq) 128 (Operand.reg "%carry.0.lcssa.i518.i.i") (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))], Term.condbr (Operand.reg "%tobool.not31.i519.i.i") "if.end151.i.i" "while.body.us.i520.i.i"⟩ := by decide

theorem numFast_findBlock_while_body_us_i520_i_i :
    numFastBody.findBlock "while.body.us.i520.i.i" = some ⟨"while.body.us.i520.i.i", [
          Instr.trunc "%conv9.us.i521.i.i" 128 64 (Operand.reg "%carry.0.lcssa.i518.i.i"),
          Instr.binop "%inc12.us.i522.i.i" (BinOp.add) 32 (Operand.reg "%78") (Operand.imm (Const.int 32 0x00000001#32)),
          Instr.sext "%idxprom13.us.i523.i.i" 32 64 (Operand.reg "%78"),
          Instr.gep "%arrayidx14.us.i524.i.i" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%idxprom13.us.i523.i.i"),
          Instr.store (Ty.int 64) (Operand.reg "%conv9.us.i521.i.i") (Operand.reg "%arrayidx14.us.i524.i.i")], Term.br "if.end151.i.i.sink.split"⟩ := by decide

theorem numFast_findBlock_for_body_i527_i_i :
    numFastBody.findBlock "for.body.i527.i.i" = some ⟨"for.body.i527.i.i", [
          Instr.phi "%indvars.iv.i528.i.i" (Ty.int 64) [("for.body.lr.ph.i525.i.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i527.i.i", (Operand.reg "%indvars.iv.next.i536.i.i.3"))],
          Instr.phi "%carry.029.i529.i.i" (Ty.int 128) [("for.body.lr.ph.i525.i.i.new", (Operand.reg "%conv.i514.i.i")),
                                       ("for.body.i527.i.i", (Operand.reg "%shr.i535.i.i.3"))],
          Instr.phi "%niter1054" (Ty.int 64) [("for.body.lr.ph.i525.i.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i527.i.i", (Operand.reg "%niter1054.next.3"))],
          Instr.gep "%arrayidx.i530.i.i" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.i528.i.i"),
          Instr.load "%82" (Ty.int 64) (Operand.reg "%arrayidx.i530.i.i"),
          Instr.zext "%conv2.i531.i.i" 64 128 (Operand.reg "%82"),
          Instr.binop "%mul.i532.i.i" (BinOp.mul) 128 (Operand.reg "%conv2.i531.i.i") (Operand.reg "%conv3.i.i.i"),
          Instr.binop "%add4.i533.i.i" (BinOp.add) 128 (Operand.reg "%mul.i532.i.i") (Operand.reg "%carry.029.i529.i.i"),
          Instr.trunc "%conv5.i534.i.i" 128 64 (Operand.reg "%add4.i533.i.i"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i534.i.i") (Operand.reg "%arrayidx.i530.i.i"),
          Instr.binop "%shr.i535.i.i" (BinOp.lshr) 128 (Operand.reg "%add4.i533.i.i") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i536.i.i" (BinOp.or) 64 (Operand.reg "%indvars.iv.i528.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.gep "%arrayidx.i530.i.i.1" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.next.i536.i.i"),
          Instr.load "%83" (Ty.int 64) (Operand.reg "%arrayidx.i530.i.i.1"),
          Instr.zext "%conv2.i531.i.i.1" 64 128 (Operand.reg "%83"),
          Instr.binop "%mul.i532.i.i.1" (BinOp.mul) 128 (Operand.reg "%conv2.i531.i.i.1") (Operand.reg "%conv3.i.i.i"),
          Instr.binop "%add4.i533.i.i.1" (BinOp.add) 128 (Operand.reg "%mul.i532.i.i.1") (Operand.reg "%shr.i535.i.i"),
          Instr.trunc "%conv5.i534.i.i.1" 128 64 (Operand.reg "%add4.i533.i.i.1"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i534.i.i.1") (Operand.reg "%arrayidx.i530.i.i.1"),
          Instr.binop "%shr.i535.i.i.1" (BinOp.lshr) 128 (Operand.reg "%add4.i533.i.i.1") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i536.i.i.1" (BinOp.or) 64 (Operand.reg "%indvars.iv.i528.i.i") (Operand.imm (Const.int 64 0x0000000000000002#64)),
          Instr.gep "%arrayidx.i530.i.i.2" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.next.i536.i.i.1"),
          Instr.load "%84" (Ty.int 64) (Operand.reg "%arrayidx.i530.i.i.2"),
          Instr.zext "%conv2.i531.i.i.2" 64 128 (Operand.reg "%84"),
          Instr.binop "%mul.i532.i.i.2" (BinOp.mul) 128 (Operand.reg "%conv2.i531.i.i.2") (Operand.reg "%conv3.i.i.i"),
          Instr.binop "%add4.i533.i.i.2" (BinOp.add) 128 (Operand.reg "%mul.i532.i.i.2") (Operand.reg "%shr.i535.i.i.1"),
          Instr.trunc "%conv5.i534.i.i.2" 128 64 (Operand.reg "%add4.i533.i.i.2"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i534.i.i.2") (Operand.reg "%arrayidx.i530.i.i.2"),
          Instr.binop "%shr.i535.i.i.2" (BinOp.lshr) 128 (Operand.reg "%add4.i533.i.i.2") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i536.i.i.2" (BinOp.or) 64 (Operand.reg "%indvars.iv.i528.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
          Instr.gep "%arrayidx.i530.i.i.3" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.next.i536.i.i.2"),
          Instr.load "%85" (Ty.int 64) (Operand.reg "%arrayidx.i530.i.i.3"),
          Instr.zext "%conv2.i531.i.i.3" 64 128 (Operand.reg "%85"),
          Instr.binop "%mul.i532.i.i.3" (BinOp.mul) 128 (Operand.reg "%conv2.i531.i.i.3") (Operand.reg "%conv3.i.i.i"),
          Instr.binop "%add4.i533.i.i.3" (BinOp.add) 128 (Operand.reg "%mul.i532.i.i.3") (Operand.reg "%shr.i535.i.i.2"),
          Instr.trunc "%conv5.i534.i.i.3" 128 64 (Operand.reg "%add4.i533.i.i.3"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i534.i.i.3") (Operand.reg "%arrayidx.i530.i.i.3"),
          Instr.binop "%shr.i535.i.i.3" (BinOp.lshr) 128 (Operand.reg "%add4.i533.i.i.3") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i536.i.i.3" (BinOp.add) 64 (Operand.reg "%indvars.iv.i528.i.i") (Operand.imm (Const.int 64 0x0000000000000004#64)),
          Instr.binop "%niter1054.next.3" (BinOp.add) 64 (Operand.reg "%niter1054") (Operand.imm (Const.int 64 0x0000000000000004#64)),
          Instr.icmp "%niter1054.ncmp.3" (IPred.eq) 64 (Operand.reg "%niter1054.next.3") (Operand.reg "%unroll_iter1053")], Term.condbr (Operand.reg "%niter1054.ncmp.3") "while.cond.preheader.i517.i.i.loopexit.unr-lcssa" "for.body.i527.i.i"⟩ := by decide

theorem numFast_findBlock_if_end151_i_i_sink_split :
    numFastBody.findBlock "if.end151.i.i.sink.split" = some ⟨"if.end151.i.i.sink.split", [
          Instr.phi "%inc12.us.i522.i.i.sink" (Ty.int 32) [("while.body.us.i520.i.i", (Operand.reg "%inc12.us.i522.i.i")),
                                       ("if.end126.i.i", (Operand.imm (Const.int 32 0x00000000#32)))],
          Instr.store (Ty.int 32) (Operand.reg "%inc12.us.i522.i.i.sink") (Operand.reg "%n.i.i.i")], Term.br "if.end151.i.i"⟩ := by decide

theorem numFast_findBlock_if_end151_i_i :
    numFastBody.findBlock "if.end151.i.i" = some ⟨"if.end151.i.i", [
          Instr.gep "%pow.i.i" (Ty.int 8) (Operand.reg "%v.i.i") (Operand.imm (Const.int 64 0x0000000000000308#64)),
          Instr.store (Ty.int 64) (Operand.imm (Const.int 64 0x0000000000000001#64)) (Operand.reg "%pow.i.i"),
          Instr.gep "%n.i539.i.i" (Ty.int 8) (Operand.reg "%v.i.i") (Operand.imm (Const.int 64 0x0000000000000608#64)),
          Instr.store (Ty.int 32) (Operand.imm (Const.int 32 0x00000001#32)) (Operand.reg "%n.i539.i.i"),
          Instr.icmp "%tobool152.not.i.i" (IPred.eq) 32 (Operand.reg "%sticky.0714.i.i") (Operand.imm (Const.int 32 0x00000000#32))], Term.condbr (Operand.reg "%tobool152.not.i.i") "if.else164.i.i" "if.then153.i.i"⟩ := by decide

theorem numFast_findBlock_if_then153_i_i :
    numFastBody.findBlock "if.then153.i.i" = some ⟨"if.then153.i.i", [
          Instr.binop "%sub154.i.i" (BinOp.sub) 64 (Operand.imm (Const.int 64 0x0000000000000000#64)) (Operand.reg "%add108.i.i"),
          Instr.icmp "%cmp155746.i.i" (IPred.sgt) 64 (Operand.reg "%sub154.i.i") (Operand.imm (Const.int 64 0x000000000000001a#64))], Term.condbr (Operand.reg "%cmp155746.i.i") "while.body.i.i" "while.end.thread.i.i"⟩ := by decide

theorem numFast_findBlock_while_body_i_i :
    numFastBody.findBlock "while.body.i.i" = some ⟨"while.body.i.i", [
          Instr.phi "%k.0748.i.i" (Ty.int 64) [("stk_mul_u64.exit.i.i", (Operand.reg "%sub158.i.i")),
                                       ("if.then153.i.i", (Operand.reg "%sub154.i.i"))],
          Instr.phi "%inc12.us.i.i745747.i.i" (Ty.int 32) [("stk_mul_u64.exit.i.i", (Operand.reg "%inc12.us.i.i744.i.i")),
                                       ("if.then153.i.i", (Operand.imm (Const.int 32 0x00000001#32)))],
          Instr.icmp "%cmp28.i.i.i.i" (IPred.sgt) 32 (Operand.reg "%inc12.us.i.i745747.i.i") (Operand.imm (Const.int 32 0x00000000#32))], Term.condbr (Operand.reg "%cmp28.i.i.i.i") "for.body.lr.ph.i.i.i.i" "stk_mul_u64.exit.i.i"⟩ := by decide

theorem numFast_findBlock_for_body_lr_ph_i_i_i_i :
    numFastBody.findBlock "for.body.lr.ph.i.i.i.i" = some ⟨"for.body.lr.ph.i.i.i.i", [
          Instr.zext "%wide.trip.count.i.i.i.i" 32 64 (Operand.reg "%inc12.us.i.i745747.i.i"),
          Instr.binop "%xtraiter1055" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i.i.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
          Instr.icmp "%86" (IPred.ult) 32 (Operand.reg "%inc12.us.i.i745747.i.i") (Operand.imm (Const.int 32 0x00000004#32))], Term.condbr (Operand.reg "%86") "while.cond.preheader.i.i.i.i.unr-lcssa" "for.body.lr.ph.i.i.i.i.new"⟩ := by decide

theorem numFast_findBlock_for_body_lr_ph_i_i_i_i_new :
    numFastBody.findBlock "for.body.lr.ph.i.i.i.i.new" = some ⟨"for.body.lr.ph.i.i.i.i.new", [
          Instr.binop "%unroll_iter1060" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i.i.i.i") (Operand.imm (Const.int 64 0x000000007ffffffc#64))], Term.br "for.body.i.i.i.i"⟩ := by decide

theorem numFast_findBlock_while_cond_preheader_i_i_i_i_unr_lcssa_loopexit :
    numFastBody.findBlock "while.cond.preheader.i.i.i.i.unr-lcssa.loopexit" = some ⟨"while.cond.preheader.i.i.i.i.unr-lcssa.loopexit", [
          Instr.trunc "%extract.t1091" 128 64 (Operand.reg "%shr.i.i.i.i.3")], Term.br "while.cond.preheader.i.i.i.i.unr-lcssa"⟩ := by decide

theorem numFast_findBlock_while_cond_preheader_i_i_i_i_unr_lcssa :
    numFastBody.findBlock "while.cond.preheader.i.i.i.i.unr-lcssa" = some ⟨"while.cond.preheader.i.i.i.i.unr-lcssa", [
          Instr.phi "%add4.i.i.i.i.lcssa.ph" (Ty.int 128) [("for.body.lr.ph.i.i.i.i", (Operand.imm Const.poison)),
                                       ("while.cond.preheader.i.i.i.i.unr-lcssa.loopexit", (Operand.reg "%add4.i.i.i.i.3"))],
          Instr.phi "%shr.i.i.i.i.lcssa.ph.off0" (Ty.int 64) [("for.body.lr.ph.i.i.i.i", (Operand.imm Const.poison)),
                                       ("while.cond.preheader.i.i.i.i.unr-lcssa.loopexit", (Operand.reg "%extract.t1091"))],
          Instr.phi "%indvars.iv.i.i.i.i.unr" (Ty.int 64) [("for.body.lr.ph.i.i.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("while.cond.preheader.i.i.i.i.unr-lcssa.loopexit", (Operand.reg "%indvars.iv.next.i.i.i.i.3"))],
          Instr.phi "%carry.029.i.i.i.i.unr" (Ty.int 128) [("for.body.lr.ph.i.i.i.i", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
                                       ("while.cond.preheader.i.i.i.i.unr-lcssa.loopexit", (Operand.reg "%shr.i.i.i.i.3"))],
          Instr.icmp "%lcmp.mod1057.not" (IPred.eq) 64 (Operand.reg "%xtraiter1055") (Operand.imm (Const.int 64 0x0000000000000000#64))], Term.condbr (Operand.reg "%lcmp.mod1057.not") "while.cond.preheader.i.i.i.i" "for.body.i.i.i.i.epil"⟩ := by decide

theorem numFast_findBlock_for_body_i_i_i_i_epil :
    numFastBody.findBlock "for.body.i.i.i.i.epil" = some ⟨"for.body.i.i.i.i.epil", [
          Instr.phi "%indvars.iv.i.i.i.i.epil" (Ty.int 64) [("for.body.i.i.i.i.epil", (Operand.reg "%indvars.iv.next.i.i.i.i.epil")),
                                       ("while.cond.preheader.i.i.i.i.unr-lcssa", (Operand.reg "%indvars.iv.i.i.i.i.unr"))],
          Instr.phi "%carry.029.i.i.i.i.epil" (Ty.int 128) [("for.body.i.i.i.i.epil", (Operand.reg "%shr.i.i.i.i.epil")),
                                       ("while.cond.preheader.i.i.i.i.unr-lcssa", (Operand.reg "%carry.029.i.i.i.i.unr"))],
          Instr.phi "%epil.iter1056" (Ty.int 64) [("for.body.i.i.i.i.epil", (Operand.reg "%epil.iter1056.next")),
                                       ("while.cond.preheader.i.i.i.i.unr-lcssa", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
          Instr.gep "%arrayidx.i.i.i.i.epil" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%indvars.iv.i.i.i.i.epil"),
          Instr.load "%87" (Ty.int 64) (Operand.reg "%arrayidx.i.i.i.i.epil"),
          Instr.zext "%conv2.i.i.i.i.epil" 64 128 (Operand.reg "%87"),
          Instr.binop "%mul.i.i.i.i.epil" (BinOp.mul) 128 (Operand.reg "%conv2.i.i.i.i.epil") (Operand.imm (Const.int 128 0x00000000000000006765c793fa10079d#128)),
          Instr.binop "%add4.i.i.i.i.epil" (BinOp.add) 128 (Operand.reg "%mul.i.i.i.i.epil") (Operand.reg "%carry.029.i.i.i.i.epil"),
          Instr.trunc "%conv5.i.i.i.i.epil" 128 64 (Operand.reg "%add4.i.i.i.i.epil"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i.i.i.epil") (Operand.reg "%arrayidx.i.i.i.i.epil"),
          Instr.binop "%shr.i.i.i.i.epil" (BinOp.lshr) 128 (Operand.reg "%add4.i.i.i.i.epil") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i.i.i.i.epil" (BinOp.add) 64 (Operand.reg "%indvars.iv.i.i.i.i.epil") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.binop "%epil.iter1056.next" (BinOp.add) 64 (Operand.reg "%epil.iter1056") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.icmp "%epil.iter1056.cmp.not" (IPred.eq) 64 (Operand.reg "%epil.iter1056.next") (Operand.reg "%xtraiter1055")], Term.condbr (Operand.reg "%epil.iter1056.cmp.not") "while.cond.preheader.i.i.i.i.epilog-lcssa" "for.body.i.i.i.i.epil"⟩ := by decide

theorem numFast_findBlock_while_cond_preheader_i_i_i_i_epilog_lcssa :
    numFastBody.findBlock "while.cond.preheader.i.i.i.i.epilog-lcssa" = some ⟨"while.cond.preheader.i.i.i.i.epilog-lcssa", [
          Instr.trunc "%extract.t1090" 128 64 (Operand.reg "%shr.i.i.i.i.epil")], Term.br "while.cond.preheader.i.i.i.i"⟩ := by decide

theorem numFast_findBlock_while_cond_preheader_i_i_i_i :
    numFastBody.findBlock "while.cond.preheader.i.i.i.i" = some ⟨"while.cond.preheader.i.i.i.i", [
          Instr.phi "%add4.i.i.i.i.lcssa" (Ty.int 128) [("while.cond.preheader.i.i.i.i.unr-lcssa", (Operand.reg "%add4.i.i.i.i.lcssa.ph")),
                                       ("while.cond.preheader.i.i.i.i.epilog-lcssa", (Operand.reg "%add4.i.i.i.i.epil"))],
          Instr.phi "%shr.i.i.i.i.lcssa.off0" (Ty.int 64) [("while.cond.preheader.i.i.i.i.unr-lcssa", (Operand.reg "%shr.i.i.i.i.lcssa.ph.off0")),
                                       ("while.cond.preheader.i.i.i.i.epilog-lcssa", (Operand.reg "%extract.t1090"))],
          Instr.icmp "%tobool.not31.i.i.i.i" (IPred.ult) 128 (Operand.reg "%add4.i.i.i.i.lcssa") (Operand.imm (Const.int 128 0x00000000000000010000000000000000#128))], Term.condbr (Operand.reg "%tobool.not31.i.i.i.i") "stk_mul_u64.exit.i.i" "while.body.us.i.i.i.i"⟩ := by decide

theorem numFast_findBlock_while_body_us_i_i_i_i :
    numFastBody.findBlock "while.body.us.i.i.i.i" = some ⟨"while.body.us.i.i.i.i", [
          Instr.binop "%inc12.us.i.i.i.i" (BinOp.add) 32 (Operand.reg "%inc12.us.i.i745747.i.i") (Operand.imm (Const.int 32 0x00000001#32)),
          Instr.gep "%arrayidx14.us.i.i.i.i" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%wide.trip.count.i.i.i.i"),
          Instr.store (Ty.int 64) (Operand.reg "%shr.i.i.i.i.lcssa.off0") (Operand.reg "%arrayidx14.us.i.i.i.i")], Term.br "stk_mul_u64.exit.i.i"⟩ := by decide

theorem numFast_findBlock_for_body_i_i_i_i :
    numFastBody.findBlock "for.body.i.i.i.i" = some ⟨"for.body.i.i.i.i", [
          Instr.phi "%indvars.iv.i.i.i.i" (Ty.int 64) [("for.body.lr.ph.i.i.i.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i.i.i.i", (Operand.reg "%indvars.iv.next.i.i.i.i.3"))],
          Instr.phi "%carry.029.i.i.i.i" (Ty.int 128) [("for.body.lr.ph.i.i.i.i.new", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
                                       ("for.body.i.i.i.i", (Operand.reg "%shr.i.i.i.i.3"))],
          Instr.phi "%niter1061" (Ty.int 64) [("for.body.lr.ph.i.i.i.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i.i.i.i", (Operand.reg "%niter1061.next.3"))],
          Instr.gep "%arrayidx.i.i.i.i" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%indvars.iv.i.i.i.i"),
          Instr.load "%88" (Ty.int 64) (Operand.reg "%arrayidx.i.i.i.i"),
          Instr.zext "%conv2.i.i.i.i" 64 128 (Operand.reg "%88"),
          Instr.binop "%mul.i.i.i.i" (BinOp.mul) 128 (Operand.reg "%conv2.i.i.i.i") (Operand.imm (Const.int 128 0x00000000000000006765c793fa10079d#128)),
          Instr.binop "%add4.i.i.i.i" (BinOp.add) 128 (Operand.reg "%mul.i.i.i.i") (Operand.reg "%carry.029.i.i.i.i"),
          Instr.trunc "%conv5.i.i.i.i" 128 64 (Operand.reg "%add4.i.i.i.i"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i.i.i") (Operand.reg "%arrayidx.i.i.i.i"),
          Instr.binop "%shr.i.i.i.i" (BinOp.lshr) 128 (Operand.reg "%add4.i.i.i.i") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i.i.i.i" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.gep "%arrayidx.i.i.i.i.1" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%indvars.iv.next.i.i.i.i"),
          Instr.load "%89" (Ty.int 64) (Operand.reg "%arrayidx.i.i.i.i.1"),
          Instr.zext "%conv2.i.i.i.i.1" 64 128 (Operand.reg "%89"),
          Instr.binop "%mul.i.i.i.i.1" (BinOp.mul) 128 (Operand.reg "%conv2.i.i.i.i.1") (Operand.imm (Const.int 128 0x00000000000000006765c793fa10079d#128)),
          Instr.binop "%add4.i.i.i.i.1" (BinOp.add) 128 (Operand.reg "%mul.i.i.i.i.1") (Operand.reg "%shr.i.i.i.i"),
          Instr.trunc "%conv5.i.i.i.i.1" 128 64 (Operand.reg "%add4.i.i.i.i.1"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i.i.i.1") (Operand.reg "%arrayidx.i.i.i.i.1"),
          Instr.binop "%shr.i.i.i.i.1" (BinOp.lshr) 128 (Operand.reg "%add4.i.i.i.i.1") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i.i.i.i.1" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i.i.i") (Operand.imm (Const.int 64 0x0000000000000002#64)),
          Instr.gep "%arrayidx.i.i.i.i.2" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%indvars.iv.next.i.i.i.i.1"),
          Instr.load "%90" (Ty.int 64) (Operand.reg "%arrayidx.i.i.i.i.2"),
          Instr.zext "%conv2.i.i.i.i.2" 64 128 (Operand.reg "%90"),
          Instr.binop "%mul.i.i.i.i.2" (BinOp.mul) 128 (Operand.reg "%conv2.i.i.i.i.2") (Operand.imm (Const.int 128 0x00000000000000006765c793fa10079d#128)),
          Instr.binop "%add4.i.i.i.i.2" (BinOp.add) 128 (Operand.reg "%mul.i.i.i.i.2") (Operand.reg "%shr.i.i.i.i.1"),
          Instr.trunc "%conv5.i.i.i.i.2" 128 64 (Operand.reg "%add4.i.i.i.i.2"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i.i.i.2") (Operand.reg "%arrayidx.i.i.i.i.2"),
          Instr.binop "%shr.i.i.i.i.2" (BinOp.lshr) 128 (Operand.reg "%add4.i.i.i.i.2") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i.i.i.i.2" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
          Instr.gep "%arrayidx.i.i.i.i.3" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%indvars.iv.next.i.i.i.i.2"),
          Instr.load "%91" (Ty.int 64) (Operand.reg "%arrayidx.i.i.i.i.3"),
          Instr.zext "%conv2.i.i.i.i.3" 64 128 (Operand.reg "%91"),
          Instr.binop "%mul.i.i.i.i.3" (BinOp.mul) 128 (Operand.reg "%conv2.i.i.i.i.3") (Operand.imm (Const.int 128 0x00000000000000006765c793fa10079d#128)),
          Instr.binop "%add4.i.i.i.i.3" (BinOp.add) 128 (Operand.reg "%mul.i.i.i.i.3") (Operand.reg "%shr.i.i.i.i.2"),
          Instr.trunc "%conv5.i.i.i.i.3" 128 64 (Operand.reg "%add4.i.i.i.i.3"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i.i.i.3") (Operand.reg "%arrayidx.i.i.i.i.3"),
          Instr.binop "%shr.i.i.i.i.3" (BinOp.lshr) 128 (Operand.reg "%add4.i.i.i.i.3") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i.i.i.i.3" (BinOp.add) 64 (Operand.reg "%indvars.iv.i.i.i.i") (Operand.imm (Const.int 64 0x0000000000000004#64)),
          Instr.binop "%niter1061.next.3" (BinOp.add) 64 (Operand.reg "%niter1061") (Operand.imm (Const.int 64 0x0000000000000004#64)),
          Instr.icmp "%niter1061.ncmp.3" (IPred.eq) 64 (Operand.reg "%niter1061.next.3") (Operand.reg "%unroll_iter1060")], Term.condbr (Operand.reg "%niter1061.ncmp.3") "while.cond.preheader.i.i.i.i.unr-lcssa.loopexit" "for.body.i.i.i.i"⟩ := by decide

theorem numFast_findBlock_stk_mul_u64_exit_i_i :
    numFastBody.findBlock "stk_mul_u64.exit.i.i" = some ⟨"stk_mul_u64.exit.i.i", [
          Instr.phi "%inc12.us.i.i744.i.i" (Ty.int 32) [("while.body.i.i", (Operand.reg "%inc12.us.i.i745747.i.i")),
                                       ("while.cond.preheader.i.i.i.i", (Operand.reg "%inc12.us.i.i745747.i.i")),
                                       ("while.body.us.i.i.i.i", (Operand.reg "%inc12.us.i.i.i.i"))],
          Instr.binop "%sub158.i.i" (BinOp.add) 64 (Operand.reg "%k.0748.i.i") (Operand.imm (Const.int 64 0xffffffffffffffe5#64)),
          Instr.icmp "%cmp155.i.i" (IPred.sgt) 64 (Operand.reg "%k.0748.i.i") (Operand.imm (Const.int 64 0x0000000000000035#64))], Term.condbr (Operand.reg "%cmp155.i.i") "while.body.i.i" "while.end.i.i"⟩ := by decide

theorem numFast_findBlock_while_end_i_i :
    numFastBody.findBlock "while.end.i.i" = some ⟨"while.end.i.i", [
          Instr.store (Ty.int 32) (Operand.reg "%inc12.us.i.i744.i.i") (Operand.reg "%n.i539.i.i"),
          Instr.icmp "%tobool159.not.i.i" (IPred.ne) 64 (Operand.reg "%sub158.i.i") (Operand.imm (Const.int 64 0x0000000000000000#64)),
          Instr.icmp "%cmp28.i.i541.i.i" (IPred.sgt) 32 (Operand.reg "%inc12.us.i.i744.i.i") (Operand.imm (Const.int 32 0x00000000#32)),
          Instr.select "%or.cond864.i.i" (Ty.int 1) (Operand.reg "%tobool159.not.i.i") (Operand.reg "%cmp28.i.i541.i.i") (Operand.imm (Const.int 1 0x0#1))], Term.condbr (Operand.reg "%or.cond864.i.i") "for.body.lr.ph.i.i542.i.i" "if.end198.i.i"⟩ := by decide

theorem numFast_findBlock_while_end_thread_i_i :
    numFastBody.findBlock "while.end.thread.i.i" = some ⟨"while.end.thread.i.i", [
          Instr.store (Ty.int 32) (Operand.imm (Const.int 32 0x00000001#32)) (Operand.reg "%n.i539.i.i"),
          Instr.icmp "%tobool159.not821.i.i" (IPred.eq) 64 (Operand.reg "%add108.i.i") (Operand.imm (Const.int 64 0x0000000000000000#64))], Term.condbr (Operand.reg "%tobool159.not821.i.i") "if.end198.i.i" "for.body.lr.ph.i.i542.i.i"⟩ := by decide

theorem numFast_findBlock_for_body_lr_ph_i_i542_i_i :
    numFastBody.findBlock "for.body.lr.ph.i.i542.i.i" = some ⟨"for.body.lr.ph.i.i542.i.i", [
          Instr.phi "%92" (Ty.int 32) [("while.end.thread.i.i", (Operand.imm (Const.int 32 0x00000001#32))),
                                       ("while.end.i.i", (Operand.reg "%inc12.us.i.i744.i.i"))],
          Instr.phi "%k.0.lcssa822825.i.i" (Ty.int 64) [("while.end.thread.i.i", (Operand.reg "%sub154.i.i")),
                                       ("while.end.i.i", (Operand.reg "%sub158.i.i"))],
          Instr.gep "%arrayidx162.i.i" (Ty.int 64) (Operand.global "@STK_P5") (Operand.reg "%k.0.lcssa822825.i.i"),
          Instr.load "%93" (Ty.int 64) (Operand.reg "%arrayidx162.i.i"),
          Instr.zext "%conv3.i.i.i.i" 64 128 (Operand.reg "%93"),
          Instr.zext "%wide.trip.count.i.i543.i.i" 32 64 (Operand.reg "%92"),
          Instr.binop "%xtraiter1062" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i.i543.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
          Instr.binop "%94" (BinOp.add) 32 (Operand.reg "%92") (Operand.imm (Const.int 32 0xffffffff#32)),
          Instr.icmp "%95" (IPred.ult) 32 (Operand.reg "%94") (Operand.imm (Const.int 32 0x00000003#32))], Term.condbr (Operand.reg "%95") "while.cond.preheader.i.i555.i.i.unr-lcssa" "for.body.lr.ph.i.i542.i.i.new"⟩ := by decide

theorem numFast_findBlock_for_body_lr_ph_i_i542_i_i_new :
    numFastBody.findBlock "for.body.lr.ph.i.i542.i.i.new" = some ⟨"for.body.lr.ph.i.i542.i.i.new", [
          Instr.binop "%unroll_iter1067" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i.i543.i.i") (Operand.imm (Const.int 64 0x000000007ffffffc#64))], Term.br "for.body.i.i544.i.i"⟩ := by decide

theorem numFast_findBlock_while_cond_preheader_i_i555_i_i_unr_lcssa_loopexit :
    numFastBody.findBlock "while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit" = some ⟨"while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit", [
          Instr.trunc "%extract.t1093" 128 64 (Operand.reg "%shr.i.i552.i.i.3")], Term.br "while.cond.preheader.i.i555.i.i.unr-lcssa"⟩ := by decide

theorem numFast_findBlock_while_cond_preheader_i_i555_i_i_unr_lcssa :
    numFastBody.findBlock "while.cond.preheader.i.i555.i.i.unr-lcssa" = some ⟨"while.cond.preheader.i.i555.i.i.unr-lcssa", [
          Instr.phi "%add4.i.i550.i.i.lcssa.ph" (Ty.int 128) [("for.body.lr.ph.i.i542.i.i", (Operand.imm Const.poison)),
                                       ("while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit", (Operand.reg "%add4.i.i550.i.i.3"))],
          Instr.phi "%shr.i.i552.i.i.lcssa.ph.off0" (Ty.int 64) [("for.body.lr.ph.i.i542.i.i", (Operand.imm Const.poison)),
                                       ("while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit", (Operand.reg "%extract.t1093"))],
          Instr.phi "%indvars.iv.i.i545.i.i.unr" (Ty.int 64) [("for.body.lr.ph.i.i542.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit", (Operand.reg "%indvars.iv.next.i.i553.i.i.3"))],
          Instr.phi "%carry.029.i.i546.i.i.unr" (Ty.int 128) [("for.body.lr.ph.i.i542.i.i", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
                                       ("while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit", (Operand.reg "%shr.i.i552.i.i.3"))],
          Instr.icmp "%lcmp.mod1064.not" (IPred.eq) 64 (Operand.reg "%xtraiter1062") (Operand.imm (Const.int 64 0x0000000000000000#64))], Term.condbr (Operand.reg "%lcmp.mod1064.not") "while.cond.preheader.i.i555.i.i" "for.body.i.i544.i.i.epil"⟩ := by decide

theorem numFast_findBlock_for_body_i_i544_i_i_epil :
    numFastBody.findBlock "for.body.i.i544.i.i.epil" = some ⟨"for.body.i.i544.i.i.epil", [
          Instr.phi "%indvars.iv.i.i545.i.i.epil" (Ty.int 64) [("for.body.i.i544.i.i.epil", (Operand.reg "%indvars.iv.next.i.i553.i.i.epil")),
                                       ("while.cond.preheader.i.i555.i.i.unr-lcssa", (Operand.reg "%indvars.iv.i.i545.i.i.unr"))],
          Instr.phi "%carry.029.i.i546.i.i.epil" (Ty.int 128) [("for.body.i.i544.i.i.epil", (Operand.reg "%shr.i.i552.i.i.epil")),
                                       ("while.cond.preheader.i.i555.i.i.unr-lcssa", (Operand.reg "%carry.029.i.i546.i.i.unr"))],
          Instr.phi "%epil.iter1063" (Ty.int 64) [("for.body.i.i544.i.i.epil", (Operand.reg "%epil.iter1063.next")),
                                       ("while.cond.preheader.i.i555.i.i.unr-lcssa", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
          Instr.gep "%arrayidx.i.i547.i.i.epil" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%indvars.iv.i.i545.i.i.epil"),
          Instr.load "%96" (Ty.int 64) (Operand.reg "%arrayidx.i.i547.i.i.epil"),
          Instr.zext "%conv2.i.i548.i.i.epil" 64 128 (Operand.reg "%96"),
          Instr.binop "%mul.i.i549.i.i.epil" (BinOp.mul) 128 (Operand.reg "%conv2.i.i548.i.i.epil") (Operand.reg "%conv3.i.i.i.i"),
          Instr.binop "%add4.i.i550.i.i.epil" (BinOp.add) 128 (Operand.reg "%mul.i.i549.i.i.epil") (Operand.reg "%carry.029.i.i546.i.i.epil"),
          Instr.trunc "%conv5.i.i551.i.i.epil" 128 64 (Operand.reg "%add4.i.i550.i.i.epil"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i551.i.i.epil") (Operand.reg "%arrayidx.i.i547.i.i.epil"),
          Instr.binop "%shr.i.i552.i.i.epil" (BinOp.lshr) 128 (Operand.reg "%add4.i.i550.i.i.epil") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i.i553.i.i.epil" (BinOp.add) 64 (Operand.reg "%indvars.iv.i.i545.i.i.epil") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.binop "%epil.iter1063.next" (BinOp.add) 64 (Operand.reg "%epil.iter1063") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.icmp "%epil.iter1063.cmp.not" (IPred.eq) 64 (Operand.reg "%epil.iter1063.next") (Operand.reg "%xtraiter1062")], Term.condbr (Operand.reg "%epil.iter1063.cmp.not") "while.cond.preheader.i.i555.i.i.epilog-lcssa" "for.body.i.i544.i.i.epil"⟩ := by decide

theorem numFast_findBlock_while_cond_preheader_i_i555_i_i_epilog_lcssa :
    numFastBody.findBlock "while.cond.preheader.i.i555.i.i.epilog-lcssa" = some ⟨"while.cond.preheader.i.i555.i.i.epilog-lcssa", [
          Instr.trunc "%extract.t1092" 128 64 (Operand.reg "%shr.i.i552.i.i.epil")], Term.br "while.cond.preheader.i.i555.i.i"⟩ := by decide

theorem numFast_findBlock_while_cond_preheader_i_i555_i_i :
    numFastBody.findBlock "while.cond.preheader.i.i555.i.i" = some ⟨"while.cond.preheader.i.i555.i.i", [
          Instr.phi "%add4.i.i550.i.i.lcssa" (Ty.int 128) [("while.cond.preheader.i.i555.i.i.unr-lcssa", (Operand.reg "%add4.i.i550.i.i.lcssa.ph")),
                                       ("while.cond.preheader.i.i555.i.i.epilog-lcssa", (Operand.reg "%add4.i.i550.i.i.epil"))],
          Instr.phi "%shr.i.i552.i.i.lcssa.off0" (Ty.int 64) [("while.cond.preheader.i.i555.i.i.unr-lcssa", (Operand.reg "%shr.i.i552.i.i.lcssa.ph.off0")),
                                       ("while.cond.preheader.i.i555.i.i.epilog-lcssa", (Operand.reg "%extract.t1092"))],
          Instr.icmp "%tobool.not31.i.i556.i.i" (IPred.ult) 128 (Operand.reg "%add4.i.i550.i.i.lcssa") (Operand.imm (Const.int 128 0x00000000000000010000000000000000#128))], Term.condbr (Operand.reg "%tobool.not31.i.i556.i.i") "if.end198.i.i" "while.body.us.i.i557.i.i"⟩ := by decide

theorem numFast_findBlock_while_body_us_i_i557_i_i :
    numFastBody.findBlock "while.body.us.i.i557.i.i" = some ⟨"while.body.us.i.i557.i.i", [
          Instr.binop "%inc12.us.i.i559.i.i" (BinOp.add) 32 (Operand.reg "%92") (Operand.imm (Const.int 32 0x00000001#32)),
          Instr.gep "%arrayidx14.us.i.i560.i.i" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%wide.trip.count.i.i543.i.i"),
          Instr.store (Ty.int 64) (Operand.reg "%shr.i.i552.i.i.lcssa.off0") (Operand.reg "%arrayidx14.us.i.i560.i.i"),
          Instr.store (Ty.int 32) (Operand.reg "%inc12.us.i.i559.i.i") (Operand.reg "%n.i539.i.i")], Term.br "if.end198.i.i"⟩ := by decide

theorem numFast_findBlock_for_body_i_i544_i_i :
    numFastBody.findBlock "for.body.i.i544.i.i" = some ⟨"for.body.i.i544.i.i", [
          Instr.phi "%indvars.iv.i.i545.i.i" (Ty.int 64) [("for.body.lr.ph.i.i542.i.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i.i544.i.i", (Operand.reg "%indvars.iv.next.i.i553.i.i.3"))],
          Instr.phi "%carry.029.i.i546.i.i" (Ty.int 128) [("for.body.lr.ph.i.i542.i.i.new", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
                                       ("for.body.i.i544.i.i", (Operand.reg "%shr.i.i552.i.i.3"))],
          Instr.phi "%niter1068" (Ty.int 64) [("for.body.lr.ph.i.i542.i.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i.i544.i.i", (Operand.reg "%niter1068.next.3"))],
          Instr.gep "%arrayidx.i.i547.i.i" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%indvars.iv.i.i545.i.i"),
          Instr.load "%97" (Ty.int 64) (Operand.reg "%arrayidx.i.i547.i.i"),
          Instr.zext "%conv2.i.i548.i.i" 64 128 (Operand.reg "%97"),
          Instr.binop "%mul.i.i549.i.i" (BinOp.mul) 128 (Operand.reg "%conv2.i.i548.i.i") (Operand.reg "%conv3.i.i.i.i"),
          Instr.binop "%add4.i.i550.i.i" (BinOp.add) 128 (Operand.reg "%mul.i.i549.i.i") (Operand.reg "%carry.029.i.i546.i.i"),
          Instr.trunc "%conv5.i.i551.i.i" 128 64 (Operand.reg "%add4.i.i550.i.i"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i551.i.i") (Operand.reg "%arrayidx.i.i547.i.i"),
          Instr.binop "%shr.i.i552.i.i" (BinOp.lshr) 128 (Operand.reg "%add4.i.i550.i.i") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i.i553.i.i" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i545.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.gep "%arrayidx.i.i547.i.i.1" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%indvars.iv.next.i.i553.i.i"),
          Instr.load "%98" (Ty.int 64) (Operand.reg "%arrayidx.i.i547.i.i.1"),
          Instr.zext "%conv2.i.i548.i.i.1" 64 128 (Operand.reg "%98"),
          Instr.binop "%mul.i.i549.i.i.1" (BinOp.mul) 128 (Operand.reg "%conv2.i.i548.i.i.1") (Operand.reg "%conv3.i.i.i.i"),
          Instr.binop "%add4.i.i550.i.i.1" (BinOp.add) 128 (Operand.reg "%mul.i.i549.i.i.1") (Operand.reg "%shr.i.i552.i.i"),
          Instr.trunc "%conv5.i.i551.i.i.1" 128 64 (Operand.reg "%add4.i.i550.i.i.1"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i551.i.i.1") (Operand.reg "%arrayidx.i.i547.i.i.1"),
          Instr.binop "%shr.i.i552.i.i.1" (BinOp.lshr) 128 (Operand.reg "%add4.i.i550.i.i.1") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i.i553.i.i.1" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i545.i.i") (Operand.imm (Const.int 64 0x0000000000000002#64)),
          Instr.gep "%arrayidx.i.i547.i.i.2" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%indvars.iv.next.i.i553.i.i.1"),
          Instr.load "%99" (Ty.int 64) (Operand.reg "%arrayidx.i.i547.i.i.2"),
          Instr.zext "%conv2.i.i548.i.i.2" 64 128 (Operand.reg "%99"),
          Instr.binop "%mul.i.i549.i.i.2" (BinOp.mul) 128 (Operand.reg "%conv2.i.i548.i.i.2") (Operand.reg "%conv3.i.i.i.i"),
          Instr.binop "%add4.i.i550.i.i.2" (BinOp.add) 128 (Operand.reg "%mul.i.i549.i.i.2") (Operand.reg "%shr.i.i552.i.i.1"),
          Instr.trunc "%conv5.i.i551.i.i.2" 128 64 (Operand.reg "%add4.i.i550.i.i.2"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i551.i.i.2") (Operand.reg "%arrayidx.i.i547.i.i.2"),
          Instr.binop "%shr.i.i552.i.i.2" (BinOp.lshr) 128 (Operand.reg "%add4.i.i550.i.i.2") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i.i553.i.i.2" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i545.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
          Instr.gep "%arrayidx.i.i547.i.i.3" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%indvars.iv.next.i.i553.i.i.2"),
          Instr.load "%100" (Ty.int 64) (Operand.reg "%arrayidx.i.i547.i.i.3"),
          Instr.zext "%conv2.i.i548.i.i.3" 64 128 (Operand.reg "%100"),
          Instr.binop "%mul.i.i549.i.i.3" (BinOp.mul) 128 (Operand.reg "%conv2.i.i548.i.i.3") (Operand.reg "%conv3.i.i.i.i"),
          Instr.binop "%add4.i.i550.i.i.3" (BinOp.add) 128 (Operand.reg "%mul.i.i549.i.i.3") (Operand.reg "%shr.i.i552.i.i.2"),
          Instr.trunc "%conv5.i.i551.i.i.3" 128 64 (Operand.reg "%add4.i.i550.i.i.3"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i551.i.i.3") (Operand.reg "%arrayidx.i.i547.i.i.3"),
          Instr.binop "%shr.i.i552.i.i.3" (BinOp.lshr) 128 (Operand.reg "%add4.i.i550.i.i.3") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i.i553.i.i.3" (BinOp.add) 64 (Operand.reg "%indvars.iv.i.i545.i.i") (Operand.imm (Const.int 64 0x0000000000000004#64)),
          Instr.binop "%niter1068.next.3" (BinOp.add) 64 (Operand.reg "%niter1068") (Operand.imm (Const.int 64 0x0000000000000004#64)),
          Instr.icmp "%niter1068.ncmp.3" (IPred.eq) 64 (Operand.reg "%niter1068.next.3") (Operand.reg "%unroll_iter1067")], Term.condbr (Operand.reg "%niter1068.ncmp.3") "while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit" "for.body.i.i544.i.i"⟩ := by decide

theorem numFast_findBlock_if_else164_i_i :
    numFastBody.findBlock "if.else164.i.i" = some ⟨"if.else164.i.i", [
          Instr.icmp "%cmp165.i.i" (IPred.slt) 64 (Operand.reg "%add108.i.i") (Operand.imm (Const.int 64 0x0000000000000000#64))], Term.condbr (Operand.reg "%cmp165.i.i") "if.then167.i.i" "while.cond184.preheader.i.i"⟩ := by decide

theorem numFast_findBlock_while_cond184_preheader_i_i :
    numFastBody.findBlock "while.cond184.preheader.i.i" = some ⟨"while.cond184.preheader.i.i", [
          Instr.load "%n.i.promoted751.i.i" (Ty.int 32) (Operand.reg "%n.i.i.i"),
          Instr.icmp "%cmp185753.i.i" (IPred.ugt) 64 (Operand.reg "%add108.i.i") (Operand.imm (Const.int 64 0x0000000000000012#64))], Term.condbr (Operand.reg "%cmp185753.i.i") "while.body187.i.i" "while.end190.i.i"⟩ := by decide

theorem numFast_findBlock_if_then167_i_i :
    numFastBody.findBlock "if.then167.i.i" = some ⟨"if.then167.i.i", [
          Instr.binop "%sub169.i.i" (BinOp.sub) 64 (Operand.imm (Const.int 64 0x0000000000000000#64)) (Operand.reg "%add108.i.i"),
          Instr.icmp "%cmp171760.i.i" (IPred.sgt) 64 (Operand.reg "%sub169.i.i") (Operand.imm (Const.int 64 0x0000000000000012#64))], Term.condbr (Operand.reg "%cmp171760.i.i") "while.body173.i.i" "while.end176.thread.i.i"⟩ := by decide

theorem numFast_findBlock_while_end176_thread_i_i :
    numFastBody.findBlock "while.end176.thread.i.i" = some ⟨"while.end176.thread.i.i", [
          Instr.store (Ty.int 32) (Operand.imm (Const.int 32 0x00000001#32)) (Operand.reg "%n.i539.i.i")], Term.br "if.then178.i.i"⟩ := by decide

theorem numFast_findBlock_while_body173_i_i :
    numFastBody.findBlock "while.body173.i.i" = some ⟨"while.body173.i.i", [
          Instr.phi "%k168.0762.i.i" (Ty.int 64) [("stk_mul_u64.exit583.i.i", (Operand.reg "%sub175.i.i")),
                                       ("if.then167.i.i", (Operand.reg "%sub169.i.i"))],
          Instr.phi "%inc12.us.i.i581759761.i.i" (Ty.int 32) [("stk_mul_u64.exit583.i.i", (Operand.reg "%inc12.us.i.i581758.i.i")),
                                       ("if.then167.i.i", (Operand.imm (Const.int 32 0x00000001#32)))],
          Instr.icmp "%cmp28.i.i563.i.i" (IPred.sgt) 32 (Operand.reg "%inc12.us.i.i581759761.i.i") (Operand.imm (Const.int 32 0x00000000#32))], Term.condbr (Operand.reg "%cmp28.i.i563.i.i") "for.body.lr.ph.i.i564.i.i" "stk_mul_u64.exit583.i.i"⟩ := by decide

theorem numFast_findBlock_for_body_lr_ph_i_i564_i_i :
    numFastBody.findBlock "for.body.lr.ph.i.i564.i.i" = some ⟨"for.body.lr.ph.i.i564.i.i", [
          Instr.zext "%wide.trip.count.i.i565.i.i" 32 64 (Operand.reg "%inc12.us.i.i581759761.i.i"),
          Instr.binop "%xtraiter1083" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i.i565.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
          Instr.icmp "%101" (IPred.ult) 32 (Operand.reg "%inc12.us.i.i581759761.i.i") (Operand.imm (Const.int 32 0x00000004#32))], Term.condbr (Operand.reg "%101") "while.cond.preheader.i.i577.i.i.unr-lcssa" "for.body.lr.ph.i.i564.i.i.new"⟩ := by decide

theorem numFast_findBlock_for_body_lr_ph_i_i564_i_i_new :
    numFastBody.findBlock "for.body.lr.ph.i.i564.i.i.new" = some ⟨"for.body.lr.ph.i.i564.i.i.new", [
          Instr.binop "%unroll_iter1088" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i.i565.i.i") (Operand.imm (Const.int 64 0x000000007ffffffc#64))], Term.br "for.body.i.i566.i.i"⟩ := by decide

theorem numFast_findBlock_while_cond_preheader_i_i577_i_i_unr_lcssa_loopexit :
    numFastBody.findBlock "while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit" = some ⟨"while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit", [
          Instr.trunc "%extract.t1099" 128 64 (Operand.reg "%shr.i.i574.i.i.3")], Term.br "while.cond.preheader.i.i577.i.i.unr-lcssa"⟩ := by decide

theorem numFast_findBlock_while_cond_preheader_i_i577_i_i_unr_lcssa :
    numFastBody.findBlock "while.cond.preheader.i.i577.i.i.unr-lcssa" = some ⟨"while.cond.preheader.i.i577.i.i.unr-lcssa", [
          Instr.phi "%add4.i.i572.i.i.lcssa.ph" (Ty.int 128) [("for.body.lr.ph.i.i564.i.i", (Operand.imm Const.poison)),
                                       ("while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit", (Operand.reg "%add4.i.i572.i.i.3"))],
          Instr.phi "%shr.i.i574.i.i.lcssa.ph.off0" (Ty.int 64) [("for.body.lr.ph.i.i564.i.i", (Operand.imm Const.poison)),
                                       ("while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit", (Operand.reg "%extract.t1099"))],
          Instr.phi "%indvars.iv.i.i567.i.i.unr" (Ty.int 64) [("for.body.lr.ph.i.i564.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit", (Operand.reg "%indvars.iv.next.i.i575.i.i.3"))],
          Instr.phi "%carry.029.i.i568.i.i.unr" (Ty.int 128) [("for.body.lr.ph.i.i564.i.i", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
                                       ("while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit", (Operand.reg "%shr.i.i574.i.i.3"))],
          Instr.icmp "%lcmp.mod1085.not" (IPred.eq) 64 (Operand.reg "%xtraiter1083") (Operand.imm (Const.int 64 0x0000000000000000#64))], Term.condbr (Operand.reg "%lcmp.mod1085.not") "while.cond.preheader.i.i577.i.i" "for.body.i.i566.i.i.epil"⟩ := by decide

theorem numFast_findBlock_for_body_i_i566_i_i_epil :
    numFastBody.findBlock "for.body.i.i566.i.i.epil" = some ⟨"for.body.i.i566.i.i.epil", [
          Instr.phi "%indvars.iv.i.i567.i.i.epil" (Ty.int 64) [("for.body.i.i566.i.i.epil", (Operand.reg "%indvars.iv.next.i.i575.i.i.epil")),
                                       ("while.cond.preheader.i.i577.i.i.unr-lcssa", (Operand.reg "%indvars.iv.i.i567.i.i.unr"))],
          Instr.phi "%carry.029.i.i568.i.i.epil" (Ty.int 128) [("for.body.i.i566.i.i.epil", (Operand.reg "%shr.i.i574.i.i.epil")),
                                       ("while.cond.preheader.i.i577.i.i.unr-lcssa", (Operand.reg "%carry.029.i.i568.i.i.unr"))],
          Instr.phi "%epil.iter1084" (Ty.int 64) [("for.body.i.i566.i.i.epil", (Operand.reg "%epil.iter1084.next")),
                                       ("while.cond.preheader.i.i577.i.i.unr-lcssa", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
          Instr.gep "%arrayidx.i.i569.i.i.epil" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%indvars.iv.i.i567.i.i.epil"),
          Instr.load "%102" (Ty.int 64) (Operand.reg "%arrayidx.i.i569.i.i.epil"),
          Instr.zext "%conv2.i.i570.i.i.epil" 64 128 (Operand.reg "%102"),
          Instr.binop "%mul.i.i571.i.i.epil" (BinOp.mul) 128 (Operand.reg "%conv2.i.i570.i.i.epil") (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
          Instr.binop "%add4.i.i572.i.i.epil" (BinOp.add) 128 (Operand.reg "%mul.i.i571.i.i.epil") (Operand.reg "%carry.029.i.i568.i.i.epil"),
          Instr.trunc "%conv5.i.i573.i.i.epil" 128 64 (Operand.reg "%add4.i.i572.i.i.epil"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i573.i.i.epil") (Operand.reg "%arrayidx.i.i569.i.i.epil"),
          Instr.binop "%shr.i.i574.i.i.epil" (BinOp.lshr) 128 (Operand.reg "%add4.i.i572.i.i.epil") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i.i575.i.i.epil" (BinOp.add) 64 (Operand.reg "%indvars.iv.i.i567.i.i.epil") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.binop "%epil.iter1084.next" (BinOp.add) 64 (Operand.reg "%epil.iter1084") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.icmp "%epil.iter1084.cmp.not" (IPred.eq) 64 (Operand.reg "%epil.iter1084.next") (Operand.reg "%xtraiter1083")], Term.condbr (Operand.reg "%epil.iter1084.cmp.not") "while.cond.preheader.i.i577.i.i.epilog-lcssa" "for.body.i.i566.i.i.epil"⟩ := by decide

theorem numFast_findBlock_while_cond_preheader_i_i577_i_i_epilog_lcssa :
    numFastBody.findBlock "while.cond.preheader.i.i577.i.i.epilog-lcssa" = some ⟨"while.cond.preheader.i.i577.i.i.epilog-lcssa", [
          Instr.trunc "%extract.t1098" 128 64 (Operand.reg "%shr.i.i574.i.i.epil")], Term.br "while.cond.preheader.i.i577.i.i"⟩ := by decide

theorem numFast_findBlock_while_cond_preheader_i_i577_i_i :
    numFastBody.findBlock "while.cond.preheader.i.i577.i.i" = some ⟨"while.cond.preheader.i.i577.i.i", [
          Instr.phi "%add4.i.i572.i.i.lcssa" (Ty.int 128) [("while.cond.preheader.i.i577.i.i.unr-lcssa", (Operand.reg "%add4.i.i572.i.i.lcssa.ph")),
                                       ("while.cond.preheader.i.i577.i.i.epilog-lcssa", (Operand.reg "%add4.i.i572.i.i.epil"))],
          Instr.phi "%shr.i.i574.i.i.lcssa.off0" (Ty.int 64) [("while.cond.preheader.i.i577.i.i.unr-lcssa", (Operand.reg "%shr.i.i574.i.i.lcssa.ph.off0")),
                                       ("while.cond.preheader.i.i577.i.i.epilog-lcssa", (Operand.reg "%extract.t1098"))],
          Instr.icmp "%tobool.not31.i.i578.i.i" (IPred.ult) 128 (Operand.reg "%add4.i.i572.i.i.lcssa") (Operand.imm (Const.int 128 0x00000000000000010000000000000000#128))], Term.condbr (Operand.reg "%tobool.not31.i.i578.i.i") "stk_mul_u64.exit583.i.i" "while.body.us.i.i579.i.i"⟩ := by decide

theorem numFast_findBlock_while_body_us_i_i579_i_i :
    numFastBody.findBlock "while.body.us.i.i579.i.i" = some ⟨"while.body.us.i.i579.i.i", [
          Instr.binop "%inc12.us.i.i581.i.i" (BinOp.add) 32 (Operand.reg "%inc12.us.i.i581759761.i.i") (Operand.imm (Const.int 32 0x00000001#32)),
          Instr.gep "%arrayidx14.us.i.i582.i.i" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%wide.trip.count.i.i565.i.i"),
          Instr.store (Ty.int 64) (Operand.reg "%shr.i.i574.i.i.lcssa.off0") (Operand.reg "%arrayidx14.us.i.i582.i.i")], Term.br "stk_mul_u64.exit583.i.i"⟩ := by decide

theorem numFast_findBlock_for_body_i_i566_i_i :
    numFastBody.findBlock "for.body.i.i566.i.i" = some ⟨"for.body.i.i566.i.i", [
          Instr.phi "%indvars.iv.i.i567.i.i" (Ty.int 64) [("for.body.lr.ph.i.i564.i.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i.i566.i.i", (Operand.reg "%indvars.iv.next.i.i575.i.i.3"))],
          Instr.phi "%carry.029.i.i568.i.i" (Ty.int 128) [("for.body.lr.ph.i.i564.i.i.new", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
                                       ("for.body.i.i566.i.i", (Operand.reg "%shr.i.i574.i.i.3"))],
          Instr.phi "%niter1089" (Ty.int 64) [("for.body.lr.ph.i.i564.i.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i.i566.i.i", (Operand.reg "%niter1089.next.3"))],
          Instr.gep "%arrayidx.i.i569.i.i" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%indvars.iv.i.i567.i.i"),
          Instr.load "%103" (Ty.int 64) (Operand.reg "%arrayidx.i.i569.i.i"),
          Instr.zext "%conv2.i.i570.i.i" 64 128 (Operand.reg "%103"),
          Instr.binop "%mul.i.i571.i.i" (BinOp.mul) 128 (Operand.reg "%conv2.i.i570.i.i") (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
          Instr.binop "%add4.i.i572.i.i" (BinOp.add) 128 (Operand.reg "%mul.i.i571.i.i") (Operand.reg "%carry.029.i.i568.i.i"),
          Instr.trunc "%conv5.i.i573.i.i" 128 64 (Operand.reg "%add4.i.i572.i.i"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i573.i.i") (Operand.reg "%arrayidx.i.i569.i.i"),
          Instr.binop "%shr.i.i574.i.i" (BinOp.lshr) 128 (Operand.reg "%add4.i.i572.i.i") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i.i575.i.i" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i567.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.gep "%arrayidx.i.i569.i.i.1" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%indvars.iv.next.i.i575.i.i"),
          Instr.load "%104" (Ty.int 64) (Operand.reg "%arrayidx.i.i569.i.i.1"),
          Instr.zext "%conv2.i.i570.i.i.1" 64 128 (Operand.reg "%104"),
          Instr.binop "%mul.i.i571.i.i.1" (BinOp.mul) 128 (Operand.reg "%conv2.i.i570.i.i.1") (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
          Instr.binop "%add4.i.i572.i.i.1" (BinOp.add) 128 (Operand.reg "%mul.i.i571.i.i.1") (Operand.reg "%shr.i.i574.i.i"),
          Instr.trunc "%conv5.i.i573.i.i.1" 128 64 (Operand.reg "%add4.i.i572.i.i.1"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i573.i.i.1") (Operand.reg "%arrayidx.i.i569.i.i.1"),
          Instr.binop "%shr.i.i574.i.i.1" (BinOp.lshr) 128 (Operand.reg "%add4.i.i572.i.i.1") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i.i575.i.i.1" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i567.i.i") (Operand.imm (Const.int 64 0x0000000000000002#64)),
          Instr.gep "%arrayidx.i.i569.i.i.2" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%indvars.iv.next.i.i575.i.i.1"),
          Instr.load "%105" (Ty.int 64) (Operand.reg "%arrayidx.i.i569.i.i.2"),
          Instr.zext "%conv2.i.i570.i.i.2" 64 128 (Operand.reg "%105"),
          Instr.binop "%mul.i.i571.i.i.2" (BinOp.mul) 128 (Operand.reg "%conv2.i.i570.i.i.2") (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
          Instr.binop "%add4.i.i572.i.i.2" (BinOp.add) 128 (Operand.reg "%mul.i.i571.i.i.2") (Operand.reg "%shr.i.i574.i.i.1"),
          Instr.trunc "%conv5.i.i573.i.i.2" 128 64 (Operand.reg "%add4.i.i572.i.i.2"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i573.i.i.2") (Operand.reg "%arrayidx.i.i569.i.i.2"),
          Instr.binop "%shr.i.i574.i.i.2" (BinOp.lshr) 128 (Operand.reg "%add4.i.i572.i.i.2") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i.i575.i.i.2" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i567.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
          Instr.gep "%arrayidx.i.i569.i.i.3" (Ty.int 64) (Operand.reg "%pow.i.i") (Operand.reg "%indvars.iv.next.i.i575.i.i.2"),
          Instr.load "%106" (Ty.int 64) (Operand.reg "%arrayidx.i.i569.i.i.3"),
          Instr.zext "%conv2.i.i570.i.i.3" 64 128 (Operand.reg "%106"),
          Instr.binop "%mul.i.i571.i.i.3" (BinOp.mul) 128 (Operand.reg "%conv2.i.i570.i.i.3") (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
          Instr.binop "%add4.i.i572.i.i.3" (BinOp.add) 128 (Operand.reg "%mul.i.i571.i.i.3") (Operand.reg "%shr.i.i574.i.i.2"),
          Instr.trunc "%conv5.i.i573.i.i.3" 128 64 (Operand.reg "%add4.i.i572.i.i.3"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i573.i.i.3") (Operand.reg "%arrayidx.i.i569.i.i.3"),
          Instr.binop "%shr.i.i574.i.i.3" (BinOp.lshr) 128 (Operand.reg "%add4.i.i572.i.i.3") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i.i575.i.i.3" (BinOp.add) 64 (Operand.reg "%indvars.iv.i.i567.i.i") (Operand.imm (Const.int 64 0x0000000000000004#64)),
          Instr.binop "%niter1089.next.3" (BinOp.add) 64 (Operand.reg "%niter1089") (Operand.imm (Const.int 64 0x0000000000000004#64)),
          Instr.icmp "%niter1089.ncmp.3" (IPred.eq) 64 (Operand.reg "%niter1089.next.3") (Operand.reg "%unroll_iter1088")], Term.condbr (Operand.reg "%niter1089.ncmp.3") "while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit" "for.body.i.i566.i.i"⟩ := by decide

theorem numFast_findBlock_stk_mul_u64_exit583_i_i :
    numFastBody.findBlock "stk_mul_u64.exit583.i.i" = some ⟨"stk_mul_u64.exit583.i.i", [
          Instr.phi "%inc12.us.i.i581758.i.i" (Ty.int 32) [("while.body173.i.i", (Operand.reg "%inc12.us.i.i581759761.i.i")),
                                       ("while.cond.preheader.i.i577.i.i", (Operand.reg "%inc12.us.i.i581759761.i.i")),
                                       ("while.body.us.i.i579.i.i", (Operand.reg "%inc12.us.i.i581.i.i"))],
          Instr.binop "%sub175.i.i" (BinOp.add) 64 (Operand.reg "%k168.0762.i.i") (Operand.imm (Const.int 64 0xffffffffffffffed#64)),
          Instr.icmp "%cmp171.i.i" (IPred.sgt) 64 (Operand.reg "%k168.0762.i.i") (Operand.imm (Const.int 64 0x0000000000000025#64))], Term.condbr (Operand.reg "%cmp171.i.i") "while.body173.i.i" "while.end176.i.i"⟩ := by decide

theorem numFast_findBlock_while_end176_i_i :
    numFastBody.findBlock "while.end176.i.i" = some ⟨"while.end176.i.i", [
          Instr.store (Ty.int 32) (Operand.reg "%inc12.us.i.i581758.i.i") (Operand.reg "%n.i539.i.i"),
          Instr.icmp "%tobool177.not.i.i" (IPred.eq) 64 (Operand.reg "%sub175.i.i") (Operand.imm (Const.int 64 0x0000000000000000#64))], Term.condbr (Operand.reg "%tobool177.not.i.i") "if.end198.i.i" "if.then178.i.i"⟩ := by decide

theorem numFast_findBlock_if_then178_i_i :
    numFastBody.findBlock "if.then178.i.i" = some ⟨"if.then178.i.i", [
          Instr.phi "%k168.0.lcssa829.i.i" (Ty.int 64) [("while.end176.thread.i.i", (Operand.reg "%sub169.i.i")),
                                       ("while.end176.i.i", (Operand.reg "%sub175.i.i"))],
          Instr.gep "%arrayidx180.i.i" (Ty.int 64) (Operand.global "@NUMF_EL1_P10") (Operand.reg "%k168.0.lcssa829.i.i"),
          Instr.load "%107" (Ty.int 64) (Operand.reg "%arrayidx180.i.i"),
          Instr.callVoid "stk_mul_u64" [(Ty.ptr, (Operand.reg "%pow.i.i")),
                             ((Ty.int 64), (Operand.reg "%107"))]], Term.br "if.end198.i.i"⟩ := by decide

theorem numFast_findBlock_while_body187_i_i :
    numFastBody.findBlock "while.body187.i.i" = some ⟨"while.body187.i.i", [
          Instr.phi "%k183.0754.i.i" (Ty.int 64) [("stk_mul_u64.exit605.i.i", (Operand.reg "%sub189.i.i")),
                                       ("while.cond184.preheader.i.i", (Operand.reg "%add108.i.i"))],
          Instr.phi "%108" (Ty.int 32) [("stk_mul_u64.exit605.i.i", (Operand.reg "%115")),
                                       ("while.cond184.preheader.i.i", (Operand.reg "%n.i.promoted751.i.i"))],
          Instr.icmp "%cmp28.i.i585.i.i" (IPred.sgt) 32 (Operand.reg "%108") (Operand.imm (Const.int 32 0x00000000#32))], Term.condbr (Operand.reg "%cmp28.i.i585.i.i") "for.body.lr.ph.i.i586.i.i" "stk_mul_u64.exit605.i.i"⟩ := by decide

theorem numFast_findBlock_for_body_lr_ph_i_i586_i_i :
    numFastBody.findBlock "for.body.lr.ph.i.i586.i.i" = some ⟨"for.body.lr.ph.i.i586.i.i", [
          Instr.zext "%wide.trip.count.i.i587.i.i" 32 64 (Operand.reg "%108"),
          Instr.binop "%xtraiter1069" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i.i587.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
          Instr.icmp "%109" (IPred.ult) 32 (Operand.reg "%108") (Operand.imm (Const.int 32 0x00000004#32))], Term.condbr (Operand.reg "%109") "while.cond.preheader.i.i599.i.i.unr-lcssa" "for.body.lr.ph.i.i586.i.i.new"⟩ := by decide

theorem numFast_findBlock_for_body_lr_ph_i_i586_i_i_new :
    numFastBody.findBlock "for.body.lr.ph.i.i586.i.i.new" = some ⟨"for.body.lr.ph.i.i586.i.i.new", [
          Instr.binop "%unroll_iter1074" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i.i587.i.i") (Operand.imm (Const.int 64 0x000000007ffffffc#64))], Term.br "for.body.i.i588.i.i"⟩ := by decide

theorem numFast_findBlock_while_cond_preheader_i_i599_i_i_unr_lcssa_loopexit :
    numFastBody.findBlock "while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit" = some ⟨"while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit", [
          Instr.trunc "%extract.t1095" 128 64 (Operand.reg "%shr.i.i596.i.i.3")], Term.br "while.cond.preheader.i.i599.i.i.unr-lcssa"⟩ := by decide

theorem numFast_findBlock_while_cond_preheader_i_i599_i_i_unr_lcssa :
    numFastBody.findBlock "while.cond.preheader.i.i599.i.i.unr-lcssa" = some ⟨"while.cond.preheader.i.i599.i.i.unr-lcssa", [
          Instr.phi "%add4.i.i594.i.i.lcssa.ph" (Ty.int 128) [("for.body.lr.ph.i.i586.i.i", (Operand.imm Const.poison)),
                                       ("while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit", (Operand.reg "%add4.i.i594.i.i.3"))],
          Instr.phi "%shr.i.i596.i.i.lcssa.ph.off0" (Ty.int 64) [("for.body.lr.ph.i.i586.i.i", (Operand.imm Const.poison)),
                                       ("while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit", (Operand.reg "%extract.t1095"))],
          Instr.phi "%indvars.iv.i.i589.i.i.unr" (Ty.int 64) [("for.body.lr.ph.i.i586.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit", (Operand.reg "%indvars.iv.next.i.i597.i.i.3"))],
          Instr.phi "%carry.029.i.i590.i.i.unr" (Ty.int 128) [("for.body.lr.ph.i.i586.i.i", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
                                       ("while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit", (Operand.reg "%shr.i.i596.i.i.3"))],
          Instr.icmp "%lcmp.mod1071.not" (IPred.eq) 64 (Operand.reg "%xtraiter1069") (Operand.imm (Const.int 64 0x0000000000000000#64))], Term.condbr (Operand.reg "%lcmp.mod1071.not") "while.cond.preheader.i.i599.i.i" "for.body.i.i588.i.i.epil"⟩ := by decide

theorem numFast_findBlock_for_body_i_i588_i_i_epil :
    numFastBody.findBlock "for.body.i.i588.i.i.epil" = some ⟨"for.body.i.i588.i.i.epil", [
          Instr.phi "%indvars.iv.i.i589.i.i.epil" (Ty.int 64) [("for.body.i.i588.i.i.epil", (Operand.reg "%indvars.iv.next.i.i597.i.i.epil")),
                                       ("while.cond.preheader.i.i599.i.i.unr-lcssa", (Operand.reg "%indvars.iv.i.i589.i.i.unr"))],
          Instr.phi "%carry.029.i.i590.i.i.epil" (Ty.int 128) [("for.body.i.i588.i.i.epil", (Operand.reg "%shr.i.i596.i.i.epil")),
                                       ("while.cond.preheader.i.i599.i.i.unr-lcssa", (Operand.reg "%carry.029.i.i590.i.i.unr"))],
          Instr.phi "%epil.iter1070" (Ty.int 64) [("for.body.i.i588.i.i.epil", (Operand.reg "%epil.iter1070.next")),
                                       ("while.cond.preheader.i.i599.i.i.unr-lcssa", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
          Instr.gep "%arrayidx.i.i591.i.i.epil" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.i.i589.i.i.epil"),
          Instr.load "%110" (Ty.int 64) (Operand.reg "%arrayidx.i.i591.i.i.epil"),
          Instr.zext "%conv2.i.i592.i.i.epil" 64 128 (Operand.reg "%110"),
          Instr.binop "%mul.i.i593.i.i.epil" (BinOp.mul) 128 (Operand.reg "%conv2.i.i592.i.i.epil") (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
          Instr.binop "%add4.i.i594.i.i.epil" (BinOp.add) 128 (Operand.reg "%mul.i.i593.i.i.epil") (Operand.reg "%carry.029.i.i590.i.i.epil"),
          Instr.trunc "%conv5.i.i595.i.i.epil" 128 64 (Operand.reg "%add4.i.i594.i.i.epil"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i595.i.i.epil") (Operand.reg "%arrayidx.i.i591.i.i.epil"),
          Instr.binop "%shr.i.i596.i.i.epil" (BinOp.lshr) 128 (Operand.reg "%add4.i.i594.i.i.epil") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i.i597.i.i.epil" (BinOp.add) 64 (Operand.reg "%indvars.iv.i.i589.i.i.epil") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.binop "%epil.iter1070.next" (BinOp.add) 64 (Operand.reg "%epil.iter1070") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.icmp "%epil.iter1070.cmp.not" (IPred.eq) 64 (Operand.reg "%epil.iter1070.next") (Operand.reg "%xtraiter1069")], Term.condbr (Operand.reg "%epil.iter1070.cmp.not") "while.cond.preheader.i.i599.i.i.epilog-lcssa" "for.body.i.i588.i.i.epil"⟩ := by decide

theorem numFast_findBlock_while_cond_preheader_i_i599_i_i_epilog_lcssa :
    numFastBody.findBlock "while.cond.preheader.i.i599.i.i.epilog-lcssa" = some ⟨"while.cond.preheader.i.i599.i.i.epilog-lcssa", [
          Instr.trunc "%extract.t1094" 128 64 (Operand.reg "%shr.i.i596.i.i.epil")], Term.br "while.cond.preheader.i.i599.i.i"⟩ := by decide

theorem numFast_findBlock_while_cond_preheader_i_i599_i_i :
    numFastBody.findBlock "while.cond.preheader.i.i599.i.i" = some ⟨"while.cond.preheader.i.i599.i.i", [
          Instr.phi "%add4.i.i594.i.i.lcssa" (Ty.int 128) [("while.cond.preheader.i.i599.i.i.unr-lcssa", (Operand.reg "%add4.i.i594.i.i.lcssa.ph")),
                                       ("while.cond.preheader.i.i599.i.i.epilog-lcssa", (Operand.reg "%add4.i.i594.i.i.epil"))],
          Instr.phi "%shr.i.i596.i.i.lcssa.off0" (Ty.int 64) [("while.cond.preheader.i.i599.i.i.unr-lcssa", (Operand.reg "%shr.i.i596.i.i.lcssa.ph.off0")),
                                       ("while.cond.preheader.i.i599.i.i.epilog-lcssa", (Operand.reg "%extract.t1094"))],
          Instr.icmp "%tobool.not31.i.i600.i.i" (IPred.ult) 128 (Operand.reg "%add4.i.i594.i.i.lcssa") (Operand.imm (Const.int 128 0x00000000000000010000000000000000#128))], Term.condbr (Operand.reg "%tobool.not31.i.i600.i.i") "stk_mul_u64.exit605.i.i" "while.body.us.i.i601.i.i"⟩ := by decide

theorem numFast_findBlock_while_body_us_i_i601_i_i :
    numFastBody.findBlock "while.body.us.i.i601.i.i" = some ⟨"while.body.us.i.i601.i.i", [
          Instr.binop "%inc12.us.i.i603.i.i" (BinOp.add) 32 (Operand.reg "%108") (Operand.imm (Const.int 32 0x00000001#32)),
          Instr.gep "%arrayidx14.us.i.i604.i.i" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%wide.trip.count.i.i587.i.i"),
          Instr.store (Ty.int 64) (Operand.reg "%shr.i.i596.i.i.lcssa.off0") (Operand.reg "%arrayidx14.us.i.i604.i.i")], Term.br "stk_mul_u64.exit605.i.i"⟩ := by decide

theorem numFast_findBlock_for_body_i_i588_i_i :
    numFastBody.findBlock "for.body.i.i588.i.i" = some ⟨"for.body.i.i588.i.i", [
          Instr.phi "%indvars.iv.i.i589.i.i" (Ty.int 64) [("for.body.lr.ph.i.i586.i.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i.i588.i.i", (Operand.reg "%indvars.iv.next.i.i597.i.i.3"))],
          Instr.phi "%carry.029.i.i590.i.i" (Ty.int 128) [("for.body.lr.ph.i.i586.i.i.new", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
                                       ("for.body.i.i588.i.i", (Operand.reg "%shr.i.i596.i.i.3"))],
          Instr.phi "%niter1075" (Ty.int 64) [("for.body.lr.ph.i.i586.i.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i.i588.i.i", (Operand.reg "%niter1075.next.3"))],
          Instr.gep "%arrayidx.i.i591.i.i" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.i.i589.i.i"),
          Instr.load "%111" (Ty.int 64) (Operand.reg "%arrayidx.i.i591.i.i"),
          Instr.zext "%conv2.i.i592.i.i" 64 128 (Operand.reg "%111"),
          Instr.binop "%mul.i.i593.i.i" (BinOp.mul) 128 (Operand.reg "%conv2.i.i592.i.i") (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
          Instr.binop "%add4.i.i594.i.i" (BinOp.add) 128 (Operand.reg "%mul.i.i593.i.i") (Operand.reg "%carry.029.i.i590.i.i"),
          Instr.trunc "%conv5.i.i595.i.i" 128 64 (Operand.reg "%add4.i.i594.i.i"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i595.i.i") (Operand.reg "%arrayidx.i.i591.i.i"),
          Instr.binop "%shr.i.i596.i.i" (BinOp.lshr) 128 (Operand.reg "%add4.i.i594.i.i") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i.i597.i.i" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i589.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.gep "%arrayidx.i.i591.i.i.1" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.next.i.i597.i.i"),
          Instr.load "%112" (Ty.int 64) (Operand.reg "%arrayidx.i.i591.i.i.1"),
          Instr.zext "%conv2.i.i592.i.i.1" 64 128 (Operand.reg "%112"),
          Instr.binop "%mul.i.i593.i.i.1" (BinOp.mul) 128 (Operand.reg "%conv2.i.i592.i.i.1") (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
          Instr.binop "%add4.i.i594.i.i.1" (BinOp.add) 128 (Operand.reg "%mul.i.i593.i.i.1") (Operand.reg "%shr.i.i596.i.i"),
          Instr.trunc "%conv5.i.i595.i.i.1" 128 64 (Operand.reg "%add4.i.i594.i.i.1"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i595.i.i.1") (Operand.reg "%arrayidx.i.i591.i.i.1"),
          Instr.binop "%shr.i.i596.i.i.1" (BinOp.lshr) 128 (Operand.reg "%add4.i.i594.i.i.1") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i.i597.i.i.1" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i589.i.i") (Operand.imm (Const.int 64 0x0000000000000002#64)),
          Instr.gep "%arrayidx.i.i591.i.i.2" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.next.i.i597.i.i.1"),
          Instr.load "%113" (Ty.int 64) (Operand.reg "%arrayidx.i.i591.i.i.2"),
          Instr.zext "%conv2.i.i592.i.i.2" 64 128 (Operand.reg "%113"),
          Instr.binop "%mul.i.i593.i.i.2" (BinOp.mul) 128 (Operand.reg "%conv2.i.i592.i.i.2") (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
          Instr.binop "%add4.i.i594.i.i.2" (BinOp.add) 128 (Operand.reg "%mul.i.i593.i.i.2") (Operand.reg "%shr.i.i596.i.i.1"),
          Instr.trunc "%conv5.i.i595.i.i.2" 128 64 (Operand.reg "%add4.i.i594.i.i.2"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i595.i.i.2") (Operand.reg "%arrayidx.i.i591.i.i.2"),
          Instr.binop "%shr.i.i596.i.i.2" (BinOp.lshr) 128 (Operand.reg "%add4.i.i594.i.i.2") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i.i597.i.i.2" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i589.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
          Instr.gep "%arrayidx.i.i591.i.i.3" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.next.i.i597.i.i.2"),
          Instr.load "%114" (Ty.int 64) (Operand.reg "%arrayidx.i.i591.i.i.3"),
          Instr.zext "%conv2.i.i592.i.i.3" 64 128 (Operand.reg "%114"),
          Instr.binop "%mul.i.i593.i.i.3" (BinOp.mul) 128 (Operand.reg "%conv2.i.i592.i.i.3") (Operand.imm (Const.int 128 0x00000000000000008ac7230489e80000#128)),
          Instr.binop "%add4.i.i594.i.i.3" (BinOp.add) 128 (Operand.reg "%mul.i.i593.i.i.3") (Operand.reg "%shr.i.i596.i.i.2"),
          Instr.trunc "%conv5.i.i595.i.i.3" 128 64 (Operand.reg "%add4.i.i594.i.i.3"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i595.i.i.3") (Operand.reg "%arrayidx.i.i591.i.i.3"),
          Instr.binop "%shr.i.i596.i.i.3" (BinOp.lshr) 128 (Operand.reg "%add4.i.i594.i.i.3") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i.i597.i.i.3" (BinOp.add) 64 (Operand.reg "%indvars.iv.i.i589.i.i") (Operand.imm (Const.int 64 0x0000000000000004#64)),
          Instr.binop "%niter1075.next.3" (BinOp.add) 64 (Operand.reg "%niter1075") (Operand.imm (Const.int 64 0x0000000000000004#64)),
          Instr.icmp "%niter1075.ncmp.3" (IPred.eq) 64 (Operand.reg "%niter1075.next.3") (Operand.reg "%unroll_iter1074")], Term.condbr (Operand.reg "%niter1075.ncmp.3") "while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit" "for.body.i.i588.i.i"⟩ := by decide

theorem numFast_findBlock_stk_mul_u64_exit605_i_i :
    numFastBody.findBlock "stk_mul_u64.exit605.i.i" = some ⟨"stk_mul_u64.exit605.i.i", [
          Instr.phi "%115" (Ty.int 32) [("while.body187.i.i", (Operand.reg "%108")),
                                       ("while.cond.preheader.i.i599.i.i", (Operand.reg "%108")),
                                       ("while.body.us.i.i601.i.i", (Operand.reg "%inc12.us.i.i603.i.i"))],
          Instr.binop "%sub189.i.i" (BinOp.add) 64 (Operand.reg "%k183.0754.i.i") (Operand.imm (Const.int 64 0xffffffffffffffed#64)),
          Instr.icmp "%cmp185.i.i" (IPred.sgt) 64 (Operand.reg "%k183.0754.i.i") (Operand.imm (Const.int 64 0x0000000000000025#64))], Term.condbr (Operand.reg "%cmp185.i.i") "while.body187.i.i" "while.end190.i.i"⟩ := by decide

theorem numFast_findBlock_while_end190_i_i :
    numFastBody.findBlock "while.end190.i.i" = some ⟨"while.end190.i.i", [
          Instr.phi "%116" (Ty.int 32) [("while.cond184.preheader.i.i", (Operand.reg "%n.i.promoted751.i.i")),
                                       ("stk_mul_u64.exit605.i.i", (Operand.reg "%115"))],
          Instr.phi "%k183.0.lcssa.i.i" (Ty.int 64) [("while.cond184.preheader.i.i", (Operand.reg "%add108.i.i")),
                                       ("stk_mul_u64.exit605.i.i", (Operand.reg "%sub189.i.i"))],
          Instr.store (Ty.int 32) (Operand.reg "%116") (Operand.reg "%n.i.i.i"),
          Instr.icmp "%tobool191.not.i.i" (IPred.ne) 64 (Operand.reg "%k183.0.lcssa.i.i") (Operand.imm (Const.int 64 0x0000000000000000#64)),
          Instr.icmp "%cmp28.i.i607.i.i" (IPred.sgt) 32 (Operand.reg "%116") (Operand.imm (Const.int 32 0x00000000#32)),
          Instr.select "%or.cond865.i.i" (Ty.int 1) (Operand.reg "%tobool191.not.i.i") (Operand.reg "%cmp28.i.i607.i.i") (Operand.imm (Const.int 1 0x0#1))], Term.condbr (Operand.reg "%or.cond865.i.i") "for.body.lr.ph.i.i608.i.i" "if.end195.i.i"⟩ := by decide

theorem numFast_findBlock_for_body_lr_ph_i_i608_i_i :
    numFastBody.findBlock "for.body.lr.ph.i.i608.i.i" = some ⟨"for.body.lr.ph.i.i608.i.i", [
          Instr.gep "%arrayidx194.i.i" (Ty.int 64) (Operand.global "@NUMF_EL1_P10") (Operand.reg "%k183.0.lcssa.i.i"),
          Instr.load "%117" (Ty.int 64) (Operand.reg "%arrayidx194.i.i"),
          Instr.zext "%conv3.i.i609.i.i" 64 128 (Operand.reg "%117"),
          Instr.zext "%wide.trip.count.i.i610.i.i" 32 64 (Operand.reg "%116"),
          Instr.binop "%xtraiter1076" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i.i610.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
          Instr.icmp "%118" (IPred.ult) 32 (Operand.reg "%116") (Operand.imm (Const.int 32 0x00000004#32))], Term.condbr (Operand.reg "%118") "while.cond.preheader.i.i622.i.i.unr-lcssa" "for.body.lr.ph.i.i608.i.i.new"⟩ := by decide

theorem numFast_findBlock_for_body_lr_ph_i_i608_i_i_new :
    numFastBody.findBlock "for.body.lr.ph.i.i608.i.i.new" = some ⟨"for.body.lr.ph.i.i608.i.i.new", [
          Instr.binop "%unroll_iter1081" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i.i610.i.i") (Operand.imm (Const.int 64 0x000000007ffffffc#64))], Term.br "for.body.i.i611.i.i"⟩ := by decide

theorem numFast_findBlock_while_cond_preheader_i_i622_i_i_unr_lcssa_loopexit :
    numFastBody.findBlock "while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit" = some ⟨"while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit", [
          Instr.trunc "%extract.t1097" 128 64 (Operand.reg "%shr.i.i619.i.i.3")], Term.br "while.cond.preheader.i.i622.i.i.unr-lcssa"⟩ := by decide

theorem numFast_findBlock_while_cond_preheader_i_i622_i_i_unr_lcssa :
    numFastBody.findBlock "while.cond.preheader.i.i622.i.i.unr-lcssa" = some ⟨"while.cond.preheader.i.i622.i.i.unr-lcssa", [
          Instr.phi "%add4.i.i617.i.i.lcssa.ph" (Ty.int 128) [("for.body.lr.ph.i.i608.i.i", (Operand.imm Const.poison)),
                                       ("while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit", (Operand.reg "%add4.i.i617.i.i.3"))],
          Instr.phi "%shr.i.i619.i.i.lcssa.ph.off0" (Ty.int 64) [("for.body.lr.ph.i.i608.i.i", (Operand.imm Const.poison)),
                                       ("while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit", (Operand.reg "%extract.t1097"))],
          Instr.phi "%indvars.iv.i.i612.i.i.unr" (Ty.int 64) [("for.body.lr.ph.i.i608.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit", (Operand.reg "%indvars.iv.next.i.i620.i.i.3"))],
          Instr.phi "%carry.029.i.i613.i.i.unr" (Ty.int 128) [("for.body.lr.ph.i.i608.i.i", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
                                       ("while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit", (Operand.reg "%shr.i.i619.i.i.3"))],
          Instr.icmp "%lcmp.mod1078.not" (IPred.eq) 64 (Operand.reg "%xtraiter1076") (Operand.imm (Const.int 64 0x0000000000000000#64))], Term.condbr (Operand.reg "%lcmp.mod1078.not") "while.cond.preheader.i.i622.i.i" "for.body.i.i611.i.i.epil"⟩ := by decide

theorem numFast_findBlock_for_body_i_i611_i_i_epil :
    numFastBody.findBlock "for.body.i.i611.i.i.epil" = some ⟨"for.body.i.i611.i.i.epil", [
          Instr.phi "%indvars.iv.i.i612.i.i.epil" (Ty.int 64) [("for.body.i.i611.i.i.epil", (Operand.reg "%indvars.iv.next.i.i620.i.i.epil")),
                                       ("while.cond.preheader.i.i622.i.i.unr-lcssa", (Operand.reg "%indvars.iv.i.i612.i.i.unr"))],
          Instr.phi "%carry.029.i.i613.i.i.epil" (Ty.int 128) [("for.body.i.i611.i.i.epil", (Operand.reg "%shr.i.i619.i.i.epil")),
                                       ("while.cond.preheader.i.i622.i.i.unr-lcssa", (Operand.reg "%carry.029.i.i613.i.i.unr"))],
          Instr.phi "%epil.iter1077" (Ty.int 64) [("for.body.i.i611.i.i.epil", (Operand.reg "%epil.iter1077.next")),
                                       ("while.cond.preheader.i.i622.i.i.unr-lcssa", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
          Instr.gep "%arrayidx.i.i614.i.i.epil" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.i.i612.i.i.epil"),
          Instr.load "%119" (Ty.int 64) (Operand.reg "%arrayidx.i.i614.i.i.epil"),
          Instr.zext "%conv2.i.i615.i.i.epil" 64 128 (Operand.reg "%119"),
          Instr.binop "%mul.i.i616.i.i.epil" (BinOp.mul) 128 (Operand.reg "%conv2.i.i615.i.i.epil") (Operand.reg "%conv3.i.i609.i.i"),
          Instr.binop "%add4.i.i617.i.i.epil" (BinOp.add) 128 (Operand.reg "%mul.i.i616.i.i.epil") (Operand.reg "%carry.029.i.i613.i.i.epil"),
          Instr.trunc "%conv5.i.i618.i.i.epil" 128 64 (Operand.reg "%add4.i.i617.i.i.epil"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i618.i.i.epil") (Operand.reg "%arrayidx.i.i614.i.i.epil"),
          Instr.binop "%shr.i.i619.i.i.epil" (BinOp.lshr) 128 (Operand.reg "%add4.i.i617.i.i.epil") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i.i620.i.i.epil" (BinOp.add) 64 (Operand.reg "%indvars.iv.i.i612.i.i.epil") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.binop "%epil.iter1077.next" (BinOp.add) 64 (Operand.reg "%epil.iter1077") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.icmp "%epil.iter1077.cmp.not" (IPred.eq) 64 (Operand.reg "%epil.iter1077.next") (Operand.reg "%xtraiter1076")], Term.condbr (Operand.reg "%epil.iter1077.cmp.not") "while.cond.preheader.i.i622.i.i.epilog-lcssa" "for.body.i.i611.i.i.epil"⟩ := by decide

theorem numFast_findBlock_while_cond_preheader_i_i622_i_i_epilog_lcssa :
    numFastBody.findBlock "while.cond.preheader.i.i622.i.i.epilog-lcssa" = some ⟨"while.cond.preheader.i.i622.i.i.epilog-lcssa", [
          Instr.trunc "%extract.t1096" 128 64 (Operand.reg "%shr.i.i619.i.i.epil")], Term.br "while.cond.preheader.i.i622.i.i"⟩ := by decide

theorem numFast_findBlock_while_cond_preheader_i_i622_i_i :
    numFastBody.findBlock "while.cond.preheader.i.i622.i.i" = some ⟨"while.cond.preheader.i.i622.i.i", [
          Instr.phi "%add4.i.i617.i.i.lcssa" (Ty.int 128) [("while.cond.preheader.i.i622.i.i.unr-lcssa", (Operand.reg "%add4.i.i617.i.i.lcssa.ph")),
                                       ("while.cond.preheader.i.i622.i.i.epilog-lcssa", (Operand.reg "%add4.i.i617.i.i.epil"))],
          Instr.phi "%shr.i.i619.i.i.lcssa.off0" (Ty.int 64) [("while.cond.preheader.i.i622.i.i.unr-lcssa", (Operand.reg "%shr.i.i619.i.i.lcssa.ph.off0")),
                                       ("while.cond.preheader.i.i622.i.i.epilog-lcssa", (Operand.reg "%extract.t1096"))],
          Instr.icmp "%tobool.not31.i.i623.i.i" (IPred.ult) 128 (Operand.reg "%add4.i.i617.i.i.lcssa") (Operand.imm (Const.int 128 0x00000000000000010000000000000000#128))], Term.condbr (Operand.reg "%tobool.not31.i.i623.i.i") "if.end195.i.i" "while.body.us.i.i624.i.i"⟩ := by decide

theorem numFast_findBlock_while_body_us_i_i624_i_i :
    numFastBody.findBlock "while.body.us.i.i624.i.i" = some ⟨"while.body.us.i.i624.i.i", [
          Instr.binop "%inc12.us.i.i626.i.i" (BinOp.add) 32 (Operand.reg "%116") (Operand.imm (Const.int 32 0x00000001#32)),
          Instr.gep "%arrayidx14.us.i.i627.i.i" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%wide.trip.count.i.i610.i.i"),
          Instr.store (Ty.int 64) (Operand.reg "%shr.i.i619.i.i.lcssa.off0") (Operand.reg "%arrayidx14.us.i.i627.i.i"),
          Instr.store (Ty.int 32) (Operand.reg "%inc12.us.i.i626.i.i") (Operand.reg "%n.i.i.i")], Term.br "if.end195.i.i"⟩ := by decide

theorem numFast_findBlock_for_body_i_i611_i_i :
    numFastBody.findBlock "for.body.i.i611.i.i" = some ⟨"for.body.i.i611.i.i", [
          Instr.phi "%indvars.iv.i.i612.i.i" (Ty.int 64) [("for.body.lr.ph.i.i608.i.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i.i611.i.i", (Operand.reg "%indvars.iv.next.i.i620.i.i.3"))],
          Instr.phi "%carry.029.i.i613.i.i" (Ty.int 128) [("for.body.lr.ph.i.i608.i.i.new", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
                                       ("for.body.i.i611.i.i", (Operand.reg "%shr.i.i619.i.i.3"))],
          Instr.phi "%niter1082" (Ty.int 64) [("for.body.lr.ph.i.i608.i.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i.i611.i.i", (Operand.reg "%niter1082.next.3"))],
          Instr.gep "%arrayidx.i.i614.i.i" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.i.i612.i.i"),
          Instr.load "%120" (Ty.int 64) (Operand.reg "%arrayidx.i.i614.i.i"),
          Instr.zext "%conv2.i.i615.i.i" 64 128 (Operand.reg "%120"),
          Instr.binop "%mul.i.i616.i.i" (BinOp.mul) 128 (Operand.reg "%conv2.i.i615.i.i") (Operand.reg "%conv3.i.i609.i.i"),
          Instr.binop "%add4.i.i617.i.i" (BinOp.add) 128 (Operand.reg "%mul.i.i616.i.i") (Operand.reg "%carry.029.i.i613.i.i"),
          Instr.trunc "%conv5.i.i618.i.i" 128 64 (Operand.reg "%add4.i.i617.i.i"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i618.i.i") (Operand.reg "%arrayidx.i.i614.i.i"),
          Instr.binop "%shr.i.i619.i.i" (BinOp.lshr) 128 (Operand.reg "%add4.i.i617.i.i") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i.i620.i.i" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i612.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.gep "%arrayidx.i.i614.i.i.1" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.next.i.i620.i.i"),
          Instr.load "%121" (Ty.int 64) (Operand.reg "%arrayidx.i.i614.i.i.1"),
          Instr.zext "%conv2.i.i615.i.i.1" 64 128 (Operand.reg "%121"),
          Instr.binop "%mul.i.i616.i.i.1" (BinOp.mul) 128 (Operand.reg "%conv2.i.i615.i.i.1") (Operand.reg "%conv3.i.i609.i.i"),
          Instr.binop "%add4.i.i617.i.i.1" (BinOp.add) 128 (Operand.reg "%mul.i.i616.i.i.1") (Operand.reg "%shr.i.i619.i.i"),
          Instr.trunc "%conv5.i.i618.i.i.1" 128 64 (Operand.reg "%add4.i.i617.i.i.1"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i618.i.i.1") (Operand.reg "%arrayidx.i.i614.i.i.1"),
          Instr.binop "%shr.i.i619.i.i.1" (BinOp.lshr) 128 (Operand.reg "%add4.i.i617.i.i.1") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i.i620.i.i.1" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i612.i.i") (Operand.imm (Const.int 64 0x0000000000000002#64)),
          Instr.gep "%arrayidx.i.i614.i.i.2" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.next.i.i620.i.i.1"),
          Instr.load "%122" (Ty.int 64) (Operand.reg "%arrayidx.i.i614.i.i.2"),
          Instr.zext "%conv2.i.i615.i.i.2" 64 128 (Operand.reg "%122"),
          Instr.binop "%mul.i.i616.i.i.2" (BinOp.mul) 128 (Operand.reg "%conv2.i.i615.i.i.2") (Operand.reg "%conv3.i.i609.i.i"),
          Instr.binop "%add4.i.i617.i.i.2" (BinOp.add) 128 (Operand.reg "%mul.i.i616.i.i.2") (Operand.reg "%shr.i.i619.i.i.1"),
          Instr.trunc "%conv5.i.i618.i.i.2" 128 64 (Operand.reg "%add4.i.i617.i.i.2"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i618.i.i.2") (Operand.reg "%arrayidx.i.i614.i.i.2"),
          Instr.binop "%shr.i.i619.i.i.2" (BinOp.lshr) 128 (Operand.reg "%add4.i.i617.i.i.2") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i.i620.i.i.2" (BinOp.or) 64 (Operand.reg "%indvars.iv.i.i612.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
          Instr.gep "%arrayidx.i.i614.i.i.3" (Ty.int 64) (Operand.reg "%v.i.i") (Operand.reg "%indvars.iv.next.i.i620.i.i.2"),
          Instr.load "%123" (Ty.int 64) (Operand.reg "%arrayidx.i.i614.i.i.3"),
          Instr.zext "%conv2.i.i615.i.i.3" 64 128 (Operand.reg "%123"),
          Instr.binop "%mul.i.i616.i.i.3" (BinOp.mul) 128 (Operand.reg "%conv2.i.i615.i.i.3") (Operand.reg "%conv3.i.i609.i.i"),
          Instr.binop "%add4.i.i617.i.i.3" (BinOp.add) 128 (Operand.reg "%mul.i.i616.i.i.3") (Operand.reg "%shr.i.i619.i.i.2"),
          Instr.trunc "%conv5.i.i618.i.i.3" 128 64 (Operand.reg "%add4.i.i617.i.i.3"),
          Instr.store (Ty.int 64) (Operand.reg "%conv5.i.i618.i.i.3") (Operand.reg "%arrayidx.i.i614.i.i.3"),
          Instr.binop "%shr.i.i619.i.i.3" (BinOp.lshr) 128 (Operand.reg "%add4.i.i617.i.i.3") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
          Instr.binop "%indvars.iv.next.i.i620.i.i.3" (BinOp.add) 64 (Operand.reg "%indvars.iv.i.i612.i.i") (Operand.imm (Const.int 64 0x0000000000000004#64)),
          Instr.binop "%niter1082.next.3" (BinOp.add) 64 (Operand.reg "%niter1082") (Operand.imm (Const.int 64 0x0000000000000004#64)),
          Instr.icmp "%niter1082.ncmp.3" (IPred.eq) 64 (Operand.reg "%niter1082.next.3") (Operand.reg "%unroll_iter1081")], Term.condbr (Operand.reg "%niter1082.ncmp.3") "while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit" "for.body.i.i611.i.i"⟩ := by decide

theorem numFast_findBlock_if_end195_i_i :
    numFastBody.findBlock "if.end195.i.i" = some ⟨"if.end195.i.i", [
          Instr.store (Ty.int 64) (Operand.imm (Const.int 64 0x0000000000000000#64)) (Operand.reg "%S128.i.i")], Term.br "if.end198.i.i"⟩ := by decide

theorem numFast_findBlock_if_end198_i_i :
    numFastBody.findBlock "if.end198.i.i" = some ⟨"if.end198.i.i", [
          Instr.binop "%reass.sub" (BinOp.sub) 64 (Operand.reg "%add110.i.i") (Operand.reg "%topn.0711.i.i"),
          Instr.binop "%sub200.i.i" (BinOp.add) 64 (Operand.reg "%reass.sub") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.uitofp "%conv202.i.i" 64 (Operand.reg "%top.0709.i.i")], Term.br "while.cond203.i.i"⟩ := by decide

theorem numFast_findBlock_while_cond203_i_i :
    numFastBody.findBlock "while.cond203.i.i" = some ⟨"while.cond203.i.i", [
          Instr.phi "%e10.0.i.i" (Ty.int 64) [("if.end198.i.i", (Operand.reg "%sub200.i.i")),
                                       ("while.body206.i.i", (Operand.reg "%sub219.i.i"))],
          Instr.phi "%d201.0.i.i" Ty.double [("if.end198.i.i", (Operand.reg "%conv202.i.i")),
                                       ("while.body206.i.i", (Operand.reg "%mul217.i.i"))],
          Instr.icmp "%cmp204.i.i" (IPred.sgt) 64 (Operand.reg "%e10.0.i.i") (Operand.imm (Const.int 64 0x0000000000000000#64))], Term.condbr (Operand.reg "%cmp204.i.i") "while.body206.i.i" "while.cond229.i.i.preheader"⟩ := by decide

theorem numFast_findBlock_while_body206_i_i :
    numFastBody.findBlock "while.body206.i.i" = some ⟨"while.body206.i.i", [
          Instr.icmp "%124.min" (IPred.ult) 64 (Operand.reg "%e10.0.i.i") (Operand.imm (Const.int 64 0x0000000000000016#64)),
          Instr.select "%124" (Ty.int 64) (Operand.reg "%124.min") (Operand.reg "%e10.0.i.i") (Operand.imm (Const.int 64 0x0000000000000016#64)),
          Instr.gep "%arrayidx216.i.i" Ty.double (Operand.global "@NUMF_EL1_POW10") (Operand.reg "%124"),
          Instr.load "%125" Ty.double (Operand.reg "%arrayidx216.i.i"),
          Instr.fmul "%mul217.i.i" (Operand.reg "%d201.0.i.i") (Operand.reg "%125"),
          Instr.binop "%sub219.i.i" (BinOp.sub) 64 (Operand.reg "%e10.0.i.i") (Operand.reg "%124"),
          Instr.bitcastToInt "%.cast.i.i.i" (Operand.reg "%mul217.i.i"),
          Instr.icmp "%cmp221.i.i" (IPred.ugt) 64 (Operand.reg "%.cast.i.i.i") (Operand.imm (Const.int 64 0x7fefffffffffffff#64))], Term.condbr (Operand.reg "%cmp221.i.i") "while.cond229.i.i.preheader" "while.cond203.i.i"⟩ := by decide

theorem numFast_findBlock_while_cond229_i_i_preheader :
    numFastBody.findBlock "while.cond229.i.i.preheader" = some ⟨"while.cond229.i.i.preheader", [
          Instr.phi "%e10.2.i.i.ph" (Ty.int 64) [("while.cond203.i.i", (Operand.reg "%e10.0.i.i")),
                                       ("while.body206.i.i", (Operand.reg "%sub219.i.i"))],
          Instr.phi "%d201.2.i.i.ph" Ty.double [("while.cond203.i.i", (Operand.reg "%d201.0.i.i")),
                                       ("while.body206.i.i", (Operand.reg "%mul217.i.i"))]], Term.br "while.cond229.i.i"⟩ := by decide

theorem numFast_findBlock_while_cond229_i_i :
    numFastBody.findBlock "while.cond229.i.i" = some ⟨"while.cond229.i.i", [
          Instr.phi "%e10.2.i.i" (Ty.int 64) [("while.body232.i.i", (Operand.reg "%add245.i.i")),
                                       ("while.cond229.i.i.preheader", (Operand.reg "%e10.2.i.i.ph"))],
          Instr.phi "%d201.2.i.i" Ty.double [("while.body232.i.i", (Operand.reg "%div.i.i")),
                                       ("while.cond229.i.i.preheader", (Operand.reg "%d201.2.i.i.ph"))],
          Instr.icmp "%cmp230.i.i" (IPred.slt) 64 (Operand.reg "%e10.2.i.i") (Operand.imm (Const.int 64 0x0000000000000000#64))], Term.condbr (Operand.reg "%cmp230.i.i") "while.body232.i.i" "while.end253.i.i"⟩ := by decide

theorem numFast_findBlock_while_body232_i_i :
    numFastBody.findBlock "while.body232.i.i" = some ⟨"while.body232.i.i", [
          Instr.icmp "%cmp234.i.i" (IPred.ult) 64 (Operand.reg "%e10.2.i.i") (Operand.imm (Const.int 64 0xffffffffffffffea#64)),
          Instr.binop "%.neg.i.i" (BinOp.mul) 64 (Operand.reg "%e10.2.i.i") (Operand.imm (Const.int 64 0xffffffff00000000#64)),
          Instr.binop "%126" (BinOp.ashr) 64 (Operand.reg "%.neg.i.i") (Operand.imm (Const.int 64 0x0000000000000020#64)),
          Instr.select "%idxprom242.i.i" (Ty.int 64) (Operand.reg "%cmp234.i.i") (Operand.imm (Const.int 64 0x0000000000000016#64)) (Operand.reg "%126"),
          Instr.gep "%arrayidx243.i.i" Ty.double (Operand.global "@NUMF_EL1_POW10") (Operand.reg "%idxprom242.i.i"),
          Instr.load "%127" Ty.double (Operand.reg "%arrayidx243.i.i"),
          Instr.fdiv "%div.i.i" (Operand.reg "%d201.2.i.i") (Operand.reg "%127"),
          Instr.binop "%add245.i.i" (BinOp.add) 64 (Operand.reg "%idxprom242.i.i") (Operand.reg "%e10.2.i.i"),
          Instr.fcmp "%cmp246.i.i" (FPred.oeq) (Operand.reg "%div.i.i") (Operand.imm (Const.float 0x0000000000000000#64))], Term.condbr (Operand.reg "%cmp246.i.i") "while.end253.i.i" "while.cond229.i.i"⟩ := by decide

theorem numFast_findBlock_while_end253_i_i :
    numFastBody.findBlock "while.end253.i.i" = some ⟨"while.end253.i.i", [
          Instr.phi "%d201.3.i.i" Ty.double [("while.body232.i.i", (Operand.reg "%div.i.i")),
                                       ("while.cond229.i.i", (Operand.reg "%d201.2.i.i"))],
          Instr.bitcastToInt "%.cast.i629.i.i" (Operand.reg "%d201.3.i.i")], Term.br "for.cond255.i.i"⟩ := by decide

theorem numFast_findBlock_for_cond255_i_i :
    numFastBody.findBlock "for.cond255.i.i" = some ⟨"for.cond255.i.i", [
          Instr.phi "%b.0.i.i" (Ty.int 64) [("while.end253.i.i", (Operand.reg "%.cast.i629.i.i")),
                                       ("for.cond255.i.i.backedge", (Operand.reg "%b.0.i.i.be"))],
          Instr.icmp "%cmp256.i.i" (IPred.eq) 64 (Operand.reg "%b.0.i.i") (Operand.imm (Const.int 64 0x0000000000000000#64))], Term.condbr (Operand.reg "%cmp256.i.i") "if.then258.i.i" "if.end264.i.i"⟩ := by decide

theorem numFast_findBlock_if_then258_i_i :
    numFastBody.findBlock "if.then258.i.i" = some ⟨"if.then258.i.i", [
          Instr.call "%call259.i.i" (Ty.int 32) "stk_cmp" [(Ty.ptr, (Operand.reg "%v.i.i")),
                             ((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000001#64))),
                             ((Ty.int 64), (Operand.imm (Const.int 64 0xfffffffffffffbcd#64)))],
          Instr.icmp "%cmp260.i.i" (IPred.sgt) 32 (Operand.reg "%call259.i.i") (Operand.imm (Const.int 32 0x00000000#32))], Term.condbr (Operand.reg "%cmp260.i.i") "for.cond255.i.i.backedge" "for.end359.i.i"⟩ := by decide

theorem numFast_findBlock_if_end264_i_i :
    numFastBody.findBlock "if.end264.i.i" = some ⟨"if.end264.i.i", [
          Instr.icmp "%cmp265.i.i" (IPred.ugt) 64 (Operand.reg "%b.0.i.i") (Operand.imm (Const.int 64 0x7fefffffffffffff#64))], Term.condbr (Operand.reg "%cmp265.i.i") "if.then267.i.i" "if.end273.i.i"⟩ := by decide

theorem numFast_findBlock_if_then267_i_i :
    numFastBody.findBlock "if.then267.i.i" = some ⟨"if.then267.i.i", [
          Instr.call "%call268.i.i" (Ty.int 32) "stk_cmp" [(Ty.ptr, (Operand.reg "%v.i.i")),
                             ((Ty.int 64), (Operand.imm (Const.int 64 0x003fffffffffffff#64))),
                             ((Ty.int 64), (Operand.imm (Const.int 64 0x00000000000003ca#64)))],
          Instr.icmp "%cmp269.i.i" (IPred.slt) 32 (Operand.reg "%call268.i.i") (Operand.imm (Const.int 32 0x00000000#32))], Term.condbr (Operand.reg "%cmp269.i.i") "for.cond255.i.i.backedge" "for.end359.i.i"⟩ := by decide

theorem numFast_findBlock_if_end273_i_i :
    numFastBody.findBlock "if.end273.i.i" = some ⟨"if.end273.i.i", [
          Instr.binop "%shr.i.i" (BinOp.lshr) 64 (Operand.reg "%b.0.i.i") (Operand.imm (Const.int 64 0x0000000000000034#64)),
          Instr.icmp "%cmp275.i.i" (IPred.ult) 64 (Operand.reg "%b.0.i.i") (Operand.imm (Const.int 64 0x0010000000000000#64)),
          Instr.binop "%and280.i.i" (BinOp.and) 64 (Operand.reg "%b.0.i.i") (Operand.imm (Const.int 64 0x000fffffffffffff#64)),
          Instr.binop "%or.i.i" (BinOp.or) 64 (Operand.reg "%and280.i.i") (Operand.imm (Const.int 64 0x0010000000000000#64)),
          Instr.select "%cond282.i.i" (Ty.int 64) (Operand.reg "%cmp275.i.i") (Operand.reg "%b.0.i.i") (Operand.reg "%or.i.i"),
          Instr.binop "%sub288.i.i" (BinOp.add) 64 (Operand.reg "%shr.i.i") (Operand.imm (Const.int 64 0xfffffffffffffbcd#64)),
          Instr.select "%cond290.i.i" (Ty.int 64) (Operand.reg "%cmp275.i.i") (Operand.imm (Const.int 64 0xfffffffffffffbce#64)) (Operand.reg "%sub288.i.i"),
          Instr.call "%call291.i.i" (Ty.int 32) "stk_cmp" [(Ty.ptr, (Operand.reg "%v.i.i")),
                             ((Ty.int 64), (Operand.reg "%cond282.i.i")),
                             ((Ty.int 64), (Operand.reg "%cond290.i.i"))],
          Instr.icmp "%cmp292.i.i" (IPred.eq) 32 (Operand.reg "%call291.i.i") (Operand.imm (Const.int 32 0x00000000#32))], Term.condbr (Operand.reg "%cmp292.i.i") "for.end359.i.i" "if.end295.i.i"⟩ := by decide

theorem numFast_findBlock_if_end295_i_i :
    numFastBody.findBlock "if.end295.i.i" = some ⟨"if.end295.i.i", [
          Instr.icmp "%cmp296.i.i" (IPred.sgt) 32 (Operand.reg "%call291.i.i") (Operand.imm (Const.int 32 0x00000000#32))], Term.condbr (Operand.reg "%cmp296.i.i") "if.then298.i.i" "if.end318.i.i"⟩ := by decide

theorem numFast_findBlock_if_then298_i_i :
    numFastBody.findBlock "if.then298.i.i" = some ⟨"if.then298.i.i", [
          Instr.binop "%mul299.i.i" (BinOp.shl) 64 (Operand.reg "%cond282.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.binop "%add300.i.i" (BinOp.or) 64 (Operand.reg "%mul299.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.binop "%sub301.i.i" (BinOp.add) 64 (Operand.reg "%cond290.i.i") (Operand.imm (Const.int 64 0xffffffffffffffff#64)),
          Instr.call "%call302.i.i" (Ty.int 32) "stk_cmp" [(Ty.ptr, (Operand.reg "%v.i.i")),
                             ((Ty.int 64), (Operand.reg "%add300.i.i")),
                             ((Ty.int 64), (Operand.reg "%sub301.i.i"))],
          Instr.icmp "%cmp303.i.i" (IPred.slt) 32 (Operand.reg "%call302.i.i") (Operand.imm (Const.int 32 0x00000000#32))], Term.condbr (Operand.reg "%cmp303.i.i") "for.end359.i.i" "if.end306.i.i"⟩ := by decide

theorem numFast_findBlock_if_end306_i_i :
    numFastBody.findBlock "if.end306.i.i" = some ⟨"if.end306.i.i", [
          Instr.icmp "%cmp307.i.i" (IPred.eq) 32 (Operand.reg "%call302.i.i") (Operand.imm (Const.int 32 0x00000000#32))], Term.condbr (Operand.reg "%cmp307.i.i") "if.then309.i.i" "if.end315.i.i"⟩ := by decide

theorem numFast_findBlock_if_then309_i_i :
    numFastBody.findBlock "if.then309.i.i" = some ⟨"if.then309.i.i", [
          Instr.binop "%and310.i.i" (BinOp.and) 64 (Operand.reg "%cond282.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.binop "%spec.select507.i.i" (BinOp.add) 64 (Operand.reg "%and310.i.i") (Operand.reg "%b.0.i.i")], Term.br "for.end359.i.i"⟩ := by decide

theorem numFast_findBlock_if_end315_i_i :
    numFastBody.findBlock "if.end315.i.i" = some ⟨"if.end315.i.i", [
          Instr.binop "%inc316.i.i" (BinOp.add) 64 (Operand.reg "%b.0.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64))], Term.br "for.cond255.i.i.backedge"⟩ := by decide

theorem numFast_findBlock_if_end318_i_i :
    numFastBody.findBlock "if.end318.i.i" = some ⟨"if.end318.i.i", [
          Instr.icmp "%cmp322.i.i" (IPred.ugt) 64 (Operand.reg "%cond282.i.i") (Operand.imm (Const.int 64 0x0010000000000000#64)),
          Instr.binop "%or.cond391.i.i" (BinOp.or) 1 (Operand.reg "%cmp275.i.i") (Operand.reg "%cmp322.i.i")], Term.condbr (Operand.reg "%or.cond391.i.i") "if.then324.i.i" "if.else328.i.i"⟩ := by decide

theorem numFast_findBlock_if_then324_i_i :
    numFastBody.findBlock "if.then324.i.i" = some ⟨"if.then324.i.i", [
          Instr.binop "%mul325.i.i" (BinOp.shl) 64 (Operand.reg "%cond282.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.binop "%sub326.i.i" (BinOp.add) 64 (Operand.reg "%mul325.i.i") (Operand.imm (Const.int 64 0xffffffffffffffff#64)),
          Instr.binop "%sub327.i.i" (BinOp.add) 64 (Operand.reg "%cond290.i.i") (Operand.imm (Const.int 64 0xffffffffffffffff#64))], Term.br "if.end335.i.i"⟩ := by decide

theorem numFast_findBlock_if_else328_i_i :
    numFastBody.findBlock "if.else328.i.i" = some ⟨"if.else328.i.i", [
          Instr.icmp "%cmp329.i.i" (IPred.eq) 64 (Operand.reg "%shr.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.binop "%sub333.i.i" (BinOp.add) 64 (Operand.reg "%shr.i.i") (Operand.imm (Const.int 64 0xfffffffffffffbcb#64)),
          Instr.select "%spec.select511.i.i" (Ty.int 64) (Operand.reg "%cmp329.i.i") (Operand.imm (Const.int 64 0x001fffffffffffff#64)) (Operand.imm (Const.int 64 0x003fffffffffffff#64)),
          Instr.select "%spec.select512.i.i" (Ty.int 64) (Operand.reg "%cmp329.i.i") (Operand.imm (Const.int 64 0xfffffffffffffbcd#64)) (Operand.reg "%sub333.i.i")], Term.br "if.end335.i.i"⟩ := by decide

theorem numFast_findBlock_if_end335_i_i :
    numFastBody.findBlock "if.end335.i.i" = some ⟨"if.end335.i.i", [
          Instr.phi "%J.0.i.i" (Ty.int 64) [("if.then324.i.i", (Operand.reg "%sub326.i.i")),
                                       ("if.else328.i.i", (Operand.reg "%spec.select511.i.i"))],
          Instr.phi "%eB.0.i.i" (Ty.int 64) [("if.then324.i.i", (Operand.reg "%sub327.i.i")),
                                       ("if.else328.i.i", (Operand.reg "%spec.select512.i.i"))],
          Instr.call "%call336.i.i" (Ty.int 32) "stk_cmp" [(Ty.ptr, (Operand.reg "%v.i.i")),
                             ((Ty.int 64), (Operand.reg "%J.0.i.i")),
                             ((Ty.int 64), (Operand.reg "%eB.0.i.i"))],
          Instr.icmp "%cmp337.i.i" (IPred.sgt) 32 (Operand.reg "%call336.i.i") (Operand.imm (Const.int 32 0x00000000#32))], Term.condbr (Operand.reg "%cmp337.i.i") "for.end359.i.i" "if.end340.i.i"⟩ := by decide

theorem numFast_findBlock_if_end340_i_i :
    numFastBody.findBlock "if.end340.i.i" = some ⟨"if.end340.i.i", [
          Instr.icmp "%cmp341.i.i" (IPred.eq) 32 (Operand.reg "%call336.i.i") (Operand.imm (Const.int 32 0x00000000#32))], Term.condbr (Operand.reg "%cmp341.i.i") "if.then343.i.i" "if.end348.i.i"⟩ := by decide

theorem numFast_findBlock_if_then343_i_i :
    numFastBody.findBlock "if.then343.i.i" = some ⟨"if.then343.i.i", [
          Instr.binop "%128" (BinOp.and) 64 (Operand.reg "%cond282.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
          Instr.binop "%spec.select508.i.i" (BinOp.sub) 64 (Operand.reg "%b.0.i.i") (Operand.reg "%128")], Term.br "for.end359.i.i"⟩ := by decide

theorem numFast_findBlock_if_end348_i_i :
    numFastBody.findBlock "if.end348.i.i" = some ⟨"if.end348.i.i", [
          Instr.binop "%dec349.i.i" (BinOp.add) 64 (Operand.reg "%b.0.i.i") (Operand.imm (Const.int 64 0xffffffffffffffff#64))], Term.br "for.cond255.i.i.backedge"⟩ := by decide

theorem numFast_findBlock_for_cond255_i_i_backedge :
    numFastBody.findBlock "for.cond255.i.i.backedge" = some ⟨"for.cond255.i.i.backedge", [
          Instr.phi "%b.0.i.i.be" (Ty.int 64) [("if.then258.i.i", (Operand.imm (Const.int 64 0x0000000000000001#64))),
                                       ("if.then267.i.i", (Operand.imm (Const.int 64 0x7fefffffffffffff#64))),
                                       ("if.end315.i.i", (Operand.reg "%inc316.i.i")),
                                       ("if.end348.i.i", (Operand.reg "%dec349.i.i"))]], Term.br "for.cond255.i.i"⟩ := by decide

theorem numFast_findBlock_for_end359_i_i :
    numFastBody.findBlock "for.end359.i.i" = some ⟨"for.end359.i.i", [
          Instr.phi "%b.6.i.i" (Ty.int 64) [("if.then343.i.i", (Operand.reg "%spec.select508.i.i")),
                                       ("if.then309.i.i", (Operand.reg "%spec.select507.i.i")),
                                       ("if.end273.i.i", (Operand.reg "%b.0.i.i")),
                                       ("if.then298.i.i", (Operand.reg "%b.0.i.i")),
                                       ("if.end335.i.i", (Operand.reg "%b.0.i.i")),
                                       ("if.then267.i.i", (Operand.imm (Const.int 64 0x7ff0000000000000#64))),
                                       ("if.then258.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
          Instr.bitcastToDouble "%.cast.i630.i.i" (Operand.reg "%b.6.i.i"),
          Instr.fneg "%fneg363.i.i" (Operand.reg "%.cast.i630.i.i"),
          Instr.select "%cond366.i.i" Ty.double (Operand.reg "%cmp1.i") (Operand.reg "%fneg363.i.i") (Operand.reg "%.cast.i630.i.i"),
          Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000620#64))),
                             (Ty.ptr, (Operand.reg "%v.i.i"))]], Term.br "if.end291"⟩ := by decide

theorem numFast_findBlock_if_end291 :
    numFastBody.findBlock "if.end291" = some ⟨"if.end291", [
          Instr.phi "%retval.1.i.i" Ty.double [("if.then59.i.i", (Operand.reg "%cond.i.i")),
                                       ("if.then123.i.i", (Operand.reg "%cond125.i.i")),
                                       ("for.end359.i.i", (Operand.reg "%cond366.i.i")),
                                       ("if.then113.i.i", (Operand.reg "%spec.select694.i.i"))],
          Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000300#64))),
                             (Ty.ptr, (Operand.reg "%dig.i.i"))],
          Instr.store Ty.double (Operand.reg "%retval.1.i.i") (Operand.reg "%out")], Term.br "cleanup300"⟩ := by decide

theorem numFast_findBlock_cleanup300 :
    numFastBody.findBlock "cleanup300" = some ⟨"cleanup300", numFastCleanup300Instrs, Term.ret (Ty.int 32) (some (Operand.reg "%retval.8"))⟩ := by decide


/-! ### The instruction lists, projected from the pins -/

theorem numFastEntryInstrs_eq :
    (numFastBody.findBlock "entry").map (·.instrs) = some numFastEntryInstrs := by decide

theorem numFastLandLhsTrueInstrs_eq :
    (numFastBody.findBlock "land.lhs.true").map (·.instrs) = some numFastLandLhsTrueInstrs := by decide

theorem numFastIfEndInstrs_eq :
    (numFastBody.findBlock "if.end").map (·.instrs) = some numFastIfEndInstrs := by decide

theorem numFastIfThen5Instrs_eq :
    (numFastBody.findBlock "if.then5").map (·.instrs) = some numFastIfThen5Instrs := by decide

theorem numFastIfEnd6Instrs_eq :
    (numFastBody.findBlock "if.end6").map (·.instrs) = some numFastIfEnd6Instrs := by decide

theorem numFastIfElseInstrs_eq :
    (numFastBody.findBlock "if.else").map (·.instrs) = some numFastIfElseInstrs := by decide

theorem numFastLandLhsTrue41Instrs_eq :
    (numFastBody.findBlock "land.lhs.true41").map (·.instrs) = some numFastLandLhsTrue41Instrs := by decide

theorem numFastWhileBody52Instrs_eq :
    (numFastBody.findBlock "while.body52").map (·.instrs) = some numFastWhileBody52Instrs := by decide

theorem numFastIfThen55Instrs_eq :
    (numFastBody.findBlock "if.then55").map (·.instrs) = some numFastIfThen55Instrs := by decide

theorem numFastIfEnd62Instrs_eq :
    (numFastBody.findBlock "if.end62").map (·.instrs) = some numFastIfEnd62Instrs := by decide

theorem numFastIfElse66Instrs_eq :
    (numFastBody.findBlock "if.else66").map (·.instrs) = some numFastIfElse66Instrs := by decide

theorem numFastIfEnd68Instrs_eq :
    (numFastBody.findBlock "if.end68").map (·.instrs) = some numFastIfEnd68Instrs := by decide

theorem numFastIfEnd230Instrs_eq :
    (numFastBody.findBlock "if.end230").map (·.instrs) = some numFastIfEnd230Instrs := by decide

theorem numFastCleanup300Instrs_eq :
    (numFastBody.findBlock "cleanup300").map (·.instrs) = some numFastCleanup300Instrs := by decide


/-! ### Axiom footprints

The pins are kernel computations, so they rest on nothing: `decide` on a closed
literal is `rfl` at the reducer.  The instrument is `#print axioms`; a
declaration proved with `sorry` prints `sorryAx` under the same command, which
is the control §7.6 records. -/

/-- info: 'LeanLLVM.Refinement.numFast_findBlock_land_lhs_true41' does not depend on any axioms -/
#guard_msgs in
#print axioms numFast_findBlock_land_lhs_true41

/-- info: 'LeanLLVM.Refinement.numFastLandLhsTrue41Instrs_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms numFastLandLhsTrue41Instrs_eq

end LeanLLVM.Refinement
