/-
`od_scalar_value`'s emitted body, pinned whole: the AST the fixture parses to.

`JsonStage2HelperIR` reads `probes/install/ir/stage2.helper.od_scalar_value.ll`
and took the parsed function as the body, stating it by shape: the symbol's
name, 38 blocks, 145 instructions and four parameters, plus one store the
capture's rewrite produces.  A shape pin does not say what any block holds, so
nothing in the tree stated the text this body *is*: an edit to the fixture that
kept the counts would leave every guard true and the body describing text nobody
had read.  This module closes that the way `JsonStage2HelperIRNumFast` closes it
for `num_fast_el1` and `JsonClassifyIR` does for the classifier: the literal
below is the parse written out, and the `#guard` beneath it asserts that parsing
the fixture returns exactly this.

The literal is generated from the parse rather than copied from the text —

    nix develop -c bash probes/install/ir/capture-stage2-helpers.sh --emit-pins od_scalar_value

— so a regeneration that drifts from the fixture fails the build rather than
pinning a body the text no longer has.

**What the fixture is.**  `od_scalar_value`'s own `define` block, captured from
the same emission `capture-stage2.sh` takes the walk from: `noinline` on every
helper except `s2_walk`, the measured compiler line, `opt
-passes=lower-switch`, and the walk's three rewrites — the conversion slot's
`alloca double` becomes the appended pointer parameter `%d`, the refusal
messages become `null`, and the one `llvm.umin.i64` unfolds to its
`icmp`/`select` pair.  `probes/install/ir/stage2.helpers.tsv` records the shape
and the rewrites, and the capture refuses if the emission stops carrying them.

**What the pin establishes, and what it does not.**  It establishes the relation
between the committed text and the AST: `firstFunction odScalarValueSrc` is
`some odScalarValueBody`, so every block, instruction and immediate the body has
is a line of the file beside it, and the mutant control shows the equality is
about the text rather than a search that would accept anything.  It does not
establish that the compiled object executes this text: that step is the
derivation in `capture-stage2-helpers.sh`, outside the kernel, as it is for
every captured unit in the tree.

**The relation to the walk's theorems.**  The walk's obligation does not name
this body.  `Stage2WalkObligation` runs `stage2Body` at `stage2SubCalls`, and
the `od_scalar_value` entry of that selection is
`JsonStage2Body.stage2ScalarValue`, the model of the function's observable at
the call boundary.  What links the two is a contract proof, and that proof is
not here: `s2ScalarValueContract` states the caller-side record of the model,
and its proof of this emitted body is obstructed by the body's `num_fast_el1`
call (`JsonStage2HelperIRNumFast` pins that callee's text; its conversion arm is
open) and by the record chain `outTag`/`emitBlobs` must match byte for byte.  So
the text-to-AST relation is closed here and the AST-to-model relation remains
owed — a proof obligation recorded at `docs/contract.md` §7.6 row e, not a gap
in the pin.
-/
import LeanLLVM.Refinement.JsonStage2HelperIR

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM

/-! ### The body, as the fixture parses -/

/-- `@od_scalar_value`, as
`probes/install/ir/stage2.helper.od_scalar_value.ll` parses.  Generated from the
parse by `capture-stage2-helpers.sh --emit-pins od_scalar_value`; the `#guard`
below is what holds it to the fixture. -/
def odScalarValueBody : Function :=
{ name := "od_scalar_value",
  retTy := (Ty.int 32),
  params := [("%c", Ty.ptr),
             ("%t", Ty.ptr),
             ("%o", Ty.ptr),
             ("%d", Ty.ptr)],
  blocks := [
    { name := "entry",
      instrs := [
        Instr.alloca "%ei" (Ty.int 64) 0,
        Instr.load "%0" Ty.ptr (Operand.reg "%c"),
        Instr.load "%1" (Ty.int 64) (Operand.reg "%t"),
        Instr.gep "%arrayidx" (Ty.int 8) (Operand.reg "%0") (Operand.reg "%1"),
        Instr.gep "%kind" (Ty.int 8) (Operand.reg "%t") (Operand.imm (Const.int 64 0x0000000000000010#64)),
        Instr.load "%2" (Ty.int 32) (Operand.reg "%kind")
      ],
      term := Term.br "NodeBlock" },
    { name := "NodeBlock",
      instrs := [
        Instr.icmp "%Pivot" (IPred.slt) 32 (Operand.reg "%2") (Operand.imm (Const.int 32 0x00000007#32))
      ],
      term := Term.condbr (Operand.reg "%Pivot") "LeafBlock" "LeafBlock1" },
    { name := "LeafBlock1",
      instrs := [
        Instr.icmp "%SwitchLeaf2" (IPred.eq) 32 (Operand.reg "%2") (Operand.imm (Const.int 32 0x00000007#32))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf2") "if.then4" "if.end20" },
    { name := "LeafBlock",
      instrs := [
        Instr.icmp "%SwitchLeaf" (IPred.eq) 32 (Operand.reg "%2") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf") "if.then" "if.end20" },
    { name := "if.then",
      instrs := [
        Instr.gep "%3" (Ty.int 8) (Operand.reg "%c") (Operand.imm (Const.int 64 0x0000000000000458#64)),
        Instr.load "%c.val95" Ty.ptr (Operand.reg "%3"),
        Instr.store (Ty.int 32) (Operand.imm (Const.int 32 0x00000000#32)) (Operand.reg "%c.val95"),
        Instr.gep "%off1.i.i" (Ty.int 8) (Operand.reg "%c.val95") (Operand.imm (Const.int 64 0x0000000000000008#64)),
        Instr.store (Ty.int 64) (Operand.reg "%1") (Operand.reg "%off1.i.i"),
        Instr.gep "%msg2.i.i" (Ty.int 8) (Operand.reg "%c.val95") (Operand.imm (Const.int 64 0x0000000000000010#64)),
        Instr.store Ty.ptr (Operand.imm Const.null) (Operand.reg "%msg2.i.i")
      ],
      term := Term.br "cleanup64" },
    { name := "if.then4",
      instrs := [
        Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000008#64))),
                             (Ty.ptr, (Operand.reg "%d"))],
        Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000008#64))),
                             (Ty.ptr, (Operand.reg "%ei"))],
        Instr.gep "%end" (Ty.int 8) (Operand.reg "%t") (Operand.imm (Const.int 64 0x0000000000000008#64)),
        Instr.load "%4" (Ty.int 64) (Operand.reg "%end"),
        Instr.binop "%sub" (BinOp.sub) 64 (Operand.reg "%4") (Operand.reg "%1"),
        Instr.call "%call8" (Ty.int 32) "num_fast_el1" [(Ty.ptr, (Operand.reg "%arrayidx")),
                             ((Ty.int 64), (Operand.reg "%sub")),
                             (Ty.ptr, (Operand.reg "%d")),
                             (Ty.ptr, (Operand.reg "%ei"))],
        Instr.icmp "%tobool.not" (IPred.eq) 32 (Operand.reg "%call8") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%tobool.not") "if.then9" "if.then14" },
    { name := "if.then9",
      instrs := [
        Instr.load "%5" (Ty.int 64) (Operand.reg "%t"),
        Instr.load "%6" (Ty.int 64) (Operand.reg "%ei"),
        Instr.binop "%add" (BinOp.add) 64 (Operand.reg "%6") (Operand.reg "%5"),
        Instr.gep "%7" (Ty.int 8) (Operand.reg "%c") (Operand.imm (Const.int 64 0x0000000000000458#64)),
        Instr.load "%c.val94" Ty.ptr (Operand.reg "%7"),
        Instr.store (Ty.int 32) (Operand.imm (Const.int 32 0x00000000#32)) (Operand.reg "%c.val94"),
        Instr.gep "%off1.i.i96" (Ty.int 8) (Operand.reg "%c.val94") (Operand.imm (Const.int 64 0x0000000000000008#64)),
        Instr.store (Ty.int 64) (Operand.reg "%add") (Operand.reg "%off1.i.i96"),
        Instr.gep "%msg2.i.i97" (Ty.int 8) (Operand.reg "%c.val94") (Operand.imm (Const.int 64 0x0000000000000010#64)),
        Instr.store Ty.ptr (Operand.imm Const.null) (Operand.reg "%msg2.i.i97")
      ],
      term := Term.br "cleanup" },
    { name := "if.then14",
      instrs := [
        Instr.gep "%hash.i.i" (Ty.int 8) (Operand.reg "%o") (Operand.imm (Const.int 64 0x0000000000000020#64)),
        Instr.load "%8" (Ty.int 32) (Operand.reg "%hash.i.i"),
        Instr.icmp "%tobool.not.i.i" (IPred.eq) 32 (Operand.reg "%8") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%tobool.not.i.i") "if.end.i.i" "if.then.i.i" },
    { name := "if.then.i.i",
      instrs := [
        Instr.gep "%h1.i.i.i" (Ty.int 8) (Operand.reg "%o") (Operand.imm (Const.int 64 0x0000000000000018#64)),
        Instr.load "%9" (Ty.int 64) (Operand.reg "%h1.i.i.i"),
        Instr.binop "%xor.us.i.i.i" (BinOp.xor) 64 (Operand.reg "%9") (Operand.imm (Const.int 64 0x0000000000000007#64)),
        Instr.binop "%10" (BinOp.mul) 64 (Operand.reg "%xor.us.i.i.i") (Operand.imm (Const.int 64 0xdf442d22ce4859b9#64)),
        Instr.binop "%mul11.i.i.i" (BinOp.add) 64 (Operand.reg "%10") (Operand.imm (Const.int 64 0x9e3779b97f4a7c15#64)),
        Instr.store (Ty.int 64) (Operand.reg "%mul11.i.i.i") (Operand.reg "%h1.i.i.i")
      ],
      term := Term.br "out_tag.exit" },
    { name := "if.end.i.i",
      instrs := [
        Instr.gep "%11" (Ty.int 8) (Operand.reg "%o") (Operand.imm (Const.int 64 0x0000000000000008#64)),
        Instr.load "%o.val.i.i" (Ty.int 64) (Operand.reg "%11"),
        Instr.gep "%12" (Ty.int 8) (Operand.reg "%o") (Operand.imm (Const.int 64 0x0000000000000010#64)),
        Instr.load "%o.val11.i.i" (Ty.int 64) (Operand.reg "%12"),
        Instr.binop "%add.i.i.i" (BinOp.add) 64 (Operand.reg "%o.val.i.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%cmp.not.i.i.i" (IPred.ugt) 64 (Operand.reg "%add.i.i.i") (Operand.reg "%o.val11.i.i")
      ],
      term := Term.condbr (Operand.reg "%cmp.not.i.i.i") "if.end.i.i.i" "out_reserve.exit.i.i" },
    { name := "if.end.i.i.i",
      instrs := [
        Instr.callVoid "llvm.trap" []
      ],
      term := Term.unreachable },
    { name := "out_reserve.exit.i.i",
      instrs := [
        Instr.load "%13" Ty.ptr (Operand.reg "%o"),
        Instr.gep "%add.ptr.i.i" (Ty.int 8) (Operand.reg "%13") (Operand.reg "%o.val.i.i"),
        Instr.store (Ty.int 8) (Operand.imm (Const.int 8 0x07#8)) (Operand.reg "%add.ptr.i.i"),
        Instr.load "%14" (Ty.int 64) (Operand.reg "%11"),
        Instr.binop "%add.i.i" (BinOp.add) 64 (Operand.reg "%14") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.store (Ty.int 64) (Operand.reg "%add.i.i") (Operand.reg "%11"),
        Instr.load "%.pre" (Ty.int 32) (Operand.reg "%hash.i.i"),
        Instr.icmp "%15" (IPred.eq) 32 (Operand.reg "%.pre") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.br "out_tag.exit" },
    { name := "out_tag.exit",
      instrs := [
        Instr.phi "%tobool.not.i.i99" (Ty.int 1) [("if.then.i.i", (Operand.imm (Const.int 1 0x0#1))),
                                       ("out_reserve.exit.i.i", (Operand.reg "%15"))],
        Instr.load "%16" (Ty.int 64) (Operand.reg "%d")
      ],
      term := Term.condbr (Operand.reg "%tobool.not.i.i99") "if.end.i.i104" "if.then.i.i100" },
    { name := "if.then.i.i100",
      instrs := [
        Instr.gep "%h1.i.i.i101" (Ty.int 8) (Operand.reg "%o") (Operand.imm (Const.int 64 0x0000000000000018#64)),
        Instr.load "%17" (Ty.int 64) (Operand.reg "%h1.i.i.i101"),
        Instr.binop "%xor.us.i.i.i102" (BinOp.xor) 64 (Operand.reg "%16") (Operand.reg "%17"),
        Instr.binop "%18" (BinOp.mul) 64 (Operand.reg "%xor.us.i.i.i102") (Operand.imm (Const.int 64 0xdf442d22ce4859b9#64)),
        Instr.binop "%mul11.i.i.i103" (BinOp.add) 64 (Operand.reg "%18") (Operand.imm (Const.int 64 0xf1bbcdcbfa53e0a8#64)),
        Instr.store (Ty.int 64) (Operand.reg "%mul11.i.i.i103") (Operand.reg "%h1.i.i.i101")
      ],
      term := Term.br "cleanup" },
    { name := "if.end.i.i104",
      instrs := [
        Instr.gep "%19" (Ty.int 8) (Operand.reg "%o") (Operand.imm (Const.int 64 0x0000000000000008#64)),
        Instr.load "%o.val.i.i105" (Ty.int 64) (Operand.reg "%19"),
        Instr.gep "%20" (Ty.int 8) (Operand.reg "%o") (Operand.imm (Const.int 64 0x0000000000000010#64)),
        Instr.load "%o.val11.i.i106" (Ty.int 64) (Operand.reg "%20"),
        Instr.binop "%add.i.i.i107" (BinOp.add) 64 (Operand.reg "%o.val.i.i105") (Operand.imm (Const.int 64 0x0000000000000008#64)),
        Instr.icmp "%cmp.not.i.i.i108" (IPred.ugt) 64 (Operand.reg "%add.i.i.i107") (Operand.reg "%o.val11.i.i106")
      ],
      term := Term.condbr (Operand.reg "%cmp.not.i.i.i108") "if.end.i.i.i113" "out_reserve.exit.i.i109" },
    { name := "if.end.i.i.i113",
      instrs := [
        Instr.callVoid "llvm.trap" []
      ],
      term := Term.unreachable },
    { name := "out_reserve.exit.i.i109",
      instrs := [
        Instr.load "%21" Ty.ptr (Operand.reg "%o"),
        Instr.gep "%add.ptr.i.i110" (Ty.int 8) (Operand.reg "%21") (Operand.reg "%o.val.i.i105"),
        Instr.store (Ty.int 64) (Operand.reg "%16") (Operand.reg "%add.ptr.i.i110"),
        Instr.load "%22" (Ty.int 64) (Operand.reg "%19"),
        Instr.binop "%add.i.i112" (BinOp.add) 64 (Operand.reg "%22") (Operand.imm (Const.int 64 0x0000000000000008#64)),
        Instr.store (Ty.int 64) (Operand.reg "%add.i.i112") (Operand.reg "%19")
      ],
      term := Term.br "cleanup" },
    { name := "cleanup",
      instrs := [
        Instr.phi "%retval.0" (Ty.int 32) [("if.then9", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("if.then.i.i100", (Operand.imm (Const.int 32 0x00000001#32))),
                                       ("out_reserve.exit.i.i109", (Operand.imm (Const.int 32 0x00000001#32)))],
        Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000008#64))),
                             (Ty.ptr, (Operand.reg "%ei"))],
        Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000008#64))),
                             (Ty.ptr, (Operand.reg "%d"))]
      ],
      term := Term.br "cleanup64" },
    { name := "if.end20",
      instrs := [
        Instr.load "%23" (Ty.int 8) (Operand.reg "%arrayidx")
      ],
      term := Term.br "NodeBlock11" },
    { name := "NodeBlock11",
      instrs := [
        Instr.icmp "%Pivot12" (IPred.slt) 8 (Operand.reg "%23") (Operand.imm (Const.int 8 0x6e#8))
      ],
      term := Term.condbr (Operand.reg "%Pivot12") "LeafBlock3" "NodeBlock9" },
    { name := "NodeBlock9",
      instrs := [
        Instr.icmp "%Pivot10" (IPred.slt) 8 (Operand.reg "%23") (Operand.imm (Const.int 8 0x74#8))
      ],
      term := Term.condbr (Operand.reg "%Pivot10") "LeafBlock5" "LeafBlock7" },
    { name := "LeafBlock7",
      instrs := [
        Instr.icmp "%SwitchLeaf8" (IPred.eq) 8 (Operand.reg "%23") (Operand.imm (Const.int 8 0x74#8))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf8") "if.end39" "if.else34" },
    { name := "LeafBlock5",
      instrs := [
        Instr.icmp "%SwitchLeaf6" (IPred.eq) 8 (Operand.reg "%23") (Operand.imm (Const.int 8 0x6e#8))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf6") "if.then33" "if.else34" },
    { name := "LeafBlock3",
      instrs := [
        Instr.icmp "%SwitchLeaf4" (IPred.eq) 8 (Operand.reg "%23") (Operand.imm (Const.int 8 0x66#8))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf4") "if.then28" "if.else34" },
    { name := "if.then28",
      instrs := [

      ],
      term := Term.br "if.end39" },
    { name := "if.then33",
      instrs := [

      ],
      term := Term.br "if.end39" },
    { name := "if.else34",
      instrs := [
        Instr.gep "%24" (Ty.int 8) (Operand.reg "%c") (Operand.imm (Const.int 64 0x0000000000000458#64)),
        Instr.load "%c.val93" Ty.ptr (Operand.reg "%24"),
        Instr.store (Ty.int 32) (Operand.imm (Const.int 32 0x00000000#32)) (Operand.reg "%c.val93"),
        Instr.gep "%off1.i.i114" (Ty.int 8) (Operand.reg "%c.val93") (Operand.imm (Const.int 64 0x0000000000000008#64)),
        Instr.store (Ty.int 64) (Operand.reg "%1") (Operand.reg "%off1.i.i114"),
        Instr.gep "%msg2.i.i115" (Ty.int 8) (Operand.reg "%c.val93") (Operand.imm (Const.int 64 0x0000000000000010#64)),
        Instr.store Ty.ptr (Operand.imm Const.null) (Operand.reg "%msg2.i.i115")
      ],
      term := Term.br "cleanup64" },
    { name := "if.end39",
      instrs := [
        Instr.phi "%lit.0" Ty.ptr [("if.then28", (Operand.imm Const.null)),
                                       ("if.then33", (Operand.imm Const.null)),
                                       ("LeafBlock7", (Operand.imm Const.null))],
        Instr.phi "%ln.0" (Ty.int 64) [("if.then28", (Operand.imm (Const.int 64 0x0000000000000005#64))),
                                       ("if.then33", (Operand.imm (Const.int 64 0x0000000000000004#64))),
                                       ("LeafBlock7", (Operand.imm (Const.int 64 0x0000000000000004#64)))],
        Instr.phi "%tag.0" (Ty.int 8) [("if.then28", (Operand.imm (Const.int 8 0x09#8))),
                                       ("if.then33", (Operand.imm (Const.int 8 0x0a#8))),
                                       ("LeafBlock7", (Operand.imm (Const.int 8 0x08#8)))],
        Instr.gep "%end44" (Ty.int 8) (Operand.reg "%t") (Operand.imm (Const.int 64 0x0000000000000008#64)),
        Instr.load "%25" (Ty.int 64) (Operand.reg "%end44"),
        Instr.binop "%sub46" (BinOp.sub) 64 (Operand.reg "%25") (Operand.reg "%1"),
        Instr.icmp "%cond.i.min" (IPred.ult) 64 (Operand.reg "%sub46") (Operand.reg "%ln.0"),
        Instr.select "%cond.i" (Ty.int 64) (Operand.reg "%cond.i.min") (Operand.reg "%sub46") (Operand.reg "%ln.0"),
        Instr.icmp "%cmp3.not28.not.i" (IPred.eq) 64 (Operand.reg "%25") (Operand.reg "%1")
      ],
      term := Term.condbr (Operand.reg "%cmp3.not28.not.i") "for.end.i" "for.body.i" },
    { name := "for.body.i",
      instrs := [
        Instr.phi "%i.029.i" (Ty.int 64) [("for.inc.i", (Operand.reg "%inc.i")),
                                       ("if.end39", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.gep "%arrayidx.i" (Ty.int 8) (Operand.reg "%arrayidx") (Operand.reg "%i.029.i"),
        Instr.load "%26" (Ty.int 8) (Operand.reg "%arrayidx.i"),
        Instr.gep "%arrayidx6.i" (Ty.int 8) (Operand.reg "%lit.0") (Operand.reg "%i.029.i"),
        Instr.load "%27" (Ty.int 8) (Operand.reg "%arrayidx6.i"),
        Instr.icmp "%cmp8.not.i" (IPred.eq) 8 (Operand.reg "%26") (Operand.reg "%27")
      ],
      term := Term.condbr (Operand.reg "%cmp8.not.i") "for.inc.i" "if.then49" },
    { name := "for.inc.i",
      instrs := [
        Instr.binop "%inc.i" (BinOp.add) 64 (Operand.reg "%i.029.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%exitcond.not.i" (IPred.eq) 64 (Operand.reg "%inc.i") (Operand.reg "%cond.i")
      ],
      term := Term.condbr (Operand.reg "%exitcond.not.i") "for.end.i" "for.body.i" },
    { name := "for.end.i",
      instrs := [
        Instr.icmp "%cmp11.not.i" (IPred.eq) 64 (Operand.reg "%sub46") (Operand.reg "%ln.0")
      ],
      term := Term.condbr (Operand.reg "%cmp11.not.i") "if.then55" "if.then49" },
    { name := "if.then49",
      instrs := [
        Instr.phi "%ei40.0.ph" (Ty.int 64) [("for.end.i", (Operand.reg "%cond.i")),
                                       ("for.body.i", (Operand.reg "%i.029.i"))],
        Instr.binop "%add51" (BinOp.add) 64 (Operand.reg "%ei40.0.ph") (Operand.reg "%1"),
        Instr.gep "%28" (Ty.int 8) (Operand.reg "%c") (Operand.imm (Const.int 64 0x0000000000000458#64)),
        Instr.load "%c.val" Ty.ptr (Operand.reg "%28"),
        Instr.store (Ty.int 32) (Operand.imm (Const.int 32 0x00000000#32)) (Operand.reg "%c.val"),
        Instr.gep "%off1.i.i117" (Ty.int 8) (Operand.reg "%c.val") (Operand.imm (Const.int 64 0x0000000000000008#64)),
        Instr.store (Ty.int 64) (Operand.reg "%add51") (Operand.reg "%off1.i.i117"),
        Instr.gep "%msg2.i.i118" (Ty.int 8) (Operand.reg "%c.val") (Operand.imm (Const.int 64 0x0000000000000010#64)),
        Instr.store Ty.ptr (Operand.imm Const.null) (Operand.reg "%msg2.i.i118")
      ],
      term := Term.br "cleanup64" },
    { name := "if.then55",
      instrs := [
        Instr.gep "%hash.i.i120" (Ty.int 8) (Operand.reg "%o") (Operand.imm (Const.int 64 0x0000000000000020#64)),
        Instr.load "%29" (Ty.int 32) (Operand.reg "%hash.i.i120"),
        Instr.icmp "%tobool.not.i.i121" (IPred.eq) 32 (Operand.reg "%29") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%tobool.not.i.i121") "if.end.i.i126" "if.then.i.i122" },
    { name := "if.then.i.i122",
      instrs := [
        Instr.gep "%h1.i.i.i123" (Ty.int 8) (Operand.reg "%o") (Operand.imm (Const.int 64 0x0000000000000018#64)),
        Instr.load "%30" (Ty.int 64) (Operand.reg "%h1.i.i.i123"),
        Instr.zext "%conv.i.i.i" 8 64 (Operand.reg "%tag.0"),
        Instr.binop "%xor.us.i.i.i124" (BinOp.xor) 64 (Operand.reg "%30") (Operand.reg "%conv.i.i.i"),
        Instr.binop "%31" (BinOp.mul) 64 (Operand.reg "%xor.us.i.i.i124") (Operand.imm (Const.int 64 0xdf442d22ce4859b9#64)),
        Instr.binop "%mul11.i.i.i125" (BinOp.add) 64 (Operand.reg "%31") (Operand.imm (Const.int 64 0x9e3779b97f4a7c15#64)),
        Instr.store (Ty.int 64) (Operand.reg "%mul11.i.i.i125") (Operand.reg "%h1.i.i.i123")
      ],
      term := Term.br "cleanup64" },
    { name := "if.end.i.i126",
      instrs := [
        Instr.gep "%32" (Ty.int 8) (Operand.reg "%o") (Operand.imm (Const.int 64 0x0000000000000008#64)),
        Instr.load "%o.val.i.i127" (Ty.int 64) (Operand.reg "%32"),
        Instr.gep "%33" (Ty.int 8) (Operand.reg "%o") (Operand.imm (Const.int 64 0x0000000000000010#64)),
        Instr.load "%o.val11.i.i128" (Ty.int 64) (Operand.reg "%33"),
        Instr.binop "%add.i.i.i129" (BinOp.add) 64 (Operand.reg "%o.val.i.i127") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%cmp.not.i.i.i130" (IPred.ugt) 64 (Operand.reg "%add.i.i.i129") (Operand.reg "%o.val11.i.i128")
      ],
      term := Term.condbr (Operand.reg "%cmp.not.i.i.i130") "if.end.i.i.i135" "out_reserve.exit.i.i131" },
    { name := "if.end.i.i.i135",
      instrs := [
        Instr.callVoid "llvm.trap" []
      ],
      term := Term.unreachable },
    { name := "out_reserve.exit.i.i131",
      instrs := [
        Instr.load "%34" Ty.ptr (Operand.reg "%o"),
        Instr.gep "%add.ptr.i.i132" (Ty.int 8) (Operand.reg "%34") (Operand.reg "%o.val.i.i127"),
        Instr.store (Ty.int 8) (Operand.reg "%tag.0") (Operand.reg "%add.ptr.i.i132"),
        Instr.load "%35" (Ty.int 64) (Operand.reg "%32"),
        Instr.binop "%add.i.i134" (BinOp.add) 64 (Operand.reg "%35") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.store (Ty.int 64) (Operand.reg "%add.i.i134") (Operand.reg "%32")
      ],
      term := Term.br "cleanup64" },
    { name := "cleanup64",
      instrs := [
        Instr.phi "%retval.3" (Ty.int 32) [("if.then", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("cleanup", (Operand.reg "%retval.0")),
                                       ("if.else34", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("if.then49", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("if.then.i.i122", (Operand.imm (Const.int 32 0x00000001#32))),
                                       ("out_reserve.exit.i.i131", (Operand.imm (Const.int 32 0x00000001#32)))]
      ],
      term := Term.ret (Ty.int 32) (some (Operand.reg "%retval.3")) }] }

-- Parsing the fixture returns the pinned body.
#guard decide (firstFunction odScalarValueSrc = some odScalarValueBody)

/-! #### The pin's control

`odScalarValueSrcMutated` is the same fixture with the entry dispatch's pivot
changed (`icmp slt i32 %2, 7` → `icmp slt i32 %2, 8`): it parses, and it is not
the pinned body, so the equality above is about the text rather than about a
search that would accept either. -/
def odScalarValueSrcMutated : String :=
  odScalarValueSrc.replace "icmp slt i32 %2, 7" "icmp slt i32 %2, 8"

#guard parses odScalarValueSrcMutated
#guard decide (firstFunction odScalarValueSrcMutated ≠ some odScalarValueBody)

/-! #### The shape the capture records

`stage2.helpers.tsv`'s row for this symbol states 38 blocks, 145 parsed
instructions and four parameters.  The literal above implies the counts; they
are read here in the inventory's own vocabulary so that the row and the pin are
one statement. -/
#guard decide
  ((odScalarValueBody.name, odScalarValueBody.blocks.length,
      (odScalarValueBody.blocks.flatMap (·.instrs)).length,
      odScalarValueBody.params.length) =
    ("od_scalar_value", 38, 145, 4))

-- The refusal path stores the error record's message pointer at offset sixteen,
-- as the capture's `null` rewrite leaves it.
#guard storesNullAt odScalarValueBody "%msg2.i.i"

-- The marker's control, in this run: the same read on a body with no refusal
-- record reports absence.
#guard (match firstFunction s2InitSrc with
  | some f => !storesNullAt f "%msg2.i.i"
  | none => false)

end LeanLLVM.Refinement
