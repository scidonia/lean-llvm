/-
`od_gap_recover`'s emitted body, pinned whole: the AST the fixture parses to.

`JsonStage2HelperOdGap` states the model — `gapRecoverWrite`'s rule, the case
table, the `Calls` entry and its post — and pins the C text the rule encodes.
Nothing there reads the *emitted* body: the helper is a plain `static void` in
`kernel/json/stage2.c`, the certified walk fixture inlines it, and only the
additive entry keeps it a call (`stage2-noevent.candidate.ll:1201`).  This module
pins the emitted body the way `JsonStage2HelperIROdScalar` pins
`od_scalar_value`: the literal below is the parser's own result written out, and
the `#guard` beneath it asserts that parsing the fixture returns exactly this.

The literal is generated from the parse rather than copied from the text —

    nix develop -c bash probes/install/ir/capture-stage2-helpers.sh --emit-pins od_gap_recover

— so a regeneration that drifts from the fixture fails the build rather than
pinning a body the text no longer has.

**What the fixture is.**  The helper's own `define` block, captured from the same
emission `capture-stage2.sh` takes the walk from — `noinline` on every helper,
the measured compiler line, `opt -passes=lower-switch`, and the walk's token strip
— with the source transform extended to this function: the source spells it
`static void`, so clang inlines it at the measured line and the capture marks it
`noinline` as it marks the other helpers.  SROA drops the token pointer's dead
fields, so the emission's argument list is the additive entry's declaration
exactly, `(ptr %c, i64 %t.0.val)`.

**The three rewrites.**  The capture's own, recorded in
`probes/install/ir/stage2.helpers.tsv` and refused there if the emission stops
carrying them:

* the one `llvm.umin.i64` unfolds to its `icmp ult`/`select` pair — the
  fragment's unsigned minimum is `i32` at two registers — which is the literal
  compare's bound `min(len, literal length)`;
* each refusal site's message word stores the site's tag (`i64 1` number, `2`
  literal, `3` scalar, `4` extra token) where the text stores the address of its
  `err_set` literal.  Nothing loads the word (the no-event derivation's rewrite
  r6), the model records which site ran, and the tag numbers are the model's own
  `gapTagNumber`, `gapTagLiteral`, `gapTagScalar` and `gapTagExtra`;
* the literal compare selects among `@.str.17`, `@.str.18` and `@.str.19` in a
  `phi ptr`, and a global constant is neither a declaration `parseModule` reads
  nor a symbol a lone `define` assembles against.  The three addresses are
  appended pointer parameters, `%littrue`, `%litfalse` and `%litnull`, and the
  capture ties each phi edge to the module's own constant text before it
  substitutes, so a renumbered emission is refused rather than silently mapped
  to the wrong literal.  The staging supplies the three addresses and the bytes
  they hold; nothing in the body's arms changes.

The callee and the two lifetime intrinsics are declared after the body so the
fixture assembles and verifies on its own.

**What the pin establishes, and what it does not.**  It establishes the relation
between the committed text and the AST: `firstFunction odGapRecoverSrc` is
`some odGapRecoverBody`, so every block, instruction and immediate the body has
is a line of the file beside it.  The mutation controls show the equality is
about the text rather than a search that would accept anything: the tag control
changes one site's tag, and the offset control changes the `e` field's GEP.
It does not establish that the compiled object executes this text: that step is
the derivation in `capture-stage2-helpers.sh`, outside the kernel, as it is for
every captured unit in the tree.

**The relation to the model.**  `JsonStage2HelperIROdGapSteps` pins this body's
blocks and states the instruction and terminator steps a run proof is written in;
no theorem there runs the body, and nothing in either module relates it to
`stage2GapRecover`.  The transcription-to-instructions distance is therefore the
one `docs/contract.md` §7.6 records for this helper, unchanged: this module says
the committed text parses to the AST below, and the body's runs at the call
boundary remain owed.
-/
import LeanLLVM.Refinement.JsonStage2HelperIR
import LeanLLVM.Refinement.JsonStage2HelperOdGap

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM

/-! ### The fixture -/

/-- `@od_gap_recover`, from `probes/install/ir/stage2.helper.od_gap_recover.ll`. -/
def odGapRecoverSrc : String :=
  include_str "../../probes/install/ir/stage2.helper.od_gap_recover.ll"

/-! #### The body, as the fixture parses -/

/-- `@od_gap_recover`, as `probes/install/ir/stage2.helper.od_gap_recover.ll`
parses.  Generated from the parse by
`capture-stage2-helpers.sh --emit-pins od_gap_recover`; the `#guard` below is
what holds it to the fixture. -/
def odGapRecoverBody : Function :=
{ name := "od_gap_recover",
  retTy := Ty.void,
  params := [("%c", Ty.ptr),
             ("%t.0.val", (Ty.int 64)),
             ("%littrue", Ty.ptr),
             ("%litfalse", Ty.ptr),
             ("%litnull", Ty.ptr)],
  blocks := [
    { name := "entry",
      instrs := [
        Instr.alloca "%d" Ty.double 0,
        Instr.alloca "%ei" (Ty.int 64) 0,
        Instr.load "%0" Ty.ptr (Operand.reg "%c"),
        Instr.gep "%k" (Ty.int 8) (Operand.reg "%c") (Operand.imm (Const.int 64 0x0000000000000020#64)),
        Instr.load "%1" (Ty.int 64) (Operand.reg "%k"),
        Instr.gep "%nix" (Ty.int 8) (Operand.reg "%c") (Operand.imm (Const.int 64 0x0000000000000018#64)),
        Instr.load "%2" (Ty.int 64) (Operand.reg "%nix"),
        Instr.icmp "%cmp" (IPred.ult) 64 (Operand.reg "%1") (Operand.reg "%2")
      ],
      term := Term.condbr (Operand.reg "%cmp") "cond.true" "cond.false" },
    { name := "cond.true",
      instrs := [
        Instr.gep "%ix" (Ty.int 8) (Operand.reg "%c") (Operand.imm (Const.int 64 0x0000000000000010#64)),
        Instr.load "%3" Ty.ptr (Operand.reg "%ix"),
        Instr.gep "%arrayidx" (Ty.int 32) (Operand.reg "%3") (Operand.reg "%1"),
        Instr.load "%4" (Ty.int 32) (Operand.reg "%arrayidx"),
        Instr.zext "%conv" 32 64 (Operand.reg "%4")
      ],
      term := Term.br "cond.end" },
    { name := "cond.false",
      instrs := [
        Instr.gep "%n" (Ty.int 8) (Operand.reg "%c") (Operand.imm (Const.int 64 0x0000000000000008#64)),
        Instr.load "%5" (Ty.int 64) (Operand.reg "%n")
      ],
      term := Term.br "cond.end" },
    { name := "cond.end",
      instrs := [
        Instr.phi "%cond" (Ty.int 64) [("cond.true", (Operand.reg "%conv")),
                                       ("cond.false", (Operand.reg "%5"))],
        Instr.icmp "%cmp310" (IPred.ult) 64 (Operand.reg "%t.0.val") (Operand.reg "%cond")
      ],
      term := Term.condbr (Operand.reg "%cmp310") "land.rhs" "while.end" },
    { name := "land.rhs",
      instrs := [
        Instr.phi "%ee.011" (Ty.int 64) [("while.body", (Operand.reg "%inc")),
                                       ("cond.end", (Operand.reg "%t.0.val"))],
        Instr.gep "%arrayidx5" (Ty.int 8) (Operand.reg "%0") (Operand.reg "%ee.011"),
        Instr.load "%6" (Ty.int 8) (Operand.reg "%arrayidx5")
      ],
      term := Term.br "NodeBlock5" },
    { name := "NodeBlock5",
      instrs := [
        Instr.icmp "%Pivot6" (IPred.slt) 8 (Operand.reg "%6") (Operand.imm (Const.int 8 0x0d#8))
      ],
      term := Term.condbr (Operand.reg "%Pivot6") "LeafBlock" "NodeBlock" },
    { name := "NodeBlock",
      instrs := [
        Instr.icmp "%Pivot" (IPred.slt) 8 (Operand.reg "%6") (Operand.imm (Const.int 8 0x20#8))
      ],
      term := Term.condbr (Operand.reg "%Pivot") "LeafBlock1" "LeafBlock3" },
    { name := "LeafBlock3",
      instrs := [
        Instr.icmp "%SwitchLeaf4" (IPred.eq) 8 (Operand.reg "%6") (Operand.imm (Const.int 8 0x20#8))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf4") "while.end" "while.body" },
    { name := "LeafBlock1",
      instrs := [
        Instr.icmp "%SwitchLeaf2" (IPred.eq) 8 (Operand.reg "%6") (Operand.imm (Const.int 8 0x0d#8))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf2") "while.end" "while.body" },
    { name := "LeafBlock",
      instrs := [
        Instr.binop "%.off" (BinOp.add) 8 (Operand.reg "%6") (Operand.imm (Const.int 8 0xf7#8)),
        Instr.icmp "%SwitchLeaf" (IPred.ule) 8 (Operand.reg "%.off") (Operand.imm (Const.int 8 0x01#8))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf") "while.end" "while.body" },
    { name := "while.body",
      instrs := [
        Instr.binop "%inc" (BinOp.add) 64 (Operand.reg "%ee.011") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%exitcond.not" (IPred.eq) 64 (Operand.reg "%inc") (Operand.reg "%cond")
      ],
      term := Term.condbr (Operand.reg "%exitcond.not") "cleanup82" "land.rhs" },
    { name := "while.end",
      instrs := [
        Instr.phi "%ee.0.lcssa" (Ty.int 64) [("cond.end", (Operand.reg "%t.0.val")),
                                       ("LeafBlock", (Operand.reg "%ee.011")),
                                       ("LeafBlock1", (Operand.reg "%ee.011")),
                                       ("LeafBlock3", (Operand.reg "%ee.011"))],
        Instr.icmp "%cmp6" (IPred.eq) 64 (Operand.reg "%ee.0.lcssa") (Operand.reg "%cond")
      ],
      term := Term.condbr (Operand.reg "%cmp6") "cleanup82" "if.end" },
    { name := "if.end",
      instrs := [
        Instr.gep "%arrayidx9" (Ty.int 8) (Operand.reg "%0") (Operand.reg "%t.0.val"),
        Instr.load "%7" (Ty.int 8) (Operand.reg "%arrayidx9"),
        Instr.icmp "%cmp11" (IPred.eq) 8 (Operand.reg "%7") (Operand.imm (Const.int 8 0x2d#8)),
        Instr.binop "%8" (BinOp.add) 8 (Operand.reg "%7") (Operand.imm (Const.int 8 0xd0#8)),
        Instr.icmp "%or.cond" (IPred.ult) 8 (Operand.reg "%8") (Operand.imm (Const.int 8 0x0a#8)),
        Instr.binop "%or.cond127" (BinOp.or) 1 (Operand.reg "%cmp11") (Operand.reg "%or.cond")
      ],
      term := Term.condbr (Operand.reg "%or.cond127") "if.then19" "if.else" },
    { name := "if.then19",
      instrs := [
        Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000008#64))),
                             (Ty.ptr, (Operand.reg "%d"))],
        Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000008#64))),
                             (Ty.ptr, (Operand.reg "%ei"))],
        Instr.binop "%sub" (BinOp.sub) 64 (Operand.reg "%ee.0.lcssa") (Operand.reg "%t.0.val"),
        Instr.call "%call23" (Ty.int 32) "num_fast_el1" [(Ty.ptr, (Operand.reg "%arrayidx9")),
                             ((Ty.int 64), (Operand.reg "%sub")),
                             (Ty.ptr, (Operand.reg "%d")),
                             (Ty.ptr, (Operand.reg "%ei"))],
        Instr.icmp "%tobool24.not.not" (IPred.eq) 32 (Operand.reg "%call23") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%tobool24.not.not") "if.then25" "if.end67.critedge" },
    { name := "if.then25",
      instrs := [
        Instr.gep "%e" (Ty.int 8) (Operand.reg "%c") (Operand.imm (Const.int 64 0x0000000000000458#64)),
        Instr.load "%9" Ty.ptr (Operand.reg "%e"),
        Instr.load "%10" (Ty.int 64) (Operand.reg "%ei"),
        Instr.binop "%add" (BinOp.add) 64 (Operand.reg "%10") (Operand.reg "%t.0.val"),
        Instr.store (Ty.int 32) (Operand.imm (Const.int 32 0x00000000#32)) (Operand.reg "%9"),
        Instr.gep "%off1.i" (Ty.int 8) (Operand.reg "%9") (Operand.imm (Const.int 64 0x0000000000000008#64)),
        Instr.store (Ty.int 64) (Operand.reg "%add") (Operand.reg "%off1.i"),
        Instr.gep "%msg2.i" (Ty.int 8) (Operand.reg "%9") (Operand.imm (Const.int 64 0x0000000000000010#64)),
        Instr.store (Ty.int 64) (Operand.imm (Const.int 64 0x0000000000000001#64)) (Operand.reg "%msg2.i"),
        Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000008#64))),
                             (Ty.ptr, (Operand.reg "%ei"))],
        Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000008#64))),
                             (Ty.ptr, (Operand.reg "%d"))]
      ],
      term := Term.br "cleanup82" },
    { name := "if.else",
      instrs := [

      ],
      term := Term.br "NodeBlock15" },
    { name := "NodeBlock15",
      instrs := [
        Instr.icmp "%Pivot16" (IPred.slt) 8 (Operand.reg "%7") (Operand.imm (Const.int 8 0x6e#8))
      ],
      term := Term.condbr (Operand.reg "%Pivot16") "LeafBlock7" "NodeBlock13" },
    { name := "NodeBlock13",
      instrs := [
        Instr.icmp "%Pivot14" (IPred.slt) 8 (Operand.reg "%7") (Operand.imm (Const.int 8 0x74#8))
      ],
      term := Term.condbr (Operand.reg "%Pivot14") "LeafBlock9" "LeafBlock11" },
    { name := "LeafBlock11",
      instrs := [
        Instr.icmp "%SwitchLeaf12" (IPred.eq) 8 (Operand.reg "%7") (Operand.imm (Const.int 8 0x74#8))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf12") "if.end48" "if.else43" },
    { name := "LeafBlock9",
      instrs := [
        Instr.icmp "%SwitchLeaf10" (IPred.eq) 8 (Operand.reg "%7") (Operand.imm (Const.int 8 0x6e#8))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf10") "if.then42" "if.else43" },
    { name := "LeafBlock7",
      instrs := [
        Instr.icmp "%SwitchLeaf8" (IPred.eq) 8 (Operand.reg "%7") (Operand.imm (Const.int 8 0x66#8))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf8") "if.then37" "if.else43" },
    { name := "if.then37",
      instrs := [

      ],
      term := Term.br "if.end48" },
    { name := "if.then42",
      instrs := [

      ],
      term := Term.br "if.end48" },
    { name := "if.else43",
      instrs := [
        Instr.gep "%e44" (Ty.int 8) (Operand.reg "%c") (Operand.imm (Const.int 64 0x0000000000000458#64)),
        Instr.load "%11" Ty.ptr (Operand.reg "%e44"),
        Instr.store (Ty.int 32) (Operand.imm (Const.int 32 0x00000000#32)) (Operand.reg "%11"),
        Instr.gep "%off1.i129" (Ty.int 8) (Operand.reg "%11") (Operand.imm (Const.int 64 0x0000000000000008#64)),
        Instr.store (Ty.int 64) (Operand.reg "%t.0.val") (Operand.reg "%off1.i129"),
        Instr.gep "%msg2.i130" (Ty.int 8) (Operand.reg "%11") (Operand.imm (Const.int 64 0x0000000000000010#64)),
        Instr.store (Ty.int 64) (Operand.imm (Const.int 64 0x0000000000000003#64)) (Operand.reg "%msg2.i130")
      ],
      term := Term.br "cleanup82" },
    { name := "if.end48",
      instrs := [
        Instr.phi "%lit.0" Ty.ptr [("if.then37", (Operand.reg "%litfalse")),
                                       ("if.then42", (Operand.reg "%litnull")),
                                       ("LeafBlock11", (Operand.reg "%littrue"))],
        Instr.phi "%ln.0" (Ty.int 64) [("if.then37", (Operand.imm (Const.int 64 0x0000000000000005#64))),
                                       ("if.then42", (Operand.imm (Const.int 64 0x0000000000000004#64))),
                                       ("LeafBlock11", (Operand.imm (Const.int 64 0x0000000000000004#64)))],
        Instr.binop "%sub54" (BinOp.sub) 64 (Operand.reg "%ee.0.lcssa") (Operand.reg "%t.0.val"),
        Instr.icmp "%cond.i.min" (IPred.ult) 64 (Operand.reg "%sub54") (Operand.reg "%ln.0"),
        Instr.select "%cond.i" (Ty.int 64) (Operand.reg "%cond.i.min") (Operand.reg "%sub54") (Operand.reg "%ln.0"),
        Instr.icmp "%cmp3.not28.not.i" (IPred.eq) 64 (Operand.reg "%ee.0.lcssa") (Operand.reg "%t.0.val")
      ],
      term := Term.condbr (Operand.reg "%cmp3.not28.not.i") "for.end.i" "for.body.i" },
    { name := "for.body.i",
      instrs := [
        Instr.phi "%i.029.i" (Ty.int 64) [("for.inc.i", (Operand.reg "%inc.i")),
                                       ("if.end48", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.gep "%arrayidx.i" (Ty.int 8) (Operand.reg "%arrayidx9") (Operand.reg "%i.029.i"),
        Instr.load "%12" (Ty.int 8) (Operand.reg "%arrayidx.i"),
        Instr.gep "%arrayidx6.i" (Ty.int 8) (Operand.reg "%lit.0") (Operand.reg "%i.029.i"),
        Instr.load "%13" (Ty.int 8) (Operand.reg "%arrayidx6.i"),
        Instr.icmp "%cmp8.not.i" (IPred.eq) 8 (Operand.reg "%12") (Operand.reg "%13")
      ],
      term := Term.condbr (Operand.reg "%cmp8.not.i") "for.inc.i" "if.then57" },
    { name := "for.inc.i",
      instrs := [
        Instr.binop "%inc.i" (BinOp.add) 64 (Operand.reg "%i.029.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%exitcond.not.i" (IPred.eq) 64 (Operand.reg "%inc.i") (Operand.reg "%cond.i")
      ],
      term := Term.condbr (Operand.reg "%exitcond.not.i") "for.end.i" "for.body.i" },
    { name := "for.end.i",
      instrs := [
        Instr.icmp "%cmp11.not.i" (IPred.eq) 64 (Operand.reg "%sub54") (Operand.reg "%ln.0")
      ],
      term := Term.condbr (Operand.reg "%cmp11.not.i") "if.end67" "if.then57" },
    { name := "if.then57",
      instrs := [
        Instr.phi "%ei49.0.ph" (Ty.int 64) [("for.end.i", (Operand.reg "%cond.i")),
                                       ("for.body.i", (Operand.reg "%i.029.i"))],
        Instr.gep "%e58" (Ty.int 8) (Operand.reg "%c") (Operand.imm (Const.int 64 0x0000000000000458#64)),
        Instr.load "%14" Ty.ptr (Operand.reg "%e58"),
        Instr.binop "%add60" (BinOp.add) 64 (Operand.reg "%ei49.0.ph") (Operand.reg "%t.0.val"),
        Instr.store (Ty.int 32) (Operand.imm (Const.int 32 0x00000000#32)) (Operand.reg "%14"),
        Instr.gep "%off1.i131" (Ty.int 8) (Operand.reg "%14") (Operand.imm (Const.int 64 0x0000000000000008#64)),
        Instr.store (Ty.int 64) (Operand.reg "%add60") (Operand.reg "%off1.i131"),
        Instr.gep "%msg2.i132" (Ty.int 8) (Operand.reg "%14") (Operand.imm (Const.int 64 0x0000000000000010#64)),
        Instr.store (Ty.int 64) (Operand.imm (Const.int 64 0x0000000000000002#64)) (Operand.reg "%msg2.i132")
      ],
      term := Term.br "cleanup82" },
    { name := "if.end67.critedge",
      instrs := [
        Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000008#64))),
                             (Ty.ptr, (Operand.reg "%ei"))],
        Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000008#64))),
                             (Ty.ptr, (Operand.reg "%d"))]
      ],
      term := Term.br "if.end67" },
    { name := "if.end67",
      instrs := [
        Instr.icmp "%cmp6919" (IPred.ult) 64 (Operand.reg "%ee.0.lcssa") (Operand.reg "%cond")
      ],
      term := Term.condbr (Operand.reg "%cmp6919") "land.rhs71" "while.end78" },
    { name := "land.rhs71",
      instrs := [
        Instr.phi "%s2.020" (Ty.int 64) [("while.body76", (Operand.reg "%inc77")),
                                       ("if.end67", (Operand.reg "%ee.0.lcssa"))],
        Instr.gep "%arrayidx72" (Ty.int 8) (Operand.reg "%0") (Operand.reg "%s2.020"),
        Instr.load "%15" (Ty.int 8) (Operand.reg "%arrayidx72")
      ],
      term := Term.br "NodeBlock26" },
    { name := "NodeBlock26",
      instrs := [
        Instr.icmp "%Pivot27" (IPred.slt) 8 (Operand.reg "%15") (Operand.imm (Const.int 8 0x0d#8))
      ],
      term := Term.condbr (Operand.reg "%Pivot27") "LeafBlock17" "NodeBlock24" },
    { name := "NodeBlock24",
      instrs := [
        Instr.icmp "%Pivot25" (IPred.slt) 8 (Operand.reg "%15") (Operand.imm (Const.int 8 0x20#8))
      ],
      term := Term.condbr (Operand.reg "%Pivot25") "LeafBlock20" "LeafBlock22" },
    { name := "LeafBlock22",
      instrs := [
        Instr.icmp "%SwitchLeaf23" (IPred.eq) 8 (Operand.reg "%15") (Operand.imm (Const.int 8 0x20#8))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf23") "while.body76" "while.end78" },
    { name := "LeafBlock20",
      instrs := [
        Instr.icmp "%SwitchLeaf21" (IPred.eq) 8 (Operand.reg "%15") (Operand.imm (Const.int 8 0x0d#8))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf21") "while.body76" "while.end78" },
    { name := "LeafBlock17",
      instrs := [
        Instr.binop "%.off18" (BinOp.add) 8 (Operand.reg "%15") (Operand.imm (Const.int 8 0xf7#8)),
        Instr.icmp "%SwitchLeaf19" (IPred.ule) 8 (Operand.reg "%.off18") (Operand.imm (Const.int 8 0x01#8))
      ],
      term := Term.condbr (Operand.reg "%SwitchLeaf19") "while.body76" "while.end78" },
    { name := "while.body76",
      instrs := [
        Instr.binop "%inc77" (BinOp.add) 64 (Operand.reg "%s2.020") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%exitcond24.not" (IPred.eq) 64 (Operand.reg "%inc77") (Operand.reg "%cond")
      ],
      term := Term.condbr (Operand.reg "%exitcond24.not") "while.end78" "land.rhs71" },
    { name := "while.end78",
      instrs := [
        Instr.phi "%s2.0.lcssa" (Ty.int 64) [("if.end67", (Operand.reg "%ee.0.lcssa")),
                                       ("while.body76", (Operand.reg "%cond")),
                                       ("LeafBlock17", (Operand.reg "%s2.020")),
                                       ("LeafBlock20", (Operand.reg "%s2.020")),
                                       ("LeafBlock22", (Operand.reg "%s2.020"))],
        Instr.gep "%e79" (Ty.int 8) (Operand.reg "%c") (Operand.imm (Const.int 64 0x0000000000000458#64)),
        Instr.load "%16" Ty.ptr (Operand.reg "%e79"),
        Instr.store (Ty.int 32) (Operand.imm (Const.int 32 0x00000000#32)) (Operand.reg "%16"),
        Instr.gep "%off1.i137" (Ty.int 8) (Operand.reg "%16") (Operand.imm (Const.int 64 0x0000000000000008#64)),
        Instr.store (Ty.int 64) (Operand.reg "%s2.0.lcssa") (Operand.reg "%off1.i137"),
        Instr.gep "%msg2.i138" (Ty.int 8) (Operand.reg "%16") (Operand.imm (Const.int 64 0x0000000000000010#64)),
        Instr.store (Ty.int 64) (Operand.imm (Const.int 64 0x0000000000000004#64)) (Operand.reg "%msg2.i138")
      ],
      term := Term.br "cleanup82" },
    { name := "cleanup82",
      instrs := [

      ],
      term := Term.ret Ty.void none }] }

-- Parsing the fixture returns the pinned body.
#guard decide (firstFunction odGapRecoverSrc = some odGapRecoverBody)

/-! #### The pin's controls

Two one-word mutations of the fixture: the number site's tag (`i64 1` → `i64 2`)
and the cursor's `e` field (`i64 1112` → `i64 1113`).  Each parses, and neither
is the pinned body, so the equality above is about the text rather than about a
search that would accept either. -/
def odGapRecoverTagMutated : String :=
  odGapRecoverSrc.replace "store i64 1, ptr %msg2.i" "store i64 2, ptr %msg2.i"

def odGapRecoverOffsetMutated : String :=
  odGapRecoverSrc.replace
    "getelementptr inbounds i8, ptr %c, i64 1112" "getelementptr inbounds i8, ptr %c, i64 1113"

#guard parses odGapRecoverTagMutated
#guard decide (firstFunction odGapRecoverTagMutated ≠ some odGapRecoverBody)
#guard parses odGapRecoverOffsetMutated
#guard decide (firstFunction odGapRecoverOffsetMutated ≠ some odGapRecoverBody)

/-! #### The shape the capture records

`stage2.helpers.tsv`'s row for this symbol states 40 blocks, 110 parsed
instructions and five parameters (the two the entry passes and the three staged
literal pointers).  The literal above implies the counts; they are read here in
the inventory's own vocabulary so that the row and the pin are one statement. -/
#guard decide
  ((odGapRecoverBody.name, odGapRecoverBody.blocks.length,
      (odGapRecoverBody.blocks.flatMap (·.instrs)).length,
      odGapRecoverBody.params.length) =
    ("od_gap_recover", 40, 110, 5))

/-! #### The cursor's offsets, and the record's sites

The model reads the cursor's six fields at `odGapCurN` (8), `odGapCurIx` (16),
`odGapCurNix` (24), `odGapCurK` (32) and `odGapCurE` (1112), with `b` at zero
read as a pointer word.  The fixture's GEPs are those addresses, and the controls
above and below show the markers discriminate. -/
#guard odGapCurN = 8 ∧ odGapCurIx = 16 ∧ odGapCurNix = 24 ∧ odGapCurK = 32 ∧
  odGapCurE = 1112
#guard occurs odGapRecoverSrc "  %0 = load ptr, ptr %c\n"
#guard occurs odGapRecoverSrc "getelementptr inbounds i8, ptr %c, i64 8\n"
#guard occurs odGapRecoverSrc "getelementptr inbounds i8, ptr %c, i64 16\n"
#guard occurs odGapRecoverSrc "getelementptr inbounds i8, ptr %c, i64 24\n"
#guard occurs odGapRecoverSrc "getelementptr inbounds i8, ptr %c, i64 32\n"
#guard occurs odGapRecoverSrc "getelementptr inbounds i8, ptr %c, i64 1112\n"
-- The controls: the same searches on one-word mutations report absence.
#guard !occurs odGapRecoverSrc "getelementptr inbounds i8, ptr %c, i64 1113\n"
#guard !occurs odGapRecoverSrc "  %0 = load ptr, ptr %d\n"

/-- The four refusal sites' tag stores, at the record's message word. -/
def gapMsgTagStores (f : Function) : List (BitVec 64) :=
  (f.blocks.flatMap (·.instrs)).filterMap fun i =>
    match i with
    | .store (.int 64) (.imm (.int 64 v)) (.reg r) =>
        if "%msg2.i" == r || "%msg2.i130" == r || "%msg2.i132" == r || "%msg2.i138" == r
        then some v else none
    | _ => none

-- The four sites, by tag: number, scalar, literal and extra token.
#guard decide (gapMsgTagStores odGapRecoverBody =
  [0x0000000000000001#64, 0x0000000000000003#64, 0x0000000000000002#64,
   0x0000000000000004#64])

-- The tag numbers are the model's own.
#guard gapTagNumber = 1 ∧ gapTagLiteral = 2 ∧ gapTagScalar = 3 ∧ gapTagExtra = 4

-- The control: the same read on the tag-mutated fixture does not find the
-- number site's tag where the pinned body has it.
#guard (match firstFunction odGapRecoverTagMutated with
  | some f => gapMsgTagStores f ≠ gapMsgTagStores odGapRecoverBody
  | none => false)

-- The literal compare selects its three literals through the staged parameters,
-- one edge each, and the tag stores are the only `i64` stores to the record's
-- message word.
#guard occurs odGapRecoverSrc
  "  %lit.0 = phi ptr [ %litfalse, %if.then37 ], [ %litnull, %if.then42 ], [ %littrue, %LeafBlock11 ]\n"
#guard occurs odGapRecoverSrc "store i64 1, ptr %msg2.i\n"
#guard occurs odGapRecoverSrc "store i64 3, ptr %msg2.i130\n"
#guard occurs odGapRecoverSrc "store i64 2, ptr %msg2.i132\n"
#guard occurs odGapRecoverSrc "store i64 4, ptr %msg2.i138\n"

/-! #### The argument surface

The emission's two arguments are the additive entry's declaration exactly, and
the three staged literal pointers are appended after them. -/
#guard occurs stage2NoEventFixture "declare void @od_gap_recover(ptr %c, i64 %t.0.val)"
#guard occurs odGapRecoverSrc
  "define void @od_gap_recover(ptr %c, i64 %t.0.val, ptr %littrue, ptr %litfalse, ptr %litnull) {\n"
#guard decide (odGapRecoverBody.params.map (fun p => p.2) =
  [(Ty.ptr), (Ty.int 64), (Ty.ptr), (Ty.ptr), (Ty.ptr)])
#guard decide ((odGapRecoverBody.params.map (fun p => p.2)).take 2 =
  [(Ty.ptr), (Ty.int 64)])

-- The two staging objects the body allocates, and the call it makes, are the
-- text's: an `alloca double` conversion slot, an `alloca i64` offset slot, and
-- the number path's `num_fast_el1` call.
#guard occurs odGapRecoverSrc "  %d = alloca double\n"
#guard occurs odGapRecoverSrc "  %ei = alloca i64\n"
#guard occurs odGapRecoverSrc
  "call i32 @num_fast_el1(ptr %arrayidx9, i64 %sub, ptr %d, ptr %ei)"

end LeanLLVM.Refinement
