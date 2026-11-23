/-
The table-driven stage-2 candidate's emitted body, pinned, and its obligation.

`probes/install/ir/pipeline/stage2-dfa.candidate.ll` is the body this module
names.  `probes/install/ir/capture-stage2-dfa.sh` records how it is derived:
`kernel/json/stage2_dfa.c` with the included `kernel/json/stage2.c` transformed
(`noinline` on every helper, `sd_walk` forced inline), compiled at the measured
line, switch-lowered, reduced to the one `define` block, stripped, its six
allocas flattened to the record's eight slots, and its three read-only tables
carried in the `cst` slot (classifier at 0, resume table at 256, transition
table at 272).

The parameters are the ABI's thirteen followed by `stage2Args`' eight:
`%d.i %c.i %ctype.i %cst.i %t352.i %s %z %e`.  Six are live (`c`, `ctype`
carrying the DFA stack, `t352` the scalar token, `s`, `z`, `e`); `d` is unused
and `cst` is read only.  That is why `stage2Args` and `WalkScope.Γ_stage2work`
apply to this body unchanged, and why the obligation below is stated at that
record.

`stage2DfaBody` is the parsed fixture written out, and the `#guard`s assert that
the parser returns exactly it, that the declaration count and ABI/staging prefix
are the ones the derivation claims, and that `retsValued` holds.  The AST literal
is generated from the fixture with a one-off emitter over `parseModule`; the pin,
not the emitter, is what the proofs use.

The first helper-call rows are `stage2Dfa_calls`: the call instructions of the
pinned body, their callees and their argument lists, read off the AST.  The
production obligation is `Stage2DfaWalkObligation`; whose proof must supply the
loop invariant `Stage2DfaLoopAgrees` (the `xj`, `z.alen`, `z.ev.len` and `mem`
clauses beside the abstract state and stack already proved in
`JsonStage2DfaRun`).  Neither is proved here.
-/
import LeanLLVM.Refinement.JsonStage2WalkFlushPost
import LeanLLVM.Refinement.JsonStage2DfaRun

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2IR (stage2Calls)
open LeanLLVM.Refinement.WalkScope

/-- The pinned fixture. -/
def dfaSrc : String :=
  include_str "../../probes/install/ir/pipeline/stage2-dfa.candidate.ll"

/-- Parse a fixture and take its single function. -/
def dfaFirstFunction (src : String) : Option Function :=
  match parseModule src with
  | .ok m => m.functions.head?
  | .error _ => none

def stage2DfaBody : Function :=
{ name := "leanllvm_json_stage2_dfa",
  retTy := (Ty.int 64),
  params := [("%b", Ty.ptr), ("%n", (Ty.int 64)), ("%ep", Ty.ptr), ("%nep", (Ty.int 64)), ("%xp", Ty.ptr), ("%nxp", (Ty.int 64)), ("%dst", Ty.ptr), ("%dstcap", (Ty.int 64)), ("%ndst", Ty.ptr), ("%ev", Ty.ptr), ("%evcap", (Ty.int 64)), ("%nev", Ty.ptr), ("%err", Ty.ptr), ("%d.i", Ty.ptr), ("%c.i", Ty.ptr), ("%ctype.i", Ty.ptr), ("%cst.i", Ty.ptr), ("%t352.i", Ty.ptr), ("%s", Ty.ptr), ("%z", Ty.ptr), ("%e", Ty.ptr)],
  blocks := [
{ name := "entry",
    instrs := [
      Instr.alloca "%xj.i" (Ty.int 64) 0,
      Instr.alloca "%outn.i" (Ty.int 64) 0,
      Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (.imm (.int 64 (BitVec.ofNat 64 120)))), (Ty.ptr, (.reg "%s"))],
      Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (.imm (.int 64 (BitVec.ofNat 64 64)))), (Ty.ptr, (.reg "%z"))],
      Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (.imm (.int 64 (BitVec.ofNat 64 24)))), (Ty.ptr, (.reg "%e"))],
      Instr.binop "%add" BinOp.add 64 (.reg "%n") (.imm (.int 64 (BitVec.ofNat 64 63))),
      Instr.binop "%shr" BinOp.lshr 64 (.reg "%add") (.imm (.int 64 (BitVec.ofNat 64 6))),
      Instr.callVoid "s2_init" [(Ty.ptr, (.reg "%s")), (Ty.ptr, (.reg "%b")), ((Ty.int 64), (.reg "%n")), ((Ty.int 64), (.reg "%shr")), (Ty.ptr, (.reg "%ep"))],
      Instr.gep "%hash1.i.i" (Ty.int 8) (.reg "%z") (.imm (.int 64 (BitVec.ofNat 64 32))),
      Instr.gep "%ar" (Ty.int 8) (.reg "%z") (.imm (.int 64 (BitVec.ofNat 64 40))),
      Instr.gep "%0" (Ty.int 8) (.reg "%z") (.imm (.int 64 (BitVec.ofNat 64 24))),
      Instr.callVoid "llvm.memset.p0.i64" [(Ty.ptr, (.reg "%0")), ((Ty.int 8), (.imm (.int 8 (BitVec.ofNat 8 0)))), ((Ty.int 64), (.imm (.int 64 (BitVec.ofNat 64 16)))), ((Ty.int 1), (.imm (.int 1 (BitVec.ofNat 1 0))))],
      Instr.store Ty.ptr (.reg "%dst") (.reg "%ar"),
      Instr.load "%1" (Ty.int 64) (.reg "%ndst"),
      Instr.gep "%alen" (Ty.int 8) (.reg "%z") (.imm (.int 64 (BitVec.ofNat 64 48))),
      Instr.store (Ty.int 64) (.reg "%1") (.reg "%alen"),
      Instr.gep "%acap" (Ty.int 8) (.reg "%z") (.imm (.int 64 (BitVec.ofNat 64 56))),
      Instr.store (Ty.int 64) (.reg "%dstcap") (.reg "%acap"),
      Instr.store Ty.ptr (.reg "%ev") (.reg "%z"),
      Instr.load "%2" (Ty.int 64) (.reg "%nev"),
      Instr.gep "%len" (Ty.int 8) (.reg "%z") (.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (.reg "%2") (.reg "%len"),
      Instr.gep "%cap" (Ty.int 8) (.reg "%z") (.imm (.int 64 (BitVec.ofNat 64 16))),
      Instr.store (Ty.int 64) (.reg "%evcap") (.reg "%cap"),
      Instr.store (Ty.int 32) (.imm (.int 32 (BitVec.ofNat 32 1))) (.reg "%e"),
      Instr.gep "%off" (Ty.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (.imm (.int 64 (BitVec.ofNat 64 0))) (.reg "%off"),
      Instr.gep "%msg" (Ty.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 16))),
      Instr.store Ty.ptr (.imm .null) (.reg "%msg"),
      Instr.load "%3" Ty.ptr (.reg "%s"),
      Instr.gep "%n2.i" (Ty.int 8) (.reg "%s") (.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.load "%4" (Ty.int 64) (.reg "%n2.i"),
      Instr.gep "%ep4.i" (Ty.int 8) (.reg "%s") (.imm (.int 64 (BitVec.ofNat 64 48))),
      Instr.load "%5" Ty.ptr (.reg "%ep4.i"),
      Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (.imm (.int 64 (BitVec.ofNat 64 520)))), (Ty.ptr, (.reg "%ctype.i"))],
      Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (.reg "%xj.i"))],
      Instr.store (Ty.int 64) (.imm (.int 64 (BitVec.ofNat 64 0))) (.reg "%xj.i"),
      Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (.imm (.int 64 (BitVec.ofNat 64 1192)))), (Ty.ptr, (.reg "%c.i"))],
      Instr.gep "%6" (Ty.int 8) (.reg "%c.i") (.imm (.int 64 (BitVec.ofNat 64 32))),
      Instr.callVoid "llvm.memset.p0.i64" [(Ty.ptr, (.reg "%6")), ((Ty.int 8), (.imm (.int 8 (BitVec.ofNat 8 0)))), ((Ty.int 64), (.imm (.int 64 (BitVec.ofNat 64 1160)))), ((Ty.int 1), (.imm (.int 1 (BitVec.ofNat 1 0))))],
      Instr.store Ty.ptr (.reg "%3") (.reg "%c.i"),
      Instr.gep "%n8.i" (Ty.int 8) (.reg "%c.i") (.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.store (Ty.int 64) (.reg "%4") (.reg "%n8.i"),
      Instr.gep "%ix.i" (Ty.int 8) (.reg "%c.i") (.imm (.int 64 (BitVec.ofNat 64 16))),
      Instr.store Ty.ptr (.reg "%5") (.reg "%ix.i"),
      Instr.gep "%nix.i" (Ty.int 8) (.reg "%c.i") (.imm (.int 64 (BitVec.ofNat 64 24))),
      Instr.store (Ty.int 64) (.reg "%nep") (.reg "%nix.i"),
      Instr.gep "%e9.i" (Ty.int 8) (.reg "%c.i") (.imm (.int 64 (BitVec.ofNat 64 1112))),
      Instr.store Ty.ptr (.reg "%e") (.reg "%e9.i"),
      Instr.gep "%invariant.gep" (Ty.int 8) (.reg "%3") (.imm (.int 64 (BitVec.ofNat 64 18446744073709551615))),
      Instr.icmp "%cmp.i153160.not" IPred.eq 64 (.reg "%nep") (.imm (.int 64 (BitVec.ofNat 64 0)))
    ],
    term := Term.condbr (.reg "%cmp.i153160.not") "if.then233.i" "while.body.i.lr.ph.lr.ph" },
{ name := "while.body.i.lr.ph.lr.ph",
    instrs := [
      Instr.gep "%gap.i" (Ty.int 8) (.reg "%t352.i") (.imm (.int 64 (BitVec.ofNat 64 20))),
      Instr.gep "%end.i" (Ty.int 8) (.reg "%t352.i") (.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.gep "%kind174.i" (Ty.int 8) (.reg "%t352.i") (.imm (.int 64 (BitVec.ofNat 64 16))),
      Instr.gep "%k60.i" (Ty.int 8) (.reg "%c.i") (.imm (.int 64 (BitVec.ofNat 64 32))),
      Instr.gep "%h1.i.i.i26" (Ty.int 8) (.reg "%z") (.imm (.int 64 (BitVec.ofNat 64 24)))
    ],
    term := Term.br "while.body.i.lr.ph" },
{ name := "while.body.i.lr.ph",
    instrs := [
      Instr.phi "%sp.0.i.ph163" (Ty.int 32) [("while.body.i.lr.ph.lr.ph", (.imm (.int 32 (BitVec.ofNat 32 0)))), ("while.cond.i.outer.backedge", (.reg "%sp.0.i.ph.be"))],
      Instr.phi "%state.0.i.ph162" (Ty.int 32) [("while.body.i.lr.ph.lr.ph", (.imm (.int 32 (BitVec.ofNat 32 0)))), ("while.cond.i.outer.backedge", (.reg "%state.0.i.ph.be"))],
      Instr.phi "%k.0.i.ph161" (Ty.int 64) [("while.body.i.lr.ph.lr.ph", (.imm (.int 64 (BitVec.ofNat 64 0)))), ("while.cond.i.outer.backedge", (.reg "%inc.i"))]
    ],
    term := Term.br "while.body.i" },
{ name := "while.body.i",
    instrs := [
      Instr.phi "%state.0.i155" (Ty.int 32) [("while.body.i.lr.ph", (.reg "%state.0.i.ph162")), ("while.cond.i.backedge", (.reg "%and.i"))],
      Instr.phi "%k.0.i154" (Ty.int 64) [("while.body.i.lr.ph", (.reg "%k.0.i.ph161")), ("while.cond.i.backedge", (.reg "%k.0.i.be"))],
      Instr.binop "%inc.i" BinOp.add 64 (.reg "%k.0.i154") (.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.gep "%arrayidx.i" (Ty.int 32) (.reg "%5") (.reg "%k.0.i154"),
      Instr.load "%7" (Ty.int 32) (.reg "%arrayidx.i"),
      Instr.zext "%idxprom.i" 32 64 (.reg "%7"),
      Instr.gep "%arrayidx10.i" (Ty.int 8) (.reg "%3") (.reg "%idxprom.i"),
      Instr.load "%8" (Ty.int 8) (.reg "%arrayidx10.i"),
      Instr.zext "%idxprom11.i" 8 64 (.reg "%8"),
      Instr.gep "%arrayidx12.i" (Ty.int 8) (.reg "%cst.i") (.reg "%idxprom11.i"),
      Instr.load "%9" (Ty.int 8) (.reg "%arrayidx12.i"),
      Instr.zext "%idxprom13.i" 32 64 (.reg "%state.0.i155"),
      Instr.zext "%idxprom15.i" 8 64 (.reg "%9"),
      Instr.gep "%cst.tr" (Ty.int 8) (.reg "%cst.i") (.imm (.int 64 (BitVec.ofNat 64 272))),
      Instr.binop "%tr.off" BinOp.shl 64 (.reg "%idxprom13.i") (.imm (.int 64 (BitVec.ofNat 64 3))),
      Instr.gep "%tr.row" (Ty.int 8) (.reg "%cst.tr") (.reg "%tr.off"),
      Instr.gep "%arrayidx16.i" (Ty.int 8) (.reg "%tr.row") (.reg "%idxprom15.i"),
      Instr.load "%10" (Ty.int 8) (.reg "%arrayidx16.i"),
      Instr.zext "%conv17.i" 8 32 (.reg "%10"),
      Instr.binop "%shr.i" BinOp.lshr 32 (.reg "%conv17.i") (.imm (.int 32 (BitVec.ofNat 32 4))),
      Instr.binop "%and.i" BinOp.and 32 (.reg "%conv17.i") (.imm (.int 32 (BitVec.ofNat 32 15)))
    ],
    term := Term.br "NodeBlock7" },
{ name := "NodeBlock7",
    instrs := [
      Instr.icmp "%Pivot8" IPred.slt 32 (.reg "%shr.i") (.imm (.int 32 (BitVec.ofNat 32 5)))
    ],
    term := Term.condbr (.reg "%Pivot8") "NodeBlock1" "NodeBlock5" },
{ name := "NodeBlock5",
    instrs := [
      Instr.icmp "%Pivot6" IPred.slt 32 (.reg "%shr.i") (.imm (.int 32 (BitVec.ofNat 32 6)))
    ],
    term := Term.condbr (.reg "%Pivot6") "sw.bb51.i" "NodeBlock3" },
{ name := "NodeBlock3",
    instrs := [
      Instr.icmp "%Pivot4" IPred.slt 32 (.reg "%shr.i") (.imm (.int 32 (BitVec.ofNat 32 7)))
    ],
    term := Term.condbr (.reg "%Pivot4") "sw.bb115.i" "LeafBlock" },
{ name := "LeafBlock",
    instrs := [
      Instr.icmp "%SwitchLeaf" IPred.eq 32 (.reg "%shr.i") (.imm (.int 32 (BitVec.ofNat 32 7)))
    ],
    term := Term.condbr (.reg "%SwitchLeaf") "if.then.i" "sw.default.i" },
{ name := "NodeBlock1",
    instrs := [
      Instr.icmp "%Pivot2" IPred.slt 32 (.reg "%shr.i") (.imm (.int 32 (BitVec.ofNat 32 1)))
    ],
    term := Term.condbr (.reg "%Pivot2") "while.cond.i.backedge" "NodeBlock" },
{ name := "NodeBlock",
    instrs := [
      Instr.icmp "%Pivot" IPred.slt 32 (.reg "%shr.i") (.imm (.int 32 (BitVec.ofNat 32 3)))
    ],
    term := Term.condbr (.reg "%Pivot") "sw.bb.i" "sw.bb39.i" },
{ name := "if.then.i",
    instrs := [
      Instr.store (Ty.int 64) (.reg "%idxprom.i") (.reg "%off")
    ],
    term := Term.br "if.then" },
{ name := "sw.bb.i",
    instrs := [
      Instr.icmp "%cmp22.i" IPred.ugt 32 (.reg "%sp.0.i.ph163") (.imm (.int 32 (BitVec.ofNat 32 519)))
    ],
    term := Term.condbr (.reg "%cmp22.i") "if.then24.i" "if.end27.i" },
{ name := "if.then24.i",
    instrs := [
      Instr.store (Ty.int 64) (.reg "%idxprom.i") (.reg "%off")
    ],
    term := Term.br "if.then" },
{ name := "if.end27.i",
    instrs := [
      Instr.icmp "%tobool28.not.i" IPred.eq 32 (.reg "%sp.0.i.ph163") (.imm (.int 32 (BitVec.ofNat 32 0)))
    ],
    term := Term.condbr (.reg "%tobool28.not.i") "if.end34.i" "if.then29.i" },
{ name := "if.then29.i",
    instrs := [
      Instr.gep "%cst.restore" (Ty.int 8) (.reg "%cst.i") (.imm (.int 64 (BitVec.ofNat 64 256))),
      Instr.gep "%arrayidx31.i" (Ty.int 8) (.reg "%cst.restore") (.reg "%idxprom13.i"),
      Instr.load "%11" (Ty.int 8) (.reg "%arrayidx31.i"),
      Instr.binop "%sub.i" BinOp.add 32 (.reg "%sp.0.i.ph163") (.imm (.int 32 (BitVec.ofNat 32 4294967295))),
      Instr.zext "%idxprom32.i" 32 64 (.reg "%sub.i"),
      Instr.gep "%arrayidx33.i" (Ty.int 8) (.reg "%ctype.i") (.reg "%idxprom32.i"),
      Instr.store (Ty.int 8) (.reg "%11") (.reg "%arrayidx33.i")
    ],
    term := Term.br "if.end34.i" },
{ name := "if.end34.i",
    instrs := [
      Instr.binop "%inc35.i" BinOp.add 32 (.reg "%sp.0.i.ph163") (.imm (.int 32 (BitVec.ofNat 32 1))),
      Instr.icmp "%cmp36.i" IPred.eq 32 (.reg "%shr.i") (.imm (.int 32 (BitVec.ofNat 32 1))),
      Instr.select "%conv38.i" (Ty.int 8) (.reg "%cmp36.i") (.imm (.int 8 (BitVec.ofNat 8 1))) (.imm (.int 8 (BitVec.ofNat 8 3))),
      Instr.load "%12" (Ty.int 32) (.reg "%hash1.i.i"),
      Instr.icmp "%tobool.not.i.i" IPred.eq 32 (.reg "%12") (.imm (.int 32 (BitVec.ofNat 32 0)))
    ],
    term := Term.condbr (.reg "%tobool.not.i.i") "if.end.i.i" "if.then.i.i" },
{ name := "if.then.i.i",
    instrs := [
      Instr.load "%13" (Ty.int 64) (.reg "%h1.i.i.i26"),
      Instr.zext "%conv.i.i.i" 8 64 (.reg "%conv38.i"),
      Instr.binop "%xor.us.i.i.i" BinOp.xor 64 (.reg "%13") (.reg "%conv.i.i.i"),
      Instr.binop "%14" BinOp.mul 64 (.reg "%xor.us.i.i.i") (.imm (.int 64 (BitVec.ofNat 64 16088033396387240377))),
      Instr.binop "%mul11.i.i.i" BinOp.add 64 (.reg "%14") (.imm (.int 64 (BitVec.ofNat 64 11400714819323198485))),
      Instr.store (Ty.int 64) (.reg "%mul11.i.i.i") (.reg "%h1.i.i.i26")
    ],
    term := Term.br "while.cond.i.outer.backedge" },
{ name := "if.end.i.i",
    instrs := [
      Instr.load "%o.val.i.i" (Ty.int 64) (.reg "%len"),
      Instr.load "%o.val11.i.i" (Ty.int 64) (.reg "%cap"),
      Instr.binop "%add.i.i.i" BinOp.add 64 (.reg "%o.val.i.i") (.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.icmp "%cmp.not.i.i.i" IPred.ugt 64 (.reg "%add.i.i.i") (.reg "%o.val11.i.i")
    ],
    term := Term.condbr (.reg "%cmp.not.i.i.i") "if.end.i.i.i" "out_reserve.exit.i.i" },
{ name := "if.end.i.i.i",
    instrs := [
      Instr.callVoid "llvm.trap" []
    ],
    term := Term.unreachable },
{ name := "out_reserve.exit.i.i",
    instrs := [
      Instr.load "%15" Ty.ptr (.reg "%z"),
      Instr.gep "%add.ptr.i.i" (Ty.int 8) (.reg "%15") (.reg "%o.val.i.i"),
      Instr.store (Ty.int 8) (.reg "%conv38.i") (.reg "%add.ptr.i.i"),
      Instr.store (Ty.int 64) (.reg "%add.i.i.i") (.reg "%len")
    ],
    term := Term.br "while.cond.i.outer.backedge" },
{ name := "sw.bb39.i",
    instrs := [
      Instr.binop "%dec.i" BinOp.add 32 (.reg "%sp.0.i.ph163") (.imm (.int 32 (BitVec.ofNat 32 4294967295))),
      Instr.icmp "%tobool40.not.i" IPred.eq 32 (.reg "%dec.i") (.imm (.int 32 (BitVec.ofNat 32 0)))
    ],
    term := Term.condbr (.reg "%tobool40.not.i") "cond.end.i" "cond.true.i" },
{ name := "cond.true.i",
    instrs := [
      Instr.binop "%sub41.i" BinOp.add 32 (.reg "%sp.0.i.ph163") (.imm (.int 32 (BitVec.ofNat 32 4294967294))),
      Instr.zext "%idxprom42.i" 32 64 (.reg "%sub41.i"),
      Instr.gep "%arrayidx43.i" (Ty.int 8) (.reg "%ctype.i") (.reg "%idxprom42.i"),
      Instr.load "%16" (Ty.int 8) (.reg "%arrayidx43.i"),
      Instr.zext "%conv44.i" 8 32 (.reg "%16")
    ],
    term := Term.br "cond.end.i" },
{ name := "cond.end.i",
    instrs := [
      Instr.phi "%cond45.i" (Ty.int 32) [("cond.true.i", (.reg "%conv44.i")), ("sw.bb39.i", (.imm (.int 32 (BitVec.ofNat 32 1))))],
      Instr.icmp "%cmp47.i" IPred.eq 32 (.reg "%shr.i") (.imm (.int 32 (BitVec.ofNat 32 3))),
      Instr.select "%conv50.i" (Ty.int 8) (.reg "%cmp47.i") (.imm (.int 8 (BitVec.ofNat 8 2))) (.imm (.int 8 (BitVec.ofNat 8 4))),
      Instr.load "%17" (Ty.int 32) (.reg "%hash1.i.i"),
      Instr.icmp "%tobool.not.i.i24" IPred.eq 32 (.reg "%17") (.imm (.int 32 (BitVec.ofNat 32 0)))
    ],
    term := Term.condbr (.reg "%tobool.not.i.i24") "if.end.i.i30" "if.then.i.i25" },
{ name := "if.then.i.i25",
    instrs := [
      Instr.load "%18" (Ty.int 64) (.reg "%h1.i.i.i26"),
      Instr.zext "%conv.i.i.i27" 8 64 (.reg "%conv50.i"),
      Instr.binop "%xor.us.i.i.i28" BinOp.xor 64 (.reg "%18") (.reg "%conv.i.i.i27"),
      Instr.binop "%19" BinOp.mul 64 (.reg "%xor.us.i.i.i28") (.imm (.int 64 (BitVec.ofNat 64 16088033396387240377))),
      Instr.binop "%mul11.i.i.i29" BinOp.add 64 (.reg "%19") (.imm (.int 64 (BitVec.ofNat 64 11400714819323198485))),
      Instr.store (Ty.int 64) (.reg "%mul11.i.i.i29") (.reg "%h1.i.i.i26")
    ],
    term := Term.br "while.cond.i.outer.backedge" },
{ name := "if.end.i.i30",
    instrs := [
      Instr.load "%o.val.i.i31" (Ty.int 64) (.reg "%len"),
      Instr.load "%o.val11.i.i32" (Ty.int 64) (.reg "%cap"),
      Instr.binop "%add.i.i.i33" BinOp.add 64 (.reg "%o.val.i.i31") (.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.icmp "%cmp.not.i.i.i34" IPred.ugt 64 (.reg "%add.i.i.i33") (.reg "%o.val11.i.i32")
    ],
    term := Term.condbr (.reg "%cmp.not.i.i.i34") "if.end.i.i.i39" "out_reserve.exit.i.i35" },
{ name := "if.end.i.i.i39",
    instrs := [
      Instr.callVoid "llvm.trap" []
    ],
    term := Term.unreachable },
{ name := "out_reserve.exit.i.i35",
    instrs := [
      Instr.load "%20" Ty.ptr (.reg "%z"),
      Instr.gep "%add.ptr.i.i36" (Ty.int 8) (.reg "%20") (.reg "%o.val.i.i31"),
      Instr.store (Ty.int 8) (.reg "%conv50.i") (.reg "%add.ptr.i.i36"),
      Instr.store (Ty.int 64) (.reg "%add.i.i.i33") (.reg "%len")
    ],
    term := Term.br "while.cond.i.outer.backedge" },
{ name := "while.cond.i.outer.backedge",
    instrs := [
      Instr.phi "%state.0.i.ph.be" (Ty.int 32) [("if.then.i.i", (.reg "%and.i")), ("out_reserve.exit.i.i", (.reg "%and.i")), ("if.then.i.i25", (.reg "%cond45.i")), ("out_reserve.exit.i.i35", (.reg "%cond45.i"))],
      Instr.phi "%sp.0.i.ph.be" (Ty.int 32) [("if.then.i.i", (.reg "%inc35.i")), ("out_reserve.exit.i.i", (.reg "%inc35.i")), ("if.then.i.i25", (.reg "%dec.i")), ("out_reserve.exit.i.i35", (.reg "%dec.i"))],
      Instr.icmp "%cmp.i153" IPred.ult 64 (.reg "%inc.i") (.reg "%nep")
    ],
    term := Term.condbr (.reg "%cmp.i153") "while.body.i.lr.ph" "while.end225.i" },
{ name := "sw.bb51.i",
    instrs := [
      Instr.icmp "%cmp52.not.i" IPred.ult 64 (.reg "%inc.i") (.reg "%nep")
    ],
    term := Term.condbr (.reg "%cmp52.not.i") "if.end57.i" "if.then54.i" },
{ name := "if.then54.i",
    instrs := [
      Instr.store (Ty.int 64) (.reg "%idxprom.i") (.reg "%off")
    ],
    term := Term.br "if.then" },
{ name := "if.end57.i",
    instrs := [
      Instr.binop "%inc58.i" BinOp.add 64 (.reg "%k.0.i154") (.imm (.int 64 (BitVec.ofNat 64 2))),
      Instr.gep "%arrayidx59.i" (Ty.int 32) (.reg "%5") (.reg "%inc.i"),
      Instr.load "%21" (Ty.int 32) (.reg "%arrayidx59.i"),
      Instr.store (Ty.int 64) (.reg "%inc58.i") (.reg "%k60.i"),
      Instr.zext "%conv61.i" 32 64 (.reg "%21"),
      Instr.icmp "%cmp62.not.i" IPred.ugt 64 (.reg "%4") (.reg "%conv61.i")
    ],
    term := Term.condbr (.reg "%cmp62.not.i") "if.end67.i" "if.then64.i" },
{ name := "if.then64.i",
    instrs := [
      Instr.store (Ty.int 64) (.reg "%idxprom.i") (.reg "%off")
    ],
    term := Term.br "if.then" },
{ name := "if.end67.i",
    instrs := [
      Instr.binop "%22" BinOp.and 32 (.reg "%state.0.i155") (.imm (.int 32 (BitVec.ofNat 32 4294967294))),
      Instr.icmp "%23" IPred.eq 32 (.reg "%22") (.imm (.int 32 (BitVec.ofNat 32 2))),
      Instr.binop "%24" BinOp.xor 64 (.reg "%idxprom.i") (.imm (.int 64 (BitVec.ofNat 64 18446744073709551615))),
      Instr.binop "%sub75.i" BinOp.add 64 (.reg "%conv61.i") (.reg "%24"),
      Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (.reg "%outn.i"))],
      Instr.store (Ty.int 64) (.imm (.int 64 (BitVec.ofNat 64 0))) (.reg "%outn.i"),
      Instr.binop "%add.i" BinOp.add 64 (.reg "%sub75.i") (.imm (.int 64 (BitVec.ofNat 64 64))),
      Instr.load "%z.val19" (Ty.int 64) (.reg "%alen"),
      Instr.load "%z.val20" (Ty.int 64) (.reg "%acap"),
      Instr.binop "%add.i41" BinOp.add 64 (.reg "%add.i") (.reg "%z.val19"),
      Instr.icmp "%cmp.not.i" IPred.ugt 64 (.reg "%add.i41") (.reg "%z.val20")
    ],
    term := Term.condbr (.reg "%cmp.not.i") "if.end.i" "z_arena_reserve.exit" },
{ name := "if.end.i",
    instrs := [
      Instr.callVoid "llvm.trap" []
    ],
    term := Term.unreachable },
{ name := "z_arena_reserve.exit",
    instrs := [
      Instr.load "%25" Ty.ptr (.reg "%ar"),
      Instr.gep "%add.ptr.i" (Ty.int 8) (.reg "%25") (.reg "%z.val19"),
      Instr.gep "%add.ptr77.i" (Ty.int 8) (.reg "%arrayidx10.i") (.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.call "%call78.i" (Ty.int 32) "s2_string_body" [(Ty.ptr, (.reg "%c.i")), (Ty.ptr, (.reg "%add.ptr77.i")), ((Ty.int 64), (.reg "%sub75.i")), (Ty.ptr, (.reg "%add.ptr.i")), (Ty.ptr, (.reg "%outn.i")), (Ty.ptr, (.reg "%xp")), (Ty.ptr, (.reg "%xj.i")), ((Ty.int 64), (.reg "%nxp"))]
    ],
    term := Term.br "NodeBlock11" },
{ name := "NodeBlock11",
    instrs := [
      Instr.icmp "%Pivot12" IPred.slt 32 (.reg "%call78.i") (.imm (.int 32 (BitVec.ofNat 32 1)))
    ],
    term := Term.condbr (.reg "%Pivot12") "cleanup.i.thread" "LeafBlock9" },
{ name := "LeafBlock9",
    instrs := [
      Instr.icmp "%SwitchLeaf10" IPred.eq 32 (.reg "%call78.i") (.imm (.int 32 (BitVec.ofNat 32 1)))
    ],
    term := Term.condbr (.reg "%SwitchLeaf10") "if.then84.i" "if.else.i" },
{ name := "cleanup.i.thread",
    instrs := [
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (.reg "%outn.i"))]
    ],
    term := Term.br "if.then" },
{ name := "if.then84.i",
    instrs := [
      Instr.binop "%add86.i" BinOp.add 32 (.reg "%7") (.imm (.int 32 (BitVec.ofNat 32 1))),
      Instr.zext "%conv87.i" 32 64 (.reg "%add86.i"),
      Instr.binop "%or.i" BinOp.or 64 (.reg "%conv87.i") (.imm (.int 64 (BitVec.ofNat 64 9223372036854775808)))
    ],
    term := Term.br "if.end92.i" },
{ name := "if.else.i",
    instrs := [
      Instr.load "%26" (Ty.int 64) (.reg "%outn.i"),
      Instr.binop "%add91.i" BinOp.add 64 (.reg "%z.val19") (.reg "%26"),
      Instr.store (Ty.int 64) (.reg "%add91.i") (.reg "%alen")
    ],
    term := Term.br "if.end92.i" },
{ name := "if.end92.i",
    instrs := [
      Instr.phi "%conv88.i.sink.in" (Ty.int 64) [("if.then84.i", (.reg "%sub75.i")), ("if.else.i", (.reg "%26"))],
      Instr.phi "%.sink" (Ty.int 64) [("if.then84.i", (.reg "%or.i")), ("if.else.i", (.reg "%z.val19"))],
      Instr.load "%z.val" (Ty.int 64) (.reg "%len"),
      Instr.load "%z.val18" (Ty.int 64) (.reg "%cap"),
      Instr.binop "%add.i42" BinOp.add 64 (.reg "%z.val") (.imm (.int 64 (BitVec.ofNat 64 13))),
      Instr.icmp "%cmp.not.i43" IPred.ugt 64 (.reg "%add.i42") (.reg "%z.val18")
    ],
    term := Term.condbr (.reg "%cmp.not.i43") "if.end.i44" "cleanup.i" },
{ name := "if.end.i44",
    instrs := [
      Instr.callVoid "llvm.trap" []
    ],
    term := Term.unreachable },
{ name := "cleanup.i",
    instrs := [
      Instr.trunc "%conv88.i.sink" 64 32 (.reg "%conv88.i.sink.in"),
      Instr.load "%27" Ty.ptr (.reg "%z"),
      Instr.gep "%add.ptr98.i" (Ty.int 8) (.reg "%27") (.reg "%z.val"),
      Instr.select "%conv101.i" (Ty.int 8) (.reg "%23") (.imm (.int 8 (BitVec.ofNat 8 5))) (.imm (.int 8 (BitVec.ofNat 8 6))),
      Instr.store (Ty.int 8) (.reg "%conv101.i") (.reg "%add.ptr98.i"),
      Instr.gep "%add.ptr103.i" (Ty.int 8) (.reg "%add.ptr98.i") (.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.store (Ty.int 32) (.reg "%conv88.i.sink") (.reg "%add.ptr103.i"),
      Instr.gep "%add.ptr105.i" (Ty.int 8) (.reg "%add.ptr98.i") (.imm (.int 64 (BitVec.ofNat 64 5))),
      Instr.store (Ty.int 64) (.reg "%.sink") (.reg "%add.ptr105.i"),
      Instr.store (Ty.int 64) (.reg "%add.i42") (.reg "%len"),
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (.reg "%outn.i"))]
    ],
    term := Term.br "while.cond.i.backedge" },
{ name := "while.cond.i.backedge",
    instrs := [
      Instr.phi "%k.0.i.be" (Ty.int 64) [("if.end211.i", (.reg "%inc.i")), ("cleanup.i", (.reg "%inc58.i")), ("NodeBlock1", (.reg "%inc.i"))],
      Instr.icmp "%cmp.i" IPred.ult 64 (.reg "%k.0.i.be") (.reg "%nep")
    ],
    term := Term.condbr (.reg "%cmp.i") "while.body.i" "while.end225.i" },
{ name := "sw.bb115.i",
    instrs := [
      Instr.icmp "%cmp116.i" IPred.ult 64 (.reg "%inc.i") (.reg "%nep")
    ],
    term := Term.condbr (.reg "%cmp116.i") "cond.true118.i" "cond.end122.i" },
{ name := "cond.true118.i",
    instrs := [
      Instr.gep "%arrayidx119.i" (Ty.int 32) (.reg "%5") (.reg "%inc.i"),
      Instr.load "%28" (Ty.int 32) (.reg "%arrayidx119.i"),
      Instr.zext "%conv120.i" 32 64 (.reg "%28")
    ],
    term := Term.br "cond.end122.i" },
{ name := "cond.end122.i",
    instrs := [
      Instr.phi "%cond123.i" (Ty.int 64) [("cond.true118.i", (.reg "%conv120.i")), ("sw.bb115.i", (.reg "%4"))],
      Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (.imm (.int 64 (BitVec.ofNat 64 24)))), (Ty.ptr, (.reg "%t352.i"))],
      Instr.store (Ty.int 64) (.reg "%idxprom.i") (.reg "%t352.i"),
      Instr.store (Ty.int 32) (.imm (.int 32 (BitVec.ofNat 32 1))) (.reg "%gap.i"),
      Instr.icmp "%cmp127.i" IPred.ugt 64 (.reg "%cond123.i") (.reg "%idxprom.i")
    ],
    term := Term.condbr (.reg "%cmp127.i") "land.lhs.true.i" "if.end143.i" },
{ name := "land.lhs.true.i",
    instrs := [
      Instr.gep "%gep" (Ty.int 8) (.reg "%invariant.gep") (.reg "%cond123.i"),
      Instr.load "%29" (Ty.int 8) (.reg "%gep")
    ],
    term := Term.br "NodeBlock21" },
{ name := "NodeBlock21",
    instrs := [
      Instr.icmp "%Pivot22" IPred.slt 8 (.reg "%29") (.imm (.int 8 (BitVec.ofNat 8 13)))
    ],
    term := Term.condbr (.reg "%Pivot22") "LeafBlock13" "NodeBlock19" },
{ name := "NodeBlock19",
    instrs := [
      Instr.icmp "%Pivot20" IPred.slt 8 (.reg "%29") (.imm (.int 8 (BitVec.ofNat 8 32)))
    ],
    term := Term.condbr (.reg "%Pivot20") "LeafBlock15" "LeafBlock17" },
{ name := "LeafBlock17",
    instrs := [
      Instr.icmp "%SwitchLeaf18" IPred.eq 8 (.reg "%29") (.imm (.int 8 (BitVec.ofNat 8 32)))
    ],
    term := Term.condbr (.reg "%SwitchLeaf18") "land.rhs.i.preheader" "if.end143.i" },
{ name := "LeafBlock15",
    instrs := [
      Instr.icmp "%SwitchLeaf16" IPred.eq 8 (.reg "%29") (.imm (.int 8 (BitVec.ofNat 8 13)))
    ],
    term := Term.condbr (.reg "%SwitchLeaf16") "land.rhs.i.preheader" "if.end143.i" },
{ name := "LeafBlock13",
    instrs := [
      Instr.binop "%.off" BinOp.add 8 (.reg "%29") (.imm (.int 8 (BitVec.ofNat 8 247))),
      Instr.icmp "%SwitchLeaf14" IPred.ule 8 (.reg "%.off") (.imm (.int 8 (BitVec.ofNat 8 1)))
    ],
    term := Term.condbr (.reg "%SwitchLeaf14") "land.rhs.i.preheader" "if.end143.i" },
{ name := "land.rhs.i.preheader",
    instrs := [

    ],
    term := Term.br "land.rhs.i" },
{ name := "land.rhs.i",
    instrs := [
      Instr.phi "%ee.0.i144" (Ty.int 64) [("while.body141.i", (.reg "%inc142.i")), ("land.rhs.i.preheader", (.reg "%idxprom.i"))],
      Instr.gep "%arrayidx138.i" (Ty.int 8) (.reg "%3") (.reg "%ee.0.i144"),
      Instr.load "%30" (Ty.int 8) (.reg "%arrayidx138.i")
    ],
    term := Term.br "NodeBlock32" },
{ name := "NodeBlock32",
    instrs := [
      Instr.icmp "%Pivot33" IPred.slt 8 (.reg "%30") (.imm (.int 8 (BitVec.ofNat 8 13)))
    ],
    term := Term.condbr (.reg "%Pivot33") "LeafBlock23" "NodeBlock30" },
{ name := "NodeBlock30",
    instrs := [
      Instr.icmp "%Pivot31" IPred.slt 8 (.reg "%30") (.imm (.int 8 (BitVec.ofNat 8 32)))
    ],
    term := Term.condbr (.reg "%Pivot31") "LeafBlock26" "LeafBlock28" },
{ name := "LeafBlock28",
    instrs := [
      Instr.icmp "%SwitchLeaf29" IPred.eq 8 (.reg "%30") (.imm (.int 8 (BitVec.ofNat 8 32)))
    ],
    term := Term.condbr (.reg "%SwitchLeaf29") "if.end143.i" "while.body141.i" },
{ name := "LeafBlock26",
    instrs := [
      Instr.icmp "%SwitchLeaf27" IPred.eq 8 (.reg "%30") (.imm (.int 8 (BitVec.ofNat 8 13)))
    ],
    term := Term.condbr (.reg "%SwitchLeaf27") "if.end143.i" "while.body141.i" },
{ name := "LeafBlock23",
    instrs := [
      Instr.binop "%.off24" BinOp.add 8 (.reg "%30") (.imm (.int 8 (BitVec.ofNat 8 247))),
      Instr.icmp "%SwitchLeaf25" IPred.ule 8 (.reg "%.off24") (.imm (.int 8 (BitVec.ofNat 8 1)))
    ],
    term := Term.condbr (.reg "%SwitchLeaf25") "if.end143.i" "while.body141.i" },
{ name := "while.body141.i",
    instrs := [
      Instr.binop "%inc142.i" BinOp.add 64 (.reg "%ee.0.i144") (.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.icmp "%exitcond.not" IPred.eq 64 (.reg "%inc142.i") (.reg "%cond123.i")
    ],
    term := Term.condbr (.reg "%exitcond.not") "if.end143.i" "land.rhs.i" },
{ name := "if.end143.i",
    instrs := [
      Instr.phi "%ee.1.i" (Ty.int 64) [("cond.end122.i", (.reg "%idxprom.i")), ("while.body141.i", (.reg "%cond123.i")), ("LeafBlock23", (.reg "%ee.0.i144")), ("LeafBlock26", (.reg "%ee.0.i144")), ("LeafBlock28", (.reg "%ee.0.i144")), ("LeafBlock13", (.reg "%cond123.i")), ("LeafBlock15", (.reg "%cond123.i")), ("LeafBlock17", (.reg "%cond123.i"))],
      Instr.store (Ty.int 64) (.reg "%ee.1.i") (.reg "%end.i"),
      Instr.icmp "%cmp147.i" IPred.eq 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 45))),
      Instr.binop "%31" BinOp.add 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 208))),
      Instr.icmp "%or.cond.i" IPred.ult 8 (.reg "%31") (.imm (.int 8 (BitVec.ofNat 8 10))),
      Instr.binop "%or.cond362.i" BinOp.or 1 (.reg "%cmp147.i") (.reg "%or.cond.i")
    ],
    term := Term.condbr (.reg "%or.cond362.i") "if.end180.i" "if.else157.i" },
{ name := "if.else157.i",
    instrs := [

    ],
    term := Term.br "NodeBlock42" },
{ name := "NodeBlock42",
    instrs := [
      Instr.icmp "%Pivot43" IPred.slt 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 110)))
    ],
    term := Term.condbr (.reg "%Pivot43") "LeafBlock34" "NodeBlock40" },
{ name := "NodeBlock40",
    instrs := [
      Instr.icmp "%Pivot41" IPred.slt 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 116)))
    ],
    term := Term.condbr (.reg "%Pivot41") "LeafBlock36" "LeafBlock38" },
{ name := "LeafBlock38",
    instrs := [
      Instr.icmp "%SwitchLeaf39" IPred.eq 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 116)))
    ],
    term := Term.condbr (.reg "%SwitchLeaf39") "if.end180.i" "if.else175.i" },
{ name := "LeafBlock36",
    instrs := [
      Instr.icmp "%SwitchLeaf37" IPred.eq 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 110)))
    ],
    term := Term.condbr (.reg "%SwitchLeaf37") "if.then173.i" "if.else175.i" },
{ name := "LeafBlock34",
    instrs := [
      Instr.icmp "%SwitchLeaf35" IPred.eq 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 102)))
    ],
    term := Term.condbr (.reg "%SwitchLeaf35") "if.then167.i" "if.else175.i" },
{ name := "if.then167.i",
    instrs := [

    ],
    term := Term.br "if.end180.i" },
{ name := "if.then173.i",
    instrs := [

    ],
    term := Term.br "if.end180.i" },
{ name := "if.else175.i",
    instrs := [

    ],
    term := Term.br "if.end180.i" },
{ name := "if.end180.i",
    instrs := [
      Instr.phi "%.sink317" (Ty.int 32) [("if.else175.i", (.imm (.int 32 (BitVec.ofNat 32 0)))), ("if.then173.i", (.imm (.int 32 (BitVec.ofNat 32 10)))), ("if.then167.i", (.imm (.int 32 (BitVec.ofNat 32 9)))), ("if.end143.i", (.imm (.int 32 (BitVec.ofNat 32 7)))), ("LeafBlock38", (.imm (.int 32 (BitVec.ofNat 32 8))))],
      Instr.store (Ty.int 32) (.reg "%.sink317") (.reg "%kind174.i"),
      Instr.call "%call182.i" (Ty.int 32) "od_scalar_value" [(Ty.ptr, (.reg "%c.i")), (Ty.ptr, (.reg "%t352.i")), (Ty.ptr, (.reg "%z"))],
      Instr.icmp "%tobool183.not.i" IPred.eq 32 (.reg "%call182.i") (.imm (.int 32 (BitVec.ofNat 32 0)))
    ],
    term := Term.condbr (.reg "%tobool183.not.i") "if.then187.i" "if.end189.i" },
{ name := "if.then187.i",
    instrs := [
      Instr.callVoid "od_gap_recover" [(Ty.ptr, (.reg "%c.i")), ((Ty.int 64), (.reg "%idxprom.i"))]
    ],
    term := Term.br "cleanup212.i" },
{ name := "if.end189.i",
    instrs := [
      Instr.icmp "%cmp190.i" IPred.ult 64 (.reg "%ee.1.i") (.reg "%cond123.i")
    ],
    term := Term.condbr (.reg "%cmp190.i") "land.rhs196.i" "if.end211.i" },
{ name := "land.rhs196.i",
    instrs := [
      Instr.phi "%q.0.i152" (Ty.int 64) [("while.body201.i", (.reg "%inc202.i")), ("if.end189.i", (.reg "%ee.1.i"))],
      Instr.gep "%arrayidx197.i" (Ty.int 8) (.reg "%3") (.reg "%q.0.i152"),
      Instr.load "%32" (Ty.int 8) (.reg "%arrayidx197.i")
    ],
    term := Term.br "NodeBlock53" },
{ name := "NodeBlock53",
    instrs := [
      Instr.icmp "%Pivot54" IPred.slt 8 (.reg "%32") (.imm (.int 8 (BitVec.ofNat 8 13)))
    ],
    term := Term.condbr (.reg "%Pivot54") "LeafBlock44" "NodeBlock51" },
{ name := "NodeBlock51",
    instrs := [
      Instr.icmp "%Pivot52" IPred.slt 8 (.reg "%32") (.imm (.int 8 (BitVec.ofNat 8 32)))
    ],
    term := Term.condbr (.reg "%Pivot52") "LeafBlock47" "LeafBlock49" },
{ name := "LeafBlock49",
    instrs := [
      Instr.icmp "%SwitchLeaf50" IPred.eq 8 (.reg "%32") (.imm (.int 8 (BitVec.ofNat 8 32)))
    ],
    term := Term.condbr (.reg "%SwitchLeaf50") "while.body201.i" "if.then206.i" },
{ name := "LeafBlock47",
    instrs := [
      Instr.icmp "%SwitchLeaf48" IPred.eq 8 (.reg "%32") (.imm (.int 8 (BitVec.ofNat 8 13)))
    ],
    term := Term.condbr (.reg "%SwitchLeaf48") "while.body201.i" "if.then206.i" },
{ name := "LeafBlock44",
    instrs := [
      Instr.binop "%.off45" BinOp.add 8 (.reg "%32") (.imm (.int 8 (BitVec.ofNat 8 247))),
      Instr.icmp "%SwitchLeaf46" IPred.ule 8 (.reg "%.off45") (.imm (.int 8 (BitVec.ofNat 8 1)))
    ],
    term := Term.condbr (.reg "%SwitchLeaf46") "while.body201.i" "if.then206.i" },
{ name := "while.body201.i",
    instrs := [
      Instr.binop "%inc202.i" BinOp.add 64 (.reg "%q.0.i152") (.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.icmp "%exitcond238.not" IPred.eq 64 (.reg "%inc202.i") (.reg "%cond123.i")
    ],
    term := Term.condbr (.reg "%exitcond238.not") "if.end211.i" "land.rhs196.i" },
{ name := "if.then206.i",
    instrs := [
      Instr.store (Ty.int 64) (.reg "%q.0.i152") (.reg "%off")
    ],
    term := Term.br "cleanup212.i" },
{ name := "if.end211.i",
    instrs := [
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (.imm (.int 64 (BitVec.ofNat 64 24)))), (Ty.ptr, (.reg "%t352.i"))]
    ],
    term := Term.br "while.cond.i.backedge" },
{ name := "cleanup212.i",
    instrs := [
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (.imm (.int 64 (BitVec.ofNat 64 24)))), (Ty.ptr, (.reg "%t352.i"))]
    ],
    term := Term.br "if.then" },
{ name := "sw.default.i",
    instrs := [
      Instr.store (Ty.int 64) (.reg "%idxprom.i") (.reg "%off")
    ],
    term := Term.br "if.then" },
{ name := "while.end225.i",
    instrs := [
      Instr.phi "%sp.0.i.ph.lcssa142" (Ty.int 32) [("while.cond.i.backedge", (.reg "%sp.0.i.ph163")), ("while.cond.i.outer.backedge", (.reg "%sp.0.i.ph.be"))],
      Instr.phi "%state.0.i.lcssa" (Ty.int 32) [("while.cond.i.backedge", (.reg "%and.i")), ("while.cond.i.outer.backedge", (.reg "%state.0.i.ph.be"))],
      Instr.icmp "%cmp226.not.i" IPred.eq 32 (.reg "%sp.0.i.ph.lcssa142") (.imm (.int 32 (BitVec.ofNat 32 0)))
    ],
    term := Term.condbr (.reg "%cmp226.not.i") "if.end230.i" "if.then228.i" },
{ name := "if.then228.i",
    instrs := [
      Instr.store (Ty.int 64) (.reg "%4") (.reg "%off")
    ],
    term := Term.br "if.then" },
{ name := "if.end230.i",
    instrs := [
      Instr.icmp "%cmp231.not.i" IPred.eq 32 (.reg "%state.0.i.lcssa") (.imm (.int 32 (BitVec.ofNat 32 1)))
    ],
    term := Term.condbr (.reg "%cmp231.not.i") "sd_walk.exit" "if.then233.i" },
{ name := "if.then233.i",
    instrs := [
      Instr.store (Ty.int 64) (.reg "%4") (.reg "%off")
    ],
    term := Term.br "if.then" },
{ name := "sd_walk.exit",
    instrs := [
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (.imm (.int 64 (BitVec.ofNat 64 1192)))), (Ty.ptr, (.reg "%c.i"))],
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (.reg "%xj.i"))],
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (.imm (.int 64 (BitVec.ofNat 64 520)))), (Ty.ptr, (.reg "%ctype.i"))],
      Instr.load "%33" (Ty.int 64) (.reg "%alen"),
      Instr.store (Ty.int 64) (.reg "%33") (.reg "%ndst"),
      Instr.load "%34" (Ty.int 64) (.reg "%len"),
      Instr.store (Ty.int 64) (.reg "%34") (.reg "%nev")
    ],
    term := Term.br "if.end" },
{ name := "if.then",
    instrs := [
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (.imm (.int 64 (BitVec.ofNat 64 1192)))), (Ty.ptr, (.reg "%c.i"))],
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (.reg "%xj.i"))],
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (.imm (.int 64 (BitVec.ofNat 64 520)))), (Ty.ptr, (.reg "%ctype.i"))],
      Instr.load "%35" (Ty.int 64) (.reg "%alen"),
      Instr.store (Ty.int 64) (.reg "%35") (.reg "%ndst"),
      Instr.load "%36" (Ty.int 64) (.reg "%len"),
      Instr.store (Ty.int 64) (.reg "%36") (.reg "%nev"),
      Instr.load "%37" (Ty.int 64) (.reg "%off"),
      Instr.store (Ty.int 64) (.reg "%37") (.reg "%err")
    ],
    term := Term.br "if.end" },
{ name := "if.end",
    instrs := [
      Instr.phi "%tobool.not66" (Ty.int 64) [("if.then", (.imm (.int 64 (BitVec.ofNat 64 0)))), ("sd_walk.exit", (.imm (.int 64 (BitVec.ofNat 64 1))))],
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (.imm (.int 64 (BitVec.ofNat 64 24)))), (Ty.ptr, (.reg "%e"))],
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (.imm (.int 64 (BitVec.ofNat 64 64)))), (Ty.ptr, (.reg "%z"))],
      Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (.imm (.int 64 (BitVec.ofNat 64 120)))), (Ty.ptr, (.reg "%s"))]
    ],
    term := Term.ret (Ty.int 64) (some (.reg "%tobool.not66")) }
] }

/-! ### The pin -/

/- The fixture parses to exactly this body. -/
#guard decide (dfaFirstFunction dfaSrc = some stage2DfaBody)

/- The ABI and record prefix the derivation claims. -/
#guard decide (stage2DfaBody.params.length = 21)
#guard decide (stage2DfaBody.blocks.length = 92)

/-- The rets-valued fact the call-site guarantee consumes, read off the pin. -/
theorem stage2DfaBody_retsValued : retsValued stage2DfaBody = true := by decide

/-! ### The call rows -/

/-- Every call instruction's callee, in body order. -/
def stage2DfaCalls : List String :=
  stage2DfaBody.blocks.flatMap fun b =>
    b.instrs.filterMap fun i =>
      match i with
      | .call _ _ c _ => some c
      | .callVoid c _ => some c
      | _ => none

/-- **The pinned body's call rows.**  The first helper call is `s2_init` in the
entry block; the loop's helpers are `s2_string_body`, `od_scalar_value` and
`od_gap_recover`; the four traps are the reserve guards. -/
theorem stage2DfaBody_calls :
    stage2DfaCalls =
      ["llvm.lifetime.start.p0", "llvm.lifetime.start.p0",
       "llvm.lifetime.start.p0", "s2_init", "llvm.memset.p0.i64",
       "llvm.lifetime.start.p0", "llvm.lifetime.start.p0",
       "llvm.lifetime.start.p0", "llvm.memset.p0.i64", "llvm.trap",
       "llvm.trap", "llvm.lifetime.start.p0", "llvm.trap",
       "s2_string_body", "llvm.lifetime.end.p0", "llvm.trap",
       "llvm.lifetime.end.p0", "llvm.lifetime.start.p0", "od_scalar_value",
       "od_gap_recover", "llvm.lifetime.end.p0", "llvm.lifetime.end.p0",
       "llvm.lifetime.end.p0", "llvm.lifetime.end.p0",
       "llvm.lifetime.end.p0", "llvm.lifetime.end.p0",
       "llvm.lifetime.end.p0", "llvm.lifetime.end.p0",
       "llvm.lifetime.end.p0", "llvm.lifetime.end.p0",
       "llvm.lifetime.end.p0"] := by decide

/-- **The first helper-call row.**  The entry block's eighth instruction is the
`s2_init` call at the five staged arguments. -/
theorem stage2DfaBody_first_helper :
    stage2DfaBody.blocks.head?.bind (fun b => b.instrs[7]?) =
      some (Instr.callVoid "s2_init"
        [(Ty.ptr, .reg "%s"), (Ty.ptr, .reg "%b"), ((Ty.int 64), .reg "%n"),
         ((Ty.int 64), .reg "%shr"), (Ty.ptr, .reg "%ep")]) := by decide

/-! ### The obligation and its loop invariant -/

/-- The classifier, resume and transition bytes the `cst` slot must hold. -/
def stage2DfaClsBytes : List UInt8 := sdClsRow.map UInt8.ofNat

def stage2DfaTrBytes : List UInt8 := sdTrRow.map UInt8.ofNat

def stage2DfaRestoreBytes : List UInt8 := sdRestoreRow.map UInt8.ofNat

/-- The three read-only tables at the `cst` slot: 256 classifier bytes at 0, the
10 resume bytes at 256, and the 80 transition bytes at 272. -/
def Stage2DfaTableBytes (mem : Mem) (cst : Nat) : Prop :=
  readBytes mem cst 256 = some stage2DfaClsBytes ∧
  readBytes mem (cst + 256) 10 = some stage2DfaRestoreBytes ∧
  readBytes mem (cst + 272) 80 = some stage2DfaTrBytes

/-- **The walk obligation for the DFA body**, at the record and staging the
certified selection uses.  `stk` fills the `ctype` slot, `cst` carries the three
read-only tables, and `d`/the remaining slots are the record's.

The record's pre stages the `cst` region but does not constrain its bytes, while
the body dispatches on them.  So the proof's exact goal is this `Satisfies`
**together with** `Stage2DfaTableBytes mem cst` at the call: the body reads the
classifier, the resume table and the transition table from that slot, and a
contract that admitted arbitrary `cst` bytes would not state the DFA's
dispatches.  This premise is the statement change the body proof owes; the
obligation below is the `Satisfies` the conductor named, not a weakened one. -/
def Stage2DfaWalkObligation (d c stk cst tok s z e : Nat) : Prop :=
  Satisfies (stage2Calls stage2SubCalls) stage2DfaBody
    (Γ_stage2work d c stk cst tok s z e)

/-- The loop's observable state: the entry cursor, the escape cursor, the arena
length, the event-stream length, and memory. -/
structure Stage2DfaLoopState where
  k : Nat
  xj : Nat
  alen : Nat
  evLen : Nat
  mem : Mem
  deriving DecidableEq, Repr

/-- The body-level loop agreement the obligation owes: the DFA's loop carries
the certified run's four cursor/memory components at every entry.  The abstract
configuration and stack clauses are `JsonStage2DfaRun.runDfa_abs`. -/
def Stage2DfaLoopAgrees (dfa cert : Stage2DfaLoopState) : Prop :=
  dfa.k = cert.k ∧ dfa.xj = cert.xj ∧ dfa.alen = cert.alen ∧
  dfa.evLen = cert.evLen ∧ dfa.mem = cert.mem

end LeanLLVM.Refinement
