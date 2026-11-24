/-
The instruction and terminator steps `od_gap_recover`'s emitted body needs, and
its block pins.

This module is the vocabulary a run proof of the body is written in, and it
states no contract: the block pins are here, the per-instruction `denoteCode`
steps at the body's own widths are here, and the three terminator shapes are
here.  The loop instances and the run at the call boundary are not, so nothing
in this module relates the body to `JsonStage2HelperOdGap`'s rule — the model's
transcription-to-instructions distance for this helper stays the seam
`docs/contract.md` records.

**The block pins.**  `capture-stage2-helpers.sh --emit-pins od_gap_recover` with
every block listed as a run prints the instruction lists below and each
`findBlock` equation; every `findBlock` is `decide`, so a block whose
instruction list moved fails here rather than inside a step.

**Why the steps are needed.**  `BlockEval`'s chain steps are the 64-bit shapes
the pipeline's blocks use.  This body is byte and 32-bit work as well — the
switch's `icmp slt i8`/`icmp ule i8`, the index word's `i32` load and `i32`
element `getelementptr`, the record's `i32` and immediate `i64` stores, an
`alloca` of `double`, and calls of two and four arguments — so the shapes below
are the same `evalInstr` steps at these widths.  Each is stated once and its
`denoteCode` wrapper is the step through `denoteCode_cons_of`, nothing else.

`gap_step` is `BlockEval`'s chain extended by these shapes and `gap_eval` closes a
block once its chain has run, exactly as `block_eval` does.
-/
import LeanLLVM.Refinement.JsonStage2HelperIROdGap
import LeanLLVM.Refinement.BlockEval
import LeanLLVM.Refinement.LoopFuel

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonS1MasksIR
  (evalInstr_load evalInstr_binop evalInstr_icmp evalInstr_store evalInstr_call
   evalOperands_cons evalInstr_zext evalInstr_select_true evalInstr_select_false)

/-! ### The block pins, and their instruction lists

Generated from the parse by `capture-stage2-helpers.sh --emit-pins
od_gap_recover` with every block listed as a run: each `findBlock` is `decide`,
so a block whose instruction list moved fails here rather than inside a step. -/

def odGapRecoverEntryInstrs : List Instr :=
  [
    Instr.alloca "%d" Ty.double 0,
    Instr.alloca "%ei" (Ty.int 64) 0,
    Instr.load "%0" Ty.ptr (Operand.reg "%c"),
    Instr.gep "%k" (Ty.int 8) (Operand.reg "%c") (Operand.imm (Const.int 64 0x0000000000000020#64)),
    Instr.load "%1" (Ty.int 64) (Operand.reg "%k"),
    Instr.gep "%nix" (Ty.int 8) (Operand.reg "%c") (Operand.imm (Const.int 64 0x0000000000000018#64)),
    Instr.load "%2" (Ty.int 64) (Operand.reg "%nix"),
    Instr.icmp "%cmp" (IPred.ult) 64 (Operand.reg "%1") (Operand.reg "%2")]

def odGapRecoverCondTrueInstrs : List Instr :=
  [
    Instr.gep "%ix" (Ty.int 8) (Operand.reg "%c") (Operand.imm (Const.int 64 0x0000000000000010#64)),
    Instr.load "%3" Ty.ptr (Operand.reg "%ix"),
    Instr.gep "%arrayidx" (Ty.int 32) (Operand.reg "%3") (Operand.reg "%1"),
    Instr.load "%4" (Ty.int 32) (Operand.reg "%arrayidx"),
    Instr.zext "%conv" 32 64 (Operand.reg "%4")]

def odGapRecoverCondFalseInstrs : List Instr :=
  [
    Instr.gep "%n" (Ty.int 8) (Operand.reg "%c") (Operand.imm (Const.int 64 0x0000000000000008#64)),
    Instr.load "%5" (Ty.int 64) (Operand.reg "%n")]

def odGapRecoverCondEndInstrs : List Instr :=
  [
    Instr.phi "%cond" (Ty.int 64) [("cond.true", (Operand.reg "%conv")),
                                       ("cond.false", (Operand.reg "%5"))],
    Instr.icmp "%cmp310" (IPred.ult) 64 (Operand.reg "%t.0.val") (Operand.reg "%cond")]

def odGapRecoverLandRhsInstrs : List Instr :=
  [
    Instr.phi "%ee.011" (Ty.int 64) [("while.body", (Operand.reg "%inc")),
                                       ("cond.end", (Operand.reg "%t.0.val"))],
    Instr.gep "%arrayidx5" (Ty.int 8) (Operand.reg "%0") (Operand.reg "%ee.011"),
    Instr.load "%6" (Ty.int 8) (Operand.reg "%arrayidx5")]

def odGapRecoverNodeBlock5Instrs : List Instr :=
  [
    Instr.icmp "%Pivot6" (IPred.slt) 8 (Operand.reg "%6") (Operand.imm (Const.int 8 0x0d#8))]

def odGapRecoverNodeBlockInstrs : List Instr :=
  [
    Instr.icmp "%Pivot" (IPred.slt) 8 (Operand.reg "%6") (Operand.imm (Const.int 8 0x20#8))]

def odGapRecoverLeafBlock3Instrs : List Instr :=
  [
    Instr.icmp "%SwitchLeaf4" (IPred.eq) 8 (Operand.reg "%6") (Operand.imm (Const.int 8 0x20#8))]

def odGapRecoverLeafBlock1Instrs : List Instr :=
  [
    Instr.icmp "%SwitchLeaf2" (IPred.eq) 8 (Operand.reg "%6") (Operand.imm (Const.int 8 0x0d#8))]

def odGapRecoverLeafBlockInstrs : List Instr :=
  [
    Instr.binop "%.off" (BinOp.add) 8 (Operand.reg "%6") (Operand.imm (Const.int 8 0xf7#8)),
    Instr.icmp "%SwitchLeaf" (IPred.ule) 8 (Operand.reg "%.off") (Operand.imm (Const.int 8 0x01#8))]

def odGapRecoverWhileBodyInstrs : List Instr :=
  [
    Instr.binop "%inc" (BinOp.add) 64 (Operand.reg "%ee.011") (Operand.imm (Const.int 64 0x0000000000000001#64)),
    Instr.icmp "%exitcond.not" (IPred.eq) 64 (Operand.reg "%inc") (Operand.reg "%cond")]

def odGapRecoverWhileEndInstrs : List Instr :=
  [
    Instr.phi "%ee.0.lcssa" (Ty.int 64) [("cond.end", (Operand.reg "%t.0.val")),
                                       ("LeafBlock", (Operand.reg "%ee.011")),
                                       ("LeafBlock1", (Operand.reg "%ee.011")),
                                       ("LeafBlock3", (Operand.reg "%ee.011"))],
    Instr.icmp "%cmp6" (IPred.eq) 64 (Operand.reg "%ee.0.lcssa") (Operand.reg "%cond")]

def odGapRecoverIfEndInstrs : List Instr :=
  [
    Instr.gep "%arrayidx9" (Ty.int 8) (Operand.reg "%0") (Operand.reg "%t.0.val"),
    Instr.load "%7" (Ty.int 8) (Operand.reg "%arrayidx9"),
    Instr.icmp "%cmp11" (IPred.eq) 8 (Operand.reg "%7") (Operand.imm (Const.int 8 0x2d#8)),
    Instr.binop "%8" (BinOp.add) 8 (Operand.reg "%7") (Operand.imm (Const.int 8 0xd0#8)),
    Instr.icmp "%or.cond" (IPred.ult) 8 (Operand.reg "%8") (Operand.imm (Const.int 8 0x0a#8)),
    Instr.binop "%or.cond127" (BinOp.or) 1 (Operand.reg "%cmp11") (Operand.reg "%or.cond")]

def odGapRecoverIfThen19Instrs : List Instr :=
  [
    Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000008#64))),
                             (Ty.ptr, (Operand.reg "%d"))],
    Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000008#64))),
                             (Ty.ptr, (Operand.reg "%ei"))],
    Instr.binop "%sub" (BinOp.sub) 64 (Operand.reg "%ee.0.lcssa") (Operand.reg "%t.0.val"),
    Instr.call "%call23" (Ty.int 32) "num_fast_el1" [(Ty.ptr, (Operand.reg "%arrayidx9")),
                             ((Ty.int 64), (Operand.reg "%sub")),
                             (Ty.ptr, (Operand.reg "%d")),
                             (Ty.ptr, (Operand.reg "%ei"))],
    Instr.icmp "%tobool24.not.not" (IPred.eq) 32 (Operand.reg "%call23") (Operand.imm (Const.int 32 0x00000000#32))]

def odGapRecoverIfThen25Instrs : List Instr :=
  [
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
                             (Ty.ptr, (Operand.reg "%d"))]]

def odGapRecoverIfElseInstrs : List Instr :=
  [
]

def odGapRecoverNodeBlock15Instrs : List Instr :=
  [
    Instr.icmp "%Pivot16" (IPred.slt) 8 (Operand.reg "%7") (Operand.imm (Const.int 8 0x6e#8))]

def odGapRecoverNodeBlock13Instrs : List Instr :=
  [
    Instr.icmp "%Pivot14" (IPred.slt) 8 (Operand.reg "%7") (Operand.imm (Const.int 8 0x74#8))]

def odGapRecoverLeafBlock11Instrs : List Instr :=
  [
    Instr.icmp "%SwitchLeaf12" (IPred.eq) 8 (Operand.reg "%7") (Operand.imm (Const.int 8 0x74#8))]

def odGapRecoverLeafBlock9Instrs : List Instr :=
  [
    Instr.icmp "%SwitchLeaf10" (IPred.eq) 8 (Operand.reg "%7") (Operand.imm (Const.int 8 0x6e#8))]

def odGapRecoverLeafBlock7Instrs : List Instr :=
  [
    Instr.icmp "%SwitchLeaf8" (IPred.eq) 8 (Operand.reg "%7") (Operand.imm (Const.int 8 0x66#8))]

def odGapRecoverIfThen37Instrs : List Instr :=
  [
]

def odGapRecoverIfThen42Instrs : List Instr :=
  [
]

def odGapRecoverIfElse43Instrs : List Instr :=
  [
    Instr.gep "%e44" (Ty.int 8) (Operand.reg "%c") (Operand.imm (Const.int 64 0x0000000000000458#64)),
    Instr.load "%11" Ty.ptr (Operand.reg "%e44"),
    Instr.store (Ty.int 32) (Operand.imm (Const.int 32 0x00000000#32)) (Operand.reg "%11"),
    Instr.gep "%off1.i129" (Ty.int 8) (Operand.reg "%11") (Operand.imm (Const.int 64 0x0000000000000008#64)),
    Instr.store (Ty.int 64) (Operand.reg "%t.0.val") (Operand.reg "%off1.i129"),
    Instr.gep "%msg2.i130" (Ty.int 8) (Operand.reg "%11") (Operand.imm (Const.int 64 0x0000000000000010#64)),
    Instr.store (Ty.int 64) (Operand.imm (Const.int 64 0x0000000000000003#64)) (Operand.reg "%msg2.i130")]

def odGapRecoverIfEnd48Instrs : List Instr :=
  [
    Instr.phi "%lit.0" Ty.ptr [("if.then37", (Operand.reg "%litfalse")),
                                       ("if.then42", (Operand.reg "%litnull")),
                                       ("LeafBlock11", (Operand.reg "%littrue"))],
    Instr.phi "%ln.0" (Ty.int 64) [("if.then37", (Operand.imm (Const.int 64 0x0000000000000005#64))),
                                       ("if.then42", (Operand.imm (Const.int 64 0x0000000000000004#64))),
                                       ("LeafBlock11", (Operand.imm (Const.int 64 0x0000000000000004#64)))],
    Instr.binop "%sub54" (BinOp.sub) 64 (Operand.reg "%ee.0.lcssa") (Operand.reg "%t.0.val"),
    Instr.icmp "%cond.i.min" (IPred.ult) 64 (Operand.reg "%sub54") (Operand.reg "%ln.0"),
    Instr.select "%cond.i" (Ty.int 64) (Operand.reg "%cond.i.min") (Operand.reg "%sub54") (Operand.reg "%ln.0"),
    Instr.icmp "%cmp3.not28.not.i" (IPred.eq) 64 (Operand.reg "%ee.0.lcssa") (Operand.reg "%t.0.val")]

def odGapRecoverForBodyIInstrs : List Instr :=
  [
    Instr.phi "%i.029.i" (Ty.int 64) [("for.inc.i", (Operand.reg "%inc.i")),
                                       ("if.end48", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
    Instr.gep "%arrayidx.i" (Ty.int 8) (Operand.reg "%arrayidx9") (Operand.reg "%i.029.i"),
    Instr.load "%12" (Ty.int 8) (Operand.reg "%arrayidx.i"),
    Instr.gep "%arrayidx6.i" (Ty.int 8) (Operand.reg "%lit.0") (Operand.reg "%i.029.i"),
    Instr.load "%13" (Ty.int 8) (Operand.reg "%arrayidx6.i"),
    Instr.icmp "%cmp8.not.i" (IPred.eq) 8 (Operand.reg "%12") (Operand.reg "%13")]

def odGapRecoverForIncIInstrs : List Instr :=
  [
    Instr.binop "%inc.i" (BinOp.add) 64 (Operand.reg "%i.029.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
    Instr.icmp "%exitcond.not.i" (IPred.eq) 64 (Operand.reg "%inc.i") (Operand.reg "%cond.i")]

def odGapRecoverForEndIInstrs : List Instr :=
  [
    Instr.icmp "%cmp11.not.i" (IPred.eq) 64 (Operand.reg "%sub54") (Operand.reg "%ln.0")]

def odGapRecoverIfThen57Instrs : List Instr :=
  [
    Instr.phi "%ei49.0.ph" (Ty.int 64) [("for.end.i", (Operand.reg "%cond.i")),
                                       ("for.body.i", (Operand.reg "%i.029.i"))],
    Instr.gep "%e58" (Ty.int 8) (Operand.reg "%c") (Operand.imm (Const.int 64 0x0000000000000458#64)),
    Instr.load "%14" Ty.ptr (Operand.reg "%e58"),
    Instr.binop "%add60" (BinOp.add) 64 (Operand.reg "%ei49.0.ph") (Operand.reg "%t.0.val"),
    Instr.store (Ty.int 32) (Operand.imm (Const.int 32 0x00000000#32)) (Operand.reg "%14"),
    Instr.gep "%off1.i131" (Ty.int 8) (Operand.reg "%14") (Operand.imm (Const.int 64 0x0000000000000008#64)),
    Instr.store (Ty.int 64) (Operand.reg "%add60") (Operand.reg "%off1.i131"),
    Instr.gep "%msg2.i132" (Ty.int 8) (Operand.reg "%14") (Operand.imm (Const.int 64 0x0000000000000010#64)),
    Instr.store (Ty.int 64) (Operand.imm (Const.int 64 0x0000000000000002#64)) (Operand.reg "%msg2.i132")]

def odGapRecoverIfEnd67CritedgeInstrs : List Instr :=
  [
    Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000008#64))),
                             (Ty.ptr, (Operand.reg "%ei"))],
    Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000008#64))),
                             (Ty.ptr, (Operand.reg "%d"))]]

def odGapRecoverIfEnd67Instrs : List Instr :=
  [
    Instr.icmp "%cmp6919" (IPred.ult) 64 (Operand.reg "%ee.0.lcssa") (Operand.reg "%cond")]

def odGapRecoverLandRhs71Instrs : List Instr :=
  [
    Instr.phi "%s2.020" (Ty.int 64) [("while.body76", (Operand.reg "%inc77")),
                                       ("if.end67", (Operand.reg "%ee.0.lcssa"))],
    Instr.gep "%arrayidx72" (Ty.int 8) (Operand.reg "%0") (Operand.reg "%s2.020"),
    Instr.load "%15" (Ty.int 8) (Operand.reg "%arrayidx72")]

def odGapRecoverNodeBlock26Instrs : List Instr :=
  [
    Instr.icmp "%Pivot27" (IPred.slt) 8 (Operand.reg "%15") (Operand.imm (Const.int 8 0x0d#8))]

def odGapRecoverNodeBlock24Instrs : List Instr :=
  [
    Instr.icmp "%Pivot25" (IPred.slt) 8 (Operand.reg "%15") (Operand.imm (Const.int 8 0x20#8))]

def odGapRecoverLeafBlock22Instrs : List Instr :=
  [
    Instr.icmp "%SwitchLeaf23" (IPred.eq) 8 (Operand.reg "%15") (Operand.imm (Const.int 8 0x20#8))]

def odGapRecoverLeafBlock20Instrs : List Instr :=
  [
    Instr.icmp "%SwitchLeaf21" (IPred.eq) 8 (Operand.reg "%15") (Operand.imm (Const.int 8 0x0d#8))]

def odGapRecoverLeafBlock17Instrs : List Instr :=
  [
    Instr.binop "%.off18" (BinOp.add) 8 (Operand.reg "%15") (Operand.imm (Const.int 8 0xf7#8)),
    Instr.icmp "%SwitchLeaf19" (IPred.ule) 8 (Operand.reg "%.off18") (Operand.imm (Const.int 8 0x01#8))]

def odGapRecoverWhileBody76Instrs : List Instr :=
  [
    Instr.binop "%inc77" (BinOp.add) 64 (Operand.reg "%s2.020") (Operand.imm (Const.int 64 0x0000000000000001#64)),
    Instr.icmp "%exitcond24.not" (IPred.eq) 64 (Operand.reg "%inc77") (Operand.reg "%cond")]

def odGapRecoverWhileEnd78Instrs : List Instr :=
  [
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
    Instr.store (Ty.int 64) (Operand.imm (Const.int 64 0x0000000000000004#64)) (Operand.reg "%msg2.i138")]

def odGapRecoverCleanup82Instrs : List Instr :=
  [
]

-- § the pins
theorem odGapRecover_findBlock_entry :
    odGapRecoverBody.findBlock "entry" = some ⟨"entry", odGapRecoverEntryInstrs, Term.condbr (Operand.reg "%cmp") "cond.true" "cond.false"⟩ := by decide

theorem odGapRecover_findBlock_cond_true :
    odGapRecoverBody.findBlock "cond.true" = some ⟨"cond.true", odGapRecoverCondTrueInstrs, Term.br "cond.end"⟩ := by decide

theorem odGapRecover_findBlock_cond_false :
    odGapRecoverBody.findBlock "cond.false" = some ⟨"cond.false", odGapRecoverCondFalseInstrs, Term.br "cond.end"⟩ := by decide

theorem odGapRecover_findBlock_cond_end :
    odGapRecoverBody.findBlock "cond.end" = some ⟨"cond.end", odGapRecoverCondEndInstrs, Term.condbr (Operand.reg "%cmp310") "land.rhs" "while.end"⟩ := by decide

theorem odGapRecover_findBlock_land_rhs :
    odGapRecoverBody.findBlock "land.rhs" = some ⟨"land.rhs", odGapRecoverLandRhsInstrs, Term.br "NodeBlock5"⟩ := by decide

theorem odGapRecover_findBlock_NodeBlock5 :
    odGapRecoverBody.findBlock "NodeBlock5" = some ⟨"NodeBlock5", odGapRecoverNodeBlock5Instrs, Term.condbr (Operand.reg "%Pivot6") "LeafBlock" "NodeBlock"⟩ := by decide

theorem odGapRecover_findBlock_NodeBlock :
    odGapRecoverBody.findBlock "NodeBlock" = some ⟨"NodeBlock", odGapRecoverNodeBlockInstrs, Term.condbr (Operand.reg "%Pivot") "LeafBlock1" "LeafBlock3"⟩ := by decide

theorem odGapRecover_findBlock_LeafBlock3 :
    odGapRecoverBody.findBlock "LeafBlock3" = some ⟨"LeafBlock3", odGapRecoverLeafBlock3Instrs, Term.condbr (Operand.reg "%SwitchLeaf4") "while.end" "while.body"⟩ := by decide

theorem odGapRecover_findBlock_LeafBlock1 :
    odGapRecoverBody.findBlock "LeafBlock1" = some ⟨"LeafBlock1", odGapRecoverLeafBlock1Instrs, Term.condbr (Operand.reg "%SwitchLeaf2") "while.end" "while.body"⟩ := by decide

theorem odGapRecover_findBlock_LeafBlock :
    odGapRecoverBody.findBlock "LeafBlock" = some ⟨"LeafBlock", odGapRecoverLeafBlockInstrs, Term.condbr (Operand.reg "%SwitchLeaf") "while.end" "while.body"⟩ := by decide

theorem odGapRecover_findBlock_while_body :
    odGapRecoverBody.findBlock "while.body" = some ⟨"while.body", odGapRecoverWhileBodyInstrs, Term.condbr (Operand.reg "%exitcond.not") "cleanup82" "land.rhs"⟩ := by decide

theorem odGapRecover_findBlock_while_end :
    odGapRecoverBody.findBlock "while.end" = some ⟨"while.end", odGapRecoverWhileEndInstrs, Term.condbr (Operand.reg "%cmp6") "cleanup82" "if.end"⟩ := by decide

theorem odGapRecover_findBlock_if_end :
    odGapRecoverBody.findBlock "if.end" = some ⟨"if.end", odGapRecoverIfEndInstrs, Term.condbr (Operand.reg "%or.cond127") "if.then19" "if.else"⟩ := by decide

theorem odGapRecover_findBlock_if_then19 :
    odGapRecoverBody.findBlock "if.then19" = some ⟨"if.then19", odGapRecoverIfThen19Instrs, Term.condbr (Operand.reg "%tobool24.not.not") "if.then25" "if.end67.critedge"⟩ := by decide

theorem odGapRecover_findBlock_if_then25 :
    odGapRecoverBody.findBlock "if.then25" = some ⟨"if.then25", odGapRecoverIfThen25Instrs, Term.br "cleanup82"⟩ := by decide

theorem odGapRecover_findBlock_if_else :
    odGapRecoverBody.findBlock "if.else" = some ⟨"if.else", odGapRecoverIfElseInstrs, Term.br "NodeBlock15"⟩ := by decide

theorem odGapRecover_findBlock_NodeBlock15 :
    odGapRecoverBody.findBlock "NodeBlock15" = some ⟨"NodeBlock15", odGapRecoverNodeBlock15Instrs, Term.condbr (Operand.reg "%Pivot16") "LeafBlock7" "NodeBlock13"⟩ := by decide

theorem odGapRecover_findBlock_NodeBlock13 :
    odGapRecoverBody.findBlock "NodeBlock13" = some ⟨"NodeBlock13", odGapRecoverNodeBlock13Instrs, Term.condbr (Operand.reg "%Pivot14") "LeafBlock9" "LeafBlock11"⟩ := by decide

theorem odGapRecover_findBlock_LeafBlock11 :
    odGapRecoverBody.findBlock "LeafBlock11" = some ⟨"LeafBlock11", odGapRecoverLeafBlock11Instrs, Term.condbr (Operand.reg "%SwitchLeaf12") "if.end48" "if.else43"⟩ := by decide

theorem odGapRecover_findBlock_LeafBlock9 :
    odGapRecoverBody.findBlock "LeafBlock9" = some ⟨"LeafBlock9", odGapRecoverLeafBlock9Instrs, Term.condbr (Operand.reg "%SwitchLeaf10") "if.then42" "if.else43"⟩ := by decide

theorem odGapRecover_findBlock_LeafBlock7 :
    odGapRecoverBody.findBlock "LeafBlock7" = some ⟨"LeafBlock7", odGapRecoverLeafBlock7Instrs, Term.condbr (Operand.reg "%SwitchLeaf8") "if.then37" "if.else43"⟩ := by decide

theorem odGapRecover_findBlock_if_then37 :
    odGapRecoverBody.findBlock "if.then37" = some ⟨"if.then37", odGapRecoverIfThen37Instrs, Term.br "if.end48"⟩ := by decide

theorem odGapRecover_findBlock_if_then42 :
    odGapRecoverBody.findBlock "if.then42" = some ⟨"if.then42", odGapRecoverIfThen42Instrs, Term.br "if.end48"⟩ := by decide

theorem odGapRecover_findBlock_if_else43 :
    odGapRecoverBody.findBlock "if.else43" = some ⟨"if.else43", odGapRecoverIfElse43Instrs, Term.br "cleanup82"⟩ := by decide

theorem odGapRecover_findBlock_if_end48 :
    odGapRecoverBody.findBlock "if.end48" = some ⟨"if.end48", odGapRecoverIfEnd48Instrs, Term.condbr (Operand.reg "%cmp3.not28.not.i") "for.end.i" "for.body.i"⟩ := by decide

theorem odGapRecover_findBlock_for_body_i :
    odGapRecoverBody.findBlock "for.body.i" = some ⟨"for.body.i", odGapRecoverForBodyIInstrs, Term.condbr (Operand.reg "%cmp8.not.i") "for.inc.i" "if.then57"⟩ := by decide

theorem odGapRecover_findBlock_for_inc_i :
    odGapRecoverBody.findBlock "for.inc.i" = some ⟨"for.inc.i", odGapRecoverForIncIInstrs, Term.condbr (Operand.reg "%exitcond.not.i") "for.end.i" "for.body.i"⟩ := by decide

theorem odGapRecover_findBlock_for_end_i :
    odGapRecoverBody.findBlock "for.end.i" = some ⟨"for.end.i", odGapRecoverForEndIInstrs, Term.condbr (Operand.reg "%cmp11.not.i") "if.end67" "if.then57"⟩ := by decide

theorem odGapRecover_findBlock_if_then57 :
    odGapRecoverBody.findBlock "if.then57" = some ⟨"if.then57", odGapRecoverIfThen57Instrs, Term.br "cleanup82"⟩ := by decide

theorem odGapRecover_findBlock_if_end67_critedge :
    odGapRecoverBody.findBlock "if.end67.critedge" = some ⟨"if.end67.critedge", odGapRecoverIfEnd67CritedgeInstrs, Term.br "if.end67"⟩ := by decide

theorem odGapRecover_findBlock_if_end67 :
    odGapRecoverBody.findBlock "if.end67" = some ⟨"if.end67", odGapRecoverIfEnd67Instrs, Term.condbr (Operand.reg "%cmp6919") "land.rhs71" "while.end78"⟩ := by decide

theorem odGapRecover_findBlock_land_rhs71 :
    odGapRecoverBody.findBlock "land.rhs71" = some ⟨"land.rhs71", odGapRecoverLandRhs71Instrs, Term.br "NodeBlock26"⟩ := by decide

theorem odGapRecover_findBlock_NodeBlock26 :
    odGapRecoverBody.findBlock "NodeBlock26" = some ⟨"NodeBlock26", odGapRecoverNodeBlock26Instrs, Term.condbr (Operand.reg "%Pivot27") "LeafBlock17" "NodeBlock24"⟩ := by decide

theorem odGapRecover_findBlock_NodeBlock24 :
    odGapRecoverBody.findBlock "NodeBlock24" = some ⟨"NodeBlock24", odGapRecoverNodeBlock24Instrs, Term.condbr (Operand.reg "%Pivot25") "LeafBlock20" "LeafBlock22"⟩ := by decide

theorem odGapRecover_findBlock_LeafBlock22 :
    odGapRecoverBody.findBlock "LeafBlock22" = some ⟨"LeafBlock22", odGapRecoverLeafBlock22Instrs, Term.condbr (Operand.reg "%SwitchLeaf23") "while.body76" "while.end78"⟩ := by decide

theorem odGapRecover_findBlock_LeafBlock20 :
    odGapRecoverBody.findBlock "LeafBlock20" = some ⟨"LeafBlock20", odGapRecoverLeafBlock20Instrs, Term.condbr (Operand.reg "%SwitchLeaf21") "while.body76" "while.end78"⟩ := by decide

theorem odGapRecover_findBlock_LeafBlock17 :
    odGapRecoverBody.findBlock "LeafBlock17" = some ⟨"LeafBlock17", odGapRecoverLeafBlock17Instrs, Term.condbr (Operand.reg "%SwitchLeaf19") "while.body76" "while.end78"⟩ := by decide

theorem odGapRecover_findBlock_while_body76 :
    odGapRecoverBody.findBlock "while.body76" = some ⟨"while.body76", odGapRecoverWhileBody76Instrs, Term.condbr (Operand.reg "%exitcond24.not") "while.end78" "land.rhs71"⟩ := by decide

theorem odGapRecover_findBlock_while_end78 :
    odGapRecoverBody.findBlock "while.end78" = some ⟨"while.end78", odGapRecoverWhileEnd78Instrs, Term.br "cleanup82"⟩ := by decide

theorem odGapRecover_findBlock_cleanup82 :
    odGapRecoverBody.findBlock "cleanup82" = some ⟨"cleanup82", odGapRecoverCleanup82Instrs, Term.ret Ty.void none⟩ := by decide

-- § the instruction-list projections
theorem odGapRecoverEntryInstrs_eq :
    (odGapRecoverBody.findBlock "entry").map (·.instrs) = some odGapRecoverEntryInstrs := by decide

theorem odGapRecoverCondTrueInstrs_eq :
    (odGapRecoverBody.findBlock "cond.true").map (·.instrs) = some odGapRecoverCondTrueInstrs := by decide

theorem odGapRecoverCondFalseInstrs_eq :
    (odGapRecoverBody.findBlock "cond.false").map (·.instrs) = some odGapRecoverCondFalseInstrs := by decide

theorem odGapRecoverCondEndInstrs_eq :
    (odGapRecoverBody.findBlock "cond.end").map (·.instrs) = some odGapRecoverCondEndInstrs := by decide

theorem odGapRecoverLandRhsInstrs_eq :
    (odGapRecoverBody.findBlock "land.rhs").map (·.instrs) = some odGapRecoverLandRhsInstrs := by decide

theorem odGapRecoverNodeBlock5Instrs_eq :
    (odGapRecoverBody.findBlock "NodeBlock5").map (·.instrs) = some odGapRecoverNodeBlock5Instrs := by decide

theorem odGapRecoverNodeBlockInstrs_eq :
    (odGapRecoverBody.findBlock "NodeBlock").map (·.instrs) = some odGapRecoverNodeBlockInstrs := by decide

theorem odGapRecoverLeafBlock3Instrs_eq :
    (odGapRecoverBody.findBlock "LeafBlock3").map (·.instrs) = some odGapRecoverLeafBlock3Instrs := by decide

theorem odGapRecoverLeafBlock1Instrs_eq :
    (odGapRecoverBody.findBlock "LeafBlock1").map (·.instrs) = some odGapRecoverLeafBlock1Instrs := by decide

theorem odGapRecoverLeafBlockInstrs_eq :
    (odGapRecoverBody.findBlock "LeafBlock").map (·.instrs) = some odGapRecoverLeafBlockInstrs := by decide

theorem odGapRecoverWhileBodyInstrs_eq :
    (odGapRecoverBody.findBlock "while.body").map (·.instrs) = some odGapRecoverWhileBodyInstrs := by decide

theorem odGapRecoverWhileEndInstrs_eq :
    (odGapRecoverBody.findBlock "while.end").map (·.instrs) = some odGapRecoverWhileEndInstrs := by decide

theorem odGapRecoverIfEndInstrs_eq :
    (odGapRecoverBody.findBlock "if.end").map (·.instrs) = some odGapRecoverIfEndInstrs := by decide

theorem odGapRecoverIfThen19Instrs_eq :
    (odGapRecoverBody.findBlock "if.then19").map (·.instrs) = some odGapRecoverIfThen19Instrs := by decide

theorem odGapRecoverIfThen25Instrs_eq :
    (odGapRecoverBody.findBlock "if.then25").map (·.instrs) = some odGapRecoverIfThen25Instrs := by decide

theorem odGapRecoverIfElseInstrs_eq :
    (odGapRecoverBody.findBlock "if.else").map (·.instrs) = some odGapRecoverIfElseInstrs := by decide

theorem odGapRecoverNodeBlock15Instrs_eq :
    (odGapRecoverBody.findBlock "NodeBlock15").map (·.instrs) = some odGapRecoverNodeBlock15Instrs := by decide

theorem odGapRecoverNodeBlock13Instrs_eq :
    (odGapRecoverBody.findBlock "NodeBlock13").map (·.instrs) = some odGapRecoverNodeBlock13Instrs := by decide

theorem odGapRecoverLeafBlock11Instrs_eq :
    (odGapRecoverBody.findBlock "LeafBlock11").map (·.instrs) = some odGapRecoverLeafBlock11Instrs := by decide

theorem odGapRecoverLeafBlock9Instrs_eq :
    (odGapRecoverBody.findBlock "LeafBlock9").map (·.instrs) = some odGapRecoverLeafBlock9Instrs := by decide

theorem odGapRecoverLeafBlock7Instrs_eq :
    (odGapRecoverBody.findBlock "LeafBlock7").map (·.instrs) = some odGapRecoverLeafBlock7Instrs := by decide

theorem odGapRecoverIfThen37Instrs_eq :
    (odGapRecoverBody.findBlock "if.then37").map (·.instrs) = some odGapRecoverIfThen37Instrs := by decide

theorem odGapRecoverIfThen42Instrs_eq :
    (odGapRecoverBody.findBlock "if.then42").map (·.instrs) = some odGapRecoverIfThen42Instrs := by decide

theorem odGapRecoverIfElse43Instrs_eq :
    (odGapRecoverBody.findBlock "if.else43").map (·.instrs) = some odGapRecoverIfElse43Instrs := by decide

theorem odGapRecoverIfEnd48Instrs_eq :
    (odGapRecoverBody.findBlock "if.end48").map (·.instrs) = some odGapRecoverIfEnd48Instrs := by decide

theorem odGapRecoverForBodyIInstrs_eq :
    (odGapRecoverBody.findBlock "for.body.i").map (·.instrs) = some odGapRecoverForBodyIInstrs := by decide

theorem odGapRecoverForIncIInstrs_eq :
    (odGapRecoverBody.findBlock "for.inc.i").map (·.instrs) = some odGapRecoverForIncIInstrs := by decide

theorem odGapRecoverForEndIInstrs_eq :
    (odGapRecoverBody.findBlock "for.end.i").map (·.instrs) = some odGapRecoverForEndIInstrs := by decide

theorem odGapRecoverIfThen57Instrs_eq :
    (odGapRecoverBody.findBlock "if.then57").map (·.instrs) = some odGapRecoverIfThen57Instrs := by decide

theorem odGapRecoverIfEnd67CritedgeInstrs_eq :
    (odGapRecoverBody.findBlock "if.end67.critedge").map (·.instrs) = some odGapRecoverIfEnd67CritedgeInstrs := by decide

theorem odGapRecoverIfEnd67Instrs_eq :
    (odGapRecoverBody.findBlock "if.end67").map (·.instrs) = some odGapRecoverIfEnd67Instrs := by decide

theorem odGapRecoverLandRhs71Instrs_eq :
    (odGapRecoverBody.findBlock "land.rhs71").map (·.instrs) = some odGapRecoverLandRhs71Instrs := by decide

theorem odGapRecoverNodeBlock26Instrs_eq :
    (odGapRecoverBody.findBlock "NodeBlock26").map (·.instrs) = some odGapRecoverNodeBlock26Instrs := by decide

theorem odGapRecoverNodeBlock24Instrs_eq :
    (odGapRecoverBody.findBlock "NodeBlock24").map (·.instrs) = some odGapRecoverNodeBlock24Instrs := by decide

theorem odGapRecoverLeafBlock22Instrs_eq :
    (odGapRecoverBody.findBlock "LeafBlock22").map (·.instrs) = some odGapRecoverLeafBlock22Instrs := by decide

theorem odGapRecoverLeafBlock20Instrs_eq :
    (odGapRecoverBody.findBlock "LeafBlock20").map (·.instrs) = some odGapRecoverLeafBlock20Instrs := by decide

theorem odGapRecoverLeafBlock17Instrs_eq :
    (odGapRecoverBody.findBlock "LeafBlock17").map (·.instrs) = some odGapRecoverLeafBlock17Instrs := by decide

theorem odGapRecoverWhileBody76Instrs_eq :
    (odGapRecoverBody.findBlock "while.body76").map (·.instrs) = some odGapRecoverWhileBody76Instrs := by decide

theorem odGapRecoverWhileEnd78Instrs_eq :
    (odGapRecoverBody.findBlock "while.end78").map (·.instrs) = some odGapRecoverWhileEnd78Instrs := by decide

theorem odGapRecoverCleanup82Instrs_eq :
    (odGapRecoverBody.findBlock "cleanup82").map (·.instrs) = some odGapRecoverCleanup82Instrs := by decide


/-! ### The instruction steps this body needs

`BlockEval`'s chain steps are the 64-bit shapes the pipeline's blocks use.  This
body is byte and 32-bit work as well — the switch's `icmp slt i8`/`icmp ule i8`,
the index word's `i32` load and `i32` element `getelementptr`, the record's `i32`
and immediate `i64` stores, and calls of two and four arguments — so the steps
below are the same shapes at this body's widths.  Each is a `denoteCode` step,
nothing else. -/

theorem gap_step_alloca (calls : Calls) (env : Env) (s : State) (d : String) (ty : Ty)
    (al : Nat) :
    evalInstr calls (stateAt env s) (.alloca d ty al) =
      some (stateAt ((d, .ptr s.next) :: env) { s with next := s.next + ty.sizeBytes }) := by
  simp only [evalInstr, stateAt]

theorem gap_denote_alloca (calls : Calls) (env : Env) (s : State) (d : String) (ty : Ty)
    (al : Nat) (is : List Instr) :
    denoteCode calls (.alloca d ty al :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt ((d, .ptr s.next) :: env) { s with next := s.next + ty.sizeBytes }) := by
  rw [denoteCode_cons_of _ _ _ _ _ (gap_step_alloca calls env s d ty al)]

theorem gap_step_add_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {w : Nat} {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) :
    evalInstr calls (stateAt env s) (.binop d .add w (.reg a) (.imm (.int w c))) =
      some (stateAt ((d, .int w (x + c)) :: env) s) := by
  simp only [evalInstr, evalOperand, stateAt, ha, State.bind, evalBinopNat, evalBinop,
    Const.toValue, Value.intToNat, Option.map, ite_true, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

theorem gap_denote_add_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {w : Nat} {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) (is : List Instr) :
    denoteCode calls (.binop d .add w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (x + c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (gap_step_add_imm calls env s d a ha)]

theorem gap_step_or_reg (calls : Calls) (env : Env) (s : State) (d a b : String)
    {w : Nat} {x y : BitVec w}
    (ha : lookupName env a = some (.int w x)) (hb : lookupName env b = some (.int w y)) :
    evalInstr calls (stateAt env s) (.binop d .or w (.reg a) (.reg b)) =
      some (stateAt ((d, .int w (x ||| y)) :: env) s) := by
  simp only [evalInstr, evalOperand, stateAt, ha, hb, State.bind, evalBinopNat, evalBinop,
    Value.intToNat, Option.map, ite_true, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem gap_denote_or_reg (calls : Calls) (env : Env) (s : State) (d a b : String)
    {w : Nat} {x y : BitVec w}
    (ha : lookupName env a = some (.int w x)) (hb : lookupName env b = some (.int w y))
    (is : List Instr) :
    denoteCode calls (.binop d .or w (.reg a) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (x ||| y)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (gap_step_or_reg calls env s d a b ha hb)]

theorem gap_step_icmp_eq_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {w : Nat} {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) :
    evalInstr calls (stateAt env s) (.icmp d .eq w (.reg a) (.imm (.int w c))) =
      some (stateAt ((d, .int 1 (evalICmp .eq x c)) :: env) s) := by
  simp only [evalInstr, evalOperand, stateAt, ha, State.bind, Const.toValue, Value.intToNat,
    ite_true, evalICmpNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem gap_denote_icmp_eq_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {w : Nat} {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) (is : List Instr) :
    denoteCode calls (.icmp d .eq w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp .eq x c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (gap_step_icmp_eq_imm calls env s d a ha)]

theorem gap_step_icmp_slt_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {w : Nat} {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) :
    evalInstr calls (stateAt env s) (.icmp d .slt w (.reg a) (.imm (.int w c))) =
      some (stateAt ((d, .int 1 (evalICmp .slt x c)) :: env) s) := by
  simp only [evalInstr, evalOperand, stateAt, ha, State.bind, Const.toValue, Value.intToNat,
    ite_true, evalICmpNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem gap_denote_icmp_slt_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {w : Nat} {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) (is : List Instr) :
    denoteCode calls (.icmp d .slt w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp .slt x c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (gap_step_icmp_slt_imm calls env s d a ha)]

theorem gap_step_icmp_ule_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {w : Nat} {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) :
    evalInstr calls (stateAt env s) (.icmp d .ule w (.reg a) (.imm (.int w c))) =
      some (stateAt ((d, .int 1 (evalICmp .ule x c)) :: env) s) := by
  simp only [evalInstr, evalOperand, stateAt, ha, State.bind, Const.toValue, Value.intToNat,
    ite_true, evalICmpNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem gap_denote_icmp_ule_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {w : Nat} {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) (is : List Instr) :
    denoteCode calls (.icmp d .ule w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp .ule x c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (gap_step_icmp_ule_imm calls env s d a ha)]

theorem gap_step_icmp_ult_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {w : Nat} {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) :
    evalInstr calls (stateAt env s) (.icmp d .ult w (.reg a) (.imm (.int w c))) =
      some (stateAt ((d, .int 1 (evalICmp .ult x c)) :: env) s) := by
  simp only [evalInstr, evalOperand, stateAt, ha, State.bind, Const.toValue, Value.intToNat,
    ite_true, evalICmpNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem gap_denote_icmp_ult_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {w : Nat} {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) (is : List Instr) :
    denoteCode calls (.icmp d .ult w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp .ult x c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (gap_step_icmp_ult_imm calls env s d a ha)]

theorem gap_step_icmp_eq_reg (calls : Calls) (env : Env) (s : State) (d a b : String)
    {w : Nat} {x y : BitVec w}
    (ha : lookupName env a = some (.int w x)) (hb : lookupName env b = some (.int w y)) :
    evalInstr calls (stateAt env s) (.icmp d .eq w (.reg a) (.reg b)) =
      some (stateAt ((d, .int 1 (evalICmp .eq x y)) :: env) s) := by
  simp only [evalInstr, evalOperand, stateAt, ha, hb, State.bind, Value.intToNat,
    ite_true, evalICmpNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem gap_denote_icmp_eq_reg (calls : Calls) (env : Env) (s : State) (d a b : String)
    {w : Nat} {x y : BitVec w}
    (ha : lookupName env a = some (.int w x)) (hb : lookupName env b = some (.int w y))
    (is : List Instr) :
    denoteCode calls (.icmp d .eq w (.reg a) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp .eq x y)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (gap_step_icmp_eq_reg calls env s d a b ha hb)]

theorem gap_step_icmp_ult_reg (calls : Calls) (env : Env) (s : State) (d a b : String)
    {w : Nat} {x y : BitVec w}
    (ha : lookupName env a = some (.int w x)) (hb : lookupName env b = some (.int w y)) :
    evalInstr calls (stateAt env s) (.icmp d .ult w (.reg a) (.reg b)) =
      some (stateAt ((d, .int 1 (evalICmp .ult x y)) :: env) s) := by
  simp only [evalInstr, evalOperand, stateAt, ha, hb, State.bind, Value.intToNat,
    ite_true, evalICmpNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem gap_denote_icmp_ult_reg (calls : Calls) (env : Env) (s : State) (d a b : String)
    {w : Nat} {x y : BitVec w}
    (ha : lookupName env a = some (.int w x)) (hb : lookupName env b = some (.int w y))
    (is : List Instr) :
    denoteCode calls (.icmp d .ult w (.reg a) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp .ult x y)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (gap_step_icmp_ult_reg calls env s d a b ha hb)]

theorem gap_step_load8 (calls : Calls) (env : Env) (s : State) (d p : String)
    {a : Nat} {v : BitVec 8}
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 1 = some (natToBytes v.toNat 1)) :
    evalInstr calls (stateAt env s) (.load d (.int 8) (.reg p)) =
      some (stateAt ((d, .int 8 v) :: env) s) := by
  simp only [evalInstr, evalOperand, stateAt, hp, State.bind, hv, loadValue,
    show ((8 : Nat) = 0) = False from by decide, ite_false, Option.map, natToBytes_toNat,
    show (256 : Nat) ^ 1 = 2 ^ 8 from by decide, Nat.mod_eq_of_lt v.isLt,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem gap_denote_load8 (calls : Calls) (env : Env) (s : State) (d p : String)
    {a : Nat} {v : BitVec 8}
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 1 = some (natToBytes v.toNat 1)) (is : List Instr) :
    denoteCode calls (.load d (.int 8) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 8 v) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (gap_step_load8 calls env s d p hp hv)]

theorem gap_step_load32 (calls : Calls) (env : Env) (s : State) (d p : String)
    {a : Nat} {v : BitVec 32}
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 4 = some (natToBytes v.toNat 4)) :
    evalInstr calls (stateAt env s) (.load d (.int 32) (.reg p)) =
      some (stateAt ((d, .int 32 v) :: env) s) := by
  simp only [evalInstr, evalOperand, stateAt, hp, State.bind, hv, loadValue,
    show ((32 : Nat) = 0) = False from by decide,
    show (32 + 7) / 8 = 4 from by decide, ite_false, Option.map, natToBytes_toNat,
    show (256 : Nat) ^ 4 = 2 ^ 32 from by decide, Nat.mod_eq_of_lt v.isLt,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem gap_denote_load32 (calls : Calls) (env : Env) (s : State) (d p : String)
    {a : Nat} {v : BitVec 32}
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 4 = some (natToBytes v.toNat 4)) (is : List Instr) :
    denoteCode calls (.load d (.int 32) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 32 v) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (gap_step_load32 calls env s d p hp hv)]

theorem gap_step_loadPtr (calls : Calls) (env : Env) (s : State) (d p : String)
    {a v : Nat}
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 8 = some (natToBytes v 8)) (hv64 : v < 2 ^ 64) :
    evalInstr calls (stateAt env s) (.load d Ty.ptr (.reg p)) =
      some (stateAt ((d, .ptr v) :: env) s) := by
  simp only [evalInstr, evalOperand, stateAt, hp, State.bind, hv, loadValue, Option.map,
    natToBytes_toNat, show (256 : Nat) ^ 8 = 2 ^ 64 from by decide,
    Nat.mod_eq_of_lt hv64]

theorem gap_denote_loadPtr (calls : Calls) (env : Env) (s : State) (d p : String)
    {a v : Nat}
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 8 = some (natToBytes v 8)) (hv64 : v < 2 ^ 64)
    (is : List Instr) :
    denoteCode calls (.load d Ty.ptr (.reg p) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .ptr v) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (gap_step_loadPtr calls env s d p hp hv hv64)]

theorem gap_step_store_imm32 (calls : Calls) (env : Env) (s : State) (p : String)
    {c : BitVec 32} {a : Nat}
    (hp : lookupName env p = some (.ptr a)) :
    evalInstr calls (stateAt env s) (.store (.int 32) (.imm (.int 32 c)) (.reg p)) =
      some (stateAt env { s with mem := writeBytes s.mem a (natToBytes c.toNat 4) }) := by
  simp only [evalInstr, evalOperand, stateAt, hp, State.bind, Const.toValue, storeValue,
    Option.map, ite_true, show ((32 : Nat) = 32) = True from by decide]

theorem gap_denote_store_imm32 (calls : Calls) (env : Env) (s : State) (p : String)
    {c : BitVec 32} {a : Nat}
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store (.int 32) (.imm (.int 32 c)) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt env { s with mem := writeBytes s.mem a (natToBytes c.toNat 4) }) := by
  rw [denoteCode_cons_of _ _ _ _ _ (gap_step_store_imm32 calls env s p hp)]

theorem gap_step_store_imm64 (calls : Calls) (env : Env) (s : State) (p : String)
    {c : BitVec 64} {a : Nat}
    (hp : lookupName env p = some (.ptr a)) :
    evalInstr calls (stateAt env s) (.store (.int 64) (.imm (.int 64 c)) (.reg p)) =
      some (stateAt env { s with mem := writeBytes s.mem a (natToBytes c.toNat 8) }) := by
  simp only [evalInstr, evalOperand, stateAt, hp, State.bind, Const.toValue, storeValue,
    Option.map, ite_true, show ((64 : Nat) = 64) = True from by decide]

theorem gap_denote_store_imm64 (calls : Calls) (env : Env) (s : State) (p : String)
    {c : BitVec 64} {a : Nat}
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store (.int 64) (.imm (.int 64 c)) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt env { s with mem := writeBytes s.mem a (natToBytes c.toNat 8) }) := by
  rw [denoteCode_cons_of _ _ _ _ _ (gap_step_store_imm64 calls env s p hp)]

theorem gap_step_gep32 (calls : Calls) (env : Env) (s : State) (d base off : String)
    {a : Nat} {idx : BitVec 64}
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 idx))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63) :
    evalInstr calls (stateAt env s) (.gep d (.int 32) (.reg base) (.reg off)) =
      some (stateAt ((d, .ptr (a + (idx.signExtend 64).toNat * 4)) :: env) s) := by
  simp only [evalInstr, evalOperand, stateAt, hb, ho, State.bind, ite_eq_left hpos,
    Ty.sizeBytes]

theorem gap_denote_gep32 (calls : Calls) (env : Env) (s : State) (d base off : String)
    {a : Nat} {idx : BitVec 64}
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 idx))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63) (is : List Instr) :
    denoteCode calls (.gep d (.int 32) (.reg base) (.reg off) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .ptr (a + (idx.signExtend 64).toNat * 4)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (gap_step_gep32 calls env s d base off hb ho hpos)]

theorem gap_step_call4 (calls : Calls) (env : Env) (s : State) (d callee : String)
    (o1 o2 o3 o4 : Operand) {v1 v2 v3 v4 : Value} {r : CallOutcome}
    (h1 : evalOperand (stateAt env s) o1 = some v1)
    (h2 : evalOperand (stateAt env s) o2 = some v2)
    (h3 : evalOperand (stateAt env s) o3 = some v3)
    (h4 : evalOperand (stateAt env s) o4 = some v4)
    (hc : calls callee [v1, v2, v3, v4] s.mem s.next = some r) :
    evalInstr calls (stateAt env s)
        (.call d (Ty.int 32) callee [(Ty.ptr, o1), (Ty.int 64, o2), (Ty.ptr, o3),
          (Ty.ptr, o4)]) =
      some (stateAt ((d, r.ret) :: env) { s with mem := r.mem, next := r.next }) := by
  simp only [evalInstr, h1, h2, h3, h4, evalOperands]
  rw [stateAt_mem, stateAt_next, hc]
  rfl

theorem gap_denote_call4 (calls : Calls) (env : Env) (s : State) (d callee : String)
    (o1 o2 o3 o4 : Operand) {v1 v2 v3 v4 : Value} {r : CallOutcome}
    (h1 : evalOperand (stateAt env s) o1 = some v1)
    (h2 : evalOperand (stateAt env s) o2 = some v2)
    (h3 : evalOperand (stateAt env s) o3 = some v3)
    (h4 : evalOperand (stateAt env s) o4 = some v4)
    (hc : calls callee [v1, v2, v3, v4] s.mem s.next = some r) (is : List Instr) :
    denoteCode calls
        (.call d (Ty.int 32) callee [(Ty.ptr, o1), (Ty.int 64, o2), (Ty.ptr, o3),
          (Ty.ptr, o4)] :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt ((d, r.ret) :: env) { s with mem := r.mem, next := r.next }) := by
  rw [denoteCode_cons_of _ _ _ _ _ (gap_step_call4 calls env s d callee o1 o2 o3 o4
    h1 h2 h3 h4 hc)]

theorem gap_step_callVoid2 (calls : Calls) (env : Env) (s : State) (callee : String)
    (o1 o2 : Operand) {v1 v2 : Value} {r : CallOutcome}
    (h1 : evalOperand (stateAt env s) o1 = some v1)
    (h2 : evalOperand (stateAt env s) o2 = some v2)
    (hc : calls callee [v1, v2] s.mem s.next = some r) :
    evalInstr calls (stateAt env s) (.callVoid callee [(Ty.int 64, o1), (Ty.ptr, o2)]) =
      some (stateAt env { s with mem := r.mem, next := r.next }) := by
  simp only [evalInstr, h1, h2, evalOperands]
  rw [stateAt_mem, stateAt_next, hc]
  rfl

theorem gap_denote_callVoid2 (calls : Calls) (env : Env) (s : State) (callee : String)
    (o1 o2 : Operand) {v1 v2 : Value} {r : CallOutcome}
    (h1 : evalOperand (stateAt env s) o1 = some v1)
    (h2 : evalOperand (stateAt env s) o2 = some v2)
    (hc : calls callee [v1, v2] s.mem s.next = some r) (is : List Instr) :
    denoteCode calls (.callVoid callee [(Ty.int 64, o1), (Ty.ptr, o2)] :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt env { s with mem := r.mem, next := r.next }) := by
  rw [denoteCode_cons_of _ _ _ _ _ (gap_step_callVoid2 calls env s callee o1 o2 h1 h2 hc)]

theorem gap_step_gep8_imm (calls : Calls) (env : Env) (s : State) (d base : String)
    (c : BitVec 64) {a : Nat}
    (hb : lookupName env base = some (.ptr a))
    (hpos : (c.signExtend 64).toNat < 2 ^ 63) :
    evalInstr calls (stateAt env s) (.gep d (.int 8) (.reg base) (.imm (.int 64 c))) =
      some (stateAt ((d, .ptr (a + (c.signExtend 64).toNat)) :: env) s) := by
  rw [evalInstr_gep_i8 (s := stateAt env s)
    (hb := evalOperand_reg_of env s base (.ptr a) hb)
    (ho := evalOperand_lit_of _ 64 c) (hpos := hpos)]
  simp only [stateAt, State.bind]

theorem gap_denote_gep8_imm (calls : Calls) (env : Env) (s : State) (d base : String)
    (c : BitVec 64) {a : Nat}
    (hb : lookupName env base = some (.ptr a))
    (hpos : (c.signExtend 64).toNat < 2 ^ 63) (is : List Instr) :
    denoteCode calls (.gep d (.int 8) (.reg base) (.imm (.int 64 c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .ptr (a + (c.signExtend 64).toNat)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (gap_step_gep8_imm calls env s d base c hb hpos)]

/-! ### The terminator steps

The three terminator shapes the body's blocks end in.  Each is `execTerm`'s own
definition at that shape, named so a block step can rewrite the branch bit it
computed rather than case-splitting inside the step. -/

theorem gap_execTerm_br (s : State) (d : String) :
    execTerm s (.br d) = .jump { s with pc := d, pre := some s.pc } := rfl

theorem gap_execTerm_condbr_one {s : State} {c : Operand} {t f : String}
    (h : evalOperand s c = some (.int 1 1)) :
    execTerm s (.condbr c t f) = .jump { s with pc := t, pre := some s.pc } := by
  simp [execTerm, h]

theorem gap_execTerm_condbr_zero {s : State} {c : Operand} {t f : String}
    (h : evalOperand s c = some (.int 1 0)) :
    execTerm s (.condbr c t f) = .jump { s with pc := f, pre := some s.pc } := by
  simp [execTerm, h]

theorem gap_execTerm_retVoid (s : State) :
    execTerm s (.ret Ty.void none) = .ret none s := rfl

macro "gap_step" : tactic => `(tactic|
  (first
   | block_step
   | rw [gap_denote_alloca _ _ _ _ _ _ _]
   | rw [gap_denote_add_imm _ _ _ _ _ ?_ _]
   | rw [gap_denote_or_reg _ _ _ _ _ _ ?_ ?_ _]
   | rw [gap_denote_icmp_eq_imm _ _ _ _ _ ?_ _]
   | rw [gap_denote_icmp_slt_imm _ _ _ _ _ ?_ _]
   | rw [gap_denote_icmp_ule_imm _ _ _ _ _ ?_ _]
   | rw [gap_denote_icmp_ult_imm _ _ _ _ _ ?_ _]
   | rw [gap_denote_icmp_eq_reg _ _ _ _ _ _ ?_ ?_ _]
   | rw [gap_denote_icmp_ult_reg _ _ _ _ _ _ ?_ ?_ _]
   | rw [gap_denote_load8 _ _ _ _ _ ?_ ?_ _]
   | rw [gap_denote_load32 _ _ _ _ _ ?_ ?_ _]
   | rw [gap_denote_loadPtr _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [gap_denote_store_imm32 _ _ _ _ ?_ _]
   | rw [gap_denote_store_imm64 _ _ _ _ ?_ _]
   | rw [gap_denote_gep32 _ _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [gap_denote_gep8_imm _ _ _ _ _ _ ?_ ?_ _]
   | rw [gap_denote_call4 _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ _]
   | rw [gap_denote_callVoid2 _ _ _ _ _ _ ?_ ?_ ?_ _]))

macro "gap_eval" : tactic => `(tactic|
  (repeat gap_step
   block_close))

/-! ### Axiom footprints

The steps are `evalInstr`'s own definition at one instruction shape; the three
that carry a `BitVec` arithmetic are the only ones that could pick up a carrier,
and they do not. -/
#print axioms gap_step_add_imm
#print axioms gap_step_icmp_slt_imm
#print axioms gap_step_load8
#print axioms gap_step_loadPtr
#print axioms gap_step_gep32
#print axioms gap_step_call4
#print axioms gap_denote_alloca

end LeanLLVM.Refinement
