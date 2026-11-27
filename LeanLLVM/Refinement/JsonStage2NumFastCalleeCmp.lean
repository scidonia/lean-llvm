/-
`stk_cmp`'s emitted body, and the fifth symbol it needs before the epilogue's
loop can be stated at its callee.

`JsonStage2NumFastEpilogueLoop` proved that the release selection leaves the
rounding loop's comparison unanswered, and named the callee half's fourth entry
`FbStkCmpAnswered`.  This module captures the body that entry would have to be
answered with, and finds that the body is not a closed unit either.

**The body is large because the comparison's helpers were inlined.**  The
emission at the measured compiler line inlines `stk_copy`, `stk_shl` and
`stk_cmp_bn` into `stk_cmp`, and the optimizer unrolls the shift loop four limbs
an iteration, so the captured body is 104 blocks and 757 instructions — two
allocations of `%struct.StkBn`, the copy's fast path, the shift's unrolled and
residual loops, and the bignum comparison's loop.  `stk_mul_u64` stays out of
line, as the capture's transform marks it.

**The copy is a fortified `memcpy`, and it is a fifth symbol.**  `stk_copy`
copies `(size_t)s->n * sizeof s->w[0]` bytes to a 776-byte object, and the
compiler line's hardening replaces the library call with `__memcpy_chk(dst,
src, n, 776)`.  That is a symbol of the C library rather than of `stage2.c`, and
no selection in this tree answers it: `stage2NumFastCalls` answers the three
conversion callees, `s2HelperCalls` the lifetime markers, `memset` and the trap,
and delegates the rest to `noCalls`.  So the fourth callee's body needs a fifth
answer, and the epilogue's loop is `ub` at that body's first copy — the copy is
on every path that carries a nonzero significand, and the loop's own `%v->m`
count is positive — so the loop is undefined before its first comparison.

**What this module establishes.**

* the pin — `numCmpSrc` is the fixture, `firstFunctionWith numCmpLayout` of it is
  `numCmpBody` block by block, with a mutated-text control and the parsed shape
  the inventory records (104 blocks, 757 instructions, 3 parameters);
* the entry's run and the two steps after it — `numCmp_entry_denote`,
  `numCmp_ifThen_denote` and `numCmp_ifThenI_denote_none`: from the entry state
  the first block allocates, marks its two ranges live, reads the sticky flag and
  branches, the second copies the count and branches, and the third's copy is
  undefined when `__memcpy_chk` is unanswered (`numCmp_run_ub`: `runFuel` at
  three steps is `some .ub`);
* the environment — `numCmpCalls` answers the body's own callees: the lifetime
  markers and `memset` through the walk's staging, `stk_mul_u64` through
  `numStkMulAnswer`, and everything else — `__memcpy_chk` included — to the base;
  `numCmpBodyCalls` is a selection with `stk_cmp` answered by this body's run;
* the arm, negatively — `numCmpBodyCalls_none`: at any base that leaves
  `__memcpy_chk` unanswered, the answered `stk_cmp` answers *nothing* at the
  state the epilogue's loop passes, so this body cannot replace the site's `ub`
  with the model.  `numCmpBodyCalls_stage2_none` is that fact at the
  release selection: adding `stk_cmp` to the callee half does not close it;
* the restated boundary — `FbMemcpyAnswered` is the fifth answer,
  `FbEpilogueAnsweredMem` is `FbEpilogueAnswered` with it, `fb_tail_answeredMem`
  is the fallback's tail there, and `fbEpilogueAnsweredMem_not_release` is the
  release selection failing it.  What the answered boundary still carries is
  named too: `FbLoopEntry` is the entry state the loop is stated at, whose word
  and cells are read from the digits array and the staged window, and
  `fb_loopEntry_tail` is the tail at such a state.

**The layout the fixture is parsed at.**  The body's two allocations name
`%struct.StkBn`, which is `uint64_t w[96]` and the `int` count — 776 bytes —
and the offsets its `getelementptr`s use are the byte offsets of `%struct.Stk`'s
fields (the copy source at 776, the exponent at 1552, the sticky flag at 1560),
so the layout states `StkBn` 776 and `Stk` 1568.

There is no `sorry`, `admit` or `native_decide` below.
-/
import LeanLLVM.Refinement.JsonStage2NumFastEpilogueLoop
import LeanLLVM.Refinement.JsonStage2NumFastCalleeMul
import LeanLLVM.Refinement.JsonStage2NumFastBody

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.NumFastEpilogueLoop
open LeanLLVM.Refinement.NumFastEpilogueShape
open LeanLLVM.JSON
open LeanLLVM.StrtodRefine

namespace NumFastCalleeCmp

/-! ### The fixture and the body -/

/-- The captured body, as `capture-stage2-callees.sh` writes it. -/
def numCmpSrc : String :=
  include_str "../../probes/install/ir/stage2.callee.stk_cmp.ll"

/-- The declared layout the fixture needs: `%struct.StkBn` is `uint64_t w[96]`
and the `int` count — 776 bytes — and `%struct.Stk` is two of those, the
`int64_t` exponent and the `int` sticky flag — 1568 bytes.  The offsets the
body's `getelementptr`s use are these fields' byte offsets. -/
def numCmpLayout : Layout := [("StkBn", 776), ("Stk", 1568)]

/-- `@stk_cmp`, as the fixture parses under `numCmpLayout`.  Generated from the
parse by `capture-stage2-callees.sh --emit-pins stk_cmp`. -/
def numCmpBody : Function :=
{ name := "stk_cmp",
  retTy := (Ty.int 32),
  params := [("%v", Ty.ptr),
             ("%J", (Ty.int 64)),
             ("%eB", (Ty.int 64))],
  blocks := [
    { name := "entry",
      instrs := [
        Instr.alloca "%a" (Ty.struct "StkBn" 776) 0,
        Instr.alloca "%b" (Ty.struct "StkBn" 776) 0,
        Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000308#64))),
                             (Ty.ptr, (Operand.reg "%a"))],
        Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000308#64))),
                             (Ty.ptr, (Operand.reg "%b"))],
        Instr.gep "%sticky" (Ty.int 8) (Operand.reg "%v") (Operand.imm (Const.int 64 0x0000000000000618#64)),
        Instr.load "%0" (Ty.int 32) (Operand.reg "%sticky"),
        Instr.icmp "%tobool.not" (IPred.eq) 32 (Operand.reg "%0") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%tobool.not") "if.end" "if.then" },
    { name := "if.then",
      instrs := [
        Instr.gep "%n.i" (Ty.int 8) (Operand.reg "%v") (Operand.imm (Const.int 64 0x0000000000000608#64)),
        Instr.load "%1" (Ty.int 32) (Operand.reg "%n.i"),
        Instr.gep "%n1.i" (Ty.int 8) (Operand.reg "%b") (Operand.imm (Const.int 64 0x0000000000000300#64)),
        Instr.store (Ty.int 32) (Operand.reg "%1") (Operand.reg "%n1.i"),
        Instr.icmp "%tobool.not.i" (IPred.eq) 32 (Operand.reg "%1") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%tobool.not.i") "stk_copy.exit" "if.then.i" },
    { name := "if.then.i",
      instrs := [
        Instr.gep "%pow" (Ty.int 8) (Operand.reg "%v") (Operand.imm (Const.int 64 0x0000000000000308#64)),
        Instr.sext "%conv.i" 32 64 (Operand.reg "%1"),
        Instr.binop "%mul.i" (BinOp.shl) 64 (Operand.reg "%conv.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
        Instr.call "%call.i.i" Ty.ptr "__memcpy_chk" [(Ty.ptr, (Operand.reg "%b")),
                             (Ty.ptr, (Operand.reg "%pow")),
                             ((Ty.int 64), (Operand.reg "%mul.i")),
                             ((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000308#64)))]
      ],
      term := Term.br "stk_copy.exit" },
    { name := "stk_copy.exit",
      instrs := [
        Instr.callVoid "stk_mul_u64" [(Ty.ptr, (Operand.reg "%b")),
                             ((Ty.int 64), (Operand.reg "%J"))],
        Instr.gep "%S" (Ty.int 8) (Operand.reg "%v") (Operand.imm (Const.int 64 0x0000000000000610#64)),
        Instr.load "%2" (Ty.int 64) (Operand.reg "%S"),
        Instr.binop "%sub" (BinOp.sub) 64 (Operand.reg "%eB") (Operand.reg "%2"),
        Instr.trunc "%conv" 64 32 (Operand.reg "%sub"),
        Instr.icmp "%cmp.i" (IPred.eq) 32 (Operand.reg "%conv") (Operand.imm (Const.int 32 0x00000000#32)),
        Instr.load "%.pre" (Ty.int 32) (Operand.reg "%n1.i")
      ],
      term := Term.condbr (Operand.reg "%cmp.i") "stk_shl.exit" "lor.lhs.false.i" },
    { name := "lor.lhs.false.i",
      instrs := [
        Instr.icmp "%cmp1.i" (IPred.eq) 32 (Operand.reg "%.pre") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%cmp1.i") "stk_shl.exit" "if.end.i" },
    { name := "if.end.i",
      instrs := [
        Instr.binop "%div78.i" (BinOp.lshr) 32 (Operand.reg "%conv") (Operand.imm (Const.int 32 0x00000006#32)),
        Instr.binop "%rem2.i" (BinOp.and) 32 (Operand.reg "%conv") (Operand.imm (Const.int 32 0x0000003f#32)),
        Instr.icmp "%tobool.not.i28" (IPred.ne) 32 (Operand.reg "%rem2.i") (Operand.imm (Const.int 32 0x00000000#32)),
        Instr.icmp "%cmp579.i" (IPred.sgt) 32 (Operand.reg "%.pre") (Operand.imm (Const.int 32 0x00000000#32)),
        Instr.binop "%or.cond.i" (BinOp.and) 1 (Operand.reg "%tobool.not.i28") (Operand.reg "%cmp579.i")
      ],
      term := Term.condbr (Operand.reg "%or.cond.i") "for.body.lr.ph.i" "if.end18.i" },
    { name := "for.body.lr.ph.i",
      instrs := [
        Instr.binop "%sh_prom.i" (BinOp.and) 64 (Operand.reg "%sub") (Operand.imm (Const.int 64 0x000000000000003f#64)),
        Instr.binop "%sub.i" (BinOp.sub) 32 (Operand.imm (Const.int 32 0x00000040#32)) (Operand.reg "%rem2.i"),
        Instr.zext "%sh_prom9.i" 32 64 (Operand.reg "%sub.i"),
        Instr.zext "%wide.trip.count.i" 32 64 (Operand.reg "%.pre"),
        Instr.binop "%xtraiter" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
        Instr.icmp "%3" (IPred.ult) 32 (Operand.reg "%.pre") (Operand.imm (Const.int 32 0x00000004#32))
      ],
      term := Term.condbr (Operand.reg "%3") "for.cond.cleanup.i.unr-lcssa" "for.body.lr.ph.i.new" },
    { name := "for.body.lr.ph.i.new",
      instrs := [
        Instr.binop "%unroll_iter" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i") (Operand.imm (Const.int 64 0x000000007ffffffc#64))
      ],
      term := Term.br "for.body.i" },
    { name := "for.cond.cleanup.i.unr-lcssa",
      instrs := [
        Instr.phi "%shr.i.lcssa.ph" (Ty.int 64) [("for.body.lr.ph.i", (Operand.imm Const.poison)),
                                       ("for.body.i", (Operand.reg "%shr.i.3"))],
        Instr.phi "%indvars.iv.i.unr" (Ty.int 64) [("for.body.lr.ph.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i", (Operand.reg "%indvars.iv.next.i.3"))],
        Instr.phi "%carry.081.i.unr" (Ty.int 64) [("for.body.lr.ph.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i", (Operand.reg "%shr.i.3"))],
        Instr.icmp "%lcmp.mod.not" (IPred.eq) 64 (Operand.reg "%xtraiter") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%lcmp.mod.not") "for.cond.cleanup.i" "for.body.i.epil" },
    { name := "for.body.i.epil",
      instrs := [
        Instr.phi "%indvars.iv.i.epil" (Ty.int 64) [("for.body.i.epil", (Operand.reg "%indvars.iv.next.i.epil")),
                                       ("for.cond.cleanup.i.unr-lcssa", (Operand.reg "%indvars.iv.i.unr"))],
        Instr.phi "%carry.081.i.epil" (Ty.int 64) [("for.body.i.epil", (Operand.reg "%shr.i.epil")),
                                       ("for.cond.cleanup.i.unr-lcssa", (Operand.reg "%carry.081.i.unr"))],
        Instr.phi "%epil.iter" (Ty.int 64) [("for.body.i.epil", (Operand.reg "%epil.iter.next")),
                                       ("for.cond.cleanup.i.unr-lcssa", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.gep "%arrayidx.i.epil" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%indvars.iv.i.epil"),
        Instr.load "%4" (Ty.int 64) (Operand.reg "%arrayidx.i.epil"),
        Instr.binop "%shl.i.epil" (BinOp.shl) 64 (Operand.reg "%4") (Operand.reg "%sh_prom.i"),
        Instr.binop "%or.i.epil" (BinOp.or) 64 (Operand.reg "%shl.i.epil") (Operand.reg "%carry.081.i.epil"),
        Instr.store (Ty.int 64) (Operand.reg "%or.i.epil") (Operand.reg "%arrayidx.i.epil"),
        Instr.binop "%shr.i.epil" (BinOp.lshr) 64 (Operand.reg "%4") (Operand.reg "%sh_prom9.i"),
        Instr.binop "%indvars.iv.next.i.epil" (BinOp.add) 64 (Operand.reg "%indvars.iv.i.epil") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.binop "%epil.iter.next" (BinOp.add) 64 (Operand.reg "%epil.iter") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%epil.iter.cmp.not" (IPred.eq) 64 (Operand.reg "%epil.iter.next") (Operand.reg "%xtraiter")
      ],
      term := Term.condbr (Operand.reg "%epil.iter.cmp.not") "for.cond.cleanup.i" "for.body.i.epil" },
    { name := "for.cond.cleanup.i",
      instrs := [
        Instr.phi "%shr.i.lcssa" (Ty.int 64) [("for.cond.cleanup.i.unr-lcssa", (Operand.reg "%shr.i.lcssa.ph")),
                                       ("for.body.i.epil", (Operand.reg "%shr.i.epil"))],
        Instr.icmp "%tobool10.not.i" (IPred.eq) 64 (Operand.reg "%shr.i.lcssa") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%tobool10.not.i") "if.end18.i" "if.then11.i" },
    { name := "for.body.i",
      instrs := [
        Instr.phi "%indvars.iv.i" (Ty.int 64) [("for.body.lr.ph.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i", (Operand.reg "%indvars.iv.next.i.3"))],
        Instr.phi "%carry.081.i" (Ty.int 64) [("for.body.lr.ph.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i", (Operand.reg "%shr.i.3"))],
        Instr.phi "%niter" (Ty.int 64) [("for.body.lr.ph.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i", (Operand.reg "%niter.next.3"))],
        Instr.gep "%arrayidx.i" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%indvars.iv.i"),
        Instr.load "%5" (Ty.int 64) (Operand.reg "%arrayidx.i"),
        Instr.binop "%shl.i" (BinOp.shl) 64 (Operand.reg "%5") (Operand.reg "%sh_prom.i"),
        Instr.binop "%or.i" (BinOp.or) 64 (Operand.reg "%shl.i") (Operand.reg "%carry.081.i"),
        Instr.store (Ty.int 64) (Operand.reg "%or.i") (Operand.reg "%arrayidx.i"),
        Instr.binop "%shr.i" (BinOp.lshr) 64 (Operand.reg "%5") (Operand.reg "%sh_prom9.i"),
        Instr.binop "%indvars.iv.next.i" (BinOp.or) 64 (Operand.reg "%indvars.iv.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.gep "%arrayidx.i.1" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%indvars.iv.next.i"),
        Instr.load "%6" (Ty.int 64) (Operand.reg "%arrayidx.i.1"),
        Instr.binop "%shl.i.1" (BinOp.shl) 64 (Operand.reg "%6") (Operand.reg "%sh_prom.i"),
        Instr.binop "%or.i.1" (BinOp.or) 64 (Operand.reg "%shl.i.1") (Operand.reg "%shr.i"),
        Instr.store (Ty.int 64) (Operand.reg "%or.i.1") (Operand.reg "%arrayidx.i.1"),
        Instr.binop "%shr.i.1" (BinOp.lshr) 64 (Operand.reg "%6") (Operand.reg "%sh_prom9.i"),
        Instr.binop "%indvars.iv.next.i.1" (BinOp.or) 64 (Operand.reg "%indvars.iv.i") (Operand.imm (Const.int 64 0x0000000000000002#64)),
        Instr.gep "%arrayidx.i.2" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%indvars.iv.next.i.1"),
        Instr.load "%7" (Ty.int 64) (Operand.reg "%arrayidx.i.2"),
        Instr.binop "%shl.i.2" (BinOp.shl) 64 (Operand.reg "%7") (Operand.reg "%sh_prom.i"),
        Instr.binop "%or.i.2" (BinOp.or) 64 (Operand.reg "%shl.i.2") (Operand.reg "%shr.i.1"),
        Instr.store (Ty.int 64) (Operand.reg "%or.i.2") (Operand.reg "%arrayidx.i.2"),
        Instr.binop "%shr.i.2" (BinOp.lshr) 64 (Operand.reg "%7") (Operand.reg "%sh_prom9.i"),
        Instr.binop "%indvars.iv.next.i.2" (BinOp.or) 64 (Operand.reg "%indvars.iv.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
        Instr.gep "%arrayidx.i.3" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%indvars.iv.next.i.2"),
        Instr.load "%8" (Ty.int 64) (Operand.reg "%arrayidx.i.3"),
        Instr.binop "%shl.i.3" (BinOp.shl) 64 (Operand.reg "%8") (Operand.reg "%sh_prom.i"),
        Instr.binop "%or.i.3" (BinOp.or) 64 (Operand.reg "%shl.i.3") (Operand.reg "%shr.i.2"),
        Instr.store (Ty.int 64) (Operand.reg "%or.i.3") (Operand.reg "%arrayidx.i.3"),
        Instr.binop "%shr.i.3" (BinOp.lshr) 64 (Operand.reg "%8") (Operand.reg "%sh_prom9.i"),
        Instr.binop "%indvars.iv.next.i.3" (BinOp.add) 64 (Operand.reg "%indvars.iv.i") (Operand.imm (Const.int 64 0x0000000000000004#64)),
        Instr.binop "%niter.next.3" (BinOp.add) 64 (Operand.reg "%niter") (Operand.imm (Const.int 64 0x0000000000000004#64)),
        Instr.icmp "%niter.ncmp.3" (IPred.eq) 64 (Operand.reg "%niter.next.3") (Operand.reg "%unroll_iter")
      ],
      term := Term.condbr (Operand.reg "%niter.ncmp.3") "for.cond.cleanup.i.unr-lcssa" "for.body.i" },
    { name := "if.then11.i",
      instrs := [
        Instr.binop "%inc14.i" (BinOp.add) 32 (Operand.reg "%.pre") (Operand.imm (Const.int 32 0x00000001#32)),
        Instr.gep "%arrayidx16.i" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%wide.trip.count.i"),
        Instr.store (Ty.int 64) (Operand.reg "%shr.i.lcssa") (Operand.reg "%arrayidx16.i")
      ],
      term := Term.br "if.end18.i" },
    { name := "if.end18.i",
      instrs := [
        Instr.phi "%9" (Ty.int 32) [("for.cond.cleanup.i", (Operand.reg "%.pre")),
                                       ("if.then11.i", (Operand.reg "%inc14.i")),
                                       ("if.end.i", (Operand.reg "%.pre"))],
        Instr.icmp "%tobool19.not.i" (IPred.ult) 32 (Operand.reg "%conv") (Operand.imm (Const.int 32 0x00000040#32))
      ],
      term := Term.condbr (Operand.reg "%tobool19.not.i") "stk_shl.exit" "if.then20.i" },
    { name := "if.then20.i",
      instrs := [
        Instr.binop "%i21.082.i" (BinOp.add) 32 (Operand.reg "%9") (Operand.imm (Const.int 32 0xffffffff#32)),
        Instr.icmp "%cmp2583.i" (IPred.sgt) 32 (Operand.reg "%i21.082.i") (Operand.imm (Const.int 32 0xffffffff#32))
      ],
      term := Term.condbr (Operand.reg "%cmp2583.i") "iter.check" "for.cond.cleanup39.i" },
    { name := "iter.check",
      instrs := [
        Instr.zext "%10" 32 64 (Operand.reg "%i21.082.i"),
        Instr.zext "%11" 32 64 (Operand.reg "%9"),
        Instr.icmp "%min.iters.check" (IPred.ult) 32 (Operand.reg "%9") (Operand.imm (Const.int 32 0x00000004#32))
      ],
      term := Term.condbr (Operand.reg "%min.iters.check") "for.body27.i.preheader" "vector.scevcheck" },
    { name := "vector.scevcheck",
      instrs := [
        Instr.binop "%12" (BinOp.add) 32 (Operand.reg "%9") (Operand.reg "%div78.i"),
        Instr.binop "%13" (BinOp.add) 32 (Operand.reg "%12") (Operand.imm (Const.int 32 0xffffffff#32)),
        Instr.icmp "%14" (IPred.sgt) 32 (Operand.reg "%div78.i") (Operand.reg "%13")
      ],
      term := Term.condbr (Operand.reg "%14") "for.body27.i.preheader" "vector.memcheck" },
    { name := "vector.memcheck",
      instrs := [
        Instr.binop "%15" (BinOp.add) 32 (Operand.reg "%9") (Operand.reg "%div78.i"),
        Instr.binop "%16" (BinOp.add) 32 (Operand.reg "%15") (Operand.imm (Const.int 32 0xffffffff#32)),
        Instr.sext "%17" 32 64 (Operand.reg "%16"),
        Instr.binop "%18" (BinOp.sub) 64 (Operand.reg "%10") (Operand.reg "%17"),
        Instr.binop "%19" (BinOp.and) 64 (Operand.reg "%18") (Operand.imm (Const.int 64 0x1ffffffffffffff0#64)),
        Instr.icmp "%diff.check" (IPred.eq) 64 (Operand.reg "%19") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%diff.check") "for.body27.i.preheader" "vector.main.loop.iter.check" },
    { name := "vector.main.loop.iter.check",
      instrs := [
        Instr.icmp "%min.iters.check190" (IPred.ult) 32 (Operand.reg "%9") (Operand.imm (Const.int 32 0x00000010#32))
      ],
      term := Term.condbr (Operand.reg "%min.iters.check190") "vec.epilog.ph" "vector.ph" },
    { name := "vector.ph",
      instrs := [
        Instr.binop "%n.vec" (BinOp.and) 64 (Operand.reg "%11") (Operand.imm (Const.int 64 0x00000000fffffff0#64))
      ],
      term := Term.br "vector.body" },
    { name := "vector.body",
      instrs := [
        Instr.phi "%index" (Ty.int 64) [("vector.ph", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("vector.body", (Operand.reg "%index.next"))],
        Instr.binop "%20" (BinOp.sub) 64 (Operand.reg "%10") (Operand.reg "%index"),
        Instr.trunc "%21" 64 32 (Operand.reg "%index"),
        Instr.binop "%22" (BinOp.sub) 32 (Operand.reg "%i21.082.i") (Operand.reg "%21"),
        Instr.gep "%23" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%20"),
        Instr.gep "%24" (Ty.int 8) (Operand.reg "%23") (Operand.imm (Const.int 64 0xffffffffffffffe8#64)),
        Instr.gep "%25" (Ty.int 8) (Operand.reg "%23") (Operand.imm (Const.int 64 0xffffffffffffffc8#64)),
        Instr.gep "%26" (Ty.int 8) (Operand.reg "%23") (Operand.imm (Const.int 64 0xffffffffffffffa8#64)),
        Instr.gep "%27" (Ty.int 8) (Operand.reg "%23") (Operand.imm (Const.int 64 0xffffffffffffff88#64)),
        Instr.load "%wide.load" (Ty.vec 4 (Ty.int 64)) (Operand.reg "%24"),
        Instr.load "%wide.load191" (Ty.vec 4 (Ty.int 64)) (Operand.reg "%25"),
        Instr.load "%wide.load193" (Ty.vec 4 (Ty.int 64)) (Operand.reg "%26"),
        Instr.load "%wide.load195" (Ty.vec 4 (Ty.int 64)) (Operand.reg "%27"),
        Instr.binop "%28" (BinOp.add) 32 (Operand.reg "%div78.i") (Operand.reg "%22"),
        Instr.sext "%29" 32 64 (Operand.reg "%28"),
        Instr.gep "%30" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%29"),
        Instr.gep "%31" (Ty.int 8) (Operand.reg "%30") (Operand.imm (Const.int 64 0xffffffffffffffe8#64)),
        Instr.gep "%32" (Ty.int 8) (Operand.reg "%30") (Operand.imm (Const.int 64 0xffffffffffffffc8#64)),
        Instr.gep "%33" (Ty.int 8) (Operand.reg "%30") (Operand.imm (Const.int 64 0xffffffffffffffa8#64)),
        Instr.gep "%34" (Ty.int 8) (Operand.reg "%30") (Operand.imm (Const.int 64 0xffffffffffffff88#64)),
        Instr.store (Ty.vec 4 (Ty.int 64)) (Operand.reg "%wide.load") (Operand.reg "%31"),
        Instr.store (Ty.vec 4 (Ty.int 64)) (Operand.reg "%wide.load191") (Operand.reg "%32"),
        Instr.store (Ty.vec 4 (Ty.int 64)) (Operand.reg "%wide.load193") (Operand.reg "%33"),
        Instr.store (Ty.vec 4 (Ty.int 64)) (Operand.reg "%wide.load195") (Operand.reg "%34"),
        Instr.binop "%index.next" (BinOp.add) 64 (Operand.reg "%index") (Operand.imm (Const.int 64 0x0000000000000010#64)),
        Instr.icmp "%35" (IPred.eq) 64 (Operand.reg "%index.next") (Operand.reg "%n.vec")
      ],
      term := Term.condbr (Operand.reg "%35") "middle.block" "vector.body" },
    { name := "middle.block",
      instrs := [
        Instr.icmp "%cmp.n" (IPred.eq) 64 (Operand.reg "%n.vec") (Operand.reg "%11")
      ],
      term := Term.condbr (Operand.reg "%cmp.n") "for.cond.cleanup39.i" "vec.epilog.iter.check" },
    { name := "vec.epilog.iter.check",
      instrs := [
        Instr.binop "%ind.end" (BinOp.sub) 64 (Operand.reg "%10") (Operand.reg "%n.vec"),
        Instr.binop "%n.vec.remaining" (BinOp.and) 64 (Operand.reg "%11") (Operand.imm (Const.int 64 0x000000000000000c#64)),
        Instr.icmp "%min.epilog.iters.check" (IPred.eq) 64 (Operand.reg "%n.vec.remaining") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%min.epilog.iters.check") "for.body27.i.preheader" "vec.epilog.ph" },
    { name := "vec.epilog.ph",
      instrs := [
        Instr.phi "%vec.epilog.resume.val" (Ty.int 64) [("vec.epilog.iter.check", (Operand.reg "%n.vec")),
                                       ("vector.main.loop.iter.check", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.binop "%n.vec202" (BinOp.and) 64 (Operand.reg "%11") (Operand.imm (Const.int 64 0x00000000fffffffc#64)),
        Instr.binop "%36" (BinOp.sub) 64 (Operand.reg "%10") (Operand.reg "%n.vec202"),
        Instr.gep "%invariant.gep" (Ty.int 8) (Operand.reg "%b") (Operand.imm (Const.int 64 0xffffffffffffffe8#64)),
        Instr.gep "%invariant.gep340" (Ty.int 8) (Operand.reg "%b") (Operand.imm (Const.int 64 0xffffffffffffffe8#64))
      ],
      term := Term.br "vec.epilog.vector.body" },
    { name := "vec.epilog.vector.body",
      instrs := [
        Instr.phi "%index203" (Ty.int 64) [("vec.epilog.ph", (Operand.reg "%vec.epilog.resume.val")),
                                       ("vec.epilog.vector.body", (Operand.reg "%index.next208"))],
        Instr.binop "%offset.idx" (BinOp.sub) 64 (Operand.reg "%10") (Operand.reg "%index203"),
        Instr.trunc "%37" 64 32 (Operand.reg "%index203"),
        Instr.binop "%38" (BinOp.sub) 32 (Operand.reg "%i21.082.i") (Operand.reg "%37"),
        Instr.gep "%gep" (Ty.int 64) (Operand.reg "%invariant.gep") (Operand.reg "%offset.idx"),
        Instr.load "%wide.load205" (Ty.vec 4 (Ty.int 64)) (Operand.reg "%gep"),
        Instr.binop "%39" (BinOp.add) 32 (Operand.reg "%div78.i") (Operand.reg "%38"),
        Instr.sext "%40" 32 64 (Operand.reg "%39"),
        Instr.gep "%gep341" (Ty.int 64) (Operand.reg "%invariant.gep340") (Operand.reg "%40"),
        Instr.store (Ty.vec 4 (Ty.int 64)) (Operand.reg "%wide.load205") (Operand.reg "%gep341"),
        Instr.binop "%index.next208" (BinOp.add) 64 (Operand.reg "%index203") (Operand.imm (Const.int 64 0x0000000000000004#64)),
        Instr.icmp "%41" (IPred.eq) 64 (Operand.reg "%index.next208") (Operand.reg "%n.vec202")
      ],
      term := Term.condbr (Operand.reg "%41") "vec.epilog.middle.block" "vec.epilog.vector.body" },
    { name := "vec.epilog.middle.block",
      instrs := [
        Instr.icmp "%cmp.n209" (IPred.eq) 64 (Operand.reg "%n.vec202") (Operand.reg "%11")
      ],
      term := Term.condbr (Operand.reg "%cmp.n209") "for.cond.cleanup39.i" "for.body27.i.preheader" },
    { name := "for.body27.i.preheader",
      instrs := [
        Instr.phi "%indvars.iv88.i.ph" (Ty.int 64) [("iter.check", (Operand.reg "%10")),
                                       ("vector.scevcheck", (Operand.reg "%10")),
                                       ("vector.memcheck", (Operand.reg "%10")),
                                       ("vec.epilog.iter.check", (Operand.reg "%ind.end")),
                                       ("vec.epilog.middle.block", (Operand.reg "%36"))],
        Instr.binop "%42" (BinOp.add) 64 (Operand.reg "%indvars.iv88.i.ph") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.binop "%xtraiter317" (BinOp.and) 64 (Operand.reg "%42") (Operand.imm (Const.int 64 0x0000000000000007#64)),
        Instr.binop "%43" (BinOp.and) 64 (Operand.reg "%indvars.iv88.i.ph") (Operand.imm (Const.int 64 0x0000000000000007#64)),
        Instr.icmp "%lcmp.mod318.not" (IPred.eq) 64 (Operand.reg "%43") (Operand.imm (Const.int 64 0x0000000000000007#64))
      ],
      term := Term.condbr (Operand.reg "%lcmp.mod318.not") "for.body27.i.prol.loopexit" "for.body27.i.prol" },
    { name := "for.body27.i.prol",
      instrs := [
        Instr.phi "%indvars.iv88.i.prol" (Ty.int 64) [("for.body27.i.prol", (Operand.reg "%indvars.iv.next89.i.prol")),
                                       ("for.body27.i.preheader", (Operand.reg "%indvars.iv88.i.ph"))],
        Instr.phi "%prol.iter" (Ty.int 64) [("for.body27.i.prol", (Operand.reg "%prol.iter.next")),
                                       ("for.body27.i.preheader", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.gep "%arrayidx30.i.prol" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%indvars.iv88.i.prol"),
        Instr.load "%44" (Ty.int 64) (Operand.reg "%arrayidx30.i.prol"),
        Instr.trunc "%45" 64 32 (Operand.reg "%indvars.iv88.i.prol"),
        Instr.binop "%46" (BinOp.add) 32 (Operand.reg "%div78.i") (Operand.reg "%45"),
        Instr.sext "%idxprom32.i.prol" 32 64 (Operand.reg "%46"),
        Instr.gep "%arrayidx33.i.prol" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%idxprom32.i.prol"),
        Instr.store (Ty.int 64) (Operand.reg "%44") (Operand.reg "%arrayidx33.i.prol"),
        Instr.binop "%indvars.iv.next89.i.prol" (BinOp.add) 64 (Operand.reg "%indvars.iv88.i.prol") (Operand.imm (Const.int 64 0xffffffffffffffff#64)),
        Instr.binop "%prol.iter.next" (BinOp.add) 64 (Operand.reg "%prol.iter") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%prol.iter.cmp.not" (IPred.eq) 64 (Operand.reg "%prol.iter.next") (Operand.reg "%xtraiter317")
      ],
      term := Term.condbr (Operand.reg "%prol.iter.cmp.not") "for.body27.i.prol.loopexit" "for.body27.i.prol" },
    { name := "for.body27.i.prol.loopexit",
      instrs := [
        Instr.phi "%indvars.iv88.i.unr" (Ty.int 64) [("for.body27.i.preheader", (Operand.reg "%indvars.iv88.i.ph")),
                                       ("for.body27.i.prol", (Operand.reg "%indvars.iv.next89.i.prol"))],
        Instr.icmp "%47" (IPred.ult) 64 (Operand.reg "%indvars.iv88.i.ph") (Operand.imm (Const.int 64 0x0000000000000007#64))
      ],
      term := Term.condbr (Operand.reg "%47") "for.cond.cleanup39.i" "for.body27.i" },
    { name := "for.body27.i",
      instrs := [
        Instr.phi "%indvars.iv88.i" (Ty.int 64) [("for.body27.i", (Operand.reg "%indvars.iv.next89.i.7")),
                                       ("for.body27.i.prol.loopexit", (Operand.reg "%indvars.iv88.i.unr"))],
        Instr.gep "%arrayidx30.i" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%indvars.iv88.i"),
        Instr.load "%48" (Ty.int 64) (Operand.reg "%arrayidx30.i"),
        Instr.trunc "%49" 64 32 (Operand.reg "%indvars.iv88.i"),
        Instr.binop "%50" (BinOp.add) 32 (Operand.reg "%div78.i") (Operand.reg "%49"),
        Instr.sext "%idxprom32.i" 32 64 (Operand.reg "%50"),
        Instr.gep "%arrayidx33.i" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%idxprom32.i"),
        Instr.store (Ty.int 64) (Operand.reg "%48") (Operand.reg "%arrayidx33.i"),
        Instr.binop "%indvars.iv.next89.i" (BinOp.add) 64 (Operand.reg "%indvars.iv88.i") (Operand.imm (Const.int 64 0xffffffffffffffff#64)),
        Instr.gep "%arrayidx30.i.1" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%indvars.iv.next89.i"),
        Instr.load "%51" (Ty.int 64) (Operand.reg "%arrayidx30.i.1"),
        Instr.trunc "%52" 64 32 (Operand.reg "%indvars.iv.next89.i"),
        Instr.binop "%53" (BinOp.add) 32 (Operand.reg "%div78.i") (Operand.reg "%52"),
        Instr.sext "%idxprom32.i.1" 32 64 (Operand.reg "%53"),
        Instr.gep "%arrayidx33.i.1" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%idxprom32.i.1"),
        Instr.store (Ty.int 64) (Operand.reg "%51") (Operand.reg "%arrayidx33.i.1"),
        Instr.binop "%indvars.iv.next89.i.1" (BinOp.add) 64 (Operand.reg "%indvars.iv88.i") (Operand.imm (Const.int 64 0xfffffffffffffffe#64)),
        Instr.gep "%arrayidx30.i.2" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%indvars.iv.next89.i.1"),
        Instr.load "%54" (Ty.int 64) (Operand.reg "%arrayidx30.i.2"),
        Instr.trunc "%55" 64 32 (Operand.reg "%indvars.iv.next89.i.1"),
        Instr.binop "%56" (BinOp.add) 32 (Operand.reg "%div78.i") (Operand.reg "%55"),
        Instr.sext "%idxprom32.i.2" 32 64 (Operand.reg "%56"),
        Instr.gep "%arrayidx33.i.2" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%idxprom32.i.2"),
        Instr.store (Ty.int 64) (Operand.reg "%54") (Operand.reg "%arrayidx33.i.2"),
        Instr.binop "%indvars.iv.next89.i.2" (BinOp.add) 64 (Operand.reg "%indvars.iv88.i") (Operand.imm (Const.int 64 0xfffffffffffffffd#64)),
        Instr.gep "%arrayidx30.i.3" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%indvars.iv.next89.i.2"),
        Instr.load "%57" (Ty.int 64) (Operand.reg "%arrayidx30.i.3"),
        Instr.trunc "%58" 64 32 (Operand.reg "%indvars.iv.next89.i.2"),
        Instr.binop "%59" (BinOp.add) 32 (Operand.reg "%div78.i") (Operand.reg "%58"),
        Instr.sext "%idxprom32.i.3" 32 64 (Operand.reg "%59"),
        Instr.gep "%arrayidx33.i.3" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%idxprom32.i.3"),
        Instr.store (Ty.int 64) (Operand.reg "%57") (Operand.reg "%arrayidx33.i.3"),
        Instr.binop "%indvars.iv.next89.i.3" (BinOp.add) 64 (Operand.reg "%indvars.iv88.i") (Operand.imm (Const.int 64 0xfffffffffffffffc#64)),
        Instr.gep "%arrayidx30.i.4" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%indvars.iv.next89.i.3"),
        Instr.load "%60" (Ty.int 64) (Operand.reg "%arrayidx30.i.4"),
        Instr.trunc "%61" 64 32 (Operand.reg "%indvars.iv.next89.i.3"),
        Instr.binop "%62" (BinOp.add) 32 (Operand.reg "%div78.i") (Operand.reg "%61"),
        Instr.sext "%idxprom32.i.4" 32 64 (Operand.reg "%62"),
        Instr.gep "%arrayidx33.i.4" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%idxprom32.i.4"),
        Instr.store (Ty.int 64) (Operand.reg "%60") (Operand.reg "%arrayidx33.i.4"),
        Instr.binop "%indvars.iv.next89.i.4" (BinOp.add) 64 (Operand.reg "%indvars.iv88.i") (Operand.imm (Const.int 64 0xfffffffffffffffb#64)),
        Instr.gep "%arrayidx30.i.5" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%indvars.iv.next89.i.4"),
        Instr.load "%63" (Ty.int 64) (Operand.reg "%arrayidx30.i.5"),
        Instr.trunc "%64" 64 32 (Operand.reg "%indvars.iv.next89.i.4"),
        Instr.binop "%65" (BinOp.add) 32 (Operand.reg "%div78.i") (Operand.reg "%64"),
        Instr.sext "%idxprom32.i.5" 32 64 (Operand.reg "%65"),
        Instr.gep "%arrayidx33.i.5" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%idxprom32.i.5"),
        Instr.store (Ty.int 64) (Operand.reg "%63") (Operand.reg "%arrayidx33.i.5"),
        Instr.binop "%indvars.iv.next89.i.5" (BinOp.add) 64 (Operand.reg "%indvars.iv88.i") (Operand.imm (Const.int 64 0xfffffffffffffffa#64)),
        Instr.gep "%arrayidx30.i.6" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%indvars.iv.next89.i.5"),
        Instr.load "%66" (Ty.int 64) (Operand.reg "%arrayidx30.i.6"),
        Instr.trunc "%67" 64 32 (Operand.reg "%indvars.iv.next89.i.5"),
        Instr.binop "%68" (BinOp.add) 32 (Operand.reg "%div78.i") (Operand.reg "%67"),
        Instr.sext "%idxprom32.i.6" 32 64 (Operand.reg "%68"),
        Instr.gep "%arrayidx33.i.6" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%idxprom32.i.6"),
        Instr.store (Ty.int 64) (Operand.reg "%66") (Operand.reg "%arrayidx33.i.6"),
        Instr.binop "%indvars.iv.next89.i.6" (BinOp.add) 64 (Operand.reg "%indvars.iv88.i") (Operand.imm (Const.int 64 0xfffffffffffffff9#64)),
        Instr.gep "%arrayidx30.i.7" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%indvars.iv.next89.i.6"),
        Instr.load "%69" (Ty.int 64) (Operand.reg "%arrayidx30.i.7"),
        Instr.trunc "%70" 64 32 (Operand.reg "%indvars.iv.next89.i.6"),
        Instr.binop "%71" (BinOp.add) 32 (Operand.reg "%div78.i") (Operand.reg "%70"),
        Instr.sext "%idxprom32.i.7" 32 64 (Operand.reg "%71"),
        Instr.gep "%arrayidx33.i.7" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%idxprom32.i.7"),
        Instr.store (Ty.int 64) (Operand.reg "%69") (Operand.reg "%arrayidx33.i.7"),
        Instr.binop "%indvars.iv.next89.i.7" (BinOp.add) 64 (Operand.reg "%indvars.iv88.i") (Operand.imm (Const.int 64 0xfffffffffffffff8#64)),
        Instr.icmp "%cmp25.not.i.7" (IPred.eq) 64 (Operand.reg "%indvars.iv.next89.i.6") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%cmp25.not.i.7") "for.cond.cleanup39.i" "for.body27.i" },
    { name := "for.cond.cleanup39.i",
      instrs := [
        Instr.binop "%72" (BinOp.lshr) 64 (Operand.reg "%sub") (Operand.imm (Const.int 64 0x0000000000000003#64)),
        Instr.binop "%73" (BinOp.and) 64 (Operand.reg "%72") (Operand.imm (Const.int 64 0x000000001ffffff8#64)),
        Instr.callVoid "llvm.memset.p0.i64" [(Ty.ptr, (Operand.reg "%b")),
                             ((Ty.int 8), (Operand.imm (Const.int 8 0x00#8))),
                             ((Ty.int 64), (Operand.reg "%73")),
                             ((Ty.int 1), (Operand.imm (Const.int 1 0x0#1)))],
        Instr.binop "%add48.i" (BinOp.add) 32 (Operand.reg "%9") (Operand.reg "%div78.i")
      ],
      term := Term.br "stk_shl.exit" },
    { name := "stk_shl.exit",
      instrs := [
        Instr.phi "%74" (Ty.int 32) [("stk_copy.exit", (Operand.reg "%.pre")),
                                       ("lor.lhs.false.i", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("if.end18.i", (Operand.reg "%9")),
                                       ("for.cond.cleanup39.i", (Operand.reg "%add48.i"))],
        Instr.gep "%n.i29" (Ty.int 8) (Operand.reg "%v") (Operand.imm (Const.int 64 0x0000000000000300#64)),
        Instr.load "%75" (Ty.int 32) (Operand.reg "%n.i29"),
        Instr.icmp "%cmp.not.i" (IPred.eq) 32 (Operand.reg "%75") (Operand.reg "%74")
      ],
      term := Term.condbr (Operand.reg "%cmp.not.i") "for.cond.preheader.i" "if.then.i31" },
    { name := "for.cond.preheader.i",
      instrs := [
        Instr.zext "%76" 32 64 (Operand.reg "%74")
      ],
      term := Term.br "for.cond.i" },
    { name := "if.then.i31",
      instrs := [
        Instr.icmp "%cmp4.i" (IPred.slt) 32 (Operand.reg "%75") (Operand.reg "%74"),
        Instr.select "%spec.select" (Ty.int 32) (Operand.reg "%cmp4.i") (Operand.imm (Const.int 32 0xffffffff#32)) (Operand.imm (Const.int 32 0x00000001#32))
      ],
      term := Term.br "cleanup" },
    { name := "for.cond.i",
      instrs := [
        Instr.phi "%indvars.iv.i32" (Ty.int 64) [("for.cond.preheader.i", (Operand.reg "%76")),
                                       ("for.body.i34", (Operand.reg "%indvars.iv.next.i33"))],
        Instr.binop "%indvars.iv.next.i33" (BinOp.add) 64 (Operand.reg "%indvars.iv.i32") (Operand.imm (Const.int 64 0xffffffffffffffff#64)),
        Instr.binop "%77" (BinOp.and) 64 (Operand.reg "%indvars.iv.next.i33") (Operand.imm (Const.int 64 0x0000000080000000#64)),
        Instr.icmp "%cmp6.not.i" (IPred.eq) 64 (Operand.reg "%77") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%cmp6.not.i") "for.body.i34" "cleanup" },
    { name := "for.body.i34",
      instrs := [
        Instr.binop "%idxprom.i" (BinOp.and) 64 (Operand.reg "%indvars.iv.next.i33") (Operand.imm (Const.int 64 0x000000007fffffff#64)),
        Instr.gep "%arrayidx.i35" (Ty.int 64) (Operand.reg "%v") (Operand.reg "%idxprom.i"),
        Instr.load "%78" (Ty.int 64) (Operand.reg "%arrayidx.i35"),
        Instr.gep "%arrayidx9.i" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%idxprom.i"),
        Instr.load "%79" (Ty.int 64) (Operand.reg "%arrayidx9.i"),
        Instr.icmp "%cmp10.not.i" (IPred.eq) 64 (Operand.reg "%78") (Operand.reg "%79")
      ],
      term := Term.condbr (Operand.reg "%cmp10.not.i") "for.cond.i" "if.then11.i36" },
    { name := "if.then11.i36",
      instrs := [
        Instr.icmp "%cmp18.i" (IPred.ult) 64 (Operand.reg "%78") (Operand.reg "%79"),
        Instr.select "%spec.select172" (Ty.int 32) (Operand.reg "%cmp18.i") (Operand.imm (Const.int 32 0xffffffff#32)) (Operand.imm (Const.int 32 0x00000001#32))
      ],
      term := Term.br "cleanup" },
    { name := "if.end",
      instrs := [
        Instr.gep "%n.i37" (Ty.int 8) (Operand.reg "%v") (Operand.imm (Const.int 64 0x0000000000000300#64)),
        Instr.load "%80" (Ty.int 32) (Operand.reg "%n.i37"),
        Instr.gep "%n1.i38" (Ty.int 8) (Operand.reg "%a") (Operand.imm (Const.int 64 0x0000000000000300#64)),
        Instr.store (Ty.int 32) (Operand.reg "%80") (Operand.reg "%n1.i38"),
        Instr.icmp "%tobool.not.i39" (IPred.eq) 32 (Operand.reg "%80") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%tobool.not.i39") "stk_copy.exit45" "if.then.i40" },
    { name := "if.then.i40",
      instrs := [
        Instr.sext "%conv.i41" 32 64 (Operand.reg "%80"),
        Instr.binop "%mul.i42" (BinOp.shl) 64 (Operand.reg "%conv.i41") (Operand.imm (Const.int 64 0x0000000000000003#64)),
        Instr.call "%call.i.i43" Ty.ptr "__memcpy_chk" [(Ty.ptr, (Operand.reg "%a")),
                             (Ty.ptr, (Operand.reg "%v")),
                             ((Ty.int 64), (Operand.reg "%mul.i42")),
                             ((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000308#64)))]
      ],
      term := Term.br "stk_copy.exit45" },
    { name := "stk_copy.exit45",
      instrs := [
        Instr.icmp "%cmp3" (IPred.slt) 64 (Operand.reg "%eB") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%cmp3") "if.then5" "if.end8" },
    { name := "if.then5",
      instrs := [
        Instr.trunc "%81" 64 32 (Operand.reg "%eB"),
        Instr.binop "%conv7" (BinOp.sub) 32 (Operand.imm (Const.int 32 0x00000000#32)) (Operand.reg "%81"),
        Instr.load "%82" (Ty.int 32) (Operand.reg "%n1.i38"),
        Instr.icmp "%cmp1.i49" (IPred.eq) 32 (Operand.reg "%82") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%cmp1.i49") "if.end8" "if.end.i50" },
    { name := "if.end.i50",
      instrs := [
        Instr.binop "%div78.i51" (BinOp.lshr) 32 (Operand.reg "%conv7") (Operand.imm (Const.int 32 0x00000006#32)),
        Instr.binop "%rem2.i52" (BinOp.and) 32 (Operand.reg "%conv7") (Operand.imm (Const.int 32 0x0000003f#32)),
        Instr.icmp "%tobool.not.i53" (IPred.ne) 32 (Operand.reg "%rem2.i52") (Operand.imm (Const.int 32 0x00000000#32)),
        Instr.icmp "%cmp579.i54" (IPred.sgt) 32 (Operand.reg "%82") (Operand.imm (Const.int 32 0x00000000#32)),
        Instr.binop "%or.cond.i55" (BinOp.and) 1 (Operand.reg "%tobool.not.i53") (Operand.reg "%cmp579.i54")
      ],
      term := Term.condbr (Operand.reg "%or.cond.i55") "for.body.lr.ph.i71" "if.end18.i56" },
    { name := "for.body.lr.ph.i71",
      instrs := [
        Instr.zext "%sh_prom.i72" 32 64 (Operand.reg "%rem2.i52"),
        Instr.binop "%sub.i73" (BinOp.sub) 32 (Operand.imm (Const.int 32 0x00000040#32)) (Operand.reg "%rem2.i52"),
        Instr.zext "%sh_prom9.i74" 32 64 (Operand.reg "%sub.i73"),
        Instr.zext "%wide.trip.count.i75" 32 64 (Operand.reg "%82"),
        Instr.binop "%xtraiter319" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i75") (Operand.imm (Const.int 64 0x0000000000000003#64)),
        Instr.icmp "%83" (IPred.ult) 32 (Operand.reg "%82") (Operand.imm (Const.int 32 0x00000004#32))
      ],
      term := Term.condbr (Operand.reg "%83") "for.cond.cleanup.i85.unr-lcssa" "for.body.lr.ph.i71.new" },
    { name := "for.body.lr.ph.i71.new",
      instrs := [
        Instr.binop "%unroll_iter323" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i75") (Operand.imm (Const.int 64 0x000000007ffffffc#64))
      ],
      term := Term.br "for.body.i76" },
    { name := "for.cond.cleanup.i85.unr-lcssa",
      instrs := [
        Instr.phi "%shr.i82.lcssa.ph" (Ty.int 64) [("for.body.lr.ph.i71", (Operand.imm Const.poison)),
                                       ("for.body.i76", (Operand.reg "%shr.i82.3"))],
        Instr.phi "%indvars.iv.i77.unr" (Ty.int 64) [("for.body.lr.ph.i71", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i76", (Operand.reg "%indvars.iv.next.i83.3"))],
        Instr.phi "%carry.081.i78.unr" (Ty.int 64) [("for.body.lr.ph.i71", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i76", (Operand.reg "%shr.i82.3"))],
        Instr.icmp "%lcmp.mod321.not" (IPred.eq) 64 (Operand.reg "%xtraiter319") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%lcmp.mod321.not") "for.cond.cleanup.i85" "for.body.i76.epil" },
    { name := "for.body.i76.epil",
      instrs := [
        Instr.phi "%indvars.iv.i77.epil" (Ty.int 64) [("for.body.i76.epil", (Operand.reg "%indvars.iv.next.i83.epil")),
                                       ("for.cond.cleanup.i85.unr-lcssa", (Operand.reg "%indvars.iv.i77.unr"))],
        Instr.phi "%carry.081.i78.epil" (Ty.int 64) [("for.body.i76.epil", (Operand.reg "%shr.i82.epil")),
                                       ("for.cond.cleanup.i85.unr-lcssa", (Operand.reg "%carry.081.i78.unr"))],
        Instr.phi "%epil.iter320" (Ty.int 64) [("for.body.i76.epil", (Operand.reg "%epil.iter320.next")),
                                       ("for.cond.cleanup.i85.unr-lcssa", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.gep "%arrayidx.i79.epil" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%indvars.iv.i77.epil"),
        Instr.load "%84" (Ty.int 64) (Operand.reg "%arrayidx.i79.epil"),
        Instr.binop "%shl.i80.epil" (BinOp.shl) 64 (Operand.reg "%84") (Operand.reg "%sh_prom.i72"),
        Instr.binop "%or.i81.epil" (BinOp.or) 64 (Operand.reg "%shl.i80.epil") (Operand.reg "%carry.081.i78.epil"),
        Instr.store (Ty.int 64) (Operand.reg "%or.i81.epil") (Operand.reg "%arrayidx.i79.epil"),
        Instr.binop "%shr.i82.epil" (BinOp.lshr) 64 (Operand.reg "%84") (Operand.reg "%sh_prom9.i74"),
        Instr.binop "%indvars.iv.next.i83.epil" (BinOp.add) 64 (Operand.reg "%indvars.iv.i77.epil") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.binop "%epil.iter320.next" (BinOp.add) 64 (Operand.reg "%epil.iter320") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%epil.iter320.cmp.not" (IPred.eq) 64 (Operand.reg "%epil.iter320.next") (Operand.reg "%xtraiter319")
      ],
      term := Term.condbr (Operand.reg "%epil.iter320.cmp.not") "for.cond.cleanup.i85" "for.body.i76.epil" },
    { name := "for.cond.cleanup.i85",
      instrs := [
        Instr.phi "%shr.i82.lcssa" (Ty.int 64) [("for.cond.cleanup.i85.unr-lcssa", (Operand.reg "%shr.i82.lcssa.ph")),
                                       ("for.body.i76.epil", (Operand.reg "%shr.i82.epil"))],
        Instr.icmp "%tobool10.not.i86" (IPred.eq) 64 (Operand.reg "%shr.i82.lcssa") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%tobool10.not.i86") "if.end18.i56" "if.then11.i87" },
    { name := "for.body.i76",
      instrs := [
        Instr.phi "%indvars.iv.i77" (Ty.int 64) [("for.body.lr.ph.i71.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i76", (Operand.reg "%indvars.iv.next.i83.3"))],
        Instr.phi "%carry.081.i78" (Ty.int 64) [("for.body.lr.ph.i71.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i76", (Operand.reg "%shr.i82.3"))],
        Instr.phi "%niter324" (Ty.int 64) [("for.body.lr.ph.i71.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i76", (Operand.reg "%niter324.next.3"))],
        Instr.gep "%arrayidx.i79" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%indvars.iv.i77"),
        Instr.load "%85" (Ty.int 64) (Operand.reg "%arrayidx.i79"),
        Instr.binop "%shl.i80" (BinOp.shl) 64 (Operand.reg "%85") (Operand.reg "%sh_prom.i72"),
        Instr.binop "%or.i81" (BinOp.or) 64 (Operand.reg "%shl.i80") (Operand.reg "%carry.081.i78"),
        Instr.store (Ty.int 64) (Operand.reg "%or.i81") (Operand.reg "%arrayidx.i79"),
        Instr.binop "%shr.i82" (BinOp.lshr) 64 (Operand.reg "%85") (Operand.reg "%sh_prom9.i74"),
        Instr.binop "%indvars.iv.next.i83" (BinOp.or) 64 (Operand.reg "%indvars.iv.i77") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.gep "%arrayidx.i79.1" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%indvars.iv.next.i83"),
        Instr.load "%86" (Ty.int 64) (Operand.reg "%arrayidx.i79.1"),
        Instr.binop "%shl.i80.1" (BinOp.shl) 64 (Operand.reg "%86") (Operand.reg "%sh_prom.i72"),
        Instr.binop "%or.i81.1" (BinOp.or) 64 (Operand.reg "%shl.i80.1") (Operand.reg "%shr.i82"),
        Instr.store (Ty.int 64) (Operand.reg "%or.i81.1") (Operand.reg "%arrayidx.i79.1"),
        Instr.binop "%shr.i82.1" (BinOp.lshr) 64 (Operand.reg "%86") (Operand.reg "%sh_prom9.i74"),
        Instr.binop "%indvars.iv.next.i83.1" (BinOp.or) 64 (Operand.reg "%indvars.iv.i77") (Operand.imm (Const.int 64 0x0000000000000002#64)),
        Instr.gep "%arrayidx.i79.2" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%indvars.iv.next.i83.1"),
        Instr.load "%87" (Ty.int 64) (Operand.reg "%arrayidx.i79.2"),
        Instr.binop "%shl.i80.2" (BinOp.shl) 64 (Operand.reg "%87") (Operand.reg "%sh_prom.i72"),
        Instr.binop "%or.i81.2" (BinOp.or) 64 (Operand.reg "%shl.i80.2") (Operand.reg "%shr.i82.1"),
        Instr.store (Ty.int 64) (Operand.reg "%or.i81.2") (Operand.reg "%arrayidx.i79.2"),
        Instr.binop "%shr.i82.2" (BinOp.lshr) 64 (Operand.reg "%87") (Operand.reg "%sh_prom9.i74"),
        Instr.binop "%indvars.iv.next.i83.2" (BinOp.or) 64 (Operand.reg "%indvars.iv.i77") (Operand.imm (Const.int 64 0x0000000000000003#64)),
        Instr.gep "%arrayidx.i79.3" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%indvars.iv.next.i83.2"),
        Instr.load "%88" (Ty.int 64) (Operand.reg "%arrayidx.i79.3"),
        Instr.binop "%shl.i80.3" (BinOp.shl) 64 (Operand.reg "%88") (Operand.reg "%sh_prom.i72"),
        Instr.binop "%or.i81.3" (BinOp.or) 64 (Operand.reg "%shl.i80.3") (Operand.reg "%shr.i82.2"),
        Instr.store (Ty.int 64) (Operand.reg "%or.i81.3") (Operand.reg "%arrayidx.i79.3"),
        Instr.binop "%shr.i82.3" (BinOp.lshr) 64 (Operand.reg "%88") (Operand.reg "%sh_prom9.i74"),
        Instr.binop "%indvars.iv.next.i83.3" (BinOp.add) 64 (Operand.reg "%indvars.iv.i77") (Operand.imm (Const.int 64 0x0000000000000004#64)),
        Instr.binop "%niter324.next.3" (BinOp.add) 64 (Operand.reg "%niter324") (Operand.imm (Const.int 64 0x0000000000000004#64)),
        Instr.icmp "%niter324.ncmp.3" (IPred.eq) 64 (Operand.reg "%niter324.next.3") (Operand.reg "%unroll_iter323")
      ],
      term := Term.condbr (Operand.reg "%niter324.ncmp.3") "for.cond.cleanup.i85.unr-lcssa" "for.body.i76" },
    { name := "if.then11.i87",
      instrs := [
        Instr.binop "%inc14.i88" (BinOp.add) 32 (Operand.reg "%82") (Operand.imm (Const.int 32 0x00000001#32)),
        Instr.store (Ty.int 32) (Operand.reg "%inc14.i88") (Operand.reg "%n1.i38"),
        Instr.gep "%arrayidx16.i90" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%wide.trip.count.i75"),
        Instr.store (Ty.int 64) (Operand.reg "%shr.i82.lcssa") (Operand.reg "%arrayidx16.i90")
      ],
      term := Term.br "if.end18.i56" },
    { name := "if.end18.i56",
      instrs := [
        Instr.phi "%89" (Ty.int 32) [("for.cond.cleanup.i85", (Operand.reg "%82")),
                                       ("if.then11.i87", (Operand.reg "%inc14.i88")),
                                       ("if.end.i50", (Operand.reg "%82"))],
        Instr.icmp "%tobool19.not.i57" (IPred.ult) 32 (Operand.reg "%conv7") (Operand.imm (Const.int 32 0x00000040#32))
      ],
      term := Term.condbr (Operand.reg "%tobool19.not.i57") "if.end8" "if.then20.i58" },
    { name := "if.then20.i58",
      instrs := [
        Instr.binop "%i21.082.i59" (BinOp.add) 32 (Operand.reg "%89") (Operand.imm (Const.int 32 0xffffffff#32)),
        Instr.icmp "%cmp2583.i60" (IPred.sgt) 32 (Operand.reg "%i21.082.i59") (Operand.imm (Const.int 32 0xffffffff#32))
      ],
      term := Term.condbr (Operand.reg "%cmp2583.i60") "iter.check218" "for.cond.cleanup39.i61" },
    { name := "iter.check218",
      instrs := [
        Instr.zext "%90" 32 64 (Operand.reg "%i21.082.i59"),
        Instr.zext "%91" 32 64 (Operand.reg "%89"),
        Instr.icmp "%min.iters.check216" (IPred.ult) 32 (Operand.reg "%89") (Operand.imm (Const.int 32 0x00000004#32))
      ],
      term := Term.condbr (Operand.reg "%min.iters.check216") "for.body27.i64.preheader" "vector.scevcheck210" },
    { name := "vector.scevcheck210",
      instrs := [
        Instr.binop "%92" (BinOp.add) 32 (Operand.reg "%89") (Operand.reg "%div78.i51"),
        Instr.binop "%93" (BinOp.add) 32 (Operand.reg "%92") (Operand.imm (Const.int 32 0xffffffff#32)),
        Instr.icmp "%94" (IPred.sgt) 32 (Operand.reg "%div78.i51") (Operand.reg "%93")
      ],
      term := Term.condbr (Operand.reg "%94") "for.body27.i64.preheader" "vector.memcheck214" },
    { name := "vector.memcheck214",
      instrs := [
        Instr.binop "%95" (BinOp.add) 32 (Operand.reg "%89") (Operand.reg "%div78.i51"),
        Instr.binop "%96" (BinOp.add) 32 (Operand.reg "%95") (Operand.imm (Const.int 32 0xffffffff#32)),
        Instr.sext "%97" 32 64 (Operand.reg "%96"),
        Instr.binop "%98" (BinOp.sub) 64 (Operand.reg "%90") (Operand.reg "%97"),
        Instr.binop "%99" (BinOp.and) 64 (Operand.reg "%98") (Operand.imm (Const.int 64 0x1ffffffffffffff0#64)),
        Instr.icmp "%diff.check215" (IPred.eq) 64 (Operand.reg "%99") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%diff.check215") "for.body27.i64.preheader" "vector.main.loop.iter.check220" },
    { name := "vector.main.loop.iter.check220",
      instrs := [
        Instr.icmp "%min.iters.check219" (IPred.ult) 32 (Operand.reg "%89") (Operand.imm (Const.int 32 0x00000010#32))
      ],
      term := Term.condbr (Operand.reg "%min.iters.check219") "vec.epilog.ph243" "vector.ph221" },
    { name := "vector.ph221",
      instrs := [
        Instr.binop "%n.vec223" (BinOp.and) 64 (Operand.reg "%91") (Operand.imm (Const.int 64 0x00000000fffffff0#64))
      ],
      term := Term.br "vector.body224" },
    { name := "vector.body224",
      instrs := [
        Instr.phi "%index225" (Ty.int 64) [("vector.ph221", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("vector.body224", (Operand.reg "%index.next238"))],
        Instr.binop "%100" (BinOp.sub) 64 (Operand.reg "%90") (Operand.reg "%index225"),
        Instr.trunc "%101" 64 32 (Operand.reg "%index225"),
        Instr.binop "%102" (BinOp.sub) 32 (Operand.reg "%i21.082.i59") (Operand.reg "%101"),
        Instr.gep "%103" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%100"),
        Instr.gep "%104" (Ty.int 8) (Operand.reg "%103") (Operand.imm (Const.int 64 0xffffffffffffffe8#64)),
        Instr.gep "%105" (Ty.int 8) (Operand.reg "%103") (Operand.imm (Const.int 64 0xffffffffffffffc8#64)),
        Instr.gep "%106" (Ty.int 8) (Operand.reg "%103") (Operand.imm (Const.int 64 0xffffffffffffffa8#64)),
        Instr.gep "%107" (Ty.int 8) (Operand.reg "%103") (Operand.imm (Const.int 64 0xffffffffffffff88#64)),
        Instr.load "%wide.load226" (Ty.vec 4 (Ty.int 64)) (Operand.reg "%104"),
        Instr.load "%wide.load228" (Ty.vec 4 (Ty.int 64)) (Operand.reg "%105"),
        Instr.load "%wide.load230" (Ty.vec 4 (Ty.int 64)) (Operand.reg "%106"),
        Instr.load "%wide.load232" (Ty.vec 4 (Ty.int 64)) (Operand.reg "%107"),
        Instr.binop "%108" (BinOp.add) 32 (Operand.reg "%div78.i51") (Operand.reg "%102"),
        Instr.sext "%109" 32 64 (Operand.reg "%108"),
        Instr.gep "%110" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%109"),
        Instr.gep "%111" (Ty.int 8) (Operand.reg "%110") (Operand.imm (Const.int 64 0xffffffffffffffe8#64)),
        Instr.gep "%112" (Ty.int 8) (Operand.reg "%110") (Operand.imm (Const.int 64 0xffffffffffffffc8#64)),
        Instr.gep "%113" (Ty.int 8) (Operand.reg "%110") (Operand.imm (Const.int 64 0xffffffffffffffa8#64)),
        Instr.gep "%114" (Ty.int 8) (Operand.reg "%110") (Operand.imm (Const.int 64 0xffffffffffffff88#64)),
        Instr.store (Ty.vec 4 (Ty.int 64)) (Operand.reg "%wide.load226") (Operand.reg "%111"),
        Instr.store (Ty.vec 4 (Ty.int 64)) (Operand.reg "%wide.load228") (Operand.reg "%112"),
        Instr.store (Ty.vec 4 (Ty.int 64)) (Operand.reg "%wide.load230") (Operand.reg "%113"),
        Instr.store (Ty.vec 4 (Ty.int 64)) (Operand.reg "%wide.load232") (Operand.reg "%114"),
        Instr.binop "%index.next238" (BinOp.add) 64 (Operand.reg "%index225") (Operand.imm (Const.int 64 0x0000000000000010#64)),
        Instr.icmp "%115" (IPred.eq) 64 (Operand.reg "%index.next238") (Operand.reg "%n.vec223")
      ],
      term := Term.condbr (Operand.reg "%115") "middle.block239" "vector.body224" },
    { name := "middle.block239",
      instrs := [
        Instr.icmp "%cmp.n240" (IPred.eq) 64 (Operand.reg "%n.vec223") (Operand.reg "%91")
      ],
      term := Term.condbr (Operand.reg "%cmp.n240") "for.cond.cleanup39.i61" "vec.epilog.iter.check244" },
    { name := "vec.epilog.iter.check244",
      instrs := [
        Instr.binop "%ind.end260" (BinOp.sub) 64 (Operand.reg "%90") (Operand.reg "%n.vec223"),
        Instr.binop "%n.vec.remaining245" (BinOp.and) 64 (Operand.reg "%91") (Operand.imm (Const.int 64 0x000000000000000c#64)),
        Instr.icmp "%min.epilog.iters.check246" (IPred.eq) 64 (Operand.reg "%n.vec.remaining245") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%min.epilog.iters.check246") "for.body27.i64.preheader" "vec.epilog.ph243" },
    { name := "vec.epilog.ph243",
      instrs := [
        Instr.phi "%vec.epilog.resume.val241" (Ty.int 64) [("vec.epilog.iter.check244", (Operand.reg "%n.vec223")),
                                       ("vector.main.loop.iter.check220", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.binop "%n.vec248" (BinOp.and) 64 (Operand.reg "%91") (Operand.imm (Const.int 64 0x00000000fffffffc#64)),
        Instr.binop "%116" (BinOp.sub) 64 (Operand.reg "%90") (Operand.reg "%n.vec248"),
        Instr.gep "%invariant.gep342" (Ty.int 8) (Operand.reg "%a") (Operand.imm (Const.int 64 0xffffffffffffffe8#64)),
        Instr.gep "%invariant.gep344" (Ty.int 8) (Operand.reg "%a") (Operand.imm (Const.int 64 0xffffffffffffffe8#64))
      ],
      term := Term.br "vec.epilog.vector.body249" },
    { name := "vec.epilog.vector.body249",
      instrs := [
        Instr.phi "%index250" (Ty.int 64) [("vec.epilog.ph243", (Operand.reg "%vec.epilog.resume.val241")),
                                       ("vec.epilog.vector.body249", (Operand.reg "%index.next256"))],
        Instr.binop "%offset.idx251" (BinOp.sub) 64 (Operand.reg "%90") (Operand.reg "%index250"),
        Instr.trunc "%117" 64 32 (Operand.reg "%index250"),
        Instr.binop "%118" (BinOp.sub) 32 (Operand.reg "%i21.082.i59") (Operand.reg "%117"),
        Instr.gep "%gep343" (Ty.int 64) (Operand.reg "%invariant.gep342") (Operand.reg "%offset.idx251"),
        Instr.load "%wide.load253" (Ty.vec 4 (Ty.int 64)) (Operand.reg "%gep343"),
        Instr.binop "%119" (BinOp.add) 32 (Operand.reg "%div78.i51") (Operand.reg "%118"),
        Instr.sext "%120" 32 64 (Operand.reg "%119"),
        Instr.gep "%gep345" (Ty.int 64) (Operand.reg "%invariant.gep344") (Operand.reg "%120"),
        Instr.store (Ty.vec 4 (Ty.int 64)) (Operand.reg "%wide.load253") (Operand.reg "%gep345"),
        Instr.binop "%index.next256" (BinOp.add) 64 (Operand.reg "%index250") (Operand.imm (Const.int 64 0x0000000000000004#64)),
        Instr.icmp "%121" (IPred.eq) 64 (Operand.reg "%index.next256") (Operand.reg "%n.vec248")
      ],
      term := Term.condbr (Operand.reg "%121") "vec.epilog.middle.block257" "vec.epilog.vector.body249" },
    { name := "vec.epilog.middle.block257",
      instrs := [
        Instr.icmp "%cmp.n258" (IPred.eq) 64 (Operand.reg "%n.vec248") (Operand.reg "%91")
      ],
      term := Term.condbr (Operand.reg "%cmp.n258") "for.cond.cleanup39.i61" "for.body27.i64.preheader" },
    { name := "for.body27.i64.preheader",
      instrs := [
        Instr.phi "%indvars.iv88.i65.ph" (Ty.int 64) [("iter.check218", (Operand.reg "%90")),
                                       ("vector.scevcheck210", (Operand.reg "%90")),
                                       ("vector.memcheck214", (Operand.reg "%90")),
                                       ("vec.epilog.iter.check244", (Operand.reg "%ind.end260")),
                                       ("vec.epilog.middle.block257", (Operand.reg "%116"))],
        Instr.binop "%122" (BinOp.add) 64 (Operand.reg "%indvars.iv88.i65.ph") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.binop "%xtraiter325" (BinOp.and) 64 (Operand.reg "%122") (Operand.imm (Const.int 64 0x0000000000000007#64)),
        Instr.binop "%123" (BinOp.and) 64 (Operand.reg "%indvars.iv88.i65.ph") (Operand.imm (Const.int 64 0x0000000000000007#64)),
        Instr.icmp "%lcmp.mod326.not" (IPred.eq) 64 (Operand.reg "%123") (Operand.imm (Const.int 64 0x0000000000000007#64))
      ],
      term := Term.condbr (Operand.reg "%lcmp.mod326.not") "for.body27.i64.prol.loopexit" "for.body27.i64.prol" },
    { name := "for.body27.i64.prol",
      instrs := [
        Instr.phi "%indvars.iv88.i65.prol" (Ty.int 64) [("for.body27.i64.prol", (Operand.reg "%indvars.iv.next89.i69.prol")),
                                       ("for.body27.i64.preheader", (Operand.reg "%indvars.iv88.i65.ph"))],
        Instr.phi "%prol.iter327" (Ty.int 64) [("for.body27.i64.prol", (Operand.reg "%prol.iter327.next")),
                                       ("for.body27.i64.preheader", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.gep "%arrayidx30.i66.prol" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%indvars.iv88.i65.prol"),
        Instr.load "%124" (Ty.int 64) (Operand.reg "%arrayidx30.i66.prol"),
        Instr.trunc "%125" 64 32 (Operand.reg "%indvars.iv88.i65.prol"),
        Instr.binop "%126" (BinOp.add) 32 (Operand.reg "%div78.i51") (Operand.reg "%125"),
        Instr.sext "%idxprom32.i67.prol" 32 64 (Operand.reg "%126"),
        Instr.gep "%arrayidx33.i68.prol" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%idxprom32.i67.prol"),
        Instr.store (Ty.int 64) (Operand.reg "%124") (Operand.reg "%arrayidx33.i68.prol"),
        Instr.binop "%indvars.iv.next89.i69.prol" (BinOp.add) 64 (Operand.reg "%indvars.iv88.i65.prol") (Operand.imm (Const.int 64 0xffffffffffffffff#64)),
        Instr.binop "%prol.iter327.next" (BinOp.add) 64 (Operand.reg "%prol.iter327") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%prol.iter327.cmp.not" (IPred.eq) 64 (Operand.reg "%prol.iter327.next") (Operand.reg "%xtraiter325")
      ],
      term := Term.condbr (Operand.reg "%prol.iter327.cmp.not") "for.body27.i64.prol.loopexit" "for.body27.i64.prol" },
    { name := "for.body27.i64.prol.loopexit",
      instrs := [
        Instr.phi "%indvars.iv88.i65.unr" (Ty.int 64) [("for.body27.i64.preheader", (Operand.reg "%indvars.iv88.i65.ph")),
                                       ("for.body27.i64.prol", (Operand.reg "%indvars.iv.next89.i69.prol"))],
        Instr.icmp "%127" (IPred.ult) 64 (Operand.reg "%indvars.iv88.i65.ph") (Operand.imm (Const.int 64 0x0000000000000007#64))
      ],
      term := Term.condbr (Operand.reg "%127") "for.cond.cleanup39.i61" "for.body27.i64" },
    { name := "for.body27.i64",
      instrs := [
        Instr.phi "%indvars.iv88.i65" (Ty.int 64) [("for.body27.i64", (Operand.reg "%indvars.iv.next89.i69.7")),
                                       ("for.body27.i64.prol.loopexit", (Operand.reg "%indvars.iv88.i65.unr"))],
        Instr.gep "%arrayidx30.i66" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%indvars.iv88.i65"),
        Instr.load "%128" (Ty.int 64) (Operand.reg "%arrayidx30.i66"),
        Instr.trunc "%129" 64 32 (Operand.reg "%indvars.iv88.i65"),
        Instr.binop "%130" (BinOp.add) 32 (Operand.reg "%div78.i51") (Operand.reg "%129"),
        Instr.sext "%idxprom32.i67" 32 64 (Operand.reg "%130"),
        Instr.gep "%arrayidx33.i68" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%idxprom32.i67"),
        Instr.store (Ty.int 64) (Operand.reg "%128") (Operand.reg "%arrayidx33.i68"),
        Instr.binop "%indvars.iv.next89.i69" (BinOp.add) 64 (Operand.reg "%indvars.iv88.i65") (Operand.imm (Const.int 64 0xffffffffffffffff#64)),
        Instr.gep "%arrayidx30.i66.1" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%indvars.iv.next89.i69"),
        Instr.load "%131" (Ty.int 64) (Operand.reg "%arrayidx30.i66.1"),
        Instr.trunc "%132" 64 32 (Operand.reg "%indvars.iv.next89.i69"),
        Instr.binop "%133" (BinOp.add) 32 (Operand.reg "%div78.i51") (Operand.reg "%132"),
        Instr.sext "%idxprom32.i67.1" 32 64 (Operand.reg "%133"),
        Instr.gep "%arrayidx33.i68.1" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%idxprom32.i67.1"),
        Instr.store (Ty.int 64) (Operand.reg "%131") (Operand.reg "%arrayidx33.i68.1"),
        Instr.binop "%indvars.iv.next89.i69.1" (BinOp.add) 64 (Operand.reg "%indvars.iv88.i65") (Operand.imm (Const.int 64 0xfffffffffffffffe#64)),
        Instr.gep "%arrayidx30.i66.2" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%indvars.iv.next89.i69.1"),
        Instr.load "%134" (Ty.int 64) (Operand.reg "%arrayidx30.i66.2"),
        Instr.trunc "%135" 64 32 (Operand.reg "%indvars.iv.next89.i69.1"),
        Instr.binop "%136" (BinOp.add) 32 (Operand.reg "%div78.i51") (Operand.reg "%135"),
        Instr.sext "%idxprom32.i67.2" 32 64 (Operand.reg "%136"),
        Instr.gep "%arrayidx33.i68.2" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%idxprom32.i67.2"),
        Instr.store (Ty.int 64) (Operand.reg "%134") (Operand.reg "%arrayidx33.i68.2"),
        Instr.binop "%indvars.iv.next89.i69.2" (BinOp.add) 64 (Operand.reg "%indvars.iv88.i65") (Operand.imm (Const.int 64 0xfffffffffffffffd#64)),
        Instr.gep "%arrayidx30.i66.3" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%indvars.iv.next89.i69.2"),
        Instr.load "%137" (Ty.int 64) (Operand.reg "%arrayidx30.i66.3"),
        Instr.trunc "%138" 64 32 (Operand.reg "%indvars.iv.next89.i69.2"),
        Instr.binop "%139" (BinOp.add) 32 (Operand.reg "%div78.i51") (Operand.reg "%138"),
        Instr.sext "%idxprom32.i67.3" 32 64 (Operand.reg "%139"),
        Instr.gep "%arrayidx33.i68.3" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%idxprom32.i67.3"),
        Instr.store (Ty.int 64) (Operand.reg "%137") (Operand.reg "%arrayidx33.i68.3"),
        Instr.binop "%indvars.iv.next89.i69.3" (BinOp.add) 64 (Operand.reg "%indvars.iv88.i65") (Operand.imm (Const.int 64 0xfffffffffffffffc#64)),
        Instr.gep "%arrayidx30.i66.4" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%indvars.iv.next89.i69.3"),
        Instr.load "%140" (Ty.int 64) (Operand.reg "%arrayidx30.i66.4"),
        Instr.trunc "%141" 64 32 (Operand.reg "%indvars.iv.next89.i69.3"),
        Instr.binop "%142" (BinOp.add) 32 (Operand.reg "%div78.i51") (Operand.reg "%141"),
        Instr.sext "%idxprom32.i67.4" 32 64 (Operand.reg "%142"),
        Instr.gep "%arrayidx33.i68.4" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%idxprom32.i67.4"),
        Instr.store (Ty.int 64) (Operand.reg "%140") (Operand.reg "%arrayidx33.i68.4"),
        Instr.binop "%indvars.iv.next89.i69.4" (BinOp.add) 64 (Operand.reg "%indvars.iv88.i65") (Operand.imm (Const.int 64 0xfffffffffffffffb#64)),
        Instr.gep "%arrayidx30.i66.5" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%indvars.iv.next89.i69.4"),
        Instr.load "%143" (Ty.int 64) (Operand.reg "%arrayidx30.i66.5"),
        Instr.trunc "%144" 64 32 (Operand.reg "%indvars.iv.next89.i69.4"),
        Instr.binop "%145" (BinOp.add) 32 (Operand.reg "%div78.i51") (Operand.reg "%144"),
        Instr.sext "%idxprom32.i67.5" 32 64 (Operand.reg "%145"),
        Instr.gep "%arrayidx33.i68.5" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%idxprom32.i67.5"),
        Instr.store (Ty.int 64) (Operand.reg "%143") (Operand.reg "%arrayidx33.i68.5"),
        Instr.binop "%indvars.iv.next89.i69.5" (BinOp.add) 64 (Operand.reg "%indvars.iv88.i65") (Operand.imm (Const.int 64 0xfffffffffffffffa#64)),
        Instr.gep "%arrayidx30.i66.6" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%indvars.iv.next89.i69.5"),
        Instr.load "%146" (Ty.int 64) (Operand.reg "%arrayidx30.i66.6"),
        Instr.trunc "%147" 64 32 (Operand.reg "%indvars.iv.next89.i69.5"),
        Instr.binop "%148" (BinOp.add) 32 (Operand.reg "%div78.i51") (Operand.reg "%147"),
        Instr.sext "%idxprom32.i67.6" 32 64 (Operand.reg "%148"),
        Instr.gep "%arrayidx33.i68.6" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%idxprom32.i67.6"),
        Instr.store (Ty.int 64) (Operand.reg "%146") (Operand.reg "%arrayidx33.i68.6"),
        Instr.binop "%indvars.iv.next89.i69.6" (BinOp.add) 64 (Operand.reg "%indvars.iv88.i65") (Operand.imm (Const.int 64 0xfffffffffffffff9#64)),
        Instr.gep "%arrayidx30.i66.7" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%indvars.iv.next89.i69.6"),
        Instr.load "%149" (Ty.int 64) (Operand.reg "%arrayidx30.i66.7"),
        Instr.trunc "%150" 64 32 (Operand.reg "%indvars.iv.next89.i69.6"),
        Instr.binop "%151" (BinOp.add) 32 (Operand.reg "%div78.i51") (Operand.reg "%150"),
        Instr.sext "%idxprom32.i67.7" 32 64 (Operand.reg "%151"),
        Instr.gep "%arrayidx33.i68.7" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%idxprom32.i67.7"),
        Instr.store (Ty.int 64) (Operand.reg "%149") (Operand.reg "%arrayidx33.i68.7"),
        Instr.binop "%indvars.iv.next89.i69.7" (BinOp.add) 64 (Operand.reg "%indvars.iv88.i65") (Operand.imm (Const.int 64 0xfffffffffffffff8#64)),
        Instr.icmp "%cmp25.not.i70.7" (IPred.eq) 64 (Operand.reg "%indvars.iv.next89.i69.6") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%cmp25.not.i70.7") "for.cond.cleanup39.i61" "for.body27.i64" },
    { name := "for.cond.cleanup39.i61",
      instrs := [
        Instr.binop "%152" (BinOp.lshr) 32 (Operand.reg "%conv7") (Operand.imm (Const.int 32 0x00000003#32)),
        Instr.binop "%153" (BinOp.and) 32 (Operand.reg "%152") (Operand.imm (Const.int 32 0x1ffffff8#32)),
        Instr.zext "%154" 32 64 (Operand.reg "%153"),
        Instr.callVoid "llvm.memset.p0.i64" [(Ty.ptr, (Operand.reg "%a")),
                             ((Ty.int 8), (Operand.imm (Const.int 8 0x00#8))),
                             ((Ty.int 64), (Operand.reg "%154")),
                             ((Ty.int 1), (Operand.imm (Const.int 1 0x0#1)))],
        Instr.binop "%add48.i62" (BinOp.add) 32 (Operand.reg "%89") (Operand.reg "%div78.i51"),
        Instr.store (Ty.int 32) (Operand.reg "%add48.i62") (Operand.reg "%n1.i38")
      ],
      term := Term.br "if.end8" },
    { name := "if.end8",
      instrs := [
        Instr.gep "%n.i92" (Ty.int 8) (Operand.reg "%v") (Operand.imm (Const.int 64 0x0000000000000608#64)),
        Instr.load "%155" (Ty.int 32) (Operand.reg "%n.i92"),
        Instr.gep "%n1.i93" (Ty.int 8) (Operand.reg "%b") (Operand.imm (Const.int 64 0x0000000000000300#64)),
        Instr.store (Ty.int 32) (Operand.reg "%155") (Operand.reg "%n1.i93"),
        Instr.icmp "%tobool.not.i94" (IPred.eq) 32 (Operand.reg "%155") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%tobool.not.i94") "stk_copy.exit100" "if.then.i95" },
    { name := "if.then.i95",
      instrs := [
        Instr.gep "%pow9" (Ty.int 8) (Operand.reg "%v") (Operand.imm (Const.int 64 0x0000000000000308#64)),
        Instr.sext "%conv.i96" 32 64 (Operand.reg "%155"),
        Instr.binop "%mul.i97" (BinOp.shl) 64 (Operand.reg "%conv.i96") (Operand.imm (Const.int 64 0x0000000000000003#64)),
        Instr.call "%call.i.i98" Ty.ptr "__memcpy_chk" [(Ty.ptr, (Operand.reg "%b")),
                             (Ty.ptr, (Operand.reg "%pow9")),
                             ((Ty.int 64), (Operand.reg "%mul.i97")),
                             ((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000308#64)))]
      ],
      term := Term.br "stk_copy.exit100" },
    { name := "stk_copy.exit100",
      instrs := [
        Instr.callVoid "stk_mul_u64" [(Ty.ptr, (Operand.reg "%b")),
                             ((Ty.int 64), (Operand.reg "%J"))],
        Instr.icmp "%cmp10" (IPred.sgt) 64 (Operand.reg "%eB") (Operand.imm (Const.int 64 0x0000000000000000#64)),
        Instr.load "%.pre181" (Ty.int 32) (Operand.reg "%n1.i93")
      ],
      term := Term.condbr (Operand.reg "%cmp10") "lor.lhs.false.i102" "if.end14" },
    { name := "lor.lhs.false.i102",
      instrs := [
        Instr.icmp "%cmp1.i104" (IPred.eq) 32 (Operand.reg "%.pre181") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%cmp1.i104") "if.end14" "if.end.i105" },
    { name := "if.end.i105",
      instrs := [
        Instr.trunc "%conv13" 64 32 (Operand.reg "%eB"),
        Instr.binop "%div78.i106" (BinOp.lshr) 32 (Operand.reg "%conv13") (Operand.imm (Const.int 32 0x00000006#32)),
        Instr.binop "%rem2.i107" (BinOp.and) 32 (Operand.reg "%conv13") (Operand.imm (Const.int 32 0x0000003f#32)),
        Instr.icmp "%tobool.not.i108" (IPred.ne) 32 (Operand.reg "%rem2.i107") (Operand.imm (Const.int 32 0x00000000#32)),
        Instr.icmp "%cmp579.i109" (IPred.sgt) 32 (Operand.reg "%.pre181") (Operand.imm (Const.int 32 0x00000000#32)),
        Instr.binop "%or.cond.i110" (BinOp.and) 1 (Operand.reg "%tobool.not.i108") (Operand.reg "%cmp579.i109")
      ],
      term := Term.condbr (Operand.reg "%or.cond.i110") "for.body.lr.ph.i126" "if.end18.i111" },
    { name := "for.body.lr.ph.i126",
      instrs := [
        Instr.binop "%sh_prom.i127" (BinOp.and) 64 (Operand.reg "%eB") (Operand.imm (Const.int 64 0x000000000000003f#64)),
        Instr.binop "%sub.i128" (BinOp.sub) 32 (Operand.imm (Const.int 32 0x00000040#32)) (Operand.reg "%rem2.i107"),
        Instr.zext "%sh_prom9.i129" 32 64 (Operand.reg "%sub.i128"),
        Instr.zext "%wide.trip.count.i130" 32 64 (Operand.reg "%.pre181"),
        Instr.binop "%xtraiter328" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i130") (Operand.imm (Const.int 64 0x0000000000000003#64)),
        Instr.icmp "%156" (IPred.ult) 32 (Operand.reg "%.pre181") (Operand.imm (Const.int 32 0x00000004#32))
      ],
      term := Term.condbr (Operand.reg "%156") "for.cond.cleanup.i140.unr-lcssa" "for.body.lr.ph.i126.new" },
    { name := "for.body.lr.ph.i126.new",
      instrs := [
        Instr.binop "%unroll_iter332" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i130") (Operand.imm (Const.int 64 0x000000007ffffffc#64))
      ],
      term := Term.br "for.body.i131" },
    { name := "for.cond.cleanup.i140.unr-lcssa",
      instrs := [
        Instr.phi "%shr.i137.lcssa.ph" (Ty.int 64) [("for.body.lr.ph.i126", (Operand.imm Const.poison)),
                                       ("for.body.i131", (Operand.reg "%shr.i137.3"))],
        Instr.phi "%indvars.iv.i132.unr" (Ty.int 64) [("for.body.lr.ph.i126", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i131", (Operand.reg "%indvars.iv.next.i138.3"))],
        Instr.phi "%carry.081.i133.unr" (Ty.int 64) [("for.body.lr.ph.i126", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i131", (Operand.reg "%shr.i137.3"))],
        Instr.icmp "%lcmp.mod330.not" (IPred.eq) 64 (Operand.reg "%xtraiter328") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%lcmp.mod330.not") "for.cond.cleanup.i140" "for.body.i131.epil" },
    { name := "for.body.i131.epil",
      instrs := [
        Instr.phi "%indvars.iv.i132.epil" (Ty.int 64) [("for.body.i131.epil", (Operand.reg "%indvars.iv.next.i138.epil")),
                                       ("for.cond.cleanup.i140.unr-lcssa", (Operand.reg "%indvars.iv.i132.unr"))],
        Instr.phi "%carry.081.i133.epil" (Ty.int 64) [("for.body.i131.epil", (Operand.reg "%shr.i137.epil")),
                                       ("for.cond.cleanup.i140.unr-lcssa", (Operand.reg "%carry.081.i133.unr"))],
        Instr.phi "%epil.iter329" (Ty.int 64) [("for.body.i131.epil", (Operand.reg "%epil.iter329.next")),
                                       ("for.cond.cleanup.i140.unr-lcssa", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.gep "%arrayidx.i134.epil" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%indvars.iv.i132.epil"),
        Instr.load "%157" (Ty.int 64) (Operand.reg "%arrayidx.i134.epil"),
        Instr.binop "%shl.i135.epil" (BinOp.shl) 64 (Operand.reg "%157") (Operand.reg "%sh_prom.i127"),
        Instr.binop "%or.i136.epil" (BinOp.or) 64 (Operand.reg "%shl.i135.epil") (Operand.reg "%carry.081.i133.epil"),
        Instr.store (Ty.int 64) (Operand.reg "%or.i136.epil") (Operand.reg "%arrayidx.i134.epil"),
        Instr.binop "%shr.i137.epil" (BinOp.lshr) 64 (Operand.reg "%157") (Operand.reg "%sh_prom9.i129"),
        Instr.binop "%indvars.iv.next.i138.epil" (BinOp.add) 64 (Operand.reg "%indvars.iv.i132.epil") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.binop "%epil.iter329.next" (BinOp.add) 64 (Operand.reg "%epil.iter329") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%epil.iter329.cmp.not" (IPred.eq) 64 (Operand.reg "%epil.iter329.next") (Operand.reg "%xtraiter328")
      ],
      term := Term.condbr (Operand.reg "%epil.iter329.cmp.not") "for.cond.cleanup.i140" "for.body.i131.epil" },
    { name := "for.cond.cleanup.i140",
      instrs := [
        Instr.phi "%shr.i137.lcssa" (Ty.int 64) [("for.cond.cleanup.i140.unr-lcssa", (Operand.reg "%shr.i137.lcssa.ph")),
                                       ("for.body.i131.epil", (Operand.reg "%shr.i137.epil"))],
        Instr.icmp "%tobool10.not.i141" (IPred.eq) 64 (Operand.reg "%shr.i137.lcssa") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%tobool10.not.i141") "if.end18.i111" "if.then11.i142" },
    { name := "for.body.i131",
      instrs := [
        Instr.phi "%indvars.iv.i132" (Ty.int 64) [("for.body.lr.ph.i126.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i131", (Operand.reg "%indvars.iv.next.i138.3"))],
        Instr.phi "%carry.081.i133" (Ty.int 64) [("for.body.lr.ph.i126.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i131", (Operand.reg "%shr.i137.3"))],
        Instr.phi "%niter333" (Ty.int 64) [("for.body.lr.ph.i126.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i131", (Operand.reg "%niter333.next.3"))],
        Instr.gep "%arrayidx.i134" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%indvars.iv.i132"),
        Instr.load "%158" (Ty.int 64) (Operand.reg "%arrayidx.i134"),
        Instr.binop "%shl.i135" (BinOp.shl) 64 (Operand.reg "%158") (Operand.reg "%sh_prom.i127"),
        Instr.binop "%or.i136" (BinOp.or) 64 (Operand.reg "%shl.i135") (Operand.reg "%carry.081.i133"),
        Instr.store (Ty.int 64) (Operand.reg "%or.i136") (Operand.reg "%arrayidx.i134"),
        Instr.binop "%shr.i137" (BinOp.lshr) 64 (Operand.reg "%158") (Operand.reg "%sh_prom9.i129"),
        Instr.binop "%indvars.iv.next.i138" (BinOp.or) 64 (Operand.reg "%indvars.iv.i132") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.gep "%arrayidx.i134.1" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%indvars.iv.next.i138"),
        Instr.load "%159" (Ty.int 64) (Operand.reg "%arrayidx.i134.1"),
        Instr.binop "%shl.i135.1" (BinOp.shl) 64 (Operand.reg "%159") (Operand.reg "%sh_prom.i127"),
        Instr.binop "%or.i136.1" (BinOp.or) 64 (Operand.reg "%shl.i135.1") (Operand.reg "%shr.i137"),
        Instr.store (Ty.int 64) (Operand.reg "%or.i136.1") (Operand.reg "%arrayidx.i134.1"),
        Instr.binop "%shr.i137.1" (BinOp.lshr) 64 (Operand.reg "%159") (Operand.reg "%sh_prom9.i129"),
        Instr.binop "%indvars.iv.next.i138.1" (BinOp.or) 64 (Operand.reg "%indvars.iv.i132") (Operand.imm (Const.int 64 0x0000000000000002#64)),
        Instr.gep "%arrayidx.i134.2" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%indvars.iv.next.i138.1"),
        Instr.load "%160" (Ty.int 64) (Operand.reg "%arrayidx.i134.2"),
        Instr.binop "%shl.i135.2" (BinOp.shl) 64 (Operand.reg "%160") (Operand.reg "%sh_prom.i127"),
        Instr.binop "%or.i136.2" (BinOp.or) 64 (Operand.reg "%shl.i135.2") (Operand.reg "%shr.i137.1"),
        Instr.store (Ty.int 64) (Operand.reg "%or.i136.2") (Operand.reg "%arrayidx.i134.2"),
        Instr.binop "%shr.i137.2" (BinOp.lshr) 64 (Operand.reg "%160") (Operand.reg "%sh_prom9.i129"),
        Instr.binop "%indvars.iv.next.i138.2" (BinOp.or) 64 (Operand.reg "%indvars.iv.i132") (Operand.imm (Const.int 64 0x0000000000000003#64)),
        Instr.gep "%arrayidx.i134.3" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%indvars.iv.next.i138.2"),
        Instr.load "%161" (Ty.int 64) (Operand.reg "%arrayidx.i134.3"),
        Instr.binop "%shl.i135.3" (BinOp.shl) 64 (Operand.reg "%161") (Operand.reg "%sh_prom.i127"),
        Instr.binop "%or.i136.3" (BinOp.or) 64 (Operand.reg "%shl.i135.3") (Operand.reg "%shr.i137.2"),
        Instr.store (Ty.int 64) (Operand.reg "%or.i136.3") (Operand.reg "%arrayidx.i134.3"),
        Instr.binop "%shr.i137.3" (BinOp.lshr) 64 (Operand.reg "%161") (Operand.reg "%sh_prom9.i129"),
        Instr.binop "%indvars.iv.next.i138.3" (BinOp.add) 64 (Operand.reg "%indvars.iv.i132") (Operand.imm (Const.int 64 0x0000000000000004#64)),
        Instr.binop "%niter333.next.3" (BinOp.add) 64 (Operand.reg "%niter333") (Operand.imm (Const.int 64 0x0000000000000004#64)),
        Instr.icmp "%niter333.ncmp.3" (IPred.eq) 64 (Operand.reg "%niter333.next.3") (Operand.reg "%unroll_iter332")
      ],
      term := Term.condbr (Operand.reg "%niter333.ncmp.3") "for.cond.cleanup.i140.unr-lcssa" "for.body.i131" },
    { name := "if.then11.i142",
      instrs := [
        Instr.binop "%inc14.i143" (BinOp.add) 32 (Operand.reg "%.pre181") (Operand.imm (Const.int 32 0x00000001#32)),
        Instr.gep "%arrayidx16.i145" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%wide.trip.count.i130"),
        Instr.store (Ty.int 64) (Operand.reg "%shr.i137.lcssa") (Operand.reg "%arrayidx16.i145")
      ],
      term := Term.br "if.end18.i111" },
    { name := "if.end18.i111",
      instrs := [
        Instr.phi "%162" (Ty.int 32) [("for.cond.cleanup.i140", (Operand.reg "%.pre181")),
                                       ("if.then11.i142", (Operand.reg "%inc14.i143")),
                                       ("if.end.i105", (Operand.reg "%.pre181"))],
        Instr.icmp "%tobool19.not.i112" (IPred.ult) 64 (Operand.reg "%eB") (Operand.imm (Const.int 64 0x0000000000000040#64))
      ],
      term := Term.condbr (Operand.reg "%tobool19.not.i112") "if.end14" "if.then20.i113" },
    { name := "if.then20.i113",
      instrs := [
        Instr.binop "%i21.082.i114" (BinOp.add) 32 (Operand.reg "%162") (Operand.imm (Const.int 32 0xffffffff#32)),
        Instr.icmp "%cmp2583.i115" (IPred.sgt) 32 (Operand.reg "%i21.082.i114") (Operand.imm (Const.int 32 0xffffffff#32))
      ],
      term := Term.condbr (Operand.reg "%cmp2583.i115") "iter.check269" "for.cond.cleanup39.i116" },
    { name := "iter.check269",
      instrs := [
        Instr.zext "%163" 32 64 (Operand.reg "%i21.082.i114"),
        Instr.zext "%164" 32 64 (Operand.reg "%162"),
        Instr.icmp "%min.iters.check267" (IPred.ult) 32 (Operand.reg "%162") (Operand.imm (Const.int 32 0x00000004#32))
      ],
      term := Term.condbr (Operand.reg "%min.iters.check267") "for.body27.i119.preheader" "vector.scevcheck261" },
    { name := "vector.scevcheck261",
      instrs := [
        Instr.binop "%165" (BinOp.add) 32 (Operand.reg "%162") (Operand.reg "%div78.i106"),
        Instr.binop "%166" (BinOp.add) 32 (Operand.reg "%165") (Operand.imm (Const.int 32 0xffffffff#32)),
        Instr.icmp "%167" (IPred.sgt) 32 (Operand.reg "%div78.i106") (Operand.reg "%166")
      ],
      term := Term.condbr (Operand.reg "%167") "for.body27.i119.preheader" "vector.memcheck265" },
    { name := "vector.memcheck265",
      instrs := [
        Instr.binop "%168" (BinOp.add) 32 (Operand.reg "%162") (Operand.reg "%div78.i106"),
        Instr.binop "%169" (BinOp.add) 32 (Operand.reg "%168") (Operand.imm (Const.int 32 0xffffffff#32)),
        Instr.sext "%170" 32 64 (Operand.reg "%169"),
        Instr.binop "%171" (BinOp.sub) 64 (Operand.reg "%163") (Operand.reg "%170"),
        Instr.binop "%172" (BinOp.and) 64 (Operand.reg "%171") (Operand.imm (Const.int 64 0x1ffffffffffffff0#64)),
        Instr.icmp "%diff.check266" (IPred.eq) 64 (Operand.reg "%172") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%diff.check266") "for.body27.i119.preheader" "vector.main.loop.iter.check271" },
    { name := "vector.main.loop.iter.check271",
      instrs := [
        Instr.icmp "%min.iters.check270" (IPred.ult) 32 (Operand.reg "%162") (Operand.imm (Const.int 32 0x00000010#32))
      ],
      term := Term.condbr (Operand.reg "%min.iters.check270") "vec.epilog.ph294" "vector.ph272" },
    { name := "vector.ph272",
      instrs := [
        Instr.binop "%n.vec274" (BinOp.and) 64 (Operand.reg "%164") (Operand.imm (Const.int 64 0x00000000fffffff0#64))
      ],
      term := Term.br "vector.body275" },
    { name := "vector.body275",
      instrs := [
        Instr.phi "%index276" (Ty.int 64) [("vector.ph272", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("vector.body275", (Operand.reg "%index.next289"))],
        Instr.binop "%173" (BinOp.sub) 64 (Operand.reg "%163") (Operand.reg "%index276"),
        Instr.trunc "%174" 64 32 (Operand.reg "%index276"),
        Instr.binop "%175" (BinOp.sub) 32 (Operand.reg "%i21.082.i114") (Operand.reg "%174"),
        Instr.gep "%176" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%173"),
        Instr.gep "%177" (Ty.int 8) (Operand.reg "%176") (Operand.imm (Const.int 64 0xffffffffffffffe8#64)),
        Instr.gep "%178" (Ty.int 8) (Operand.reg "%176") (Operand.imm (Const.int 64 0xffffffffffffffc8#64)),
        Instr.gep "%179" (Ty.int 8) (Operand.reg "%176") (Operand.imm (Const.int 64 0xffffffffffffffa8#64)),
        Instr.gep "%180" (Ty.int 8) (Operand.reg "%176") (Operand.imm (Const.int 64 0xffffffffffffff88#64)),
        Instr.load "%wide.load277" (Ty.vec 4 (Ty.int 64)) (Operand.reg "%177"),
        Instr.load "%wide.load279" (Ty.vec 4 (Ty.int 64)) (Operand.reg "%178"),
        Instr.load "%wide.load281" (Ty.vec 4 (Ty.int 64)) (Operand.reg "%179"),
        Instr.load "%wide.load283" (Ty.vec 4 (Ty.int 64)) (Operand.reg "%180"),
        Instr.binop "%181" (BinOp.add) 32 (Operand.reg "%div78.i106") (Operand.reg "%175"),
        Instr.sext "%182" 32 64 (Operand.reg "%181"),
        Instr.gep "%183" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%182"),
        Instr.gep "%184" (Ty.int 8) (Operand.reg "%183") (Operand.imm (Const.int 64 0xffffffffffffffe8#64)),
        Instr.gep "%185" (Ty.int 8) (Operand.reg "%183") (Operand.imm (Const.int 64 0xffffffffffffffc8#64)),
        Instr.gep "%186" (Ty.int 8) (Operand.reg "%183") (Operand.imm (Const.int 64 0xffffffffffffffa8#64)),
        Instr.gep "%187" (Ty.int 8) (Operand.reg "%183") (Operand.imm (Const.int 64 0xffffffffffffff88#64)),
        Instr.store (Ty.vec 4 (Ty.int 64)) (Operand.reg "%wide.load277") (Operand.reg "%184"),
        Instr.store (Ty.vec 4 (Ty.int 64)) (Operand.reg "%wide.load279") (Operand.reg "%185"),
        Instr.store (Ty.vec 4 (Ty.int 64)) (Operand.reg "%wide.load281") (Operand.reg "%186"),
        Instr.store (Ty.vec 4 (Ty.int 64)) (Operand.reg "%wide.load283") (Operand.reg "%187"),
        Instr.binop "%index.next289" (BinOp.add) 64 (Operand.reg "%index276") (Operand.imm (Const.int 64 0x0000000000000010#64)),
        Instr.icmp "%188" (IPred.eq) 64 (Operand.reg "%index.next289") (Operand.reg "%n.vec274")
      ],
      term := Term.condbr (Operand.reg "%188") "middle.block290" "vector.body275" },
    { name := "middle.block290",
      instrs := [
        Instr.icmp "%cmp.n291" (IPred.eq) 64 (Operand.reg "%n.vec274") (Operand.reg "%164")
      ],
      term := Term.condbr (Operand.reg "%cmp.n291") "for.cond.cleanup39.i116" "vec.epilog.iter.check295" },
    { name := "vec.epilog.iter.check295",
      instrs := [
        Instr.binop "%ind.end311" (BinOp.sub) 64 (Operand.reg "%163") (Operand.reg "%n.vec274"),
        Instr.binop "%n.vec.remaining296" (BinOp.and) 64 (Operand.reg "%164") (Operand.imm (Const.int 64 0x000000000000000c#64)),
        Instr.icmp "%min.epilog.iters.check297" (IPred.eq) 64 (Operand.reg "%n.vec.remaining296") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%min.epilog.iters.check297") "for.body27.i119.preheader" "vec.epilog.ph294" },
    { name := "vec.epilog.ph294",
      instrs := [
        Instr.phi "%vec.epilog.resume.val292" (Ty.int 64) [("vec.epilog.iter.check295", (Operand.reg "%n.vec274")),
                                       ("vector.main.loop.iter.check271", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.binop "%n.vec299" (BinOp.and) 64 (Operand.reg "%164") (Operand.imm (Const.int 64 0x00000000fffffffc#64)),
        Instr.binop "%189" (BinOp.sub) 64 (Operand.reg "%163") (Operand.reg "%n.vec299"),
        Instr.gep "%invariant.gep346" (Ty.int 8) (Operand.reg "%b") (Operand.imm (Const.int 64 0xffffffffffffffe8#64)),
        Instr.gep "%invariant.gep348" (Ty.int 8) (Operand.reg "%b") (Operand.imm (Const.int 64 0xffffffffffffffe8#64))
      ],
      term := Term.br "vec.epilog.vector.body300" },
    { name := "vec.epilog.vector.body300",
      instrs := [
        Instr.phi "%index301" (Ty.int 64) [("vec.epilog.ph294", (Operand.reg "%vec.epilog.resume.val292")),
                                       ("vec.epilog.vector.body300", (Operand.reg "%index.next307"))],
        Instr.binop "%offset.idx302" (BinOp.sub) 64 (Operand.reg "%163") (Operand.reg "%index301"),
        Instr.trunc "%190" 64 32 (Operand.reg "%index301"),
        Instr.binop "%191" (BinOp.sub) 32 (Operand.reg "%i21.082.i114") (Operand.reg "%190"),
        Instr.gep "%gep347" (Ty.int 64) (Operand.reg "%invariant.gep346") (Operand.reg "%offset.idx302"),
        Instr.load "%wide.load304" (Ty.vec 4 (Ty.int 64)) (Operand.reg "%gep347"),
        Instr.binop "%192" (BinOp.add) 32 (Operand.reg "%div78.i106") (Operand.reg "%191"),
        Instr.sext "%193" 32 64 (Operand.reg "%192"),
        Instr.gep "%gep349" (Ty.int 64) (Operand.reg "%invariant.gep348") (Operand.reg "%193"),
        Instr.store (Ty.vec 4 (Ty.int 64)) (Operand.reg "%wide.load304") (Operand.reg "%gep349"),
        Instr.binop "%index.next307" (BinOp.add) 64 (Operand.reg "%index301") (Operand.imm (Const.int 64 0x0000000000000004#64)),
        Instr.icmp "%194" (IPred.eq) 64 (Operand.reg "%index.next307") (Operand.reg "%n.vec299")
      ],
      term := Term.condbr (Operand.reg "%194") "vec.epilog.middle.block308" "vec.epilog.vector.body300" },
    { name := "vec.epilog.middle.block308",
      instrs := [
        Instr.icmp "%cmp.n309" (IPred.eq) 64 (Operand.reg "%n.vec299") (Operand.reg "%164")
      ],
      term := Term.condbr (Operand.reg "%cmp.n309") "for.cond.cleanup39.i116" "for.body27.i119.preheader" },
    { name := "for.body27.i119.preheader",
      instrs := [
        Instr.phi "%indvars.iv88.i120.ph" (Ty.int 64) [("iter.check269", (Operand.reg "%163")),
                                       ("vector.scevcheck261", (Operand.reg "%163")),
                                       ("vector.memcheck265", (Operand.reg "%163")),
                                       ("vec.epilog.iter.check295", (Operand.reg "%ind.end311")),
                                       ("vec.epilog.middle.block308", (Operand.reg "%189"))],
        Instr.binop "%195" (BinOp.add) 64 (Operand.reg "%indvars.iv88.i120.ph") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.binop "%xtraiter334" (BinOp.and) 64 (Operand.reg "%195") (Operand.imm (Const.int 64 0x0000000000000007#64)),
        Instr.binop "%196" (BinOp.and) 64 (Operand.reg "%indvars.iv88.i120.ph") (Operand.imm (Const.int 64 0x0000000000000007#64)),
        Instr.icmp "%lcmp.mod335.not" (IPred.eq) 64 (Operand.reg "%196") (Operand.imm (Const.int 64 0x0000000000000007#64))
      ],
      term := Term.condbr (Operand.reg "%lcmp.mod335.not") "for.body27.i119.prol.loopexit" "for.body27.i119.prol" },
    { name := "for.body27.i119.prol",
      instrs := [
        Instr.phi "%indvars.iv88.i120.prol" (Ty.int 64) [("for.body27.i119.prol", (Operand.reg "%indvars.iv.next89.i124.prol")),
                                       ("for.body27.i119.preheader", (Operand.reg "%indvars.iv88.i120.ph"))],
        Instr.phi "%prol.iter336" (Ty.int 64) [("for.body27.i119.prol", (Operand.reg "%prol.iter336.next")),
                                       ("for.body27.i119.preheader", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.gep "%arrayidx30.i121.prol" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%indvars.iv88.i120.prol"),
        Instr.load "%197" (Ty.int 64) (Operand.reg "%arrayidx30.i121.prol"),
        Instr.trunc "%198" 64 32 (Operand.reg "%indvars.iv88.i120.prol"),
        Instr.binop "%199" (BinOp.add) 32 (Operand.reg "%div78.i106") (Operand.reg "%198"),
        Instr.sext "%idxprom32.i122.prol" 32 64 (Operand.reg "%199"),
        Instr.gep "%arrayidx33.i123.prol" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%idxprom32.i122.prol"),
        Instr.store (Ty.int 64) (Operand.reg "%197") (Operand.reg "%arrayidx33.i123.prol"),
        Instr.binop "%indvars.iv.next89.i124.prol" (BinOp.add) 64 (Operand.reg "%indvars.iv88.i120.prol") (Operand.imm (Const.int 64 0xffffffffffffffff#64)),
        Instr.binop "%prol.iter336.next" (BinOp.add) 64 (Operand.reg "%prol.iter336") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%prol.iter336.cmp.not" (IPred.eq) 64 (Operand.reg "%prol.iter336.next") (Operand.reg "%xtraiter334")
      ],
      term := Term.condbr (Operand.reg "%prol.iter336.cmp.not") "for.body27.i119.prol.loopexit" "for.body27.i119.prol" },
    { name := "for.body27.i119.prol.loopexit",
      instrs := [
        Instr.phi "%indvars.iv88.i120.unr" (Ty.int 64) [("for.body27.i119.preheader", (Operand.reg "%indvars.iv88.i120.ph")),
                                       ("for.body27.i119.prol", (Operand.reg "%indvars.iv.next89.i124.prol"))],
        Instr.icmp "%200" (IPred.ult) 64 (Operand.reg "%indvars.iv88.i120.ph") (Operand.imm (Const.int 64 0x0000000000000007#64))
      ],
      term := Term.condbr (Operand.reg "%200") "for.cond.cleanup39.i116" "for.body27.i119" },
    { name := "for.body27.i119",
      instrs := [
        Instr.phi "%indvars.iv88.i120" (Ty.int 64) [("for.body27.i119", (Operand.reg "%indvars.iv.next89.i124.7")),
                                       ("for.body27.i119.prol.loopexit", (Operand.reg "%indvars.iv88.i120.unr"))],
        Instr.gep "%arrayidx30.i121" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%indvars.iv88.i120"),
        Instr.load "%201" (Ty.int 64) (Operand.reg "%arrayidx30.i121"),
        Instr.trunc "%202" 64 32 (Operand.reg "%indvars.iv88.i120"),
        Instr.binop "%203" (BinOp.add) 32 (Operand.reg "%div78.i106") (Operand.reg "%202"),
        Instr.sext "%idxprom32.i122" 32 64 (Operand.reg "%203"),
        Instr.gep "%arrayidx33.i123" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%idxprom32.i122"),
        Instr.store (Ty.int 64) (Operand.reg "%201") (Operand.reg "%arrayidx33.i123"),
        Instr.binop "%indvars.iv.next89.i124" (BinOp.add) 64 (Operand.reg "%indvars.iv88.i120") (Operand.imm (Const.int 64 0xffffffffffffffff#64)),
        Instr.gep "%arrayidx30.i121.1" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%indvars.iv.next89.i124"),
        Instr.load "%204" (Ty.int 64) (Operand.reg "%arrayidx30.i121.1"),
        Instr.trunc "%205" 64 32 (Operand.reg "%indvars.iv.next89.i124"),
        Instr.binop "%206" (BinOp.add) 32 (Operand.reg "%div78.i106") (Operand.reg "%205"),
        Instr.sext "%idxprom32.i122.1" 32 64 (Operand.reg "%206"),
        Instr.gep "%arrayidx33.i123.1" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%idxprom32.i122.1"),
        Instr.store (Ty.int 64) (Operand.reg "%204") (Operand.reg "%arrayidx33.i123.1"),
        Instr.binop "%indvars.iv.next89.i124.1" (BinOp.add) 64 (Operand.reg "%indvars.iv88.i120") (Operand.imm (Const.int 64 0xfffffffffffffffe#64)),
        Instr.gep "%arrayidx30.i121.2" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%indvars.iv.next89.i124.1"),
        Instr.load "%207" (Ty.int 64) (Operand.reg "%arrayidx30.i121.2"),
        Instr.trunc "%208" 64 32 (Operand.reg "%indvars.iv.next89.i124.1"),
        Instr.binop "%209" (BinOp.add) 32 (Operand.reg "%div78.i106") (Operand.reg "%208"),
        Instr.sext "%idxprom32.i122.2" 32 64 (Operand.reg "%209"),
        Instr.gep "%arrayidx33.i123.2" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%idxprom32.i122.2"),
        Instr.store (Ty.int 64) (Operand.reg "%207") (Operand.reg "%arrayidx33.i123.2"),
        Instr.binop "%indvars.iv.next89.i124.2" (BinOp.add) 64 (Operand.reg "%indvars.iv88.i120") (Operand.imm (Const.int 64 0xfffffffffffffffd#64)),
        Instr.gep "%arrayidx30.i121.3" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%indvars.iv.next89.i124.2"),
        Instr.load "%210" (Ty.int 64) (Operand.reg "%arrayidx30.i121.3"),
        Instr.trunc "%211" 64 32 (Operand.reg "%indvars.iv.next89.i124.2"),
        Instr.binop "%212" (BinOp.add) 32 (Operand.reg "%div78.i106") (Operand.reg "%211"),
        Instr.sext "%idxprom32.i122.3" 32 64 (Operand.reg "%212"),
        Instr.gep "%arrayidx33.i123.3" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%idxprom32.i122.3"),
        Instr.store (Ty.int 64) (Operand.reg "%210") (Operand.reg "%arrayidx33.i123.3"),
        Instr.binop "%indvars.iv.next89.i124.3" (BinOp.add) 64 (Operand.reg "%indvars.iv88.i120") (Operand.imm (Const.int 64 0xfffffffffffffffc#64)),
        Instr.gep "%arrayidx30.i121.4" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%indvars.iv.next89.i124.3"),
        Instr.load "%213" (Ty.int 64) (Operand.reg "%arrayidx30.i121.4"),
        Instr.trunc "%214" 64 32 (Operand.reg "%indvars.iv.next89.i124.3"),
        Instr.binop "%215" (BinOp.add) 32 (Operand.reg "%div78.i106") (Operand.reg "%214"),
        Instr.sext "%idxprom32.i122.4" 32 64 (Operand.reg "%215"),
        Instr.gep "%arrayidx33.i123.4" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%idxprom32.i122.4"),
        Instr.store (Ty.int 64) (Operand.reg "%213") (Operand.reg "%arrayidx33.i123.4"),
        Instr.binop "%indvars.iv.next89.i124.4" (BinOp.add) 64 (Operand.reg "%indvars.iv88.i120") (Operand.imm (Const.int 64 0xfffffffffffffffb#64)),
        Instr.gep "%arrayidx30.i121.5" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%indvars.iv.next89.i124.4"),
        Instr.load "%216" (Ty.int 64) (Operand.reg "%arrayidx30.i121.5"),
        Instr.trunc "%217" 64 32 (Operand.reg "%indvars.iv.next89.i124.4"),
        Instr.binop "%218" (BinOp.add) 32 (Operand.reg "%div78.i106") (Operand.reg "%217"),
        Instr.sext "%idxprom32.i122.5" 32 64 (Operand.reg "%218"),
        Instr.gep "%arrayidx33.i123.5" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%idxprom32.i122.5"),
        Instr.store (Ty.int 64) (Operand.reg "%216") (Operand.reg "%arrayidx33.i123.5"),
        Instr.binop "%indvars.iv.next89.i124.5" (BinOp.add) 64 (Operand.reg "%indvars.iv88.i120") (Operand.imm (Const.int 64 0xfffffffffffffffa#64)),
        Instr.gep "%arrayidx30.i121.6" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%indvars.iv.next89.i124.5"),
        Instr.load "%219" (Ty.int 64) (Operand.reg "%arrayidx30.i121.6"),
        Instr.trunc "%220" 64 32 (Operand.reg "%indvars.iv.next89.i124.5"),
        Instr.binop "%221" (BinOp.add) 32 (Operand.reg "%div78.i106") (Operand.reg "%220"),
        Instr.sext "%idxprom32.i122.6" 32 64 (Operand.reg "%221"),
        Instr.gep "%arrayidx33.i123.6" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%idxprom32.i122.6"),
        Instr.store (Ty.int 64) (Operand.reg "%219") (Operand.reg "%arrayidx33.i123.6"),
        Instr.binop "%indvars.iv.next89.i124.6" (BinOp.add) 64 (Operand.reg "%indvars.iv88.i120") (Operand.imm (Const.int 64 0xfffffffffffffff9#64)),
        Instr.gep "%arrayidx30.i121.7" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%indvars.iv.next89.i124.6"),
        Instr.load "%222" (Ty.int 64) (Operand.reg "%arrayidx30.i121.7"),
        Instr.trunc "%223" 64 32 (Operand.reg "%indvars.iv.next89.i124.6"),
        Instr.binop "%224" (BinOp.add) 32 (Operand.reg "%div78.i106") (Operand.reg "%223"),
        Instr.sext "%idxprom32.i122.7" 32 64 (Operand.reg "%224"),
        Instr.gep "%arrayidx33.i123.7" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%idxprom32.i122.7"),
        Instr.store (Ty.int 64) (Operand.reg "%222") (Operand.reg "%arrayidx33.i123.7"),
        Instr.binop "%indvars.iv.next89.i124.7" (BinOp.add) 64 (Operand.reg "%indvars.iv88.i120") (Operand.imm (Const.int 64 0xfffffffffffffff8#64)),
        Instr.icmp "%cmp25.not.i125.7" (IPred.eq) 64 (Operand.reg "%indvars.iv.next89.i124.6") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%cmp25.not.i125.7") "for.cond.cleanup39.i116" "for.body27.i119" },
    { name := "for.cond.cleanup39.i116",
      instrs := [
        Instr.binop "%225" (BinOp.lshr) 64 (Operand.reg "%eB") (Operand.imm (Const.int 64 0x0000000000000003#64)),
        Instr.binop "%226" (BinOp.and) 64 (Operand.reg "%225") (Operand.imm (Const.int 64 0x000000001ffffff8#64)),
        Instr.callVoid "llvm.memset.p0.i64" [(Ty.ptr, (Operand.reg "%b")),
                             ((Ty.int 8), (Operand.imm (Const.int 8 0x00#8))),
                             ((Ty.int 64), (Operand.reg "%226")),
                             ((Ty.int 1), (Operand.imm (Const.int 1 0x0#1)))],
        Instr.binop "%add48.i117" (BinOp.add) 32 (Operand.reg "%162") (Operand.reg "%div78.i106")
      ],
      term := Term.br "if.end14" },
    { name := "if.end14",
      instrs := [
        Instr.phi "%227" (Ty.int 32) [("for.cond.cleanup39.i116", (Operand.reg "%add48.i117")),
                                       ("if.end18.i111", (Operand.reg "%162")),
                                       ("lor.lhs.false.i102", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("stk_copy.exit100", (Operand.reg "%.pre181"))],
        Instr.load "%228" (Ty.int 32) (Operand.reg "%n1.i38"),
        Instr.icmp "%cmp.not.i149" (IPred.eq) 32 (Operand.reg "%228") (Operand.reg "%227")
      ],
      term := Term.condbr (Operand.reg "%cmp.not.i149") "for.cond.preheader.i154" "if.then.i150" },
    { name := "for.cond.preheader.i154",
      instrs := [
        Instr.zext "%229" 32 64 (Operand.reg "%227")
      ],
      term := Term.br "for.cond.i155" },
    { name := "if.then.i150",
      instrs := [
        Instr.icmp "%cmp4.i151" (IPred.slt) 32 (Operand.reg "%228") (Operand.reg "%227"),
        Instr.select "%cond.i152" (Ty.int 32) (Operand.reg "%cmp4.i151") (Operand.imm (Const.int 32 0xffffffff#32)) (Operand.imm (Const.int 32 0x00000001#32))
      ],
      term := Term.br "cleanup" },
    { name := "for.cond.i155",
      instrs := [
        Instr.phi "%indvars.iv.i156" (Ty.int 64) [("for.cond.preheader.i154", (Operand.reg "%229")),
                                       ("for.body.i159", (Operand.reg "%indvars.iv.next.i157"))],
        Instr.binop "%indvars.iv.next.i157" (BinOp.add) 64 (Operand.reg "%indvars.iv.i156") (Operand.imm (Const.int 64 0xffffffffffffffff#64)),
        Instr.binop "%230" (BinOp.and) 64 (Operand.reg "%indvars.iv.next.i157") (Operand.imm (Const.int 64 0x0000000080000000#64)),
        Instr.icmp "%cmp6.not.i158" (IPred.eq) 64 (Operand.reg "%230") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%cmp6.not.i158") "for.body.i159" "cleanup" },
    { name := "for.body.i159",
      instrs := [
        Instr.binop "%idxprom.i160" (BinOp.and) 64 (Operand.reg "%indvars.iv.next.i157") (Operand.imm (Const.int 64 0x000000007fffffff#64)),
        Instr.gep "%arrayidx.i161" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%idxprom.i160"),
        Instr.load "%231" (Ty.int 64) (Operand.reg "%arrayidx.i161"),
        Instr.gep "%arrayidx9.i162" (Ty.int 64) (Operand.reg "%b") (Operand.reg "%idxprom.i160"),
        Instr.load "%232" (Ty.int 64) (Operand.reg "%arrayidx9.i162"),
        Instr.icmp "%cmp10.not.i163" (IPred.eq) 64 (Operand.reg "%231") (Operand.reg "%232")
      ],
      term := Term.condbr (Operand.reg "%cmp10.not.i163") "for.cond.i155" "if.then11.i164" },
    { name := "if.then11.i164",
      instrs := [
        Instr.icmp "%cmp18.i165" (IPred.ult) 64 (Operand.reg "%231") (Operand.reg "%232"),
        Instr.select "%cond19.i166" (Ty.int 32) (Operand.reg "%cmp18.i165") (Operand.imm (Const.int 32 0xffffffff#32)) (Operand.imm (Const.int 32 0x00000001#32))
      ],
      term := Term.br "cleanup" },
    { name := "cleanup",
      instrs := [
        Instr.phi "%retval.0" (Ty.int 32) [("if.then.i150", (Operand.reg "%cond.i152")),
                                       ("if.then11.i164", (Operand.reg "%cond19.i166")),
                                       ("if.then.i31", (Operand.reg "%spec.select")),
                                       ("if.then11.i36", (Operand.reg "%spec.select172")),
                                       ("for.cond.i155", (Operand.imm (Const.int 32 0x00000000#32))),
                                       ("for.cond.i", (Operand.imm (Const.int 32 0x00000001#32)))],
        Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000308#64))),
                             (Ty.ptr, (Operand.reg "%b"))],
        Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000308#64))),
                             (Ty.ptr, (Operand.reg "%a"))]
      ],
      term := Term.ret (Ty.int 32) (some (Operand.reg "%retval.0")) }] }


/- The pin: the fixture parses to the literal above. -/
#guard decide (firstFunctionWith numCmpLayout numCmpSrc = some numCmpBody)

/- The control: the same fixture with the sticky flag's offset changed parses,
and it is not the pinned body, so the equality above is about the text rather
than about a search that would accept anything. -/
def numCmpSrcMutated : String := numCmpSrc.replace "i64 1560" "i64 1561"

#guard decide (firstFunctionWith numCmpLayout numCmpSrcMutated ≠ some numCmpBody)

/- The layout is load-bearing: without the two extents the fixture is refused,
because the struct's size is not in the text. -/
#guard decide (firstFunction numCmpSrc = none)

/- The shape `stage2.callees.tsv` records: 104 blocks, 757 parsed instructions,
three parameters. -/
#guard decide
  ((numCmpBody.name, numCmpBody.blocks.length,
      (numCmpBody.blocks.flatMap (·.instrs)).length, numCmpBody.params.length) =
    ("stk_cmp", 104, 757, 3))

/- The symbols the body names: `stk_mul_u64` out of line, the lifetime markers,
`memset`, and the fortified copy that is a fifth answer. -/
#guard hasSubstr numCmpSrc "@stk_mul_u64"
#guard hasSubstr numCmpSrc "@__memcpy_chk"
#guard hasSubstr numCmpSrc "@llvm.lifetime.start.p0"
#guard hasSubstr numCmpSrc "@llvm.memset.p0.i64"

/-! ### The block pins

The three blocks the argument below runs through, each read from the literal:
the entry's allocations and flag test, the copy count's branch, and the fortified
copy that ends the block undefined. -/

def numCmpEntryInstrs : List Instr :=
  [
    Instr.alloca "%a" (Ty.struct "StkBn" 776) 0,
    Instr.alloca "%b" (Ty.struct "StkBn" 776) 0,
    Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000308#64))),
                             (Ty.ptr, (Operand.reg "%a"))],
    Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000308#64))),
                             (Ty.ptr, (Operand.reg "%b"))],
    Instr.gep "%sticky" (Ty.int 8) (Operand.reg "%v") (Operand.imm (Const.int 64 0x0000000000000618#64)),
    Instr.load "%0" (Ty.int 32) (Operand.reg "%sticky"),
    Instr.icmp "%tobool.not" (IPred.eq) 32 (Operand.reg "%0") (Operand.imm (Const.int 32 0x00000000#32))]

def numCmpIfThenInstrs : List Instr :=
  [
    Instr.gep "%n.i" (Ty.int 8) (Operand.reg "%v") (Operand.imm (Const.int 64 0x0000000000000608#64)),
    Instr.load "%1" (Ty.int 32) (Operand.reg "%n.i"),
    Instr.gep "%n1.i" (Ty.int 8) (Operand.reg "%b") (Operand.imm (Const.int 64 0x0000000000000300#64)),
    Instr.store (Ty.int 32) (Operand.reg "%1") (Operand.reg "%n1.i"),
    Instr.icmp "%tobool.not.i" (IPred.eq) 32 (Operand.reg "%1") (Operand.imm (Const.int 32 0x00000000#32))]

def numCmpIfThenIInstrs : List Instr :=
  [
    Instr.gep "%pow" (Ty.int 8) (Operand.reg "%v") (Operand.imm (Const.int 64 0x0000000000000308#64)),
    Instr.sext "%conv.i" 32 64 (Operand.reg "%1"),
    Instr.binop "%mul.i" (BinOp.shl) 64 (Operand.reg "%conv.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
    Instr.call "%call.i.i" Ty.ptr "__memcpy_chk" [(Ty.ptr, (Operand.reg "%b")),
                             (Ty.ptr, (Operand.reg "%pow")),
                             ((Ty.int 64), (Operand.reg "%mul.i")),
                             ((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000308#64)))]]


theorem numCmp_findBlock_entry :
    numCmpBody.findBlock "entry" =
      some ⟨"entry", numCmpEntryInstrs,
        Term.condbr (Operand.reg "%tobool.not") "if.end" "if.then"⟩ := by decide

theorem numCmp_findBlock_ifThen :
    numCmpBody.findBlock "if.then" =
      some ⟨"if.then", numCmpIfThenInstrs,
        Term.condbr (Operand.reg "%tobool.not.i") "stk_copy.exit" "if.then.i"⟩ := by decide

theorem numCmp_findBlock_ifThenI :
    numCmpBody.findBlock "if.then.i" =
      some ⟨"if.then.i", numCmpIfThenIInstrs, Term.br "stk_copy.exit"⟩ := by decide


/-! ### The environment the body runs in

The body's own callees are the lifetime markers and `memset` (the walk's
staging), `stk_mul_u64` (its model), and the fortified copy — which nothing in
this tree answers.  `numCmpCalls base` is the first three and the base's answer
for the fourth; `numCmpBodyCalls` below is a selection that answers `stk_cmp`
with a run in that environment. -/

/-- The multiply answered by its model, and every other symbol to the base. -/
def numMulCalls (base : Calls) : Calls :=
  fun callee args mem next =>
    if callee = "stk_mul_u64" then numStkMulAnswer args mem next
    else base callee args mem next

/-- The body's environment: the walk's staging answers the lifetime markers,
`memset` and the trap; `stk_mul_u64` its model; everything else the base. -/
def numCmpCalls (base : Calls) : Calls := JsonStage2IR.stage2Calls (numMulCalls base)

/-- A lifetime marker leaves the state it is called on. -/
theorem numCmpCalls_lifetime (base : Calls) (w a : Nat) (mem : Mem) (next : Nat) :
    numCmpCalls base "llvm.lifetime.start.p0" [.int 64 w, .ptr a] mem next =
      some ⟨.int 1 0, mem, next⟩ := rfl

/-- The fortified copy is the base's to answer: the body's environment does not
add one. -/
theorem numCmpCalls_memcpy (base : Calls) (vs : List Value) (mem : Mem) (next : Nat) :
    numCmpCalls base "__memcpy_chk" vs mem next = base "__memcpy_chk" vs mem next := by
  simp [numCmpCalls, numMulCalls, JsonStage2IR.stage2Calls]

/-! ### The step vocabulary this body needs

Two instruction shapes the tree's chain steps do not already cover are stated
here: the two-argument void call (the lifetime markers) and the 32-bit `sext`.
The four-argument call that ends `if.then.i` is stated for *any* argument list at
a callee that answers nothing, which is the only fact about it this module uses. -/

/-- A two-argument void call: the lifetime markers' shape. -/
theorem denoteCode_callVoid2 (calls : Calls) (env : Env) (s : State) (callee : String)
    (o1 o2 : Operand) {v1 v2 : Value} {r : CallOutcome}
    (h1 : evalOperand (stateAt env s) o1 = some v1)
    (h2 : evalOperand (stateAt env s) o2 = some v2)
    (hc : calls callee [v1, v2] s.mem s.next = some r) (is : List Instr) :
    denoteCode calls (.callVoid callee [(Ty.int 64, o1), (Ty.ptr, o2)] :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt env { s with mem := r.mem, next := r.next }) := by
  have hargs : evalOperands (stateAt env s) [(Ty.int 64, o1), (Ty.ptr, o2)] =
      some [v1, v2] := by
    simp only [evalOperands, h1, h2]
  have hc' : calls callee [v1, v2] (stateAt env s).mem (stateAt env s).next = some r := hc
  refine BlockEval.denoteCode_cons_of calls _ is _ _ ?_ (by rfl)
  simp only [evalInstr, hargs, hc']
  rfl

/-- `%d = sext iN %v to iM`. -/
theorem denoteCode_sext (calls : Calls) (env : Env) (s : State) (d v : String)
    (wIn wOut : Nat) {x : BitVec wIn}
    (hv : lookupName env v = some (.int wIn x)) (is : List Instr) :
    denoteCode calls (.sext d wIn wOut (.reg v) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int wOut (BitVec.ofNat wOut
        (BitVec.signExtend wOut (BitVec.ofNat wIn x.toNat)).toNat)) :: env) s) := by
  refine BlockEval.denoteCode_cons_of calls _ is _ _ ?_ (by rfl)
  simp [evalInstr, evalOperand, stateAt, hv, State.bind]

/-- A four-argument call whose callee answers nothing is undefined, whatever its
arguments read: the fortified copy's shape. -/
theorem denoteCode_call_none4_any (calls : Calls) (env : Env) (s : State)
    (d callee : String) (a b c e : Operand)
    (hnone : ∀ (vs : List Value) (mem : Mem) (next : Nat),
      calls callee vs mem next = none) (is : List Instr) :
    denoteCode calls
        (.call d Ty.ptr callee
          [(Ty.ptr, a), (Ty.ptr, b), (Ty.int 64, c), (Ty.int 64, e)] :: is)
        (stateAt env s) = none := by
  simp only [denoteCode, denoteRun, evalInstr, State.bindAll]
  cases h : evalOperands (stateAt env s)
      [(Ty.ptr, a), (Ty.ptr, b), (Ty.int 64, c), (Ty.int 64, e)] with
  | none => rfl
  | some vs => simp only [h, hnone vs (stateAt env s).mem (stateAt env s).next]

theorem numCmp_step_size : (Ty.struct "StkBn" 776).sizeBytes = 776 := by decide

/-- The lifetime markers' step at this body's environment: they leave the state
they are called on, so the run passes through them without a cell or a write. -/
theorem denoteCode_lifetime_start (base : Calls) (env : Env) (s : State)
    (o1 o2 : Operand) {v1 v2 : Value}
    (h1 : evalOperand (stateAt env s) o1 = some v1)
    (h2 : evalOperand (stateAt env s) o2 = some v2) (is : List Instr) :
    denoteCode (numCmpCalls base)
        (.callVoid "llvm.lifetime.start.p0" [(Ty.int 64, o1), (Ty.ptr, o2)] :: is)
        (stateAt env s) =
      denoteCode (numCmpCalls base) is (stateAt env s) := by
  rw [denoteCode_callVoid2 (calls := numCmpCalls base) (callee := "llvm.lifetime.start.p0")
    (o1 := o1) (o2 := o2) (v1 := v1) (v2 := v2)
    (r := ⟨.int 1 0, s.mem, s.next⟩) (h1 := h1) (h2 := h2) (hc := by rfl)]

/-! ### `entry`: the two allocations, the markers, and the flag test -/

/-- The body's arguments, as the entry's environment holds them. -/
def numCmpEntryEnv (v J eB : Nat) : Env :=
  [("%v", .ptr v), ("%J", .int 64 J), ("%eB", .int 64 eB)]

/-- The state the body's entry is reached in, below the parameters. -/
def numCmpRaw (mem : Mem) (next : Nat) : State :=
  { env := [], mem := mem, next := next, pc := "entry", pre := none }

def numCmpEntryState (v J eB : Nat) (mem : Mem) (next : Nat) : State :=
  { env := numCmpEntryEnv v J eB, mem := mem, next := next, pc := "entry", pre := none }

/-- `entry`'s cells: the allocations' two pointers, the flag's read and its
test, in the order the block writes them. -/
def numCmpAfterEntryEnv (v J eB nxt : Nat) (sw : BitVec 32) : Env :=
  ("%tobool.not", .int 1 (evalICmp .eq sw 0)) ::
  ("%0", .int 32 sw) ::
  ("%sticky", .ptr (v + 1560)) ::
  ("%b", .ptr (nxt + 776)) ::
  ("%a", .ptr nxt) :: numCmpEntryEnv v J eB

/-- One allocation of the body's `StkBn`: the cell is the allocator's current
address and the cursor advances by the struct's extent.  The state is written as
`{ s with next := nxt }` so a chain of allocations keeps one base state and its
arithmetic, rather than nesting record updates. -/
theorem step_alloca_nxt (calls : Calls) (env : Env) (s : State) (d : String) (nxt : Nat) :
    evalInstr calls (stateAt env { s with next := nxt }) (.alloca d (Ty.struct "StkBn" 776) 0) =
      some (stateAt ((d, .ptr nxt) :: env) { s with next := nxt + 776 }) := by
  simp [evalInstr, stateAt, numCmp_step_size]

/-- `entry`'s run: the two allocations advance the cursor by 776 each, the two
markers write nothing, and the flag's word is read and tested.  The chain is
`Eq.trans` rather than `rw`, so each step is checked against the previous step's
state by definitional equality instead of by a subterm search. -/
theorem numCmp_entry_denote (base : Calls) (v J eB : Nat) (s : State) (nxt : Nat)
    (sw : BitVec 32)
    (hsw : readBytes s.mem (v + 1560) 4 = some (natToBytes sw.toNat 4)) :
    denoteCode (numCmpCalls base) numCmpEntryInstrs
        (stateAt (numCmpEntryEnv v J eB) { s with next := nxt }) =
      some (stateAt (numCmpAfterEntryEnv v J eB nxt sw)
        { s with next := nxt + 776 + 776 }) := by
  unfold numCmpEntryInstrs
  refine (BlockEval.denoteCode_cons_of _ _ _ _ _
    (step_alloca_nxt (calls := numCmpCalls base) (env := numCmpEntryEnv v J eB)
      (s := s) (d := "%a") (nxt := nxt))).trans ?_
  refine (BlockEval.denoteCode_cons_of _ _ _ _ _
    (step_alloca_nxt (calls := numCmpCalls base)
      (env := ("%a", .ptr nxt) :: numCmpEntryEnv v J eB)
      (s := s) (d := "%b") (nxt := nxt + 776))).trans ?_
  refine (denoteCode_lifetime_start (base := base)
    (env := ("%b", .ptr (nxt + 776)) :: ("%a", .ptr nxt) :: numCmpEntryEnv v J eB)
    (s := { s with next := nxt + 776 + 776 })
    (o1 := .imm (.int 64 776)) (o2 := .reg "%a") (v1 := .int 64 776) (v2 := .ptr nxt)
    (by rfl) (by simp only [numCmpEntryEnv]; block_lk) _).trans ?_
  refine (denoteCode_lifetime_start (base := base)
    (env := ("%b", .ptr (nxt + 776)) :: ("%a", .ptr nxt) :: numCmpEntryEnv v J eB)
    (s := { s with next := nxt + 776 + 776 })
    (o1 := .imm (.int 64 776)) (o2 := .reg "%b") (v1 := .int 64 776)
    (v2 := .ptr (nxt + 776)) (by rfl)
    (by simp only [numCmpEntryEnv]; block_lk) _).trans ?_
  refine (denoteCode_gep8_imm (calls := numCmpCalls base)
    (env := ("%b", .ptr (nxt + 776)) :: ("%a", .ptr nxt) :: numCmpEntryEnv v J eB)
    (s := { s with next := nxt + 776 + 776 }) (d := "%sticky") (base := "%v")
    (c := 0x0000000000000618#64) (hb := by
      simp only [numCmpEntryEnv]; block_lk) (hc := by decide) _).trans ?_
  refine (denoteCode_load32_word (calls := numCmpCalls base)
    (env := ("%sticky", .ptr (v + 1560)) ::
      ("%b", .ptr (nxt + 776)) :: ("%a", .ptr nxt) :: numCmpEntryEnv v J eB)
    (s := { s with next := nxt + 776 + 776 }) (d := "%0") (p := "%sticky")
    (hp := by block_lk)
    (hv := by simpa using hsw) _).trans ?_
  refine (denoteCode_icmp_imm_w (calls := numCmpCalls base)
    (env := ("%0", .int 32 sw) :: ("%sticky", .ptr (v + 1560)) ::
      ("%b", .ptr (nxt + 776)) :: ("%a", .ptr nxt) :: numCmpEntryEnv v J eB)
    (s := { s with next := nxt + 776 + 776 }) (d := "%tobool.not") (a := "%0")
    (pred := IPred.eq) (w := 32) (ha := by block_lk) _).trans ?_
  rfl

/-! ### `if.then`: the copy's count and its branch -/

/-- `if.then`'s cells: the count, the destination's pointer and the branch bit. -/
def numCmpIfThenEnv (v J eB nxt : Nat) (sw nw : BitVec 32) : Env :=
  ("%tobool.not.i", .int 1 (evalICmp .eq nw 0)) ::
  ("%n1.i", .ptr (nxt + 776 + 768)) ::
  ("%1", .int 32 nw) ::
  ("%n.i", .ptr (v + 1544)) ::
  numCmpAfterEntryEnv v J eB nxt sw

theorem numCmp_ifThen_denote (base : Calls) (v J eB nxt : Nat) (s : State)
    (sw nw : BitVec 32)
    (hnw : readBytes s.mem (v + 1544) 4 = some (natToBytes nw.toNat 4)) :
    denoteCode (numCmpCalls base) numCmpIfThenInstrs
        (stateAt (numCmpAfterEntryEnv v J eB nxt sw) s) =
      some (stateAt (numCmpIfThenEnv v J eB nxt sw nw)
        { s with mem := writeBytes s.mem (nxt + 776 + 768) (natToBytes nw.toNat 4) }) := by
  unfold numCmpIfThenInstrs
  refine (denoteCode_gep8_imm (calls := numCmpCalls base)
    (env := numCmpAfterEntryEnv v J eB nxt sw) (s := s) (d := "%n.i") (base := "%v")
    (c := 0x0000000000000608#64)
    (hb := by simp only [numCmpAfterEntryEnv, numCmpEntryEnv]; block_lk)
    (hc := by decide) _).trans ?_
  refine (denoteCode_load32_word (calls := numCmpCalls base)
    (env := ("%n.i", .ptr (v + 1544)) :: numCmpAfterEntryEnv v J eB nxt sw)
    (s := s) (d := "%1") (p := "%n.i") (hp := by block_lk) (hv := hnw) _).trans ?_
  refine (denoteCode_gep8_imm (calls := numCmpCalls base)
    (env := ("%1", .int 32 nw) :: ("%n.i", .ptr (v + 1544)) ::
      numCmpAfterEntryEnv v J eB nxt sw)
    (s := s) (d := "%n1.i") (base := "%b") (c := 0x0000000000000300#64)
    (hb := by simp only [numCmpAfterEntryEnv]; block_lk) (hc := by decide) _).trans ?_
  refine (denoteCode_store32 (calls := numCmpCalls base)
    (env := ("%n1.i", .ptr (nxt + 776 + 768)) :: ("%1", .int 32 nw) ::
      ("%n.i", .ptr (v + 1544)) :: numCmpAfterEntryEnv v J eB nxt sw)
    (s := s) (v := "%1") (p := "%n1.i") (hv := by block_lk) (hp := by block_lk) _).trans ?_
  refine (denoteCode_icmp_imm_w (calls := numCmpCalls base)
    (env := ("%n1.i", .ptr (nxt + 776 + 768)) :: ("%1", .int 32 nw) ::
      ("%n.i", .ptr (v + 1544)) :: numCmpAfterEntryEnv v J eB nxt sw)
    (s := { s with mem := writeBytes s.mem (nxt + 776 + 768) (natToBytes nw.toNat 4) })
    (d := "%tobool.not.i") (a := "%1") (pred := IPred.eq) (w := 32)
    (ha := by block_lk) _).trans ?_
  rfl

/-! ### `if.then.i`: the fortified copy -/

/-- `if.then.i` is undefined where the fortified copy is unanswered: the block
forms the destination's byte count and calls `__memcpy_chk`, and a selection that
leaves that symbol unanswered ends the block's run there. -/
theorem numCmp_ifThenI_denote_none {base : Calls} {env : Env} {s : State}
    {b v : Nat} {nw : BitVec 32}
    (hmem : ∀ (vs : List Value) (mem : Mem) (next : Nat),
      base "__memcpy_chk" vs mem next = none)
    (hb : lookupName env "%b" = some (.ptr b))
    (hv : lookupName env "%v" = some (.ptr v))
    (h1 : lookupName env "%1" = some (.int 32 nw)) :
    denoteCode (numCmpCalls base) numCmpIfThenIInstrs (stateAt env s) = none := by
  unfold numCmpIfThenIInstrs
  refine (denoteCode_gep8_imm (calls := numCmpCalls base)
    (env := env) (s := s) (d := "%pow") (base := "%v") (c := 0x0000000000000308#64)
    (hb := hv) (hc := by decide) _).trans ?_
  refine (denoteCode_sext (calls := numCmpCalls base)
    (env := ("%pow", .ptr (v + 776)) :: env) (s := s) (d := "%conv.i")
    (v := "%1") (wIn := 32) (wOut := 64)
    (hv := by
      rw [show lookupName (("%pow", .ptr (v + 776)) :: env) "%1" = lookupName env "%1" from by
        rw [lookupName_cons_ne _ _ (by decide)]]
      exact h1) _).trans ?_
  refine (denoteCode_shl_imm (calls := numCmpCalls base)
    (env := ("%conv.i", .int 64 (BitVec.ofNat 64
      (BitVec.signExtend 64 (BitVec.ofNat 32 nw.toNat)).toNat)) ::
      ("%pow", .ptr (v + 776)) :: env)
    (s := s) (d := "%mul.i") (a := "%conv.i") (c := 0x0000000000000003#64)
    (ha := lookupName_cons_self _ _ _) _).trans ?_
  exact denoteCode_call_none4_any (numCmpCalls base) _ s "%call.i.i" "__memcpy_chk"
    (Operand.reg "%b") (Operand.reg "%pow")
    (Operand.reg "%mul.i") (Operand.imm (Const.int 64 0x0000000000000308#64))
    (by
      intro vs mem next
      rw [numCmpCalls_memcpy]
      exact hmem vs mem next)
    _

/-! ### The step at a pinned block -/

/-- A block whose run ends undefined, at its own pin. -/
theorem numCmp_step_ub {calls : Calls} {env : Env} {s : State}
    {block dest : String} {instrs : List Instr}
    (hpc : s.pc = block)
    (hfind : numCmpBody.findBlock block = some ⟨block, instrs, Term.br dest⟩)
    (hden : denoteCode calls instrs (stateAt env s) = none) :
    step calls numCmpBody (stateAt env s) = .ub := by
  have hrec : denoteCode calls instrs
      { env := env, mem := s.mem, next := s.next, pc := block, pre := s.pre } = none := by
    rw [← hpc]
    exact hden
  simp only [stateAt, step, hpc, hfind, hrec]

/-! ### The run to the undefined copy -/

theorem numCmp_runFuel_jump {calls : Calls} {f : Function} {s t : State}
    (h : step calls f s = .jump t) : ∀ k, runFuel calls (1 + k) f s = runFuel calls k f t := by
  intro k
  rw [show 1 + k = k + 1 from Nat.add_comm 1 k, runFuel.eq_2, h]

/-- **The body's first copy is undefined where `__memcpy_chk` is unanswered.**
From the entry state the run reaches `some .ub` in three control steps: the flag
is set, so `entry` takes `if.then`; the count is nonzero, so `if.then` takes
`if.then.i`; and that block's fortified copy has no answer. -/
theorem numCmp_run_ub (base : Calls) (v J eB : Nat) (mem : Mem) (next : Nat)
    (sw nw : BitVec 32)
    (hsw : readBytes mem (v + 1560) 4 = some (natToBytes sw.toNat 4))
    (hnw : readBytes mem (v + 1544) 4 = some (natToBytes nw.toNat 4))
    (hsw0 : evalICmp .eq sw 0 = 0) (hnw0 : evalICmp .eq nw 0 = 0)
    (hmem : ∀ (vs : List Value) (m : Mem) (n : Nat),
      base "__memcpy_chk" vs m n = none) :
    runFuel (numCmpCalls base) 3 numCmpBody (numCmpEntryState v J eB mem next) = some .ub := by
  have hpc0 : (numCmpEntryState v J eB mem next).pc = "entry" := rfl
  have hcode0 : denoteCode (numCmpCalls base) numCmpEntryInstrs
      (numCmpEntryState v J eB mem next) =
      some (stateAt (numCmpAfterEntryEnv v J eB next sw)
        { numCmpRaw mem next with next := next + 776 + 776 }) := by
    have hst : numCmpEntryState v J eB mem next =
        stateAt (numCmpEntryEnv v J eB) { numCmpRaw mem next with next := next } := rfl
    rw [hst]
    exact numCmp_entry_denote base v J eB (numCmpRaw mem next) next sw hsw
  have hbit0 : evalOperand
      (stateAt (numCmpAfterEntryEnv v J eB next sw)
        { numCmpRaw mem next with next := next + 776 + 776 }) (.reg "%tobool.not") =
      some (.int 1 (evalICmp .eq sw 0)) :=
    evalOperand_reg_of _ _ _ _ (by simp [numCmpAfterEntryEnv])
  have h1 : step (numCmpCalls base) numCmpBody (numCmpEntryState v J eB mem next) =
      .jump (stateAt (numCmpAfterEntryEnv v J eB next sw)
        { numCmpRaw mem next with
          next := next + 776 + 776, pc := "if.then", pre := some "entry" }) := by
    unfold step execTerm
    rw [hpc0, numCmp_findBlock_entry]
    simp only [hcode0, hbit0, hsw0]
    rfl
  have hcode1 : denoteCode (numCmpCalls base) numCmpIfThenInstrs
      (stateAt (numCmpAfterEntryEnv v J eB next sw)
        { numCmpRaw mem next with
          next := next + 776 + 776, pc := "if.then", pre := some "entry" }) =
      some (stateAt (numCmpIfThenEnv v J eB next sw nw)
        { numCmpRaw mem next with
          next := next + 776 + 776,
          mem := writeBytes mem (next + 776 + 768) (natToBytes nw.toNat 4),
          pc := "if.then", pre := some "entry" }) := by
    have h := numCmp_ifThen_denote base v J eB next
      { numCmpRaw mem next with
        next := next + 776 + 776, pc := "if.then", pre := some "entry" } sw nw hnw
    simpa only [numCmpRaw] using h
  have hbit1 : evalOperand
      (stateAt (numCmpIfThenEnv v J eB next sw nw)
        { numCmpRaw mem next with
          next := next + 776 + 776,
          mem := writeBytes mem (next + 776 + 768) (natToBytes nw.toNat 4),
          pc := "if.then", pre := some "entry" }) (.reg "%tobool.not.i") =
      some (.int 1 (evalICmp .eq nw 0)) :=
    evalOperand_reg_of _ _ _ _ (by simp [numCmpIfThenEnv])
  have h2 : step (numCmpCalls base) numCmpBody
      (stateAt (numCmpAfterEntryEnv v J eB next sw)
        { numCmpRaw mem next with
          next := next + 776 + 776, pc := "if.then", pre := some "entry" }) =
      .jump (stateAt (numCmpIfThenEnv v J eB next sw nw)
        { numCmpRaw mem next with
          next := next + 776 + 776,
          mem := writeBytes mem (next + 776 + 768) (natToBytes nw.toNat 4),
          pc := "if.then.i", pre := some "if.then" }) := by
    have hpc1 : (stateAt (numCmpAfterEntryEnv v J eB next sw)
        { numCmpRaw mem next with
          next := next + 776 + 776, pc := "if.then", pre := some "entry" }).pc = "if.then" := rfl
    unfold step execTerm
    rw [hpc1, numCmp_findBlock_ifThen]
    simp only [hcode1, hbit1, hnw0]
    rfl
  have hden3 := numCmp_ifThenI_denote_none (base := base)
    (env := numCmpIfThenEnv v J eB next sw nw)
    (s := { numCmpRaw mem next with
      next := next + 776 + 776,
      mem := writeBytes mem (next + 776 + 768) (natToBytes nw.toNat 4),
      pc := "if.then.i", pre := some "if.then" })
    hmem
    (by simp only [numCmpIfThenEnv, numCmpAfterEntryEnv]; block_lk)
    (by simp only [numCmpIfThenEnv, numCmpAfterEntryEnv, numCmpEntryEnv]; block_lk)
    (by simp only [numCmpIfThenEnv]; block_lk)
  have hpc2 : (stateAt (numCmpIfThenEnv v J eB next sw nw)
      { numCmpRaw mem next with
        next := next + 776 + 776,
        mem := writeBytes mem (next + 776 + 768) (natToBytes nw.toNat 4),
        pc := "if.then.i", pre := some "if.then" }).pc = "if.then.i" := rfl
  have h3 : step (numCmpCalls base) numCmpBody
      (stateAt (numCmpIfThenEnv v J eB next sw nw)
        { numCmpRaw mem next with
          next := next + 776 + 776,
          mem := writeBytes mem (next + 776 + 768) (natToBytes nw.toNat 4),
          pc := "if.then.i", pre := some "if.then" }) = .ub := by
    unfold step
    rw [hpc2, numCmp_findBlock_ifThenI]
    simp only [hden3]
  rw [show (3 : Nat) = 1 + 2 from rfl, numCmp_runFuel_jump h1 2]
  rw [show (2 : Nat) = 1 + 1 from rfl, numCmp_runFuel_jump h2 1]
  rw [show (1 : Nat) = 0 + 1 from rfl, runFuel.eq_2, h3]

/-! ### The body's answer, and why it is not the arm

`numCmpRunAnswer` is the body's answer at the arguments the walk passes; the
first theorem below is that it is *nothing* wherever the fortified copy is
unanswered, so a selection that adds `stk_cmp` to the callee half and nothing
else does not close the loop's site. -/

/-- A run's outcome as the call's answer. -/
def numCmpOptionOutcome : Option Outcome → Nat → Option CallOutcome
  | some (.ret (some v) m), next => some { ret := v, mem := m, next := next }
  | _, _ => none

/-- The body's answer, run from the selection's entry state. -/
def numCmpRunAnswer (base : Calls) (v : Nat) (J eB : BitVec 64) (mem : Mem)
    (next : Nat) : Option CallOutcome :=
  numCmpOptionOutcome
    (runFuel (numCmpCalls base) 3 numCmpBody
      (numCmpEntryState v J.toNat eB.toNat mem next)) next

/-- **The body answers nothing at the loop's own state.**  With the flag set and
the count nonzero — which is what the epilogue's carried value has — the run
reaches the fortified copy and stops, so the answer the selection would install
is `none`. -/
theorem numCmpRunAnswer_none (base : Calls) (v : Nat) (J eB : BitVec 64)
    (mem : Mem) (next : Nat) (sw nw : BitVec 32)
    (hsw : readBytes mem (v + 1560) 4 = some (natToBytes sw.toNat 4))
    (hnw : readBytes mem (v + 1544) 4 = some (natToBytes nw.toNat 4))
    (hsw0 : evalICmp .eq sw 0 = 0) (hnw0 : evalICmp .eq nw 0 = 0)
    (hmem : ∀ (vs : List Value) (m : Mem) (n : Nat),
      base "__memcpy_chk" vs m n = none) :
    numCmpRunAnswer base v J eB mem next = none := by
  simp only [numCmpRunAnswer,
    numCmp_run_ub base v J.toNat eB.toNat mem next sw nw hsw hnw hsw0 hnw0 hmem,
    numCmpOptionOutcome]

/-- The arguments the walk passes, decoded: the pointer and the two `uint64_t`
words.  A bare pattern match, so the arm's equation is the match's own. -/
def numCmpAnswer (base : Calls) (args : List Value) (mem : Mem) (next : Nat) :
    Option CallOutcome :=
  match args with
  | [.ptr v, .int 64 J, .int 64 eB] => numCmpRunAnswer base v J eB mem next
  | _ => none

/-- The walk's selection with `stk_cmp` answered by its pinned body's run. -/
def numCmpBodyCalls (base : Calls) : Calls :=
  fun callee args mem next =>
    if callee = "stk_cmp" then numCmpAnswer base args mem next
    else base callee args mem next

/-- **Adding `stk_cmp` to the selection does not answer it.**  At any base that
leaves `__memcpy_chk` unanswered, the answered `stk_cmp` answers nothing at the
loop's state, so the site's `ub` is not replaced by a model. -/
theorem numCmpBodyCalls_none (base : Calls) (v : Nat) (J eB : BitVec 64)
    (mem : Mem) (next : Nat) (sw nw : BitVec 32)
    (hsw : readBytes mem (v + 1560) 4 = some (natToBytes sw.toNat 4))
    (hnw : readBytes mem (v + 1544) 4 = some (natToBytes nw.toNat 4))
    (hsw0 : evalICmp .eq sw 0 = 0) (hnw0 : evalICmp .eq nw 0 = 0)
    (hmem : ∀ (vs : List Value) (m : Mem) (n : Nat),
      base "__memcpy_chk" vs m n = none) :
    numCmpBodyCalls base "stk_cmp" [.ptr v, .int 64 J, .int 64 eB] mem next = none := by
  unfold numCmpBodyCalls numCmpAnswer
  rw [if_pos rfl]
  exact numCmpRunAnswer_none base v J eB mem next sw nw hsw hnw hsw0 hnw0 hmem

/-- The release selection leaves the fortified copy unanswered: it answers the
conversion's three callees, the lifetime markers, `memset` and the trap, and
every other symbol is `noCalls`'. -/
theorem stage2NumFastCalls_memcpy (epow : Int → Option EPow) (vs : List Value)
    (mem : Mem) (next : Nat) :
    stage2NumFastCalls epow "__memcpy_chk" vs mem next = none := by
  simp only [stage2NumFastCalls, numFastCalls, s2HelperCalls, JsonStage2IR.stage2Calls]
  rfl

/-- **The release selection still fails with `stk_cmp` answered.**  The body's
answer is `none` there too, because the symbol it stops at is the fifth one. -/
theorem numCmpBodyCalls_stage2_none (epow : Int → Option EPow) (v : Nat)
    (J eB : BitVec 64) (mem : Mem) (next : Nat) (sw nw : BitVec 32)
    (hsw : readBytes mem (v + 1560) 4 = some (natToBytes sw.toNat 4))
    (hnw : readBytes mem (v + 1544) 4 = some (natToBytes nw.toNat 4))
    (hsw0 : evalICmp .eq sw 0 = 0) (hnw0 : evalICmp .eq nw 0 = 0) :
    numCmpBodyCalls (stage2NumFastCalls epow) "stk_cmp"
      [.ptr v, .int 64 J, .int 64 eB] mem next = none :=
  numCmpBodyCalls_none (stage2NumFastCalls epow) v J eB mem next sw nw hsw hnw hsw0 hnw0
    (fun vs m n => stage2NumFastCalls_memcpy epow vs m n)

/-! ### The restated boundary

The epilogue's boundary now names the body's own first answer as well: the
selection has to answer `stk_cmp` *and* the fortified copy.  What the answered
boundary still carries is named at the end: the loop's entry state, whose word
and cells are read from the digits array and the staged window. -/

/-- The selection answers the fortified copy. -/
def FbMemcpyAnswered (calls : Calls) : Prop :=
  ∀ (vs : List Value) (mem : Mem) (next : Nat),
    ∃ r : CallOutcome, calls "__memcpy_chk" vs mem next = some r

/-- The epilogue's boundary with the fifth answer added. -/
def FbEpilogueAnsweredMem (calls : Calls) (d : Decimal) (digA out J : Nat) : Prop :=
  FbEpilogueAnswered calls d digA out J ∧ FbMemcpyAnswered calls

/-- The release selection does not answer the fortified copy. -/
theorem stage2NumFastCalls_not_memcpyAnswered (epow : Int → Option EPow) :
    ¬ FbMemcpyAnswered (stage2NumFastCalls epow) := by
  intro h
  obtain ⟨r, hr⟩ := h [] [] 0
  rw [stage2NumFastCalls_memcpy] at hr
  cases hr

/-- The release selection is not the boundary even with `stk_cmp` answered. -/
theorem fbEpilogueAnsweredMem_not_release (epow : Int → Option EPow)
    (d : Decimal) (digA out J : Nat) :
    ¬ FbEpilogueAnsweredMem (stage2NumFastCalls epow) d digA out J :=
  fun h => stage2NumFastCalls_not_memcpyAnswered epow h.2

/-- **The fallback's tail at the boundary with both answers.**  The conclusion is
`fb_tail_at`'s, at the clause the loop can be stated at once the callee and the
copy are answered. -/
theorem fb_tail_answeredMem {calls : Calls} {d : Decimal} {out err digA J : Nat}
    (hd : d.wellFormed)
    (hEpi : FbEpilogueAnsweredMem calls d digA out J)
    (hStart : NumFastFallback.FbStart291 calls digA)
    (e : State) (hpc : e.pc = "while.end253.i.i")
    (hword : NumFastTier3Ladder.t3DivExitWord e) (htie : FbEpilogueTie d e) :
    ∃ (o : CallOutcome) (r : CallOutcome),
      runFuel calls (J + 2) numFastBody (stateAt e.env e) =
        some (.ret (some o.ret) o.mem) ∧
      o.ret = .int 32 1 ∧
      o.next = r.next ∧
      o.mem = writeBytes r.mem out (wordBytes 8 (strtodSpec d).toBits) ∧
      UnchangedOutside r.mem o.mem [(out, 8), (err, 8)] :=
  fb_tail_answered hd hEpi.1 hStart e hpc hword htie

/-- The clause an answered selection still carries: the loop is stated at an
entry state whose carried word (`t3DivExitWord`) and cells (`FbEpilogueTie`) are
read from the digits array and the staged window.  Its producer is the scan's
read-back, not the callee half. -/
def FbLoopEntry (d : Decimal) : Prop :=
  ∃ e : State, e.pc = "while.end253.i.i" ∧
    NumFastTier3Ladder.t3DivExitWord e ∧ FbEpilogueTie d e

/-- **The tail at an entry state the producer supplies.**  Once the callee and
the copy are answered, the remaining obligation is a state at the loop's entry
with the carried word and the tie's cells — the memory-parametric clause — and
the run from it is `fb_tail_answeredMem`'s. -/
theorem fb_loopEntry_tail {calls : Calls} {d : Decimal} {out err digA J : Nat}
    (hd : d.wellFormed)
    (hEpi : FbEpilogueAnsweredMem calls d digA out J)
    (hStart : NumFastFallback.FbStart291 calls digA)
    (hEntry : FbLoopEntry d) :
    ∃ (e : State) (o r : CallOutcome),
      e.pc = "while.end253.i.i" ∧
      runFuel calls (J + 2) numFastBody (stateAt e.env e) =
        some (.ret (some o.ret) o.mem) ∧
      o.ret = .int 32 1 ∧
      o.next = r.next ∧
      o.mem = writeBytes r.mem out (wordBytes 8 (strtodSpec d).toBits) ∧
      UnchangedOutside r.mem o.mem [(out, 8), (err, 8)] := by
  obtain ⟨e, hpc, hword, htie⟩ := hEntry
  obtain ⟨o, r, hrun, hret, hnext, hmem, hunch⟩ :=
    fb_tail_answeredMem hd hEpi hStart e hpc hword htie
  exact ⟨e, o, r, hpc, hrun, hret, hnext, hmem, hunch⟩

/-! ### Axiom footprints

Pinned with `#guard_msgs` so the build checks the footprints rather than printing
them.  The instrument is `#print axioms`; a declaration proved with `sorry`
prints `sorryAx` under the same command, which is the control the tree records. -/

/-- info: 'LeanLLVM.Refinement.NumFastCalleeCmp.step_alloca_nxt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms step_alloca_nxt

/-- info: 'LeanLLVM.Refinement.NumFastCalleeCmp.denoteCode_callVoid2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms denoteCode_callVoid2

/-- info: 'LeanLLVM.Refinement.NumFastCalleeCmp.numCmp_entry_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms numCmp_entry_denote

/-- info: 'LeanLLVM.Refinement.NumFastCalleeCmp.numCmp_ifThen_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms numCmp_ifThen_denote

/-- info: 'LeanLLVM.Refinement.NumFastCalleeCmp.numCmp_run_ub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms numCmp_run_ub

/-- info: 'LeanLLVM.Refinement.NumFastCalleeCmp.numCmpRunAnswer_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms numCmpRunAnswer_none

/-- info: 'LeanLLVM.Refinement.NumFastCalleeCmp.numCmpBodyCalls_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms numCmpBodyCalls_none

/-- info: 'LeanLLVM.Refinement.NumFastCalleeCmp.stage2NumFastCalls_memcpy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2NumFastCalls_memcpy

/-- info: 'LeanLLVM.Refinement.NumFastCalleeCmp.fb_tail_answeredMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fb_tail_answeredMem

end NumFastCalleeCmp

end LeanLLVM.Refinement
