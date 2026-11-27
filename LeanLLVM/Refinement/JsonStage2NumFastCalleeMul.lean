/-
`stk_mul_u64`'s emitted body, pinned, and the multiply it computes.

`JsonNumFastAssumed`'s callee half names three out-of-line functions and their
models; `JsonStage2NumFastCalls` supplies the models (`numStkMulAnswer` for the
in-place multiply) and `JsonStage2NumFastCalleeD8` pins the first body and the
eight-digit test it computes.  This module is the second of the three: the body
`probes/install/ir/stage2.callee.stk_mul_u64.ll` captures, block by block, and
the run that carries it from the entry state to the selection's answer.

**What the body is.**  `kernel/json/stage2.c`'s `stk_mul_u64` multiplies a
`StkBn` — 96 `uint64_t` limbs and an `int` count at offset 768 — by a `uint64_t`
in place.  It calls `stk_mul_add`, which the emission inlines, so the captured
body is the carry chain itself: an unrolled loop whose iteration multiplies four
limbs, a residual loop for the count's low two bits, and a tail that appends the
final carry word.  Eleven blocks, seventy-seven instructions.

**What this module establishes.**  The pin, the environment, every block's arm
but the four-limb iteration's *composed* statement, and that iteration's four
limb steps:

* the pin — `stkMulSrc` is the fixture, `firstFunction` of it is `stkMulBody`
  block by block with a mutated-text control, and each block's instruction list
  is its own `def` with a `findBlock` theorem stated of the literal;
* the environment — the body executes no call, so every `Calls` is its
  environment, and each block's chain below is stated at an arbitrary one;
* the arms — each block's `denoteCode` at its pin and its `step`: the entry's
  count test, the preheader's unroll decisions, the two joins (`unr-lcssa` from
  the loop, whose members select registers, and `while.cond.preheader.i` from
  either exit), the residue iteration from its own head and from the join, the
  carry tail's two exits and the single `ret void`;
* the group iteration, one limb at a time — `for.body.i`'s leading `phi` run
  (`stkMulGroupPhisInstrs`), its four nine-instruction limb steps
  (`stkMulLimb0Instrs`–`stkMulLimb3Instrs`, each with its own `_denote`), the
  counter tail (`stkMulTailInstrs`), and the environment and state they compose
  to (`stkMulGroupEnv`, `stkMulGroupState`).  **The composed thirty-six-cell
  statement is not proved**; see below;
* the arithmetic the group iteration and the run consume — the fold's cons step
  and its concatenation (`stkMulFold_cons`, `stkMulFold_append`), and the memory
  facts a written limb prefix rests on (`readBytes_stkWriteLimbs_above`,
  `stkWriteLimbs_append`, `writeBytes_eq_self_of_readBytes`, `stkLimbState_read_above`,
  and the byte round trip).

**What remains, and its measured obstruction.**

* **The composed group statement.**  `stkMul_group_denote` — the four limb
  denotations composed with `JsonEntrySteps.denoteCode_append` into the
  thirty-six-cell statement — was written three ways and each exceeds the
  elaboration budget on `fn-mul2-01a21253`:
  - states as `?_` goals for the four split steps: 8,000,000 heartbeats
    exceeded at the first split's `whnf` (the `rw` solves the state metavariable
    by `isDefEq` against the whole nested term);
  - intermediate states named but `let`-shared: 8,000,000 exceeded and still
    running at 1,000 s; at 24,000,000 it did not finish in 1,000 s (the `let`
    unfolds into an exponentially larger term on each side of the check);
  - intermediate states named and every carry spelled out: 8,000,000 exceeded
    at `h0`'s statement-elaboration `whnf`; 24,000,000 still running at 1,170 s;
  - the limb lemmas taken untyped (`have h0 := …`): 8,000,000 exceeded, still
    running at 316 s.
  The limb steps themselves each elaborate in seconds, which is why the split is
  the right answer to the *whole-block* timeout (543 s and 614 s at 8,000,000
  heartbeats, two attempts, on `t3c-01a21253`); the composition is a second,
  separate cost.  The next attempt should compose at the `step` level (the block
  is one control step whatever its denotation costs) or split the block's
  denotation at a *block boundary* by giving the second half its own `def`, so
  no single declaration ever holds the nested state;
* **the two loop inductions** — `for.body.i`'s group loop (G iterations, entering
  with `%indvars.iv.i`/`%carry.029.i`/`%niter` selected from `for.body.i` or
  `for.body.lr.ph.i.new`) and `for.body.i.epil`'s residue loop (the count's low
  two bits), each a `∀ k, runFuel (G + k) … = runFuel k …` induction over the
  block's arm.  The arithmetic they need is the emitted `i128` words read as the
  model's `Nat` fold: the widened product and its carry addition do not wrap
  (both below `2 ^ 128`), so the truncation is `% 2 ^ 64` and the shift `/ 2 ^ 64`,
  and the carry bound `c < 2 ^ 64` is preserved by the emitted tail;
* **the composition** — `stkMul_run`, from the entry state to the `ret void` at
  fuel `n + 12`, with the count's two shapes (`0 < n < 4` through the short-count
  path, `4 ≤ n` through the group loop) and the carry tail's two exits.

The `poison` incomings `while.cond.preheader.i.unr-lcssa` binds on the
short-count edge are never read on either shape: the residue count there is
`n % 4 = n ≠ 0`, so the join's second member carries real values.

**Why the count is bounded by 96.**  `StkBn` is `uint64_t w[96]`; a count above
96 would put the limb writes over the count cell, where the body and the model
stop agreeing because the body does not rewrite an unchanged count while the
model does.  Below it the two write at disjoint addresses and the agreement is
literal — the same `Mem` list.

**What it is not.**  It is not the agreement theorem's `Calls` entry: the model's
`numStkMulAnswer` is `JsonStage2NumFastCalls`'s, and this module proves the body
computes it, not that the compiled program does.  Nothing here reads
`probes/install/ir/capture-stage2-callees.sh`'s compiler line: the fixture is the
text, and the pin is what the parser makes of it.
-/
import LeanLLVM.Refinement.JsonStage2HelperIR
import LeanLLVM.Refinement.JsonEntrySteps
import LeanLLVM.Refinement.JsonStage2NumFastCalls
import LeanLLVM.Refinement.BitLanes
import LeanLLVM.Memory

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval

/-! ### The fixture and the body -/

/-- The captured body, as `capture-stage2-callees.sh` writes it. -/
def stkMulSrc : String :=
  include_str "../../probes/install/ir/stage2.callee.stk_mul_u64.ll"

/-- `@stk_mul_u64`, as the fixture parses.  Generated from the parse by
`probes/install/ir/emit-callee-pins.lean`; the `#guard` below holds it to the
fixture. -/
def stkMulBody : Function :=
{ name := "stk_mul_u64",
  retTy := Ty.void,
  params := [("%a", Ty.ptr),
             ("%m", (Ty.int 64))],
  blocks := [
    { name := "entry",
      instrs := [
        Instr.gep "%n.i" (Ty.int 8) (Operand.reg "%a") (Operand.imm (Const.int 64 0x0000000000000300#64)),
        Instr.load "%0" (Ty.int 32) (Operand.reg "%n.i"),
        Instr.icmp "%cmp28.i" (IPred.sgt) 32 (Operand.reg "%0") (Operand.imm (Const.int 32 0x00000000#32))
      ],
      term := Term.condbr (Operand.reg "%cmp28.i") "for.body.lr.ph.i" "stk_mul_add.exit" },
    { name := "for.body.lr.ph.i",
      instrs := [
        Instr.zext "%conv3.i" 64 128 (Operand.reg "%m"),
        Instr.zext "%wide.trip.count.i" 32 64 (Operand.reg "%0"),
        Instr.binop "%xtraiter" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
        Instr.icmp "%1" (IPred.ult) 32 (Operand.reg "%0") (Operand.imm (Const.int 32 0x00000004#32))
      ],
      term := Term.condbr (Operand.reg "%1") "while.cond.preheader.i.unr-lcssa" "for.body.lr.ph.i.new" },
    { name := "for.body.lr.ph.i.new",
      instrs := [
        Instr.binop "%unroll_iter" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i") (Operand.imm (Const.int 64 0x000000007ffffffc#64))
      ],
      term := Term.br "for.body.i" },
    { name := "while.cond.preheader.i.unr-lcssa.loopexit",
      instrs := [
        Instr.trunc "%extract.t6" 128 64 (Operand.reg "%shr.i.3")
      ],
      term := Term.br "while.cond.preheader.i.unr-lcssa" },
    { name := "while.cond.preheader.i.unr-lcssa",
      instrs := [
        Instr.phi "%add4.i.lcssa.ph" (Ty.int 128) [("for.body.lr.ph.i", (Operand.imm Const.poison)),
                                       ("while.cond.preheader.i.unr-lcssa.loopexit", (Operand.reg "%add4.i.3"))],
        Instr.phi "%shr.i.lcssa.ph.off0" (Ty.int 64) [("for.body.lr.ph.i", (Operand.imm Const.poison)),
                                       ("while.cond.preheader.i.unr-lcssa.loopexit", (Operand.reg "%extract.t6"))],
        Instr.phi "%indvars.iv.i.unr" (Ty.int 64) [("for.body.lr.ph.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("while.cond.preheader.i.unr-lcssa.loopexit", (Operand.reg "%indvars.iv.next.i.3"))],
        Instr.phi "%carry.029.i.unr" (Ty.int 128) [("for.body.lr.ph.i", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
                                       ("while.cond.preheader.i.unr-lcssa.loopexit", (Operand.reg "%shr.i.3"))],
        Instr.icmp "%lcmp.mod.not" (IPred.eq) 64 (Operand.reg "%xtraiter") (Operand.imm (Const.int 64 0x0000000000000000#64))
      ],
      term := Term.condbr (Operand.reg "%lcmp.mod.not") "while.cond.preheader.i" "for.body.i.epil" },
    { name := "for.body.i.epil",
      instrs := [
        Instr.phi "%indvars.iv.i.epil" (Ty.int 64) [("for.body.i.epil", (Operand.reg "%indvars.iv.next.i.epil")),
                                       ("while.cond.preheader.i.unr-lcssa", (Operand.reg "%indvars.iv.i.unr"))],
        Instr.phi "%carry.029.i.epil" (Ty.int 128) [("for.body.i.epil", (Operand.reg "%shr.i.epil")),
                                       ("while.cond.preheader.i.unr-lcssa", (Operand.reg "%carry.029.i.unr"))],
        Instr.phi "%epil.iter" (Ty.int 64) [("for.body.i.epil", (Operand.reg "%epil.iter.next")),
                                       ("while.cond.preheader.i.unr-lcssa", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
        Instr.gep "%arrayidx.i.epil" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%indvars.iv.i.epil"),
        Instr.load "%2" (Ty.int 64) (Operand.reg "%arrayidx.i.epil"),
        Instr.zext "%conv2.i.epil" 64 128 (Operand.reg "%2"),
        Instr.binop "%mul.i.epil" (BinOp.mul) 128 (Operand.reg "%conv2.i.epil") (Operand.reg "%conv3.i"),
        Instr.binop "%add4.i.epil" (BinOp.add) 128 (Operand.reg "%mul.i.epil") (Operand.reg "%carry.029.i.epil"),
        Instr.trunc "%conv5.i.epil" 128 64 (Operand.reg "%add4.i.epil"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.epil") (Operand.reg "%arrayidx.i.epil"),
        Instr.binop "%shr.i.epil" (BinOp.lshr) 128 (Operand.reg "%add4.i.epil") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.epil" (BinOp.add) 64 (Operand.reg "%indvars.iv.i.epil") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.binop "%epil.iter.next" (BinOp.add) 64 (Operand.reg "%epil.iter") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.icmp "%epil.iter.cmp.not" (IPred.eq) 64 (Operand.reg "%epil.iter.next") (Operand.reg "%xtraiter")
      ],
      term := Term.condbr (Operand.reg "%epil.iter.cmp.not") "while.cond.preheader.i.epilog-lcssa" "for.body.i.epil" },
    { name := "while.cond.preheader.i.epilog-lcssa",
      instrs := [
        Instr.trunc "%extract.t5" 128 64 (Operand.reg "%shr.i.epil")
      ],
      term := Term.br "while.cond.preheader.i" },
    { name := "while.cond.preheader.i",
      instrs := [
        Instr.phi "%add4.i.lcssa" (Ty.int 128) [("while.cond.preheader.i.unr-lcssa", (Operand.reg "%add4.i.lcssa.ph")),
                                       ("while.cond.preheader.i.epilog-lcssa", (Operand.reg "%add4.i.epil"))],
        Instr.phi "%shr.i.lcssa.off0" (Ty.int 64) [("while.cond.preheader.i.unr-lcssa", (Operand.reg "%shr.i.lcssa.ph.off0")),
                                       ("while.cond.preheader.i.epilog-lcssa", (Operand.reg "%extract.t5"))],
        Instr.icmp "%tobool.not31.i" (IPred.ult) 128 (Operand.reg "%add4.i.lcssa") (Operand.imm (Const.int 128 0x00000000000000010000000000000000#128))
      ],
      term := Term.condbr (Operand.reg "%tobool.not31.i") "stk_mul_add.exit" "while.body.us.i" },
    { name := "while.body.us.i",
      instrs := [
        Instr.binop "%inc12.us.i" (BinOp.add) 32 (Operand.reg "%0") (Operand.imm (Const.int 32 0x00000001#32)),
        Instr.gep "%arrayidx14.us.i" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%wide.trip.count.i"),
        Instr.store (Ty.int 64) (Operand.reg "%shr.i.lcssa.off0") (Operand.reg "%arrayidx14.us.i"),
        Instr.store (Ty.int 32) (Operand.reg "%inc12.us.i") (Operand.reg "%n.i")
      ],
      term := Term.br "stk_mul_add.exit" },
    { name := "for.body.i",
      instrs := [
        Instr.phi "%indvars.iv.i" (Ty.int 64) [("for.body.lr.ph.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i", (Operand.reg "%indvars.iv.next.i.3"))],
        Instr.phi "%carry.029.i" (Ty.int 128) [("for.body.lr.ph.i.new", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
                                       ("for.body.i", (Operand.reg "%shr.i.3"))],
        Instr.phi "%niter" (Ty.int 64) [("for.body.lr.ph.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i", (Operand.reg "%niter.next.3"))],
        Instr.gep "%arrayidx.i" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%indvars.iv.i"),
        Instr.load "%3" (Ty.int 64) (Operand.reg "%arrayidx.i"),
        Instr.zext "%conv2.i" 64 128 (Operand.reg "%3"),
        Instr.binop "%mul.i" (BinOp.mul) 128 (Operand.reg "%conv2.i") (Operand.reg "%conv3.i"),
        Instr.binop "%add4.i" (BinOp.add) 128 (Operand.reg "%mul.i") (Operand.reg "%carry.029.i"),
        Instr.trunc "%conv5.i" 128 64 (Operand.reg "%add4.i"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i") (Operand.reg "%arrayidx.i"),
        Instr.binop "%shr.i" (BinOp.lshr) 128 (Operand.reg "%add4.i") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i" (BinOp.or) 64 (Operand.reg "%indvars.iv.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
        Instr.gep "%arrayidx.i.1" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%indvars.iv.next.i"),
        Instr.load "%4" (Ty.int 64) (Operand.reg "%arrayidx.i.1"),
        Instr.zext "%conv2.i.1" 64 128 (Operand.reg "%4"),
        Instr.binop "%mul.i.1" (BinOp.mul) 128 (Operand.reg "%conv2.i.1") (Operand.reg "%conv3.i"),
        Instr.binop "%add4.i.1" (BinOp.add) 128 (Operand.reg "%mul.i.1") (Operand.reg "%shr.i"),
        Instr.trunc "%conv5.i.1" 128 64 (Operand.reg "%add4.i.1"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.1") (Operand.reg "%arrayidx.i.1"),
        Instr.binop "%shr.i.1" (BinOp.lshr) 128 (Operand.reg "%add4.i.1") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.1" (BinOp.or) 64 (Operand.reg "%indvars.iv.i") (Operand.imm (Const.int 64 0x0000000000000002#64)),
        Instr.gep "%arrayidx.i.2" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%indvars.iv.next.i.1"),
        Instr.load "%5" (Ty.int 64) (Operand.reg "%arrayidx.i.2"),
        Instr.zext "%conv2.i.2" 64 128 (Operand.reg "%5"),
        Instr.binop "%mul.i.2" (BinOp.mul) 128 (Operand.reg "%conv2.i.2") (Operand.reg "%conv3.i"),
        Instr.binop "%add4.i.2" (BinOp.add) 128 (Operand.reg "%mul.i.2") (Operand.reg "%shr.i.1"),
        Instr.trunc "%conv5.i.2" 128 64 (Operand.reg "%add4.i.2"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.2") (Operand.reg "%arrayidx.i.2"),
        Instr.binop "%shr.i.2" (BinOp.lshr) 128 (Operand.reg "%add4.i.2") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.2" (BinOp.or) 64 (Operand.reg "%indvars.iv.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
        Instr.gep "%arrayidx.i.3" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%indvars.iv.next.i.2"),
        Instr.load "%6" (Ty.int 64) (Operand.reg "%arrayidx.i.3"),
        Instr.zext "%conv2.i.3" 64 128 (Operand.reg "%6"),
        Instr.binop "%mul.i.3" (BinOp.mul) 128 (Operand.reg "%conv2.i.3") (Operand.reg "%conv3.i"),
        Instr.binop "%add4.i.3" (BinOp.add) 128 (Operand.reg "%mul.i.3") (Operand.reg "%shr.i.2"),
        Instr.trunc "%conv5.i.3" 128 64 (Operand.reg "%add4.i.3"),
        Instr.store (Ty.int 64) (Operand.reg "%conv5.i.3") (Operand.reg "%arrayidx.i.3"),
        Instr.binop "%shr.i.3" (BinOp.lshr) 128 (Operand.reg "%add4.i.3") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
        Instr.binop "%indvars.iv.next.i.3" (BinOp.add) 64 (Operand.reg "%indvars.iv.i") (Operand.imm (Const.int 64 0x0000000000000004#64)),
        Instr.binop "%niter.next.3" (BinOp.add) 64 (Operand.reg "%niter") (Operand.imm (Const.int 64 0x0000000000000004#64)),
        Instr.icmp "%niter.ncmp.3" (IPred.eq) 64 (Operand.reg "%niter.next.3") (Operand.reg "%unroll_iter")
      ],
      term := Term.condbr (Operand.reg "%niter.ncmp.3") "while.cond.preheader.i.unr-lcssa.loopexit" "for.body.i" },
    { name := "stk_mul_add.exit",
      instrs := [
      ],
      term := Term.ret Ty.void none }] }

/- The pin: the fixture parses to the literal above. -/
#guard decide (firstFunction stkMulSrc = some stkMulBody)

/- The control: the same fixture with the unroll mask changed parses, and it is
not the pinned body, so the equality above is about the text rather than about a
search that would accept anything. -/
def stkMulSrcMutated : String := stkMulSrc.replace ", 2147483644" ", 2147483643"

#guard parses stkMulSrcMutated
#guard decide (firstFunction stkMulSrcMutated ≠ some stkMulBody)

/- The shape `stage2.callees.tsv` records: eleven blocks, seventy-seven parsed
instructions, two parameters. -/
#guard decide
  ((stkMulBody.name, stkMulBody.blocks.length,
      (stkMulBody.blocks.flatMap (·.instrs)).length, stkMulBody.params.length) =
    ("stk_mul_u64", 11, 77, 2))

/-- The environment: the body executes no call, so it consults no `Calls`.  Every
step below is stated at an arbitrary one. -/
def stkMulCalls : Calls := noCalls

#guard (stkMulBody.blocks.flatMap (·.instrs)).all
  (fun i => match i with
    | .call .. => false
    | .callVoid .. => false
    | _ => true)

/-! ### The block pins

Each block's instruction list is the literal's own, and `findBlock` is stated of
it so a proof below reads the block rather than re-finding it by name. -/

def stkMulEntryInstrs : List Instr :=
  [
    Instr.gep "%n.i" (Ty.int 8) (Operand.reg "%a") (Operand.imm (Const.int 64 0x0000000000000300#64)),
    Instr.load "%0" (Ty.int 32) (Operand.reg "%n.i"),
    Instr.icmp "%cmp28.i" (IPred.sgt) 32 (Operand.reg "%0") (Operand.imm (Const.int 32 0x00000000#32))]

def stkMulForBodyLrPhIInstrs : List Instr :=
  [
    Instr.zext "%conv3.i" 64 128 (Operand.reg "%m"),
    Instr.zext "%wide.trip.count.i" 32 64 (Operand.reg "%0"),
    Instr.binop "%xtraiter" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
    Instr.icmp "%1" (IPred.ult) 32 (Operand.reg "%0") (Operand.imm (Const.int 32 0x0000000000000004#32))]

def stkMulForBodyLrPhINewInstrs : List Instr :=
  [
    Instr.binop "%unroll_iter" (BinOp.and) 64 (Operand.reg "%wide.trip.count.i") (Operand.imm (Const.int 64 0x000000007ffffffc#64))]

def stkMulWhileCondPreheaderIUnrLcssaLoopexitInstrs : List Instr :=
  [
    Instr.trunc "%extract.t6" 128 64 (Operand.reg "%shr.i.3")]

def stkMulWhileCondPreheaderIUnrLcssaInstrs : List Instr :=
  [
    Instr.phi "%add4.i.lcssa.ph" (Ty.int 128) [("for.body.lr.ph.i", (Operand.imm Const.poison)),
                                       ("while.cond.preheader.i.unr-lcssa.loopexit", (Operand.reg "%add4.i.3"))],
    Instr.phi "%shr.i.lcssa.ph.off0" (Ty.int 64) [("for.body.lr.ph.i", (Operand.imm Const.poison)),
                                       ("while.cond.preheader.i.unr-lcssa.loopexit", (Operand.reg "%extract.t6"))],
    Instr.phi "%indvars.iv.i.unr" (Ty.int 64) [("for.body.lr.ph.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("while.cond.preheader.i.unr-lcssa.loopexit", (Operand.reg "%indvars.iv.next.i.3"))],
    Instr.phi "%carry.029.i.unr" (Ty.int 128) [("for.body.lr.ph.i", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
                                       ("while.cond.preheader.i.unr-lcssa.loopexit", (Operand.reg "%shr.i.3"))],
    Instr.icmp "%lcmp.mod.not" (IPred.eq) 64 (Operand.reg "%xtraiter") (Operand.imm (Const.int 64 0x0000000000000000#64))]

def stkMulForBodyIEpilInstrs : List Instr :=
  [
    Instr.phi "%indvars.iv.i.epil" (Ty.int 64) [("for.body.i.epil", (Operand.reg "%indvars.iv.next.i.epil")),
                                       ("while.cond.preheader.i.unr-lcssa", (Operand.reg "%indvars.iv.i.unr"))],
    Instr.phi "%carry.029.i.epil" (Ty.int 128) [("for.body.i.epil", (Operand.reg "%shr.i.epil")),
                                       ("while.cond.preheader.i.unr-lcssa", (Operand.reg "%carry.029.i.unr"))],
    Instr.phi "%epil.iter" (Ty.int 64) [("for.body.i.epil", (Operand.reg "%epil.iter.next")),
                                       ("while.cond.preheader.i.unr-lcssa", (Operand.imm (Const.int 64 0x0000000000000000#64)))],
    Instr.gep "%arrayidx.i.epil" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%indvars.iv.i.epil"),
    Instr.load "%2" (Ty.int 64) (Operand.reg "%arrayidx.i.epil"),
    Instr.zext "%conv2.i.epil" 64 128 (Operand.reg "%2"),
    Instr.binop "%mul.i.epil" (BinOp.mul) 128 (Operand.reg "%conv2.i.epil") (Operand.reg "%conv3.i"),
    Instr.binop "%add4.i.epil" (BinOp.add) 128 (Operand.reg "%mul.i.epil") (Operand.reg "%carry.029.i.epil"),
    Instr.trunc "%conv5.i.epil" 128 64 (Operand.reg "%add4.i.epil"),
    Instr.store (Ty.int 64) (Operand.reg "%conv5.i.epil") (Operand.reg "%arrayidx.i.epil"),
    Instr.binop "%shr.i.epil" (BinOp.lshr) 128 (Operand.reg "%add4.i.epil") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
    Instr.binop "%indvars.iv.next.i.epil" (BinOp.add) 64 (Operand.reg "%indvars.iv.i.epil") (Operand.imm (Const.int 64 0x0000000000000001#64)),
    Instr.binop "%epil.iter.next" (BinOp.add) 64 (Operand.reg "%epil.iter") (Operand.imm (Const.int 64 0x0000000000000001#64)),
    Instr.icmp "%epil.iter.cmp.not" (IPred.eq) 64 (Operand.reg "%epil.iter.next") (Operand.reg "%xtraiter")]

def stkMulWhileCondPreheaderIEpilogLcssaInstrs : List Instr :=
  [
    Instr.trunc "%extract.t5" 128 64 (Operand.reg "%shr.i.epil")]

def stkMulWhileCondPreheaderIInstrs : List Instr :=
  [
    Instr.phi "%add4.i.lcssa" (Ty.int 128) [("while.cond.preheader.i.unr-lcssa", (Operand.reg "%add4.i.lcssa.ph")),
                                       ("while.cond.preheader.i.epilog-lcssa", (Operand.reg "%add4.i.epil"))],
    Instr.phi "%shr.i.lcssa.off0" (Ty.int 64) [("while.cond.preheader.i.unr-lcssa", (Operand.reg "%shr.i.lcssa.ph.off0")),
                                       ("while.cond.preheader.i.epilog-lcssa", (Operand.reg "%extract.t5"))],
    Instr.icmp "%tobool.not31.i" (IPred.ult) 128 (Operand.reg "%add4.i.lcssa") (Operand.imm (Const.int 128 0x00000000000000010000000000000000#128))]

def stkMulWhileBodyUsIInstrs : List Instr :=
  [
    Instr.binop "%inc12.us.i" (BinOp.add) 32 (Operand.reg "%0") (Operand.imm (Const.int 32 0x0000000000000001#32)),
    Instr.gep "%arrayidx14.us.i" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%wide.trip.count.i"),
    Instr.store (Ty.int 64) (Operand.reg "%shr.i.lcssa.off0") (Operand.reg "%arrayidx14.us.i"),
    Instr.store (Ty.int 32) (Operand.reg "%inc12.us.i") (Operand.reg "%n.i")]

def stkMulForBodyIInstrs : List Instr :=
  [
    Instr.phi "%indvars.iv.i" (Ty.int 64) [("for.body.lr.ph.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i", (Operand.reg "%indvars.iv.next.i.3"))],
    Instr.phi "%carry.029.i" (Ty.int 128) [("for.body.lr.ph.i.new", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
                                       ("for.body.i", (Operand.reg "%shr.i.3"))],
    Instr.phi "%niter" (Ty.int 64) [("for.body.lr.ph.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                       ("for.body.i", (Operand.reg "%niter.next.3"))],
    Instr.gep "%arrayidx.i" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%indvars.iv.i"),
    Instr.load "%3" (Ty.int 64) (Operand.reg "%arrayidx.i"),
    Instr.zext "%conv2.i" 64 128 (Operand.reg "%3"),
    Instr.binop "%mul.i" (BinOp.mul) 128 (Operand.reg "%conv2.i") (Operand.reg "%conv3.i"),
    Instr.binop "%add4.i" (BinOp.add) 128 (Operand.reg "%mul.i") (Operand.reg "%carry.029.i"),
    Instr.trunc "%conv5.i" 128 64 (Operand.reg "%add4.i"),
    Instr.store (Ty.int 64) (Operand.reg "%conv5.i") (Operand.reg "%arrayidx.i"),
    Instr.binop "%shr.i" (BinOp.lshr) 128 (Operand.reg "%add4.i") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
    Instr.binop "%indvars.iv.next.i" (BinOp.or) 64 (Operand.reg "%indvars.iv.i") (Operand.imm (Const.int 64 0x0000000000000001#64)),
    Instr.gep "%arrayidx.i.1" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%indvars.iv.next.i"),
    Instr.load "%4" (Ty.int 64) (Operand.reg "%arrayidx.i.1"),
    Instr.zext "%conv2.i.1" 64 128 (Operand.reg "%4"),
    Instr.binop "%mul.i.1" (BinOp.mul) 128 (Operand.reg "%conv2.i.1") (Operand.reg "%conv3.i"),
    Instr.binop "%add4.i.1" (BinOp.add) 128 (Operand.reg "%mul.i.1") (Operand.reg "%shr.i"),
    Instr.trunc "%conv5.i.1" 128 64 (Operand.reg "%add4.i.1"),
    Instr.store (Ty.int 64) (Operand.reg "%conv5.i.1") (Operand.reg "%arrayidx.i.1"),
    Instr.binop "%shr.i.1" (BinOp.lshr) 128 (Operand.reg "%add4.i.1") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
    Instr.binop "%indvars.iv.next.i.1" (BinOp.or) 64 (Operand.reg "%indvars.iv.i") (Operand.imm (Const.int 64 0x0000000000000002#64)),
    Instr.gep "%arrayidx.i.2" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%indvars.iv.next.i.1"),
    Instr.load "%5" (Ty.int 64) (Operand.reg "%arrayidx.i.2"),
    Instr.zext "%conv2.i.2" 64 128 (Operand.reg "%5"),
    Instr.binop "%mul.i.2" (BinOp.mul) 128 (Operand.reg "%conv2.i.2") (Operand.reg "%conv3.i"),
    Instr.binop "%add4.i.2" (BinOp.add) 128 (Operand.reg "%mul.i.2") (Operand.reg "%shr.i.1"),
    Instr.trunc "%conv5.i.2" 128 64 (Operand.reg "%add4.i.2"),
    Instr.store (Ty.int 64) (Operand.reg "%conv5.i.2") (Operand.reg "%arrayidx.i.2"),
    Instr.binop "%shr.i.2" (BinOp.lshr) 128 (Operand.reg "%add4.i.2") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
    Instr.binop "%indvars.iv.next.i.2" (BinOp.or) 64 (Operand.reg "%indvars.iv.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
    Instr.gep "%arrayidx.i.3" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%indvars.iv.next.i.2"),
    Instr.load "%6" (Ty.int 64) (Operand.reg "%arrayidx.i.3"),
    Instr.zext "%conv2.i.3" 64 128 (Operand.reg "%6"),
    Instr.binop "%mul.i.3" (BinOp.mul) 128 (Operand.reg "%conv2.i.3") (Operand.reg "%conv3.i"),
    Instr.binop "%add4.i.3" (BinOp.add) 128 (Operand.reg "%mul.i.3") (Operand.reg "%shr.i.2"),
    Instr.trunc "%conv5.i.3" 128 64 (Operand.reg "%add4.i.3"),
    Instr.store (Ty.int 64) (Operand.reg "%conv5.i.3") (Operand.reg "%arrayidx.i.3"),
    Instr.binop "%shr.i.3" (BinOp.lshr) 128 (Operand.reg "%add4.i.3") (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
    Instr.binop "%indvars.iv.next.i.3" (BinOp.add) 64 (Operand.reg "%indvars.iv.i") (Operand.imm (Const.int 64 0x0000000000000004#64)),
    Instr.binop "%niter.next.3" (BinOp.add) 64 (Operand.reg "%niter") (Operand.imm (Const.int 64 0x0000000000000004#64)),
    Instr.icmp "%niter.ncmp.3" (IPred.eq) 64 (Operand.reg "%niter.next.3") (Operand.reg "%unroll_iter")]

def stkMulStkMulAddExitInstrs : List Instr :=
  [
]

theorem stkMul_findBlock_entry :
    stkMulBody.findBlock "entry" = some ⟨"entry", stkMulEntryInstrs, Term.condbr (Operand.reg "%cmp28.i") "for.body.lr.ph.i" "stk_mul_add.exit"⟩ := by decide

theorem stkMul_findBlock_for_body_lr_ph_i :
    stkMulBody.findBlock "for.body.lr.ph.i" = some ⟨"for.body.lr.ph.i", stkMulForBodyLrPhIInstrs, Term.condbr (Operand.reg "%1") "while.cond.preheader.i.unr-lcssa" "for.body.lr.ph.i.new"⟩ := by decide

theorem stkMul_findBlock_for_body_lr_ph_i_new :
    stkMulBody.findBlock "for.body.lr.ph.i.new" = some ⟨"for.body.lr.ph.i.new", stkMulForBodyLrPhINewInstrs, Term.br "for.body.i"⟩ := by decide

theorem stkMul_findBlock_while_cond_preheader_i_unr_lcssa_loopexit :
    stkMulBody.findBlock "while.cond.preheader.i.unr-lcssa.loopexit" = some ⟨"while.cond.preheader.i.unr-lcssa.loopexit", stkMulWhileCondPreheaderIUnrLcssaLoopexitInstrs, Term.br "while.cond.preheader.i.unr-lcssa"⟩ := by decide

theorem stkMul_findBlock_while_cond_preheader_i_unr_lcssa :
    stkMulBody.findBlock "while.cond.preheader.i.unr-lcssa" = some ⟨"while.cond.preheader.i.unr-lcssa", stkMulWhileCondPreheaderIUnrLcssaInstrs, Term.condbr (Operand.reg "%lcmp.mod.not") "while.cond.preheader.i" "for.body.i.epil"⟩ := by decide

theorem stkMul_findBlock_for_body_i_epil :
    stkMulBody.findBlock "for.body.i.epil" = some ⟨"for.body.i.epil", stkMulForBodyIEpilInstrs, Term.condbr (Operand.reg "%epil.iter.cmp.not") "while.cond.preheader.i.epilog-lcssa" "for.body.i.epil"⟩ := by decide

theorem stkMul_findBlock_while_cond_preheader_i_epilog_lcssa :
    stkMulBody.findBlock "while.cond.preheader.i.epilog-lcssa" = some ⟨"while.cond.preheader.i.epilog-lcssa", stkMulWhileCondPreheaderIEpilogLcssaInstrs, Term.br "while.cond.preheader.i"⟩ := by decide

theorem stkMul_findBlock_while_cond_preheader_i :
    stkMulBody.findBlock "while.cond.preheader.i" = some ⟨"while.cond.preheader.i", stkMulWhileCondPreheaderIInstrs, Term.condbr (Operand.reg "%tobool.not31.i") "stk_mul_add.exit" "while.body.us.i"⟩ := by decide

theorem stkMul_findBlock_while_body_us_i :
    stkMulBody.findBlock "while.body.us.i" = some ⟨"while.body.us.i", stkMulWhileBodyUsIInstrs, Term.br "stk_mul_add.exit"⟩ := by decide

theorem stkMul_findBlock_for_body_i :
    stkMulBody.findBlock "for.body.i" = some ⟨"for.body.i", stkMulForBodyIInstrs, Term.condbr (Operand.reg "%niter.ncmp.3") "while.cond.preheader.i.unr-lcssa.loopexit" "for.body.i"⟩ := by decide

theorem stkMul_findBlock_stk_mul_add_exit :
    stkMulBody.findBlock "stk_mul_add.exit" = some ⟨"stk_mul_add.exit", stkMulStkMulAddExitInstrs, Term.ret Ty.void none⟩ := by decide

/-! ### The instruction vocabulary this body needs

`BlockEval`'s steps are at `i64`; the multiply uses `i32` and `i128` operands too,
so the four shapes it adds are the width-generic `binop`, the width-generic
`icmp`, the `i32` load and store, and the two `getelementptr` forms whose element
type is `i64` (the limb index) or whose offset is a literal (`i8` at 768). -/

/-- `%d = op iW %a, %b`: the operation's own result, at the width the operands
carry.  The operation's result is a parameter because the body's `mul` and `add`
are `i128` and its `or`/`and` are `i64`; the caller names it, and `block_eval`
lets the block's statement fix it. -/
theorem step_binop_reg_w (calls : Calls) (env : Env) (s : State) (d a b : String)
    (op : BinOp) (w : Nat) {x y z : BitVec w}
    (ha : lookupName env a = some (.int w x))
    (hb : lookupName env b = some (.int w y))
    (hz : evalBinop op x y = some z) :
    evalInstr calls (stateAt env s) (.binop d op w (.reg a) (.reg b)) =
      some (stateAt ((d, .int w z) :: env) s) := by
  have hr : evalBinopNat op w x.toNat y.toNat = some z.toNat := by
    simp only [evalBinopNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, hz, Option.map_some]
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using JsonS1MasksIR.evalInstr_binop (calls := calls) (s := stateAt env s)
      (d := d) (op := op) (w := w)
      (ha := evalOperand_reg_of env s a (.int w x) ha)
      (hb := evalOperand_reg_of env s b (.int w y) hb) (hr := hr)

/-- `%d = op iW %a, <c>` at any width. -/
theorem step_binop_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (op : BinOp) (w : Nat) {x c z : BitVec w}
    (ha : lookupName env a = some (.int w x))
    (hz : evalBinop op x c = some z) :
    evalInstr calls (stateAt env s) (.binop d op w (.reg a) (.imm (.int w c))) =
      some (stateAt ((d, .int w z) :: env) s) := by
  have hr : evalBinopNat op w x.toNat c.toNat = some z.toNat := by
    simp only [evalBinopNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, hz, Option.map_some]
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using JsonS1MasksIR.evalInstr_binop (calls := calls) (s := stateAt env s)
      (d := d) (op := op) (w := w)
      (ha := evalOperand_reg_of env s a (.int w x) ha)
      (hb := evalOperand_lit_of _ w c) (hr := hr)

/-- `%d = icmp <pred> iW %a, %b` at any width. -/
theorem step_icmp_reg_w (calls : Calls) (env : Env) (s : State) (d a b : String)
    (pred : IPred) (w : Nat) {x y : BitVec w}
    (ha : lookupName env a = some (.int w x))
    (hb : lookupName env b = some (.int w y)) :
    evalInstr calls (stateAt env s) (.icmp d pred w (.reg a) (.reg b)) =
      some (stateAt ((d, .int 1 (evalICmp pred x y)) :: env) s) := by
  rw [JsonS1MasksIR.evalInstr_icmp (s := stateAt env s)
    (ha := evalOperand_reg_of env s a (.int w x) ha)
    (hb := evalOperand_reg_of env s b (.int w y) hb)]
  rfl

/-- `%d = icmp <pred> iW %a, <c>` at any width. -/
theorem step_icmp_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (pred : IPred) (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) :
    evalInstr calls (stateAt env s) (.icmp d pred w (.reg a) (.imm (.int w c))) =
      some (stateAt ((d, .int 1 (evalICmp pred x c)) :: env) s) := by
  rw [JsonS1MasksIR.evalInstr_icmp (s := stateAt env s)
    (ha := evalOperand_reg_of env s a (.int w x) ha)
    (hb := evalOperand_lit_of _ w c)]
  rfl

/-- A 32-bit load at a readable four-byte range. -/
theorem step_load32 (calls : Calls) (env : Env) (s : State) (d p : String)
    {a : Nat} {v : BitVec 32}
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 4 = some (natToBytes v.toNat 4)) :
    evalInstr calls (stateAt env s) (.load d (.int 32) (.reg p)) =
      some (stateAt ((d, .int 32 v) :: env) s) := by
  have hb : bytesToNat (natToBytes v.toNat 4) = v.toNat := by
    rw [natToBytes_toNat, show (256 : Nat) ^ 4 = 2 ^ 32 from by decide]
    exact Nat.mod_eq_of_lt v.isLt
  have hv' : loadValue s.mem (.int 32) a = some (.int 32 v) := by
    simp only [loadValue, show (32 + 7) / 8 = 4 from rfl,
      show (32 = 0) = False from by decide, ite_false, hv, hb,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [JsonS1MasksIR.evalInstr_load (s := stateAt env s)
    (hp := evalOperand_reg_of env s p (.ptr a) hp)
    (hv := by simpa only [stateAt] using hv')]
  simp [stateAt, State.bind]

/-- `store i32 %v, ptr %p`. -/
theorem step_store32 (calls : Calls) (env : Env) (s : State) (v p : String)
    {x : BitVec 32} {a : Nat}
    (hv : lookupName env v = some (.int 32 x))
    (hp : lookupName env p = some (.ptr a)) :
    evalInstr calls (stateAt env s) (.store (.int 32) (.reg v) (.reg p)) =
      some (stateAt env
        { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) }) := by
  rw [JsonS1MasksIR.evalInstr_store (s := stateAt env s) (vv := .int 32 x) (a := a)
    (s' := stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) })
    (hv := evalOperand_reg_of env s v (.int 32 x) hv)
    (hp := evalOperand_reg_of env s p (.ptr a) hp)]
  simp [storeValue, stateAt]

/-- A 64-bit index sign-extended to 64 bits is itself. -/
theorem stk_signExtend_self_toNat (x : BitVec 64) : (x.signExtend 64).toNat = x.toNat := by
  rw [BitVec.signExtend_eq]

/-- `%d = getelementptr i64, ptr %base, i64 %off`: eight bytes per index step. -/
theorem step_gep_i64_reg (calls : Calls) (env : Env) (s : State) (d base off : String)
    {a : Nat} {idx : BitVec 64}
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 idx))
    (hpos : idx.toNat < 2 ^ 63) :
    evalInstr calls (stateAt env s) (.gep d (.int 64) (.reg base) (.reg off)) =
      some (stateAt ((d, .ptr (a + idx.toNat * (Ty.int 64).sizeBytes)) :: env) s) := by
  rw [evalInstr_gep (s := stateAt env s) (elemTy := .int 64)
    (hb := evalOperand_reg_of env s base (.ptr a) hb)
    (ho := evalOperand_reg_of env s off (.int 64 idx) ho)
    (hpos := by rw [stk_signExtend_self_toNat]; exact hpos)]
  simp only [stk_signExtend_self_toNat, stateAt, State.bind]

/-- `%d = getelementptr i8, ptr %base, i64 <c>`: one byte per index step, at a
literal offset. -/
theorem step_gep8_imm (calls : Calls) (env : Env) (s : State) (d base : String)
    {a : Nat} {c : BitVec 64} (hb : lookupName env base = some (.ptr a))
    (hc : c.toNat < 2 ^ 63) :
    evalInstr calls (stateAt env s) (.gep d (.int 8) (.reg base) (.imm (.int 64 c))) =
      some (stateAt ((d, .ptr (a + c.toNat)) :: env) s) := by
  rw [evalInstr_gep_i8 (s := stateAt env s) (w := 64) (n := c)
    (hb := evalOperand_reg_of env s base (.ptr a) hb)
    (ho := evalOperand_lit_of _ 64 c)
    (hpos := by rw [stk_signExtend_self_toNat]; exact hc)]
  simp only [stk_signExtend_self_toNat, Ty.sizeBytes, Nat.mul_one, stateAt, State.bind]

/-! ### The chain steps

One `denoteCode` step per wrapper above. -/

theorem denoteCode_binop_reg_w (calls : Calls) (env : Env) (s : State) (d a b : String)
    (op : BinOp) (w : Nat) {x y z : BitVec w}
    (ha : lookupName env a = some (.int w x))
    (hb : lookupName env b = some (.int w y))
    (hz : evalBinop op x y = some z) (is : List Instr) :
    denoteCode calls (.binop d op w (.reg a) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w z) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_binop_reg_w calls env s d a b op w ha hb hz)]

theorem denoteCode_binop_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (op : BinOp) (w : Nat) {x c z : BitVec w}
    (ha : lookupName env a = some (.int w x))
    (hz : evalBinop op x c = some z) (is : List Instr) :
    denoteCode calls (.binop d op w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w z) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_binop_imm_w calls env s d a op w ha hz)]

theorem denoteCode_icmp_reg_w (calls : Calls) (env : Env) (s : State) (d a b : String)
    (pred : IPred) (w : Nat) {x y : BitVec w}
    (ha : lookupName env a = some (.int w x))
    (hb : lookupName env b = some (.int w y)) (is : List Instr) :
    denoteCode calls (.icmp d pred w (.reg a) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp pred x y)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_icmp_reg_w calls env s d a b pred w ha hb)]

theorem denoteCode_icmp_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (pred : IPred) (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) (is : List Instr) :
    denoteCode calls (.icmp d pred w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp pred x c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_icmp_imm_w calls env s d a pred w ha)]

theorem denoteCode_load32 (calls : Calls) (env : Env) (s : State) (d p : String)
    {a : Nat} {v : BitVec 32}
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 4 = some (natToBytes v.toNat 4)) (is : List Instr) :
    denoteCode calls (.load d (.int 32) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 32 v) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_load32 calls env s d p hp hv)]

theorem denoteCode_store32 (calls : Calls) (env : Env) (s : State) (v p : String)
    {x : BitVec 32} {a : Nat}
    (hv : lookupName env v = some (.int 32 x))
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store (.int 32) (.reg v) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) }) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_store32 calls env s v p hv hp)]

theorem denoteCode_gep_i64_reg (calls : Calls) (env : Env) (s : State) (d base off : String)
    {a : Nat} {idx : BitVec 64}
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 idx))
    (hpos : idx.toNat < 2 ^ 63) (is : List Instr) :
    denoteCode calls (.gep d (.int 64) (.reg base) (.reg off) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt ((d, .ptr (a + idx.toNat * (Ty.int 64).sizeBytes)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _
    (step_gep_i64_reg calls env s d base off hb ho hpos)]

theorem denoteCode_gep8_imm (calls : Calls) (env : Env) (s : State) (d base : String)
    {a : Nat} {c : BitVec 64} (hb : lookupName env base = some (.ptr a))
    (hc : c.toNat < 2 ^ 63) (is : List Instr) :
    denoteCode calls (.gep d (.int 8) (.reg base) (.imm (.int 64 c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .ptr (a + c.toNat)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_gep8_imm calls env s d base hb hc)]

/-- One instruction of this body: the chain step whose shape matches.  It extends
`block_step` with the four shape families above and keeps its `phi` run. -/
macro "stk_block_step" : tactic => `(tactic|
  (first
   | block_step
   | rw [denoteCode_binop_reg_w _ _ _ _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_binop_imm_w _ _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_icmp_reg_w _ _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_icmp_imm_w _ _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_trunc _ _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_zext _ _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_gep_i64_reg _ _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_gep8_imm _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_gep8_reg _ _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_load64 _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_load32 _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_store64 _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_store32 _ _ _ _ _ ?_ ?_ _]
   | block_phi_run))

/-- Resolve a register read against one of the group's environment builders: the
builder is unfolded first, because a `lookupName` into a `def`-headed environment
never reduces.  (`block_lk` alone stops at the def's head — the closure of the
four-limb split's lesson, per limb.) -/
macro "stk_lk" : tactic => `(tactic|
  (first
   | assumption
   | (simp only [stkMulLimb0Env, stkMulLimb1Env, stkMulLimb2Env, stkMulLimb3Env,
        stkMulTailEnv]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      first
       | rw [lookupName_cons_self]
       | assumption
       | rfl)))

/-- A whole straight-line block of this body: every instruction's step, then the
side goals. -/
macro "stk_block_eval" : tactic => `(tactic|
  (repeat stk_block_step
   block_close
   all_goals (try decide)))

/-! ### The step at a pinned block

The three control shapes the body's blocks take: an unconditional jump, a branch
whose bit is known, and the `ret void`.  Each reads the block's own pin, so a
step lemma below never re-finds the block by name. -/

/-- A block ending in `br`: one jump to its target. -/
theorem stkMul_step_br {calls : Calls} {env env' : Env} {s : State}
    {instrs : List Instr} {block dest : String}
    (hpc : s.pc = block)
    (hfind : stkMulBody.findBlock block = some ⟨block, instrs, Term.br dest⟩)
    (hden : denoteCode calls instrs (stateAt env s) = some (stateAt env' s)) :
    step calls stkMulBody (stateAt env s) =
      .jump (stateAt env' { s with pc := dest, pre := some block }) := by
  have hrec : denoteCode calls instrs
      { env := env, mem := s.mem, next := s.next, pc := block, pre := s.pre } =
        some (stateAt env' s) := by
    rw [← hpc]
    exact hden
  have h1 : step calls stkMulBody (stateAt env s) =
      Ctrl.jump (State.mk env' s.mem s.next dest (some block)) := by
    simp only [stateAt, step, hpc, hfind, hrec, execTerm]
  simpa only [stateAt] using h1

/-- A block ending in a `condbr` whose bit is one. -/
theorem stkMul_step_condbr_one {calls : Calls} {env env' : Env} {s : State}
    {instrs : List Instr} {block t f c : String} {x : BitVec 1}
    (hpc : s.pc = block)
    (hfind : stkMulBody.findBlock block =
      some ⟨block, instrs, Term.condbr (Operand.reg c) t f⟩)
    (hden : denoteCode calls instrs (stateAt env s) = some (stateAt env' s))
    (hbit : evalOperand (State.mk env' s.mem s.next block s.pre) (.reg c) =
      some (.int 1 x)) (hx : x = 1) :
    step calls stkMulBody (stateAt env s) =
      .jump (stateAt env' { s with pc := t, pre := some block }) := by
  have hrec : denoteCode calls instrs
      { env := env, mem := s.mem, next := s.next, pc := block, pre := s.pre } =
        some (stateAt env' s) := by
    rw [← hpc]
    exact hden
  subst hx
  have h1 : step calls stkMulBody (stateAt env s) =
      Ctrl.jump (State.mk env' s.mem s.next t (some block)) := by
    simp only [stateAt, step, hpc, hfind, hrec, execTerm, hbit, if_true, if_false]
  simpa only [stateAt] using h1

/-- A block ending in a `condbr` whose bit is zero. -/
theorem stkMul_step_condbr_zero {calls : Calls} {env env' : Env} {s : State}
    {instrs : List Instr} {block t f c : String} {x : BitVec 1}
    (hpc : s.pc = block)
    (hfind : stkMulBody.findBlock block =
      some ⟨block, instrs, Term.condbr (Operand.reg c) t f⟩)
    (hden : denoteCode calls instrs (stateAt env s) = some (stateAt env' s))
    (hbit : evalOperand (State.mk env' s.mem s.next block s.pre) (.reg c) =
      some (.int 1 x)) (hx : x = 0) :
    step calls stkMulBody (stateAt env s) =
      .jump (stateAt env' { s with pc := f, pre := some block }) := by
  have hrec : denoteCode calls instrs
      { env := env, mem := s.mem, next := s.next, pc := block, pre := s.pre } =
        some (stateAt env' s) := by
    rw [← hpc]
    exact hden
  subst hx
  have h1 : step calls stkMulBody (stateAt env s) =
      Ctrl.jump (State.mk env' s.mem s.next f (some block)) := by
    simp only [stateAt, step, hpc, hfind, hrec, execTerm, hbit, if_true, if_false,
      if_neg (show ¬((0 : BitVec 1) = 1) from by decide)]
  simpa only [stateAt] using h1

/-- The `ret void` block: the run's outcome, and the memory it leaves. -/
theorem stkMul_step_ret {calls : Calls} {env : Env} {s : State}
    (hpc : s.pc = "stk_mul_add.exit") :
    step calls stkMulBody (stateAt env s) = Ctrl.ret none (stateAt env s) := by
  have hrec : denoteCode calls stkMulStkMulAddExitInstrs
      { env := env, mem := s.mem, next := s.next, pc := "stk_mul_add.exit", pre := s.pre } =
        some (stateAt env s) := by
    rw [← hpc]
    rfl
  simp only [stateAt, step, hpc, stkMul_findBlock_stk_mul_add_exit, hrec, execTerm]

/-! ### Bytes, and the written prefix

Two facts about the memory model carry the multiply: an encoding of a byte list
is that list, and a write of the bytes a range reads back leaves the memory
alone.  Then the written limb prefix: reads above it are the underlying memory's,
and the prefix composes. -/

/-- A byte list is the little-endian encoding of the value it denotes. -/
theorem natToBytes_bytesToNat_stk (bs : List UInt8) :
    natToBytes (bytesToNat bs) bs.length = bs := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
      show UInt8.ofNat ((b.toNat + 256 * bytesToNat rest) % 256) ::
          natToBytes ((b.toNat + 256 * bytesToNat rest) / 256) rest.length = b :: rest
      have hlt : b.toNat < 256 := by simpa using UInt8.toNat_lt b
      have hmod : (b.toNat + 256 * bytesToNat rest) % 256 = b.toNat := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
      have hdiv : (b.toNat + 256 * bytesToNat rest) / 256 = bytesToNat rest := by
        rw [Nat.add_mul_div_left _ _ (by decide : 0 < 256), Nat.div_eq_of_lt hlt,
          Nat.zero_add]
      rw [hmod, hdiv, ih, UInt8.ofNat_toNat]

/-- A byte written where the memory already holds it is the memory. -/
theorem writeByte_eq_self_of_readByte {m : Mem} {addr : Nat} {b : UInt8}
    (h : readByte m addr = some b) : writeByte m addr b = m := by
  induction m with
  | nil => simp [readByte] at h
  | cons cell rest ih =>
      obtain ⟨a, b'⟩ := cell
      simp only [writeByte]
      split
      · rename_i ha
        subst ha
        simp only [readByte] at h
        rw [Option.some.inj h]
      · rename_i ha
        simp only [readByte] at h
        rw [ite_eq_right ha] at h
        simp only [ih h]

/-- A write sequence does not disturb a read whose range is above it. -/
theorem readBytes_writeBytes_above_stk (m : Mem) (bs : List UInt8) :
    ∀ (n addr start : Nat), start + bs.length ≤ addr →
      readBytes (writeBytes m start bs) addr n = readBytes m addr n
  | 0, _, _, _ => by simp only [readBytes]
  | n + 1, addr, start, h => by
      simp only [readBytes]
      rw [readByte_writeBytes_above m bs h]
      cases hr : readByte m addr with
      | none => rfl
      | some b => rw [readBytes_writeBytes_above_stk m bs n (addr + 1) start (by omega)]

/-- A write of the bytes a range reads back leaves the memory unchanged. -/
theorem writeBytes_eq_self_of_readBytes {m : Mem} {addr : Nat} {bs : List UInt8}
    (h : readBytes m addr bs.length = some bs) : writeBytes m addr bs = m := by
  induction bs generalizing m addr with
  | nil => rfl
  | cons b rest ih =>
      rw [List.length_cons] at h
      cases hm : readByte m addr with
      | none =>
          have h' : readBytes m addr (rest.length + 1) = none := by
            simp only [readBytes, hm]
          rw [h'] at h
          cases h
      | some b' =>
          cases hr : readBytes m (addr + 1) rest.length with
          | none =>
              have h' : readBytes m addr (rest.length + 1) = none := by
                simp only [readBytes, hm, hr]
              rw [h'] at h
              cases h
          | some rest' =>
              have h' : readBytes m addr (rest.length + 1) = some (b' :: rest') := by
                simp only [readBytes, hm, hr]
              rw [h'] at h
              have h2 : b' :: rest' = b :: rest := Option.some.inj h
              rw [List.cons.injEq] at h2
              obtain ⟨hb', hr'⟩ := h2
              rw [hb'] at hm
              rw [hr'] at hr
              have hstep : readBytes (writeByte m addr b) (addr + 1) rest.length =
                  some rest := by
                have hup := readBytes_writeBytes_above_stk m [b] rest.length (addr + 1) addr
                  (by simp only [List.length_cons, List.length_nil]; omega)
                exact hup.trans hr
              show writeBytes (writeByte m addr b) (addr + 1) rest = m
              rw [ih (m := writeByte m addr b) (addr := addr + 1) hstep]
              exact writeByte_eq_self_of_readByte hm

/-- Reads above a written limb prefix are the underlying memory's. -/
theorem readBytes_stkWriteLimbs_above (mem : Mem) :
    ∀ (ws : List Nat) (a q k : Nat), a + 8 * ws.length ≤ q →
      readBytes (stkWriteLimbs mem a ws) q k = readBytes mem q k
  | [], a, q, k, _ => rfl
  | w :: ws, a, q, k, h => by
      show readBytes
        (stkWriteLimbs (writeBytes mem a (natToBytes (w % 2 ^ 64) 8)) (a + 8) ws) q k = _
      rw [readBytes_stkWriteLimbs_above (writeBytes mem a (natToBytes (w % 2 ^ 64) 8))
        ws (a + 8) q k (by
          have hlen : (w :: ws).length = ws.length + 1 := rfl
          rw [hlen, Nat.mul_succ] at h
          omega)]
      rw [readBytes_writeBytes_above_stk mem (natToBytes (w % 2 ^ 64) 8) k q a
        (by
          have hlen : (w :: ws).length = ws.length + 1 := rfl
          rw [hlen] at h
          rw [natToBytes_length]
          omega)]

/-- The written prefix composes: appending limbs to a prefix continues at the
address the prefix ended at. -/
theorem stkWriteLimbs_append (mem : Mem) :
    ∀ (l1 l2 : List Nat) (a : Nat),
      stkWriteLimbs mem a (l1 ++ l2) =
        stkWriteLimbs (stkWriteLimbs mem a l1) (a + 8 * l1.length) l2
  | [], l2, a => by simp only [List.nil_append, stkWriteLimbs, List.length_nil,
      Nat.mul_zero, Nat.add_zero]
  | w :: ws, l2, a => by
      show stkWriteLimbs (writeBytes mem a (natToBytes (w % 2 ^ 64) 8)) (a + 8)
          (ws ++ l2) = _
      rw [stkWriteLimbs_append (writeBytes mem a (natToBytes (w % 2 ^ 64) 8)) ws l2 (a + 8)]
      simp only [List.length_cons, Nat.mul_succ]
      congr 1
      omega

/-! ### The entry block

`%n.i` is the count cell's address (768 bytes past the struct), `%0` the count,
and `%cmp28.i` its signed positive test. -/

/-- The entry's environment: the count's address, the count, and its test. -/
def stkMulEntryEnv (env : Env) (a : Nat) (nv : BitVec 32) : Env :=
  ("%cmp28.i", .int 1 (evalICmp .sgt nv 0x00000000#32)) ::
  ("%0", .int 32 nv) ::
  ("%n.i", .ptr (a + 768)) :: env

/-- The entry's chain at its pin. -/
theorem stkMul_entry_denote {calls : Calls} {env : Env} {s : State}
    {a : Nat} {nv : BitVec 32}
    (ha : lookupName env "%a" = some (.ptr a))
    (hn : readBytes s.mem (a + 768) 4 = some (natToBytes nv.toNat 4)) :
    denoteCode calls stkMulEntryInstrs (stateAt env s) =
      some (stateAt (stkMulEntryEnv env a nv) s) := by
  unfold stkMulEntryInstrs stkMulEntryEnv
  stk_block_eval

/-! ### The preheader

`%conv3.i` widens the multiplier once, `%wide.trip.count.i` the count, and the
block's two tests are the unroll decision (`%0 <u 4`) and the residue's mask. -/

/-- The preheader's environment. -/
def stkMulLrPhEnv (env : Env) (m : BitVec 64) (nv : BitVec 32) : Env :=
  ("%1", .int 1 (evalICmp .ult nv 0x00000004#32)) ::
  ("%xtraiter", .int 64 (BitVec.ofNat 64 nv.toNat &&& 0x0000000000000003#64)) ::
  ("%wide.trip.count.i", .int 64 (BitVec.ofNat 64 nv.toNat)) ::
  ("%conv3.i", .int 128 (BitVec.ofNat 128 m.toNat)) :: env

/-- The preheader's chain at its pin. -/
theorem stkMul_lrPh_denote {calls : Calls} {env : Env} {s : State}
    {m : BitVec 64} {nv : BitVec 32}
    (hm : lookupName env "%m" = some (.int 64 m))
    (hn : lookupName env "%0" = some (.int 32 nv)) :
    denoteCode calls stkMulForBodyLrPhIInstrs (stateAt env s) =
      some (stateAt (stkMulLrPhEnv env m nv) s) := by
  unfold stkMulForBodyLrPhIInstrs stkMulLrPhEnv
  stk_block_eval

/-- The widened-count block: the group count. -/
def stkMulLrPhNewEnv (env : Env) (wide : BitVec 64) : Env :=
  ("%unroll_iter", .int 64 (wide &&& 0x000000007ffffffc#64)) :: env

/-- The widened-count block's chain at its pin. -/
theorem stkMul_lrPhNew_denote {calls : Calls} {env : Env} {s : State}
    {wide : BitVec 64}
    (hw : lookupName env "%wide.trip.count.i" = some (.int 64 wide)) :
    denoteCode calls stkMulForBodyLrPhINewInstrs (stateAt env s) =
      some (stateAt (stkMulLrPhNewEnv env wide) s) := by
  unfold stkMulForBodyLrPhINewInstrs stkMulLrPhNewEnv
  stk_block_eval

/-! ### The two truncated-carry blocks

`%extract.t6` and `%extract.t5` are the loops' last carry read back at `i64`: the
value the tail block's phi takes from each exit. -/

/-- The group loop's exit: the last iteration's shifted carry, truncated. -/
def stkMulLoopexitEnv (env : Env) (sh : BitVec 128) : Env :=
  ("%extract.t6", .int 64 (BitVec.ofNat 64 (sh.toNat % 2 ^ 64))) :: env

/-- The group loop's exit chain at its pin. -/
theorem stkMul_loopexit_denote {calls : Calls} {env : Env} {s : State}
    {sh : BitVec 128}
    (hs : lookupName env "%shr.i.3" = some (.int 128 sh)) :
    denoteCode calls stkMulWhileCondPreheaderIUnrLcssaLoopexitInstrs (stateAt env s) =
      some (stateAt (stkMulLoopexitEnv env sh) s) := by
  unfold stkMulWhileCondPreheaderIUnrLcssaLoopexitInstrs stkMulLoopexitEnv
  stk_block_eval

/-- The residue loop's exit: the same truncation of `%shr.i.epil`. -/
def stkMulEpilogLcssaEnv (env : Env) (sh : BitVec 128) : Env :=
  ("%extract.t5", .int 64 (BitVec.ofNat 64 (sh.toNat % 2 ^ 64))) :: env

/-- The residue loop's exit chain at its pin. -/
theorem stkMul_epilogLcssa_denote {calls : Calls} {env : Env} {s : State}
    {sh : BitVec 128}
    (hs : lookupName env "%shr.i.epil" = some (.int 128 sh)) :
    denoteCode calls stkMulWhileCondPreheaderIEpilogLcssaInstrs (stateAt env s) =
      some (stateAt (stkMulEpilogLcssaEnv env sh) s) := by
  unfold stkMulWhileCondPreheaderIEpilogLcssaInstrs stkMulEpilogLcssaEnv
  stk_block_eval

/-! ### The carry tail's write

The tail writes the final carry at limb index `n` and the count `n + 1`; the two
stores are the last writes the body makes. -/

/-- The tail's environment: the incremented count and the carry's address. -/
def stkMulBodyUsEnv (env : Env) (a : Nat) (wide : BitVec 64) (nv : BitVec 32) : Env :=
  ("%arrayidx14.us.i", .ptr (a + wide.toNat * (Ty.int 64).sizeBytes)) ::
  ("%inc12.us.i", .int 32 (nv + 0x00000001#32)) :: env

/-- The tail's state: the carry word written at limb index `n`, then the count. -/
def stkMulBodyUsState (s : State) (a ni : Nat) (nv : BitVec 32) (wide off : BitVec 64) :
    State :=
  State.mk s.env
    (writeBytes
      (writeBytes s.mem (a + wide.toNat * (Ty.int 64).sizeBytes)
        (natToBytes off.toNat 8))
      ni (natToBytes (nv + 0x00000001#32).toNat 4))
    s.next s.pc s.pre

/-- The tail's chain at its pin, and the memory it leaves. -/
theorem stkMul_whileBodyUs_denote {calls : Calls} {env : Env} {s : State}
    {a ni : Nat} {nv : BitVec 32} {wide off : BitVec 64}
    (ha : lookupName env "%a" = some (.ptr a))
    (hn : lookupName env "%n.i" = some (.ptr ni))
    (hnv : lookupName env "%0" = some (.int 32 nv))
    (hw : lookupName env "%wide.trip.count.i" = some (.int 64 wide))
    (hwpos : wide.toNat < 2 ^ 63)
    (hoff : lookupName env "%shr.i.lcssa.off0" = some (.int 64 off)) :
    denoteCode calls stkMulWhileBodyUsIInstrs (stateAt env s) =
      some (stateAt (stkMulBodyUsEnv env a wide nv)
        (stkMulBodyUsState s a ni nv wide off)) := by
  unfold stkMulWhileBodyUsIInstrs stkMulBodyUsEnv stkMulBodyUsState
  stk_block_eval



/-! ### A `phi` step, and a block's leading run, read one member at a time

`BlockEval`'s `block_phi_run` collects a run's members' values as metavariables
and lets the block's statement fix them; a member whose incoming is the `poison`
literal is outside `PhiSelects` altogether, and a run whose members' cells are
all the statement names is clearer read one step at a time.  These are the two
steps: `denoteRun_phi_reg` for a register incoming, `denoteRun_phi_imm` for a
literal one, and `denoteRun_phi_poison` for the marker. -/

/-- Splitting a straight-line sequence at a point whose state is already known. -/
theorem stkMul_denoteCode_append_apply {calls : Calls} {a b : List Instr} {s s' : State}
    (h : denoteCode calls a s = some s') (hb : startsWithPhi b = false) :
    denoteCode calls (a ++ b) s = denoteCode calls b s' := by
  rw [JsonEntrySteps.denoteCode_append (hb := hb), h]
  rfl

/-- A code list's run is the empty-pending run: the bridge from `denoteRun` back
to the `denoteCode` the chain steps rewrite. -/
theorem denoteCode_eq_denoteRun (calls : Calls) (is : List Instr) (s : State) :
    denoteCode calls is s = denoteRun calls [] is s := rfl

/-- One member of a leading `phi` run: the run continues with the selected
binding installed. -/
theorem denoteRun_phi_cons {calls : Calls} {pend : List (String × Value)}
    {d : String} {ty : Ty} {inc : List (String × Operand)} {is : List Instr}
    {s : State} {v : Value} (h : phiSelect s inc = some v) :
    denoteRun calls pend (.phi d ty inc :: is) s =
      denoteRun calls (pend ++ [(d, v)]) is s := by
  simp only [denoteRun, h]

/-- A leading `phi` whose selected incoming is a register. -/
theorem denoteRun_phi_reg {calls : Calls} {pend : List (String × Value)}
    {d : String} {ty : Ty} {inc : List (String × Operand)} {is : List Instr}
    {s : State} {p : String} {n : String} {v : Value}
    (hpre : s.pre = some p) (hinc : phiIncoming p inc = some (.reg n))
    (h : evalOperand s (.reg n) = some v) :
    denoteRun calls pend (.phi d ty inc :: is) s =
      denoteRun calls (pend ++ [(d, v)]) is s := by
  rw [denoteRun_phi_cons (v := v)]
  congr 1
  rw [show phiSelect s inc = evalOperand s (.reg n) from by
    simp only [phiSelect, hpre, hinc]]
  exact h

/-- A leading `phi` whose selected incoming is an `iW` literal. -/
theorem denoteRun_phi_int {calls : Calls} {pend : List (String × Value)}
    {d : String} {ty : Ty} {inc : List (String × Operand)} {is : List Instr}
    {s : State} {p : String} {w : Nat} {x : BitVec w}
    (hpre : s.pre = some p) (hinc : phiIncoming p inc = some (.imm (.int w x))) :
    denoteRun calls pend (.phi d ty inc :: is) s =
      denoteRun calls (pend ++ [(d, .int w x)]) is s := by
  rw [denoteRun_phi_cons (v := .int w x)]
  congr 1
  simp only [phiSelect, hpre, hinc, evalOperand, Const.toValue]

/-- A leading `phi` whose selected incoming is the `poison` literal selects the
marker: `phiSelect` names it before the operand is read. -/
theorem denoteRun_phi_poison {calls : Calls} {pend : List (String × Value)}
    {d : String} {ty : Ty} {inc : List (String × Operand)} {is : List Instr}
    {s : State} {p : String}
    (hpre : s.pre = some p) (hinc : phiIncoming p inc = some (.imm Const.poison)) :
    denoteRun calls pend (.phi d ty inc :: is) s =
      denoteRun calls (pend ++ [(d, .poison)]) is s := by
  rw [denoteRun_phi_cons (v := .poison)]
  congr 1
  simp only [phiSelect, hpre, hinc]

/-! ### The two joins

`while.cond.preheader.i.unr-lcssa` takes the group loop's last carry (or, on the
short-count path, two `poison` incomings the body never reads) and the residue
count; `while.cond.preheader.i.epilog-lcssa` truncates the residue loop's last
carry.  `while.cond.preheader.i` merges the two and tests the carry word against
`2 ^ 64`. -/

/-- The group loop's join, entered from the loop: the last iteration's sum, its
truncation, the index and the carry. -/
def stkMulUnrLcssaLoopexitEnv (env : Env) (sum : BitVec 128) (e : BitVec 64)
    (ivn : BitVec 64) (sh : BitVec 128) (xt : BitVec 64) : Env :=
  ("%lcmp.mod.not", .int 1 (evalICmp .eq xt 0x0000000000000000#64)) ::
  ("%carry.029.i.unr", .int 128 sh) ::
  ("%indvars.iv.i.unr", .int 64 ivn) ::
  ("%shr.i.lcssa.ph.off0", .int 64 e) ::
  ("%add4.i.lcssa.ph", .int 128 sum) :: env

/-- The group loop's join from the loop: every member selects a register. -/
theorem stkMul_unrLcssaLoopexit_denote {calls : Calls} {env : Env} {s : State}
    {sum : BitVec 128} {e ivn : BitVec 64} {sh : BitVec 128} {xt : BitVec 64}
    (hpre : s.pre = some "while.cond.preheader.i.unr-lcssa.loopexit")
    (hsum : lookupName env "%add4.i.3" = some (.int 128 sum))
    (he : lookupName env "%extract.t6" = some (.int 64 e))
    (hivn : lookupName env "%indvars.iv.next.i.3" = some (.int 64 ivn))
    (hsh : lookupName env "%shr.i.3" = some (.int 128 sh))
    (hxt : lookupName env "%xtraiter" = some (.int 64 xt)) :
    denoteCode calls stkMulWhileCondPreheaderIUnrLcssaInstrs (stateAt env s) =
      some (stateAt (stkMulUnrLcssaLoopexitEnv env sum e ivn sh xt) s) := by
  unfold stkMulWhileCondPreheaderIUnrLcssaInstrs stkMulUnrLcssaLoopexitEnv
  stk_block_eval

/-- The carry test's merge, from the residue loop's exit: the sum's low half is
the stored word and its high half the carry. -/
def stkMulWhileCondEnv (env : Env) (sum : BitVec 128) (e : BitVec 64) : Env :=
  ("%tobool.not31.i", .int 1 (evalICmp .ult sum
    0x00000000000000010000000000000000#128)) ::
  ("%shr.i.lcssa.off0", .int 64 e) ::
  ("%add4.i.lcssa", .int 128 sum) :: env

/-- The carry test's merge from the residue loop. -/
theorem stkMul_whileCondFromEpilog_denote {calls : Calls} {env : Env} {s : State}
    {sum : BitVec 128} {e : BitVec 64}
    (hpre : s.pre = some "while.cond.preheader.i.epilog-lcssa")
    (hsum : lookupName env "%add4.i.epil" = some (.int 128 sum))
    (he : lookupName env "%extract.t5" = some (.int 64 e)) :
    denoteCode calls stkMulWhileCondPreheaderIInstrs (stateAt env s) =
      some (stateAt (stkMulWhileCondEnv env sum e) s) := by
  unfold stkMulWhileCondPreheaderIInstrs stkMulWhileCondEnv
  stk_block_eval

/-- The carry test's merge from the group loop's join. -/
theorem stkMul_whileCondFromUnr_denote {calls : Calls} {env : Env} {s : State}
    {sum : BitVec 128} {e : BitVec 64}
    (hpre : s.pre = some "while.cond.preheader.i.unr-lcssa")
    (hsum : lookupName env "%add4.i.lcssa.ph" = some (.int 128 sum))
    (he : lookupName env "%shr.i.lcssa.ph.off0" = some (.int 64 e)) :
    denoteCode calls stkMulWhileCondPreheaderIInstrs (stateAt env s) =
      some (stateAt (stkMulWhileCondEnv env sum e) s) := by
  unfold stkMulWhileCondPreheaderIInstrs stkMulWhileCondEnv
  stk_block_eval

/-! ### The residue loop's body

One limb per iteration, at the index the phis carry. -/

/-- The residue iteration's state: the truncated sum written at the limb's
address. -/
def stkMulEpilState (s : State) (a : Nat) (ivn : BitVec 64) (cv mw : BitVec 128)
    (x : BitVec 64) : State :=
  State.mk s.env
    (writeBytes s.mem (a + ivn.toNat * (Ty.int 64).sizeBytes)
      (natToBytes (BitVec.ofNat 64
        ((BitVec.ofNat 128 x.toNat * mw + cv).toNat % 2 ^ 64)).toNat 8))
    s.next s.pc s.pre

/-- The residue iteration's environment. -/
def stkMulEpilEnv (env : Env) (a : Nat) (ivn : BitVec 64) (cv mw : BitVec 128)
    (x xt : BitVec 64) : Env :=
  ("%epil.iter.cmp.not", .int 1 (evalICmp .eq (0x0000000000000000#64 + 0x0000000000000001#64) xt)) ::
  ("%epil.iter.next", .int 64 (0x0000000000000000#64 + 0x0000000000000001#64)) ::
  ("%indvars.iv.next.i.epil", .int 64 (ivn + 0x0000000000000001#64)) ::
  ("%shr.i.epil", .int 128 ((BitVec.ofNat 128 x.toNat * mw + cv) >>> 64)) ::
  ("%conv5.i.epil", .int 64 (BitVec.ofNat 64
    ((BitVec.ofNat 128 x.toNat * mw + cv).toNat % 2 ^ 64))) ::
  ("%add4.i.epil", .int 128 (BitVec.ofNat 128 x.toNat * mw + cv)) ::
  ("%mul.i.epil", .int 128 (BitVec.ofNat 128 x.toNat * mw)) ::
  ("%conv2.i.epil", .int 128 (BitVec.ofNat 128 x.toNat)) ::
  ("%2", .int 64 x) ::
  ("%arrayidx.i.epil", .ptr (a + ivn.toNat * (Ty.int 64).sizeBytes)) ::
  ("%epil.iter", .int 64 0x0000000000000000#64) ::
  ("%carry.029.i.epil", .int 128 cv) ::
  ("%indvars.iv.i.epil", .int 64 ivn) :: env

/-- The residue iteration's environment when the loop re-enters itself: the
residue counter is the previous iteration's step. -/
def stkMulEpilEnvBack (env : Env) (a : Nat) (ivn : BitVec 64) (cv mw : BitVec 128)
    (x xt it : BitVec 64) : Env :=
  ("%epil.iter.cmp.not", .int 1 (evalICmp .eq (it + 0x0000000000000001#64) xt)) ::
  ("%epil.iter.next", .int 64 (it + 0x0000000000000001#64)) ::
  ("%indvars.iv.next.i.epil", .int 64 (ivn + 0x0000000000000001#64)) ::
  ("%shr.i.epil", .int 128 ((BitVec.ofNat 128 x.toNat * mw + cv) >>> 64)) ::
  ("%conv5.i.epil", .int 64 (BitVec.ofNat 64
    ((BitVec.ofNat 128 x.toNat * mw + cv).toNat % 2 ^ 64))) ::
  ("%add4.i.epil", .int 128 (BitVec.ofNat 128 x.toNat * mw + cv)) ::
  ("%mul.i.epil", .int 128 (BitVec.ofNat 128 x.toNat * mw)) ::
  ("%conv2.i.epil", .int 128 (BitVec.ofNat 128 x.toNat)) ::
  ("%2", .int 64 x) ::
  ("%arrayidx.i.epil", .ptr (a + ivn.toNat * (Ty.int 64).sizeBytes)) ::
  ("%epil.iter", .int 64 it) ::
  ("%carry.029.i.epil", .int 128 cv) ::
  ("%indvars.iv.i.epil", .int 64 ivn) :: env

/-- The residue iteration's chain, and the memory it writes. -/
theorem stkMul_epil_denote {calls : Calls} {env : Env} {s : State}
    {a : Nat} {ivn xt x : BitVec 64} {cv mw : BitVec 128}
    (hpre : s.pre = some "while.cond.preheader.i.unr-lcssa")
    (ha : lookupName env "%a" = some (.ptr a))
    (hivn : evalOperand (stateAt env s) (.reg "%indvars.iv.i.unr") = some (.int 64 ivn))
    (hcv : evalOperand (stateAt env s) (.reg "%carry.029.i.unr") = some (.int 128 cv))
    (hmw : lookupName env "%conv3.i" = some (.int 128 mw))
    (hxt : lookupName env "%xtraiter" = some (.int 64 xt))
    (hpos : ivn.toNat < 2 ^ 63)
    (hread : readBytes s.mem (a + ivn.toNat * (Ty.int 64).sizeBytes) 8 =
      some (natToBytes x.toNat 8)) :
    denoteCode calls stkMulForBodyIEpilInstrs (stateAt env s) =
      some (stateAt (stkMulEpilEnv env a ivn cv mw x xt)
        (stkMulEpilState s a ivn cv mw x)) := by
  unfold stkMulForBodyIEpilInstrs
  simp only [denoteCode]
  rw [denoteRun_phi_reg (s := stateAt env s) (inc := [("for.body.i.epil", .reg "%indvars.iv.next.i.epil"),
      ("while.cond.preheader.i.unr-lcssa", .reg "%indvars.iv.i.unr")])
      (n := "%indvars.iv.i.unr") (v := .int 64 ivn) hpre (by decide) hivn]
  rw [denoteRun_phi_reg (s := stateAt env s) (inc := [("for.body.i.epil", .reg "%shr.i.epil"),
      ("while.cond.preheader.i.unr-lcssa", .reg "%carry.029.i.unr")])
      (n := "%carry.029.i.unr") (v := .int 128 cv) hpre (by decide) hcv]
  rw [denoteRun_phi_int (s := stateAt env s) (inc := [("for.body.i.epil", .reg "%epil.iter.next"),
      ("while.cond.preheader.i.unr-lcssa", .imm (.int 64 0x0000000000000000#64))])
      (w := 64) (x := 0x0000000000000000#64) hpre (by decide)]
  rw [denoteRun_nil_pend (by rfl), stateAt_bindAll_runCells]
  rw [← denoteCode_eq_denoteRun]
  simp only [runCells, List.nil_append, List.cons_append, List.singleton_append]
  unfold stkMulEpilEnv stkMulEpilState
  stk_block_eval

/-- The residue iteration from the loop itself: the phis take the previous
iteration's step and the constant zero. -/
theorem stkMul_epilBack_denote {calls : Calls} {env : Env} {s : State}
    {a : Nat} {ivn xt x : BitVec 64} {cv mw : BitVec 128} {it : BitVec 64}
    (hpre : s.pre = some "for.body.i.epil")
    (ha : lookupName env "%a" = some (.ptr a))
    (hivn : evalOperand (stateAt env s) (.reg "%indvars.iv.next.i.epil") =
      some (.int 64 ivn))
    (hcv : evalOperand (stateAt env s) (.reg "%shr.i.epil") = some (.int 128 cv))
    (hit : evalOperand (stateAt env s) (.reg "%epil.iter.next") = some (.int 64 it))
    (hmw : lookupName env "%conv3.i" = some (.int 128 mw))
    (hxt : lookupName env "%xtraiter" = some (.int 64 xt))
    (hpos : ivn.toNat < 2 ^ 63)
    (hread : readBytes s.mem (a + ivn.toNat * (Ty.int 64).sizeBytes) 8 =
      some (natToBytes x.toNat 8)) :
    denoteCode calls stkMulForBodyIEpilInstrs (stateAt env s) =
      some (stateAt (stkMulEpilEnvBack env a ivn cv mw x xt it)
        (stkMulEpilState s a ivn cv mw x)) := by
  unfold stkMulForBodyIEpilInstrs
  simp only [denoteCode]
  rw [denoteRun_phi_reg (s := stateAt env s) (inc := [("for.body.i.epil", .reg "%indvars.iv.next.i.epil"),
      ("while.cond.preheader.i.unr-lcssa", .reg "%indvars.iv.i.unr")])
      (n := "%indvars.iv.next.i.epil") (v := .int 64 ivn) hpre (by decide) hivn]
  rw [denoteRun_phi_reg (s := stateAt env s) (inc := [("for.body.i.epil", .reg "%shr.i.epil"),
      ("while.cond.preheader.i.unr-lcssa", .reg "%carry.029.i.unr")])
      (n := "%shr.i.epil") (v := .int 128 cv) hpre (by decide) hcv]
  rw [denoteRun_phi_reg (s := stateAt env s) (inc := [("for.body.i.epil", .reg "%epil.iter.next"),
      ("while.cond.preheader.i.unr-lcssa", .imm (.int 64 0x0000000000000000#64))])
      (n := "%epil.iter.next") (v := .int 64 it) hpre (by decide) hit]
  rw [denoteRun_nil_pend (by rfl), stateAt_bindAll_runCells]
  rw [← denoteCode_eq_denoteRun]
  simp only [runCells, List.nil_append, List.cons_append, List.singleton_append]
  unfold stkMulEpilEnvBack stkMulEpilState
  stk_block_eval

/-! ### The fold, four limbs at a time

The emitted group multiplies four limbs per iteration; the model's fold takes one
limb per step.  The two lemmas below are what says the four steps are the fold's
four: one cons step at the fold's own `let`, and the concatenation that carries
the first part's carry into the second. -/

/-- One fold step, at the `let` the definition writes. -/
theorem stkMulFold_cons (w : Nat) (ws : List Nat) (m c : Nat) :
    stkMulFold (w :: ws) m c =
      ((w * m + c) % 2 ^ 64 ::
          (stkMulFold ws m ((w * m + c) / 2 ^ 64)).1,
       (stkMulFold ws m ((w * m + c) / 2 ^ 64)).2) := rfl

/-- The fold over a concatenation: the second part starts from the first's
carry. -/
theorem stkMulFold_append (l1 l2 : List Nat) (m c : Nat) :
    stkMulFold (l1 ++ l2) m c =
      ((stkMulFold l1 m c).1 ++ (stkMulFold l2 m (stkMulFold l1 m c).2).1,
       (stkMulFold l2 m (stkMulFold l1 m c).2).2) := by
  induction l1 generalizing c with
  | nil => simp [stkMulFold]
  | cons w ws ih =>
      rw [List.cons_append, stkMulFold_cons, stkMulFold_cons, ih]
      rfl

/-! ### The four-limb group iteration, one limb at a time

`for.body.i` multiplies four limbs per iteration.  Its statement is thirty-six
cells and four stores, and a single `block_eval` over it does not fit the
heartbeat budget (measured below); the block is therefore split into its four
nine-instruction limb steps and the counter tail, and the composed statement is
the thirty-six-cell one.  `JsonEntrySteps.denoteCode_append` is the split: the
second half must not begin with a `phi`, which is why the leading run is settled
before the first split.

**The size threshold, measured.**  `block_eval` over the whole block exceeded the
module's 8,000,000 heartbeats in one pass (two attempts, 543 s and 614 s wall on
`t3c-01a21253`), while each nine-instruction limb below elaborates in seconds.
The cost is `block_close`'s register resolution, which re-reads the environment
at every read; at ~40 instructions and 36 cells it is quadratic in the block's
size, not linear.  Splitting is what makes a body this size provable at all. -/

/-- The first limb step: `%indvars.iv.i`, the phi's carry, and the multiplier. -/
def stkMulLimb0Instrs : List Instr :=
  [Instr.gep "%arrayidx.i" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%indvars.iv.i"),
   Instr.load "%3" (Ty.int 64) (Operand.reg "%arrayidx.i"),
   Instr.zext "%conv2.i" 64 128 (Operand.reg "%3"),
   Instr.binop "%mul.i" (BinOp.mul) 128 (Operand.reg "%conv2.i") (Operand.reg "%conv3.i"),
   Instr.binop "%add4.i" (BinOp.add) 128 (Operand.reg "%mul.i") (Operand.reg "%carry.029.i"),
   Instr.trunc "%conv5.i" 128 64 (Operand.reg "%add4.i"),
   Instr.store (Ty.int 64) (Operand.reg "%conv5.i") (Operand.reg "%arrayidx.i"),
   Instr.binop "%shr.i" (BinOp.lshr) 128 (Operand.reg "%add4.i")
     (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
   Instr.binop "%indvars.iv.next.i" (BinOp.or) 64 (Operand.reg "%indvars.iv.i")
     (Operand.imm (Const.int 64 0x0000000000000001#64))]

/-- The first limb step's cells. -/
def stkMulLimb0Env (env : Env) (a : Nat) (iv : BitVec 64) (cv mw : BitVec 128)
    (x : BitVec 64) : Env :=
  let t : BitVec 128 := BitVec.ofNat 128 x.toNat * mw + cv
  ("%indvars.iv.next.i", .int 64 (iv ||| 0x0000000000000001#64)) ::
  ("%shr.i", .int 128 (t >>> 64)) ::
  ("%conv5.i", .int 64 (BitVec.ofNat 64 (t.toNat % 2 ^ 64))) ::
  ("%add4.i", .int 128 t) ::
  ("%mul.i", .int 128 (BitVec.ofNat 128 x.toNat * mw)) ::
  ("%conv2.i", .int 128 (BitVec.ofNat 128 x.toNat)) ::
  ("%3", .int 64 x) ::
  ("%arrayidx.i", .ptr (a + iv.toNat * (Ty.int 64).sizeBytes)) :: env

/-- The first limb step's state: its truncated word, written at its address. -/
def stkMulLimbState (s : State) (a : Nat) (iv : BitVec 64) (cv mw : BitVec 128)
    (x : BitVec 64) : State :=
  let t : BitVec 128 := BitVec.ofNat 128 x.toNat * mw + cv
  State.mk s.env
    (writeBytes s.mem (a + iv.toNat * (Ty.int 64).sizeBytes)
      (natToBytes (BitVec.ofNat 64 (t.toNat % 2 ^ 64)).toNat 8))
    s.next s.pc s.pre

/-- The first limb step's chain. -/
theorem stkMul_limb0_denote {calls : Calls} {env : Env} {s : State}
    {a : Nat} {iv x : BitVec 64} {cv mw : BitVec 128}
    (ha : lookupName env "%a" = some (.ptr a))
    (hiv : lookupName env "%indvars.iv.i" = some (.int 64 iv))
    (hcv : lookupName env "%carry.029.i" = some (.int 128 cv))
    (hmw : lookupName env "%conv3.i" = some (.int 128 mw))
    (hpos : iv.toNat < 2 ^ 63)
    (hread : readBytes s.mem (a + iv.toNat * (Ty.int 64).sizeBytes) 8 =
      some (natToBytes x.toNat 8)) :
    denoteCode calls stkMulLimb0Instrs (stateAt env s) =
      some (stateAt (stkMulLimb0Env env a iv cv mw x)
        (stkMulLimbState s a iv cv mw x)) := by
  unfold stkMulLimb0Instrs stkMulLimb0Env stkMulLimbState
  stk_block_eval

/-- A read above a written word is the underlying memory's: the limb step's state
only writes at its own address, so a read past it does not see the write. -/
theorem stkLimbState_read_above (s : State) (a : Nat) (iv : BitVec 64)
    (cv mw : BitVec 128) (x : BitVec 64) (k : Nat) {q : Nat}
    (hq : a + iv.toNat * (Ty.int 64).sizeBytes + 8 ≤ q) :
    readBytes (stkMulLimbState s a iv cv mw x).mem q k = readBytes s.mem q k := by
  rw [stkMulLimbState]
  exact readBytes_writeBytes_above_stk s.mem _ k q (a + iv.toNat * (Ty.int 64).sizeBytes) hq

/-- The second limb step: the first limb's `or` index, its carry, and the same
multiplier. -/
def stkMulLimb1Instrs : List Instr :=
  [Instr.gep "%arrayidx.i.1" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%indvars.iv.next.i"),
   Instr.load "%4" (Ty.int 64) (Operand.reg "%arrayidx.i.1"),
   Instr.zext "%conv2.i.1" 64 128 (Operand.reg "%4"),
   Instr.binop "%mul.i.1" (BinOp.mul) 128 (Operand.reg "%conv2.i.1") (Operand.reg "%conv3.i"),
   Instr.binop "%add4.i.1" (BinOp.add) 128 (Operand.reg "%mul.i.1") (Operand.reg "%shr.i"),
   Instr.trunc "%conv5.i.1" 128 64 (Operand.reg "%add4.i.1"),
   Instr.store (Ty.int 64) (Operand.reg "%conv5.i.1") (Operand.reg "%arrayidx.i.1"),
   Instr.binop "%shr.i.1" (BinOp.lshr) 128 (Operand.reg "%add4.i.1")
     (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
   Instr.binop "%indvars.iv.next.i.1" (BinOp.or) 64 (Operand.reg "%indvars.iv.i")
     (Operand.imm (Const.int 64 0x0000000000000002#64))]

/-- The second limb step's cells. -/
def stkMulLimb1Env (env : Env) (a : Nat) (ivn ivb : BitVec 64) (cv mw : BitVec 128)
    (x : BitVec 64) : Env :=
  let t : BitVec 128 := BitVec.ofNat 128 x.toNat * mw + cv
  ("%indvars.iv.next.i.1", .int 64 (ivb ||| 0x0000000000000002#64)) ::
  ("%shr.i.1", .int 128 (t >>> 64)) ::
  ("%conv5.i.1", .int 64 (BitVec.ofNat 64 (t.toNat % 2 ^ 64))) ::
  ("%add4.i.1", .int 128 t) ::
  ("%mul.i.1", .int 128 (BitVec.ofNat 128 x.toNat * mw)) ::
  ("%conv2.i.1", .int 128 (BitVec.ofNat 128 x.toNat)) ::
  ("%4", .int 64 x) ::
  ("%arrayidx.i.1", .ptr (a + ivn.toNat * (Ty.int 64).sizeBytes)) :: env

/-- The second limb step's chain. -/
theorem stkMul_limb1_denote {calls : Calls} {env : Env} {s : State}
    {a : Nat} {ivn ivb x : BitVec 64} {cv mw : BitVec 128}
    (ha : lookupName env "%a" = some (.ptr a))
    (hivn : lookupName env "%indvars.iv.next.i" = some (.int 64 ivn))
    (hivb : lookupName env "%indvars.iv.i" = some (.int 64 ivb))
    (hcv : lookupName env "%shr.i" = some (.int 128 cv))
    (hmw : lookupName env "%conv3.i" = some (.int 128 mw))
    (hpos : ivn.toNat < 2 ^ 63)
    (hread : readBytes s.mem (a + ivn.toNat * (Ty.int 64).sizeBytes) 8 =
      some (natToBytes x.toNat 8)) :
    denoteCode calls stkMulLimb1Instrs (stateAt env s) =
      some (stateAt (stkMulLimb1Env env a ivn ivb cv mw x)
        (stkMulLimbState s a ivn cv mw x)) := by
  unfold stkMulLimb1Instrs stkMulLimb1Env stkMulLimbState
  stk_block_eval

/-- The third limb step. -/
def stkMulLimb2Instrs : List Instr :=
  [Instr.gep "%arrayidx.i.2" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%indvars.iv.next.i.1"),
   Instr.load "%5" (Ty.int 64) (Operand.reg "%arrayidx.i.2"),
   Instr.zext "%conv2.i.2" 64 128 (Operand.reg "%5"),
   Instr.binop "%mul.i.2" (BinOp.mul) 128 (Operand.reg "%conv2.i.2") (Operand.reg "%conv3.i"),
   Instr.binop "%add4.i.2" (BinOp.add) 128 (Operand.reg "%mul.i.2") (Operand.reg "%shr.i.1"),
   Instr.trunc "%conv5.i.2" 128 64 (Operand.reg "%add4.i.2"),
   Instr.store (Ty.int 64) (Operand.reg "%conv5.i.2") (Operand.reg "%arrayidx.i.2"),
   Instr.binop "%shr.i.2" (BinOp.lshr) 128 (Operand.reg "%add4.i.2")
     (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
   Instr.binop "%indvars.iv.next.i.2" (BinOp.or) 64 (Operand.reg "%indvars.iv.i")
     (Operand.imm (Const.int 64 0x0000000000000003#64))]

/-- The third limb step's cells. -/
def stkMulLimb2Env (env : Env) (a : Nat) (ivn ivb : BitVec 64) (cv mw : BitVec 128)
    (x : BitVec 64) : Env :=
  let t : BitVec 128 := BitVec.ofNat 128 x.toNat * mw + cv
  ("%indvars.iv.next.i.2", .int 64 (ivb ||| 0x0000000000000003#64)) ::
  ("%shr.i.2", .int 128 (t >>> 64)) ::
  ("%conv5.i.2", .int 64 (BitVec.ofNat 64 (t.toNat % 2 ^ 64))) ::
  ("%add4.i.2", .int 128 t) ::
  ("%mul.i.2", .int 128 (BitVec.ofNat 128 x.toNat * mw)) ::
  ("%conv2.i.2", .int 128 (BitVec.ofNat 128 x.toNat)) ::
  ("%5", .int 64 x) ::
  ("%arrayidx.i.2", .ptr (a + ivn.toNat * (Ty.int 64).sizeBytes)) :: env

/-- The third limb step's chain. -/
theorem stkMul_limb2_denote {calls : Calls} {env : Env} {s : State}
    {a : Nat} {ivn ivb x : BitVec 64} {cv mw : BitVec 128}
    (ha : lookupName env "%a" = some (.ptr a))
    (hivn : lookupName env "%indvars.iv.next.i.1" = some (.int 64 ivn))
    (hivb : lookupName env "%indvars.iv.i" = some (.int 64 ivb))
    (hcv : lookupName env "%shr.i.1" = some (.int 128 cv))
    (hmw : lookupName env "%conv3.i" = some (.int 128 mw))
    (hpos : ivn.toNat < 2 ^ 63)
    (hread : readBytes s.mem (a + ivn.toNat * (Ty.int 64).sizeBytes) 8 =
      some (natToBytes x.toNat 8)) :
    denoteCode calls stkMulLimb2Instrs (stateAt env s) =
      some (stateAt (stkMulLimb2Env env a ivn ivb cv mw x)
        (stkMulLimbState s a ivn cv mw x)) := by
  unfold stkMulLimb2Instrs stkMulLimb2Env stkMulLimbState
  stk_block_eval

/-- The fourth limb step: the index's `+ 4` is what the next iteration's `phi`
takes. -/
def stkMulLimb3Instrs : List Instr :=
  [Instr.gep "%arrayidx.i.3" (Ty.int 64) (Operand.reg "%a") (Operand.reg "%indvars.iv.next.i.2"),
   Instr.load "%6" (Ty.int 64) (Operand.reg "%arrayidx.i.3"),
   Instr.zext "%conv2.i.3" 64 128 (Operand.reg "%6"),
   Instr.binop "%mul.i.3" (BinOp.mul) 128 (Operand.reg "%conv2.i.3") (Operand.reg "%conv3.i"),
   Instr.binop "%add4.i.3" (BinOp.add) 128 (Operand.reg "%mul.i.3") (Operand.reg "%shr.i.2"),
   Instr.trunc "%conv5.i.3" 128 64 (Operand.reg "%add4.i.3"),
   Instr.store (Ty.int 64) (Operand.reg "%conv5.i.3") (Operand.reg "%arrayidx.i.3"),
   Instr.binop "%shr.i.3" (BinOp.lshr) 128 (Operand.reg "%add4.i.3")
     (Operand.imm (Const.int 128 0x00000000000000000000000000000040#128)),
   Instr.binop "%indvars.iv.next.i.3" (BinOp.add) 64 (Operand.reg "%indvars.iv.i")
     (Operand.imm (Const.int 64 0x0000000000000004#64))]

/-- The fourth limb step's cells. -/
def stkMulLimb3Env (env : Env) (a : Nat) (ivn ivb : BitVec 64) (cv mw : BitVec 128)
    (x : BitVec 64) : Env :=
  let t : BitVec 128 := BitVec.ofNat 128 x.toNat * mw + cv
  ("%indvars.iv.next.i.3", .int 64 (ivb + 0x0000000000000004#64)) ::
  ("%shr.i.3", .int 128 (t >>> 64)) ::
  ("%conv5.i.3", .int 64 (BitVec.ofNat 64 (t.toNat % 2 ^ 64))) ::
  ("%add4.i.3", .int 128 t) ::
  ("%mul.i.3", .int 128 (BitVec.ofNat 128 x.toNat * mw)) ::
  ("%conv2.i.3", .int 128 (BitVec.ofNat 128 x.toNat)) ::
  ("%6", .int 64 x) ::
  ("%arrayidx.i.3", .ptr (a + ivn.toNat * (Ty.int 64).sizeBytes)) :: env

/-- The fourth limb step's chain. -/
theorem stkMul_limb3_denote {calls : Calls} {env : Env} {s : State}
    {a : Nat} {ivn ivb x : BitVec 64} {cv mw : BitVec 128}
    (ha : lookupName env "%a" = some (.ptr a))
    (hivn : lookupName env "%indvars.iv.next.i.2" = some (.int 64 ivn))
    (hivb : lookupName env "%indvars.iv.i" = some (.int 64 ivb))
    (hcv : lookupName env "%shr.i.2" = some (.int 128 cv))
    (hmw : lookupName env "%conv3.i" = some (.int 128 mw))
    (hpos : ivn.toNat < 2 ^ 63)
    (hread : readBytes s.mem (a + ivn.toNat * (Ty.int 64).sizeBytes) 8 =
      some (natToBytes x.toNat 8)) :
    denoteCode calls stkMulLimb3Instrs (stateAt env s) =
      some (stateAt (stkMulLimb3Env env a ivn ivb cv mw x)
        (stkMulLimbState s a ivn cv mw x)) := by
  unfold stkMulLimb3Instrs stkMulLimb3Env stkMulLimbState
  stk_block_eval

/-- The iteration's last two instructions: the group counter and its equality
with the unroll bound. -/
def stkMulTailInstrs : List Instr :=
  [Instr.binop "%niter.next.3" (BinOp.add) 64 (Operand.reg "%niter")
     (Operand.imm (Const.int 64 0x0000000000000004#64)),
   Instr.icmp "%niter.ncmp.3" (IPred.eq) 64 (Operand.reg "%niter.next.3")
     (Operand.reg "%unroll_iter")]

/-- The tail's cells. -/
def stkMulTailEnv (env : Env) (niter unroll : BitVec 64) : Env :=
  ("%niter.ncmp.3", .int 1 (evalICmp .eq (niter + 0x0000000000000004#64) unroll)) ::
  ("%niter.next.3", .int 64 (niter + 0x0000000000000004#64)) :: env

/-- The tail's chain. -/
theorem stkMul_tail_denote {calls : Calls} {env : Env} {s : State}
    {niter unroll : BitVec 64}
    (hn : lookupName env "%niter" = some (.int 64 niter))
    (hu : lookupName env "%unroll_iter" = some (.int 64 unroll)) :
    denoteCode calls stkMulTailInstrs (stateAt env s) =
      some (stateAt (stkMulTailEnv env niter unroll) s) := by
  unfold stkMulTailInstrs stkMulTailEnv
  stk_block_eval

/-- The group iteration's three leading `phi`s. -/
def stkMulGroupPhisInstrs : List Instr :=
  [Instr.phi "%indvars.iv.i" (Ty.int 64) [("for.body.lr.ph.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                 ("for.body.i", (Operand.reg "%indvars.iv.next.i.3"))],
   Instr.phi "%carry.029.i" (Ty.int 128) [("for.body.lr.ph.i.new", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
                                 ("for.body.i", (Operand.reg "%shr.i.3"))],
   Instr.phi "%niter" (Ty.int 64) [("for.body.lr.ph.i.new", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                                 ("for.body.i", (Operand.reg "%niter.next.3"))]]

/-- The group iteration's leading run reads its three words off the edge. -/
theorem stkMul_groupPhis_denote {calls : Calls} {env : Env} {s : State}
    {iv : BitVec 64} {cv : BitVec 128} {niter : BitVec 64}
    (hpre : s.pre = some "for.body.i")
    (hiv : evalOperand (stateAt env s) (.reg "%indvars.iv.next.i.3") = some (.int 64 iv))
    (hcv : evalOperand (stateAt env s) (.reg "%shr.i.3") = some (.int 128 cv))
    (hniter : evalOperand (stateAt env s) (.reg "%niter.next.3") = some (.int 64 niter)) :
    denoteCode calls stkMulGroupPhisInstrs (stateAt env s) =
      some (stateAt
        (("%niter", .int 64 niter) :: ("%carry.029.i", .int 128 cv) ::
          ("%indvars.iv.i", .int 64 iv) :: env) s) := by
  unfold stkMulGroupPhisInstrs
  simp only [denoteCode]
  rw [denoteRun_phi_reg (s := stateAt env s)
      (inc := [("for.body.lr.ph.i.new", .imm (.int 64 0x0000000000000000#64)),
        ("for.body.i", .reg "%indvars.iv.next.i.3")])
      (n := "%indvars.iv.next.i.3") (v := .int 64 iv) hpre (by decide) hiv]
  rw [denoteRun_phi_reg (s := stateAt env s)
      (inc := [("for.body.lr.ph.i.new",
          .imm (.int 128 0x00000000000000000000000000000000#128)),
        ("for.body.i", .reg "%shr.i.3")])
      (n := "%shr.i.3") (v := .int 128 cv) hpre (by decide) hcv]
  rw [denoteRun_phi_reg (s := stateAt env s)
      (inc := [("for.body.lr.ph.i.new", .imm (.int 64 0x0000000000000000#64)),
        ("for.body.i", .reg "%niter.next.3")])
      (n := "%niter.next.3") (v := .int 64 niter) hpre (by decide) hniter]
  rfl

/-- The group iteration's cells, as the four limb steps and the tail compose
them.  The carries are spelled out rather than `let`-bound: the composition's
endpoint is then *syntactically* this term, which is what makes the final `rfl`
cheap — a `let`-shared spelling unfolds into an exponentially larger term on each
side, and the defeq check for it does not fit the heartbeat budget. -/
def stkMulGroupEnv (env : Env) (a : Nat) (iv niter unroll : BitVec 64)
    (cv mw : BitVec 128) (x0 x1 x2 x3 : BitVec 64) : Env :=
  stkMulTailEnv
    (stkMulLimb3Env
      (stkMulLimb2Env
        (stkMulLimb1Env (stkMulLimb0Env env a iv cv mw x0)
          a (iv ||| 0x0000000000000001#64) iv ((BitVec.ofNat 128 x0.toNat * mw + cv) >>> 64) mw x1)
        a (iv ||| 0x0000000000000002#64) iv ((BitVec.ofNat 128 x1.toNat * mw + ((BitVec.ofNat 128 x0.toNat * mw + cv) >>> 64)) >>> 64) mw x2)
      a (iv ||| 0x0000000000000003#64) iv ((BitVec.ofNat 128 x2.toNat * mw + ((BitVec.ofNat 128 x1.toNat * mw + ((BitVec.ofNat 128 x0.toNat * mw + cv) >>> 64)) >>> 64)) >>> 64) mw x3) niter unroll

/-- The group iteration's state, as the four limb steps write it — the carries
spelled out, for the reason `stkMulGroupEnv` carries. -/
def stkMulGroupState (s : State) (a : Nat) (iv : BitVec 64) (cv mw : BitVec 128)
    (x0 x1 x2 x3 : BitVec 64) : State :=
  stkMulLimbState
    (stkMulLimbState
      (stkMulLimbState (stkMulLimbState s a iv cv mw x0)
        a (iv ||| 0x0000000000000001#64) ((BitVec.ofNat 128 x0.toNat * mw + cv) >>> 64) mw x1)
      a (iv ||| 0x0000000000000002#64) ((BitVec.ofNat 128 x1.toNat * mw + ((BitVec.ofNat 128 x0.toNat * mw + cv) >>> 64)) >>> 64) mw x2)
    a (iv ||| 0x0000000000000003#64) ((BitVec.ofNat 128 x2.toNat * mw + ((BitVec.ofNat 128 x1.toNat * mw + ((BitVec.ofNat 128 x0.toNat * mw + cv) >>> 64)) >>> 64)) >>> 64) mw x3

/-! ### The exit

`stk_mul_add.exit` is empty and returns `void`. -/

theorem stkMul_exit_denote {calls : Calls} {env : Env} {s : State} :
    denoteCode calls stkMulStkMulAddExitInstrs (stateAt env s) = some (stateAt env s) := by
  unfold stkMulStkMulAddExitInstrs
  rfl

end LeanLLVM.Refinement
