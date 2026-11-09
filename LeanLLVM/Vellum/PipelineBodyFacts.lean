/-
The assembled pipeline's body facts: the arm traces, the loop instance, the seed
and the tail.

`JsonPipelineBlockEval` closes one arm of the loop body — the copy `arm & 1 = 0`,
`arm & 2 = 0` selects, `for.body.us.us` — as the automation's sufficiency
measurement.  The body has four copies, because the emission unswitches the loop
once per value of the `arm` selector's low two bits: `arm & 1` selects the entry
emitter (POS8 at zero, B8 at one) and `arm & 2` the escape-list gate (off at zero,
on at one).  The three remaining copies are `for.body.us` (POS8, gate on),
`for.body.us83` (B8, gate off) and `for.body` (B8, gate on), and this module
closes them the same way: the instruction lists are pinned back to
`JsonPipelineIR`'s AST by `decide`, the incoming and outgoing builders name the
block's own cells, and one `block_eval` invocation derives the chain and closes
its side goals.

**What the arm traces carry and what stays the caller's.**  A block proof is
`denoteCode calls block.instrs (stateAt envIn s) = some (stateAt envOut s')`.
What remains a hypothesis is the semantic staging no block proof can discharge —
the memory the loads read, the `getelementptr` address bound, and the call
outcomes; and the outcomes are hypotheses here because the units behind them are
the caller's records, consumed one level up by the loop instance.  No register
lookup is a hypothesis: the builders hold the values the statement names.

**The dispatch blocks and the tail.**  The seed crosses the entry test's two
selection blocks before the loop's first iteration, and the tail crosses the
loop's exit, the UTF-8 stage's call, the refusal branches and the final `phi`;
those blocks' traces are here too, and their call and 32-bit-arithmetic shapes
are the chain steps the first arm's blocks do not contain.  A traced block plus
its terminator is one control step, so each of the four arms also comes with its
iteration lemma: one `runFuel` prefix from the arm's head to either the exit or
the next iteration's head, at cost one, in the shape `PipelineLoop.step` asks for.

**The environment bridge, built to the read set.**  A block trace is stated at
`stateAt envIn s`, and the builders *prepend* every register the block reads,
including the caller's own cells that `EntryState` already binds.  Two
consecutive traces therefore state their states over different environment
lists, and no trace applies to the state the previous block leaves.  What two
such states do share is what the block reads, so the bridge is stated that way:
`AgreeOn ns t s` is `State.AgreeOn` — "same memory, allocator base and
predecessor, and the same value for every name in `ns`" — instantiated at the
read set `instrsUses` computes for a block, and the transport is
`denoteCode_transport`: a completed trace at one state gives a completed one at
any state that agrees on that read set.  The per-instruction step behind it
(`evalInstr_agree`) and its preservation lemmas live beside the semantics, in
`LeanLLVM.Semantics`, because a congruence over environments is a fact about
`evalInstr` rather than about this pipeline; the `AgreeOn` constructors kept here
are the names this module's axiom pins read.

**What is not here.**  The three `PipelineBodyFacts` fields — the loop
instance, the seed and the tail.  What is here for them is the arm dispatch: the
four traces moved by `denoteCode_agree` to the state a step actually hands on,
one iteration each, and the semantics facts that move needs (`denoteCode_pc`,
`blockUses`).  The fields' remaining obligations are stated clause by clause at
the end of the module, beside the lemmas that consume them, so a later reader
starts from the obstruction rather than rediscovering it.
-/
import LeanLLVM.Vellum.JsonPipelineBlockEval
import LeanLLVM.Vellum.JsonPipelineRefine
import LeanLLVM.Vellum.JsonEscapeListContract
import LeanLLVM.Vellum.JsonEntrySteps

set_option autoImplicit false
set_option maxRecDepth 16000

namespace LeanLLVM.Vellum

open LeanLLVM
open LeanLLVM.Vellum.JsonPipelineIR (pipelineBody lit)

namespace PipelineBodyFacts

open LeanLLVM.Vellum.BlockEval
open LeanLLVM.Vellum.JsonPipelineBlockEval

/-! ### The three remaining loop-body blocks

The blocks by index in the pinned AST, as `JsonPipelineBlockEval` names its own
three: `blockAt` is the AST's list, and `decide` pins each name to its index. -/

/-- POS8 with the escape-list gate on. -/
def pUs := blockAt pipelineBody 4 (by decide)

/-- B8 with the escape-list gate off. -/
def pUs83 := blockAt pipelineBody 6 (by decide)

/-- B8 with the escape-list gate on. -/
def pBody := blockAt pipelineBody 8 (by decide)

theorem findBlock_us : pipelineBody.findBlock "for.body.us" = some pUs := by decide

theorem findBlock_us83 : pipelineBody.findBlock "for.body.us83" = some pUs83 := by
  decide

theorem findBlock_body : pipelineBody.findBlock "for.body" = some pBody := by decide

/-! ### The pinned instruction lists

Restated from `JsonPipelineIR.pipelineBody` and decided back against it, as the
first arm's three blocks are: a change to the fixture that moved an instruction
fails here rather than becoming a proof obligation elsewhere. -/

theorem pUs_instrs :
    pUs.instrs =
      [Instr.phi "%prevS.082.us" (Ty.int 64)
          [("for.body.us", Operand.reg "%shr13.us"),
           ("for.body.lr.ph.split.us", lit 64 0)],
       Instr.phi "%k.081.us" (Ty.int 64)
          [("for.body.us", Operand.reg "%call21.us"),
           ("for.body.lr.ph.split.us", Operand.reg "%0")],
       Instr.phi "%i.080.us" (Ty.int 64)
          [("for.body.us", Operand.reg "%inc.us"),
           ("for.body.lr.ph.split.us", lit 64 0)],
       Instr.binop "%shl.us" (BinOp.shl) 64 (Operand.reg "%i.080.us") (lit 64 6),
       Instr.gep "%add.ptr.us" (Ty.int 8) (Operand.reg "%b") (Operand.reg "%shl.us"),
       Instr.callVoid "leanllvm_json_s1_masks"
          [(Ty.ptr, Operand.reg "%add.ptr.us"), (Ty.ptr, Operand.reg "%sc"),
           (Ty.ptr, Operand.reg "%mk")],
       Instr.load "%8" (Ty.int 64) (Operand.reg "%mk"),
       Instr.load "%9" (Ty.int 64) (Operand.reg "%delim"),
       Instr.load "%10" (Ty.int 64) (Operand.reg "%in_string"),
       Instr.load "%11" (Ty.int 64) (Operand.reg "%ws"),
       Instr.binop "%12" (BinOp.or) 64 (Operand.reg "%8") (Operand.reg "%11"),
       Instr.binop "%13" (BinOp.or) 64 (Operand.reg "%12") (Operand.reg "%9"),
       Instr.binop "%or2.us" (BinOp.or) 64 (Operand.reg "%13") (Operand.reg "%10"),
       Instr.binop "%not.us" (BinOp.xor) 64 (Operand.reg "%or2.us") (lit 64 (-1)),
       Instr.binop "%not6.us" (BinOp.xor) 64 (Operand.reg "%10") (lit 64 (-1)),
       Instr.binop "%and.us" (BinOp.and) 64 (Operand.reg "%9") (Operand.reg "%not6.us"),
       Instr.binop "%shl8.us" (BinOp.shl) 64 (Operand.reg "%not.us") (lit 64 1),
       Instr.binop "%or9.us" (BinOp.or) 64 (Operand.reg "%shl8.us")
          (Operand.reg "%prevS.082.us"),
       Instr.binop "%not10.us" (BinOp.xor) 64 (Operand.reg "%or9.us") (lit 64 (-1)),
       Instr.binop "%and11.us" (BinOp.and) 64 (Operand.reg "%not10.us")
          (Operand.reg "%not.us"),
       Instr.binop "%14" (BinOp.or) 64 (Operand.reg "%and.us") (Operand.reg "%and11.us"),
       Instr.binop "%or12.us" (BinOp.or) 64 (Operand.reg "%14") (Operand.reg "%8"),
       Instr.binop "%shr13.us" (BinOp.lshr) 64 (Operand.reg "%not.us") (lit 64 63),
       Instr.binop "%sub.us" (BinOp.sub) 64 (Operand.reg "%n") (Operand.reg "%shl.us"),
       Instr.icmp "%cmp15.us" (IPred.ult) 64 (Operand.reg "%sub.us") (lit 64 64),
       Instr.binop "%notmask.us" (BinOp.shl) 64 (lit 64 (-1)) (Operand.reg "%sub.us"),
       Instr.binop "%sub17.us" (BinOp.xor) 64 (Operand.reg "%notmask.us") (lit 64 (-1)),
       Instr.select "%and18.us" (Ty.int 64) (Operand.reg "%cmp15.us")
          (Operand.reg "%sub17.us") (lit 64 (-1)),
       Instr.binop "%ent.0.us" (BinOp.and) 64 (Operand.reg "%or12.us")
          (Operand.reg "%and18.us"),
       Instr.store (Ty.int 64) (Operand.reg "%ent.0.us") (Operand.reg "%entw"),
       Instr.call "%call21.us" (Ty.int 64) "leanllvm_json_entry_pos8"
          [(Ty.ptr, Operand.reg "%entw"), (Ty.int 64, Operand.reg "%i.080.us"),
           (Ty.int 64, lit 64 1), (Ty.ptr, Operand.reg "%ep"),
           (Ty.int 64, Operand.reg "%k.081.us")],
       Instr.load "%15" (Ty.int 64) (Operand.reg "%backslash"),
       Instr.load "%16" (Ty.int 64) (Operand.reg "%ctl"),
       Instr.load "%17" (Ty.int 64) (Operand.reg "%in_string"),
       Instr.callVoid "leanllvm_json_escape_list"
          [(Ty.int 64, Operand.reg "%15"), (Ty.int 64, Operand.reg "%16"),
           (Ty.int 64, Operand.reg "%17"), (Ty.int 64, Operand.reg "%i.080.us"),
           (Ty.ptr, Operand.reg "%xp"), (Ty.ptr, Operand.reg "%nxp"),
           (Ty.ptr, Operand.reg "%xcarry")],
       Instr.binop "%inc.us" (BinOp.add) 64 (Operand.reg "%i.080.us") (lit 64 1),
       Instr.icmp "%exitcond115.not" (IPred.eq) 64 (Operand.reg "%inc.us")
          (Operand.reg "%shr")] := by
  decide

theorem pUs83_instrs :
    pUs83.instrs =
      [Instr.phi "%prevS.082.us84" (Ty.int 64)
          [("for.body.us83", Operand.reg "%shr13.us98"),
           ("for.body.lr.ph.split", lit 64 0)],
       Instr.phi "%k.081.us85" (Ty.int 64)
          [("for.body.us83", Operand.reg "%call.us"),
           ("for.body.lr.ph.split", Operand.reg "%0")],
       Instr.phi "%i.080.us86" (Ty.int 64)
          [("for.body.us83", Operand.reg "%inc.us106"),
           ("for.body.lr.ph.split", lit 64 0)],
       Instr.binop "%shl.us87" (BinOp.shl) 64 (Operand.reg "%i.080.us86") (lit 64 6),
       Instr.gep "%add.ptr.us88" (Ty.int 8) (Operand.reg "%b")
          (Operand.reg "%shl.us87"),
       Instr.callVoid "leanllvm_json_s1_masks"
          [(Ty.ptr, Operand.reg "%add.ptr.us88"), (Ty.ptr, Operand.reg "%sc"),
           (Ty.ptr, Operand.reg "%mk")],
       Instr.load "%18" (Ty.int 64) (Operand.reg "%mk"),
       Instr.load "%19" (Ty.int 64) (Operand.reg "%delim"),
       Instr.load "%20" (Ty.int 64) (Operand.reg "%in_string"),
       Instr.load "%21" (Ty.int 64) (Operand.reg "%ws"),
       Instr.binop "%22" (BinOp.or) 64 (Operand.reg "%18") (Operand.reg "%21"),
       Instr.binop "%23" (BinOp.or) 64 (Operand.reg "%22") (Operand.reg "%19"),
       Instr.binop "%or2.us89" (BinOp.or) 64 (Operand.reg "%23")
          (Operand.reg "%20"),
       Instr.binop "%not.us90" (BinOp.xor) 64 (Operand.reg "%or2.us89") (lit 64 (-1)),
       Instr.binop "%not6.us91" (BinOp.xor) 64 (Operand.reg "%20") (lit 64 (-1)),
       Instr.binop "%and.us92" (BinOp.and) 64 (Operand.reg "%19")
          (Operand.reg "%not6.us91"),
       Instr.binop "%shl8.us93" (BinOp.shl) 64 (Operand.reg "%not.us90") (lit 64 1),
       Instr.binop "%or9.us94" (BinOp.or) 64 (Operand.reg "%shl8.us93")
          (Operand.reg "%prevS.082.us84"),
       Instr.binop "%not10.us95" (BinOp.xor) 64 (Operand.reg "%or9.us94") (lit 64 (-1)),
       Instr.binop "%and11.us96" (BinOp.and) 64 (Operand.reg "%not10.us95")
          (Operand.reg "%not.us90"),
       Instr.binop "%24" (BinOp.or) 64 (Operand.reg "%and.us92")
          (Operand.reg "%and11.us96"),
       Instr.binop "%or12.us97" (BinOp.or) 64 (Operand.reg "%24") (Operand.reg "%18"),
       Instr.binop "%shr13.us98" (BinOp.lshr) 64 (Operand.reg "%not.us90") (lit 64 63),
       Instr.binop "%sub.us99" (BinOp.sub) 64 (Operand.reg "%n")
          (Operand.reg "%shl.us87"),
       Instr.icmp "%cmp15.us100" (IPred.ult) 64 (Operand.reg "%sub.us99") (lit 64 64),
       Instr.binop "%notmask.us101" (BinOp.shl) 64 (lit 64 (-1))
          (Operand.reg "%sub.us99"),
       Instr.binop "%sub17.us102" (BinOp.xor) 64 (Operand.reg "%notmask.us101")
          (lit 64 (-1)),
       Instr.select "%and18.us103" (Ty.int 64) (Operand.reg "%cmp15.us100")
          (Operand.reg "%sub17.us102") (lit 64 (-1)),
       Instr.binop "%ent.0.us104" (BinOp.and) 64 (Operand.reg "%or12.us97")
          (Operand.reg "%and18.us103"),
       Instr.store (Ty.int 64) (Operand.reg "%ent.0.us104") (Operand.reg "%entw"),
       Instr.call "%call.us" (Ty.int 64) "leanllvm_json_entry_b8"
          [(Ty.ptr, Operand.reg "%entw"), (Ty.int 64, Operand.reg "%i.080.us86"),
           (Ty.int 64, lit 64 1), (Ty.ptr, Operand.reg "%ep"),
           (Ty.int 64, Operand.reg "%k.081.us85")],
       Instr.binop "%inc.us106" (BinOp.add) 64 (Operand.reg "%i.080.us86")
          (lit 64 1),
       Instr.icmp "%exitcond114.not" (IPred.eq) 64 (Operand.reg "%inc.us106")
          (Operand.reg "%shr")] := by
  decide

theorem pBody_instrs :
    pBody.instrs =
      [Instr.phi "%prevS.082" (Ty.int 64)
          [("for.body", Operand.reg "%shr13"), ("for.body.lr.ph.split", lit 64 0)],
       Instr.phi "%k.081" (Ty.int 64)
          [("for.body", Operand.reg "%call"),
           ("for.body.lr.ph.split", Operand.reg "%0")],
       Instr.phi "%i.080" (Ty.int 64)
          [("for.body", Operand.reg "%inc"),
           ("for.body.lr.ph.split", lit 64 0)],
       Instr.binop "%shl" (BinOp.shl) 64 (Operand.reg "%i.080") (lit 64 6),
       Instr.gep "%add.ptr" (Ty.int 8) (Operand.reg "%b") (Operand.reg "%shl"),
       Instr.callVoid "leanllvm_json_s1_masks"
          [(Ty.ptr, Operand.reg "%add.ptr"), (Ty.ptr, Operand.reg "%sc"),
           (Ty.ptr, Operand.reg "%mk")],
       Instr.load "%27" (Ty.int 64) (Operand.reg "%mk"),
       Instr.load "%28" (Ty.int 64) (Operand.reg "%delim"),
       Instr.load "%29" (Ty.int 64) (Operand.reg "%in_string"),
       Instr.load "%30" (Ty.int 64) (Operand.reg "%ws"),
       Instr.binop "%31" (BinOp.or) 64 (Operand.reg "%27") (Operand.reg "%30"),
       Instr.binop "%32" (BinOp.or) 64 (Operand.reg "%31") (Operand.reg "%28"),
       Instr.binop "%or2" (BinOp.or) 64 (Operand.reg "%32") (Operand.reg "%29"),
       Instr.binop "%not" (BinOp.xor) 64 (Operand.reg "%or2") (lit 64 (-1)),
       Instr.binop "%not6" (BinOp.xor) 64 (Operand.reg "%29") (lit 64 (-1)),
       Instr.binop "%and" (BinOp.and) 64 (Operand.reg "%28") (Operand.reg "%not6"),
       Instr.binop "%shl8" (BinOp.shl) 64 (Operand.reg "%not") (lit 64 1),
       Instr.binop "%or9" (BinOp.or) 64 (Operand.reg "%shl8")
          (Operand.reg "%prevS.082"),
       Instr.binop "%not10" (BinOp.xor) 64 (Operand.reg "%or9") (lit 64 (-1)),
       Instr.binop "%and11" (BinOp.and) 64 (Operand.reg "%not10")
          (Operand.reg "%not"),
       Instr.binop "%33" (BinOp.or) 64 (Operand.reg "%and") (Operand.reg "%and11"),
       Instr.binop "%or12" (BinOp.or) 64 (Operand.reg "%33") (Operand.reg "%27"),
       Instr.binop "%shr13" (BinOp.lshr) 64 (Operand.reg "%not") (lit 64 63),
       Instr.binop "%sub" (BinOp.sub) 64 (Operand.reg "%n") (Operand.reg "%shl"),
       Instr.icmp "%cmp15" (IPred.ult) 64 (Operand.reg "%sub") (lit 64 64),
       Instr.binop "%notmask" (BinOp.shl) 64 (lit 64 (-1)) (Operand.reg "%sub"),
       Instr.binop "%sub17" (BinOp.xor) 64 (Operand.reg "%notmask") (lit 64 (-1)),
       Instr.select "%and18" (Ty.int 64) (Operand.reg "%cmp15")
          (Operand.reg "%sub17") (lit 64 (-1)),
       Instr.binop "%ent.0" (BinOp.and) 64 (Operand.reg "%or12")
          (Operand.reg "%and18"),
       Instr.store (Ty.int 64) (Operand.reg "%ent.0") (Operand.reg "%entw"),
       Instr.call "%call" (Ty.int 64) "leanllvm_json_entry_b8"
          [(Ty.ptr, Operand.reg "%entw"), (Ty.int 64, Operand.reg "%i.080"),
           (Ty.int 64, lit 64 1), (Ty.ptr, Operand.reg "%ep"),
           (Ty.int 64, Operand.reg "%k.081")],
       Instr.load "%34" (Ty.int 64) (Operand.reg "%backslash"),
       Instr.load "%35" (Ty.int 64) (Operand.reg "%ctl"),
       Instr.load "%36" (Ty.int 64) (Operand.reg "%in_string"),
       Instr.callVoid "leanllvm_json_escape_list"
          [(Ty.int 64, Operand.reg "%34"), (Ty.int 64, Operand.reg "%35"),
           (Ty.int 64, Operand.reg "%36"), (Ty.int 64, Operand.reg "%i.080"),
           (Ty.ptr, Operand.reg "%xp"), (Ty.ptr, Operand.reg "%nxp"),
           (Ty.ptr, Operand.reg "%xcarry")],
       Instr.binop "%inc" (BinOp.add) 64 (Operand.reg "%i.080") (lit 64 1),
       Instr.icmp "%exitcond.not" (IPred.eq) 64 (Operand.reg "%inc")
          (Operand.reg "%shr")] := by
  decide

/-- The POS8-with-gate body's terminator. -/
theorem pUs_term :
    pUs.term = Term.condbr (Operand.reg "%exitcond115.not") "for.cond.cleanup"
      "for.body.us" := by decide

/-- The B8-no-gate body's terminator. -/
theorem pUs83_term :
    pUs83.term = Term.condbr (Operand.reg "%exitcond114.not") "for.cond.cleanup"
      "for.body.us83" := by decide

/-- The B8-with-gate body's terminator. -/
theorem pBody_term :
    pBody.term = Term.condbr (Operand.reg "%exitcond.not") "for.cond.cleanup"
      "for.body" := by decide

/-! ### The further chain steps the gate-on arms and the tail contain

`BlockEval`'s chain steps are the shapes the first arm's blocks contain: a
three-pointer void call, a five-argument call whose third argument is a literal,
`getelementptr` at a register index, and 64-bit arithmetic.  The gate-on arms add
the escape list's seven-argument void call; the dispatch blocks add
`getelementptr` at a literal index; and the tail adds UTF-8's three-argument call,
stage 2's thirteen-argument call, and `for.cond.cleanup`'s 32-bit shift and mask.
Those shapes are stated here, one chain step each, so a block that contains them
is still one `pipeline_block_eval` invocation.  The two 32-bit steps are the
64-bit ones at an arbitrary width, which is what `for.cond.cleanup`'s `%26` and
`%conv` need. -/

/-- `%d = lshr iW %a, <c>`, at any width. -/
theorem step_lshr_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) :
    evalInstr calls (stateAt env s) (.binop d .lshr w (.reg a) (.imm (.int w c))) =
      some (stateAt ((d, .int w (x >>> c.toNat)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using LeanLLVM.Vellum.JsonS1MasksIR.evalInstr_binop (r := (x >>> c.toNat).toNat)
      (ha := LeanLLVM.Vellum.BlockEval.evalOperand_reg_of env s a (.int w x) ha)
      (hb := LeanLLVM.Vellum.BlockEval.evalOperand_lit_of _ w c)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- `%d = and iW %a, <c>`, at any width. -/
theorem step_and_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) :
    evalInstr calls (stateAt env s) (.binop d .and w (.reg a) (.imm (.int w c))) =
      some (stateAt ((d, .int w (x &&& c)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using LeanLLVM.Vellum.JsonS1MasksIR.evalInstr_binop (r := (x &&& c).toNat)
      (ha := LeanLLVM.Vellum.BlockEval.evalOperand_reg_of env s a (.int w x) ha)
      (hb := LeanLLVM.Vellum.BlockEval.evalOperand_lit_of _ w c)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

theorem denoteCode_lshr_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) (is : List Instr) :
    denoteCode calls (.binop d .lshr w (.reg a) (.imm (.int w c)) :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (x >>> c.toNat)) :: env) s) := by
  rw [LeanLLVM.Vellum.BlockEval.denoteCode_cons_of _ _ _ _ _ (step_lshr_imm_w calls env s d a w ha)]

theorem denoteCode_and_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) (is : List Instr) :
    denoteCode calls (.binop d .and w (.reg a) (.imm (.int w c)) :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (x &&& c)) :: env) s) := by
  rw [LeanLLVM.Vellum.BlockEval.denoteCode_cons_of _ _ _ _ _ (step_and_imm_w calls env s d a w ha)]

/-- `%d = getelementptr i8, ptr %base, <c>`, at a literal index below `2 ^ 63`. -/
theorem step_gep8_lit (calls : Calls) (env : Env) (s : State) (d base : String)
    {a : Nat} {w : Nat} {n : BitVec w}
    (hb : lookupName env base = some (.ptr a))
    (hpos : (n.signExtend 64).toNat < 2 ^ 63) :
    evalInstr calls (stateAt env s) (.gep d (.int 8) (.reg base) (.imm (.int w n))) =
      some (stateAt ((d, .ptr (a + (n.signExtend 64).toNat)) :: env) s) := by
  rw [LeanLLVM.evalInstr_gep_i8 (hb := LeanLLVM.Vellum.BlockEval.evalOperand_reg_of env s base (.ptr a) hb)
    (ho := LeanLLVM.Vellum.BlockEval.evalOperand_lit_of _ w n) (hpos := hpos)]
  simp only [stateAt, State.bind]

theorem denoteCode_gep8_lit (calls : Calls) (env : Env) (s : State) (d base : String)
    {a : Nat} {w : Nat} {n : BitVec w}
    (hb : lookupName env base = some (.ptr a))
    (hpos : (n.signExtend 64).toNat < 2 ^ 63) (is : List Instr) :
    denoteCode calls (.gep d (.int 8) (.reg base) (.imm (.int w n)) :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt ((d, .ptr (a + (n.signExtend 64).toNat)) :: env) s) := by
  rw [LeanLLVM.Vellum.BlockEval.denoteCode_cons_of _ _ _ _ _ (step_gep8_lit calls env s d base hb hpos)]

/-- The escape list's call: seven arguments, four masks then three pointers,
returning nothing. -/
theorem step_callVoid_escape (calls : Calls) (env : Env) (s : State)
    (callee : String) (o1 o2 o3 o4 o5 o6 o7 : String)
    {v1 v2 v3 v4 : BitVec 64} {p1 p2 p3 : Nat} {r : CallOutcome}
    (h1 : lookupName env o1 = some (.int 64 v1))
    (h2 : lookupName env o2 = some (.int 64 v2))
    (h3 : lookupName env o3 = some (.int 64 v3))
    (h4 : lookupName env o4 = some (.int 64 v4))
    (h5 : lookupName env o5 = some (.ptr p1))
    (h6 : lookupName env o6 = some (.ptr p2))
    (h7 : lookupName env o7 = some (.ptr p3))
    (hc : calls callee [.int 64 v1, .int 64 v2, .int 64 v3, .int 64 v4,
      .ptr p1, .ptr p2, .ptr p3] s.mem s.next = some r) :
    evalInstr calls (stateAt env s)
        (.callVoid callee [(Ty.int 64, .reg o1), (Ty.int 64, .reg o2),
          (Ty.int 64, .reg o3), (Ty.int 64, .reg o4), (Ty.ptr, .reg o5),
          (Ty.ptr, .reg o6), (Ty.ptr, .reg o7)]) =
      some (stateAt env { s with mem := r.mem, next := r.next }) := by
  have hargs : evalOperands (stateAt env s)
      [(Ty.int 64, .reg o1), (Ty.int 64, .reg o2), (Ty.int 64, .reg o3),
       (Ty.int 64, .reg o4), (Ty.ptr, .reg o5), (Ty.ptr, .reg o6),
       (Ty.ptr, .reg o7)] =
      some [.int 64 v1, .int 64 v2, .int 64 v3, .int 64 v4,
        .ptr p1, .ptr p2, .ptr p3] := by
    simp only [evalOperands,
      LeanLLVM.Vellum.BlockEval.evalOperand_reg_of env s o1 (.int 64 v1) h1,
      LeanLLVM.Vellum.BlockEval.evalOperand_reg_of env s o2 (.int 64 v2) h2,
      LeanLLVM.Vellum.BlockEval.evalOperand_reg_of env s o3 (.int 64 v3) h3,
      LeanLLVM.Vellum.BlockEval.evalOperand_reg_of env s o4 (.int 64 v4) h4,
      LeanLLVM.Vellum.BlockEval.evalOperand_reg_of env s o5 (.ptr p1) h5,
      LeanLLVM.Vellum.BlockEval.evalOperand_reg_of env s o6 (.ptr p2) h6,
      LeanLLVM.Vellum.BlockEval.evalOperand_reg_of env s o7 (.ptr p3) h7]
  have hc' : calls callee [.int 64 v1, .int 64 v2, .int 64 v3, .int 64 v4,
      .ptr p1, .ptr p2, .ptr p3] (stateAt env s).mem (stateAt env s).next = some r := hc
  simp only [evalInstr, hargs, hc']
  rfl

theorem denoteCode_callVoid_escape (calls : Calls) (env : Env) (s : State)
    (callee : String) (o1 o2 o3 o4 o5 o6 o7 : String)
    {v1 v2 v3 v4 : BitVec 64} {p1 p2 p3 : Nat} {r : CallOutcome}
    (h1 : lookupName env o1 = some (.int 64 v1))
    (h2 : lookupName env o2 = some (.int 64 v2))
    (h3 : lookupName env o3 = some (.int 64 v3))
    (h4 : lookupName env o4 = some (.int 64 v4))
    (h5 : lookupName env o5 = some (.ptr p1))
    (h6 : lookupName env o6 = some (.ptr p2))
    (h7 : lookupName env o7 = some (.ptr p3))
    (hc : calls callee [.int 64 v1, .int 64 v2, .int 64 v3, .int 64 v4,
      .ptr p1, .ptr p2, .ptr p3] s.mem s.next = some r) (is : List Instr) :
    denoteCode calls
        (.callVoid callee [(Ty.int 64, .reg o1), (Ty.int 64, .reg o2),
          (Ty.int 64, .reg o3), (Ty.int 64, .reg o4), (Ty.ptr, .reg o5),
          (Ty.ptr, .reg o6), (Ty.ptr, .reg o7)] :: is) (stateAt env s) =
      denoteCode calls is (stateAt env { s with mem := r.mem, next := r.next }) := by
  rw [LeanLLVM.Vellum.BlockEval.denoteCode_cons_of _ _ _ _ _ (step_callVoid_escape calls env s callee o1 o2 o3
    o4 o5 o6 o7 h1 h2 h3 h4 h5 h6 h7 hc)]

/-- UTF-8's call: a byte base, the length, and the 32-bit gate. -/
theorem step_call_utf8 (calls : Calls) (env : Env) (s : State) (d callee : String)
    (bp np gp : String) {p : Nat} {n : BitVec 64} {g : BitVec 32} {r : CallOutcome}
    (hb : lookupName env bp = some (.ptr p))
    (hn : lookupName env np = some (.int 64 n))
    (hg : lookupName env gp = some (.int 32 g))
    (hc : calls callee [.ptr p, .int 64 n, .int 32 g] s.mem s.next = some r) :
    evalInstr calls (stateAt env s)
        (.call d (Ty.int 64) callee [(Ty.ptr, .reg bp), (Ty.int 64, .reg np),
          (Ty.int 32, .reg gp)]) =
      some (stateAt ((d, r.ret) :: env) { s with mem := r.mem, next := r.next }) := by
  have hargs : evalOperands (stateAt env s)
      [(Ty.ptr, .reg bp), (Ty.int 64, .reg np), (Ty.int 32, .reg gp)] =
      some [.ptr p, .int 64 n, .int 32 g] := by
    simp only [evalOperands,
      LeanLLVM.Vellum.BlockEval.evalOperand_reg_of env s bp (.ptr p) hb,
      LeanLLVM.Vellum.BlockEval.evalOperand_reg_of env s np (.int 64 n) hn,
      LeanLLVM.Vellum.BlockEval.evalOperand_reg_of env s gp (.int 32 g) hg]
  have hc' : calls callee [.ptr p, .int 64 n, .int 32 g]
      (stateAt env s).mem (stateAt env s).next = some r := hc
  simp only [evalInstr, hargs, hc']
  rfl

theorem denoteCode_call_utf8 (calls : Calls) (env : Env) (s : State)
    (d callee : String) (bp np gp : String)
    {p : Nat} {n : BitVec 64} {g : BitVec 32} {r : CallOutcome}
    (hb : lookupName env bp = some (.ptr p))
    (hn : lookupName env np = some (.int 64 n))
    (hg : lookupName env gp = some (.int 32 g))
    (hc : calls callee [.ptr p, .int 64 n, .int 32 g] s.mem s.next = some r)
    (is : List Instr) :
    denoteCode calls
        (.call d (Ty.int 64) callee [(Ty.ptr, .reg bp), (Ty.int 64, .reg np),
          (Ty.int 32, .reg gp)] :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, r.ret) :: env) { s with mem := r.mem, next := r.next }) := by
  rw [LeanLLVM.Vellum.BlockEval.denoteCode_cons_of _ _ _ _ _ (step_call_utf8 calls env s d callee bp np gp
    hb hn hg hc)]

/-- Stage 2's call: the document, the entry stream and its cursor, the escape
list and its cursor, the arena and the event stream, each with its capacity or
cursor slot, and the refusal slot — thirteen arguments, all registers. -/
theorem step_call_stage2 (calls : Calls) (env : Env) (s : State) (d callee : String)
    (rb rn rep rk rxp r37 rdst rdcap rndst rev recap rnev rerr : String)
    {pb pe px pd pn pev pnev perr : Nat} {n k x37 dcap ecap : BitVec 64}
    {r : CallOutcome}
    (h1 : lookupName env rb = some (.ptr pb))
    (h2 : lookupName env rn = some (.int 64 n))
    (h3 : lookupName env rep = some (.ptr pe))
    (h4 : lookupName env rk = some (.int 64 k))
    (h5 : lookupName env rxp = some (.ptr px))
    (h6 : lookupName env r37 = some (.int 64 x37))
    (h7 : lookupName env rdst = some (.ptr pd))
    (h8 : lookupName env rdcap = some (.int 64 dcap))
    (h9 : lookupName env rndst = some (.ptr pn))
    (h10 : lookupName env rev = some (.ptr pev))
    (h11 : lookupName env recap = some (.int 64 ecap))
    (h12 : lookupName env rnev = some (.ptr pnev))
    (h13 : lookupName env rerr = some (.ptr perr))
    (hc : calls callee [.ptr pb, .int 64 n, .ptr pe, .int 64 k, .ptr px,
      .int 64 x37, .ptr pd, .int 64 dcap, .ptr pn, .ptr pev, .int 64 ecap,
      .ptr pnev, .ptr perr] s.mem s.next = some r) :
    evalInstr calls (stateAt env s)
        (.call d (Ty.int 64) callee
          [(Ty.ptr, .reg rb), (Ty.int 64, .reg rn), (Ty.ptr, .reg rep),
           (Ty.int 64, .reg rk), (Ty.ptr, .reg rxp), (Ty.int 64, .reg r37),
           (Ty.ptr, .reg rdst), (Ty.int 64, .reg rdcap), (Ty.ptr, .reg rndst),
           (Ty.ptr, .reg rev), (Ty.int 64, .reg recap), (Ty.ptr, .reg rnev),
           (Ty.ptr, .reg rerr)]) =
      some (stateAt ((d, r.ret) :: env) { s with mem := r.mem, next := r.next }) := by
  have hargs : evalOperands (stateAt env s)
      [(Ty.ptr, .reg rb), (Ty.int 64, .reg rn), (Ty.ptr, .reg rep),
       (Ty.int 64, .reg rk), (Ty.ptr, .reg rxp), (Ty.int 64, .reg r37),
       (Ty.ptr, .reg rdst), (Ty.int 64, .reg rdcap), (Ty.ptr, .reg rndst),
       (Ty.ptr, .reg rev), (Ty.int 64, .reg recap), (Ty.ptr, .reg rnev),
       (Ty.ptr, .reg rerr)] =
      some [.ptr pb, .int 64 n, .ptr pe, .int 64 k, .ptr px, .int 64 x37,
        .ptr pd, .int 64 dcap, .ptr pn, .ptr pev, .int 64 ecap, .ptr pnev,
        .ptr perr] := by
    simp only [evalOperands,
      LeanLLVM.Vellum.BlockEval.evalOperand_reg_of env s rb (.ptr pb) h1,
      LeanLLVM.Vellum.BlockEval.evalOperand_reg_of env s rn (.int 64 n) h2,
      LeanLLVM.Vellum.BlockEval.evalOperand_reg_of env s rep (.ptr pe) h3,
      LeanLLVM.Vellum.BlockEval.evalOperand_reg_of env s rk (.int 64 k) h4,
      LeanLLVM.Vellum.BlockEval.evalOperand_reg_of env s rxp (.ptr px) h5,
      LeanLLVM.Vellum.BlockEval.evalOperand_reg_of env s r37 (.int 64 x37) h6,
      LeanLLVM.Vellum.BlockEval.evalOperand_reg_of env s rdst (.ptr pd) h7,
      LeanLLVM.Vellum.BlockEval.evalOperand_reg_of env s rdcap (.int 64 dcap) h8,
      LeanLLVM.Vellum.BlockEval.evalOperand_reg_of env s rndst (.ptr pn) h9,
      LeanLLVM.Vellum.BlockEval.evalOperand_reg_of env s rev (.ptr pev) h10,
      LeanLLVM.Vellum.BlockEval.evalOperand_reg_of env s recap (.int 64 ecap) h11,
      LeanLLVM.Vellum.BlockEval.evalOperand_reg_of env s rnev (.ptr pnev) h12,
      LeanLLVM.Vellum.BlockEval.evalOperand_reg_of env s rerr (.ptr perr) h13]
  have hc' : calls callee [.ptr pb, .int 64 n, .ptr pe, .int 64 k, .ptr px,
      .int 64 x37, .ptr pd, .int 64 dcap, .ptr pn, .ptr pev, .int 64 ecap,
      .ptr pnev, .ptr perr] (stateAt env s).mem (stateAt env s).next = some r := hc
  simp only [evalInstr, hargs, hc']
  rfl

theorem denoteCode_call_stage2 (calls : Calls) (env : Env) (s : State)
    (d callee : String) (rb rn rep rk rxp r37 rdst rdcap rndst rev recap rnev rerr : String)
    {pb pe px pd pn pev pnev perr : Nat} {n k x37 dcap ecap : BitVec 64}
    {r : CallOutcome}
    (h1 : lookupName env rb = some (.ptr pb))
    (h2 : lookupName env rn = some (.int 64 n))
    (h3 : lookupName env rep = some (.ptr pe))
    (h4 : lookupName env rk = some (.int 64 k))
    (h5 : lookupName env rxp = some (.ptr px))
    (h6 : lookupName env r37 = some (.int 64 x37))
    (h7 : lookupName env rdst = some (.ptr pd))
    (h8 : lookupName env rdcap = some (.int 64 dcap))
    (h9 : lookupName env rndst = some (.ptr pn))
    (h10 : lookupName env rev = some (.ptr pev))
    (h11 : lookupName env recap = some (.int 64 ecap))
    (h12 : lookupName env rnev = some (.ptr pnev))
    (h13 : lookupName env rerr = some (.ptr perr))
    (hc : calls callee [.ptr pb, .int 64 n, .ptr pe, .int 64 k, .ptr px,
      .int 64 x37, .ptr pd, .int 64 dcap, .ptr pn, .ptr pev, .int 64 ecap,
      .ptr pnev, .ptr perr] s.mem s.next = some r) (is : List Instr) :
    denoteCode calls
        (.call d (Ty.int 64) callee
          [(Ty.ptr, .reg rb), (Ty.int 64, .reg rn), (Ty.ptr, .reg rep),
           (Ty.int 64, .reg rk), (Ty.ptr, .reg rxp), (Ty.int 64, .reg r37),
           (Ty.ptr, .reg rdst), (Ty.int 64, .reg rdcap), (Ty.ptr, .reg rndst),
           (Ty.ptr, .reg rev), (Ty.int 64, .reg recap), (Ty.ptr, .reg rnev),
           (Ty.ptr, .reg rerr)] :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, r.ret) :: env) { s with mem := r.mem, next := r.next }) := by
  rw [LeanLLVM.Vellum.BlockEval.denoteCode_cons_of _ _ _ _ _ (step_call_stage2 calls env s d callee rb rn rep
    rk rxp r37 rdst rdcap rndst rev recap rnev rerr h1 h2 h3 h4 h5 h6 h7 h8 h9
    h10 h11 h12 h13 hc)]

/-- The chain steps `BlockEval`'s `block_step` has, plus the five above. -/
macro "pipeline_block_step" : tactic => `(tactic|
  (first
   | rw [denoteCode_callVoid_escape]
   | rw [denoteCode_call_utf8]
   | rw [denoteCode_call_stage2]
   | rw [denoteCode_gep8_lit]
   | rw [denoteCode_lshr_imm_w]
   | rw [denoteCode_and_imm_w]
   | block_step))

/-- `block_close` with the literal-address bounds decided: a `getelementptr` at
a literal index leaves `(c.signExtend 64).toNat < 2 ^ 63`, a concrete comparison
that `block_close`'s phases have no decision step for. -/
macro "pipeline_block_close" : tactic => `(tactic|
  (all_goals (try (simp (config := { failIfUnchanged := false }) only [cells, denoteCode]))
   all_goals (try rfl)
   all_goals (try (first
     | assumption
     | block_lk
     | decide
     | (simp only [phiIncoming]; rfl)
     | rfl
     | (exact LeanLLVM.Vellum.BlockEval.evalOperand_lit_of _ _ _)))
   all_goals (try rfl)))

/-- A whole block with the further shapes: `pipeline_block_step` to the last
instruction, then `pipeline_block_close`. -/
macro "pipeline_block_eval" : tactic => `(tactic|
  (repeat pipeline_block_step
   pipeline_block_close))

/-! ### The POS8-with-gate arm, `for.body.us`

The block's shape is the first arm's with the escape list's three loads and its
void call inserted between the entry call and the increment: the gate is on, so
the same three mask words the entry kernel derived are read back as the list's
`bs`/`ctl`/`im` arguments.  The builders name the block's own cells — `%8`–`%17`
where the first arm has `%1`–`%7` and no escape arm — and the statement's
hypotheses are the caller's staging: four loads after the mask call, three after
the entry call, the address bound, and the three calls' outcomes. -/

/-- The POS8-with-gate body's incoming builder. -/
def usIn (env : Env) (n : BitVec 64) (b sc mk delim inString ws backslash ctl
    entw ep xp nxp xcarry : Nat) (s13 c21 inc shr : BitVec 64) : Env :=
  cells [("%shr", .int 64 shr),
         ("%xcarry", .ptr xcarry), ("%nxp", .ptr nxp), ("%xp", .ptr xp),
         ("%inc.us", .int 64 inc), ("%call21.us", .int 64 c21),
         ("%shr13.us", .int 64 s13),
         ("%ep", .ptr ep), ("%entw", .ptr entw), ("%ctl", .ptr ctl),
         ("%backslash", .ptr backslash), ("%ws", .ptr ws),
         ("%in_string", .ptr inString), ("%delim", .ptr delim), ("%mk", .ptr mk),
         ("%sc", .ptr sc), ("%b", .ptr b), ("%n", .int 64 n)] env

/-- The POS8-with-gate body's outgoing builder: its results newest first, `r2` and
`r3` the entry and escape-list calls' returns (the second is `void`, so it binds
no cell and only its memory is observable). -/
def usOut (env : Env) (n : BitVec 64) (b sc mk delim inString ws backslash ctl
    entw ep xp nxp xcarry : Nat) (s13 c21 inc shr : BitVec 64)
    (w1 w2 w3 w4 w5 w6 w7 : BitVec 64) (ret : Value) : Env :=
  cells [("%exitcond115.not", .int 1 (vexit inc shr)),
         ("%inc.us", .int 64 (vinc inc)),
         ("%17", .int 64 w7), ("%16", .int 64 w6), ("%15", .int 64 w5),
         ("%call21.us", ret),
         ("%ent.0.us", .int 64 (vent n inc w1 w2 w3 w4 s13)),
         ("%and18.us", .int 64 (vand18 n inc)),
         ("%sub17.us", .int 64 (vsub17 n inc)),
         ("%notmask.us", .int 64 (vnotmask n inc)),
         ("%cmp15.us", .int 1 (vcmp n inc)),
         ("%sub.us", .int 64 (vsub n inc)),
         ("%shr13.us", .int 64 (vshr13 w1 w2 w3 w4)),
         ("%or12.us", .int 64 (vor12 w1 w2 w3 w4 s13)),
         ("%14", .int 64 (v7 w1 w2 w3 w4 s13)),
         ("%and11.us", .int 64 (vand11 w1 w2 w3 w4 s13)),
         ("%not10.us", .int 64 (vnot10 w1 w2 w3 w4 s13)),
         ("%or9.us", .int 64 (vor9 w1 w2 w3 w4 s13)),
         ("%shl8.us", .int 64 (vshl8 w1 w2 w3 w4)),
         ("%and.us", .int 64 (vand w2 w3)),
         ("%not6.us", .int 64 (vnot6 w3)),
         ("%not.us", .int 64 (vnot w1 w2 w3 w4)),
         ("%or2.us", .int 64 (vor2 w1 w2 w3 w4)),
         ("%13", .int 64 (v6 w1 w2 w4)), ("%12", .int 64 (v5 w1 w4)),
         ("%11", .int 64 w4), ("%10", .int 64 w3), ("%9", .int 64 w2),
         ("%8", .int 64 w1),
         ("%add.ptr.us", .ptr (b + (BitVec.signExtend 64 (sh6 inc)).toNat)),
         ("%shl.us", .int 64 (sh6 inc)),
         ("%i.080.us", .int 64 inc),
         ("%k.081.us", .int 64 c21),
         ("%prevS.082.us", .int 64 s13)]
    (usIn env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry
      s13 c21 inc shr)

/-- **The POS8-with-gate body derives its chain and closes its side goals.** -/
theorem us_denote (calls : Calls) (env : Env) (s : State) (n : BitVec 64)
    (b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry : Nat)
    (s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 : BitVec 64)
    (r1 r2 r3 : CallOutcome)
    (hpre : s.pre = some "for.body.us")
    (hld1 : readBytes r1.mem mk 8 = some (natToBytes w1.toNat 8))
    (hld2 : readBytes r1.mem delim 8 = some (natToBytes w2.toNat 8))
    (hld3 : readBytes r1.mem inString 8 = some (natToBytes w3.toNat 8))
    (hld4 : readBytes r1.mem ws 8 = some (natToBytes w4.toNat 8))
    (hpos : (BitVec.signExtend 64 (sh6 inc)).toNat < 2 ^ 63)
    (hcall1 : calls "leanllvm_json_s1_masks"
      [.ptr (b + (BitVec.signExtend 64 (sh6 inc)).toNat), .ptr sc, .ptr mk]
      s.mem s.next = some r1)
    (hcall2 : calls "leanllvm_json_entry_pos8"
      [.ptr entw, .int 64 inc, .int 64 1, .ptr ep, .int 64 c21]
      (writeBytes r1.mem entw (natToBytes (vent n inc w1 w2 w3 w4 s13).toNat 8))
      r1.next = some r2)
    (hld5 : readBytes r2.mem backslash 8 = some (natToBytes w5.toNat 8))
    (hld6 : readBytes r2.mem ctl 8 = some (natToBytes w6.toNat 8))
    (hld7 : readBytes r2.mem inString 8 = some (natToBytes w7.toNat 8))
    (hcall3 : calls "leanllvm_json_escape_list"
      [.int 64 w5, .int 64 w6, .int 64 w7, .int 64 inc, .ptr xp, .ptr nxp,
       .ptr xcarry] r2.mem r2.next = some r3) :
    denoteCode calls pUs.instrs
        (stateAt (usIn env n b sc mk delim inString ws backslash ctl entw ep
          xp nxp xcarry s13 c21 inc shr) s) =
      some (stateAt (usOut env n b sc mk delim inString ws backslash ctl entw ep
        xp nxp xcarry s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 r2.ret)
        { s with mem := r3.mem, next := r3.next }) := by
  rw [pUs_instrs]
  simp only [lit, usIn, usOut]
  pipeline_block_eval

/-! ### The B8-no-gate arm, `for.body.us83`

The same shape with the entry emitter switched: `leanllvm_json_entry_b8` at the
same five arguments, and no escape list, so the block's cells are `%18`–`%24` and
the entry result is `%call.us`. -/

/-- The B8-no-gate body's incoming builder. -/
def us83In (env : Env) (n : BitVec 64) (b sc mk delim inString ws entw ep : Nat)
    (s13 c21 inc shr : BitVec 64) : Env :=
  cells [("%shr", .int 64 shr),
         ("%inc.us106", .int 64 inc), ("%call.us", .int 64 c21),
         ("%shr13.us98", .int 64 s13),
         ("%ep", .ptr ep), ("%entw", .ptr entw), ("%ws", .ptr ws),
         ("%in_string", .ptr inString), ("%delim", .ptr delim), ("%mk", .ptr mk),
         ("%sc", .ptr sc), ("%b", .ptr b), ("%n", .int 64 n)] env

/-- The B8-no-gate body's outgoing builder. -/
def us83Out (env : Env) (n : BitVec 64) (b sc mk delim inString ws entw ep : Nat)
    (s13 c21 inc shr : BitVec 64) (w1 w2 w3 w4 : BitVec 64) (ret : Value) : Env :=
  cells [("%exitcond114.not", .int 1 (vexit inc shr)),
         ("%inc.us106", .int 64 (vinc inc)),
         ("%call.us", ret),
         ("%ent.0.us104", .int 64 (vent n inc w1 w2 w3 w4 s13)),
         ("%and18.us103", .int 64 (vand18 n inc)),
         ("%sub17.us102", .int 64 (vsub17 n inc)),
         ("%notmask.us101", .int 64 (vnotmask n inc)),
         ("%cmp15.us100", .int 1 (vcmp n inc)),
         ("%sub.us99", .int 64 (vsub n inc)),
         ("%shr13.us98", .int 64 (vshr13 w1 w2 w3 w4)),
         ("%or12.us97", .int 64 (vor12 w1 w2 w3 w4 s13)),
         ("%24", .int 64 (v7 w1 w2 w3 w4 s13)),
         ("%and11.us96", .int 64 (vand11 w1 w2 w3 w4 s13)),
         ("%not10.us95", .int 64 (vnot10 w1 w2 w3 w4 s13)),
         ("%or9.us94", .int 64 (vor9 w1 w2 w3 w4 s13)),
         ("%shl8.us93", .int 64 (vshl8 w1 w2 w3 w4)),
         ("%and.us92", .int 64 (vand w2 w3)),
         ("%not6.us91", .int 64 (vnot6 w3)),
         ("%not.us90", .int 64 (vnot w1 w2 w3 w4)),
         ("%or2.us89", .int 64 (vor2 w1 w2 w3 w4)),
         ("%23", .int 64 (v6 w1 w2 w4)), ("%22", .int 64 (v5 w1 w4)),
         ("%21", .int 64 w4), ("%20", .int 64 w3), ("%19", .int 64 w2),
         ("%18", .int 64 w1),
         ("%add.ptr.us88", .ptr (b + (BitVec.signExtend 64 (sh6 inc)).toNat)),
         ("%shl.us87", .int 64 (sh6 inc)),
         ("%i.080.us86", .int 64 inc),
         ("%k.081.us85", .int 64 c21),
         ("%prevS.082.us84", .int 64 s13)]
    (us83In env n b sc mk delim inString ws entw ep s13 c21 inc shr)

/-- **The B8-no-gate body derives its chain and closes its side goals.** -/
theorem us83_denote (calls : Calls) (env : Env) (s : State) (n : BitVec 64)
    (b sc mk delim inString ws entw ep : Nat)
    (s13 c21 inc shr w1 w2 w3 w4 : BitVec 64) (r1 r2 : CallOutcome)
    (hpre : s.pre = some "for.body.us83")
    (hld1 : readBytes r1.mem mk 8 = some (natToBytes w1.toNat 8))
    (hld2 : readBytes r1.mem delim 8 = some (natToBytes w2.toNat 8))
    (hld3 : readBytes r1.mem inString 8 = some (natToBytes w3.toNat 8))
    (hld4 : readBytes r1.mem ws 8 = some (natToBytes w4.toNat 8))
    (hpos : (BitVec.signExtend 64 (sh6 inc)).toNat < 2 ^ 63)
    (hcall1 : calls "leanllvm_json_s1_masks"
      [.ptr (b + (BitVec.signExtend 64 (sh6 inc)).toNat), .ptr sc, .ptr mk]
      s.mem s.next = some r1)
    (hcall2 : calls "leanllvm_json_entry_b8"
      [.ptr entw, .int 64 inc, .int 64 1, .ptr ep, .int 64 c21]
      (writeBytes r1.mem entw (natToBytes (vent n inc w1 w2 w3 w4 s13).toNat 8))
      r1.next = some r2) :
    denoteCode calls pUs83.instrs
        (stateAt (us83In env n b sc mk delim inString ws entw ep s13 c21 inc shr) s) =
      some (stateAt (us83Out env n b sc mk delim inString ws entw ep s13 c21 inc shr
        w1 w2 w3 w4 r2.ret) { s with mem := r2.mem, next := r2.next }) := by
  rw [pUs83_instrs]
  simp only [lit, us83In, us83Out]
  pipeline_block_eval

/-! ### The B8-with-gate arm, `for.body`

The B8 emitter with the escape list appended: the block's cells are `%27`–`%36`,
the entry result is `%call`, and the list reads `%34`–`%36`. -/

/-- The B8-with-gate body's incoming builder. -/
def bodyIn (env : Env) (n : BitVec 64) (b sc mk delim inString ws backslash ctl
    entw ep xp nxp xcarry : Nat) (s13 c21 inc shr : BitVec 64) : Env :=
  cells [("%shr", .int 64 shr),
         ("%xcarry", .ptr xcarry), ("%nxp", .ptr nxp), ("%xp", .ptr xp),
         ("%inc", .int 64 inc), ("%call", .int 64 c21),
         ("%shr13", .int 64 s13),
         ("%ep", .ptr ep), ("%entw", .ptr entw), ("%ctl", .ptr ctl),
         ("%backslash", .ptr backslash), ("%ws", .ptr ws),
         ("%in_string", .ptr inString), ("%delim", .ptr delim), ("%mk", .ptr mk),
         ("%sc", .ptr sc), ("%b", .ptr b), ("%n", .int 64 n)] env

/-- The B8-with-gate body's outgoing builder. -/
def bodyOut (env : Env) (n : BitVec 64) (b sc mk delim inString ws backslash ctl
    entw ep xp nxp xcarry : Nat) (s13 c21 inc shr : BitVec 64)
    (w1 w2 w3 w4 w5 w6 w7 : BitVec 64) (ret : Value) : Env :=
  cells [("%exitcond.not", .int 1 (vexit inc shr)),
         ("%inc", .int 64 (vinc inc)),
         ("%36", .int 64 w7), ("%35", .int 64 w6), ("%34", .int 64 w5),
         ("%call", ret),
         ("%ent.0", .int 64 (vent n inc w1 w2 w3 w4 s13)),
         ("%and18", .int 64 (vand18 n inc)),
         ("%sub17", .int 64 (vsub17 n inc)),
         ("%notmask", .int 64 (vnotmask n inc)),
         ("%cmp15", .int 1 (vcmp n inc)),
         ("%sub", .int 64 (vsub n inc)),
         ("%shr13", .int 64 (vshr13 w1 w2 w3 w4)),
         ("%or12", .int 64 (vor12 w1 w2 w3 w4 s13)),
         ("%33", .int 64 (v7 w1 w2 w3 w4 s13)),
         ("%and11", .int 64 (vand11 w1 w2 w3 w4 s13)),
         ("%not10", .int 64 (vnot10 w1 w2 w3 w4 s13)),
         ("%or9", .int 64 (vor9 w1 w2 w3 w4 s13)),
         ("%shl8", .int 64 (vshl8 w1 w2 w3 w4)),
         ("%and", .int 64 (vand w2 w3)),
         ("%not6", .int 64 (vnot6 w3)),
         ("%not", .int 64 (vnot w1 w2 w3 w4)),
         ("%or2", .int 64 (vor2 w1 w2 w3 w4)),
         ("%32", .int 64 (v6 w1 w2 w4)), ("%31", .int 64 (v5 w1 w4)),
         ("%30", .int 64 w4), ("%29", .int 64 w3), ("%28", .int 64 w2),
         ("%27", .int 64 w1),
         ("%add.ptr", .ptr (b + (BitVec.signExtend 64 (sh6 inc)).toNat)),
         ("%shl", .int 64 (sh6 inc)),
         ("%i.080", .int 64 inc),
         ("%k.081", .int 64 c21),
         ("%prevS.082", .int 64 s13)]
    (bodyIn env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry
      s13 c21 inc shr)

/-- **The B8-with-gate body derives its chain and closes its side goals.** -/
theorem body_denote (calls : Calls) (env : Env) (s : State) (n : BitVec 64)
    (b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry : Nat)
    (s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 : BitVec 64)
    (r1 r2 r3 : CallOutcome)
    (hpre : s.pre = some "for.body")
    (hld1 : readBytes r1.mem mk 8 = some (natToBytes w1.toNat 8))
    (hld2 : readBytes r1.mem delim 8 = some (natToBytes w2.toNat 8))
    (hld3 : readBytes r1.mem inString 8 = some (natToBytes w3.toNat 8))
    (hld4 : readBytes r1.mem ws 8 = some (natToBytes w4.toNat 8))
    (hpos : (BitVec.signExtend 64 (sh6 inc)).toNat < 2 ^ 63)
    (hcall1 : calls "leanllvm_json_s1_masks"
      [.ptr (b + (BitVec.signExtend 64 (sh6 inc)).toNat), .ptr sc, .ptr mk]
      s.mem s.next = some r1)
    (hcall2 : calls "leanllvm_json_entry_b8"
      [.ptr entw, .int 64 inc, .int 64 1, .ptr ep, .int 64 c21]
      (writeBytes r1.mem entw (natToBytes (vent n inc w1 w2 w3 w4 s13).toNat 8))
      r1.next = some r2)
    (hld5 : readBytes r2.mem backslash 8 = some (natToBytes w5.toNat 8))
    (hld6 : readBytes r2.mem ctl 8 = some (natToBytes w6.toNat 8))
    (hld7 : readBytes r2.mem inString 8 = some (natToBytes w7.toNat 8))
    (hcall3 : calls "leanllvm_json_escape_list"
      [.int 64 w5, .int 64 w6, .int 64 w7, .int 64 inc, .ptr xp, .ptr nxp,
       .ptr xcarry] r2.mem r2.next = some r3) :
    denoteCode calls pBody.instrs
        (stateAt (bodyIn env n b sc mk delim inString ws backslash ctl entw ep
          xp nxp xcarry s13 c21 inc shr) s) =
      some (stateAt (bodyOut env n b sc mk delim inString ws backslash ctl entw ep
        xp nxp xcarry s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 r2.ret)
        { s with mem := r3.mem, next := r3.next }) := by
  rw [pBody_instrs]
  simp only [lit, bodyIn, bodyOut]
  pipeline_block_eval

/-! ### The first iteration: the split predecessor

The seed's third step leaves `for.body.lr.ph.split.us` or `for.body.lr.ph.split`
for one of the four arm heads, and the arm traces above are stated at the back
edge.  At the first iteration every `phi` selects the split operand instead:
`%prevS` and `%i` take the literal zero and `%k` takes `%0`, the incoming count
the entry block loaded from `%nk`.  The four traces below state the same blocks
at that arrival, so the values the invariant's first state carries are read from
a trace rather than assumed.

The builders bind what the split path reads and nothing else.  The back edge's
three names (`%shr13`, `%call21`, `%inc` and their per-arm spellings) are in the
block's static read set through the self-loop `phi` entries, so binding them in
the first iteration's builder would make it disagree with the dispatch state,
which binds none of them; leaving them unbound on both sides is what lets
`AgreeOn` carry the trace to the state the split block leaves. -/

/-- `for.body.us.us`'s incoming builder at the split predecessor: `%0` (the
count the entry block loaded) and the cells the split path reads. -/
def usUsSplitIn (env : Env) (n : BitVec 64) (b sc mk delim inString ws entw ep : Nat)
    (w0 shr : BitVec 64) : Env :=
  cells [("%shr", .int 64 shr), ("%0", .int 64 w0),
         ("%ep", .ptr ep), ("%entw", .ptr entw), ("%ws", .ptr ws),
         ("%in_string", .ptr inString), ("%delim", .ptr delim), ("%mk", .ptr mk),
         ("%sc", .ptr sc), ("%b", .ptr b), ("%n", .int 64 n)] env

/-- `for.body.us.us`'s outgoing builder at the split predecessor. -/
def usUsSplitOut (env : Env) (n : BitVec 64) (b sc mk delim inString ws entw ep : Nat)
    (w0 shr w1 w2 w3 w4 : BitVec 64) (ret : Value) : Env :=
  cells [("%exitcond116.not", .int 1 (vexit 0 shr)),
         ("%inc.us.us", .int 64 (vinc 0)),
         ("%call21.us.us", ret),
         ("%ent.0.us.us", .int 64 (vent n 0 w1 w2 w3 w4 0)),
         ("%and18.us.us", .int 64 (vand18 n 0)),
         ("%sub17.us.us", .int 64 (vsub17 n 0)),
         ("%notmask.us.us", .int 64 (vnotmask n 0)),
         ("%cmp15.us.us", .int 1 (vcmp n 0)),
         ("%sub.us.us", .int 64 (vsub n 0)),
         ("%shr13.us.us", .int 64 (vshr13 w1 w2 w3 w4)),
         ("%or12.us.us", .int 64 (vor12 w1 w2 w3 w4 0)),
         ("%7", .int 64 (v7 w1 w2 w3 w4 0)),
         ("%and11.us.us", .int 64 (vand11 w1 w2 w3 w4 0)),
         ("%not10.us.us", .int 64 (vnot10 w1 w2 w3 w4 0)),
         ("%or9.us.us", .int 64 (vor9 w1 w2 w3 w4 0)),
         ("%shl8.us.us", .int 64 (vshl8 w1 w2 w3 w4)),
         ("%and.us.us", .int 64 (vand w2 w3)),
         ("%not6.us.us", .int 64 (vnot6 w3)),
         ("%not.us.us", .int 64 (vnot w1 w2 w3 w4)),
         ("%or2.us.us", .int 64 (vor2 w1 w2 w3 w4)),
         ("%6", .int 64 (v6 w1 w2 w4)),
         ("%5", .int 64 (v5 w1 w4)),
         ("%4", .int 64 w4), ("%3", .int 64 w3), ("%2", .int 64 w2),
         ("%1", .int 64 w1),
         ("%add.ptr.us.us", .ptr (b + (BitVec.signExtend 64 (sh6 0)).toNat)),
         ("%shl.us.us", .int 64 (sh6 0)),
         ("%i.080.us.us", .int 64 0),
         ("%k.081.us.us", .int 64 w0),
         ("%prevS.082.us.us", .int 64 0)]
    (usUsSplitIn env n b sc mk delim inString ws entw ep w0 shr)

/-- **`for.body.us.us` from the split predecessor.**  Every `phi` takes the
split operand, so the carried triple is `(0, %0, 0)`. -/
theorem usUs_split_denote (calls : Calls) (env : Env) (s : State) (n : BitVec 64)
    (b sc mk delim inString ws entw ep : Nat)
    (w0 shr w1 w2 w3 w4 : BitVec 64) (r1 r2 : CallOutcome)
    (hpre : s.pre = some "for.body.lr.ph.split.us")
    (hld1 : readBytes r1.mem mk 8 = some (natToBytes w1.toNat 8))
    (hld2 : readBytes r1.mem delim 8 = some (natToBytes w2.toNat 8))
    (hld3 : readBytes r1.mem inString 8 = some (natToBytes w3.toNat 8))
    (hld4 : readBytes r1.mem ws 8 = some (natToBytes w4.toNat 8))
    (hcall1 : calls "leanllvm_json_s1_masks"
      [.ptr (b + (BitVec.signExtend 64 (sh6 (0 : BitVec 64))).toNat), .ptr sc,
       .ptr mk] s.mem s.next = some r1)
    (hcall2 : calls "leanllvm_json_entry_pos8"
      [.ptr entw, .int 64 0, .int 64 1, .ptr ep, .int 64 w0]
      (writeBytes r1.mem entw (natToBytes (vent n 0 w1 w2 w3 w4 0).toNat 8))
      r1.next = some r2) :
    denoteCode calls pUsUs.instrs
        (stateAt (usUsSplitIn env n b sc mk delim inString ws entw ep w0 shr) s) =
      some (stateAt (usUsSplitOut env n b sc mk delim inString ws entw ep w0 shr
        w1 w2 w3 w4 r2.ret) { s with mem := r2.mem, next := r2.next }) := by
  rw [pUsUs_instrs]
  simp only [lit, usUsSplitIn, usUsSplitOut]
  pipeline_block_eval

/-- `for.body.us`'s incoming builder at the split predecessor. -/
def usSplitIn (env : Env) (n : BitVec 64) (b sc mk delim inString ws backslash ctl
    entw ep xp nxp xcarry : Nat) (w0 shr : BitVec 64) : Env :=
  cells [("%shr", .int 64 shr), ("%0", .int 64 w0),
         ("%xcarry", .ptr xcarry), ("%nxp", .ptr nxp), ("%xp", .ptr xp),
         ("%ep", .ptr ep), ("%entw", .ptr entw), ("%ctl", .ptr ctl),
         ("%backslash", .ptr backslash), ("%ws", .ptr ws),
         ("%in_string", .ptr inString), ("%delim", .ptr delim), ("%mk", .ptr mk),
         ("%sc", .ptr sc), ("%b", .ptr b), ("%n", .int 64 n)] env

/-- `for.body.us`'s outgoing builder at the split predecessor. -/
def usSplitOut (env : Env) (n : BitVec 64) (b sc mk delim inString ws backslash ctl
    entw ep xp nxp xcarry : Nat) (w0 shr w1 w2 w3 w4 w5 w6 w7 : BitVec 64)
    (ret : Value) : Env :=
  cells [("%exitcond115.not", .int 1 (vexit 0 shr)),
         ("%inc.us", .int 64 (vinc 0)),
         ("%17", .int 64 w7), ("%16", .int 64 w6), ("%15", .int 64 w5),
         ("%call21.us", ret),
         ("%ent.0.us", .int 64 (vent n 0 w1 w2 w3 w4 0)),
         ("%and18.us", .int 64 (vand18 n 0)),
         ("%sub17.us", .int 64 (vsub17 n 0)),
         ("%notmask.us", .int 64 (vnotmask n 0)),
         ("%cmp15.us", .int 1 (vcmp n 0)),
         ("%sub.us", .int 64 (vsub n 0)),
         ("%shr13.us", .int 64 (vshr13 w1 w2 w3 w4)),
         ("%or12.us", .int 64 (vor12 w1 w2 w3 w4 0)),
         ("%14", .int 64 (v7 w1 w2 w3 w4 0)),
         ("%and11.us", .int 64 (vand11 w1 w2 w3 w4 0)),
         ("%not10.us", .int 64 (vnot10 w1 w2 w3 w4 0)),
         ("%or9.us", .int 64 (vor9 w1 w2 w3 w4 0)),
         ("%shl8.us", .int 64 (vshl8 w1 w2 w3 w4)),
         ("%and.us", .int 64 (vand w2 w3)),
         ("%not6.us", .int 64 (vnot6 w3)),
         ("%not.us", .int 64 (vnot w1 w2 w3 w4)),
         ("%or2.us", .int 64 (vor2 w1 w2 w3 w4)),
         ("%13", .int 64 (v6 w1 w2 w4)), ("%12", .int 64 (v5 w1 w4)),
         ("%11", .int 64 w4), ("%10", .int 64 w3), ("%9", .int 64 w2),
         ("%8", .int 64 w1),
         ("%add.ptr.us", .ptr (b + (BitVec.signExtend 64 (sh6 0)).toNat)),
         ("%shl.us", .int 64 (sh6 0)),
         ("%i.080.us", .int 64 0),
         ("%k.081.us", .int 64 w0),
         ("%prevS.082.us", .int 64 0)]
    (usSplitIn env n b sc mk delim inString ws backslash ctl entw ep
      xp nxp xcarry w0 shr)

/-- **`for.body.us` from the split predecessor.** -/
theorem us_split_denote (calls : Calls) (env : Env) (s : State) (n : BitVec 64)
    (b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry : Nat)
    (w0 shr w1 w2 w3 w4 w5 w6 w7 : BitVec 64) (r1 r2 r3 : CallOutcome)
    (hpre : s.pre = some "for.body.lr.ph.split.us")
    (hld1 : readBytes r1.mem mk 8 = some (natToBytes w1.toNat 8))
    (hld2 : readBytes r1.mem delim 8 = some (natToBytes w2.toNat 8))
    (hld3 : readBytes r1.mem inString 8 = some (natToBytes w3.toNat 8))
    (hld4 : readBytes r1.mem ws 8 = some (natToBytes w4.toNat 8))
    (hcall1 : calls "leanllvm_json_s1_masks"
      [.ptr (b + (BitVec.signExtend 64 (sh6 (0 : BitVec 64))).toNat), .ptr sc,
       .ptr mk] s.mem s.next = some r1)
    (hcall2 : calls "leanllvm_json_entry_pos8"
      [.ptr entw, .int 64 0, .int 64 1, .ptr ep, .int 64 w0]
      (writeBytes r1.mem entw (natToBytes (vent n 0 w1 w2 w3 w4 0).toNat 8))
      r1.next = some r2)
    (hld5 : readBytes r2.mem backslash 8 = some (natToBytes w5.toNat 8))
    (hld6 : readBytes r2.mem ctl 8 = some (natToBytes w6.toNat 8))
    (hld7 : readBytes r2.mem inString 8 = some (natToBytes w7.toNat 8))
    (hcall3 : calls "leanllvm_json_escape_list"
      [.int 64 w5, .int 64 w6, .int 64 w7, .int 64 0, .ptr xp, .ptr nxp,
       .ptr xcarry] r2.mem r2.next = some r3) :
    denoteCode calls pUs.instrs
        (stateAt (usSplitIn env n b sc mk delim inString ws backslash ctl entw ep
          xp nxp xcarry w0 shr) s) =
      some (stateAt (usSplitOut env n b sc mk delim inString ws backslash ctl entw ep
        xp nxp xcarry w0 shr w1 w2 w3 w4 w5 w6 w7 r2.ret)
        { s with mem := r3.mem, next := r3.next }) := by
  rw [pUs_instrs]
  simp only [lit, usSplitIn, usSplitOut]
  pipeline_block_eval

/-- `for.body.us83`'s incoming builder at the split predecessor. -/
def us83SplitIn (env : Env) (n : BitVec 64) (b sc mk delim inString ws entw ep : Nat)
    (w0 shr : BitVec 64) : Env :=
  cells [("%shr", .int 64 shr), ("%0", .int 64 w0),
         ("%ep", .ptr ep), ("%entw", .ptr entw), ("%ws", .ptr ws),
         ("%in_string", .ptr inString), ("%delim", .ptr delim), ("%mk", .ptr mk),
         ("%sc", .ptr sc), ("%b", .ptr b), ("%n", .int 64 n)] env

/-- `for.body.us83`'s outgoing builder at the split predecessor. -/
def us83SplitOut (env : Env) (n : BitVec 64) (b sc mk delim inString ws entw ep : Nat)
    (w0 shr w1 w2 w3 w4 : BitVec 64) (ret : Value) : Env :=
  cells [("%exitcond114.not", .int 1 (vexit 0 shr)),
         ("%inc.us106", .int 64 (vinc 0)),
         ("%call.us", ret),
         ("%ent.0.us104", .int 64 (vent n 0 w1 w2 w3 w4 0)),
         ("%and18.us103", .int 64 (vand18 n 0)),
         ("%sub17.us102", .int 64 (vsub17 n 0)),
         ("%notmask.us101", .int 64 (vnotmask n 0)),
         ("%cmp15.us100", .int 1 (vcmp n 0)),
         ("%sub.us99", .int 64 (vsub n 0)),
         ("%shr13.us98", .int 64 (vshr13 w1 w2 w3 w4)),
         ("%or12.us97", .int 64 (vor12 w1 w2 w3 w4 0)),
         ("%24", .int 64 (v7 w1 w2 w3 w4 0)),
         ("%and11.us96", .int 64 (vand11 w1 w2 w3 w4 0)),
         ("%not10.us95", .int 64 (vnot10 w1 w2 w3 w4 0)),
         ("%or9.us94", .int 64 (vor9 w1 w2 w3 w4 0)),
         ("%shl8.us93", .int 64 (vshl8 w1 w2 w3 w4)),
         ("%and.us92", .int 64 (vand w2 w3)),
         ("%not6.us91", .int 64 (vnot6 w3)),
         ("%not.us90", .int 64 (vnot w1 w2 w3 w4)),
         ("%or2.us89", .int 64 (vor2 w1 w2 w3 w4)),
         ("%23", .int 64 (v6 w1 w2 w4)), ("%22", .int 64 (v5 w1 w4)),
         ("%21", .int 64 w4), ("%20", .int 64 w3), ("%19", .int 64 w2),
         ("%18", .int 64 w1),
         ("%add.ptr.us88", .ptr (b + (BitVec.signExtend 64 (sh6 0)).toNat)),
         ("%shl.us87", .int 64 (sh6 0)),
         ("%i.080.us86", .int 64 0),
         ("%k.081.us85", .int 64 w0),
         ("%prevS.082.us84", .int 64 0)]
    (us83SplitIn env n b sc mk delim inString ws entw ep w0 shr)

/-- **`for.body.us83` from the split predecessor.** -/
theorem us83_split_denote (calls : Calls) (env : Env) (s : State) (n : BitVec 64)
    (b sc mk delim inString ws entw ep : Nat)
    (w0 shr w1 w2 w3 w4 : BitVec 64) (r1 r2 : CallOutcome)
    (hpre : s.pre = some "for.body.lr.ph.split")
    (hld1 : readBytes r1.mem mk 8 = some (natToBytes w1.toNat 8))
    (hld2 : readBytes r1.mem delim 8 = some (natToBytes w2.toNat 8))
    (hld3 : readBytes r1.mem inString 8 = some (natToBytes w3.toNat 8))
    (hld4 : readBytes r1.mem ws 8 = some (natToBytes w4.toNat 8))
    (hcall1 : calls "leanllvm_json_s1_masks"
      [.ptr (b + (BitVec.signExtend 64 (sh6 (0 : BitVec 64))).toNat), .ptr sc,
       .ptr mk] s.mem s.next = some r1)
    (hcall2 : calls "leanllvm_json_entry_b8"
      [.ptr entw, .int 64 0, .int 64 1, .ptr ep, .int 64 w0]
      (writeBytes r1.mem entw (natToBytes (vent n 0 w1 w2 w3 w4 0).toNat 8))
      r1.next = some r2) :
    denoteCode calls pUs83.instrs
        (stateAt (us83SplitIn env n b sc mk delim inString ws entw ep w0 shr) s) =
      some (stateAt (us83SplitOut env n b sc mk delim inString ws entw ep w0 shr
        w1 w2 w3 w4 r2.ret) { s with mem := r2.mem, next := r2.next }) := by
  rw [pUs83_instrs]
  simp only [lit, us83SplitIn, us83SplitOut]
  pipeline_block_eval

/-- `for.body`'s incoming builder at the split predecessor. -/
def bodySplitIn (env : Env) (n : BitVec 64) (b sc mk delim inString ws backslash ctl
    entw ep xp nxp xcarry : Nat) (w0 shr : BitVec 64) : Env :=
  cells [("%shr", .int 64 shr), ("%0", .int 64 w0),
         ("%xcarry", .ptr xcarry), ("%nxp", .ptr nxp), ("%xp", .ptr xp),
         ("%ep", .ptr ep), ("%entw", .ptr entw), ("%ctl", .ptr ctl),
         ("%backslash", .ptr backslash), ("%ws", .ptr ws),
         ("%in_string", .ptr inString), ("%delim", .ptr delim), ("%mk", .ptr mk),
         ("%sc", .ptr sc), ("%b", .ptr b), ("%n", .int 64 n)] env

/-- `for.body`'s outgoing builder at the split predecessor. -/
def bodySplitOut (env : Env) (n : BitVec 64) (b sc mk delim inString ws backslash ctl
    entw ep xp nxp xcarry : Nat) (w0 shr w1 w2 w3 w4 w5 w6 w7 : BitVec 64)
    (ret : Value) : Env :=
  cells [("%exitcond.not", .int 1 (vexit 0 shr)),
         ("%inc", .int 64 (vinc 0)),
         ("%36", .int 64 w7), ("%35", .int 64 w6), ("%34", .int 64 w5),
         ("%call", ret),
         ("%ent.0", .int 64 (vent n 0 w1 w2 w3 w4 0)),
         ("%and18", .int 64 (vand18 n 0)),
         ("%sub17", .int 64 (vsub17 n 0)),
         ("%notmask", .int 64 (vnotmask n 0)),
         ("%cmp15", .int 1 (vcmp n 0)),
         ("%sub", .int 64 (vsub n 0)),
         ("%shr13", .int 64 (vshr13 w1 w2 w3 w4)),
         ("%or12", .int 64 (vor12 w1 w2 w3 w4 0)),
         ("%33", .int 64 (v7 w1 w2 w3 w4 0)),
         ("%and11", .int 64 (vand11 w1 w2 w3 w4 0)),
         ("%not10", .int 64 (vnot10 w1 w2 w3 w4 0)),
         ("%or9", .int 64 (vor9 w1 w2 w3 w4 0)),
         ("%shl8", .int 64 (vshl8 w1 w2 w3 w4)),
         ("%and", .int 64 (vand w2 w3)),
         ("%not6", .int 64 (vnot6 w3)),
         ("%not", .int 64 (vnot w1 w2 w3 w4)),
         ("%or2", .int 64 (vor2 w1 w2 w3 w4)),
         ("%32", .int 64 (v6 w1 w2 w4)), ("%31", .int 64 (v5 w1 w4)),
         ("%30", .int 64 w4), ("%29", .int 64 w3), ("%28", .int 64 w2),
         ("%27", .int 64 w1),
         ("%add.ptr", .ptr (b + (BitVec.signExtend 64 (sh6 0)).toNat)),
         ("%shl", .int 64 (sh6 0)),
         ("%i.080", .int 64 0),
         ("%k.081", .int 64 w0),
         ("%prevS.082", .int 64 0)]
    (bodySplitIn env n b sc mk delim inString ws backslash ctl entw ep
      xp nxp xcarry w0 shr)

/-- **`for.body` from the split predecessor.** -/
theorem body_split_denote (calls : Calls) (env : Env) (s : State) (n : BitVec 64)
    (b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry : Nat)
    (w0 shr w1 w2 w3 w4 w5 w6 w7 : BitVec 64) (r1 r2 r3 : CallOutcome)
    (hpre : s.pre = some "for.body.lr.ph.split")
    (hld1 : readBytes r1.mem mk 8 = some (natToBytes w1.toNat 8))
    (hld2 : readBytes r1.mem delim 8 = some (natToBytes w2.toNat 8))
    (hld3 : readBytes r1.mem inString 8 = some (natToBytes w3.toNat 8))
    (hld4 : readBytes r1.mem ws 8 = some (natToBytes w4.toNat 8))
    (hcall1 : calls "leanllvm_json_s1_masks"
      [.ptr (b + (BitVec.signExtend 64 (sh6 (0 : BitVec 64))).toNat), .ptr sc,
       .ptr mk] s.mem s.next = some r1)
    (hcall2 : calls "leanllvm_json_entry_b8"
      [.ptr entw, .int 64 0, .int 64 1, .ptr ep, .int 64 w0]
      (writeBytes r1.mem entw (natToBytes (vent n 0 w1 w2 w3 w4 0).toNat 8))
      r1.next = some r2)
    (hld5 : readBytes r2.mem backslash 8 = some (natToBytes w5.toNat 8))
    (hld6 : readBytes r2.mem ctl 8 = some (natToBytes w6.toNat 8))
    (hld7 : readBytes r2.mem inString 8 = some (natToBytes w7.toNat 8))
    (hcall3 : calls "leanllvm_json_escape_list"
      [.int 64 w5, .int 64 w6, .int 64 w7, .int 64 0, .ptr xp, .ptr nxp,
       .ptr xcarry] r2.mem r2.next = some r3) :
    denoteCode calls pBody.instrs
        (stateAt (bodySplitIn env n b sc mk delim inString ws backslash ctl entw ep
          xp nxp xcarry w0 shr) s) =
      some (stateAt (bodySplitOut env n b sc mk delim inString ws backslash ctl entw ep
        xp nxp xcarry w0 shr w1 w2 w3 w4 w5 w6 w7 r2.ret)
        { s with mem := r3.mem, next := r3.next }) := by
  rw [pBody_instrs]
  simp only [lit, bodySplitIn, bodySplitOut]
  pipeline_block_eval

/-! ### The dispatch blocks and the tail

The seed crosses the entry test's two selection blocks before the loop's first
iteration, and the tail crosses the loop's exit, the UTF-8 stage's call, the two
refusal branches and the final `phi`.  Those blocks' instruction lists are pinned
here, and their traces are `pipeline_block_eval` facts like the arm traces': the
one shape the dispatch adds is `getelementptr` at a literal index (`%delim`,
`%in_string`, `%ws`, `%backslash`, `%ctl` are all `%mk` plus a constant), and the
tail adds the 32-bit shift and mask `for.cond.cleanup` forms its gate from, the
UTF-8 call, and stage 2's thirteen-argument call. -/

def pLrPh := blockAt pipelineBody 1 (by decide)
def pSplitUs := blockAt pipelineBody 2 (by decide)
def pSplit := blockAt pipelineBody 5 (by decide)
def pCond := blockAt pipelineBody 7 (by decide)
def pIfThen := blockAt pipelineBody 9 (by decide)
def pIfEnd := blockAt pipelineBody 10 (by decide)

theorem findBlock_lrPh :
    pipelineBody.findBlock "for.body.lr.ph" = some pLrPh := by decide

theorem findBlock_splitUs :
    pipelineBody.findBlock "for.body.lr.ph.split.us" = some pSplitUs := by decide

theorem findBlock_split :
    pipelineBody.findBlock "for.body.lr.ph.split" = some pSplit := by decide

theorem findBlock_cond :
    pipelineBody.findBlock "for.cond.cleanup" = some pCond := by decide

theorem findBlock_ifThen :
    pipelineBody.findBlock "if.then33" = some pIfThen := by decide

theorem findBlock_ifEnd :
    pipelineBody.findBlock "if.end34" = some pIfEnd := by decide

/-- `for.cond.cleanup`'s `phi`: one incoming entry per loop-exit edge. -/
def cleanupPhi : List (String × Operand) :=
  [("entry", Operand.reg "%0"),
   ("for.body.us.us", Operand.reg "%call21.us.us"),
   ("for.body.us", Operand.reg "%call21.us"),
   ("for.body.us83", Operand.reg "%call.us"),
   ("for.body", Operand.reg "%call")]

theorem pLrPh_instrs :
    pLrPh.instrs =
      [Instr.gep "%delim" (Ty.int 8) (Operand.reg "%mk") (lit 64 8),
       Instr.gep "%in_string" (Ty.int 8) (Operand.reg "%mk") (lit 64 16),
       Instr.gep "%ws" (Ty.int 8) (Operand.reg "%mk") (lit 64 24),
       Instr.binop "%and19" (BinOp.and) 64 (Operand.reg "%arm") (lit 64 1),
       Instr.icmp "%tobool.not" (IPred.eq) 64 (Operand.reg "%and19") (lit 64 0),
       Instr.binop "%and23" (BinOp.and) 64 (Operand.reg "%arm") (lit 64 2),
       Instr.icmp "%tobool24.not" (IPred.eq) 64 (Operand.reg "%and23") (lit 64 0),
       Instr.gep "%backslash" (Ty.int 8) (Operand.reg "%mk") (lit 64 32),
       Instr.gep "%ctl" (Ty.int 8) (Operand.reg "%mk") (lit 64 40)] := by
  decide

theorem pSplitUs_instrs : pSplitUs.instrs = [] := by decide

theorem pSplit_instrs : pSplit.instrs = [] := by decide

theorem pCond_instrs :
    pCond.instrs =
      [Instr.phi "%k.0.lcssa" (Ty.int 64) cleanupPhi,
       Instr.store (Ty.int 64) (Operand.reg "%k.0.lcssa") (Operand.reg "%nk"),
       Instr.trunc "%25" 64 32 (Operand.reg "%arm"),
       Instr.binop "%26" (BinOp.lshr) 32 (Operand.reg "%25") (lit 32 2),
       Instr.binop "%conv" (BinOp.and) 32 (Operand.reg "%26") (lit 32 1),
       Instr.call "%call30" (Ty.int 64) "leanllvm_json_utf8"
          [(Ty.ptr, Operand.reg "%b"), (Ty.int 64, Operand.reg "%n"),
           (Ty.int 32, Operand.reg "%conv")],
       Instr.icmp "%cmp31.not" (IPred.eq) 64 (Operand.reg "%call30") (lit 64 0)] := by
  decide

theorem pIfThen_instrs :
    pIfThen.instrs =
      [Instr.store (Ty.int 64) (Operand.reg "%n") (Operand.reg "%err")] := by
  decide

theorem pIfEnd_instrs :
    pIfEnd.instrs =
      [Instr.load "%37" (Ty.int 64) (Operand.reg "%nxp"),
       Instr.call "%call35" (Ty.int 64) "leanllvm_json_stage2"
          [(Ty.ptr, Operand.reg "%b"), (Ty.int 64, Operand.reg "%n"),
           (Ty.ptr, Operand.reg "%ep"), (Ty.int 64, Operand.reg "%k.0.lcssa"),
           (Ty.ptr, Operand.reg "%xp"), (Ty.int 64, Operand.reg "%37"),
           (Ty.ptr, Operand.reg "%dst"), (Ty.int 64, Operand.reg "%dstcap"),
           (Ty.ptr, Operand.reg "%ndst"), (Ty.ptr, Operand.reg "%ev"),
           (Ty.int 64, Operand.reg "%evcap"), (Ty.ptr, Operand.reg "%nev"),
           (Ty.ptr, Operand.reg "%err")]] := by
  decide

theorem pEntry_term :
    pEntry.term = Term.condbr (Operand.reg "%cmp79.not") "for.cond.cleanup"
      "for.body.lr.ph" := by decide

theorem pLrPh_term :
    pLrPh.term = Term.condbr (Operand.reg "%tobool.not") "for.body.lr.ph.split.us"
      "for.body.lr.ph.split" := by decide

theorem pSplitUs_term :
    pSplitUs.term = Term.condbr (Operand.reg "%tobool24.not") "for.body.us.us"
      "for.body.us" := by decide

theorem pSplit_term :
    pSplit.term = Term.condbr (Operand.reg "%tobool24.not") "for.body.us83"
      "for.body" := by decide

theorem pCond_term :
    pCond.term = Term.condbr (Operand.reg "%cmp31.not") "if.end34" "if.then33" := by
  decide

theorem pIfThen_term : pIfThen.term = Term.br "cleanup" := by decide

theorem pIfEnd_term : pIfEnd.term = Term.br "cleanup" := by decide

/-! ### The dispatch block's trace -/

/-- The selection block's incoming builder: the two parameters it reads. -/
def lrPhIn (env : Env) (mk : Nat) (arm : BitVec 64) : Env :=
  cells [("%arm", .int 64 arm), ("%mk", .ptr mk)] env

/-- The selection block's outgoing builder: the five byte offsets and the two
selector tests. -/
def lrPhOut (env : Env) (mk : Nat) (arm : BitVec 64) : Env :=
  cells [("%ctl", .ptr (mk + 40)),
         ("%backslash", .ptr (mk + 32)),
         ("%tobool24.not", .int 1 (evalICmp .eq (arm &&& litv 64 2) (litv 64 0))),
         ("%and23", .int 64 (arm &&& litv 64 2)),
         ("%tobool.not", .int 1 (evalICmp .eq (arm &&& litv 64 1) (litv 64 0))),
         ("%and19", .int 64 (arm &&& litv 64 1)),
         ("%ws", .ptr (mk + 24)),
         ("%in_string", .ptr (mk + 16)),
         ("%delim", .ptr (mk + 8))]
    (lrPhIn env mk arm)

/-- **The selection block computes the two gates and the five byte offsets.** -/
theorem lrPh_denote (calls : Calls) (env : Env) (s : State) (mk : Nat)
    (arm : BitVec 64) :
    denoteCode calls pLrPh.instrs (stateAt (lrPhIn env mk arm) s) =
      some (stateAt (lrPhOut env mk arm) s) := by
  rw [pLrPh_instrs]
  simp only [lit, litv, lrPhIn, lrPhOut]
  pipeline_block_eval

/-! ### The tail's blocks -/

/-- The gate `for.cond.cleanup` forms from the selector: `(arm >>> 2) & 1` at
thirty-two bits. -/
def condGate (arm : BitVec 64) : BitVec 32 :=
  ((BitVec.ofNat 32 (arm.toNat % 2 ^ 32)) >>> 2) &&& 1

/-- The exit block's incoming builder: the loop-exit's selected count under its
own name, the document, the selector and the count slot. -/
def condIn (env : Env) (sel : String) (kv : BitVec 64) (b nk : Nat)
    (arm n : BitVec 64) : Env :=
  cells [("%n", .int 64 n), ("%b", .ptr b), ("%arm", .int 64 arm),
         ("%nk", .ptr nk), (sel, .int 64 kv)] env

/-- The exit block's outgoing builder. -/
def condOut (env : Env) (sel : String) (kv : BitVec 64) (b nk : Nat)
    (arm n verdict : BitVec 64) (ret : Value) : Env :=
  cells [("%cmp31.not", .int 1 (evalICmp .eq verdict (litv 64 0))),
         ("%call30", ret),
         ("%conv", .int 32 (condGate arm)),
         ("%26", .int 32 ((BitVec.ofNat 32 (arm.toNat % 2 ^ 32)) >>> 2)),
         ("%25", .int 32 (BitVec.ofNat 32 (arm.toNat % 2 ^ 32))),
         ("%k.0.lcssa", .int 64 kv)]
    (condIn env sel kv b nk arm n)

/-- **The exit block selects the count, stores it, and calls the UTF-8 stage.**
The `phi` reads the predecessor the exit came from, so its incoming operand is
named by `hinc`; the store writes the selected count to `%nk`, and the stage's
gate is `condGate arm`.  The stage's result is `i64`, and its value is the `bit`
the exit test reads, so the call is opened to its three fields and its return is
the word `hret` names. -/
theorem condCleanup_denote (calls : Calls) (env : Env) (s : State)
    (sel p : String) (kv : BitVec 64) (b nk : Nat) (arm n : BitVec 64)
    (verdict : BitVec 64) (m30 : Mem) (n30 : Nat)
    (hpre : s.pre = some p)
    (hinc : phiIncoming p cleanupPhi = some (.reg sel))
    (hop : evalOperand (stateAt (condIn env sel kv b nk arm n) s) (.reg sel)
      = some (.int 64 kv))
    (hcall : calls "leanllvm_json_utf8" [.ptr b, .int 64 n, .int 32 (condGate arm)]
      (writeBytes s.mem nk (natToBytes kv.toNat 8)) s.next = some ⟨.int 64 verdict, m30, n30⟩) :
    denoteCode calls pCond.instrs (stateAt (condIn env sel kv b nk arm n) s) =
      some (stateAt (condOut env sel kv b nk arm n verdict (.int 64 verdict))
        { s with mem := m30, next := n30 }) := by
  rw [pCond_instrs]
  simp only [lit, litv, condGate, condIn, condOut]
  pipeline_block_eval

/-- The refusal branch's incoming builder. -/
def ifThenIn (env : Env) (n : BitVec 64) (err : Nat) : Env :=
  cells [("%err", .ptr err), ("%n", .int 64 n)] env

/-- **The refusal branch stores the document length in the offset slot.** -/
theorem ifThen_denote (calls : Calls) (env : Env) (s : State)
    (n : BitVec 64) (err : Nat) :
    denoteCode calls pIfThen.instrs (stateAt (ifThenIn env n err) s) =
      some (stateAt (ifThenIn env n err)
        { s with mem := writeBytes s.mem err (natToBytes n.toNat 8) }) := by
  rw [pIfThen_instrs]
  simp only [ifThenIn]
  pipeline_block_eval

/-- The success branch's incoming builder: the escape count slot it loads and the
twelve arguments stage 2 takes. -/
def ifEndIn (env : Env) (b ep xp dst ndst ev nev err nxp : Nat)
    (n k dcap ecap : BitVec 64) : Env :=
  cells [("%err", .ptr err), ("%nev", .ptr nev), ("%evcap", .int 64 ecap),
         ("%ev", .ptr ev), ("%ndst", .ptr ndst), ("%dstcap", .int 64 dcap),
         ("%dst", .ptr dst), ("%xp", .ptr xp), ("%k.0.lcssa", .int 64 k),
         ("%ep", .ptr ep), ("%n", .int 64 n), ("%b", .ptr b),
         ("%nxp", .ptr nxp)] env

/-- The success branch's outgoing builder. -/
def ifEndOut (env : Env) (b ep xp dst ndst ev nev err nxp : Nat)
    (n k dcap ecap x37 : BitVec 64) (ret : Value) : Env :=
  cells [("%call35", ret), ("%37", .int 64 x37)]
    (ifEndIn env b ep xp dst ndst ev nev err nxp n k dcap ecap)

/-- **The success branch loads the escape count and calls stage 2.** -/
theorem ifEnd_denote (calls : Calls) (env : Env) (s : State)
    (b ep xp dst ndst ev nev err nxp : Nat)
    (n k x37 dcap ecap : BitVec 64) (r35 : CallOutcome)
    (hld : readBytes s.mem nxp 8 = some (natToBytes x37.toNat 8))
    (hcall : calls "leanllvm_json_stage2"
      [.ptr b, .int 64 n, .ptr ep, .int 64 k, .ptr xp, .int 64 x37, .ptr dst,
       .int 64 dcap, .ptr ndst, .ptr ev, .int 64 ecap, .ptr nev, .ptr err]
      s.mem s.next = some r35) :
    denoteCode calls pIfEnd.instrs
        (stateAt (ifEndIn env b ep xp dst ndst ev nev err nxp n k dcap ecap) s) =
      some (stateAt (ifEndOut env b ep xp dst ndst ev nev err nxp n k dcap ecap x37
        r35.ret) { s with mem := r35.mem, next := r35.next }) := by
  rw [pIfEnd_instrs]
  simp only [ifEndIn, ifEndOut]
  pipeline_block_eval

/-! ### The environment bridge

A block trace is stated at `stateAt envIn s`: the builders prepend every register
the block reads, including the caller's own cells, so two consecutive traces
state their states over different environment lists and no trace applies to the
state the previous block leaves.  What the blocks *do* share is what they read:
`denoteCode` consults the environment only through `lookupName`, and the memory,
the allocator base and the predecessor field directly.  So the transport fact is

* two environments that agree on `lookupName` at every name a block reads, with
  equal memory, allocator base and predecessor, run that block to states that
  agree in the same way.

That is the fact carried here, with the agreement stated over the block's own
read set — `instrsUses` — and not over all names, so it is discharged from the
staging's read set rather than from a promise no staging makes.  The relation is
`AgreeOn`; `denoteCode_transport` is the form a trace consumer uses: a completed
denotation at the canonical state transports to any state that agrees with it,
and the result agrees with the trace's outcome. -/

/-- The register names an operand reads: `Operand.regs`, at the name this
module's read-set projection states it at. -/
abbrev operandNames (op : Operand) : List String := op.regs

/-- The operands an instruction evaluates, in evaluation order. -/
def instrOperands : Instr → List Operand
  | .binop _ _ _ a b => [a, b]
  | .icmp _ _ _ a b => [a, b]
  | .icmpPtr _ _ a b => [a, b]
  | .select _ _ c a b => [c, a, b]
  | .trunc _ _ _ v => [v]
  | .zext _ _ _ v => [v]
  | .sext _ _ _ v => [v]
  | .alloca _ _ _ => []
  | .load _ _ p => [p]
  | .store _ v p => [v, p]
  | .gep _ _ base off => [base, off]
  | .icmpVec _ _ _ _ a b => [a, b]
  | .binopVec _ _ _ _ a b => [a, b]
  | .bitcastMask _ _ v => [v]
  | .extractelement _ _ _ v idx => [v, idx]
  | .insertelement _ _ _ v elt idx => [v, elt, idx]
  | .shuffleVec _ _ _ a b _ => [a, b]
  | .vecBitcast _ _ _ _ _ v => [v]
  | .call _ _ _ args => args.map (·.2)
  | .callVoid _ args => args.map (·.2)
  | .phi _ _ inc => inc.map (·.2)

/-- The register names an instruction reads: exactly its operands'.  A `phi`
names every incoming operand because which one is read depends on the predecessor
field, which `AgreeOn` carries equal. -/
def instrNames (i : Instr) : List String := (instrOperands i).flatMap operandNames

/-- An operand's names are among its instruction's read set. -/
theorem operand_mem_reads {i : Instr} {op : Operand} (hm : op ∈ instrOperands i)
    {n : String} (hn : n ∈ operandNames op) : n ∈ instrNames i :=
  List.mem_flatMap.mpr ⟨op, hm, hn⟩

/-- **Two states agree on what a block reads.**  `State.AgreeOn` names the
relation and `State.AgreeOn.bind` and its siblings carry its preservation: a
congruence over environments is a fact about `evalInstr`, so it is stated beside
the semantics (`LeanLLVM.Semantics`) and instantiated here at the read set a
block actually has. -/
abbrev AgreeOn (ns : List String) (t s : State) : Prop := State.AgreeOn ns t s

/-- The predecessor selector's operand is one of the incoming list's. -/
theorem phiIncoming_mem {p : String} {inc : List (String × Operand)} {op : Operand}
    (h : phiIncoming p inc = some op) : op ∈ inc.map (·.2) :=
  LeanLLVM.phiIncoming_mem h

/-- The preservation facts, at the names this module and its axiom pins read.
The proofs are the fragment's. -/
theorem AgreeOn.bind {ns : List String} {t s : State} {d : String} {v : Value}
    (h : AgreeOn ns t s) : AgreeOn ns (t.bind d v) (s.bind d v) :=
  State.AgreeOn.bind h

theorem AgreeOn.call {ns : List String} {t s : State} {d : String} {r : CallOutcome}
    (h : AgreeOn ns t s) :
    AgreeOn ns { t with env := (d, r.ret) :: t.env, mem := r.mem, next := r.next }
      { s with env := (d, r.ret) :: s.env, mem := r.mem, next := r.next } :=
  State.AgreeOn.call h

theorem AgreeOn.callVoid {ns : List String} {t s : State} {r : CallOutcome}
    (h : AgreeOn ns t s) :
    AgreeOn ns { t with mem := r.mem, next := r.next }
      { s with mem := r.mem, next := r.next } :=
  State.AgreeOn.callVoid h

theorem AgreeOn.alloca {ns : List String} {t s : State} {d : String} {ty : Ty}
    (h : AgreeOn ns t s) :
    AgreeOn ns
      { t with env := (d, .ptr t.next) :: t.env, next := t.next + ty.sizeBytes }
      { s with env := (d, .ptr s.next) :: s.env, next := s.next + ty.sizeBytes } :=
  State.AgreeOn.alloca h

theorem evalOperand_agree {t s : State} {op : Operand}
    (h : ∀ n ∈ operandNames op, lookupName t.env n = lookupName s.env n) :
    evalOperand t op = evalOperand s op :=
  LeanLLVM.evalOperand_agree h

theorem evalOperands_agree {t s : State} :
    ∀ (args : List (Ty × Operand)),
      (∀ op ∈ args.map (·.2), evalOperand t op = evalOperand s op) →
      evalOperands t args = evalOperands s args :=
  LeanLLVM.evalOperands_agree

/-- **A block trace transports to any state that agrees on the block's read
set.**  A completed `denoteCode` at one state gives a completed one at a state
that agrees on the names the block reads — `instrsUses` — and the two outcomes
agree in the same way.  This is the form a trace consumer uses: the builders
prepend every register a block reads, so the state the previous block leaves is
never syntactically the state the next trace is stated at. -/
theorem denoteCode_transport {calls : Calls} {is : List Instr} {s s' t : State}
    (h : AgreeOn (instrsUses is) s t) (hs : denoteCode calls is s = some s') :
    ∃ t', denoteCode calls is t = some t' ∧ AgreeOn (instrsUses is) s' t' :=
  denoteCode_agree calls is h (fun _ hn => hn) hs

/-! ### The control steps

A block trace is a `denoteCode` fact; a control step is that fact followed by the
block's terminator.  The four `execTerm` facts below are the terminator shapes
the pipeline's blocks use — a conditional jump at a decided one-bit value, an
unconditional jump, and a valued return — and `step_of_blocks` is the step those
facts produce: the block's found by name, its instructions denoted, its terminator
executed.  They are what turns any trace in this module into one `step`, and so
into the `runFuel` prefixes a loop instance consumes. -/

theorem execTerm_condbr_one {s : State} {c : Operand} {t f : String}
    (h : evalOperand s c = some (.int 1 1)) :
    execTerm s (.condbr c t f) = .jump { s with pc := t, pre := some s.pc } := by
  simp [execTerm, h]

theorem execTerm_condbr_zero {s : State} {c : Operand} {t f : String}
    (h : evalOperand s c = some (.int 1 0)) :
    execTerm s (.condbr c t f) = .jump { s with pc := f, pre := some s.pc } := by
  simp [execTerm, h]

theorem execTerm_br (s : State) (d : String) :
    execTerm s (.br d) = .jump { s with pc := d, pre := some s.pc } := rfl

theorem execTerm_ret_int {s : State} {o : Operand} {x : BitVec 64}
    (h : evalOperand s o = some (.int 64 x)) :
    execTerm s (.ret (Ty.int 64) (some o)) = .ret (some (.int 64 x)) s := by
  simp [execTerm, h]

/-- **One control step from a block's trace.**  The block is found at the state's
program counter, its instructions denote to `s'`, and its terminator is `c`. -/
theorem step_of_blocks {calls : Calls} {f : Function} {s s' : State} {b : Block}
    {c : Ctrl} (hfind : f.findBlock s.pc = some b)
    (hcode : denoteCode calls b.instrs s = some s')
    (hterm : execTerm s' b.term = c) :
    step calls f s = c := by
  simp only [step, hfind, hcode, hterm]

/-! ### One iteration, as the loop instance's step

`PipelineLoop.step` asks for a `runFuel` prefix of bounded cost from one invariant
state to the next, with the next state's block left to the invariant.  Each arm's
iteration is one control step: the arm's block trace, then its terminator, whose
test `%exitcond…` compares the carried increment with `%shr`.  The block's
denotation arrives as the trace fact, so the step adds the terminator and nothing
else, and a step is stated here for all four arms in `step`'s own shape — an exit
state or the next iteration's head, at cost one.  The call's return is carried as
the outcome `r`, whose memory and allocator base the step adopts. -/

/-- The first arm's terminator: the POS8-no-gate copy's exit test. -/
theorem pUsUs_term :
    pUsUs.term = Term.condbr (Operand.reg "%exitcond116.not") "for.cond.cleanup"
      "for.body.us.us" := by decide

/-- A one-step jump lifts to the fuel recursion's head. -/
theorem runFuel_one_of_step {calls : Calls} {f : Function} {s e : State}
    (h : step calls f s = .jump e) (k : Nat) :
    runFuel calls (1 + k) f s = runFuel calls k f e := by
  rw [show 1 + k = k + 1 from by omega]
  simp only [runFuel, h]

/-- **The `for.body.us.us` arm's iteration.**  One control step from the arm's head
reaches either the loop exit or the head of the next iteration. -/
theorem usUs_step (calls : Calls) (env : Env) (s : State) (n : BitVec 64)
    (b sc mk delim inString ws entw ep : Nat)
    (s13 c21 inc shr w1 w2 w3 w4 : BitVec 64) (r : CallOutcome) (m' : CallOutcome)
    (hpc : s.pc = "for.body.us.us")
    (hcode : denoteCode calls pUsUs.instrs
        (stateAt (usUsIn env n b sc mk delim inString ws entw ep s13 c21 inc shr) s) =
      some (stateAt (usUsOut env n b sc mk delim inString ws entw ep s13 c21 inc shr w1 w2 w3 w4 r.ret)
        { s with mem := m'.mem, next := m'.next })) :
    ∃ (e : State) (j : Nat), j ≤ 1 ∧
      (e.pc = "for.cond.cleanup" ∨ e.pc = "for.body.us.us") ∧
      ∀ k, runFuel calls (j + k) pipelineBody
        (stateAt (usUsIn env n b sc mk delim inString ws entw ep s13 c21 inc shr) s) = runFuel calls k pipelineBody e := by
  obtain hb | hb := bitVec1_eq_zero_or_one (vexit inc shr)
  · refine ⟨stateAt (usUsOut env n b sc mk delim inString ws entw ep s13 c21 inc shr w1 w2 w3 w4 r.ret)
      { s with mem := m'.mem, next := m'.next, pc := "for.body.us.us", pre := some s.pc },
      1, Nat.le_refl 1, Or.inr rfl, fun k => ?_⟩
    have hstep : step calls pipelineBody (stateAt (usUsIn env n b sc mk delim inString ws entw ep s13 c21 inc shr) s) =
        .jump (stateAt (usUsOut env n b sc mk delim inString ws entw ep s13 c21 inc shr w1 w2 w3 w4 r.ret)
          { s with mem := m'.mem, next := m'.next, pc := "for.body.us.us", pre := some s.pc }) := by
      refine step_of_blocks (b := pUsUs) (s' := stateAt (usUsOut env n b sc mk delim inString ws entw ep s13 c21 inc shr w1 w2 w3 w4 r.ret)
        { s with mem := m'.mem, next := m'.next }) ?_ ?_ ?_
      · simpa only [stateAt, hpc] using findBlock_usus
      · exact hcode
      · rw [pUsUs_term]
        refine execTerm_condbr_zero ?_
        simp only [stateAt, usUsOut, cells, evalOperand, lookupName_cons_self, hb]
    exact runFuel_one_of_step hstep k
  · refine ⟨stateAt (usUsOut env n b sc mk delim inString ws entw ep s13 c21 inc shr w1 w2 w3 w4 r.ret)
      { s with mem := m'.mem, next := m'.next, pc := "for.cond.cleanup", pre := some s.pc },
      1, Nat.le_refl 1, Or.inl rfl, fun k => ?_⟩
    have hstep : step calls pipelineBody (stateAt (usUsIn env n b sc mk delim inString ws entw ep s13 c21 inc shr) s) =
        .jump (stateAt (usUsOut env n b sc mk delim inString ws entw ep s13 c21 inc shr w1 w2 w3 w4 r.ret)
          { s with mem := m'.mem, next := m'.next, pc := "for.cond.cleanup", pre := some s.pc }) := by
      refine step_of_blocks (b := pUsUs) (s' := stateAt (usUsOut env n b sc mk delim inString ws entw ep s13 c21 inc shr w1 w2 w3 w4 r.ret)
        { s with mem := m'.mem, next := m'.next }) ?_ ?_ ?_
      · simpa only [stateAt, hpc] using findBlock_usus
      · exact hcode
      · rw [pUsUs_term]
        refine execTerm_condbr_one ?_
        simp only [stateAt, usUsOut, cells, evalOperand, lookupName_cons_self, hb]
    exact runFuel_one_of_step hstep k

/-- **The `for.body.us` arm's iteration.**  One control step from the arm's head
reaches either the loop exit or the head of the next iteration. -/
theorem us_step (calls : Calls) (env : Env) (s : State) (n : BitVec 64)
    (b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry : Nat)
    (s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 : BitVec 64) (r : CallOutcome) (m' : CallOutcome)
    (hpc : s.pc = "for.body.us")
    (hcode : denoteCode calls pUs.instrs
        (stateAt (usIn env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry s13 c21 inc shr) s) =
      some (stateAt (usOut env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 r.ret)
        { s with mem := m'.mem, next := m'.next })) :
    ∃ (e : State) (j : Nat), j ≤ 1 ∧
      (e.pc = "for.cond.cleanup" ∨ e.pc = "for.body.us") ∧
      ∀ k, runFuel calls (j + k) pipelineBody
        (stateAt (usIn env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry s13 c21 inc shr) s) = runFuel calls k pipelineBody e := by
  obtain hb | hb := bitVec1_eq_zero_or_one (vexit inc shr)
  · refine ⟨stateAt (usOut env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 r.ret)
      { s with mem := m'.mem, next := m'.next, pc := "for.body.us", pre := some s.pc },
      1, Nat.le_refl 1, Or.inr rfl, fun k => ?_⟩
    have hstep : step calls pipelineBody (stateAt (usIn env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry s13 c21 inc shr) s) =
        .jump (stateAt (usOut env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 r.ret)
          { s with mem := m'.mem, next := m'.next, pc := "for.body.us", pre := some s.pc }) := by
      refine step_of_blocks (b := pUs) (s' := stateAt (usOut env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 r.ret)
        { s with mem := m'.mem, next := m'.next }) ?_ ?_ ?_
      · simpa only [stateAt, hpc] using findBlock_us
      · exact hcode
      · rw [pUs_term]
        refine execTerm_condbr_zero ?_
        simp only [stateAt, usOut, cells, evalOperand, lookupName_cons_self, hb]
    exact runFuel_one_of_step hstep k
  · refine ⟨stateAt (usOut env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 r.ret)
      { s with mem := m'.mem, next := m'.next, pc := "for.cond.cleanup", pre := some s.pc },
      1, Nat.le_refl 1, Or.inl rfl, fun k => ?_⟩
    have hstep : step calls pipelineBody (stateAt (usIn env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry s13 c21 inc shr) s) =
        .jump (stateAt (usOut env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 r.ret)
          { s with mem := m'.mem, next := m'.next, pc := "for.cond.cleanup", pre := some s.pc }) := by
      refine step_of_blocks (b := pUs) (s' := stateAt (usOut env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 r.ret)
        { s with mem := m'.mem, next := m'.next }) ?_ ?_ ?_
      · simpa only [stateAt, hpc] using findBlock_us
      · exact hcode
      · rw [pUs_term]
        refine execTerm_condbr_one ?_
        simp only [stateAt, usOut, cells, evalOperand, lookupName_cons_self, hb]
    exact runFuel_one_of_step hstep k

/-- **The `for.body.us83` arm's iteration.**  One control step from the arm's head
reaches either the loop exit or the head of the next iteration. -/
theorem us83_step (calls : Calls) (env : Env) (s : State) (n : BitVec 64)
    (b sc mk delim inString ws entw ep : Nat)
    (s13 c21 inc shr w1 w2 w3 w4 : BitVec 64) (r : CallOutcome) (m' : CallOutcome)
    (hpc : s.pc = "for.body.us83")
    (hcode : denoteCode calls pUs83.instrs
        (stateAt (us83In env n b sc mk delim inString ws entw ep s13 c21 inc shr) s) =
      some (stateAt (us83Out env n b sc mk delim inString ws entw ep s13 c21 inc shr w1 w2 w3 w4 r.ret)
        { s with mem := m'.mem, next := m'.next })) :
    ∃ (e : State) (j : Nat), j ≤ 1 ∧
      (e.pc = "for.cond.cleanup" ∨ e.pc = "for.body.us83") ∧
      ∀ k, runFuel calls (j + k) pipelineBody
        (stateAt (us83In env n b sc mk delim inString ws entw ep s13 c21 inc shr) s) = runFuel calls k pipelineBody e := by
  obtain hb | hb := bitVec1_eq_zero_or_one (vexit inc shr)
  · refine ⟨stateAt (us83Out env n b sc mk delim inString ws entw ep s13 c21 inc shr w1 w2 w3 w4 r.ret)
      { s with mem := m'.mem, next := m'.next, pc := "for.body.us83", pre := some s.pc },
      1, Nat.le_refl 1, Or.inr rfl, fun k => ?_⟩
    have hstep : step calls pipelineBody (stateAt (us83In env n b sc mk delim inString ws entw ep s13 c21 inc shr) s) =
        .jump (stateAt (us83Out env n b sc mk delim inString ws entw ep s13 c21 inc shr w1 w2 w3 w4 r.ret)
          { s with mem := m'.mem, next := m'.next, pc := "for.body.us83", pre := some s.pc }) := by
      refine step_of_blocks (b := pUs83) (s' := stateAt (us83Out env n b sc mk delim inString ws entw ep s13 c21 inc shr w1 w2 w3 w4 r.ret)
        { s with mem := m'.mem, next := m'.next }) ?_ ?_ ?_
      · simpa only [stateAt, hpc] using findBlock_us83
      · exact hcode
      · rw [pUs83_term]
        refine execTerm_condbr_zero ?_
        simp only [stateAt, us83Out, cells, evalOperand, lookupName_cons_self, hb]
    exact runFuel_one_of_step hstep k
  · refine ⟨stateAt (us83Out env n b sc mk delim inString ws entw ep s13 c21 inc shr w1 w2 w3 w4 r.ret)
      { s with mem := m'.mem, next := m'.next, pc := "for.cond.cleanup", pre := some s.pc },
      1, Nat.le_refl 1, Or.inl rfl, fun k => ?_⟩
    have hstep : step calls pipelineBody (stateAt (us83In env n b sc mk delim inString ws entw ep s13 c21 inc shr) s) =
        .jump (stateAt (us83Out env n b sc mk delim inString ws entw ep s13 c21 inc shr w1 w2 w3 w4 r.ret)
          { s with mem := m'.mem, next := m'.next, pc := "for.cond.cleanup", pre := some s.pc }) := by
      refine step_of_blocks (b := pUs83) (s' := stateAt (us83Out env n b sc mk delim inString ws entw ep s13 c21 inc shr w1 w2 w3 w4 r.ret)
        { s with mem := m'.mem, next := m'.next }) ?_ ?_ ?_
      · simpa only [stateAt, hpc] using findBlock_us83
      · exact hcode
      · rw [pUs83_term]
        refine execTerm_condbr_one ?_
        simp only [stateAt, us83Out, cells, evalOperand, lookupName_cons_self, hb]
    exact runFuel_one_of_step hstep k

/-- **The `for.body` arm's iteration.**  One control step from the arm's head
reaches either the loop exit or the head of the next iteration. -/
theorem body_step (calls : Calls) (env : Env) (s : State) (n : BitVec 64)
    (b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry : Nat)
    (s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 : BitVec 64) (r : CallOutcome) (m' : CallOutcome)
    (hpc : s.pc = "for.body")
    (hcode : denoteCode calls pBody.instrs
        (stateAt (bodyIn env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry s13 c21 inc shr) s) =
      some (stateAt (bodyOut env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 r.ret)
        { s with mem := m'.mem, next := m'.next })) :
    ∃ (e : State) (j : Nat), j ≤ 1 ∧
      (e.pc = "for.cond.cleanup" ∨ e.pc = "for.body") ∧
      ∀ k, runFuel calls (j + k) pipelineBody
        (stateAt (bodyIn env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry s13 c21 inc shr) s) = runFuel calls k pipelineBody e := by
  obtain hb | hb := bitVec1_eq_zero_or_one (vexit inc shr)
  · refine ⟨stateAt (bodyOut env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 r.ret)
      { s with mem := m'.mem, next := m'.next, pc := "for.body", pre := some s.pc },
      1, Nat.le_refl 1, Or.inr rfl, fun k => ?_⟩
    have hstep : step calls pipelineBody (stateAt (bodyIn env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry s13 c21 inc shr) s) =
        .jump (stateAt (bodyOut env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 r.ret)
          { s with mem := m'.mem, next := m'.next, pc := "for.body", pre := some s.pc }) := by
      refine step_of_blocks (b := pBody) (s' := stateAt (bodyOut env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 r.ret)
        { s with mem := m'.mem, next := m'.next }) ?_ ?_ ?_
      · simpa only [stateAt, hpc] using findBlock_body
      · exact hcode
      · rw [pBody_term]
        refine execTerm_condbr_zero ?_
        simp only [stateAt, bodyOut, cells, evalOperand, lookupName_cons_self, hb]
    exact runFuel_one_of_step hstep k
  · refine ⟨stateAt (bodyOut env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 r.ret)
      { s with mem := m'.mem, next := m'.next, pc := "for.cond.cleanup", pre := some s.pc },
      1, Nat.le_refl 1, Or.inl rfl, fun k => ?_⟩
    have hstep : step calls pipelineBody (stateAt (bodyIn env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry s13 c21 inc shr) s) =
        .jump (stateAt (bodyOut env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 r.ret)
          { s with mem := m'.mem, next := m'.next, pc := "for.cond.cleanup", pre := some s.pc }) := by
      refine step_of_blocks (b := pBody) (s' := stateAt (bodyOut env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 r.ret)
        { s with mem := m'.mem, next := m'.next }) ?_ ?_ ?_
      · simpa only [stateAt, hpc] using findBlock_body
      · exact hcode
      · rw [pBody_term]
        refine execTerm_condbr_one ?_
        simp only [stateAt, bodyOut, cells, evalOperand, lookupName_cons_self, hb]
    exact runFuel_one_of_step hstep k

/-! ### One iteration at the state the previous iteration leaves

The four traces above are stated at `stateAt (armIn …) s`, an environment the
builder chose.  A loop instance cannot state its step there: the state a step
hands on is the one the run actually produced, whose environment is the
*builder the block computed*, not the builder its successor reads.  What the two
share is the read set, so the step is stated at the run's own state and the
trace is moved to it by `denoteCode_agree`.

Three facts make that move possible, and each is a fact about the semantics
rather than about this pipeline:

* `denoteCode_pc`: a block's instructions leave the program counter alone.  The
  transport relation does not carry the counter, and `step` reads it — the
  jump it produces writes `pre := some s.pc` — so the successor's predecessor
  field is only pinned once the counter is.
* `blockUses`: the names a trace must be transported over are the block's
  instruction read set **together with its terminator's operand**.  The
  terminator is evaluated at the state the block leaves, and it is the branch
  the step needs; `instrsUses` alone does not cover it.
* `lookupName_cells_of_notin`: a name the builder does not bind reads through
  to the incoming environment, which is what makes the transport's agreement
  dischargeable for the two names the builder leaves alone (the terminator's
  operand and the loop's entry register).

`denoteCode_pc` is not in `LeanLLVM.Semantics` because nothing else needs it;
`stateAt` and `cells` leave the counter untouched, so the transport itself never
had to. -/

/-- A store leaves the program counter alone. -/
theorem storeValue_pc {s s' : State} {ty : Ty} {v : Value} {addr : Nat}
    (h : storeValue s ty v addr = some s') : s'.pc = s.pc := by
  unfold storeValue at h
  repeat' split at h
  all_goals first
    | (injection h with h'; subst h'; rfl)
    | (cases h)

/-- An instruction leaves the program counter alone.  Every constructor either
fails, binds a destination, writes memory or moves the allocator base; none
reads or writes the block. -/
theorem evalInstr_pc {calls : Calls} {s s' : State} {i : Instr}
    (h : evalInstr calls s i = some s') : s'.pc = s.pc := by
  cases i <;>
    (simp only [evalInstr, Option.map] at h ⊢) <;>
    (repeat' split at h) <;>
    first
    | (injection h with h'; subst h'; rfl)
    | (cases h)
    | (rcases h with ⟨a, -, rfl⟩; rfl)
    | (exact storeValue_pc h)

/-- **A block's instructions leave the program counter alone.**  This is what
`step` needs: the terminator runs at the state the block leaves, and the jump it
produces writes that state's `pc` into the successor's predecessor field. -/
theorem denoteCode_pc {calls : Calls} {is : List Instr} {s s' : State}
    (h : denoteCode calls is s = some s') : s'.pc = s.pc := by
  induction is generalizing s with
  | nil => simp only [denoteCode, Option.some.injEq] at h; cases h; rfl
  | cons i is ih =>
      simp only [denoteCode] at h
      split at h
      · cases h
      · rename_i s1 hs1
        exact (ih h).trans (evalInstr_pc hs1)

/-- The name list a block's trace transports over: its instructions' read set
together with its terminator's operand.  The terminator is not one of the block's
instructions, and the step evaluates it at the state the block leaves. -/
def blockUses (b : Block) : List String := instrsUses b.instrs ++ b.term.uses

theorem instrsUses_subset_blockUses (b : Block) {n : String}
    (h : n ∈ instrsUses b.instrs) : n ∈ blockUses b :=
  List.mem_append_left _ h

theorem termUses_subset_blockUses (b : Block) {n : String}
    (h : n ∈ b.term.uses) : n ∈ blockUses b :=
  List.mem_append_right _ h

/-- Agreement at one name list is transitive.  The three carried fields are
equalities and the register agreement is pointwise, so the composition is the
one a chain of traces needs. -/
theorem AgreeOn.trans {ns : List String} {r s t : State}
    (h1 : AgreeOn ns r s) (h2 : AgreeOn ns s t) : AgreeOn ns r t :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1,
    fun n hn => (h1.2.2.2 n hn).trans (h2.2.2.2 n hn)⟩

/-- A name the builder does not bind reads through to the incoming environment. -/
theorem lookupName_cells_of_notin :
    ∀ (cs : List (String × Value)) (n : String) (env : Env),
      n ∉ cs.map (·.1) → lookupName (cells cs env) n = lookupName env n
  | [], _, _, _ => rfl
  | (k, v) :: cs, n, env, h => by
      have hk : k ≠ n := by intro hkn; exact h (by subst hkn; simp)
      simp only [cells, lookupName_cons_ne v (cells cs env) hk]
      exact lookupName_cells_of_notin cs n env (fun hc => h (List.mem_cons_of_mem _ hc))

/-! #### The four arms at the run's own state

Each lemma is the arm's iteration with the trace moved: the hypothesis `hagree`
says the run's state agrees with the trace's on the block's and terminator's read
set, `hcode` is the trace, and the conclusion is one `step` from the run's state
to either the next iteration's head or the loop exit, at cost one — the shape
`PipelineLoop.step` asks for.  The successors carry the run's own environment,
which is what a chain of iterations needs: the next lemma's `hagree` is about
*that* state.

What each `hagree` still needs is the staging: the trace's memory hypotheses (the
four mask words, the three load words, the call outcomes and the address bound)
are about the state's memory, and re-establishing the agreement at a successor
requires the units' own posts at the call sites.  That is the loop instance's
remaining obligation and it is stated per field at the end of this section. -/

/-- **The `for.body.us.us` arm, from the run's state.** -/
theorem usUs_step_at (calls : Calls) (env : Env) (s : State) (n : BitVec 64)
    (b sc mk delim inString ws entw ep : Nat)
    (s13 c21 inc shr w1 w2 w3 w4 : BitVec 64) (r : CallOutcome) (m' : CallOutcome)
    (hpc : s.pc = "for.body.us.us")
    (hagree : AgreeOn (blockUses pUsUs)
      (stateAt (usUsIn env n b sc mk delim inString ws entw ep s13 c21 inc shr) s) s)
    (hcode : denoteCode calls pUsUs.instrs
        (stateAt (usUsIn env n b sc mk delim inString ws entw ep s13 c21 inc shr) s) =
      some (stateAt (usUsOut env n b sc mk delim inString ws entw ep s13 c21 inc shr w1 w2 w3 w4 r.ret)
        { s with mem := m'.mem, next := m'.next })) :
    ∃ (e : State) (j : Nat), j ≤ 1 ∧
      (e.pc = "for.cond.cleanup" ∨ e.pc = "for.body.us.us") ∧
      ∀ k, runFuel calls (j + k) pipelineBody s = runFuel calls k pipelineBody e := by
  obtain ⟨t', ht', hag⟩ := denoteCode_agree calls pUsUs.instrs hagree
    (fun n hn => instrsUses_subset_blockUses pUsUs hn) hcode
  have hpc' : t'.pc = s.pc := denoteCode_pc ht'
  have hval : lookupName t'.env "%exitcond116.not" = some (.int 1 (vexit inc shr)) := by
    have h1 := hag.2.2.2 "%exitcond116.not" (by
      simp only [blockUses, pUsUs_term, Term.uses, Operand.regs]
      exact List.mem_append_right _ (List.mem_cons_self ..))
    rw [← h1]
    simp only [stateAt, usUsOut, cells, lookupName]
    simp +decide
  obtain hb | hb := bitVec1_eq_zero_or_one (vexit inc shr)
  · refine ⟨{ t' with pc := "for.body.us.us", pre := some s.pc }, 1, Nat.le_refl 1,
      Or.inr rfl, fun k => ?_⟩
    have hstep : step calls pipelineBody s =
        .jump { t' with pc := "for.body.us.us", pre := some s.pc } := by
      refine step_of_blocks (b := pUsUs) (s' := t') ?_ ?_ ?_
      · simpa only [hpc] using findBlock_usus
      · exact ht'
      · rw [pUsUs_term]
        have h := execTerm_condbr_zero (s := t') (c := Operand.reg "%exitcond116.not")
          (t := "for.cond.cleanup") (f := "for.body.us.us") (by
            simp only [evalOperand, hval, hb])
        simpa only [hpc'] using h
    exact runFuel_one_of_step hstep k
  · refine ⟨{ t' with pc := "for.cond.cleanup", pre := some s.pc }, 1, Nat.le_refl 1,
      Or.inl rfl, fun k => ?_⟩
    have hstep : step calls pipelineBody s =
        .jump { t' with pc := "for.cond.cleanup", pre := some s.pc } := by
      refine step_of_blocks (b := pUsUs) (s' := t') ?_ ?_ ?_
      · simpa only [hpc] using findBlock_usus
      · exact ht'
      · rw [pUsUs_term]
        have h := execTerm_condbr_one (s := t') (c := Operand.reg "%exitcond116.not")
          (t := "for.cond.cleanup") (f := "for.body.us.us") (by
            simp only [evalOperand, hval, hb])
        simpa only [hpc'] using h
    exact runFuel_one_of_step hstep k

/-- **The `for.body.us` arm, from the run's state.** -/
theorem us_step_at (calls : Calls) (env : Env) (s : State) (n : BitVec 64)
    (b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry : Nat)
    (s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 : BitVec 64) (r : CallOutcome)
    (m' : CallOutcome)
    (hpc : s.pc = "for.body.us")
    (hagree : AgreeOn (blockUses pUs)
      (stateAt (usIn env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry
        s13 c21 inc shr) s) s)
    (hcode : denoteCode calls pUs.instrs
        (stateAt (usIn env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry
          s13 c21 inc shr) s) =
      some (stateAt (usOut env n b sc mk delim inString ws backslash ctl entw ep xp nxp
        xcarry s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 r.ret)
        { s with mem := m'.mem, next := m'.next })) :
    ∃ (e : State) (j : Nat), j ≤ 1 ∧
      (e.pc = "for.cond.cleanup" ∨ e.pc = "for.body.us") ∧
      ∀ k, runFuel calls (j + k) pipelineBody s = runFuel calls k pipelineBody e := by
  obtain ⟨t', ht', hag⟩ := denoteCode_agree calls pUs.instrs hagree
    (fun n hn => instrsUses_subset_blockUses pUs hn) hcode
  have hpc' : t'.pc = s.pc := denoteCode_pc ht'
  have hval : lookupName t'.env "%exitcond115.not" = some (.int 1 (vexit inc shr)) := by
    have h1 := hag.2.2.2 "%exitcond115.not" (by
      simp only [blockUses, pUs_term, Term.uses, Operand.regs]
      exact List.mem_append_right _ (List.mem_cons_self ..))
    rw [← h1]
    simp only [stateAt, usOut, cells, lookupName]
    simp +decide
  obtain hb | hb := bitVec1_eq_zero_or_one (vexit inc shr)
  · refine ⟨{ t' with pc := "for.body.us", pre := some s.pc }, 1, Nat.le_refl 1,
      Or.inr rfl, fun k => ?_⟩
    have hstep : step calls pipelineBody s =
        .jump { t' with pc := "for.body.us", pre := some s.pc } := by
      refine step_of_blocks (b := pUs) (s' := t') ?_ ?_ ?_
      · simpa only [hpc] using findBlock_us
      · exact ht'
      · rw [pUs_term]
        have h := execTerm_condbr_zero (s := t') (c := Operand.reg "%exitcond115.not")
          (t := "for.cond.cleanup") (f := "for.body.us") (by
            simp only [evalOperand, hval, hb])
        simpa only [hpc'] using h
    exact runFuel_one_of_step hstep k
  · refine ⟨{ t' with pc := "for.cond.cleanup", pre := some s.pc }, 1, Nat.le_refl 1,
      Or.inl rfl, fun k => ?_⟩
    have hstep : step calls pipelineBody s =
        .jump { t' with pc := "for.cond.cleanup", pre := some s.pc } := by
      refine step_of_blocks (b := pUs) (s' := t') ?_ ?_ ?_
      · simpa only [hpc] using findBlock_us
      · exact ht'
      · rw [pUs_term]
        have h := execTerm_condbr_one (s := t') (c := Operand.reg "%exitcond115.not")
          (t := "for.cond.cleanup") (f := "for.body.us") (by
            simp only [evalOperand, hval, hb])
        simpa only [hpc'] using h
    exact runFuel_one_of_step hstep k

/-- **The `for.body.us83` arm, from the run's state.** -/
theorem us83_step_at (calls : Calls) (env : Env) (s : State) (n : BitVec 64)
    (b sc mk delim inString ws entw ep : Nat)
    (s13 c21 inc shr w1 w2 w3 w4 : BitVec 64) (r : CallOutcome) (m' : CallOutcome)
    (hpc : s.pc = "for.body.us83")
    (hagree : AgreeOn (blockUses pUs83)
      (stateAt (us83In env n b sc mk delim inString ws entw ep s13 c21 inc shr) s) s)
    (hcode : denoteCode calls pUs83.instrs
        (stateAt (us83In env n b sc mk delim inString ws entw ep s13 c21 inc shr) s) =
      some (stateAt (us83Out env n b sc mk delim inString ws entw ep s13 c21 inc shr w1 w2 w3 w4 r.ret)
        { s with mem := m'.mem, next := m'.next })) :
    ∃ (e : State) (j : Nat), j ≤ 1 ∧
      (e.pc = "for.cond.cleanup" ∨ e.pc = "for.body.us83") ∧
      ∀ k, runFuel calls (j + k) pipelineBody s = runFuel calls k pipelineBody e := by
  obtain ⟨t', ht', hag⟩ := denoteCode_agree calls pUs83.instrs hagree
    (fun n hn => instrsUses_subset_blockUses pUs83 hn) hcode
  have hpc' : t'.pc = s.pc := denoteCode_pc ht'
  have hval : lookupName t'.env "%exitcond114.not" = some (.int 1 (vexit inc shr)) := by
    have h1 := hag.2.2.2 "%exitcond114.not" (by
      simp only [blockUses, pUs83_term, Term.uses, Operand.regs]
      exact List.mem_append_right _ (List.mem_cons_self ..))
    rw [← h1]
    simp only [stateAt, us83Out, cells, lookupName]
    simp +decide
  obtain hb | hb := bitVec1_eq_zero_or_one (vexit inc shr)
  · refine ⟨{ t' with pc := "for.body.us83", pre := some s.pc }, 1, Nat.le_refl 1,
      Or.inr rfl, fun k => ?_⟩
    have hstep : step calls pipelineBody s =
        .jump { t' with pc := "for.body.us83", pre := some s.pc } := by
      refine step_of_blocks (b := pUs83) (s' := t') ?_ ?_ ?_
      · simpa only [hpc] using findBlock_us83
      · exact ht'
      · rw [pUs83_term]
        have h := execTerm_condbr_zero (s := t') (c := Operand.reg "%exitcond114.not")
          (t := "for.cond.cleanup") (f := "for.body.us83") (by
            simp only [evalOperand, hval, hb])
        simpa only [hpc'] using h
    exact runFuel_one_of_step hstep k
  · refine ⟨{ t' with pc := "for.cond.cleanup", pre := some s.pc }, 1, Nat.le_refl 1,
      Or.inl rfl, fun k => ?_⟩
    have hstep : step calls pipelineBody s =
        .jump { t' with pc := "for.cond.cleanup", pre := some s.pc } := by
      refine step_of_blocks (b := pUs83) (s' := t') ?_ ?_ ?_
      · simpa only [hpc] using findBlock_us83
      · exact ht'
      · rw [pUs83_term]
        have h := execTerm_condbr_one (s := t') (c := Operand.reg "%exitcond114.not")
          (t := "for.cond.cleanup") (f := "for.body.us83") (by
            simp only [evalOperand, hval, hb])
        simpa only [hpc'] using h
    exact runFuel_one_of_step hstep k

/-- **The `for.body` arm, from the run's state.** -/
theorem body_step_at (calls : Calls) (env : Env) (s : State) (n : BitVec 64)
    (b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry : Nat)
    (s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 : BitVec 64) (r : CallOutcome)
    (m' : CallOutcome)
    (hpc : s.pc = "for.body")
    (hagree : AgreeOn (blockUses pBody)
      (stateAt (bodyIn env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry
        s13 c21 inc shr) s) s)
    (hcode : denoteCode calls pBody.instrs
        (stateAt (bodyIn env n b sc mk delim inString ws backslash ctl entw ep xp nxp xcarry
          s13 c21 inc shr) s) =
      some (stateAt (bodyOut env n b sc mk delim inString ws backslash ctl entw ep xp nxp
        xcarry s13 c21 inc shr w1 w2 w3 w4 w5 w6 w7 r.ret)
        { s with mem := m'.mem, next := m'.next })) :
    ∃ (e : State) (j : Nat), j ≤ 1 ∧
      (e.pc = "for.cond.cleanup" ∨ e.pc = "for.body") ∧
      ∀ k, runFuel calls (j + k) pipelineBody s = runFuel calls k pipelineBody e := by
  obtain ⟨t', ht', hag⟩ := denoteCode_agree calls pBody.instrs hagree
    (fun n hn => instrsUses_subset_blockUses pBody hn) hcode
  have hpc' : t'.pc = s.pc := denoteCode_pc ht'
  have hval : lookupName t'.env "%exitcond.not" = some (.int 1 (vexit inc shr)) := by
    have h1 := hag.2.2.2 "%exitcond.not" (by
      simp only [blockUses, pBody_term, Term.uses, Operand.regs]
      exact List.mem_append_right _ (List.mem_cons_self ..))
    rw [← h1]
    simp only [stateAt, bodyOut, cells, lookupName]
    simp +decide
  obtain hb | hb := bitVec1_eq_zero_or_one (vexit inc shr)
  · refine ⟨{ t' with pc := "for.body", pre := some s.pc }, 1, Nat.le_refl 1,
      Or.inr rfl, fun k => ?_⟩
    have hstep : step calls pipelineBody s =
        .jump { t' with pc := "for.body", pre := some s.pc } := by
      refine step_of_blocks (b := pBody) (s' := t') ?_ ?_ ?_
      · simpa only [hpc] using findBlock_body
      · exact ht'
      · rw [pBody_term]
        have h := execTerm_condbr_zero (s := t') (c := Operand.reg "%exitcond.not")
          (t := "for.cond.cleanup") (f := "for.body") (by
            simp only [evalOperand, hval, hb])
        simpa only [hpc'] using h
    exact runFuel_one_of_step hstep k
  · refine ⟨{ t' with pc := "for.cond.cleanup", pre := some s.pc }, 1, Nat.le_refl 1,
      Or.inl rfl, fun k => ?_⟩
    have hstep : step calls pipelineBody s =
        .jump { t' with pc := "for.cond.cleanup", pre := some s.pc } := by
      refine step_of_blocks (b := pBody) (s' := t') ?_ ?_ ?_
      · simpa only [hpc] using findBlock_body
      · exact ht'
      · rw [pBody_term]
        have h := execTerm_condbr_one (s := t') (c := Operand.reg "%exitcond.not")
          (t := "for.cond.cleanup") (f := "for.body") (by
            simp only [evalOperand, hval, hb])
        simpa only [hpc'] using h
    exact runFuel_one_of_step hstep k

/-! ### What each body fact still needs

The four steps above are the loop instance's *arm dispatch*: an iteration at a
state that agrees with the arm's builder on the block's and terminator's read set
reaches the next iteration or the exit at cost one.  Turning them into the
`PipelineBodyFacts` fields is not a further lemma but three staging obligations,
one per field.  Each is recorded here with its clause, so a later reader starts
from the obstruction rather than rediscovering it.

**The loop's cell half: the terminator's stale register.**  A successor's
environment is the builder the block computed, so the successor agrees with the
*next* iteration's builder on the builder's own cells — that agreement is a
finite computation over the two cell lists.  It does **not** extend to the
terminator's operand: the successor binds `%exitcond…` to the value the block
just computed, while the incoming builder does not bind it at all, so the
transport's `instrsUses` set — which excludes destinations — must be replaced by
`blockUses`, and the builder must then supply the *old* `%exitcond…` as well.  It
cannot, because no builder binds a destination.  The loop's invariant must
therefore carry the predecessor's exit word itself (the value the predecessor's
outgoing builder bound), and the arm's step is stated at a state whose
environment supplies it rather than at a bare builder state.  That is a fact
about `AgreeOn`: the relation is over a *static* read set, and a destination read
by a terminator is read but not listed.

**The loop's memory half: the carried carry.**  The traces read four mask words,
three block words, two call outcomes and the address bound.  The mask call's post
(`masksPost`) supplies the four mask words and the outgoing carry slot, so what
the next iteration's mask call needs is a *readability* fact about the document
block and a *content* fact about the carry slot, and both are consequences of the
mask post and the staging's window.

The content clauses of `pipelineUnitsPost` are existential — `ent`, `ps`, `out`
and `evs` are not pinned by the post — so a whole-stream invariant of the entry
or position stream is **not** needed: what the invariant must carry is the two
counts, their capacity bounds and readability at `ep` and `xp`, and readability
survives a run that only writes bytes.  Two things are nevertheless missing:

* the carry pair is supplied by the escape list's own post.  The run stores the
  block's outgoing run-open and run-parity words at `carry`, and
  `escapePositionsPost` states them as `carryPair m carry (carry64 lo hi st)
  (IsBackslashB (hi ⟨31, by decide⟩)) (carry64 lo hi st).oddRun` — the same
  definition the mask record's `%sc` clause supplies through
  `carryPair_of_carrySlot`.  The pre's carry-versus-stream exclusion keeps the
  batch's stores off that slot, so the pair the next iteration's escape call
  reads is a consequence of the post rather than an obligation with no
  supplier.
* the counts' growth needs the room clause discussed next.

**The staging's arithmetic.**  The POS8 record's `pre` requires
`k + 64 * ent.length + 9 < 2 ^ 63` at the entry count the body passes, and the
escape record's requires `xn0 < 2 ^ 63`; the initial cursors' own bounds do not
survive growth, so `pipelineStaging` states the room once — `cursorRoom nk0
blocks 9` and `cursorRoom nxp0 blocks 9` — and both units' clauses follow from it
by `cursorRoom_bounds`.  `staging_count_bound_not_implied` below is the witness
the room clause answers: one block, `nk0 = 2 ^ 63 - 1`, and a capacity of
`2 ^ 63 + 100` satisfy the initial-cursor bound, the block count's `uint32` bound
and the capacity clause, and the count the second iteration passes is above the
bound the POS8 record asks for.  The escape count has the same shape, with
`nxp0` and the positions `64 * blocks` add in place of `nk0`.

**The seed.**  The three steps to the loop head are `entry`, `for.body.lr.ph` and
one of the two split blocks, and the traces for those are here
(`entry_denote`, `lrPh_denote`, and the split blocks' empty instruction lists).
The first iteration's traces are here too: `usUs_split_denote`,
`us_split_denote`, `us83_split_denote` and `body_split_denote` state the four
arm heads at the split predecessor, where every `phi` selects the split operand
and the carried triple is `(0, %0, 0)`.  What remains for the `seed` field is
not a trace: it is the join of the three dispatch traces across their builders —
the `AgreeOn` facts the loop's cell half above describes — together with the
loop instance's own `Inv`, which is the `PipelineLoop` the caller supplies.  No
instance for this body exists in the tree, so the field stays a hypothesis of the
composition until one does.

**The tail.**  `for.cond.cleanup`, `if.then33`, `if.end34` and `cleanup` are
traced here, and the tail's own stores and calls are consequent.  The post's
clauses about `dst`, `ev`, `ndst`, `nev` and `err` are facts about the memory the
stage-2 call leaves, and `PipelineBodyFacts` is parametric in the stage-2 record
`Γ2` with only `CallSatisfies` and the verdict's range as its hypotheses; those
clauses are not consequences of an arbitrary `Γ2`.  The pin that would supply
them is `Γ2 := Γ_stage2`, and it is **deferred, not missing**: `Γ_stage2` does not
exist in this tree, so `PipelineBodyFacts.exit` is stated at the arbitrary slot
until the slice that lands that record substitutes it and consumes the post
shapes it states.  A record invented here would state stage 2's write set where
it is convenient rather than where it is measured. -/

/-- **The initial cursors' bounds do not imply the room.**  A one-block document
with `nk0 = 2 ^ 63 - 1` and a capacity at `2 ^ 63 + 100` satisfies
`nk0 < 2 ^ 63`, the block count's `uint32` bound and the entry-stream capacity
clause, and the count the second iteration passes is at or above `2 ^ 63` —
which the POS8 record's `pre` refuses
(`k + 64 * ent.length + 9 < 2 ^ 63` at `ent.length = 1`).  The same construction
fails `cursorRoom nk0 blocks 9`, and the same argument applies to the escape
count with `nxp0` in place of `nk0`. -/
theorem staging_count_bound_not_implied :
    ∃ (nk0 blocks : Nat) (epcap : BitVec 64),
      nk0 < 2 ^ 63 ∧ 64 * blocks + 63 < 2 ^ 32 ∧
      nk0 + 64 * blocks + 9 ≤ epcap.toNat ∧
      ¬ (nk0 + 64 * 1 + 9 < 2 ^ 63) := by
  refine ⟨2 ^ 63 - 1, 1, BitVec.ofNat 64 (2 ^ 63 + 100), ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  · omega

/-! ### Axiom footprints

The split predecessor's builders are cell lists, and its four traces are
`pipeline_block_eval` facts like the arm traces: neither adds to the module's
footprint. -/

/-- info: 'LeanLLVM.Vellum.PipelineBodyFacts.usUsSplitIn' does not depend on any axioms -/
#guard_msgs in
#print axioms usUsSplitIn

/-- info: 'LeanLLVM.Vellum.PipelineBodyFacts.usUsSplitOut' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms usUsSplitOut

/-- info: 'LeanLLVM.Vellum.PipelineBodyFacts.usSplitIn' does not depend on any axioms -/
#guard_msgs in
#print axioms usSplitIn

/-- info: 'LeanLLVM.Vellum.PipelineBodyFacts.usSplitOut' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms usSplitOut

/-- info: 'LeanLLVM.Vellum.PipelineBodyFacts.us83SplitIn' does not depend on any axioms -/
#guard_msgs in
#print axioms us83SplitIn

/-- info: 'LeanLLVM.Vellum.PipelineBodyFacts.us83SplitOut' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms us83SplitOut

/-- info: 'LeanLLVM.Vellum.PipelineBodyFacts.bodySplitIn' does not depend on any axioms -/
#guard_msgs in
#print axioms bodySplitIn

/-- info: 'LeanLLVM.Vellum.PipelineBodyFacts.bodySplitOut' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bodySplitOut

/-- info: 'LeanLLVM.Vellum.PipelineBodyFacts.usUs_split_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms usUs_split_denote

/-- info: 'LeanLLVM.Vellum.PipelineBodyFacts.us_split_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms us_split_denote

/-- info: 'LeanLLVM.Vellum.PipelineBodyFacts.us83_split_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms us83_split_denote

/-- info: 'LeanLLVM.Vellum.PipelineBodyFacts.body_split_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms body_split_denote

end PipelineBodyFacts

open LeanLLVM.JSON (Block32)
open LeanLLVM.Vellum.JsonScanSpec
open LeanLLVM.Vellum.JsonS1MasksIR (block64 carrySlot)
open LeanLLVM.Vellum.PipelineBodyFacts
open LeanLLVM.Vellum.JsonPipelineBlockEval (pUsUs usUsIn usUsOut)
open LeanLLVM.Vellum.BlockEval (stateAt)

/-! ### The escape record's block clause, read as an address

`Γ_escape_positions.pre` reads the block at `blockAddr blk0 = blk0.toNat * 64` — a
document *offset* — through `readBytes`, an *absolute address*.  The pipeline's
staging places the document at `b` with `3 ≤ b` and passes the loop index as
`blk0`.  At `b = 3` the staging's own clauses determine the read at address `0`
to the shifted window, so the escape `pre` is refused there. -/

/-- Sixty-four bytes with a single backslash at lane 5: a document whose
backslash word is not the shifted window's. -/
def escapeWitnessDoc : List UInt8 :=
  List.replicate 5 0x61 ++ [0x5C] ++ List.replicate 58 0x61

theorem escapeWitnessDoc_length : escapeWitnessDoc.length = 64 := by
  simp [escapeWitnessDoc]

/-- The low half of a sixty-four byte list. -/
def blockLo (bs : List UInt8) (h : bs.length = 64) : Block32 :=
  fun i => bs.get ⟨i.val, by have := i.isLt; omega⟩

/-- The high half of a sixty-four byte list. -/
def blockHi (bs : List UInt8) (h : bs.length = 64) : Block32 :=
  fun i => bs.get ⟨32 + i.val, by have := i.isLt; omega⟩

theorem block64_split (bs : List UInt8) (h : bs.length = 64) :
    block64 (blockLo bs h) (blockHi bs h) = bs := by
  have h1 : List.ofFn (blockLo bs h) = bs.take 32 := by
    apply List.ext_getElem
    · simp [blockLo, List.length_take, h]
    · intro k hk1 hk2
      rw [List.getElem_ofFn, List.getElem_take]
      simp [blockLo]
  have h2 : List.ofFn (blockHi bs h) = bs.drop 32 := by
    apply List.ext_getElem
    · simp [blockHi, List.length_drop, h]
    · intro k hk1 hk2
      rw [List.getElem_ofFn, List.getElem_drop]
      simp [blockHi]
  rw [block64, h1, h2, List.take_append_drop]

/-- The witness document's block, as the memory holds it. -/
def escapeWitnessBlock : List UInt8 :=
  block64 (blockLo escapeWitnessDoc escapeWitnessDoc_length)
    (blockHi escapeWitnessDoc escapeWitnessDoc_length)

/-- The sixty-four bytes at the document's *offset* when the document starts
three bytes up: the zero prefix and the block's first sixty-one bytes. -/
def escapeShiftedDoc : List UInt8 := ([0, 0, 0] ++ escapeWitnessBlock).take 64

theorem escapeWitnessBlock_length : escapeWitnessBlock.length = 64 :=
  block64_length _ _

theorem escapeShiftedDoc_length : escapeShiftedDoc.length = 64 := by
  simp [escapeShiftedDoc, escapeWitnessBlock_length]

def escapeShiftedLo : Block32 := blockLo escapeShiftedDoc escapeShiftedDoc_length

def escapeShiftedHi : Block32 := blockHi escapeShiftedDoc escapeShiftedDoc_length

theorem escapeShiftedDoc_eq_halves :
    block64 escapeShiftedLo escapeShiftedHi = escapeShiftedDoc :=
  block64_split escapeShiftedDoc escapeShiftedDoc_length

/-- **The block's backslash word is not its own three-byte shift's.** -/
theorem escapeShifted_backslash_differ (st st' : ClassState) :
    specBackslash64 escapeShiftedLo escapeShiftedHi st ≠
      specBackslash64 (blockLo escapeWitnessDoc escapeWitnessDoc_length)
        (blockHi escapeWitnessDoc escapeWitnessDoc_length) st' := by
  obtain ⟨i, o⟩ := st
  obtain ⟨i', o'⟩ := st'
  cases i <;> cases o <;> cases i' <;> cases o' <;> decide

/-- **The first block's escape clause reads the shifted window.** -/
theorem escapeWindow_at_three {mem : Mem} {lo hi : Block32}
    (hprefix : readBytes mem 0 3 = some [0, 0, 0])
    (hwin : readBytes mem 3 64 = some (block64 lo hi)) :
    readBytes mem 0 64 = some (([0, 0, 0] ++ block64 lo hi).take 64) := by
  have hcat : readBytes mem 0 (3 + 64) = some ([0, 0, 0] ++ block64 lo hi) :=
    JsonEntrySteps.readBytes_append mem 3 0 [0, 0, 0] 64 (block64 lo hi) hprefix hwin
  have h67 : readBytes mem 0 (64 + 3) = some ([0, 0, 0] ++ block64 lo hi) := by
    rw [show (64 + 3 : Nat) = 3 + 64 from rfl]; exact hcat
  obtain ⟨hpre, -⟩ := readBytes_split mem 0 64 3 h67
  exact hpre

/-- **The block clause is not vacuous.**  When the block *is* at the address the
offset names, the clause holds at once — so the refusal below is about the
staging's base and not about a clause nothing can meet.  This is the same
detector's affirmative control, in the same section. -/
theorem escapePre_block_clause_satisfiable :
    ∃ (mem : Mem) (lo hi : Block32),
      readBytes mem (blockAddr (BitVec.ofNat 64 0)) 64 = some (block64 lo hi) := by
  refine ⟨writeBytes [] 0 escapeWitnessBlock,
    blockLo escapeWitnessDoc escapeWitnessDoc_length,
    blockHi escapeWitnessDoc escapeWitnessDoc_length, ?_⟩
  have h := readBytes_writeBytes_same (m := ([] : Mem)) escapeWitnessBlock (addr := 0)
  rw [escapeWitnessBlock_length] at h
  simpa [blockAddr, escapeWitnessBlock] using h

theorem block64_inj {lo hi lo' hi' : Block32} (h : block64 lo hi = block64 lo' hi') :
    lo = lo' ∧ hi = hi' := by
  constructor
  · funext i
    have hlt : i.val < 32 := i.isLt
    have := congrArg (fun l => l[i.val]?) h
    simpa only [block64_getElem?_lo hlt, ofFn_getElem?_of_lt hlt, Option.some.injEq]
      using this
  · funext i
    have hlt : i.val < 32 := i.isLt
    have := congrArg (fun l => l[i.val + 32]?) h
    simpa only [block64_getElem?_hi hlt, ofFn_getElem?_of_lt hlt, Option.some.injEq]
      using this

/-- The escape record's `pre`, at the clauses a call site reads. -/
theorem escape_pre_shape {budget : List Value → Mem → Nat} {args : List Value} {mem : Mem}
    {next : Nat} (h : (Γ_escape_positions budget).pre args mem next) :
    ∃ (xp xn carry : Nat) (blk0 : BitVec 64) (bs ctl im : BitVec 64) (lo hi : Block32)
      (st : ClassState),
      args = [.int 64 bs, .int 64 ctl, .int 64 im, .int 64 blk0, .ptr xp, .ptr xn,
        .ptr carry] ∧
      readBytes mem (blockAddr blk0) 64 = some (block64 lo hi) ∧
      bs = specBackslash64 lo hi st ∧
      ctl = specControl64 lo hi st ∧
      im = specInString64 lo hi st := by
  obtain ⟨xp, xn, carry, blk0, bs, ctl, im, lo, hi, st, -, -, -,
    hargs, hblock, hbs, hctl, him, -⟩ := h
  exact ⟨xp, xn, carry, blk0, bs, ctl, im, lo, hi, st, hargs, hblock, hbs, hctl, him⟩

/-- Integer values are injective at their width. -/
theorem value_int_eq_iff {w : Nat} {a b : BitVec w} :
    (Value.int w a = Value.int w b) ↔ a = b := by
  constructor
  · intro h; injection h
  · intro h; rw [h]

/-- **The escape record refuses the staged document.**  With the document at
address `3` and the three zero bytes below it, the block clause's read at
`blockAddr 0 = 0` is the shifted window, whose backslash word is not the block's;
the `pre` therefore asks for two different blocks at once. -/
theorem escapePre_refused_by_the_staged_window {mem : Mem} {bs ctl im : BitVec 64}
    {st' : ClassState} {xp xn carry next : Nat}
    (hprefix : readBytes mem 0 3 = some [0, 0, 0])
    (hwin : readBytes mem 3 64 = some escapeWitnessBlock)
    (hbs : bs = specBackslash64 (blockLo escapeWitnessDoc escapeWitnessDoc_length)
      (blockHi escapeWitnessDoc escapeWitnessDoc_length) st') :
    ¬ (Γ_escape_positions (fun _ _ => 0)).pre
      [.int 64 bs, .int 64 ctl, .int 64 im, .int 64 0, .ptr xp, .ptr xn, .ptr carry]
      mem next := by
  intro h
  obtain ⟨xp', xn', carry', blk0, bs', ctl', im', lo, hi, st, hargs, hblock, hbs', -, -⟩ :=
    escape_pre_shape h
  simp only [List.cons.injEq, and_true, value_int_eq_iff, Value.ptr.injEq] at hargs
  obtain ⟨hbsEq, -, -, hblkEq, -, -, -⟩ := hargs
  have hzero : blockAddr blk0 = 0 := by
    rw [← hblkEq]
    simp [blockAddr]
  rw [hzero] at hblock
  have hshift : readBytes mem 0 64 = some escapeShiftedDoc := by
    simpa [escapeShiftedDoc, escapeWitnessBlock] using escapeWindow_at_three hprefix hwin
  have heq : block64 lo hi = escapeShiftedDoc := by
    have hs : some (block64 lo hi) = some escapeShiftedDoc := by rw [← hblock, hshift]
    exact Option.some.inj hs
  obtain ⟨rfl, rfl⟩ := block64_inj (heq.trans escapeShiftedDoc_eq_halves.symm)
  refine escapeShifted_backslash_differ st st' ?_
  rw [← hbs, hbsEq, hbs']


/-! ### The loop instance: the arm, the carried state, the invariant

The instance is `PipelineLoop (pipelineCalls tab s2) pipelineBody` with the
iteration bound `pipelineBlocks n`, per-iteration cost one, and `pipelineLoopInv`
below.  Its `step` is the four arm traces at the run's own state; the conjunct
list is what those traces read, checked one conjunct at a time against the step
that consumes it and the post or frame that hands it on:

|conjunct|consumed by|handed on by|
|---|---|---|
|`s.pc = arm.head ∧ s.pre = some arm.head`|the arm step's `hpc` and `findBlock_*`|the arm step's successor, whose `pre` is the state's `pc`|
|`S.i + (r + 1) = blocks`, `S.shr = ofNat 64 blocks`, `S.iw = ofNat 64 S.i`|the arm's exit test `%exitcond… = eq (i + 1) shr`, so which successor a step takes|the successor's `i + 1` from `%inc`, and `shr` untouched by the arm|
|`AgreeOn (blockUses arm.block) (stateAt (arm.inBuilder s.env S) s) s`|the arm step's `hagree`, i.e. `denoteCode_transport`|the transport's agreement with the arm's *outgoing* builder, whose cells are the next builder's parameters|
|`readBytes s.mem b (64 * blocks) = some doc`|`masksPre_at`'s block read at `b + 64 * i`, and the arms' four mask words through the mask unit's post|every unit record's unchanged-outside conjunct, at the region separations also carried|
|`readBytes s.mem sc 24 = some (carrySlot …)`, `stM.oddRun = (opened && ppar)`|`masksPre_at`'s carry clause|`masksPost`'s write at `c`|
|`carryPair s.mem xcarry stE prevb prevs` (gate-on arms)|the escape list's `pre` carry clause|`escapePositionsPost`'s `carryPair m carry …`, which the post's own third exclusion makes true|
|`cursorRoom k (blocks - i) 9`, `cursorRoom xn (blocks - i) 9`|POS8's `k + 64 * nblk + 9 < 2 ^ 63` and the escape list's `xn0 < 2 ^ 63`, via `cursorRoom_bounds`|the count's growth (at most sixty-four per block) against one fewer block left|
|`HasBytes s.mem xp (4 * blockMax xn)`|the escape list's `pre` capacity clause|the batch's writes at `xp + 4 * xn` and the post's unchanged-outside conjunct|
|the three mask separations, at the staged window's extent|`masksPre_at`'s three disjunctions|static: they name addresses, not bytes|
|the three escape exclusions, at the stream's staged capacity|the escape list's count and carry exclusions|static, and stated at the capacity because a per-block extent is not preserved by the count's growth|

**What is deliberately absent, and why each absence is not an omission.**
The run state's register lookups are the transport agreement's own content, and
adding them would restate it; the iteration's block as two halves is
`blockRead_of_window`'s read of the carried window at `64 * i`, so a carried
copy would be a second statement of that clause; the entry stream's and the
entry word's readability are created by the body's own store and the emitters'
writes and consumed by no arm step.  Each of the three was in the first draft of
this list and is removed here as dead weight rather than kept for completeness.

**One clause has no supplier, and it is why the instance does not close.**
`Γ_escape_positions.pre`'s block clause is `readBytes mem (blockAddr blk0) 64`,
and `blockAddr blk0 = blk0.toNat * 64` is the block's *document offset*, not its
address.  The pipeline passes the loop index as `blk0` and stages the document at
`b` with `3 ≤ b`, so at the first block (`blk0 = 0`) the clause reads address
`0`.  `escapePre_refused_by_the_staged_window` below proves the refusal: at
`b = 3` the staging's prefix and window clauses determine that read to the
shifted window, and its backslash word is not the block's, so the `pre` asks for
two different blocks at once — the signature clause, executed.  The gate-on arms
(`for.body.us`, `for.body`) therefore have no escape conjunct a step can
preserve, and the seed cannot establish one either.  It is a statement change to
the escape record, reported to the planner rather than worked around here; the
gate-off arms' conjuncts are the ones above, all with a supplier.

**Ruled, and why this section stays.** The record's block clause is dropped from
both `pre` and `post`: the list's own header says the block is read from the
caller's masks only and the unit never reads `b`, so the clause obliged the caller
for a memory access the body does not perform, and re-basing it to
`base + blockAddr blk0` would make that false claim true.  The specification link
survives as a *value* — the block's bytes become a parameter of the record and the
position base is arithmetic inside the post — which is the owning coder's edit in
`JsonEscapeSteps.lean`/`JsonEscapeListContract.lean`.  This section is the
executed evidence for that decision and for the gate-on arms' missing conjuncts,
and it stays in the module: an omission recorded with its measurement is the only
form in which the record can carry a gap. -/

/-- The four unswitched copies of the loop body, by the arm the entry selection
took: bit 0 selects the entry emitter, bit 1 the escape list's gate. -/
inductive PipelineBodyArm where
  | pos8NoGate
  | pos8Gate
  | b8NoGate
  | b8Gate
  deriving DecidableEq, Repr

/-- The block the arm's iteration runs. -/
def PipelineBodyArm.block : PipelineBodyArm → Block
  | .pos8NoGate => pUsUs
  | .pos8Gate => pUs
  | .b8NoGate => pUs83
  | .b8Gate => pBody

/-- The block's name, which is also the state's program counter. -/
def PipelineBodyArm.head : PipelineBodyArm → String
  | .pos8NoGate => "for.body.us.us"
  | .pos8Gate => "for.body.us"
  | .b8NoGate => "for.body.us83"
  | .b8Gate => "for.body"

/-- Does the arm call the escape list?  Bit 1 of the selector. -/
def PipelineBodyArm.hasEscape : PipelineBodyArm → Bool
  | .pos8NoGate => false
  | .pos8Gate => true
  | .b8NoGate => false
  | .b8Gate => true

/-- The values the loop carries from one iteration to the next, and the shape
the run was staged at.

**What is here is what an arm step reads**: the three live words, the exit
bound, the block index, this iteration's block, the mask unit's carry slot and
state, the entry word's slot, the two counts, the escape list's stream and its
carry pair, and the six extents the units' `pre` clauses name.  What is *not*
here is anything a step can derive or does not read:

* the run state's register lookups — the transport's agreement carries them, and
  the agreement is stated at the builder the arm's trace uses, so a lookup conjunct
  would restate the agreement's own content;
* the iteration's block as two halves — it is `blockRead_of_window`'s read of the
  staged window at `64 * i`, so carrying it would be a second statement of the
  window clause;
* the entry stream's and the entry word's readability — the body's own store and
  the emitters' writes create those bytes, and every unit record's frame leaves
  them readable, so no arm step consumes a carried clause about them. -/
structure PipelineLoopCarried where
  /-- Which of the four unswitched copies this iteration runs. -/
  arm : PipelineBodyArm
  /-- The block index, `%i.080`, and its sixty-four-bit form. -/
  i : Nat
  iw : BitVec 64
  /-- The other two live words the arm carries, `%prevS` and `%k`. -/
  sw : BitVec 64
  kw : BitVec 64
  /-- The exit bound `%shr`: the document's block count, sixty-four bits. -/
  shr : BitVec 64
  /-- The document, the address it is staged at, and its length argument. -/
  b : Nat
  doc : List UInt8
  n : BitVec 64
  /-- The mask unit's carry slot and the state its three words hold. -/
  sc : Nat
  stM : ClassState
  opened : Bool
  ppar : Bool
  inside : Bool
  /-- The mask slot and the five offsets the selection block derives from it. -/
  maskSlot : Nat
  delim : Nat
  inString : Nat
  ws : Nat
  backslash : Nat
  ctl : Nat
  /-- The entry word's slot and the entry stream's base. -/
  entw : Nat
  ep : Nat
  /-- The escape list's stream, its count slot and its carry slot. -/
  xp : Nat
  nxp : Nat
  xcarry : Nat
  stE : ClassState
  prevb : Bool
  prevs : Bool
  /-- The two counts. -/
  k : Nat
  xn : Nat
  /-- The escape stream's staged capacity, `nxp0 + 64 * blocks + 8`: the extent
  the escape record's exclusions are stated at, because a per-block extent is not
  preserved by the count's growth. -/
  xpExtent : Nat
  /-- The first iteration's count, kept because `cursorRoom` is stated from it. -/
  k0 : Nat
  xn0 : Nat

/-- The arm's incoming builder, at the carried values: the four traces are stated
one per arm, so the agreement the transport consumes is stated at the same
builder. -/
def PipelineBodyArm.inBuilder (a : PipelineBodyArm) (env : Env)
    (S : PipelineLoopCarried) : Env :=
  match a with
  | .pos8NoGate =>
      usUsIn env S.n S.b S.sc S.maskSlot S.delim S.inString S.ws S.entw S.ep
        S.sw S.kw S.iw S.shr
  | .pos8Gate =>
      usIn env S.n S.b S.sc S.maskSlot S.delim S.inString S.ws S.backslash S.ctl
        S.entw S.ep S.xp S.nxp S.xcarry S.sw S.kw S.iw S.shr
  | .b8NoGate =>
      us83In env S.n S.b S.sc S.maskSlot S.delim S.inString S.ws S.entw S.ep
        S.sw S.kw S.iw S.shr
  | .b8Gate =>
      bodyIn env S.n S.b S.sc S.maskSlot S.delim S.inString S.ws S.backslash S.ctl
        S.entw S.ep S.xp S.nxp S.xcarry S.sw S.kw S.iw S.shr

/-- **The loop invariant.**  With `r + 1` iterations of budget the state is the
entry of the loop's next iteration at the arm the document's selector chose; with
the budget spent it is the loop's exit block, which is the shape
`PipelineLoop.exit` consumes.  Every conjunct names the step that reads it:

* `pc`/`pre` and the agreement — the arm step's `hpc` and `hagree`
  (`usUs_step_at` … `body_step_at`), i.e. the transport;
* `i`, `iw`, `shr` and the budget — the arm's exit test
  `%exitcond… = eq (i + 1) shr`, hence which of the two successors a step takes;
* the window — `masksPre_at`'s block read, and the arms' four mask words
  through the mask unit's post;
* the mask carry slot and `stM.oddRun` — `masksPre_at`'s carry clause;
* the escape carry pair — the escape list's `pre` carry clause (gate-on arms);
* the two `cursorRoom` clauses — POS8's `k + 64 * nblk + 9 < 2 ^ 63` and the
  escape list's `xn0 < 2 ^ 63` through `cursorRoom_bounds`;
* `HasBytes xp` — the escape list's capacity clause;
* the three mask separations — `masksPre_at`'s three disjunctions;
* the three escape exclusions — the escape list's count and carry exclusions.
  They are stated at the stream's *staged capacity* rather than at the current
  count, because the current count grows and a per-block extent is not preserved
  by the growth; the capacity extent is a staging fact and survives every step. -/
def pipelineLoopInv (blocks : Nat) : Nat → State → Prop
  | 0, s => s.pc = "for.cond.cleanup"
  | r + 1, s =>
      ∃ (S : PipelineLoopCarried),
        s.pc = S.arm.head ∧
        s.pre = some S.arm.head ∧
        S.i + (r + 1) = blocks ∧
        S.shr = BitVec.ofNat 64 blocks ∧
        S.iw = BitVec.ofNat 64 S.i ∧
        AgreeOn (blockUses S.arm.block) (stateAt (S.arm.inBuilder s.env S) s) s ∧
        readBytes s.mem S.b (64 * blocks) = some S.doc ∧
        readBytes s.mem S.sc 24 = some (carrySlot S.opened S.ppar S.inside) ∧
        S.stM.oddRun = (S.opened && S.ppar) ∧
        (S.arm.hasEscape = true →
          carryPair s.mem S.xcarry S.stE S.prevb S.prevs) ∧
        cursorRoom S.k (blocks - S.i) 9 ∧
        cursorRoom S.xn (blocks - S.i) 9 ∧
        HasBytes s.mem S.xp (4 * blockMax S.xn) ∧
        (S.b + 64 * blocks ≤ S.sc ∨ S.sc + 24 ≤ S.b) ∧
        (S.b + 64 * blocks ≤ S.maskSlot ∨ S.maskSlot + 48 ≤ S.b) ∧
        (S.sc + 24 ≤ S.maskSlot ∨ S.maskSlot + 48 ≤ S.sc) ∧
        (S.nxp + 8 ≤ S.xp ∨ S.xp + 4 * S.xpExtent ≤ S.nxp) ∧
        (S.xcarry + 16 ≤ S.nxp ∨ S.nxp + 8 ≤ S.xcarry) ∧
        (S.xcarry + 16 ≤ S.xp ∨ S.xp + 4 * S.xpExtent ≤ S.xcarry)

/-- The states the loop may leave in: the exit block, which carries the loop's
counts to the tail. -/
def pipelineLoopExit (s : State) : Prop := s.pc = "for.cond.cleanup"

/-- At a spent budget the invariant is the exit predicate, which is the shape
`PipelineLoop.exit` consumes: no step is owed from `Inv 0`. -/
theorem pipelineLoopInv_zero {blocks : Nat} {s : State}
    (h : pipelineLoopInv blocks 0 s) : pipelineLoopExit s := h

/-- **`PipelineLoop.exit`'s obligation, discharged.**  A spent budget is the loop's
exit block, so from any state the invariant admits at `r = 0` the loop's exit is
already reached and the prefix is the zero-length one.  The last iteration is
therefore `step`'s at `r = 0` — where the arm's own exit test fires and the
successor is `for.cond.cleanup` — and not `exit`'s. -/
theorem pipelineLoop_exitObligation (calls : Calls) (blocks : Nat) (s : State)
    (h : pipelineLoopInv blocks 0 s) :
    ∃ (e : State) (j : Nat), j ≤ 0 ∧ pipelineLoopExit e ∧
      ∀ k, runFuel calls (j + k) pipelineBody s = runFuel calls k pipelineBody e :=
  ⟨s, 0, Nat.le_refl 0, h, fun k => by rw [Nat.zero_add]⟩

/-- **The invariant's gate-on conjunct, and the clause that refuses it.**  For the
arms that call the escape list the invariant carries no fact that yields the
record's block clause: the clause reads `blockAddr blk0 = blk0.toNat * 64`, the
block's document offset, as an absolute address, while the staging places the
block at `b + 64 * i` with `3 ≤ b`.  At the first block and `b = 3` the read the
clause asks for is the shifted window, so the `pre` is refused (the theorem
below).  The conjunct is therefore absent from `pipelineLoopInv` rather than
present without a supplier: a conjunct no step preserves is a defect, and adding
one that no staging can seed would move the defect into the proof. -/
theorem pipelineLoopInv_escape_conjunct_unseeded :
    ∀ (budget : List Value → Mem → Nat) (mem : Mem) (next : Nat) (bs ctl im : BitVec 64)
      (st' : ClassState) (xp xn carry : Nat),
      readBytes mem 0 3 = some ([0, 0, 0] : List UInt8) →
      readBytes mem 3 64 = some ((block64 (blockLo escapeWitnessDoc
        escapeWitnessDoc_length) (blockHi escapeWitnessDoc
        escapeWitnessDoc_length) : List UInt8)) →
      bs = specBackslash64 (blockLo escapeWitnessDoc escapeWitnessDoc_length)
        (blockHi escapeWitnessDoc escapeWitnessDoc_length) st' →
      ¬ (Γ_escape_positions budget).pre
        [.int 64 bs, .int 64 ctl, .int 64 im, .int 64 0, .ptr xp, .ptr xn, .ptr carry]
        mem next := by
  intro budget mem next bs ctl im st' xp xn carry hprefix hwin hbs
  exact escapePre_refused_by_the_staged_window (mem := mem) (bs := bs) (ctl := ctl)
    (im := im) (st' := st') (xp := xp) (xn := xn) (carry := carry) (next := next)
    hprefix hwin hbs



/-! ### Axiom footprints

The refusal is a kernel computation over one sixty-four-byte document, its
three-byte shift and the record's `pre`; the invariant is a definition.  Nothing
here adds a carrier: the whole section is at `[propext, Quot.sound]`, and the
builder dispatch is a definition and depends on nothing. -/

/-- info: 'LeanLLVM.Vellum.escapePre_refused_by_the_staged_window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapePre_refused_by_the_staged_window

/-- info: 'LeanLLVM.Vellum.pipelineLoopInv_escape_conjunct_unseeded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pipelineLoopInv_escape_conjunct_unseeded

/-- info: 'LeanLLVM.Vellum.PipelineBodyArm.inBuilder' does not depend on any axioms -/
#guard_msgs in
#print axioms PipelineBodyArm.inBuilder

/-- info: 'LeanLLVM.Vellum.pipelineLoopInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pipelineLoopInv

/-- info: 'LeanLLVM.Vellum.pipelineLoopInv_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pipelineLoopInv_zero

/-- info: 'LeanLLVM.Vellum.pipelineLoop_exitObligation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pipelineLoop_exitObligation

/-- info: 'LeanLLVM.Vellum.escapeShifted_backslash_differ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapeShifted_backslash_differ

/-- info: 'LeanLLVM.Vellum.escapeWindow_at_three' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapeWindow_at_three

/-- info: 'LeanLLVM.Vellum.escapePre_block_clause_satisfiable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapePre_block_clause_satisfiable

end LeanLLVM.Vellum
