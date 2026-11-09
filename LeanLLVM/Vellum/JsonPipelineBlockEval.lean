/-
The pos8 no-gate arm's blocks, closed by the block evaluator.

This module is the artifact `BlockEval` is measured by, and it says what it is
not: it is **the automation's sufficiency on one arm**, not the pipeline's proof.
The pipeline's twelve blocks are the arm-specialised loop body in four copies,
and the copy here is the one `arm & 1 = 0`, `arm & 2 = 0` selects — the position
body with no density gate.  Three blocks of that arm are here: the entry, the
loop body, and the cleanup.  Nothing in `JsonPipelineIR` is edited: its pinned
AST is read, and the instruction lists below are its own literals, pinned back to
it by `decide`.

**Why this arm.**  It is the first the four-way copy selects, so its line count
is the baseline a second arm's copies are measured against.  The loop body is
thirty-three instructions with two calls in it, which is where the
per-instruction rate of the bespoke idiom would be paid four times over.

**What is proved.**  Each theorem is `denoteCode calls instrs (stateAt envIn s) =
some (stateAt envOut s)` for its block, with `envIn`/`envOut` the
`BlockEval.cells` builders.  The caller's parameters are the incoming builder's
cells, not hypotheses: a block's statement names the values it reads, and the
tactic resolves every register read against the builder by `String` equality —
**no register lookup appears as a hypothesis in any theorem here**.  What remains
a hypothesis is the semantic staging no block proof can discharge: the memory
the loads read, the two calls' outcomes, and the `getelementptr` address bound.

**The measured cost.**  Three blocks, seven theorems (the loop body and the
cleanup are stated once per predecessor, because `phi` selects on the
predecessor field), in the counts recorded at the module's end.  The bespoke rate
is `JsonEscapeListBody`'s: about 950 lines for three blocks.  Here each block's
*trace* is one `block_eval` invocation; the bulk is the statement's environment
builder, which the bespoke idiom does not write down because it carries the same
information as a list of lookup hypotheses instead.
-/
import LeanLLVM.Vellum.BlockEval
import LeanLLVM.Vellum.JsonPipelineIR

set_option autoImplicit false
set_option maxRecDepth 16000

namespace LeanLLVM.Vellum.JsonPipelineBlockEval

open LeanLLVM
open LeanLLVM.Vellum.BlockEval
open LeanLLVM.Vellum.JsonPipelineIR (pipelineBody lit)

/-! ### The blocks, by index -/

/-- A block by index, so a block is named without restating it. -/
def blockAt (f : Function) (i : Nat) (h : i < f.blocks.length) : Block := f.blocks[i]

def pEntry := blockAt pipelineBody 0 (by decide)
def pUsUs := blockAt pipelineBody 3 (by decide)
def pCleanup := blockAt pipelineBody 11 (by decide)

theorem findBlock_entry : pipelineBody.findBlock "entry" = some pEntry := by decide

theorem findBlock_usus :
    pipelineBody.findBlock "for.body.us.us" = some pUsUs := by decide

theorem findBlock_cleanup : pipelineBody.findBlock "cleanup" = some pCleanup := by decide

/-! ### The pinned instruction lists

The three blocks' instructions, restated from the pinned AST and decided back
against it: a change to the fixture that moved an instruction fails here rather
than becoming a proof obligation elsewhere. -/

theorem pEntry_instrs :
    pEntry.instrs =
      [Instr.binop "%add" (BinOp.add) 64 (Operand.reg "%n") (lit 64 63),
       Instr.binop "%shr" (BinOp.lshr) 64 (Operand.reg "%add") (lit 64 6),
       Instr.load "%0" (Ty.int 64) (Operand.reg "%nk"),
       Instr.icmp "%cmp79.not" (IPred.ult) 64 (Operand.reg "%add") (lit 64 64)] := by
  decide

theorem pUsUs_instrs :
    pUsUs.instrs =
      [Instr.phi "%prevS.082.us.us" (Ty.int 64) [("for.body.us.us", Operand.reg "%shr13.us.us"), ("for.body.lr.ph.split.us", lit 64 0)],
       Instr.phi "%k.081.us.us" (Ty.int 64) [("for.body.us.us", Operand.reg "%call21.us.us"), ("for.body.lr.ph.split.us", Operand.reg "%0")],
       Instr.phi "%i.080.us.us" (Ty.int 64) [("for.body.us.us", Operand.reg "%inc.us.us"), ("for.body.lr.ph.split.us", lit 64 0)],
       Instr.binop "%shl.us.us" (BinOp.shl) 64 (Operand.reg "%i.080.us.us") (lit 64 6),
       Instr.gep "%add.ptr.us.us" (Ty.int 8) (Operand.reg "%b") (Operand.reg "%shl.us.us"),
       Instr.callVoid "leanllvm_json_s1_masks" [(Ty.ptr, Operand.reg "%add.ptr.us.us"), (Ty.ptr, Operand.reg "%sc"), (Ty.ptr, Operand.reg "%mk")],
       Instr.load "%1" (Ty.int 64) (Operand.reg "%mk"),
       Instr.load "%2" (Ty.int 64) (Operand.reg "%delim"),
       Instr.load "%3" (Ty.int 64) (Operand.reg "%in_string"),
       Instr.load "%4" (Ty.int 64) (Operand.reg "%ws"),
       Instr.binop "%5" (BinOp.or) 64 (Operand.reg "%1") (Operand.reg "%4"),
       Instr.binop "%6" (BinOp.or) 64 (Operand.reg "%5") (Operand.reg "%2"),
       Instr.binop "%or2.us.us" (BinOp.or) 64 (Operand.reg "%6") (Operand.reg "%3"),
       Instr.binop "%not.us.us" (BinOp.xor) 64 (Operand.reg "%or2.us.us") (lit 64 (-1)),
       Instr.binop "%not6.us.us" (BinOp.xor) 64 (Operand.reg "%3") (lit 64 (-1)),
       Instr.binop "%and.us.us" (BinOp.and) 64 (Operand.reg "%2") (Operand.reg "%not6.us.us"),
       Instr.binop "%shl8.us.us" (BinOp.shl) 64 (Operand.reg "%not.us.us") (lit 64 1),
       Instr.binop "%or9.us.us" (BinOp.or) 64 (Operand.reg "%shl8.us.us") (Operand.reg "%prevS.082.us.us"),
       Instr.binop "%not10.us.us" (BinOp.xor) 64 (Operand.reg "%or9.us.us") (lit 64 (-1)),
       Instr.binop "%and11.us.us" (BinOp.and) 64 (Operand.reg "%not10.us.us") (Operand.reg "%not.us.us"),
       Instr.binop "%7" (BinOp.or) 64 (Operand.reg "%and.us.us") (Operand.reg "%and11.us.us"),
       Instr.binop "%or12.us.us" (BinOp.or) 64 (Operand.reg "%7") (Operand.reg "%1"),
       Instr.binop "%shr13.us.us" (BinOp.lshr) 64 (Operand.reg "%not.us.us") (lit 64 63),
       Instr.binop "%sub.us.us" (BinOp.sub) 64 (Operand.reg "%n") (Operand.reg "%shl.us.us"),
       Instr.icmp "%cmp15.us.us" (IPred.ult) 64 (Operand.reg "%sub.us.us") (lit 64 64),
       Instr.binop "%notmask.us.us" (BinOp.shl) 64 (lit 64 (-1)) (Operand.reg "%sub.us.us"),
       Instr.binop "%sub17.us.us" (BinOp.xor) 64 (Operand.reg "%notmask.us.us") (lit 64 (-1)),
       Instr.select "%and18.us.us" (Ty.int 64) (Operand.reg "%cmp15.us.us") (Operand.reg "%sub17.us.us") (lit 64 (-1)),
       Instr.binop "%ent.0.us.us" (BinOp.and) 64 (Operand.reg "%or12.us.us") (Operand.reg "%and18.us.us"),
       Instr.store (Ty.int 64) (Operand.reg "%ent.0.us.us") (Operand.reg "%entw"),
       Instr.call "%call21.us.us" (Ty.int 64) "leanllvm_json_entry_pos8" [(Ty.ptr, Operand.reg "%entw"), (Ty.int 64, Operand.reg "%i.080.us.us"), (Ty.int 64, lit 64 1), (Ty.ptr, Operand.reg "%ep"), (Ty.int 64, Operand.reg "%k.081.us.us")],
       Instr.binop "%inc.us.us" (BinOp.add) 64 (Operand.reg "%i.080.us.us") (lit 64 1),
       Instr.icmp "%exitcond116.not" (IPred.eq) 64 (Operand.reg "%inc.us.us") (Operand.reg "%shr")] := by
  decide

theorem pCleanup_instrs :
    pCleanup.instrs =
      [Instr.phi "%retval.0" (Ty.int 64) [("if.then33", lit 64 0), ("if.end34", Operand.reg "%call35")]] := by
  decide

/-! ### The literal spellings and the block's values

A literal's value is the instruction's own: `BitVec.ofInt`, which is what
`JsonPipelineIR.lit` writes.  The value abbreviations are the loop body's own
arithmetic, in the order the block computes it — the same device the bespoke
traces use (`em1`…`em13` in `JsonEscapeListBody`), but here they name values the
statement's builder holds rather than steps a proof must rewrite through. -/

abbrev litv (w : Nat) (v : Int) : BitVec w := BitVec.ofInt w v

abbrev negOne : BitVec 64 := litv 64 (-1)
abbrev one : BitVec 64 := litv 64 1

/-- `%i <<< 6`: the byte offset of a group of eight lanes. -/
abbrev sh6 (i : BitVec 64) : BitVec 64 := i <<< (litv 64 6).toNat

abbrev v5 (w1 w4 : BitVec 64) : BitVec 64 := w1 ||| w4
abbrev v6 (w1 w2 w4 : BitVec 64) : BitVec 64 := v5 w1 w4 ||| w2
abbrev vor2 (w1 w2 w3 w4 : BitVec 64) : BitVec 64 := v6 w1 w2 w4 ||| w3
abbrev vnot (w1 w2 w3 w4 : BitVec 64) : BitVec 64 := vor2 w1 w2 w3 w4 ^^^ negOne
abbrev vnot6 (w3 : BitVec 64) : BitVec 64 := w3 ^^^ negOne
abbrev vand (w2 w3 : BitVec 64) : BitVec 64 := w2 &&& vnot6 w3
abbrev vshl8 (w1 w2 w3 w4 : BitVec 64) : BitVec 64 := vnot w1 w2 w3 w4 <<< (litv 64 1).toNat
abbrev vor9 (w1 w2 w3 w4 s13 : BitVec 64) : BitVec 64 := vshl8 w1 w2 w3 w4 ||| s13
abbrev vnot10 (w1 w2 w3 w4 s13 : BitVec 64) : BitVec 64 := vor9 w1 w2 w3 w4 s13 ^^^ negOne
abbrev vand11 (w1 w2 w3 w4 s13 : BitVec 64) : BitVec 64 :=
  vnot10 w1 w2 w3 w4 s13 &&& vnot w1 w2 w3 w4
abbrev v7 (w1 w2 w3 w4 s13 : BitVec 64) : BitVec 64 :=
  vand w2 w3 ||| vand11 w1 w2 w3 w4 s13
abbrev vor12 (w1 w2 w3 w4 s13 : BitVec 64) : BitVec 64 := v7 w1 w2 w3 w4 s13 ||| w1
abbrev vshr13 (w1 w2 w3 w4 : BitVec 64) : BitVec 64 := vnot w1 w2 w3 w4 >>> (litv 64 63).toNat
abbrev vsub (n i : BitVec 64) : BitVec 64 := n - sh6 i
abbrev vcmp (n i : BitVec 64) : BitVec 1 := evalICmp .ult (vsub n i) (litv 64 64)
abbrev vnotmask (n i : BitVec 64) : BitVec 64 := negOne <<< (vsub n i).toNat
abbrev vsub17 (n i : BitVec 64) : BitVec 64 := vnotmask n i ^^^ negOne
abbrev vand18 (n i : BitVec 64) : BitVec 64 := if vcmp n i = 1 then vsub17 n i else negOne
abbrev vent (n i w1 w2 w3 w4 s13 : BitVec 64) : BitVec 64 :=
  vor12 w1 w2 w3 w4 s13 &&& vand18 n i
abbrev vinc (i : BitVec 64) : BitVec 64 := i + one
abbrev vexit (i shr : BitVec 64) : BitVec 1 := evalICmp .eq (vinc i) shr

/-! ### The three blocks -/

/-- The entry's incoming builder: the caller's `%n` and `%nk`. -/
def entryIn (env : Env) (n : BitVec 64) (nk : Nat) : Env :=
  cells [("%nk", .ptr nk), ("%n", .int 64 n)] env

/-- The entry's outgoing builder, newest first. -/
def entryOut (env : Env) (n w0 : BitVec 64) (nk : Nat) : Env :=
  cells [("%cmp79.not", .int 1 (evalICmp .ult (n + litv 64 63) (litv 64 64))),
         ("%0", .int 64 w0),
         ("%shr", .int 64 ((n + litv 64 63) >>> (litv 64 6).toNat)),
         ("%add", .int 64 (n + litv 64 63))] (entryIn env n nk)

/-- `%add = %n + 63`, `%shr = %add >>> 6`, `%0 = *%nk`, `%cmp79.not = %add < 64`.
The block has no predecessor, so no `phi`. -/
theorem entry_denote (calls : Calls) (env : Env) (s : State) (n w0 : BitVec 64) (nk : Nat)
    (hld : readBytes s.mem nk 8 = some (natToBytes w0.toNat 8)) :
    denoteCode calls pEntry.instrs (stateAt (entryIn env n nk) s) =
      some (stateAt (entryOut env n w0 nk) s) := by
  rw [pEntry_instrs]
  simp only [lit, entryIn, entryOut]
  block_eval

/-- The cleanup's incoming builder: the tail's `%call35` result. -/
def cleanupIn (env : Env) (v : BitVec 64) : Env :=
  cells [("%call35", .int 64 v)] env

/-- One `phi` and the return, entered from `if.then33` with the zero the tail
returns. -/
theorem cleanup_fromIfThen (calls : Calls) (env : Env) (s : State) (v : BitVec 64)
    (hpre : s.pre = some "if.then33") :
    denoteCode calls pCleanup.instrs (stateAt (cleanupIn env v) s) =
      some (stateAt (cells [("%retval.0", .int 64 (litv 64 0))] (cleanupIn env v)) s) := by
  rw [pCleanup_instrs]
  simp only [lit, cleanupIn]
  block_eval

/-- The same block entered from `if.end34`, where the selected operand is the
call's result. -/
theorem cleanup_fromIfEnd (calls : Calls) (env : Env) (s : State) (v : BitVec 64)
    (hpre : s.pre = some "if.end34") :
    denoteCode calls pCleanup.instrs (stateAt (cleanupIn env v) s) =
      some (stateAt (cells [("%retval.0", .int 64 v)] (cleanupIn env v)) s) := by
  rw [pCleanup_instrs]
  simp only [lit, cleanupIn]
  block_eval

/-! ### The loop body

`for.body.us.us`: thirty-three instructions, the `s1_masks` call and the
`entry_pos8` call among them.  Its chain is derived by `block_eval`, and its
side goals close on the same invocation.  The two values that the earlier
revision could not join — `%i.080.us.us` and `%k.081.us.us` in the position
call's argument list — are the phi results the block's own builder holds: the
automation's last `rfl` runs after the side goals, so the lookups resolve the
values the statement names and the call's argument list is the statement's, not
a fresh copy's.

The incoming builder names the caller's `%n`, the block's pointer arguments,
the three values the back edge carries into the phi nodes, and the outgoing
`%shr`.  The outgoing builder is the block's results in the order it computes
them.  The staging hypotheses are the caller's: the four word loads at the
memory the `s1_masks` call leaves, the `getelementptr` bound, and the two calls'
outcomes — the second at the memory the block's own store leaves.  No register
read appears as a hypothesis. -/

/-- The loop body's incoming builder: the caller's `%n`, the pointer arguments
(`%b`, `%sc`, `%mk`, `%delim`, `%in_string`, `%ws`, `%entw`, `%ep`), the three
values the back edge carries into the phi nodes (`%shr13.us.us`,
`%call21.us.us`, `%inc.us.us`), and `%shr`. -/
def usUsIn (env : Env) (n : BitVec 64) (b sc mk delim inString ws entw ep : Nat)
    (s13 c21 inc shr : BitVec 64) : Env :=
  cells [("%shr", .int 64 shr),
         ("%inc.us.us", .int 64 inc), ("%call21.us.us", .int 64 c21),
         ("%shr13.us.us", .int 64 s13),
         ("%ep", .ptr ep), ("%entw", .ptr entw), ("%ws", .ptr ws),
         ("%in_string", .ptr inString), ("%delim", .ptr delim), ("%mk", .ptr mk),
         ("%sc", .ptr sc), ("%b", .ptr b), ("%n", .int 64 n)] env

/-- The loop body's outgoing builder: its thirty-three results, newest first.
`ret` is the `entry_pos8` call's return value. -/
def usUsOut (env : Env) (n : BitVec 64) (b sc mk delim inString ws entw ep : Nat)
    (s13 c21 inc shr : BitVec 64) (w1 w2 w3 w4 : BitVec 64) (ret : Value) : Env :=
  cells [("%exitcond116.not", .int 1 (vexit inc shr)),
         ("%inc.us.us", .int 64 (vinc inc)),
         ("%call21.us.us", ret),
         ("%ent.0.us.us", .int 64 (vent n inc w1 w2 w3 w4 s13)),
         ("%and18.us.us", .int 64 (vand18 n inc)),
         ("%sub17.us.us", .int 64 (vsub17 n inc)),
         ("%notmask.us.us", .int 64 (vnotmask n inc)),
         ("%cmp15.us.us", .int 1 (vcmp n inc)),
         ("%sub.us.us", .int 64 (vsub n inc)),
         ("%shr13.us.us", .int 64 (vshr13 w1 w2 w3 w4)),
         ("%or12.us.us", .int 64 (vor12 w1 w2 w3 w4 s13)),
         ("%7", .int 64 (v7 w1 w2 w3 w4 s13)),
         ("%and11.us.us", .int 64 (vand11 w1 w2 w3 w4 s13)),
         ("%not10.us.us", .int 64 (vnot10 w1 w2 w3 w4 s13)),
         ("%or9.us.us", .int 64 (vor9 w1 w2 w3 w4 s13)),
         ("%shl8.us.us", .int 64 (vshl8 w1 w2 w3 w4)),
         ("%and.us.us", .int 64 (vand w2 w3)),
         ("%not6.us.us", .int 64 (vnot6 w3)),
         ("%not.us.us", .int 64 (vnot w1 w2 w3 w4)),
         ("%or2.us.us", .int 64 (vor2 w1 w2 w3 w4)),
         ("%6", .int 64 (v6 w1 w2 w4)),
         ("%5", .int 64 (v5 w1 w4)),
         ("%4", .int 64 w4),
         ("%3", .int 64 w3),
         ("%2", .int 64 w2),
         ("%1", .int 64 w1),
         ("%add.ptr.us.us", .ptr (b + (BitVec.signExtend 64 (sh6 inc)).toNat)),
         ("%shl.us.us", .int 64 (sh6 inc)),
         ("%i.080.us.us", .int 64 inc),
         ("%k.081.us.us", .int 64 c21),
         ("%prevS.082.us.us", .int 64 s13)]
    (usUsIn env n b sc mk delim inString ws entw ep s13 c21 inc shr)

/-- **The loop body derives its chain and closes its side goals.**  Entered from
its back edge, `for.body.us.us` computes its thirty-three results and reaches
the last comparison with the builder's own environment.  The hypotheses are the
caller's staging: the loads at the memory after `s1_masks`, the address bound,
and the two calls' outcomes.  No register lookup is a hypothesis. -/
theorem usUs_denote (calls : Calls) (env : Env) (s : State) (n : BitVec 64)
    (b sc mk delim inString ws entw ep : Nat)
    (s13 c21 inc shr w1 w2 w3 w4 : BitVec 64)
    (r1 r2 : CallOutcome)
    (hpre : s.pre = some "for.body.us.us")
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
      r1.next = some r2) :
    denoteCode calls pUsUs.instrs
        (stateAt (usUsIn env n b sc mk delim inString ws entw ep s13 c21 inc shr) s) =
      some (stateAt (usUsOut env n b sc mk delim inString ws entw ep s13 c21 inc shr
        w1 w2 w3 w4 r2.ret) { s with mem := r2.mem, next := r2.next }) := by
  rw [pUsUs_instrs]
  simp only [lit, usUsIn, usUsOut]
  block_eval

/-! **Measured, at this revision.**  `JsonEscapeListBody` is 1 110 lines and
spends them on three blocks; of that, the three instruction traces
(`entry_denote`, `ifThen_denote`, `ifEnd_denote`) are 143 lines and the rest is
the per-register lookup hypotheses and the `show` reconciliations those traces
carry.  This module's three closed blocks cost the theorem statements plus one
`block_eval` each: 22 lines for `entry` (statement 12, proof 4, builders 6), 14
lines for the two `cleanup` statements and proofs, and 79 lines for the loop
body — 49 lines of incoming and outgoing builders and a 29-line theorem (a
21-line statement and a three-line proof).  Per closed block the trace is one
tactic invocation against
the bespoke idiom's ~48 lines of instruction trace per block, and the statements
carry builders instead of lookup hypotheses.  The loop body is the measurement
that matters: its side goals close on the same invocation, with the position
call's two phi-carried operands assigned by the builder rather than named as
hypotheses. -/
end LeanLLVM.Vellum.JsonPipelineBlockEval
