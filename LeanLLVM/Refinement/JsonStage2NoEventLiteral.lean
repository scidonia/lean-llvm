/-
The no-event entry's emitted literal compare, as a region of the pinned body.

`stage2NoEventBody` (the 167-block entry at
`probes/install/ir/stage2-noevent.candidate.ll`) inlines `ne_lit`: the source
function's loop over the literal's packed bytes is emitted as one unrolled
`icmp eq i8` chain behind the block `if.end519`, with the literal selected by a
*shared* `phi` — `%lit.0`, `%ln.0`, `%tag.0` and the width selector
`%exitcond38.not.i.3` are each one `phi` whose incoming entries name the three
call-site predecessors `if.then504` (`false`, five bytes), `if.then509` (`null`,
four) and `LeafBlock68` (`true`, four), and the same chain runs for all three.
The chain is therefore parameterised by `(lit, ln)` through those `phi`s, and
the general statement below quantifies over them.  The fixture-side check is the
`#guard` on `%lit.0`'s and `%exitcond38.not.i.3`'s incoming lists: it reads the
pinned `if.end519` block and requires exactly those three predecessor/value
entries, so a re-capture that inlines three separate chains, or renames a
predecessor, fails the pin rather than leaving the general theorem describing a
shape the body no longer has.  `stage2NoEventLitChain_true`/`_false`/`_null` are
the three instances at that shared `phi`.

This module proves the chain's rule: from `if.end519`, the emitted compare
returns the first differing byte's offset, the token's length when the token is
shorter than the literal, and the literal's width when the token is longer —
exactly `neLitCheck`'s verdict and offset (`JsonStage2NoEventBody`), which
`neLitCheck_eq_litCheck` identifies with the certified `lit_check`.  The
statement is a **run to the chain's exit block**, not a `Satisfies` at a
function: the chain is a region and its two exits are blocks of the pinned body,
`if.then527` on refusal and `if.end545` on acceptance.  A `Satisfies` would need
a `ret` the region does not have; the post-literal tail (the whitespace skip,
`after_value`, `accept`) is the walk's subject, not this one.

**What is claimed, and what is not.**  The theorem says the chain writes no
memory (`e.mem = s.mem`) and reaches one of the two exits.  The run stops at
`if.then527`'s *entry*, so its `%ei520.0.ph` `phi` has not run and the cell is
not bound by anything this region proves; the offset is therefore stated as the
selection that entry state fixes:
`∃ op, phiIncoming (e.pre.getD "") ifThen527EiIncoming = some op ∧
evalOperand e op = some (.int 64 (ofNat i))`, with `neLitCheck … = some i`.  The
accepting exit carries `neLitCheck … = none`.  The refusal block's own writes —
`%add529 = ei + %idxprom` to `%off`, the `od_gap_recover` call, the four stores
and the `%ei520.0.ph` binding — are *outside* this region and are the walk's to
compose; binding the selection into the cell is its first step there.  In short,
`ne_lit`'s `*ei` is the token-relative offset the phi selects for that cell, and
the run proves the selection, not the binding.

The pins are generated from the parse in `JsonStage2HelperIRNumFast`'s idiom:
each block's instruction list is a `def` and the `findBlock` equation is a
`decide`; the body literal itself is `JsonStage2NoEventIR`'s `#guard`ed parse,
so a re-capture that moves a chain block fails the build here rather than
silently re-pointing a step.
-/
import LeanLLVM.Refinement.JsonStage2NoEventBody
import LeanLLVM.Refinement.BlockEval
import LeanLLVM.Refinement.JsonEntrySteps
import LeanLLVM.Refinement.DepthCountRefine

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2NoEventIR (stage2NoEventBody)

/-! ### The chain's blocks, pinned

Each instruction list is the literal the generated pin resolves the name to; the
`findBlock` equation is a `decide` on the parsed body. -/

/-- `if.end519`: the four `phi`s (literal, width selector, length, tag) and the
token length `%sub524`, ending in the zero-length test. -/
def stage2NoEventLitChainIfEnd519Instrs : List Instr :=
[
      Instr.phi "%lit.0" (Ty.int 64) [("if.then504", (Operand.imm (.int 64 (BitVec.ofNat 64 435728179558)))), ("if.then509", (Operand.imm (.int 64 (BitVec.ofNat 64 1819047278)))), ("LeafBlock68", (Operand.imm (.int 64 (BitVec.ofNat 64 1702195828))))],
      Instr.phi "%exitcond38.not.i.3" (Ty.int 1) [("if.then504", (Operand.imm (.int 1 (BitVec.ofNat 1 0)))), ("if.then509", (Operand.imm (.int 1 (BitVec.ofNat 1 1)))), ("LeafBlock68", (Operand.imm (.int 1 (BitVec.ofNat 1 1))))],
      Instr.phi "%ln.0" (Ty.int 64) [("if.then504", (Operand.imm (.int 64 (BitVec.ofNat 64 5)))), ("if.then509", (Operand.imm (.int 64 (BitVec.ofNat 64 4)))), ("LeafBlock68", (Operand.imm (.int 64 (BitVec.ofNat 64 4))))],
      Instr.phi "%tag.0" (Ty.int 64) [("if.then504", (Operand.imm (.int 64 (BitVec.ofNat 64 9)))), ("if.then509", (Operand.imm (.int 64 (BitVec.ofNat 64 10)))), ("LeafBlock68", (Operand.imm (.int 64 (BitVec.ofNat 64 8))))],
      Instr.binop "%sub524" BinOp.sub 64 (Operand.reg "%ee.1") (Operand.reg "%idxprom.lcssa"),
      Instr.icmp "%exitcond.not.i" IPred.eq 64 (Operand.reg "%sub524") (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
      ]

theorem stage2NoEventLitChain_findBlock_if_end519 :
    stage2NoEventBody.findBlock "if.end519" =
      some ⟨"if.end519", stage2NoEventLitChainIfEnd519Instrs, Term.condbr (Operand.reg "%exitcond.not.i") "if.then527" "if.end.i"⟩ := by decide

/-- `if.end.i`: compare byte 0. -/
def stage2NoEventLitChainIfEndIInstrs : List Instr :=
[
      Instr.load "%72" (Ty.int 8) (Operand.reg "%arrayidx6.le1046"),
      Instr.trunc "%73" 64 8 (Operand.reg "%lit.0"),
      Instr.icmp "%cmp7.not.i" IPred.eq 8 (Operand.reg "%72") (Operand.reg "%73")
      ]

theorem stage2NoEventLitChain_findBlock_if_end_i :
    stage2NoEventBody.findBlock "if.end.i" =
      some ⟨"if.end.i", stage2NoEventLitChainIfEndIInstrs, Term.condbr (Operand.reg "%cmp7.not.i") "for.body.i.1" "if.then527"⟩ := by decide

/-- The loop bound after byte 0: the token ends at one byte. -/
def stage2NoEventLitChainForBodyI1Instrs : List Instr :=
[
      Instr.icmp "%exitcond.not.i.1" IPred.eq 64 (Operand.reg "%sub524") (Operand.imm (.int 64 (BitVec.ofNat 64 1)))
      ]

theorem stage2NoEventLitChain_findBlock_for_body_i_1 :
    stage2NoEventBody.findBlock "for.body.i.1" =
      some ⟨"for.body.i.1", stage2NoEventLitChainForBodyI1Instrs, Term.condbr (Operand.reg "%exitcond.not.i.1") "if.then527" "if.end.i.1"⟩ := by decide

/-- Compare byte 1. -/
def stage2NoEventLitChainIfEndI1Instrs : List Instr :=
[
      Instr.gep "%arrayidx.i.1" (Ty.int 8) (Operand.reg "%arrayidx6.le1046") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.load "%64" (Ty.int 8) (Operand.reg "%arrayidx.i.1"),
      Instr.binop "%shr.i.1" BinOp.lshr 64 (Operand.reg "%lit.0") (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
      Instr.trunc "%65" 64 8 (Operand.reg "%shr.i.1"),
      Instr.icmp "%cmp7.not.i.1" IPred.eq 8 (Operand.reg "%64") (Operand.reg "%65")
      ]

theorem stage2NoEventLitChain_findBlock_if_end_i_1 :
    stage2NoEventBody.findBlock "if.end.i.1" =
      some ⟨"if.end.i.1", stage2NoEventLitChainIfEndI1Instrs, Term.condbr (Operand.reg "%cmp7.not.i.1") "for.body.i.2" "if.then527"⟩ := by decide

/-- The loop bound after byte 1. -/
def stage2NoEventLitChainForBodyI2Instrs : List Instr :=
[
      Instr.icmp "%exitcond.not.i.2" IPred.eq 64 (Operand.reg "%sub524") (Operand.imm (.int 64 (BitVec.ofNat 64 2)))
      ]

theorem stage2NoEventLitChain_findBlock_for_body_i_2 :
    stage2NoEventBody.findBlock "for.body.i.2" =
      some ⟨"for.body.i.2", stage2NoEventLitChainForBodyI2Instrs, Term.condbr (Operand.reg "%exitcond.not.i.2") "if.then527" "if.end.i.2"⟩ := by decide

/-- Compare byte 2. -/
def stage2NoEventLitChainIfEndI2Instrs : List Instr :=
[
      Instr.gep "%arrayidx.i.2" (Ty.int 8) (Operand.reg "%arrayidx6.le1046") (Operand.imm (.int 64 (BitVec.ofNat 64 2))),
      Instr.load "%66" (Ty.int 8) (Operand.reg "%arrayidx.i.2"),
      Instr.binop "%shr.i.2" BinOp.lshr 64 (Operand.reg "%lit.0") (Operand.imm (.int 64 (BitVec.ofNat 64 16))),
      Instr.trunc "%67" 64 8 (Operand.reg "%shr.i.2"),
      Instr.icmp "%cmp7.not.i.2" IPred.eq 8 (Operand.reg "%66") (Operand.reg "%67")
      ]

theorem stage2NoEventLitChain_findBlock_if_end_i_2 :
    stage2NoEventBody.findBlock "if.end.i.2" =
      some ⟨"if.end.i.2", stage2NoEventLitChainIfEndI2Instrs, Term.condbr (Operand.reg "%cmp7.not.i.2") "for.body.i.3" "if.then527"⟩ := by decide

/-- The loop bound after byte 2. -/
def stage2NoEventLitChainForBodyI3Instrs : List Instr :=
[
      Instr.icmp "%exitcond.not.i.3" IPred.eq 64 (Operand.reg "%sub524") (Operand.imm (.int 64 (BitVec.ofNat 64 3)))
      ]

theorem stage2NoEventLitChain_findBlock_for_body_i_3 :
    stage2NoEventBody.findBlock "for.body.i.3" =
      some ⟨"for.body.i.3", stage2NoEventLitChainForBodyI3Instrs, Term.condbr (Operand.reg "%exitcond.not.i.3") "if.then527" "if.end.i.3"⟩ := by decide

/-- Compare byte 3, then the width selector's own branch. -/
def stage2NoEventLitChainIfEndI3Instrs : List Instr :=
[
      Instr.gep "%arrayidx.i.3" (Ty.int 8) (Operand.reg "%arrayidx6.le1046") (Operand.imm (.int 64 (BitVec.ofNat 64 3))),
      Instr.load "%68" (Ty.int 8) (Operand.reg "%arrayidx.i.3"),
      Instr.binop "%shr.i.3" BinOp.lshr 64 (Operand.reg "%lit.0") (Operand.imm (.int 64 (BitVec.ofNat 64 24))),
      Instr.trunc "%69" 64 8 (Operand.reg "%shr.i.3"),
      Instr.icmp "%cmp7.not.i.3" IPred.eq 8 (Operand.reg "%68") (Operand.reg "%69")
      ]

theorem stage2NoEventLitChain_findBlock_if_end_i_3 :
    stage2NoEventBody.findBlock "if.end.i.3" =
      some ⟨"if.end.i.3", stage2NoEventLitChainIfEndI3Instrs, Term.condbr (Operand.reg "%cmp7.not.i.3") "for.cond.i.3" "if.then527"⟩ := by decide

/-- The width selector: four-byte literals skip the fifth compare. -/
def stage2NoEventLitChainForCondI3Instrs : List Instr :=
[
      ]

theorem stage2NoEventLitChain_findBlock_for_cond_i_3 :
    stage2NoEventBody.findBlock "for.cond.i.3" =
      some ⟨"for.cond.i.3", stage2NoEventLitChainForCondI3Instrs, Term.condbr (Operand.reg "%exitcond38.not.i.3") "for.end.i" "for.body.i.4"⟩ := by decide

/-- The loop bound after byte 3. -/
def stage2NoEventLitChainForBodyI4Instrs : List Instr :=
[
      Instr.icmp "%exitcond.not.i.4" IPred.eq 64 (Operand.reg "%sub524") (Operand.imm (.int 64 (BitVec.ofNat 64 4)))
      ]

theorem stage2NoEventLitChain_findBlock_for_body_i_4 :
    stage2NoEventBody.findBlock "for.body.i.4" =
      some ⟨"for.body.i.4", stage2NoEventLitChainForBodyI4Instrs, Term.condbr (Operand.reg "%exitcond.not.i.4") "if.then527" "if.end.i.4"⟩ := by decide

/-- Compare byte 4 (`false` only). -/
def stage2NoEventLitChainIfEndI4Instrs : List Instr :=
[
      Instr.gep "%arrayidx.i.4" (Ty.int 8) (Operand.reg "%arrayidx6.le1046") (Operand.imm (.int 64 (BitVec.ofNat 64 4))),
      Instr.load "%70" (Ty.int 8) (Operand.reg "%arrayidx.i.4"),
      Instr.binop "%shr.i.4" BinOp.lshr 64 (Operand.reg "%lit.0") (Operand.imm (.int 64 (BitVec.ofNat 64 32))),
      Instr.trunc "%71" 64 8 (Operand.reg "%shr.i.4"),
      Instr.icmp "%cmp7.not.i.4" IPred.eq 8 (Operand.reg "%70") (Operand.reg "%71")
      ]

theorem stage2NoEventLitChain_findBlock_if_end_i_4 :
    stage2NoEventBody.findBlock "if.end.i.4" =
      some ⟨"if.end.i.4", stage2NoEventLitChainIfEndI4Instrs, Term.condbr (Operand.reg "%cmp7.not.i.4") "for.end.i" "if.then527"⟩ := by decide

/-- The length check. -/
def stage2NoEventLitChainForEndIInstrs : List Instr :=
[
      Instr.icmp "%cmp13.not.i" IPred.eq 64 (Operand.reg "%sub524") (Operand.reg "%ln.0")
      ]

theorem stage2NoEventLitChain_findBlock_for_end_i :
    stage2NoEventBody.findBlock "for.end.i" =
      some ⟨"for.end.i", stage2NoEventLitChainForEndIInstrs, Term.condbr (Operand.reg "%cmp13.not.i") "if.end545" "if.then527"⟩ := by decide

/-- The refusal exit: the offset's own block.  Its instructions are pinned here
for the block lookup; the region's theorem stops at its entry, so this module
does not step them. -/
def stage2NoEventLitChainIfThen527Instrs : List Instr :=
[
      Instr.phi "%ei520.0.ph" (Ty.int 64) [("if.end519", (Operand.reg "%sub524")), ("if.end.i", (Operand.imm (.int 64 (BitVec.ofNat 64 0)))), ("for.body.i.1", (Operand.reg "%sub524")), ("if.end.i.1", (Operand.imm (.int 64 (BitVec.ofNat 64 1)))), ("for.body.i.2", (Operand.reg "%sub524")), ("if.end.i.2", (Operand.imm (.int 64 (BitVec.ofNat 64 2)))), ("for.body.i.3", (Operand.reg "%sub524")), ("if.end.i.3", (Operand.imm (.int 64 (BitVec.ofNat 64 3)))), ("for.body.i.4", (Operand.reg "%sub524")), ("if.end.i.4", (Operand.imm (.int 64 (BitVec.ofNat 64 4)))), ("for.end.i", (Operand.reg "%ln.0"))],
      Instr.binop "%add529" BinOp.add 64 (Operand.reg "%ei520.0.ph") (Operand.reg "%idxprom.lcssa"),
      Instr.store (Ty.int 64) (Operand.reg "%add529") (Operand.reg "%off"),
      Instr.callVoid "od_gap_recover" [(Ty.ptr, (Operand.reg "%c")), ((Ty.int 64), (Operand.reg "%idxprom.lcssa"))],
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%tokens_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%values_out"),
      Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%sum_out"),
      Instr.load "%74" (Ty.int 64) (Operand.reg "%off"),
      Instr.store (Ty.int 64) (Operand.reg "%74") (Operand.reg "%err")
      ]

theorem stage2NoEventLitChain_findBlock_if_then527 :
    stage2NoEventBody.findBlock "if.then527" =
      some ⟨"if.then527", stage2NoEventLitChainIfThen527Instrs, Term.br "cleanup580"⟩ := by decide

/-- The accepting exit: the reading's own block.  Pinned for the lookup; the
region ends at its entry. -/
def stage2NoEventLitChainIfEnd545Instrs : List Instr :=
[
      Instr.phi "%add489.pn" (Ty.int 64) [("cleanup491", (Operand.reg "%add489")), ("for.end.i", (Operand.reg "%tag.0"))],
      Instr.binop "%tokens.12" BinOp.add 64 (Operand.reg "%tokens.0.lcssa1073") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.binop "%terms.12" BinOp.add 64 (Operand.reg "%add489.pn") (Operand.reg "%terms.0.lcssa1079"),
      Instr.icmp "%cmp546" IPred.ult 64 (Operand.reg "%ee.1") (Operand.reg "%cond")
      ]

theorem stage2NoEventLitChain_findBlock_if_end545 :
    stage2NoEventBody.findBlock "if.end545" =
      some ⟨"if.end545", stage2NoEventLitChainIfEnd545Instrs, Term.condbr (Operand.reg "%cmp546") "land.rhs552" "after_value"⟩ := by decide

/-! ### The pins bite

The chain's entry is the shared `phi`: the three literals live in one `%lit.0`
whose incoming entries name the three call-site predecessors, and the width
selector `%exitcond38.not.i.3` is `0` exactly for `false` (five bytes).  These
guards read the pinned bodies, so a re-capture that splits the chain into three
inlined sites — or reorders the `phi` entries — fails here rather than leaving
the general theorem describing a shape the body no longer has. -/

/-- A block's `phi` incoming list for a destination, read from the pins. -/
def litPhiIncoming (b : Block) (d : String) : Option (List (String × Operand)) :=
  b.instrs.findSome? fun i =>
    match i with
    | .phi d' _ inc => if d' = d then some inc else none
    | _ => none

#guard decide
  (litPhiIncoming ((stage2NoEventBody.findBlock "if.end519").getD ⟨"", [], .unreachable⟩) "%lit.0" =
    some [("if.then504", Operand.imm (.int 64 (BitVec.ofNat 64 435728179558))),
     ("if.then509", Operand.imm (.int 64 (BitVec.ofNat 64 1819047278))),
     ("LeafBlock68", Operand.imm (.int 64 (BitVec.ofNat 64 1702195828)))])

#guard decide
  (litPhiIncoming ((stage2NoEventBody.findBlock "if.end519").getD ⟨"", [], .unreachable⟩) "%exitcond38.not.i.3" =
    some [("if.then504", Operand.imm (.int 1 (BitVec.ofNat 1 0))),
     ("if.then509", Operand.imm (.int 1 (BitVec.ofNat 1 1))),
     ("LeafBlock68", Operand.imm (.int 1 (BitVec.ofNat 1 1)))])

-- Two of the shape pins above restated as guards: the entry lookup resolves, and
-- `if.end.i.4`'s equation is the pinned one.  The fixture-side mutation control
-- is the imported `JsonStage2NoEventIR.lean:1467` guard
-- (`firstFunction stage2NoEventSrcMutated ≠ some stage2NoEventBody`); this
-- module cites it rather than restating it.  These two lines pin shape at
-- `stage2NoEventBody`, they are not a mutation control.
#guard decide (stage2NoEventBody.findBlock "if.end519" ≠ none)
#guard decide (stage2NoEventBody.findBlock "if.end.i.4" =
  some ⟨"if.end.i.4", stage2NoEventLitChainIfEndI4Instrs,
    Term.condbr (Operand.reg "%cmp7.not.i.4") "for.end.i" "if.then527"⟩)

/-! ### Instruction steps the chain uses

The chain's byte loads, byte compares and `getelementptr i8` with an immediate
offset are not in `BlockEval`'s vocabulary (which is written at 64-bit loads and
64-bit compares), so they are here.  Each is the `evalInstr` equation at the
instruction's own shape, and the `denoteCode` form is the composition step. -/

/-- A byte as the bit-vector the load binds. -/
theorem stage2NoEventLitChain_uint8_toBitVec (u : UInt8) :
    BitVec.ofNat 8 u.toNat = u.toBitVec := by
  have h : UInt8.ofNat u.toNat = u := UInt8.ofNat_toNat
  conv => rhs; rw [← h]
  exact (UInt8.toBitVec_ofNat u.toNat).symm

/-- The byte `i` of a packed literal, as the body computes it: `trunc (lshr lit
(8i))`. -/
theorem stage2NoEventLitChain_byte_eq (lit : BitVec 64) (i : Nat) :
    BitVec.ofNat 8 ((lit >>> (8 * i)).toNat % 2 ^ 8) =
      BitVec.ofNat 8 ((lit.toNat >>> (8 * i)) % 256) := by
  rw [BitVec.toNat_ushiftRight]
  congr 1

/-- The same byte as `packBytes`'s `UInt8`, read at its `toBitVec`. -/
theorem stage2NoEventLitChain_byte_eq_uint8 (lit : BitVec 64) (i : Nat) :
    BitVec.ofNat 8 ((lit >>> (8 * i)).toNat % 2 ^ 8) =
      (UInt8.ofNat ((lit.toNat >>> (8 * i)) % 256)).toBitVec := by
  rw [stage2NoEventLitChain_byte_eq]
  exact (UInt8.toBitVec_ofNat ((lit.toNat >>> (8 * i)) % 256)).symm

/-- A byte `icmp eq` at either outcome, at its own width: `BlockEval`'s compare
steps are stated at 64 bits. -/
theorem stage2NoEventLitChain_step_icmp_eq_w (calls : Calls) (env : Env) (s : State)
    (d : String) (w : Nat) (a b : Operand) {x y : BitVec w}
    (ha : evalOperand (stateAt env s) a = some (.int w x))
    (hb : evalOperand (stateAt env s) b = some (.int w y)) :
    evalInstr calls (stateAt env s) (.icmp d .eq w a b) =
      some (stateAt ((d, .int 1 (evalICmp .eq x y)) :: env) s) := by
  rw [JsonS1MasksIR.evalInstr_icmp ha hb]
  simp [stateAt, State.bind]

/-- An `i8` load from a readable byte. -/
theorem stage2NoEventLitChain_step_load8 (calls : Calls) (env : Env) (s : State)
    (d p : String) {a : Nat} {u : UInt8}
    (hp : lookupName env p = some (.ptr a))
    (hu : readByte s.mem a = some u) :
    evalInstr calls (stateAt env s) (.load d (.int 8) (.reg p)) =
      some (stateAt ((d, .int 8 u.toBitVec) :: env) s) := by
  have hrs : readBytes s.mem a 1 = some [u] := by
    rw [JsonEntrySteps.readBytes_one, hu]; rfl
  have h2 := DepthCountRefine.evalInstr_load8 calls (stateAt env s) d p a [u] hp hrs
  rw [h2]
  simp only [stateAt, State.bind]
  rw [show bytesToNat [u] = u.toNat from rfl, stage2NoEventLitChain_uint8_toBitVec]

/-- `getelementptr i8, ptr %base, i64 <k>`: the immediate offset's byte address. -/
theorem stage2NoEventLitChain_step_gep8_imm (calls : Calls) (env : Env) (s : State)
    (d base : String) {a k : Nat}
    (hb : lookupName env base = some (.ptr a))
    (hk : ((BitVec.ofNat 64 k).signExtend 64).toNat = k)
    (hpos : ((BitVec.ofNat 64 k).signExtend 64).toNat < 2 ^ 63) :
    evalInstr calls (stateAt env s)
        (.gep d (.int 8) (.reg base) (.imm (.int 64 (BitVec.ofNat 64 k)))) =
      some (stateAt ((d, .ptr (a + k)) :: env) s) := by
  rw [evalInstr_gep_i8 (hb := BlockEval.evalOperand_reg_of env s base (.ptr a) hb)
    (ho := BlockEval.evalOperand_lit_of _ 64 (BitVec.ofNat 64 k)) (hpos := hpos)]
  simp only [stateAt, State.bind, hk]

/-- Resolve a register read against a concrete cell list. -/
macro "lit_lk" : tactic => `(tactic|
  (simp only [stateAt, evalOperand]
   repeat rw [lookupName_cons_ne _ _ (by decide)]
   first
    | rw [lookupName_cons_self]
    | assumption))

/-- Byte `i` of the packed literal, as the chain's `trunc (lshr lit (8i))`
computes it. -/
abbrev litByte (lit : BitVec 64) (i : Nat) : BitVec 8 :=
  BitVec.ofNat 8 ((lit >>> (8 * i)).toNat % 2 ^ 8)

/-- Close a block's `denoteCode` at the environment the chain states. -/
macro "lit_close" : tactic => `(tactic|
  simp [denoteCode, denoteRun, State.bindAll, stateAt, litByte])

/-! ### The blocks' runs, computed

Each `denoteCode` below is the block's instruction list from the environment the
previous block leaves.  The environment cell a step writes sits in front of the
ones before it, so the final environment is written newest first.  These are the
`hcode` premises of the step lemmas in the next section. -/

theorem stage2NoEventLitChain_denote_if_end519 (calls : Calls) (env : Env) (s : State)
    (p : String) {lit ln tag : BitVec 64} {b : BitVec 1} {ee idx : BitVec 64}
    (hpre : s.pre = some p)
    (hincLit : phiIncoming p [("if.then504", (Operand.imm (.int 64 (BitVec.ofNat 64 435728179558)))), ("if.then509", (Operand.imm (.int 64 (BitVec.ofNat 64 1819047278)))), ("LeafBlock68", (Operand.imm (.int 64 (BitVec.ofNat 64 1702195828))))] = some (.imm (.int 64 lit)))
    (hincB : phiIncoming p [("if.then504", (Operand.imm (.int 1 (BitVec.ofNat 1 0)))), ("if.then509", (Operand.imm (.int 1 (BitVec.ofNat 1 1)))), ("LeafBlock68", (Operand.imm (.int 1 (BitVec.ofNat 1 1))))] = some (.imm (.int 1 b)))
    (hincLn : phiIncoming p [("if.then504", (Operand.imm (.int 64 (BitVec.ofNat 64 5)))), ("if.then509", (Operand.imm (.int 64 (BitVec.ofNat 64 4)))), ("LeafBlock68", (Operand.imm (.int 64 (BitVec.ofNat 64 4))))] = some (.imm (.int 64 ln)))
    (hincTag : phiIncoming p [("if.then504", (Operand.imm (.int 64 (BitVec.ofNat 64 9)))), ("if.then509", (Operand.imm (.int 64 (BitVec.ofNat 64 10)))), ("LeafBlock68", (Operand.imm (.int 64 (BitVec.ofNat 64 8))))] = some (.imm (.int 64 tag)))
    (hee : lookupName env "%ee.1" = some (.int 64 ee))
    (hidx : lookupName env "%idxprom.lcssa" = some (.int 64 idx)) :
    denoteCode calls stage2NoEventLitChainIfEnd519Instrs (stateAt env s) =
      some (stateAt
        (("%exitcond.not.i", .int 1 (evalICmp .eq (ee - idx) (BitVec.ofNat 64 0))) ::
         ("%sub524", .int 64 (ee - idx)) ::
         ("%tag.0", .int 64 tag) :: ("%ln.0", .int 64 ln) ::
         ("%exitcond38.not.i.3", .int 1 b) :: ("%lit.0", .int 64 lit) :: env) s) := by
  unfold stage2NoEventLitChainIfEnd519Instrs
  block_phi_run
  · change denoteCode calls
      [Instr.binop "%sub524" BinOp.sub 64 (Operand.reg "%ee.1") (Operand.reg "%idxprom.lcssa"),
       Instr.icmp "%exitcond.not.i" IPred.eq 64 (Operand.reg "%sub524") (Operand.imm (.int 64 (BitVec.ofNat 64 0)))]
      (stateAt (("%tag.0", .int 64 tag) :: ("%ln.0", .int 64 ln) ::
        ("%exitcond38.not.i.3", .int 1 b) :: ("%lit.0", .int 64 lit) :: env) s) =
      some (stateAt
        (("%exitcond.not.i", .int 1 (evalICmp .eq (ee - idx) (BitVec.ofNat 64 0))) ::
         ("%sub524", .int 64 (ee - idx)) ::
         ("%tag.0", .int 64 tag) :: ("%ln.0", .int 64 ln) ::
         ("%exitcond38.not.i.3", .int 1 b) :: ("%lit.0", .int 64 lit) :: env) s)
    have hee' : lookupName (("%tag.0", .int 64 tag) :: ("%ln.0", .int 64 ln) ::
        ("%exitcond38.not.i.3", .int 1 b) :: ("%lit.0", .int 64 lit) :: env)
        "%ee.1" = some (.int 64 ee) := by
      simpa [lookupName] using hee
    have hidx' : lookupName (("%tag.0", .int 64 tag) :: ("%ln.0", .int 64 ln) ::
        ("%exitcond38.not.i.3", .int 1 b) :: ("%lit.0", .int 64 lit) :: env)
        "%idxprom.lcssa" = some (.int 64 idx) := by
      simpa [lookupName] using hidx
    rw [denoteCode_cons_of _ _ _ _ _
      (BlockEval.step_sub_reg calls _ s "%sub524" "%ee.1" "%idxprom.lcssa" hee' hidx')]
    rw [denoteCode_cons_of _ _ _ _ _
      (BlockEval.step_icmp_eq_imm calls _ s "%exitcond.not.i" "%sub524"
        (by rw [lookupName_cons_self]))]
    simp only [denoteCode, denoteRun, State.bindAll]
  · exact hpre
  · rfl
  · exact hincLit
  · exact BlockEval.evalOperand_lit_of _ 64 lit
  · exact hincB
  · exact BlockEval.evalOperand_lit_of _ 1 b
  · exact hincLn
  · exact BlockEval.evalOperand_lit_of _ 64 ln
  · exact hincTag
  · exact BlockEval.evalOperand_lit_of _ 64 tag

theorem stage2NoEventLitChain_denote_if_end_i (calls : Calls) (env : Env) (s : State)
    {base : Nat} {lit : BitVec 64} {u : UInt8}
    (harr : lookupName env "%arrayidx6.le1046" = some (.ptr base))
    (hlit : lookupName env "%lit.0" = some (.int 64 lit))
    (hu : readByte s.mem base = some u) :
    denoteCode calls stage2NoEventLitChainIfEndIInstrs (stateAt env s) =
      some (stateAt
        (("%cmp7.not.i", .int 1 (evalICmp .eq u.toBitVec (litByte lit 0))) ::
         ("%73", .int 8 (litByte lit 0)) ::
         ("%72", .int 8 u.toBitVec) :: env) s) := by
  unfold stage2NoEventLitChainIfEndIInstrs
  rw [denoteCode_cons_of _ _ _ _ _
    (stage2NoEventLitChain_step_load8 calls env s "%72" "%arrayidx6.le1046" harr hu)]
  rw [denoteCode_cons_of _ _ _ _ _
    (BlockEval.step_trunc calls (("%72", .int 8 u.toBitVec) :: env) s "%73" "%lit.0" 64 8 hlit)]
  rw [denoteCode_cons_of _ _ _ _ _
    (stage2NoEventLitChain_step_icmp_eq_w calls
      (("%73", .int 8 (BitVec.ofNat 8 (lit.toNat % 2 ^ 8))) ::
       ("%72", .int 8 u.toBitVec) :: env) s "%cmp7.not.i" 8 (.reg "%72") (.reg "%73")
      (by simp only [stateAt, evalOperand]
          rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self])
      (by simp only [stateAt, evalOperand]; rw [lookupName_cons_self]))]
  lit_close

theorem stage2NoEventLitChain_denote_for_body_i_1 (calls : Calls) (env : Env) (s : State)
    {sub : BitVec 64}
    (hsub : lookupName env "%sub524" = some (.int 64 sub)) :
    denoteCode calls stage2NoEventLitChainForBodyI1Instrs (stateAt env s) =
      some (stateAt
        (("%exitcond.not.i.1", .int 1 (evalICmp .eq sub (BitVec.ofNat 64 1))) :: env) s) := by
  unfold stage2NoEventLitChainForBodyI1Instrs
  rw [denoteCode_cons_of _ _ _ _ _
    (BlockEval.step_icmp_eq_imm calls env s "%exitcond.not.i.1" "%sub524" hsub)]
  lit_close

theorem stage2NoEventLitChain_denote_if_end_i_1 (calls : Calls) (env : Env) (s : State)
    {base : Nat} {lit : BitVec 64} {u : UInt8}
    (harr : lookupName env "%arrayidx6.le1046" = some (.ptr base))
    (hlit : lookupName env "%lit.0" = some (.int 64 lit))
    (hu : readByte s.mem (base + 1) = some u) :
    denoteCode calls stage2NoEventLitChainIfEndI1Instrs (stateAt env s) =
      some (stateAt
        (("%cmp7.not.i.1", .int 1 (evalICmp .eq u.toBitVec (litByte lit 1))) ::
         ("%65", .int 8 (litByte lit 1)) ::
         ("%shr.i.1", .int 64 (lit >>> 8)) ::
         ("%64", .int 8 u.toBitVec) ::
         ("%arrayidx.i.1", .ptr (base + 1)) :: env) s) := by
  unfold stage2NoEventLitChainIfEndI1Instrs
  rw [denoteCode_cons_of _ _ _ _ _
    (stage2NoEventLitChain_step_gep8_imm calls env s "%arrayidx.i.1" "%arrayidx6.le1046"
      harr (by decide) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _
    (stage2NoEventLitChain_step_load8 calls (("%arrayidx.i.1", .ptr (base + 1)) :: env) s
      "%64" "%arrayidx.i.1" (by rw [lookupName_cons_self]) hu)]
  rw [denoteCode_cons_of _ _ _ _ _
    (BlockEval.step_lshr_imm calls (("%64", .int 8 u.toBitVec) ::
      ("%arrayidx.i.1", .ptr (base + 1)) :: env) s "%shr.i.1" "%lit.0" hlit)]
  rw [denoteCode_cons_of _ _ _ _ _
    (BlockEval.step_trunc calls (("%shr.i.1", .int 64 (lit >>> (BitVec.ofNat 64 8).toNat)) ::
      ("%64", .int 8 u.toBitVec) :: ("%arrayidx.i.1", .ptr (base + 1)) :: env) s
      "%65" "%shr.i.1" 64 8 (by rw [lookupName_cons_self]))]
  rw [denoteCode_cons_of _ _ _ _ _
    (stage2NoEventLitChain_step_icmp_eq_w calls
      (("%65", .int 8 (BitVec.ofNat 8 ((lit >>> (BitVec.ofNat 64 8).toNat).toNat % 2 ^ 8))) ::
       ("%shr.i.1", .int 64 (lit >>> (BitVec.ofNat 64 8).toNat)) ::
       ("%64", .int 8 u.toBitVec) :: ("%arrayidx.i.1", .ptr (base + 1)) :: env) s
      "%cmp7.not.i.1" 8 (.reg "%64") (.reg "%65")
      (by simp only [stateAt, evalOperand]
          rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide), lookupName_cons_self])
      (by simp only [stateAt, evalOperand]; rw [lookupName_cons_self]))]
  lit_close

theorem stage2NoEventLitChain_denote_for_body_i_2 (calls : Calls) (env : Env) (s : State)
    {sub : BitVec 64}
    (hsub : lookupName env "%sub524" = some (.int 64 sub)) :
    denoteCode calls stage2NoEventLitChainForBodyI2Instrs (stateAt env s) =
      some (stateAt
        (("%exitcond.not.i.2", .int 1 (evalICmp .eq sub (BitVec.ofNat 64 2))) :: env) s) := by
  unfold stage2NoEventLitChainForBodyI2Instrs
  rw [denoteCode_cons_of _ _ _ _ _
    (BlockEval.step_icmp_eq_imm calls env s "%exitcond.not.i.2" "%sub524" hsub)]
  lit_close

theorem stage2NoEventLitChain_denote_if_end_i_2 (calls : Calls) (env : Env) (s : State)
    {base : Nat} {lit : BitVec 64} {u : UInt8}
    (harr : lookupName env "%arrayidx6.le1046" = some (.ptr base))
    (hlit : lookupName env "%lit.0" = some (.int 64 lit))
    (hu : readByte s.mem (base + 2) = some u) :
    denoteCode calls stage2NoEventLitChainIfEndI2Instrs (stateAt env s) =
      some (stateAt
        (("%cmp7.not.i.2", .int 1 (evalICmp .eq u.toBitVec (litByte lit 2))) ::
         ("%67", .int 8 (litByte lit 2)) ::
         ("%shr.i.2", .int 64 (lit >>> 16)) ::
         ("%66", .int 8 u.toBitVec) ::
         ("%arrayidx.i.2", .ptr (base + 2)) :: env) s) := by
  unfold stage2NoEventLitChainIfEndI2Instrs
  rw [denoteCode_cons_of _ _ _ _ _
    (stage2NoEventLitChain_step_gep8_imm calls env s "%arrayidx.i.2" "%arrayidx6.le1046"
      harr (by decide) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _
    (stage2NoEventLitChain_step_load8 calls (("%arrayidx.i.2", .ptr (base + 2)) :: env) s
      "%66" "%arrayidx.i.2" (by rw [lookupName_cons_self]) hu)]
  rw [denoteCode_cons_of _ _ _ _ _
    (BlockEval.step_lshr_imm calls (("%66", .int 8 u.toBitVec) ::
      ("%arrayidx.i.2", .ptr (base + 2)) :: env) s "%shr.i.2" "%lit.0" hlit)]
  rw [denoteCode_cons_of _ _ _ _ _
    (BlockEval.step_trunc calls (("%shr.i.2", .int 64 (lit >>> (BitVec.ofNat 64 16).toNat)) ::
      ("%66", .int 8 u.toBitVec) :: ("%arrayidx.i.2", .ptr (base + 2)) :: env) s
      "%67" "%shr.i.2" 64 8 (by rw [lookupName_cons_self]))]
  rw [denoteCode_cons_of _ _ _ _ _
    (stage2NoEventLitChain_step_icmp_eq_w calls
      (("%67", .int 8 (BitVec.ofNat 8 ((lit >>> (BitVec.ofNat 64 16).toNat).toNat % 2 ^ 8))) ::
       ("%shr.i.2", .int 64 (lit >>> (BitVec.ofNat 64 16).toNat)) ::
       ("%66", .int 8 u.toBitVec) :: ("%arrayidx.i.2", .ptr (base + 2)) :: env) s
      "%cmp7.not.i.2" 8 (.reg "%66") (.reg "%67")
      (by simp only [stateAt, evalOperand]
          rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide), lookupName_cons_self])
      (by simp only [stateAt, evalOperand]; rw [lookupName_cons_self]))]
  lit_close

theorem stage2NoEventLitChain_denote_for_body_i_3 (calls : Calls) (env : Env) (s : State)
    {sub : BitVec 64}
    (hsub : lookupName env "%sub524" = some (.int 64 sub)) :
    denoteCode calls stage2NoEventLitChainForBodyI3Instrs (stateAt env s) =
      some (stateAt
        (("%exitcond.not.i.3", .int 1 (evalICmp .eq sub (BitVec.ofNat 64 3))) :: env) s) := by
  unfold stage2NoEventLitChainForBodyI3Instrs
  rw [denoteCode_cons_of _ _ _ _ _
    (BlockEval.step_icmp_eq_imm calls env s "%exitcond.not.i.3" "%sub524" hsub)]
  lit_close

theorem stage2NoEventLitChain_denote_if_end_i_3 (calls : Calls) (env : Env) (s : State)
    {base : Nat} {lit : BitVec 64} {u : UInt8}
    (harr : lookupName env "%arrayidx6.le1046" = some (.ptr base))
    (hlit : lookupName env "%lit.0" = some (.int 64 lit))
    (hu : readByte s.mem (base + 3) = some u) :
    denoteCode calls stage2NoEventLitChainIfEndI3Instrs (stateAt env s) =
      some (stateAt
        (("%cmp7.not.i.3", .int 1 (evalICmp .eq u.toBitVec (litByte lit 3))) ::
         ("%69", .int 8 (litByte lit 3)) ::
         ("%shr.i.3", .int 64 (lit >>> 24)) ::
         ("%68", .int 8 u.toBitVec) ::
         ("%arrayidx.i.3", .ptr (base + 3)) :: env) s) := by
  unfold stage2NoEventLitChainIfEndI3Instrs
  rw [denoteCode_cons_of _ _ _ _ _
    (stage2NoEventLitChain_step_gep8_imm calls env s "%arrayidx.i.3" "%arrayidx6.le1046"
      harr (by decide) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _
    (stage2NoEventLitChain_step_load8 calls (("%arrayidx.i.3", .ptr (base + 3)) :: env) s
      "%68" "%arrayidx.i.3" (by rw [lookupName_cons_self]) hu)]
  rw [denoteCode_cons_of _ _ _ _ _
    (BlockEval.step_lshr_imm calls (("%68", .int 8 u.toBitVec) ::
      ("%arrayidx.i.3", .ptr (base + 3)) :: env) s "%shr.i.3" "%lit.0" hlit)]
  rw [denoteCode_cons_of _ _ _ _ _
    (BlockEval.step_trunc calls (("%shr.i.3", .int 64 (lit >>> (BitVec.ofNat 64 24).toNat)) ::
      ("%68", .int 8 u.toBitVec) :: ("%arrayidx.i.3", .ptr (base + 3)) :: env) s
      "%69" "%shr.i.3" 64 8 (by rw [lookupName_cons_self]))]
  rw [denoteCode_cons_of _ _ _ _ _
    (stage2NoEventLitChain_step_icmp_eq_w calls
      (("%69", .int 8 (BitVec.ofNat 8 ((lit >>> (BitVec.ofNat 64 24).toNat).toNat % 2 ^ 8))) ::
       ("%shr.i.3", .int 64 (lit >>> (BitVec.ofNat 64 24).toNat)) ::
       ("%68", .int 8 u.toBitVec) :: ("%arrayidx.i.3", .ptr (base + 3)) :: env) s
      "%cmp7.not.i.3" 8 (.reg "%68") (.reg "%69")
      (by simp only [stateAt, evalOperand]
          rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide), lookupName_cons_self])
      (by simp only [stateAt, evalOperand]; rw [lookupName_cons_self]))]
  lit_close

theorem stage2NoEventLitChain_denote_for_cond_i_3 (calls : Calls) (env : Env) (s : State) :
    denoteCode calls stage2NoEventLitChainForCondI3Instrs (stateAt env s) =
      some (stateAt env s) := by
  unfold stage2NoEventLitChainForCondI3Instrs
  rfl

theorem stage2NoEventLitChain_denote_for_body_i_4 (calls : Calls) (env : Env) (s : State)
    {sub : BitVec 64}
    (hsub : lookupName env "%sub524" = some (.int 64 sub)) :
    denoteCode calls stage2NoEventLitChainForBodyI4Instrs (stateAt env s) =
      some (stateAt
        (("%exitcond.not.i.4", .int 1 (evalICmp .eq sub (BitVec.ofNat 64 4))) :: env) s) := by
  unfold stage2NoEventLitChainForBodyI4Instrs
  rw [denoteCode_cons_of _ _ _ _ _
    (BlockEval.step_icmp_eq_imm calls env s "%exitcond.not.i.4" "%sub524" hsub)]
  lit_close

theorem stage2NoEventLitChain_denote_if_end_i_4 (calls : Calls) (env : Env) (s : State)
    {base : Nat} {lit : BitVec 64} {u : UInt8}
    (harr : lookupName env "%arrayidx6.le1046" = some (.ptr base))
    (hlit : lookupName env "%lit.0" = some (.int 64 lit))
    (hu : readByte s.mem (base + 4) = some u) :
    denoteCode calls stage2NoEventLitChainIfEndI4Instrs (stateAt env s) =
      some (stateAt
        (("%cmp7.not.i.4", .int 1 (evalICmp .eq u.toBitVec (litByte lit 4))) ::
         ("%71", .int 8 (litByte lit 4)) ::
         ("%shr.i.4", .int 64 (lit >>> 32)) ::
         ("%70", .int 8 u.toBitVec) ::
         ("%arrayidx.i.4", .ptr (base + 4)) :: env) s) := by
  unfold stage2NoEventLitChainIfEndI4Instrs
  rw [denoteCode_cons_of _ _ _ _ _
    (stage2NoEventLitChain_step_gep8_imm calls env s "%arrayidx.i.4" "%arrayidx6.le1046"
      harr (by decide) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _
    (stage2NoEventLitChain_step_load8 calls (("%arrayidx.i.4", .ptr (base + 4)) :: env) s
      "%70" "%arrayidx.i.4" (by rw [lookupName_cons_self]) hu)]
  rw [denoteCode_cons_of _ _ _ _ _
    (BlockEval.step_lshr_imm calls (("%70", .int 8 u.toBitVec) ::
      ("%arrayidx.i.4", .ptr (base + 4)) :: env) s "%shr.i.4" "%lit.0" hlit)]
  rw [denoteCode_cons_of _ _ _ _ _
    (BlockEval.step_trunc calls (("%shr.i.4", .int 64 (lit >>> (BitVec.ofNat 64 32).toNat)) ::
      ("%70", .int 8 u.toBitVec) :: ("%arrayidx.i.4", .ptr (base + 4)) :: env) s
      "%71" "%shr.i.4" 64 8 (by rw [lookupName_cons_self]))]
  rw [denoteCode_cons_of _ _ _ _ _
    (stage2NoEventLitChain_step_icmp_eq_w calls
      (("%71", .int 8 (BitVec.ofNat 8 ((lit >>> (BitVec.ofNat 64 32).toNat).toNat % 2 ^ 8))) ::
       ("%shr.i.4", .int 64 (lit >>> (BitVec.ofNat 64 32).toNat)) ::
       ("%70", .int 8 u.toBitVec) :: ("%arrayidx.i.4", .ptr (base + 4)) :: env) s
      "%cmp7.not.i.4" 8 (.reg "%70") (.reg "%71")
      (by simp only [stateAt, evalOperand]
          rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide), lookupName_cons_self])
      (by simp only [stateAt, evalOperand]; rw [lookupName_cons_self]))]
  lit_close

theorem stage2NoEventLitChain_denote_for_end_i (calls : Calls) (env : Env) (s : State)
    {sub ln : BitVec 64}
    (hsub : lookupName env "%sub524" = some (.int 64 sub))
    (hln : lookupName env "%ln.0" = some (.int 64 ln)) :
    denoteCode calls stage2NoEventLitChainForEndIInstrs (stateAt env s) =
      some (stateAt
        (("%cmp13.not.i", .int 1 (evalICmp .eq sub ln)) :: env) s) := by
  unfold stage2NoEventLitChainForEndIInstrs
  rw [denoteCode_cons_of _ _ _ _ _
    (BlockEval.step_icmp_eq_reg calls env s "%cmp13.not.i" "%sub524" "%ln.0" hsub hln)]
  lit_close

/-! ### The blocks' control steps

Each is `step_at_block` at the block's pinned instruction list and terminator,
with the `denoteCode` above as its body.  The program counter it leaves is the
branch's target and the predecessor field names the block it left. -/

/-- One control step from a block's run: `step` at a state whose program counter
finds `b`, whose instructions denote to `s'`, and whose terminator is `c`. -/
theorem stage2NoEventLitChain_step_at_block {calls : Calls} {f : Function}
    {s s' : State} {b : Block} {c : Ctrl} (hfind : f.findBlock s.pc = some b)
    (hcode : denoteCode calls b.instrs s = some s')
    (hterm : execTerm s' b.term = c) : step calls f s = c := by
  simp only [step, hfind, hcode, hterm]

/-- A `condbr` on a cell binding a one-bit value: the branch target it takes, in
one form for the zero and the one. -/
theorem stage2NoEventLitChain_execTerm_condbr (s : State) (c t f pcName : String)
    {b : BitVec 1} (hpc : s.pc = pcName)
    (hop : evalOperand s (.reg c) = some (.int 1 b)) :
    execTerm s (.condbr (.reg c) t f) =
      .jump { s with pc := if b = 1 then t else f, pre := some pcName } := by
  rcases bitVec1_eq_zero_or_one b with hb | hb
  · rw [DepthCountRefine.execTerm_condbr_false (c := .reg c) (t := t) (f := f) hop hb]
    simp [hb, hpc]
  · rw [DepthCountRefine.execTerm_condbr_true (c := .reg c) (t := t) (f := f) hop hb]
    simp [hb, hpc]

theorem stage2NoEventLitChain_step_if_end519 (calls : Calls) (env : Env) (s : State)
    (p : String) {lit ln tag : BitVec 64} {b : BitVec 1} {ee idx : BitVec 64}
    (hpc : s.pc = "if.end519")
    (hpre : s.pre = some p)
    (hincLit : phiIncoming p [("if.then504", (Operand.imm (.int 64 (BitVec.ofNat 64 435728179558)))), ("if.then509", (Operand.imm (.int 64 (BitVec.ofNat 64 1819047278)))), ("LeafBlock68", (Operand.imm (.int 64 (BitVec.ofNat 64 1702195828))))] = some (.imm (.int 64 lit)))
    (hincB : phiIncoming p [("if.then504", (Operand.imm (.int 1 (BitVec.ofNat 1 0)))), ("if.then509", (Operand.imm (.int 1 (BitVec.ofNat 1 1)))), ("LeafBlock68", (Operand.imm (.int 1 (BitVec.ofNat 1 1))))] = some (.imm (.int 1 b)))
    (hincLn : phiIncoming p [("if.then504", (Operand.imm (.int 64 (BitVec.ofNat 64 5)))), ("if.then509", (Operand.imm (.int 64 (BitVec.ofNat 64 4)))), ("LeafBlock68", (Operand.imm (.int 64 (BitVec.ofNat 64 4))))] = some (.imm (.int 64 ln)))
    (hincTag : phiIncoming p [("if.then504", (Operand.imm (.int 64 (BitVec.ofNat 64 9)))), ("if.then509", (Operand.imm (.int 64 (BitVec.ofNat 64 10)))), ("LeafBlock68", (Operand.imm (.int 64 (BitVec.ofNat 64 8))))] = some (.imm (.int 64 tag)))
    (hee : lookupName env "%ee.1" = some (.int 64 ee))
    (hidx : lookupName env "%idxprom.lcssa" = some (.int 64 idx)) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt
        (("%exitcond.not.i", .int 1 (evalICmp .eq (ee - idx) (BitVec.ofNat 64 0))) ::
         ("%sub524", .int 64 (ee - idx)) ::
         ("%tag.0", .int 64 tag) :: ("%ln.0", .int 64 ln) ::
         ("%exitcond38.not.i.3", .int 1 b) :: ("%lit.0", .int 64 lit) :: env)
        { s with pc := if evalICmp .eq (ee - idx) (BitVec.ofNat 64 0) = 1
                        then "if.then527" else "if.end.i",
                 pre := some "if.end519" }) := by
  refine stage2NoEventLitChain_step_at_block (s := stateAt env s)
    (s' := stateAt (("%exitcond.not.i", .int 1 (evalICmp .eq (ee - idx) (BitVec.ofNat 64 0))) ::
         ("%sub524", .int 64 (ee - idx)) ::
         ("%tag.0", .int 64 tag) :: ("%ln.0", .int 64 ln) ::
         ("%exitcond38.not.i.3", .int 1 b) :: ("%lit.0", .int 64 lit) :: env) s)
    (b := ⟨"if.end519", stage2NoEventLitChainIfEnd519Instrs,
      Term.condbr (Operand.reg "%exitcond.not.i") "if.then527" "if.end.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using stage2NoEventLitChain_findBlock_if_end519
  · exact stage2NoEventLitChain_denote_if_end519 calls env s p hpre hincLit hincB hincLn hincTag hee hidx
  · rw [stage2NoEventLitChain_execTerm_condbr _ "%exitcond.not.i" "if.then527" "if.end.i" "if.end519"
      (by simp only [stateAt, hpc]) (by simp only [stateAt, evalOperand]; rw [lookupName_cons_self])]
    rfl

theorem stage2NoEventLitChain_step_if_end_i (calls : Calls) (env : Env) (s : State)
    {base : Nat} {lit : BitVec 64} {u : UInt8}
    (hpc : s.pc = "if.end.i")
    (harr : lookupName env "%arrayidx6.le1046" = some (.ptr base))
    (hlit : lookupName env "%lit.0" = some (.int 64 lit))
    (hu : readByte s.mem base = some u) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt
        (("%cmp7.not.i", .int 1 (evalICmp .eq u.toBitVec (litByte lit 0))) ::
         ("%73", .int 8 (litByte lit 0)) ::
         ("%72", .int 8 u.toBitVec) :: env)
        { s with pc := if evalICmp .eq u.toBitVec (litByte lit 0) = 1
                        then "for.body.i.1" else "if.then527",
                 pre := some "if.end.i" }) := by
  refine stage2NoEventLitChain_step_at_block (s := stateAt env s)
    (s' := stateAt (("%cmp7.not.i", .int 1 (evalICmp .eq u.toBitVec (litByte lit 0))) ::
         ("%73", .int 8 (litByte lit 0)) ::
         ("%72", .int 8 u.toBitVec) :: env) s)
    (b := ⟨"if.end.i", stage2NoEventLitChainIfEndIInstrs,
      Term.condbr (Operand.reg "%cmp7.not.i") "for.body.i.1" "if.then527"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using stage2NoEventLitChain_findBlock_if_end_i
  · exact stage2NoEventLitChain_denote_if_end_i calls env s harr hlit hu
  · rw [stage2NoEventLitChain_execTerm_condbr _ "%cmp7.not.i" "for.body.i.1" "if.then527" "if.end.i"
      (by simp only [stateAt, hpc]) (by simp only [stateAt, evalOperand]; rw [lookupName_cons_self])]
    rfl

theorem stage2NoEventLitChain_step_for_body_i_1 (calls : Calls) (env : Env) (s : State)
    {sub : BitVec 64}
    (hpc : s.pc = "for.body.i.1")
    (hsub : lookupName env "%sub524" = some (.int 64 sub)) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt
        (("%exitcond.not.i.1", .int 1 (evalICmp .eq sub (BitVec.ofNat 64 1))) :: env)
        { s with pc := if evalICmp .eq sub (BitVec.ofNat 64 1) = 1
                        then "if.then527" else "if.end.i.1",
                 pre := some "for.body.i.1" }) := by
  refine stage2NoEventLitChain_step_at_block (s := stateAt env s)
    (s' := stateAt (("%exitcond.not.i.1", .int 1 (evalICmp .eq sub (BitVec.ofNat 64 1))) :: env) s)
    (b := ⟨"for.body.i.1", stage2NoEventLitChainForBodyI1Instrs,
      Term.condbr (Operand.reg "%exitcond.not.i.1") "if.then527" "if.end.i.1"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using stage2NoEventLitChain_findBlock_for_body_i_1
  · exact stage2NoEventLitChain_denote_for_body_i_1 calls env s hsub
  · rw [stage2NoEventLitChain_execTerm_condbr _ "%exitcond.not.i.1" "if.then527" "if.end.i.1" "for.body.i.1"
      (by simp only [stateAt, hpc]) (by simp only [stateAt, evalOperand]; rw [lookupName_cons_self])]
    rfl

theorem stage2NoEventLitChain_step_if_end_i_1 (calls : Calls) (env : Env) (s : State)
    {base : Nat} {lit : BitVec 64} {u : UInt8}
    (hpc : s.pc = "if.end.i.1")
    (harr : lookupName env "%arrayidx6.le1046" = some (.ptr base))
    (hlit : lookupName env "%lit.0" = some (.int 64 lit))
    (hu : readByte s.mem (base + 1) = some u) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt
        (("%cmp7.not.i.1", .int 1 (evalICmp .eq u.toBitVec (litByte lit 1))) ::
         ("%65", .int 8 (litByte lit 1)) ::
         ("%shr.i.1", .int 64 (lit >>> 8)) ::
         ("%64", .int 8 u.toBitVec) ::
         ("%arrayidx.i.1", .ptr (base + 1)) :: env)
        { s with pc := if evalICmp .eq u.toBitVec (litByte lit 1) = 1
                        then "for.body.i.2" else "if.then527",
                 pre := some "if.end.i.1" }) := by
  refine stage2NoEventLitChain_step_at_block (s := stateAt env s)
    (s' := stateAt (("%cmp7.not.i.1", .int 1 (evalICmp .eq u.toBitVec (litByte lit 1))) ::
         ("%65", .int 8 (litByte lit 1)) ::
         ("%shr.i.1", .int 64 (lit >>> 8)) ::
         ("%64", .int 8 u.toBitVec) ::
         ("%arrayidx.i.1", .ptr (base + 1)) :: env) s)
    (b := ⟨"if.end.i.1", stage2NoEventLitChainIfEndI1Instrs,
      Term.condbr (Operand.reg "%cmp7.not.i.1") "for.body.i.2" "if.then527"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using stage2NoEventLitChain_findBlock_if_end_i_1
  · exact stage2NoEventLitChain_denote_if_end_i_1 calls env s harr hlit hu
  · rw [stage2NoEventLitChain_execTerm_condbr _ "%cmp7.not.i.1" "for.body.i.2" "if.then527" "if.end.i.1"
      (by simp only [stateAt, hpc]) (by simp only [stateAt, evalOperand]; rw [lookupName_cons_self])]
    rfl

theorem stage2NoEventLitChain_step_for_body_i_2 (calls : Calls) (env : Env) (s : State)
    {sub : BitVec 64}
    (hpc : s.pc = "for.body.i.2")
    (hsub : lookupName env "%sub524" = some (.int 64 sub)) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt
        (("%exitcond.not.i.2", .int 1 (evalICmp .eq sub (BitVec.ofNat 64 2))) :: env)
        { s with pc := if evalICmp .eq sub (BitVec.ofNat 64 2) = 1
                        then "if.then527" else "if.end.i.2",
                 pre := some "for.body.i.2" }) := by
  refine stage2NoEventLitChain_step_at_block (s := stateAt env s)
    (s' := stateAt (("%exitcond.not.i.2", .int 1 (evalICmp .eq sub (BitVec.ofNat 64 2))) :: env) s)
    (b := ⟨"for.body.i.2", stage2NoEventLitChainForBodyI2Instrs,
      Term.condbr (Operand.reg "%exitcond.not.i.2") "if.then527" "if.end.i.2"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using stage2NoEventLitChain_findBlock_for_body_i_2
  · exact stage2NoEventLitChain_denote_for_body_i_2 calls env s hsub
  · rw [stage2NoEventLitChain_execTerm_condbr _ "%exitcond.not.i.2" "if.then527" "if.end.i.2" "for.body.i.2"
      (by simp only [stateAt, hpc]) (by simp only [stateAt, evalOperand]; rw [lookupName_cons_self])]
    rfl

theorem stage2NoEventLitChain_step_if_end_i_2 (calls : Calls) (env : Env) (s : State)
    {base : Nat} {lit : BitVec 64} {u : UInt8}
    (hpc : s.pc = "if.end.i.2")
    (harr : lookupName env "%arrayidx6.le1046" = some (.ptr base))
    (hlit : lookupName env "%lit.0" = some (.int 64 lit))
    (hu : readByte s.mem (base + 2) = some u) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt
        (("%cmp7.not.i.2", .int 1 (evalICmp .eq u.toBitVec (litByte lit 2))) ::
         ("%67", .int 8 (litByte lit 2)) ::
         ("%shr.i.2", .int 64 (lit >>> 16)) ::
         ("%66", .int 8 u.toBitVec) ::
         ("%arrayidx.i.2", .ptr (base + 2)) :: env)
        { s with pc := if evalICmp .eq u.toBitVec (litByte lit 2) = 1
                        then "for.body.i.3" else "if.then527",
                 pre := some "if.end.i.2" }) := by
  refine stage2NoEventLitChain_step_at_block (s := stateAt env s)
    (s' := stateAt (("%cmp7.not.i.2", .int 1 (evalICmp .eq u.toBitVec (litByte lit 2))) ::
         ("%67", .int 8 (litByte lit 2)) ::
         ("%shr.i.2", .int 64 (lit >>> 16)) ::
         ("%66", .int 8 u.toBitVec) ::
         ("%arrayidx.i.2", .ptr (base + 2)) :: env) s)
    (b := ⟨"if.end.i.2", stage2NoEventLitChainIfEndI2Instrs,
      Term.condbr (Operand.reg "%cmp7.not.i.2") "for.body.i.3" "if.then527"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using stage2NoEventLitChain_findBlock_if_end_i_2
  · exact stage2NoEventLitChain_denote_if_end_i_2 calls env s harr hlit hu
  · rw [stage2NoEventLitChain_execTerm_condbr _ "%cmp7.not.i.2" "for.body.i.3" "if.then527" "if.end.i.2"
      (by simp only [stateAt, hpc]) (by simp only [stateAt, evalOperand]; rw [lookupName_cons_self])]
    rfl

theorem stage2NoEventLitChain_step_for_body_i_3 (calls : Calls) (env : Env) (s : State)
    {sub : BitVec 64}
    (hpc : s.pc = "for.body.i.3")
    (hsub : lookupName env "%sub524" = some (.int 64 sub)) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt
        (("%exitcond.not.i.3", .int 1 (evalICmp .eq sub (BitVec.ofNat 64 3))) :: env)
        { s with pc := if evalICmp .eq sub (BitVec.ofNat 64 3) = 1
                        then "if.then527" else "if.end.i.3",
                 pre := some "for.body.i.3" }) := by
  refine stage2NoEventLitChain_step_at_block (s := stateAt env s)
    (s' := stateAt (("%exitcond.not.i.3", .int 1 (evalICmp .eq sub (BitVec.ofNat 64 3))) :: env) s)
    (b := ⟨"for.body.i.3", stage2NoEventLitChainForBodyI3Instrs,
      Term.condbr (Operand.reg "%exitcond.not.i.3") "if.then527" "if.end.i.3"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using stage2NoEventLitChain_findBlock_for_body_i_3
  · exact stage2NoEventLitChain_denote_for_body_i_3 calls env s hsub
  · rw [stage2NoEventLitChain_execTerm_condbr _ "%exitcond.not.i.3" "if.then527" "if.end.i.3" "for.body.i.3"
      (by simp only [stateAt, hpc]) (by simp only [stateAt, evalOperand]; rw [lookupName_cons_self])]
    rfl

theorem stage2NoEventLitChain_step_if_end_i_3 (calls : Calls) (env : Env) (s : State)
    {base : Nat} {lit : BitVec 64} {u : UInt8}
    (hpc : s.pc = "if.end.i.3")
    (harr : lookupName env "%arrayidx6.le1046" = some (.ptr base))
    (hlit : lookupName env "%lit.0" = some (.int 64 lit))
    (hu : readByte s.mem (base + 3) = some u) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt
        (("%cmp7.not.i.3", .int 1 (evalICmp .eq u.toBitVec (litByte lit 3))) ::
         ("%69", .int 8 (litByte lit 3)) ::
         ("%shr.i.3", .int 64 (lit >>> 24)) ::
         ("%68", .int 8 u.toBitVec) ::
         ("%arrayidx.i.3", .ptr (base + 3)) :: env)
        { s with pc := if evalICmp .eq u.toBitVec (litByte lit 3) = 1
                        then "for.cond.i.3" else "if.then527",
                 pre := some "if.end.i.3" }) := by
  refine stage2NoEventLitChain_step_at_block (s := stateAt env s)
    (s' := stateAt (("%cmp7.not.i.3", .int 1 (evalICmp .eq u.toBitVec (litByte lit 3))) ::
         ("%69", .int 8 (litByte lit 3)) ::
         ("%shr.i.3", .int 64 (lit >>> 24)) ::
         ("%68", .int 8 u.toBitVec) ::
         ("%arrayidx.i.3", .ptr (base + 3)) :: env) s)
    (b := ⟨"if.end.i.3", stage2NoEventLitChainIfEndI3Instrs,
      Term.condbr (Operand.reg "%cmp7.not.i.3") "for.cond.i.3" "if.then527"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using stage2NoEventLitChain_findBlock_if_end_i_3
  · exact stage2NoEventLitChain_denote_if_end_i_3 calls env s harr hlit hu
  · rw [stage2NoEventLitChain_execTerm_condbr _ "%cmp7.not.i.3" "for.cond.i.3" "if.then527" "if.end.i.3"
      (by simp only [stateAt, hpc]) (by simp only [stateAt, evalOperand]; rw [lookupName_cons_self])]
    rfl

theorem stage2NoEventLitChain_step_for_cond_i_3 (calls : Calls) (env : Env) (s : State)
    {b : BitVec 1}
    (hpc : s.pc = "for.cond.i.3")
    (hb : lookupName env "%exitcond38.not.i.3" = some (.int 1 b)) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt env
        { s with pc := if b = 1 then "for.end.i" else "for.body.i.4",
                 pre := some "for.cond.i.3" }) := by
  refine stage2NoEventLitChain_step_at_block (s := stateAt env s)
    (s' := stateAt env s)
    (b := ⟨"for.cond.i.3", stage2NoEventLitChainForCondI3Instrs,
      Term.condbr (Operand.reg "%exitcond38.not.i.3") "for.end.i" "for.body.i.4"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using stage2NoEventLitChain_findBlock_for_cond_i_3
  · simp [stage2NoEventLitChain_denote_for_cond_i_3]
  · rw [stage2NoEventLitChain_execTerm_condbr _ "%exitcond38.not.i.3" "for.end.i" "for.body.i.4" "for.cond.i.3"
      (by simp only [stateAt, hpc]) (BlockEval.evalOperand_reg_of env s "%exitcond38.not.i.3" (.int 1 b) hb)]
    rfl

theorem stage2NoEventLitChain_step_for_body_i_4 (calls : Calls) (env : Env) (s : State)
    {sub : BitVec 64}
    (hpc : s.pc = "for.body.i.4")
    (hsub : lookupName env "%sub524" = some (.int 64 sub)) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt
        (("%exitcond.not.i.4", .int 1 (evalICmp .eq sub (BitVec.ofNat 64 4))) :: env)
        { s with pc := if evalICmp .eq sub (BitVec.ofNat 64 4) = 1
                        then "if.then527" else "if.end.i.4",
                 pre := some "for.body.i.4" }) := by
  refine stage2NoEventLitChain_step_at_block (s := stateAt env s)
    (s' := stateAt (("%exitcond.not.i.4", .int 1 (evalICmp .eq sub (BitVec.ofNat 64 4))) :: env) s)
    (b := ⟨"for.body.i.4", stage2NoEventLitChainForBodyI4Instrs,
      Term.condbr (Operand.reg "%exitcond.not.i.4") "if.then527" "if.end.i.4"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using stage2NoEventLitChain_findBlock_for_body_i_4
  · exact stage2NoEventLitChain_denote_for_body_i_4 calls env s hsub
  · rw [stage2NoEventLitChain_execTerm_condbr _ "%exitcond.not.i.4" "if.then527" "if.end.i.4" "for.body.i.4"
      (by simp only [stateAt, hpc]) (by simp only [stateAt, evalOperand]; rw [lookupName_cons_self])]
    rfl

theorem stage2NoEventLitChain_step_if_end_i_4 (calls : Calls) (env : Env) (s : State)
    {base : Nat} {lit : BitVec 64} {u : UInt8}
    (hpc : s.pc = "if.end.i.4")
    (harr : lookupName env "%arrayidx6.le1046" = some (.ptr base))
    (hlit : lookupName env "%lit.0" = some (.int 64 lit))
    (hu : readByte s.mem (base + 4) = some u) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt
        (("%cmp7.not.i.4", .int 1 (evalICmp .eq u.toBitVec (litByte lit 4))) ::
         ("%71", .int 8 (litByte lit 4)) ::
         ("%shr.i.4", .int 64 (lit >>> 32)) ::
         ("%70", .int 8 u.toBitVec) ::
         ("%arrayidx.i.4", .ptr (base + 4)) :: env)
        { s with pc := if evalICmp .eq u.toBitVec (litByte lit 4) = 1
                        then "for.end.i" else "if.then527",
                 pre := some "if.end.i.4" }) := by
  refine stage2NoEventLitChain_step_at_block (s := stateAt env s)
    (s' := stateAt (("%cmp7.not.i.4", .int 1 (evalICmp .eq u.toBitVec (litByte lit 4))) ::
         ("%71", .int 8 (litByte lit 4)) ::
         ("%shr.i.4", .int 64 (lit >>> 32)) ::
         ("%70", .int 8 u.toBitVec) ::
         ("%arrayidx.i.4", .ptr (base + 4)) :: env) s)
    (b := ⟨"if.end.i.4", stage2NoEventLitChainIfEndI4Instrs,
      Term.condbr (Operand.reg "%cmp7.not.i.4") "for.end.i" "if.then527"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using stage2NoEventLitChain_findBlock_if_end_i_4
  · exact stage2NoEventLitChain_denote_if_end_i_4 calls env s harr hlit hu
  · rw [stage2NoEventLitChain_execTerm_condbr _ "%cmp7.not.i.4" "for.end.i" "if.then527" "if.end.i.4"
      (by simp only [stateAt, hpc]) (by simp only [stateAt, evalOperand]; rw [lookupName_cons_self])]
    rfl

theorem stage2NoEventLitChain_step_for_end_i (calls : Calls) (env : Env) (s : State)
    {sub ln : BitVec 64}
    (hpc : s.pc = "for.end.i")
    (hsub : lookupName env "%sub524" = some (.int 64 sub))
    (hln : lookupName env "%ln.0" = some (.int 64 ln)) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt
        (("%cmp13.not.i", .int 1 (evalICmp .eq sub ln)) :: env)
        { s with pc := if evalICmp .eq sub ln = 1 then "if.end545" else "if.then527",
                 pre := some "for.end.i" }) := by
  refine stage2NoEventLitChain_step_at_block (s := stateAt env s)
    (s' := stateAt (("%cmp13.not.i", .int 1 (evalICmp .eq sub ln)) :: env) s)
    (b := ⟨"for.end.i", stage2NoEventLitChainForEndIInstrs,
      Term.condbr (Operand.reg "%cmp13.not.i") "if.end545" "if.then527"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using stage2NoEventLitChain_findBlock_for_end_i
  · exact stage2NoEventLitChain_denote_for_end_i calls env s hsub hln
  · rw [stage2NoEventLitChain_execTerm_condbr _ "%cmp13.not.i" "if.end545" "if.then527" "for.end.i"
      (by simp only [stateAt, hpc]) (by simp only [stateAt, evalOperand]; rw [lookupName_cons_self])]
    rfl

/-! ### The literal's bytes and the rule at a prefix

`litBytes` is the packed literal as the phi supplies it (`packByte lit i` is the
`i`-th byte the body's `lshr`/`trunc` produces), and the four lemmas below read
`neLitCheck` at the three ways the chain can stop: a differing byte, a token
that ends inside the literal, and a token that runs past it.  They are stated in
terms of `getD` so the run's byte facts (`readByte_of_readBytes`) feed them
directly. -/

/-- Byte `i` of the packed literal, as `packBytes` reads it out of the word. -/
def packByte (lit : BitVec 64) (i : Nat) : UInt8 :=
  UInt8.ofNat ((lit.toNat >>> (8 * i)) % 256)

/-- The packed literal, as the shared `phi` supplies it. -/
def litBytes (lit : BitVec 64) (ln : Nat) : List UInt8 :=
  (List.range ln).map (packByte lit)

/-- `litBytes` is the rule's `packBytes`. -/
theorem litBytes_eq_packBytes (lit : BitVec 64) (ln : Nat) :
    litBytes lit ln = packBytes lit.toNat ln := rfl

theorem litBytes_length (lit : BitVec 64) (ln : Nat) :
    (litBytes lit ln).length = ln := by
  simp [litBytes]

theorem litBytes_getD {lit : BitVec 64} {ln j : Nat} (hj : j < ln) :
    (litBytes lit ln).getD j 0 = packByte lit j := by
  simp only [litBytes, List.getD_eq_getElem?_getD, List.getElem?_map]
  rw [List.getElem?_range hj]
  rfl

/-- `packBytes`'s four-byte shape. -/
theorem litBytes_four (lit : BitVec 64) :
    litBytes lit 4 = [packByte lit 0, packByte lit 1, packByte lit 2, packByte lit 3] := rfl

/-- `packBytes`'s five-byte shape. -/
theorem litBytes_five (lit : BitVec 64) :
    litBytes lit 5 = [packByte lit 0, packByte lit 1, packByte lit 2, packByte lit 3,
      packByte lit 4] := rfl

/-- The `trunc`-form byte equals the `UInt8` `packBytes` carries. -/
theorem litByte_eq_packByte (lit : BitVec 64) (i : Nat) :
    litByte lit i = (packByte lit i).toBitVec := by
  rw [litByte]
  exact stage2NoEventLitChain_byte_eq_uint8 lit i

/-- `neLitGo` at an offset is the rule's answer shifted by the offset. -/
theorem neLitGo_shift (i : Nat) (q bs : List UInt8) :
    neLitGo i q bs = (neLitCheck q bs).map (· + i) := by
  induction q generalizing i bs with
  | nil =>
      cases bs with
      | nil => rfl
      | cons b bs =>
          show some i = (neLitCheck [] (b :: bs)).map (· + i)
          rw [show neLitCheck [] (b :: bs) = some 0 from rfl]
          simp
  | cons u q ih =>
      cases bs with
      | nil =>
          show some i = (neLitCheck (u :: q) []).map (· + i)
          rw [show neLitCheck (u :: q) [] = some 0 from rfl]
          simp
      | cons b bs =>
          by_cases h : u = b
          · have hL : neLitGo i (u :: q) (b :: bs) = neLitGo (i + 1) q bs := by
              simp only [neLitGo, ite_eq_left h]
            have hR : neLitCheck (u :: q) (b :: bs) = neLitGo 1 q bs := by
              simp only [neLitCheck, neLitGo, ite_eq_left h]
            rw [hL, hR, ih (i := i + 1), ih (i := 1), Option.map_map]
            congr 1
            funext x
            simp
            omega
          · have hL : neLitGo i (u :: q) (b :: bs) = some i := by
              simp only [neLitGo, ite_eq_right h]
            have hR : neLitCheck (u :: q) (b :: bs) = some 0 := by
              simp only [neLitCheck, neLitGo, ite_eq_right h]
            rw [hL, hR]
            simp

/-- A first differing byte at `k`, with the bytes before it equal: `some k`. -/
theorem neLitCheck_eq_some_of_diff {q bs : List UInt8} {k : Nat}
    (hq : k < q.length) (hb : k < bs.length)
    (hpre : ∀ j, j < k → q.getD j 0 = bs.getD j 0)
    (hdiff : q.getD k 0 ≠ bs.getD k 0) :
    neLitCheck q bs = some k := by
  induction k generalizing q bs with
  | zero =>
      match q, bs with
      | [], _ => simp at hq
      | _ :: _, [] => simp at hb
      | u :: qs, b :: bs' =>
          have h : u ≠ b := by simpa using hdiff
          simp [neLitCheck, neLitGo, h]
  | succ k ih =>
      match q, bs with
      | [], _ => simp at hq
      | _ :: _, [] => simp at hb
      | u :: qs, b :: bs' =>
          have hu : u = b := by
            have := hpre 0 (by omega); simpa using this
          have hq' : k < qs.length := by simpa using hq
          have hb' : k < bs'.length := by simpa using hb
          have hpre' : ∀ j, j < k → qs.getD j 0 = bs'.getD j 0 := by
            intro j hj
            have := hpre (j + 1) (by omega)
            simpa using this
          have hdiff' : qs.getD k 0 ≠ bs'.getD k 0 := by
            have := hdiff
            simpa using this
          rw [neLitCheck]
          simp only [neLitGo, hu]
          rw [neLitGo_shift, ih hq' hb' hpre' hdiff']
          rfl

/-- A token that ends inside the literal, its `k` bytes equal: `some k`. -/
theorem neLitCheck_eq_some_of_short {q bs : List UInt8} {k : Nat}
    (hlen : q.length = k) (hk : k < bs.length)
    (hpre : ∀ j, j < k → q.getD j 0 = bs.getD j 0) :
    neLitCheck q bs = some k := by
  induction k generalizing q bs with
  | zero =>
      have hq : q = [] := List.length_eq_zero_iff.mp hlen
      subst hq
      match bs with
      | [] => simp at hk
      | b :: bs' => simp [neLitCheck, neLitGo]
  | succ k ih =>
      match q, bs with
      | [], _ => simp at hlen
      | _ :: _, [] => simp at hk
      | u :: qs, b :: bs' =>
          have hu : u = b := by
            have := hpre 0 (by omega); simpa using this
          have hlen' : qs.length = k := by simpa using hlen
          have hk' : k < bs'.length := by simpa using hk
          have hpre' : ∀ j, j < k → qs.getD j 0 = bs'.getD j 0 := by
            intro j hj
            have := hpre (j + 1) (by omega)
            simpa using this
          rw [neLitCheck]
          simp only [neLitGo, hu]
          rw [neLitGo_shift, ih hlen' hk' hpre']
          rfl

/-- A token that runs past the literal, the literal's bytes equal: `some ln`. -/
theorem neLitCheck_eq_some_of_long {q bs : List UInt8}
    (hlong : bs.length < q.length)
    (hpre : ∀ j, j < bs.length → q.getD j 0 = bs.getD j 0) :
    neLitCheck q bs = some bs.length := by
  induction bs generalizing q with
  | nil =>
      match q with
      | [] => simp at hlong
      | _ :: _ => simp [neLitCheck, neLitGo]
  | cons b bs ih =>
      match q with
      | [] => simp at hlong
      | u :: qs =>
          have hu : u = b := by
            have := hpre 0 (by simp); simpa using this
          have hlong' : bs.length < qs.length := by simpa using hlong
          have hpre' : ∀ j, j < bs.length → qs.getD j 0 = bs.getD j 0 := by
            intro j hj
            have := hpre (j + 1) (by simp; omega)
            simpa using this
          rw [neLitCheck]
          simp only [neLitGo, hu]
          rw [neLitGo_shift, ih hlong' hpre']
          rfl

/-- Bytes before a prefix's end agree: the token accepts. -/
theorem neLitCheck_eq_none_of_prefix {q bs : List UInt8}
    (hlen : q.length = bs.length)
    (hpre : ∀ j, j < q.length → q.getD j 0 = bs.getD j 0) :
    neLitCheck q bs = none := by
  induction bs generalizing q with
  | nil =>
      have hq : q = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst hq; rfl
  | cons b bs ih =>
      match q with
      | [] => simp at hlen
      | u :: qs =>
          have hu : u = b := by
            have := hpre 0 (by simp)
            simpa using this
          have hlen' : qs.length = bs.length := by simpa using hlen
          have hpre' : ∀ j, j < qs.length → qs.getD j 0 = bs.getD j 0 := by
            intro j hj
            have := hpre (j + 1) (by simp; omega)
            simpa using this
          rw [neLitCheck]
          simp only [neLitGo, hu]
          rw [neLitGo_shift, ih hlen' hpre']
          rfl

/-- A token equal to the literal accepts: `none`. -/
theorem neLitCheck_eq_none_of_eq (bs : List UInt8) :
    neLitCheck bs bs = none := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      rw [neLitCheck]
      simp only [neLitGo]
      rw [neLitGo_shift, ih]
      rfl

/-! ### The rule's comparisons and the chain's exits -/

/-- `evalICmp .eq` at its one. -/
theorem stage2NoEventLitChain_evalICmp_eq_one {w : Nat} (a b : BitVec w) :
    evalICmp .eq a b = 1 ↔ a = b := by
  by_cases h : a = b <;> simp [evalICmp, h]

/-- `evalICmp .eq` at its zero. -/
theorem stage2NoEventLitChain_evalICmp_eq_zero {w : Nat} (a b : BitVec w) :
    evalICmp .eq a b = 0 ↔ a ≠ b := by
  by_cases h : a = b <;> simp [evalICmp, h]

/-- `evalICmp .eq` at two small `n`-literals that are equal. -/
theorem stage2NoEventLitChain_evalICmp_ofNat_one {n k : Nat}
    (hn : n < 2 ^ 64) (hk : k < 2 ^ 64) (h : n = k) :
    evalICmp .eq (BitVec.ofNat 64 n) (BitVec.ofNat 64 k) = 1 := by
  rw [stage2NoEventLitChain_evalICmp_eq_one]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt hk, h]

/-- `evalICmp .eq` at two small `n`-literals that differ. -/
theorem stage2NoEventLitChain_evalICmp_ofNat_zero {n k : Nat}
    (hn : n < 2 ^ 64) (hk : k < 2 ^ 64) (h : n ≠ k) :
    evalICmp .eq (BitVec.ofNat 64 n) (BitVec.ofNat 64 k) = 0 := by
  rw [stage2NoEventLitChain_evalICmp_eq_zero]
  intro heq
  apply h
  have := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt hk] at this
  exact this

/-- The body's truncated byte and `packBytes`'s `UInt8` are the same byte. -/
theorem stage2NoEventLitChain_byte_iff (u : UInt8) (lit : BitVec 64) (i : Nat) :
    (u.toBitVec = litByte lit i) ↔ (u = packByte lit i) := by
  rw [litByte_eq_packByte, UInt8.toBitVec_inj]

/-- Resolve a register read against a concrete cell list, at a lookup. -/
macro "lit_luk" : tactic => `(tactic|
  (repeat rw [lookupName_cons_ne _ _ (by decide)]
   first
    | rw [lookupName_cons_self]
    | assumption))

/-- The `%ei520.0.ph` incoming list, as `if.then527` carries it. -/
def ifThen527EiIncoming : List (String × Operand) :=
  [("if.end519", (Operand.reg "%sub524")),
   ("if.end.i", (Operand.imm (.int 64 (BitVec.ofNat 64 0)))),
   ("for.body.i.1", (Operand.reg "%sub524")),
   ("if.end.i.1", (Operand.imm (.int 64 (BitVec.ofNat 64 1)))),
   ("for.body.i.2", (Operand.reg "%sub524")),
   ("if.end.i.2", (Operand.imm (.int 64 (BitVec.ofNat 64 2)))),
   ("for.body.i.3", (Operand.reg "%sub524")),
   ("if.end.i.3", (Operand.imm (.int 64 (BitVec.ofNat 64 3)))),
   ("for.body.i.4", (Operand.reg "%sub524")),
   ("if.end.i.4", (Operand.imm (.int 64 (BitVec.ofNat 64 4)))),
   ("for.end.i", (Operand.reg "%ln.0"))]

-- The list is the pinned block's own `phi` incoming list.
#guard decide
  (litPhiIncoming ((stage2NoEventBody.findBlock "if.then527").getD ⟨"", [], .unreachable⟩) "%ei520.0.ph" =
    some ifThen527EiIncoming)

/-- The refusal exit, read at its entry state: the block's `%ei520.0.ph` selects
an operand at the predecessor the chain left, and that operand reads to the
offset.  The cell itself is bound by the block's first step, which is the
walk's. -/
def litRefusal (e : State) (i : Nat) : Prop :=
  e.pc = "if.then527" ∧
    ∃ op, phiIncoming (e.pre.getD "") ifThen527EiIncoming = some op ∧
      evalOperand e op = some (.int 64 (BitVec.ofNat 64 i))

/-- The accepting exit. -/
def litAccept (e : State) : Prop := e.pc = "if.end545"

/-- A refusal whose selected operand is a literal constant. -/
theorem litRefusal_const (e : State) (pred : String) (k : Nat)
    (hpc : e.pc = "if.then527") (hpre : e.pre = some pred)
    (hinc : phiIncoming pred ifThen527EiIncoming =
      some (.imm (.int 64 (BitVec.ofNat 64 k)))) :
    litRefusal e k :=
  ⟨hpc, _, by simpa [hpre] using hinc, rfl⟩

/-- A refusal whose selected operand is `%sub524`, read as a word. -/
theorem litRefusal_sub (e : State) (pred : String) (v : BitVec 64)
    (hpc : e.pc = "if.then527") (hpre : e.pre = some pred)
    (hinc : phiIncoming pred ifThen527EiIncoming = some (.reg "%sub524"))
    (hv : evalOperand e (.reg "%sub524") = some (.int 64 v)) :
    litRefusal e v.toNat :=
  ⟨hpc, _, by simpa [hpre] using hinc, by simpa [BitVec.ofNat_toNat] using hv⟩

/-- A refusal whose selected operand is `%ln.0`. -/
theorem litRefusal_ln (e : State) (pred : String) (v : BitVec 64)
    (hpc : e.pc = "if.then527") (hpre : e.pre = some pred)
    (hinc : phiIncoming pred ifThen527EiIncoming = some (.reg "%ln.0"))
    (hv : evalOperand e (.reg "%ln.0") = some (.int 64 v)) :
    litRefusal e v.toNat :=
  ⟨hpc, _, by simpa [hpre] using hinc, by simpa [BitVec.ofNat_toNat] using hv⟩

/-- A differing byte at `k` refuses at `k`. -/
theorem stage2NoEventLitChain_refuse_diff (e : State) (pred : String) (k : Nat)
    {q bs : List UInt8}
    (hpc : e.pc = "if.then527") (hpre : e.pre = some pred)
    (hinc : phiIncoming pred ifThen527EiIncoming =
      some (.imm (.int 64 (BitVec.ofNat 64 k))))
    (hqlen : k < q.length) (hblen : k < bs.length)
    (hprefix : ∀ j, j < k → q.getD j 0 = bs.getD j 0)
    (hdiff : q.getD k 0 ≠ bs.getD k 0) :
    ∃ i, litRefusal e i ∧ neLitCheck q bs = some i :=
  ⟨k, litRefusal_const e pred k hpc hpre hinc,
    neLitCheck_eq_some_of_diff hqlen hblen hprefix hdiff⟩

/-- A token ending at `k` refuses at `k`, reading `%sub524`. -/
theorem stage2NoEventLitChain_refuse_short (e : State) (pred : String) (k : Nat)
    {q bs : List UInt8}
    (hpc : e.pc = "if.then527") (hpre : e.pre = some pred)
    (hinc : phiIncoming pred ifThen527EiIncoming = some (.reg "%sub524"))
    (hv : evalOperand e (.reg "%sub524") = some (.int 64 (BitVec.ofNat 64 k)))
    (hk64 : k < 2 ^ 64) (hlen : q.length = k) (hk : k < bs.length)
    (hprefix : ∀ j, j < k → q.getD j 0 = bs.getD j 0) :
    ∃ i, litRefusal e i ∧ neLitCheck q bs = some i := by
  refine ⟨k, ?_, neLitCheck_eq_some_of_short hlen hk hprefix⟩
  have h := litRefusal_sub e pred (BitVec.ofNat 64 k) hpc hpre hinc hv
  rwa [show (BitVec.ofNat 64 k).toNat = k from by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]] at h

/-- A token running past the literal refuses at its width, reading `%ln.0`. -/
theorem stage2NoEventLitChain_refuse_long (e : State) (pred : String)
    {q bs : List UInt8} {v : BitVec 64}
    (hpc : e.pc = "if.then527") (hpre : e.pre = some pred)
    (hinc : phiIncoming pred ifThen527EiIncoming = some (.reg "%ln.0"))
    (hv : evalOperand e (.reg "%ln.0") = some (.int 64 v))
    (hvlen : v.toNat = bs.length)
    (hlong : bs.length < q.length)
    (hprefix : ∀ j, j < bs.length → q.getD j 0 = bs.getD j 0) :
    ∃ i, litRefusal e i ∧ neLitCheck q bs = some i :=
  ⟨v.toNat, litRefusal_ln e pred v hpc hpre hinc hv,
    by rw [hvlen]; exact neLitCheck_eq_some_of_long hlong hprefix⟩

/-- A token equal to the literal accepts. -/
theorem stage2NoEventLitChain_accept_exit (e : State) {q bs : List UInt8}
    (hpc : e.pc = "if.end545")
    (hlen : q.length = bs.length)
    (hprefix : ∀ j, j < q.length → q.getD j 0 = bs.getD j 0) :
    litAccept e ∧ neLitCheck q bs = none :=
  ⟨hpc, neLitCheck_eq_none_of_prefix hlen hprefix⟩

theorem stage2NoEventLitChain_run
    (calls : Calls) (env : Env) (s : State) (p : String)
    {base : Nat} {lit ln tag : BitVec 64} {b : BitVec 1} {ee idx : BitVec 64}
    {n : Nat} {q : List UInt8}
    (hpc : s.pc = "if.end519")
    (hpre : s.pre = some p)
    (hincLit : phiIncoming p [("if.then504", (Operand.imm (.int 64 (BitVec.ofNat 64 435728179558)))), ("if.then509", (Operand.imm (.int 64 (BitVec.ofNat 64 1819047278)))), ("LeafBlock68", (Operand.imm (.int 64 (BitVec.ofNat 64 1702195828))))] = some (.imm (.int 64 lit)))
    (hincB : phiIncoming p [("if.then504", (Operand.imm (.int 1 (BitVec.ofNat 1 0)))), ("if.then509", (Operand.imm (.int 1 (BitVec.ofNat 1 1)))), ("LeafBlock68", (Operand.imm (.int 1 (BitVec.ofNat 1 1))))] = some (.imm (.int 1 b)))
    (hincLn : phiIncoming p [("if.then504", (Operand.imm (.int 64 (BitVec.ofNat 64 5)))), ("if.then509", (Operand.imm (.int 64 (BitVec.ofNat 64 4)))), ("LeafBlock68", (Operand.imm (.int 64 (BitVec.ofNat 64 4))))] = some (.imm (.int 64 ln)))
    (hincTag : phiIncoming p [("if.then504", (Operand.imm (.int 64 (BitVec.ofNat 64 9)))), ("if.then509", (Operand.imm (.int 64 (BitVec.ofNat 64 10)))), ("LeafBlock68", (Operand.imm (.int 64 (BitVec.ofNat 64 8))))] = some (.imm (.int 64 tag)))
    (hee : lookupName env "%ee.1" = some (.int 64 ee))
    (hidx : lookupName env "%idxprom.lcssa" = some (.int 64 idx))
    (hn : n < 2 ^ 64)
    (hsub : ee - idx = BitVec.ofNat 64 n)
    (harr : lookupName env "%arrayidx6.le1046" = some (.ptr base))
    (hq : readBytes s.mem base n = some q)
    (hwidth : (ln = BitVec.ofNat 64 4 ∧ b = 1) ∨ (ln = BitVec.ofNat 64 5 ∧ b = 0)) :
    ∃ (e : State) (j : Nat), j ≤ 13 ∧ e.mem = s.mem ∧
      ((∃ i, litRefusal e i ∧ neLitCheck q (litBytes lit ln.toNat) = some i) ∨
       (litAccept e ∧ neLitCheck q (litBytes lit ln.toNat) = none)) ∧
      (∀ k, runFuel calls (j + k) stage2NoEventBody (stateAt env s) =
        runFuel calls k stage2NoEventBody e) := by
  have hsubn : (ee - idx).toNat = n := by
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have hln_ge : 4 ≤ ln.toNat := by
    rcases hwidth with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide
  let E1 : Env :=
    ("%exitcond.not.i", .int 1 (evalICmp .eq (ee - idx) (BitVec.ofNat 64 0))) ::
    ("%sub524", .int 64 (ee - idx)) ::
    ("%tag.0", .int 64 tag) :: ("%ln.0", .int 64 ln) ::
    ("%exitcond38.not.i.3", .int 1 b) :: ("%lit.0", .int 64 lit) :: env
  let E2 : Env :=
    ("%cmp7.not.i", .int 1 (evalICmp .eq (q[0]?.getD 0).toBitVec (litByte lit 0))) ::
    ("%73", .int 8 (litByte lit 0)) ::
    ("%72", .int 8 (q[0]?.getD 0).toBitVec) :: E1
  let E3 : Env :=
    ("%exitcond.not.i.1", .int 1 (evalICmp .eq (ee - idx) (BitVec.ofNat 64 1))) :: E2
  let E4 : Env :=
    ("%cmp7.not.i.1", .int 1 (evalICmp .eq (q[1]?.getD 0).toBitVec (litByte lit 1))) ::
    ("%65", .int 8 (litByte lit 1)) :: ("%shr.i.1", .int 64 (lit >>> 8)) ::
    ("%64", .int 8 (q[1]?.getD 0).toBitVec) ::
    ("%arrayidx.i.1", .ptr (base + 1)) :: E3
  let E5 : Env :=
    ("%exitcond.not.i.2", .int 1 (evalICmp .eq (ee - idx) (BitVec.ofNat 64 2))) :: E4
  let E6 : Env :=
    ("%cmp7.not.i.2", .int 1 (evalICmp .eq (q[2]?.getD 0).toBitVec (litByte lit 2))) ::
    ("%67", .int 8 (litByte lit 2)) :: ("%shr.i.2", .int 64 (lit >>> 16)) ::
    ("%66", .int 8 (q[2]?.getD 0).toBitVec) ::
    ("%arrayidx.i.2", .ptr (base + 2)) :: E5
  let E7 : Env :=
    ("%exitcond.not.i.3", .int 1 (evalICmp .eq (ee - idx) (BitVec.ofNat 64 3))) :: E6
  let E8 : Env :=
    ("%cmp7.not.i.3", .int 1 (evalICmp .eq (q[3]?.getD 0).toBitVec (litByte lit 3))) ::
    ("%69", .int 8 (litByte lit 3)) :: ("%shr.i.3", .int 64 (lit >>> 24)) ::
    ("%68", .int 8 (q[3]?.getD 0).toBitVec) ::
    ("%arrayidx.i.3", .ptr (base + 3)) :: E7
  let E10 : Env := ("%cmp13.not.i", .int 1 (evalICmp .eq (ee - idx) ln)) :: E8
  let E10b : Env :=
    ("%exitcond.not.i.4", .int 1 (evalICmp .eq (ee - idx) (BitVec.ofNat 64 4))) :: E8
  let E11 : Env :=
    ("%cmp7.not.i.4", .int 1 (evalICmp .eq (q[4]?.getD 0).toBitVec (litByte lit 4))) ::
    ("%71", .int 8 (litByte lit 4)) :: ("%shr.i.4", .int 64 (lit >>> 32)) ::
    ("%70", .int 8 (q[4]?.getD 0).toBitVec) ::
    ("%arrayidx.i.4", .ptr (base + 4)) :: E10b
  let E12 : Env := ("%cmp13.not.i", .int 1 (evalICmp .eq (ee - idx) ln)) :: E11
  have h1 := stage2NoEventLitChain_step_if_end519 calls env s p hpc hpre
    hincLit hincB hincLn hincTag hee hidx
  have hne1 : (0 : BitVec 1) ≠ 1 := by decide
  rcases n with _ | _ | _ | _ | _ | n5
  · -- n = 0
    have hbit1 : evalICmp .eq (ee - idx) (BitVec.ofNat 64 0) = 1 := by
      rw [hsub]; decide
    rw [hbit1, ite_eq_left rfl] at h1
    let t1 : State := { s with pc := "if.then527", pre := some "if.end519" }
    have h1' : step calls stage2NoEventBody (stateAt env s) = .jump (stateAt E1 t1) := by
      simpa [t1, E1, hbit1] using h1
    have hqnil : q = [] := by
      have hlen := JsonEntrySteps.readBytes_length s.mem base 0 hq
      exact List.length_eq_zero_iff.mp hlen
    subst hqnil
    refine ⟨stateAt E1 t1, 1, by omega, rfl, ?_, ?_⟩
    · left
      refine ⟨0, ?_, ?_⟩
      · refine ⟨rfl, .reg "%sub524", ?_, ?_⟩
        · show phiIncoming "if.end519" ifThen527EiIncoming = some (.reg "%sub524")
          decide
        · simp only [stateAt, evalOperand]
          rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self, hsub]
      · have hk : 0 < (litBytes lit ln.toNat).length := by
          rw [litBytes_length]; omega
        exact neLitCheck_eq_some_of_short rfl hk (by intro j hj; omega)
    · intro k
      have hlen : (Path.step (ok := fun _ => True) trivial h1' (Path.nil _)).length = 1 := rfl
      simpa using runFuel_jump_prefix h1' k
  · -- n = 1
    have hb0 : readByte s.mem base = some (q[0]?.getD 0) := by
      simpa using readByte_of_readBytes hq (k := 0) (by omega)
    have hbit1 : evalICmp .eq (ee - idx) (BitVec.ofNat 64 0) = 0 := by
      rw [hsub]; decide
    rw [hbit1, ite_eq_right hne1] at h1
    let t1 : State := { s with pc := "if.end.i", pre := some "if.end519" }
    have h1' : step calls stage2NoEventBody (stateAt env s) = .jump (stateAt E1 t1) := by
      simpa [t1, E1, hbit1] using h1
    have h2 := stage2NoEventLitChain_step_if_end_i calls E1 t1
      (by rfl) (by dsimp only [E1]; lit_luk) (by dsimp only [E1]; lit_luk) (by simpa [t1] using hb0)
    by_cases hc0 : q[0]?.getD 0 = packByte lit 0
    · have hbit2 : evalICmp .eq (q[0]?.getD 0).toBitVec (litByte lit 0) = 1 := by
        rw [stage2NoEventLitChain_evalICmp_eq_one, litByte_eq_packByte, hc0]
      rw [hbit2, ite_eq_left rfl] at h2
      let t2 : State := { t1 with pc := "for.body.i.1", pre := some "if.end.i" }
      have h2' : step calls stage2NoEventBody (stateAt E1 t1) = .jump (stateAt E2 t2) := by
        simpa [t2, E2, hbit2] using h2
      have h3 := stage2NoEventLitChain_step_for_body_i_1 calls E2 t2
        (by rfl) (by dsimp only [E2, E1]; lit_luk)
      have hbit3 : evalICmp .eq (ee - idx) (BitVec.ofNat 64 1) = 1 := by
        rw [hsub]; decide
      rw [hbit3, ite_eq_left rfl] at h3
      let t3 : State := { t2 with pc := "if.then527", pre := some "for.body.i.1" }
      have h3' : step calls stage2NoEventBody (stateAt E2 t2) = .jump (stateAt E3 t3) := by
        simpa [t3, E3, hbit3] using h3
      refine ⟨stateAt E3 t3, 3, by omega, rfl, ?_, ?_⟩
      · left
        have hv : evalOperand (stateAt E3 t3) (.reg "%sub524") =
            some (.int 64 (BitVec.ofNat 64 1)) := by
          simp only [stateAt, evalOperand]
          rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
            lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
            lookupName_cons_ne _ _ (by decide), lookupName_cons_self, hsub]
        refine stage2NoEventLitChain_refuse_short _ "for.body.i.1" 1 rfl rfl (by decide) hv
          (by decide) (JsonEntrySteps.readBytes_length s.mem base 1 hq) ?_ ?_
        · rw [litBytes_length]; omega
        · intro j hj
          have h0 : j = 0 := by omega
          subst h0
          rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 0) (by omega)]
          simpa using hc0
      · intro k
        let P : Path calls stage2NoEventBody (fun _ => True) (stateAt env s) (stateAt E3 t3) :=
          .step trivial h1' (.step trivial h2' (.step trivial h3' (.nil _)))
        have hlen : P.length = 3 := rfl
        rw [show 3 + k = P.length + k by rw [hlen]]
        exact P.runFuel k
    · have hbit2 : evalICmp .eq (q[0]?.getD 0).toBitVec (litByte lit 0) = 0 := by
        rw [stage2NoEventLitChain_evalICmp_eq_zero, litByte_eq_packByte]
        intro h; exact hc0 (UInt8.toBitVec_inj.mp h)
      rw [hbit2, ite_eq_right hne1] at h2
      let t2 : State := { t1 with pc := "if.then527", pre := some "if.end.i" }
      have h2' : step calls stage2NoEventBody (stateAt E1 t1) = .jump (stateAt E2 t2) := by
        simpa [t2, E2, hbit2] using h2
      refine ⟨stateAt E2 t2, 2, by omega, rfl, ?_, ?_⟩
      · left
        refine stage2NoEventLitChain_refuse_diff _ "if.end.i" 0 rfl rfl (by decide) ?_ ?_ ?_ ?_
        · rw [JsonEntrySteps.readBytes_length s.mem base 1 hq]; omega
        · rw [litBytes_length]; omega
        · intro j hj; omega
        · intro h
          apply hc0
          rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 0) (by omega)] at h
          simpa using h
      · intro k
        let P : Path calls stage2NoEventBody (fun _ => True) (stateAt env s) (stateAt E2 t2) :=
          .step trivial h1' (.step trivial h2' (.nil _))
        have hlen : P.length = 2 := rfl
        rw [show 2 + k = P.length + k by rw [hlen]]
        exact P.runFuel k
  · -- n = 2
    have hb0 : readByte s.mem base = some (q[0]?.getD 0) := by
      simpa using readByte_of_readBytes hq (k := 0) (by omega)
    have hbit1 : evalICmp .eq (ee - idx) (BitVec.ofNat 64 0) = 0 := by
      rw [hsub]; decide
    rw [hbit1, ite_eq_right hne1] at h1
    let t1 : State := { s with pc := "if.end.i", pre := some "if.end519" }
    have h1' : step calls stage2NoEventBody (stateAt env s) = .jump (stateAt E1 t1) := by
      simpa [t1, E1, hbit1] using h1
    have h2 := stage2NoEventLitChain_step_if_end_i calls E1 t1
      (by rfl) (by dsimp only [E1]; lit_luk) (by dsimp only [E1]; lit_luk) (by simpa [t1] using hb0)
    by_cases hc0 : q[0]?.getD 0 = packByte lit 0
    · have hbit2 : evalICmp .eq (q[0]?.getD 0).toBitVec (litByte lit 0) = 1 := by
        rw [stage2NoEventLitChain_evalICmp_eq_one, litByte_eq_packByte, hc0]
      rw [hbit2, ite_eq_left rfl] at h2
      let t2 : State := { t1 with pc := "for.body.i.1", pre := some "if.end.i" }
      have h2' : step calls stage2NoEventBody (stateAt E1 t1) = .jump (stateAt E2 t2) := by
        simpa [t2, E2, hbit2] using h2
      have h3 := stage2NoEventLitChain_step_for_body_i_1 calls E2 t2
        (by rfl) (by dsimp only [E2, E1]; lit_luk)
      have hbit3 : evalICmp .eq (ee - idx) (BitVec.ofNat 64 1) = 0 := by
        rw [hsub]; decide
      rw [hbit3, ite_eq_right hne1] at h3
      let t3 : State := { t2 with pc := "if.end.i.1", pre := some "for.body.i.1" }
      have h3' : step calls stage2NoEventBody (stateAt E2 t2) = .jump (stateAt E3 t3) := by
        simpa [t3, E3, hbit3] using h3
      have hb1 : readByte s.mem (base + 1) = some (q[1]?.getD 0) := by
        simpa using readByte_of_readBytes hq (k := 1) (by omega)
      have h4 := stage2NoEventLitChain_step_if_end_i_1 calls E3 t3
        (by rfl) (by dsimp only [E3, E2, E1]; lit_luk)
        (by dsimp only [E3, E2, E1]; lit_luk) (by simpa [t3] using hb1)
      by_cases hc1 : q[1]?.getD 0 = packByte lit 1
      · have hbit4 : evalICmp .eq (q[1]?.getD 0).toBitVec (litByte lit 1) = 1 := by
          rw [stage2NoEventLitChain_evalICmp_eq_one, litByte_eq_packByte, hc1]
        rw [hbit4, ite_eq_left rfl] at h4
        let t4 : State := { t3 with pc := "for.body.i.2", pre := some "if.end.i.1" }
        have h4' : step calls stage2NoEventBody (stateAt E3 t3) = .jump (stateAt E4 t4) := by
          simpa [t4, E4, hbit4] using h4
        have h5 := stage2NoEventLitChain_step_for_body_i_2 calls E4 t4
          (by rfl) (by dsimp only [E4, E3, E2, E1]; lit_luk)
        have hbit5 : evalICmp .eq (ee - idx) (BitVec.ofNat 64 2) = 1 := by
          rw [hsub]; decide
        rw [hbit5, ite_eq_left rfl] at h5
        let t5 : State := { t4 with pc := "if.then527", pre := some "for.body.i.2" }
        have h5' : step calls stage2NoEventBody (stateAt E4 t4) = .jump (stateAt E5 t5) := by
          simpa [t5, E5, hbit5] using h5
        refine ⟨stateAt E5 t5, 5, by omega, rfl, ?_, ?_⟩
        · left
          have hv : evalOperand (stateAt E5 t5) (.reg "%sub524") =
              some (.int 64 (BitVec.ofNat 64 2)) := by
            simp only [stateAt, evalOperand]
            repeat rw [lookupName_cons_ne _ _ (by decide)]
            rw [lookupName_cons_self, hsub]
          refine stage2NoEventLitChain_refuse_short _ "for.body.i.2" 2 rfl rfl (by decide) hv
            (by decide) (JsonEntrySteps.readBytes_length s.mem base 2 hq) ?_ ?_
          · rw [litBytes_length]; omega
          · intro j hj
            have hj' : j = 0 ∨ j = 1 := by omega
            rcases hj' with rfl | rfl
            · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 0) (by omega)]
              simpa using hc0
            · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 1) (by omega)]
              simpa using hc1
        · intro k
          let P : Path calls stage2NoEventBody (fun _ => True) (stateAt env s) (stateAt E5 t5) :=
            .step trivial h1' (.step trivial h2' (.step trivial h3' (.step trivial h4' (.step trivial h5' (.nil _)))))
          have hlen : P.length = 5 := rfl
          rw [show 5 + k = P.length + k by rw [hlen]]
          exact P.runFuel k
      · have hbit4 : evalICmp .eq (q[1]?.getD 0).toBitVec (litByte lit 1) = 0 := by
          rw [stage2NoEventLitChain_evalICmp_eq_zero, litByte_eq_packByte]
          intro h; exact hc1 (UInt8.toBitVec_inj.mp h)
        rw [hbit4, ite_eq_right hne1] at h4
        let t4 : State := { t3 with pc := "if.then527", pre := some "if.end.i.1" }
        have h4' : step calls stage2NoEventBody (stateAt E3 t3) = .jump (stateAt E4 t4) := by
          simpa [t4, E4, hbit4] using h4
        refine ⟨stateAt E4 t4, 4, by omega, rfl, ?_, ?_⟩
        · left
          refine stage2NoEventLitChain_refuse_diff _ "if.end.i.1" 1 rfl rfl (by decide) ?_ ?_ ?_ ?_
          · rw [JsonEntrySteps.readBytes_length s.mem base 2 hq]; omega
          · rw [litBytes_length]; omega
          · intro j hj
            have hj0 : j = 0 := by omega
            subst hj0
            rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 0) (by omega)]
            simpa using hc0
          · intro h
            apply hc1
            rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 1) (by omega)] at h
            simpa using h
        · intro k
          let P : Path calls stage2NoEventBody (fun _ => True) (stateAt env s) (stateAt E4 t4) :=
            .step trivial h1' (.step trivial h2' (.step trivial h3' (.step trivial h4' (.nil _))))
          have hlen : P.length = 4 := rfl
          rw [show 4 + k = P.length + k by rw [hlen]]
          exact P.runFuel k
    · have hbit2 : evalICmp .eq (q[0]?.getD 0).toBitVec (litByte lit 0) = 0 := by
        rw [stage2NoEventLitChain_evalICmp_eq_zero, litByte_eq_packByte]
        intro h; exact hc0 (UInt8.toBitVec_inj.mp h)
      rw [hbit2, ite_eq_right hne1] at h2
      let t2 : State := { t1 with pc := "if.then527", pre := some "if.end.i" }
      have h2' : step calls stage2NoEventBody (stateAt E1 t1) = .jump (stateAt E2 t2) := by
        simpa [t2, E2, hbit2] using h2
      refine ⟨stateAt E2 t2, 2, by omega, rfl, ?_, ?_⟩
      · left
        refine stage2NoEventLitChain_refuse_diff _ "if.end.i" 0 rfl rfl (by decide) ?_ ?_ ?_ ?_
        · rw [JsonEntrySteps.readBytes_length s.mem base 2 hq]; omega
        · rw [litBytes_length]; omega
        · intro j hj; omega
        · intro h
          apply hc0
          rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 0) (by omega)] at h
          simpa using h
      · intro k
        let P : Path calls stage2NoEventBody (fun _ => True) (stateAt env s) (stateAt E2 t2) :=
          .step trivial h1' (.step trivial h2' (.nil _))
        have hlen : P.length = 2 := rfl
        rw [show 2 + k = P.length + k by rw [hlen]]
        exact P.runFuel k
  · -- n = 3
    have hb0 : readByte s.mem base = some (q[0]?.getD 0) := by
      simpa using readByte_of_readBytes hq (k := 0) (by omega)
    have hbit1 : evalICmp .eq (ee - idx) (BitVec.ofNat 64 0) = 0 := by
      rw [hsub]; decide
    rw [hbit1, ite_eq_right hne1] at h1
    let t1 : State := { s with pc := "if.end.i", pre := some "if.end519" }
    have h1' : step calls stage2NoEventBody (stateAt env s) = .jump (stateAt E1 t1) := by
      simpa [t1, E1, hbit1] using h1
    have h2 := stage2NoEventLitChain_step_if_end_i calls E1 t1
      (by rfl) (by dsimp only [E1]; lit_luk) (by dsimp only [E1]; lit_luk) (by simpa [t1] using hb0)
    by_cases hc0 : q[0]?.getD 0 = packByte lit 0
    · have hbit2 : evalICmp .eq (q[0]?.getD 0).toBitVec (litByte lit 0) = 1 := by
        rw [stage2NoEventLitChain_evalICmp_eq_one, litByte_eq_packByte, hc0]
      rw [hbit2, ite_eq_left rfl] at h2
      let t2 : State := { t1 with pc := "for.body.i.1", pre := some "if.end.i" }
      have h2' : step calls stage2NoEventBody (stateAt E1 t1) = .jump (stateAt E2 t2) := by
        simpa [t2, E2, hbit2] using h2
      have h3 := stage2NoEventLitChain_step_for_body_i_1 calls E2 t2
        (by rfl) (by dsimp only [E2, E1]; lit_luk)
      have hbit3 : evalICmp .eq (ee - idx) (BitVec.ofNat 64 1) = 0 := by
        rw [hsub]; decide
      rw [hbit3, ite_eq_right hne1] at h3
      let t3 : State := { t2 with pc := "if.end.i.1", pre := some "for.body.i.1" }
      have h3' : step calls stage2NoEventBody (stateAt E2 t2) = .jump (stateAt E3 t3) := by
        simpa [t3, E3, hbit3] using h3
      have hb1 : readByte s.mem (base + 1) = some (q[1]?.getD 0) := by
        simpa using readByte_of_readBytes hq (k := 1) (by omega)
      have h4 := stage2NoEventLitChain_step_if_end_i_1 calls E3 t3
        (by rfl) (by dsimp only [E3, E2, E1]; lit_luk)
        (by dsimp only [E3, E2, E1]; lit_luk) (by simpa [t3] using hb1)
      by_cases hc1 : q[1]?.getD 0 = packByte lit 1
      · have hbit4 : evalICmp .eq (q[1]?.getD 0).toBitVec (litByte lit 1) = 1 := by
          rw [stage2NoEventLitChain_evalICmp_eq_one, litByte_eq_packByte, hc1]
        rw [hbit4, ite_eq_left rfl] at h4
        let t4 : State := { t3 with pc := "for.body.i.2", pre := some "if.end.i.1" }
        have h4' : step calls stage2NoEventBody (stateAt E3 t3) = .jump (stateAt E4 t4) := by
          simpa [t4, E4, hbit4] using h4
        have h5 := stage2NoEventLitChain_step_for_body_i_2 calls E4 t4
          (by rfl) (by dsimp only [E4, E3, E2, E1]; lit_luk)
        have hbit5 : evalICmp .eq (ee - idx) (BitVec.ofNat 64 2) = 0 := by
          rw [hsub]; decide
        rw [hbit5, ite_eq_right hne1] at h5
        let t5 : State := { t4 with pc := "if.end.i.2", pre := some "for.body.i.2" }
        have h5' : step calls stage2NoEventBody (stateAt E4 t4) = .jump (stateAt E5 t5) := by
          simpa [t5, E5, hbit5] using h5
        have hb2 : readByte s.mem (base + 2) = some (q[2]?.getD 0) := by
          simpa using readByte_of_readBytes hq (k := 2) (by omega)
        have h6 := stage2NoEventLitChain_step_if_end_i_2 calls E5 t5
          (by rfl) (by dsimp only [E5, E4, E3, E2, E1]; lit_luk)
          (by dsimp only [E5, E4, E3, E2, E1]; lit_luk) (by simpa [t5] using hb2)
        by_cases hc2 : q[2]?.getD 0 = packByte lit 2
        · have hbit6 : evalICmp .eq (q[2]?.getD 0).toBitVec (litByte lit 2) = 1 := by
            rw [stage2NoEventLitChain_evalICmp_eq_one, litByte_eq_packByte, hc2]
          rw [hbit6, ite_eq_left rfl] at h6
          let t6 : State := { t5 with pc := "for.body.i.3", pre := some "if.end.i.2" }
          have h6' : step calls stage2NoEventBody (stateAt E5 t5) = .jump (stateAt E6 t6) := by
            simpa [t6, E6, hbit6] using h6
          have h7 := stage2NoEventLitChain_step_for_body_i_3 calls E6 t6
            (by rfl) (by dsimp only [E6, E5, E4, E3, E2, E1]; lit_luk)
          have hbit7 : evalICmp .eq (ee - idx) (BitVec.ofNat 64 3) = 1 := by
            rw [hsub]; decide
          rw [hbit7, ite_eq_left rfl] at h7
          let t7 : State := { t6 with pc := "if.then527", pre := some "for.body.i.3" }
          have h7' : step calls stage2NoEventBody (stateAt E6 t6) = .jump (stateAt E7 t7) := by
            simpa [t7, E7, hbit7] using h7
          refine ⟨stateAt E7 t7, 7, by omega, rfl, ?_, ?_⟩
          · left
            have hv : evalOperand (stateAt E7 t7) (.reg "%sub524") =
                some (.int 64 (BitVec.ofNat 64 3)) := by
              simp only [stateAt, evalOperand]
              repeat rw [lookupName_cons_ne _ _ (by decide)]
              rw [lookupName_cons_self, hsub]
            refine stage2NoEventLitChain_refuse_short _ "for.body.i.3" 3 rfl rfl (by decide) hv
              (by decide) (JsonEntrySteps.readBytes_length s.mem base 3 hq) ?_ ?_
            · rw [litBytes_length]; omega
            · intro j hj
              have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
              rcases hj' with rfl | rfl | rfl
              · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 0) (by omega)]
                simpa using hc0
              · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 1) (by omega)]
                simpa using hc1
              · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 2) (by omega)]
                simpa using hc2
          · intro k
            let P : Path calls stage2NoEventBody (fun _ => True) (stateAt env s) (stateAt E7 t7) :=
              .step trivial h1' (.step trivial h2' (.step trivial h3' (.step trivial h4' (.step trivial h5' (.step trivial h6' (.step trivial h7' (.nil _)))))))
            have hlen : P.length = 7 := rfl
            rw [show 7 + k = P.length + k by rw [hlen]]
            exact P.runFuel k
        · have hbit6 : evalICmp .eq (q[2]?.getD 0).toBitVec (litByte lit 2) = 0 := by
            rw [stage2NoEventLitChain_evalICmp_eq_zero, litByte_eq_packByte]
            intro h; exact hc2 (UInt8.toBitVec_inj.mp h)
          rw [hbit6, ite_eq_right hne1] at h6
          let t6 : State := { t5 with pc := "if.then527", pre := some "if.end.i.2" }
          have h6' : step calls stage2NoEventBody (stateAt E5 t5) = .jump (stateAt E6 t6) := by
            simpa [t6, E6, hbit6] using h6
          refine ⟨stateAt E6 t6, 6, by omega, rfl, ?_, ?_⟩
          · left
            refine stage2NoEventLitChain_refuse_diff _ "if.end.i.2" 2 rfl rfl (by decide) ?_ ?_ ?_ ?_
            · rw [JsonEntrySteps.readBytes_length s.mem base 3 hq]; omega
            · rw [litBytes_length]; omega
            · intro j hj
              have hj' : j = 0 ∨ j = 1 := by omega
              rcases hj' with rfl | rfl
              · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 0) (by omega)]
                simpa using hc0
              · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 1) (by omega)]
                simpa using hc1
            · intro h
              apply hc2
              rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 2) (by omega)] at h
              simpa using h
          · intro k
            let P : Path calls stage2NoEventBody (fun _ => True) (stateAt env s) (stateAt E6 t6) :=
              .step trivial h1' (.step trivial h2' (.step trivial h3' (.step trivial h4' (.step trivial h5' (.step trivial h6' (.nil _))))))
            have hlen : P.length = 6 := rfl
            rw [show 6 + k = P.length + k by rw [hlen]]
            exact P.runFuel k
      · have hbit4 : evalICmp .eq (q[1]?.getD 0).toBitVec (litByte lit 1) = 0 := by
          rw [stage2NoEventLitChain_evalICmp_eq_zero, litByte_eq_packByte]
          intro h; exact hc1 (UInt8.toBitVec_inj.mp h)
        rw [hbit4, ite_eq_right hne1] at h4
        let t4 : State := { t3 with pc := "if.then527", pre := some "if.end.i.1" }
        have h4' : step calls stage2NoEventBody (stateAt E3 t3) = .jump (stateAt E4 t4) := by
          simpa [t4, E4, hbit4] using h4
        refine ⟨stateAt E4 t4, 4, by omega, rfl, ?_, ?_⟩
        · left
          refine stage2NoEventLitChain_refuse_diff _ "if.end.i.1" 1 rfl rfl (by decide) ?_ ?_ ?_ ?_
          · rw [JsonEntrySteps.readBytes_length s.mem base 3 hq]; omega
          · rw [litBytes_length]; omega
          · intro j hj
            have hj0 : j = 0 := by omega
            subst hj0
            rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 0) (by omega)]
            simpa using hc0
          · intro h
            apply hc1
            rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 1) (by omega)] at h
            simpa using h
        · intro k
          let P : Path calls stage2NoEventBody (fun _ => True) (stateAt env s) (stateAt E4 t4) :=
            .step trivial h1' (.step trivial h2' (.step trivial h3' (.step trivial h4' (.nil _))))
          have hlen : P.length = 4 := rfl
          rw [show 4 + k = P.length + k by rw [hlen]]
          exact P.runFuel k
    · have hbit2 : evalICmp .eq (q[0]?.getD 0).toBitVec (litByte lit 0) = 0 := by
        rw [stage2NoEventLitChain_evalICmp_eq_zero, litByte_eq_packByte]
        intro h; exact hc0 (UInt8.toBitVec_inj.mp h)
      rw [hbit2, ite_eq_right hne1] at h2
      let t2 : State := { t1 with pc := "if.then527", pre := some "if.end.i" }
      have h2' : step calls stage2NoEventBody (stateAt E1 t1) = .jump (stateAt E2 t2) := by
        simpa [t2, E2, hbit2] using h2
      refine ⟨stateAt E2 t2, 2, by omega, rfl, ?_, ?_⟩
      · left
        refine stage2NoEventLitChain_refuse_diff _ "if.end.i" 0 rfl rfl (by decide) ?_ ?_ ?_ ?_
        · rw [JsonEntrySteps.readBytes_length s.mem base 3 hq]; omega
        · rw [litBytes_length]; omega
        · intro j hj; omega
        · intro h
          apply hc0
          rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 0) (by omega)] at h
          simpa using h
      · intro k
        let P : Path calls stage2NoEventBody (fun _ => True) (stateAt env s) (stateAt E2 t2) :=
          .step trivial h1' (.step trivial h2' (.nil _))
        have hlen : P.length = 2 := rfl
        rw [show 2 + k = P.length + k by rw [hlen]]
        exact P.runFuel k
  · -- n = 4
    have hb0 : readByte s.mem base = some (q[0]?.getD 0) := by
      simpa using readByte_of_readBytes hq (k := 0) (by omega)
    have hbit1 : evalICmp .eq (ee - idx) (BitVec.ofNat 64 0) = 0 := by
      rw [hsub]; decide
    rw [hbit1, ite_eq_right hne1] at h1
    let t1 : State := { s with pc := "if.end.i", pre := some "if.end519" }
    have h1' : step calls stage2NoEventBody (stateAt env s) = .jump (stateAt E1 t1) := by
      simpa [t1, E1, hbit1] using h1
    have h2 := stage2NoEventLitChain_step_if_end_i calls E1 t1
      (by rfl) (by dsimp only [E1]; lit_luk) (by dsimp only [E1]; lit_luk) (by simpa [t1] using hb0)
    by_cases hc0 : q[0]?.getD 0 = packByte lit 0
    · have hbit2 : evalICmp .eq (q[0]?.getD 0).toBitVec (litByte lit 0) = 1 := by
        rw [stage2NoEventLitChain_evalICmp_eq_one, litByte_eq_packByte, hc0]
      rw [hbit2, ite_eq_left rfl] at h2
      let t2 : State := { t1 with pc := "for.body.i.1", pre := some "if.end.i" }
      have h2' : step calls stage2NoEventBody (stateAt E1 t1) = .jump (stateAt E2 t2) := by
        simpa [t2, E2, hbit2] using h2
      have h3 := stage2NoEventLitChain_step_for_body_i_1 calls E2 t2
        (by rfl) (by dsimp only [E2, E1]; lit_luk)
      have hbit3 : evalICmp .eq (ee - idx) (BitVec.ofNat 64 1) = 0 := by
        rw [hsub]; decide
      rw [hbit3, ite_eq_right hne1] at h3
      let t3 : State := { t2 with pc := "if.end.i.1", pre := some "for.body.i.1" }
      have h3' : step calls stage2NoEventBody (stateAt E2 t2) = .jump (stateAt E3 t3) := by
        simpa [t3, E3, hbit3] using h3
      have hb1 : readByte s.mem (base + 1) = some (q[1]?.getD 0) := by
        simpa using readByte_of_readBytes hq (k := 1) (by omega)
      have h4 := stage2NoEventLitChain_step_if_end_i_1 calls E3 t3
        (by rfl) (by dsimp only [E3, E2, E1]; lit_luk)
        (by dsimp only [E3, E2, E1]; lit_luk) (by simpa [t3] using hb1)
      by_cases hc1 : q[1]?.getD 0 = packByte lit 1
      · have hbit4 : evalICmp .eq (q[1]?.getD 0).toBitVec (litByte lit 1) = 1 := by
          rw [stage2NoEventLitChain_evalICmp_eq_one, litByte_eq_packByte, hc1]
        rw [hbit4, ite_eq_left rfl] at h4
        let t4 : State := { t3 with pc := "for.body.i.2", pre := some "if.end.i.1" }
        have h4' : step calls stage2NoEventBody (stateAt E3 t3) = .jump (stateAt E4 t4) := by
          simpa [t4, E4, hbit4] using h4
        have h5 := stage2NoEventLitChain_step_for_body_i_2 calls E4 t4
          (by rfl) (by dsimp only [E4, E3, E2, E1]; lit_luk)
        have hbit5 : evalICmp .eq (ee - idx) (BitVec.ofNat 64 2) = 0 := by
          rw [hsub]; decide
        rw [hbit5, ite_eq_right hne1] at h5
        let t5 : State := { t4 with pc := "if.end.i.2", pre := some "for.body.i.2" }
        have h5' : step calls stage2NoEventBody (stateAt E4 t4) = .jump (stateAt E5 t5) := by
          simpa [t5, E5, hbit5] using h5
        have hb2 : readByte s.mem (base + 2) = some (q[2]?.getD 0) := by
          simpa using readByte_of_readBytes hq (k := 2) (by omega)
        have h6 := stage2NoEventLitChain_step_if_end_i_2 calls E5 t5
          (by rfl) (by dsimp only [E5, E4, E3, E2, E1]; lit_luk)
          (by dsimp only [E5, E4, E3, E2, E1]; lit_luk) (by simpa [t5] using hb2)
        by_cases hc2 : q[2]?.getD 0 = packByte lit 2
        · have hbit6 : evalICmp .eq (q[2]?.getD 0).toBitVec (litByte lit 2) = 1 := by
            rw [stage2NoEventLitChain_evalICmp_eq_one, litByte_eq_packByte, hc2]
          rw [hbit6, ite_eq_left rfl] at h6
          let t6 : State := { t5 with pc := "for.body.i.3", pre := some "if.end.i.2" }
          have h6' : step calls stage2NoEventBody (stateAt E5 t5) = .jump (stateAt E6 t6) := by
            simpa [t6, E6, hbit6] using h6
          have h7 := stage2NoEventLitChain_step_for_body_i_3 calls E6 t6
            (by rfl) (by dsimp only [E6, E5, E4, E3, E2, E1]; lit_luk)
          have hbit7 : evalICmp .eq (ee - idx) (BitVec.ofNat 64 3) = 0 := by
            rw [hsub]; decide
          rw [hbit7, ite_eq_right hne1] at h7
          let t7 : State := { t6 with pc := "if.end.i.3", pre := some "for.body.i.3" }
          have h7' : step calls stage2NoEventBody (stateAt E6 t6) = .jump (stateAt E7 t7) := by
            simpa [t7, E7, hbit7] using h7
          have hb3 : readByte s.mem (base + 3) = some (q[3]?.getD 0) := by
            simpa using readByte_of_readBytes hq (k := 3) (by omega)
          have h8 := stage2NoEventLitChain_step_if_end_i_3 calls E7 t7
            (by rfl) (by dsimp only [E7, E6, E5, E4, E3, E2, E1]; lit_luk)
            (by dsimp only [E7, E6, E5, E4, E3, E2, E1]; lit_luk) (by simpa [t7] using hb3)
          by_cases hc3 : q[3]?.getD 0 = packByte lit 3
          · have hbit8 : evalICmp .eq (q[3]?.getD 0).toBitVec (litByte lit 3) = 1 := by
              rw [stage2NoEventLitChain_evalICmp_eq_one, litByte_eq_packByte, hc3]
            rw [hbit8, ite_eq_left rfl] at h8
            let t8 : State := { t7 with pc := "for.cond.i.3", pre := some "if.end.i.3" }
            have h8' : step calls stage2NoEventBody (stateAt E7 t7) = .jump (stateAt E8 t8) := by
              simpa [t8, E8, hbit8] using h8
            have h9 := stage2NoEventLitChain_step_for_cond_i_3 calls E8 t8
              (by rfl) (by dsimp only [E8, E7, E6, E5, E4, E3, E2, E1]; lit_luk)
            rcases hwidth with ⟨hln4, hb4⟩ | ⟨hln5, hb5⟩
            · rw [hb4, ite_eq_left rfl] at h9
              let t9 : State := { t8 with pc := "for.end.i", pre := some "for.cond.i.3" }
              have h9' : step calls stage2NoEventBody (stateAt E8 t8) = .jump (stateAt E8 t9) := by
                simpa [t9] using h9
              have h10 := stage2NoEventLitChain_step_for_end_i calls E8 t9
                (by rfl) (by dsimp only [E8, E7, E6, E5, E4, E3, E2, E1]; lit_luk)
                (by dsimp only [E8, E7, E6, E5, E4, E3, E2, E1]; lit_luk)
              rw [hsub, hln4] at h10
              have hbit10 : evalICmp .eq (BitVec.ofNat 64 4) (BitVec.ofNat 64 4) = 1 := by decide
              rw [hbit10, ite_eq_left rfl] at h10
              let t10 : State := { t9 with pc := "if.end545", pre := some "for.end.i" }
              have h10' : step calls stage2NoEventBody (stateAt E8 t9) = .jump (stateAt E10 t10) := by
                simpa [t10, E10, hbit10, hsub, hln4] using h10
              refine ⟨stateAt E10 t10, 10, by omega, rfl, ?_, ?_⟩
              · right
                have hlen4 : q.length = 4 := JsonEntrySteps.readBytes_length s.mem base 4 hq
                refine stage2NoEventLitChain_accept_exit _ rfl ?_ ?_
                · rw [hlen4, litBytes_length, hln4]
                  rfl
                · intro j hj
                  rw [hlen4] at hj
                  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
                  rcases hj' with rfl | rfl | rfl | rfl
                  · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 0) (by omega)]
                    simpa using hc0
                  · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 1) (by omega)]
                    simpa using hc1
                  · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 2) (by omega)]
                    simpa using hc2
                  · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 3) (by omega)]
                    simpa using hc3
              · intro k
                let P : Path calls stage2NoEventBody (fun _ => True) (stateAt env s) (stateAt E10 t10) :=
                  .step trivial h1' (.step trivial h2' (.step trivial h3' (.step trivial h4' (.step trivial h5' (.step trivial h6' (.step trivial h7' (.step trivial h8' (.step trivial h9' (.step trivial h10' (.nil _))))))))))
                have hlen : P.length = 10 := rfl
                rw [show 10 + k = P.length + k by rw [hlen]]
                exact P.runFuel k
            · have hne0 : (0 : BitVec 1) ≠ 1 := by decide
              rw [hb5, ite_eq_right hne0] at h9
              let t9 : State := { t8 with pc := "for.body.i.4", pre := some "for.cond.i.3" }
              have h9' : step calls stage2NoEventBody (stateAt E8 t8) = .jump (stateAt E8 t9) := by
                simpa [t9] using h9
              have h10 := stage2NoEventLitChain_step_for_body_i_4 calls E8 t9
                (by rfl) (by dsimp only [E8, E7, E6, E5, E4, E3, E2, E1]; lit_luk)
              rw [hsub] at h10
              have hbit10 : evalICmp .eq (BitVec.ofNat 64 4) (BitVec.ofNat 64 4) = 1 := by decide
              rw [hbit10, ite_eq_left rfl] at h10
              let t10 : State := { t9 with pc := "if.then527", pre := some "for.body.i.4" }
              have h10' : step calls stage2NoEventBody (stateAt E8 t9) = .jump (stateAt E10b t10) := by
                simpa [t10, E10b, hbit10, hsub] using h10
              refine ⟨stateAt E10b t10, 10, by omega, rfl, ?_, ?_⟩
              · left
                have hv : evalOperand (stateAt E10b t10) (.reg "%sub524") =
                    some (.int 64 (BitVec.ofNat 64 4)) := by
                  simp only [stateAt, evalOperand]
                  repeat rw [lookupName_cons_ne _ _ (by decide)]
                  rw [lookupName_cons_self, hsub]
                refine stage2NoEventLitChain_refuse_short _ "for.body.i.4" 4 rfl rfl (by decide) hv
                  (by decide) (JsonEntrySteps.readBytes_length s.mem base 4 hq) ?_ ?_
                · rw [litBytes_length, hln5]; decide
                · intro j hj
                  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
                  rcases hj' with rfl | rfl | rfl | rfl
                  · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 0) (by omega)]
                    simpa using hc0
                  · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 1) (by omega)]
                    simpa using hc1
                  · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 2) (by omega)]
                    simpa using hc2
                  · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 3) (by omega)]
                    simpa using hc3
              · intro k
                let P : Path calls stage2NoEventBody (fun _ => True) (stateAt env s) (stateAt E10b t10) :=
                  .step trivial h1' (.step trivial h2' (.step trivial h3' (.step trivial h4' (.step trivial h5' (.step trivial h6' (.step trivial h7' (.step trivial h8' (.step trivial h9' (.step trivial h10' (.nil _))))))))))
                have hlen : P.length = 10 := rfl
                rw [show 10 + k = P.length + k by rw [hlen]]
                exact P.runFuel k
          · have hbit8 : evalICmp .eq (q[3]?.getD 0).toBitVec (litByte lit 3) = 0 := by
              rw [stage2NoEventLitChain_evalICmp_eq_zero, litByte_eq_packByte]
              intro h; exact hc3 (UInt8.toBitVec_inj.mp h)
            rw [hbit8, ite_eq_right hne1] at h8
            let t8 : State := { t7 with pc := "if.then527", pre := some "if.end.i.3" }
            have h8' : step calls stage2NoEventBody (stateAt E7 t7) = .jump (stateAt E8 t8) := by
              simpa [t8, E8, hbit8] using h8
            refine ⟨stateAt E8 t8, 8, by omega, rfl, ?_, ?_⟩
            · left
              refine stage2NoEventLitChain_refuse_diff _ "if.end.i.3" 3 rfl rfl (by decide) ?_ ?_ ?_ ?_
              · rw [JsonEntrySteps.readBytes_length s.mem base 4 hq]; omega
              · rw [litBytes_length]; omega
              · intro j hj
                have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
                rcases hj' with rfl | rfl | rfl
                · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 0) (by omega)]
                  simpa using hc0
                · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 1) (by omega)]
                  simpa using hc1
                · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 2) (by omega)]
                  simpa using hc2
              · intro h
                apply hc3
                rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 3) (by omega)] at h
                simpa using h
            · intro k
              let P : Path calls stage2NoEventBody (fun _ => True) (stateAt env s) (stateAt E8 t8) :=
                .step trivial h1' (.step trivial h2' (.step trivial h3' (.step trivial h4' (.step trivial h5' (.step trivial h6' (.step trivial h7' (.step trivial h8' (.nil _))))))))
              have hlen : P.length = 8 := rfl
              rw [show 8 + k = P.length + k by rw [hlen]]
              exact P.runFuel k
        · have hbit6 : evalICmp .eq (q[2]?.getD 0).toBitVec (litByte lit 2) = 0 := by
            rw [stage2NoEventLitChain_evalICmp_eq_zero, litByte_eq_packByte]
            intro h; exact hc2 (UInt8.toBitVec_inj.mp h)
          rw [hbit6, ite_eq_right hne1] at h6
          let t6 : State := { t5 with pc := "if.then527", pre := some "if.end.i.2" }
          have h6' : step calls stage2NoEventBody (stateAt E5 t5) = .jump (stateAt E6 t6) := by
            simpa [t6, E6, hbit6] using h6
          refine ⟨stateAt E6 t6, 6, by omega, rfl, ?_, ?_⟩
          · left
            refine stage2NoEventLitChain_refuse_diff _ "if.end.i.2" 2 rfl rfl (by decide) ?_ ?_ ?_ ?_
            · rw [JsonEntrySteps.readBytes_length s.mem base 4 hq]; omega
            · rw [litBytes_length]; omega
            · intro j hj
              have hj' : j = 0 ∨ j = 1 := by omega
              rcases hj' with rfl | rfl
              · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 0) (by omega)]
                simpa using hc0
              · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 1) (by omega)]
                simpa using hc1
            · intro h
              apply hc2
              rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 2) (by omega)] at h
              simpa using h
          · intro k
            let P : Path calls stage2NoEventBody (fun _ => True) (stateAt env s) (stateAt E6 t6) :=
              .step trivial h1' (.step trivial h2' (.step trivial h3' (.step trivial h4' (.step trivial h5' (.step trivial h6' (.nil _))))))
            have hlen : P.length = 6 := rfl
            rw [show 6 + k = P.length + k by rw [hlen]]
            exact P.runFuel k
      · have hbit4 : evalICmp .eq (q[1]?.getD 0).toBitVec (litByte lit 1) = 0 := by
          rw [stage2NoEventLitChain_evalICmp_eq_zero, litByte_eq_packByte]
          intro h; exact hc1 (UInt8.toBitVec_inj.mp h)
        rw [hbit4, ite_eq_right hne1] at h4
        let t4 : State := { t3 with pc := "if.then527", pre := some "if.end.i.1" }
        have h4' : step calls stage2NoEventBody (stateAt E3 t3) = .jump (stateAt E4 t4) := by
          simpa [t4, E4, hbit4] using h4
        refine ⟨stateAt E4 t4, 4, by omega, rfl, ?_, ?_⟩
        · left
          refine stage2NoEventLitChain_refuse_diff _ "if.end.i.1" 1 rfl rfl (by decide) ?_ ?_ ?_ ?_
          · rw [JsonEntrySteps.readBytes_length s.mem base 4 hq]; omega
          · rw [litBytes_length]; omega
          · intro j hj
            have hj0 : j = 0 := by omega
            subst hj0
            rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 0) (by omega)]
            simpa using hc0
          · intro h
            apply hc1
            rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 1) (by omega)] at h
            simpa using h
        · intro k
          let P : Path calls stage2NoEventBody (fun _ => True) (stateAt env s) (stateAt E4 t4) :=
            .step trivial h1' (.step trivial h2' (.step trivial h3' (.step trivial h4' (.nil _))))
          have hlen : P.length = 4 := rfl
          rw [show 4 + k = P.length + k by rw [hlen]]
          exact P.runFuel k
    · have hbit2 : evalICmp .eq (q[0]?.getD 0).toBitVec (litByte lit 0) = 0 := by
        rw [stage2NoEventLitChain_evalICmp_eq_zero, litByte_eq_packByte]
        intro h; exact hc0 (UInt8.toBitVec_inj.mp h)
      rw [hbit2, ite_eq_right hne1] at h2
      let t2 : State := { t1 with pc := "if.then527", pre := some "if.end.i" }
      have h2' : step calls stage2NoEventBody (stateAt E1 t1) = .jump (stateAt E2 t2) := by
        simpa [t2, E2, hbit2] using h2
      refine ⟨stateAt E2 t2, 2, by omega, rfl, ?_, ?_⟩
      · left
        refine stage2NoEventLitChain_refuse_diff _ "if.end.i" 0 rfl rfl (by decide) ?_ ?_ ?_ ?_
        · rw [JsonEntrySteps.readBytes_length s.mem base 4 hq]; omega
        · rw [litBytes_length]; omega
        · intro j hj; omega
        · intro h
          apply hc0
          rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 0) (by omega)] at h
          simpa using h
      · intro k
        let P : Path calls stage2NoEventBody (fun _ => True) (stateAt env s) (stateAt E2 t2) :=
          .step trivial h1' (.step trivial h2' (.nil _))
        have hlen : P.length = 2 := rfl
        rw [show 2 + k = P.length + k by rw [hlen]]
        exact P.runFuel k
  · -- n = n5 + 5, at least five
    have hb0 : readByte s.mem base = some (q[0]?.getD 0) := by
      simpa using readByte_of_readBytes hq (k := 0) (by omega)
    have hbit1 : evalICmp .eq (ee - idx) (BitVec.ofNat 64 0) = 0 := by
      rw [hsub]; exact stage2NoEventLitChain_evalICmp_ofNat_zero (by omega) (by decide) (by omega)
    rw [hbit1, ite_eq_right hne1] at h1
    let t1 : State := { s with pc := "if.end.i", pre := some "if.end519" }
    have h1' : step calls stage2NoEventBody (stateAt env s) = .jump (stateAt E1 t1) := by
      simpa [t1, E1, hbit1] using h1
    have h2 := stage2NoEventLitChain_step_if_end_i calls E1 t1
      (by rfl) (by dsimp only [E1]; lit_luk) (by dsimp only [E1]; lit_luk) (by simpa [t1] using hb0)
    by_cases hc0 : q[0]?.getD 0 = packByte lit 0
    · have hbit2 : evalICmp .eq (q[0]?.getD 0).toBitVec (litByte lit 0) = 1 := by
        rw [stage2NoEventLitChain_evalICmp_eq_one, litByte_eq_packByte, hc0]
      rw [hbit2, ite_eq_left rfl] at h2
      let t2 : State := { t1 with pc := "for.body.i.1", pre := some "if.end.i" }
      have h2' : step calls stage2NoEventBody (stateAt E1 t1) = .jump (stateAt E2 t2) := by
        simpa [t2, E2, hbit2] using h2
      have h3 := stage2NoEventLitChain_step_for_body_i_1 calls E2 t2
        (by rfl) (by dsimp only [E2, E1]; lit_luk)
      have hbit3 : evalICmp .eq (ee - idx) (BitVec.ofNat 64 1) = 0 := by
        rw [hsub]; exact stage2NoEventLitChain_evalICmp_ofNat_zero (by omega) (by decide) (by omega)
      rw [hbit3, ite_eq_right hne1] at h3
      let t3 : State := { t2 with pc := "if.end.i.1", pre := some "for.body.i.1" }
      have h3' : step calls stage2NoEventBody (stateAt E2 t2) = .jump (stateAt E3 t3) := by
        simpa [t3, E3, hbit3] using h3
      have hb1 : readByte s.mem (base + 1) = some (q[1]?.getD 0) := by
        simpa using readByte_of_readBytes hq (k := 1) (by omega)
      have h4 := stage2NoEventLitChain_step_if_end_i_1 calls E3 t3
        (by rfl) (by dsimp only [E3, E2, E1]; lit_luk)
        (by dsimp only [E3, E2, E1]; lit_luk) (by simpa [t3] using hb1)
      by_cases hc1 : q[1]?.getD 0 = packByte lit 1
      · have hbit4 : evalICmp .eq (q[1]?.getD 0).toBitVec (litByte lit 1) = 1 := by
          rw [stage2NoEventLitChain_evalICmp_eq_one, litByte_eq_packByte, hc1]
        rw [hbit4, ite_eq_left rfl] at h4
        let t4 : State := { t3 with pc := "for.body.i.2", pre := some "if.end.i.1" }
        have h4' : step calls stage2NoEventBody (stateAt E3 t3) = .jump (stateAt E4 t4) := by
          simpa [t4, E4, hbit4] using h4
        have h5 := stage2NoEventLitChain_step_for_body_i_2 calls E4 t4
          (by rfl) (by dsimp only [E4, E3, E2, E1]; lit_luk)
        have hbit5 : evalICmp .eq (ee - idx) (BitVec.ofNat 64 2) = 0 := by
          rw [hsub]; exact stage2NoEventLitChain_evalICmp_ofNat_zero (by omega) (by decide) (by omega)
        rw [hbit5, ite_eq_right hne1] at h5
        let t5 : State := { t4 with pc := "if.end.i.2", pre := some "for.body.i.2" }
        have h5' : step calls stage2NoEventBody (stateAt E4 t4) = .jump (stateAt E5 t5) := by
          simpa [t5, E5, hbit5] using h5
        have hb2 : readByte s.mem (base + 2) = some (q[2]?.getD 0) := by
          simpa using readByte_of_readBytes hq (k := 2) (by omega)
        have h6 := stage2NoEventLitChain_step_if_end_i_2 calls E5 t5
          (by rfl) (by dsimp only [E5, E4, E3, E2, E1]; lit_luk)
          (by dsimp only [E5, E4, E3, E2, E1]; lit_luk) (by simpa [t5] using hb2)
        by_cases hc2 : q[2]?.getD 0 = packByte lit 2
        · have hbit6 : evalICmp .eq (q[2]?.getD 0).toBitVec (litByte lit 2) = 1 := by
            rw [stage2NoEventLitChain_evalICmp_eq_one, litByte_eq_packByte, hc2]
          rw [hbit6, ite_eq_left rfl] at h6
          let t6 : State := { t5 with pc := "for.body.i.3", pre := some "if.end.i.2" }
          have h6' : step calls stage2NoEventBody (stateAt E5 t5) = .jump (stateAt E6 t6) := by
            simpa [t6, E6, hbit6] using h6
          have h7 := stage2NoEventLitChain_step_for_body_i_3 calls E6 t6
            (by rfl) (by dsimp only [E6, E5, E4, E3, E2, E1]; lit_luk)
          have hbit7 : evalICmp .eq (ee - idx) (BitVec.ofNat 64 3) = 0 := by
            rw [hsub]; exact stage2NoEventLitChain_evalICmp_ofNat_zero (by omega) (by decide) (by omega)
          rw [hbit7, ite_eq_right hne1] at h7
          let t7 : State := { t6 with pc := "if.end.i.3", pre := some "for.body.i.3" }
          have h7' : step calls stage2NoEventBody (stateAt E6 t6) = .jump (stateAt E7 t7) := by
            simpa [t7, E7, hbit7] using h7
          have hb3 : readByte s.mem (base + 3) = some (q[3]?.getD 0) := by
            simpa using readByte_of_readBytes hq (k := 3) (by omega)
          have h8 := stage2NoEventLitChain_step_if_end_i_3 calls E7 t7
            (by rfl) (by dsimp only [E7, E6, E5, E4, E3, E2, E1]; lit_luk)
            (by dsimp only [E7, E6, E5, E4, E3, E2, E1]; lit_luk) (by simpa [t7] using hb3)
          by_cases hc3 : q[3]?.getD 0 = packByte lit 3
          · have hbit8 : evalICmp .eq (q[3]?.getD 0).toBitVec (litByte lit 3) = 1 := by
              rw [stage2NoEventLitChain_evalICmp_eq_one, litByte_eq_packByte, hc3]
            rw [hbit8, ite_eq_left rfl] at h8
            let t8 : State := { t7 with pc := "for.cond.i.3", pre := some "if.end.i.3" }
            have h8' : step calls stage2NoEventBody (stateAt E7 t7) = .jump (stateAt E8 t8) := by
              simpa [t8, E8, hbit8] using h8
            have h9 := stage2NoEventLitChain_step_for_cond_i_3 calls E8 t8
              (by rfl) (by dsimp only [E8, E7, E6, E5, E4, E3, E2, E1]; lit_luk)
            rcases hwidth with ⟨hln4, hb4⟩ | ⟨hln5, hb5⟩
            · rw [hb4, ite_eq_left rfl] at h9
              let t9 : State := { t8 with pc := "for.end.i", pre := some "for.cond.i.3" }
              have h9' : step calls stage2NoEventBody (stateAt E8 t8) = .jump (stateAt E8 t9) := by
                simpa [t9] using h9
              have h10 := stage2NoEventLitChain_step_for_end_i calls E8 t9
                (by rfl) (by dsimp only [E8, E7, E6, E5, E4, E3, E2, E1]; lit_luk)
                (by dsimp only [E8, E7, E6, E5, E4, E3, E2, E1]; lit_luk)
              rw [hsub, hln4] at h10
              have hbit10 : evalICmp .eq (BitVec.ofNat 64 (n5 + 5)) (BitVec.ofNat 64 4) = 0 :=
                stage2NoEventLitChain_evalICmp_ofNat_zero (by omega) (by decide) (by omega)
              rw [hbit10, ite_eq_right hne1] at h10
              let t10 : State := { t9 with pc := "if.then527", pre := some "for.end.i" }
              have h10' : step calls stage2NoEventBody (stateAt E8 t9) = .jump (stateAt E10 t10) := by
                simpa [t10, E10, hbit10, hsub, hln4] using h10
              have hqlen : 4 < q.length := by
                rw [JsonEntrySteps.readBytes_length s.mem base (n5 + 5) hq]; omega
              refine ⟨stateAt E10 t10, 10, by omega, rfl, ?_, ?_⟩
              · left
                have hv : evalOperand (stateAt E10 t10) (.reg "%ln.0") = some (.int 64 ln) := by
                  simp only [stateAt, evalOperand]
                  repeat rw [lookupName_cons_ne _ _ (by decide)]
                  rw [lookupName_cons_self]
                refine stage2NoEventLitChain_refuse_long _ "for.end.i" rfl rfl (by decide) hv ?_ ?_ ?_
                · rw [litBytes_length]
                · rw [litBytes_length, hln4]
                  rw [show (BitVec.ofNat 64 4).toNat = 4 from by decide]
                  rw [JsonEntrySteps.readBytes_length s.mem base (n5 + 5) hq]
                  omega
                · intro j hj
                  simp [litBytes_length, hln4] at hj
                  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
                  rcases hj' with rfl | rfl | rfl | rfl
                  · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 0) (by omega)]
                    simpa using hc0
                  · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 1) (by omega)]
                    simpa using hc1
                  · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 2) (by omega)]
                    simpa using hc2
                  · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 3) (by omega)]
                    simpa using hc3
              · intro k
                let P : Path calls stage2NoEventBody (fun _ => True) (stateAt env s) (stateAt E10 t10) :=
                  .step trivial h1' (.step trivial h2' (.step trivial h3' (.step trivial h4' (.step trivial h5' (.step trivial h6' (.step trivial h7' (.step trivial h8' (.step trivial h9' (.step trivial h10' (.nil _))))))))))
                have hlen : P.length = 10 := rfl
                rw [show 10 + k = P.length + k by rw [hlen]]
                exact P.runFuel k
            · have hne0 : (0 : BitVec 1) ≠ 1 := by decide
              rw [hb5, ite_eq_right hne0] at h9
              let t9 : State := { t8 with pc := "for.body.i.4", pre := some "for.cond.i.3" }
              have h9' : step calls stage2NoEventBody (stateAt E8 t8) = .jump (stateAt E8 t9) := by
                simpa [t9] using h9
              have h10 := stage2NoEventLitChain_step_for_body_i_4 calls E8 t9
                (by rfl) (by dsimp only [E8, E7, E6, E5, E4, E3, E2, E1]; lit_luk)
              rw [hsub] at h10
              have hbit10 : evalICmp .eq (BitVec.ofNat 64 (n5 + 5)) (BitVec.ofNat 64 4) = 0 :=
                stage2NoEventLitChain_evalICmp_ofNat_zero (by omega) (by decide) (by omega)
              rw [hbit10, ite_eq_right hne1] at h10
              let t10 : State := { t9 with pc := "if.end.i.4", pre := some "for.body.i.4" }
              have h10' : step calls stage2NoEventBody (stateAt E8 t9) = .jump (stateAt E10b t10) := by
                simpa [t10, E10b, hbit10, hsub] using h10
              have hb4 : readByte s.mem (base + 4) = some (q[4]?.getD 0) := by
                simpa using readByte_of_readBytes hq (k := 4) (by omega)
              have h11 := stage2NoEventLitChain_step_if_end_i_4 calls E10b t10
                (by rfl) (by dsimp only [E10b, E8, E7, E6, E5, E4, E3, E2, E1]; lit_luk)
                (by dsimp only [E10b, E8, E7, E6, E5, E4, E3, E2, E1]; lit_luk)
                (by simpa [t10] using hb4)
              by_cases hc4 : q[4]?.getD 0 = packByte lit 4
              · have hbit11 : evalICmp .eq (q[4]?.getD 0).toBitVec (litByte lit 4) = 1 := by
                  rw [stage2NoEventLitChain_evalICmp_eq_one, litByte_eq_packByte, hc4]
                rw [hbit11, ite_eq_left rfl] at h11
                let t11 : State := { t10 with pc := "for.end.i", pre := some "if.end.i.4" }
                have h11' : step calls stage2NoEventBody (stateAt E10b t10) = .jump (stateAt E11 t11) := by
                  simpa [t11, E11, hbit11] using h11
                have h12 := stage2NoEventLitChain_step_for_end_i calls E11 t11
                  (by rfl) (by dsimp only [E11, E10b, E8, E7, E6, E5, E4, E3, E2, E1]; lit_luk)
                  (by dsimp only [E11, E10b, E8, E7, E6, E5, E4, E3, E2, E1]; lit_luk)
                by_cases hn5 : n5 = 0
                · subst hn5
                  rw [hsub, hln5] at h12
                  have hbit12 : evalICmp .eq (BitVec.ofNat 64 5) (BitVec.ofNat 64 5) = 1 := by decide
                  rw [hbit12, ite_eq_left rfl] at h12
                  let t12 : State := { t11 with pc := "if.end545", pre := some "for.end.i" }
                  have h12' : step calls stage2NoEventBody (stateAt E11 t11) = .jump (stateAt E12 t12) := by
                    simpa [t12, E12, hbit12, hsub, hln5] using h12
                  refine ⟨stateAt E12 t12, 12, by omega, rfl, ?_, ?_⟩
                  · right
                    have hlen5 : q.length = 5 := by
                      rw [JsonEntrySteps.readBytes_length s.mem base 5 hq]
                    refine stage2NoEventLitChain_accept_exit _ rfl ?_ ?_
                    · rw [hlen5, litBytes_length, hln5]; rfl
                    · intro j hj
                      rw [hlen5] at hj
                      have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
                      rcases hj' with rfl | rfl | rfl | rfl | rfl
                      · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 0) (by omega)]; simpa using hc0
                      · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 1) (by omega)]; simpa using hc1
                      · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 2) (by omega)]; simpa using hc2
                      · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 3) (by omega)]; simpa using hc3
                      · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 4) (by rw [hln5]; decide)]; simpa using hc4
                  · intro k
                    let P : Path calls stage2NoEventBody (fun _ => True) (stateAt env s) (stateAt E12 t12) :=
                      .step trivial h1' (.step trivial h2' (.step trivial h3' (.step trivial h4' (.step trivial h5' (.step trivial h6' (.step trivial h7' (.step trivial h8' (.step trivial h9' (.step trivial h10' (.step trivial h11' (.step trivial h12' (.nil _))))))))))))
                    have hlen : P.length = 12 := rfl
                    rw [show 12 + k = P.length + k by rw [hlen]]
                    exact P.runFuel k
                · rw [hsub, hln5] at h12
                  have hbit12 : evalICmp .eq (BitVec.ofNat 64 (n5 + 5)) (BitVec.ofNat 64 5) = 0 :=
                    stage2NoEventLitChain_evalICmp_ofNat_zero (by omega) (by decide) (by omega)
                  rw [hbit12, ite_eq_right hne1] at h12
                  let t12 : State := { t11 with pc := "if.then527", pre := some "for.end.i" }
                  have h12' : step calls stage2NoEventBody (stateAt E11 t11) = .jump (stateAt E12 t12) := by
                    simpa [t12, E12, hbit12, hsub, hln5] using h12
                  have hqlen : 5 < q.length := by
                    rw [JsonEntrySteps.readBytes_length s.mem base (n5 + 5) hq]; omega
                  refine ⟨stateAt E12 t12, 12, by omega, rfl, ?_, ?_⟩
                  · left
                    have hv : evalOperand (stateAt E12 t12) (.reg "%ln.0") = some (.int 64 ln) := by
                      simp only [stateAt, evalOperand]
                      repeat rw [lookupName_cons_ne _ _ (by decide)]
                      rw [lookupName_cons_self]
                    refine stage2NoEventLitChain_refuse_long _ "for.end.i" rfl rfl (by decide) hv ?_ ?_ ?_
                    · rw [litBytes_length]
                    · rw [litBytes_length, hln5]
                      rw [show (BitVec.ofNat 64 5).toNat = 5 from by decide]
                      rw [JsonEntrySteps.readBytes_length s.mem base (n5 + 5) hq]
                      omega
                    · intro j hj
                      rw [litBytes_length, hln5] at hj
                      have h5 : (BitVec.ofNat 64 5).toNat = 5 := by decide
                      rw [h5] at hj
                      have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
                      rcases hj' with rfl | rfl | rfl | rfl | rfl
                      · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 0) (by omega)]; simpa using hc0
                      · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 1) (by omega)]; simpa using hc1
                      · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 2) (by omega)]; simpa using hc2
                      · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 3) (by omega)]; simpa using hc3
                      · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 4) (by rw [hln5]; decide)]; simpa using hc4
                  · intro k
                    let P : Path calls stage2NoEventBody (fun _ => True) (stateAt env s) (stateAt E12 t12) :=
                      .step trivial h1' (.step trivial h2' (.step trivial h3' (.step trivial h4' (.step trivial h5' (.step trivial h6' (.step trivial h7' (.step trivial h8' (.step trivial h9' (.step trivial h10' (.step trivial h11' (.step trivial h12' (.nil _))))))))))))
                    have hlen : P.length = 12 := rfl
                    rw [show 12 + k = P.length + k by rw [hlen]]
                    exact P.runFuel k
              · have hbit11 : evalICmp .eq (q[4]?.getD 0).toBitVec (litByte lit 4) = 0 := by
                  rw [stage2NoEventLitChain_evalICmp_eq_zero, litByte_eq_packByte]
                  intro h; exact hc4 (UInt8.toBitVec_inj.mp h)
                rw [hbit11, ite_eq_right hne1] at h11
                let t11 : State := { t10 with pc := "if.then527", pre := some "if.end.i.4" }
                have h11' : step calls stage2NoEventBody (stateAt E10b t10) = .jump (stateAt E11 t11) := by
                  simpa [t11, E11, hbit11] using h11
                refine ⟨stateAt E11 t11, 11, by omega, rfl, ?_, ?_⟩
                · left
                  refine stage2NoEventLitChain_refuse_diff _ "if.end.i.4" 4 rfl rfl (by decide) ?_ ?_ ?_ ?_
                  · rw [JsonEntrySteps.readBytes_length s.mem base (n5 + 5) hq]; omega
                  · rw [litBytes_length, hln5]; decide
                  · intro j hj
                    have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
                    rcases hj' with rfl | rfl | rfl | rfl
                    · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 0) (by omega)]; simpa using hc0
                    · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 1) (by omega)]; simpa using hc1
                    · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 2) (by omega)]; simpa using hc2
                    · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 3) (by omega)]; simpa using hc3
                  · intro h
                    apply hc4
                    rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 4) (by rw [hln5]; decide)] at h
                    simpa using h
                · intro k
                  let P : Path calls stage2NoEventBody (fun _ => True) (stateAt env s) (stateAt E11 t11) :=
                    .step trivial h1' (.step trivial h2' (.step trivial h3' (.step trivial h4' (.step trivial h5' (.step trivial h6' (.step trivial h7' (.step trivial h8' (.step trivial h9' (.step trivial h10' (.step trivial h11' (.nil _)))))))))))
                  have hlen : P.length = 11 := rfl
                  rw [show 11 + k = P.length + k by rw [hlen]]
                  exact P.runFuel k
          · have hbit8 : evalICmp .eq (q[3]?.getD 0).toBitVec (litByte lit 3) = 0 := by
              rw [stage2NoEventLitChain_evalICmp_eq_zero, litByte_eq_packByte]
              intro h; exact hc3 (UInt8.toBitVec_inj.mp h)
            rw [hbit8, ite_eq_right hne1] at h8
            let t8 : State := { t7 with pc := "if.then527", pre := some "if.end.i.3" }
            have h8' : step calls stage2NoEventBody (stateAt E7 t7) = .jump (stateAt E8 t8) := by
              simpa [t8, E8, hbit8] using h8
            refine ⟨stateAt E8 t8, 8, by omega, rfl, ?_, ?_⟩
            · left
              refine stage2NoEventLitChain_refuse_diff _ "if.end.i.3" 3 rfl rfl (by decide) ?_ ?_ ?_ ?_
              · rw [JsonEntrySteps.readBytes_length s.mem base (n5 + 5) hq]; omega
              · rw [litBytes_length]; omega
              · intro j hj
                have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
                rcases hj' with rfl | rfl | rfl
                · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 0) (by omega)]; simpa using hc0
                · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 1) (by omega)]; simpa using hc1
                · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 2) (by omega)]; simpa using hc2
              · intro h
                apply hc3
                rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 3) (by omega)] at h
                simpa using h
            · intro k
              let P : Path calls stage2NoEventBody (fun _ => True) (stateAt env s) (stateAt E8 t8) :=
                .step trivial h1' (.step trivial h2' (.step trivial h3' (.step trivial h4' (.step trivial h5' (.step trivial h6' (.step trivial h7' (.step trivial h8' (.nil _))))))))
              have hlen : P.length = 8 := rfl
              rw [show 8 + k = P.length + k by rw [hlen]]
              exact P.runFuel k
        · have hbit6 : evalICmp .eq (q[2]?.getD 0).toBitVec (litByte lit 2) = 0 := by
            rw [stage2NoEventLitChain_evalICmp_eq_zero, litByte_eq_packByte]
            intro h; exact hc2 (UInt8.toBitVec_inj.mp h)
          rw [hbit6, ite_eq_right hne1] at h6
          let t6 : State := { t5 with pc := "if.then527", pre := some "if.end.i.2" }
          have h6' : step calls stage2NoEventBody (stateAt E5 t5) = .jump (stateAt E6 t6) := by
            simpa [t6, E6, hbit6] using h6
          refine ⟨stateAt E6 t6, 6, by omega, rfl, ?_, ?_⟩
          · left
            refine stage2NoEventLitChain_refuse_diff _ "if.end.i.2" 2 rfl rfl (by decide) ?_ ?_ ?_ ?_
            · rw [JsonEntrySteps.readBytes_length s.mem base (n5 + 5) hq]; omega
            · rw [litBytes_length]; omega
            · intro j hj
              have hj' : j = 0 ∨ j = 1 := by omega
              rcases hj' with rfl | rfl
              · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 0) (by omega)]; simpa using hc0
              · rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 1) (by omega)]; simpa using hc1
            · intro h
              apply hc2
              rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 2) (by omega)] at h
              simpa using h
          · intro k
            let P : Path calls stage2NoEventBody (fun _ => True) (stateAt env s) (stateAt E6 t6) :=
              .step trivial h1' (.step trivial h2' (.step trivial h3' (.step trivial h4' (.step trivial h5' (.step trivial h6' (.nil _))))))
            have hlen : P.length = 6 := rfl
            rw [show 6 + k = P.length + k by rw [hlen]]
            exact P.runFuel k
      · have hbit4 : evalICmp .eq (q[1]?.getD 0).toBitVec (litByte lit 1) = 0 := by
          rw [stage2NoEventLitChain_evalICmp_eq_zero, litByte_eq_packByte]
          intro h; exact hc1 (UInt8.toBitVec_inj.mp h)
        rw [hbit4, ite_eq_right hne1] at h4
        let t4 : State := { t3 with pc := "if.then527", pre := some "if.end.i.1" }
        have h4' : step calls stage2NoEventBody (stateAt E3 t3) = .jump (stateAt E4 t4) := by
          simpa [t4, E4, hbit4] using h4
        refine ⟨stateAt E4 t4, 4, by omega, rfl, ?_, ?_⟩
        · left
          refine stage2NoEventLitChain_refuse_diff _ "if.end.i.1" 1 rfl rfl (by decide) ?_ ?_ ?_ ?_
          · rw [JsonEntrySteps.readBytes_length s.mem base (n5 + 5) hq]; omega
          · rw [litBytes_length]; omega
          · intro j hj
            have hj0 : j = 0 := by omega
            subst hj0
            rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 0) (by omega)]; simpa using hc0
          · intro h
            apply hc1
            rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 1) (by omega)] at h
            simpa using h
        · intro k
          let P : Path calls stage2NoEventBody (fun _ => True) (stateAt env s) (stateAt E4 t4) :=
            .step trivial h1' (.step trivial h2' (.step trivial h3' (.step trivial h4' (.nil _))))
          have hlen : P.length = 4 := rfl
          rw [show 4 + k = P.length + k by rw [hlen]]
          exact P.runFuel k
    · have hbit2 : evalICmp .eq (q[0]?.getD 0).toBitVec (litByte lit 0) = 0 := by
        rw [stage2NoEventLitChain_evalICmp_eq_zero, litByte_eq_packByte]
        intro h; exact hc0 (UInt8.toBitVec_inj.mp h)
      rw [hbit2, ite_eq_right hne1] at h2
      let t2 : State := { t1 with pc := "if.then527", pre := some "if.end.i" }
      have h2' : step calls stage2NoEventBody (stateAt E1 t1) = .jump (stateAt E2 t2) := by
        simpa [t2, E2, hbit2] using h2
      refine ⟨stateAt E2 t2, 2, by omega, rfl, ?_, ?_⟩
      · left
        refine stage2NoEventLitChain_refuse_diff _ "if.end.i" 0 rfl rfl (by decide) ?_ ?_ ?_ ?_
        · rw [JsonEntrySteps.readBytes_length s.mem base (n5 + 5) hq]; omega
        · rw [litBytes_length]; omega
        · intro j hj; omega
        · intro h
          apply hc0
          rw [litBytes_getD (lit := lit) (ln := ln.toNat) (j := 0) (by omega)] at h
          simpa using h
      · intro k
        let P : Path calls stage2NoEventBody (fun _ => True) (stateAt env s) (stateAt E2 t2) :=
          .step trivial h1' (.step trivial h2' (.nil _))
        have hlen : P.length = 2 := rfl
        rw [show 2 + k = P.length + k by rw [hlen]]
        exact P.runFuel k





/-- **The refusal arm, under the rule's value.** -/
theorem stage2NoEventLitChain_refuse
    (calls : Calls) (env : Env) (s : State) (p : String)
    {base : Nat} {lit ln tag : BitVec 64} {b : BitVec 1} {ee idx : BitVec 64}
    {n : Nat} {q : List UInt8} {i : Nat}
    (hpc : s.pc = "if.end519")
    (hpre : s.pre = some p)
    (hincLit : phiIncoming p [("if.then504", (Operand.imm (.int 64 (BitVec.ofNat 64 435728179558)))), ("if.then509", (Operand.imm (.int 64 (BitVec.ofNat 64 1819047278)))), ("LeafBlock68", (Operand.imm (.int 64 (BitVec.ofNat 64 1702195828))))] = some (.imm (.int 64 lit)))
    (hincB : phiIncoming p [("if.then504", (Operand.imm (.int 1 (BitVec.ofNat 1 0)))), ("if.then509", (Operand.imm (.int 1 (BitVec.ofNat 1 1)))), ("LeafBlock68", (Operand.imm (.int 1 (BitVec.ofNat 1 1))))] = some (.imm (.int 1 b)))
    (hincLn : phiIncoming p [("if.then504", (Operand.imm (.int 64 (BitVec.ofNat 64 5)))), ("if.then509", (Operand.imm (.int 64 (BitVec.ofNat 64 4)))), ("LeafBlock68", (Operand.imm (.int 64 (BitVec.ofNat 64 4))))] = some (.imm (.int 64 ln)))
    (hincTag : phiIncoming p [("if.then504", (Operand.imm (.int 64 (BitVec.ofNat 64 9)))), ("if.then509", (Operand.imm (.int 64 (BitVec.ofNat 64 10)))), ("LeafBlock68", (Operand.imm (.int 64 (BitVec.ofNat 64 8))))] = some (.imm (.int 64 tag)))
    (hee : lookupName env "%ee.1" = some (.int 64 ee))
    (hidx : lookupName env "%idxprom.lcssa" = some (.int 64 idx))
    (hn : n < 2 ^ 64) (hsub : ee - idx = BitVec.ofNat 64 n)
    (harr : lookupName env "%arrayidx6.le1046" = some (.ptr base))
    (hq : readBytes s.mem base n = some q)
    (hwidth : (ln = BitVec.ofNat 64 4 ∧ b = 1) ∨ (ln = BitVec.ofNat 64 5 ∧ b = 0))
    (hval : neLitCheck q (litBytes lit ln.toNat) = some i) :
    ∃ (e : State) (j : Nat), j ≤ 13 ∧ e.mem = s.mem ∧ litRefusal e i ∧
      (∀ k, runFuel calls (j + k) stage2NoEventBody (stateAt env s) =
        runFuel calls k stage2NoEventBody e) := by
  obtain ⟨e, j, hj, hmem, hdisj, hfuel⟩ :=
    stage2NoEventLitChain_run calls env s p hpc hpre hincLit hincB hincLn hincTag
      hee hidx hn hsub harr hq hwidth
  rcases hdisj with ⟨i0, hre, hne⟩ | ⟨_, hnone⟩
  · rw [hval] at hne
    cases Option.some.inj hne
    exact ⟨e, j, hj, hmem, hre, hfuel⟩
  · rw [hval] at hnone; cases hnone

/-- **The accepting arm, under the rule's value.** -/
theorem stage2NoEventLitChain_accept
    (calls : Calls) (env : Env) (s : State) (p : String)
    {base : Nat} {lit ln tag : BitVec 64} {b : BitVec 1} {ee idx : BitVec 64}
    {n : Nat} {q : List UInt8}
    (hpc : s.pc = "if.end519")
    (hpre : s.pre = some p)
    (hincLit : phiIncoming p [("if.then504", (Operand.imm (.int 64 (BitVec.ofNat 64 435728179558)))), ("if.then509", (Operand.imm (.int 64 (BitVec.ofNat 64 1819047278)))), ("LeafBlock68", (Operand.imm (.int 64 (BitVec.ofNat 64 1702195828))))] = some (.imm (.int 64 lit)))
    (hincB : phiIncoming p [("if.then504", (Operand.imm (.int 1 (BitVec.ofNat 1 0)))), ("if.then509", (Operand.imm (.int 1 (BitVec.ofNat 1 1)))), ("LeafBlock68", (Operand.imm (.int 1 (BitVec.ofNat 1 1))))] = some (.imm (.int 1 b)))
    (hincLn : phiIncoming p [("if.then504", (Operand.imm (.int 64 (BitVec.ofNat 64 5)))), ("if.then509", (Operand.imm (.int 64 (BitVec.ofNat 64 4)))), ("LeafBlock68", (Operand.imm (.int 64 (BitVec.ofNat 64 4))))] = some (.imm (.int 64 ln)))
    (hincTag : phiIncoming p [("if.then504", (Operand.imm (.int 64 (BitVec.ofNat 64 9)))), ("if.then509", (Operand.imm (.int 64 (BitVec.ofNat 64 10)))), ("LeafBlock68", (Operand.imm (.int 64 (BitVec.ofNat 64 8))))] = some (.imm (.int 64 tag)))
    (hee : lookupName env "%ee.1" = some (.int 64 ee))
    (hidx : lookupName env "%idxprom.lcssa" = some (.int 64 idx))
    (hn : n < 2 ^ 64) (hsub : ee - idx = BitVec.ofNat 64 n)
    (harr : lookupName env "%arrayidx6.le1046" = some (.ptr base))
    (hq : readBytes s.mem base n = some q)
    (hwidth : (ln = BitVec.ofNat 64 4 ∧ b = 1) ∨ (ln = BitVec.ofNat 64 5 ∧ b = 0))
    (hval : neLitCheck q (litBytes lit ln.toNat) = none) :
    ∃ (e : State) (j : Nat), j ≤ 13 ∧ e.mem = s.mem ∧ litAccept e ∧
      (∀ k, runFuel calls (j + k) stage2NoEventBody (stateAt env s) =
        runFuel calls k stage2NoEventBody e) := by
  obtain ⟨e, j, hj, hmem, hdisj, hfuel⟩ :=
    stage2NoEventLitChain_run calls env s p hpc hpre hincLit hincB hincLn hincTag
      hee hidx hn hsub harr hq hwidth
  rcases hdisj with ⟨i0, _, hne⟩ | ⟨hacc, _⟩
  · rw [hval] at hne; cases hne
  · exact ⟨e, j, hj, hmem, hacc, hfuel⟩

/-- **`true`**: the shared `phi` at `LeafBlock68`, four bytes, selector one. -/
theorem stage2NoEventLitChain_true
    (calls : Calls) (env : Env) (s : State)
    {base : Nat} {ee idx : BitVec 64} {n : Nat} {q : List UInt8}
    (hpc : s.pc = "if.end519") (hpre : s.pre = some "LeafBlock68")
    (hee : lookupName env "%ee.1" = some (.int 64 ee))
    (hidx : lookupName env "%idxprom.lcssa" = some (.int 64 idx))
    (hn : n < 2 ^ 64) (hsub : ee - idx = BitVec.ofNat 64 n)
    (harr : lookupName env "%arrayidx6.le1046" = some (.ptr base))
    (hq : readBytes s.mem base n = some q) :
    ∃ (e : State) (j : Nat), j ≤ 13 ∧ e.mem = s.mem ∧
      ((∃ i, litRefusal e i ∧ neLitCheck q (litBytes neLitTrue 4) = some i) ∨
       (litAccept e ∧ neLitCheck q (litBytes neLitTrue 4) = none)) ∧
      (∀ k, runFuel calls (j + k) stage2NoEventBody (stateAt env s) =
        runFuel calls k stage2NoEventBody e) :=
  stage2NoEventLitChain_run calls env s "LeafBlock68"
    (lit := neLitTrue) (ln := BitVec.ofNat 64 4) (tag := BitVec.ofNat 64 8)
    (b := 1) hpc hpre (by decide) (by decide) (by decide) (by decide)
    hee hidx hn hsub harr hq (Or.inl ⟨rfl, rfl⟩)

/-- **`false`**: five bytes at `if.then504`. -/
theorem stage2NoEventLitChain_false
    (calls : Calls) (env : Env) (s : State)
    {base : Nat} {ee idx : BitVec 64} {n : Nat} {q : List UInt8}
    (hpc : s.pc = "if.end519") (hpre : s.pre = some "if.then504")
    (hee : lookupName env "%ee.1" = some (.int 64 ee))
    (hidx : lookupName env "%idxprom.lcssa" = some (.int 64 idx))
    (hn : n < 2 ^ 64) (hsub : ee - idx = BitVec.ofNat 64 n)
    (harr : lookupName env "%arrayidx6.le1046" = some (.ptr base))
    (hq : readBytes s.mem base n = some q) :
    ∃ (e : State) (j : Nat), j ≤ 13 ∧ e.mem = s.mem ∧
      ((∃ i, litRefusal e i ∧ neLitCheck q (litBytes neLitFalse 5) = some i) ∨
       (litAccept e ∧ neLitCheck q (litBytes neLitFalse 5) = none)) ∧
      (∀ k, runFuel calls (j + k) stage2NoEventBody (stateAt env s) =
        runFuel calls k stage2NoEventBody e) :=
  stage2NoEventLitChain_run calls env s "if.then504"
    (lit := neLitFalse) (ln := BitVec.ofNat 64 5) (tag := BitVec.ofNat 64 9)
    (b := 0) hpc hpre (by decide) (by decide) (by decide) (by decide)
    hee hidx hn hsub harr hq (Or.inr ⟨rfl, rfl⟩)

/-- **`null`**: four bytes at `if.then509`. -/
theorem stage2NoEventLitChain_null
    (calls : Calls) (env : Env) (s : State)
    {base : Nat} {ee idx : BitVec 64} {n : Nat} {q : List UInt8}
    (hpc : s.pc = "if.end519") (hpre : s.pre = some "if.then509")
    (hee : lookupName env "%ee.1" = some (.int 64 ee))
    (hidx : lookupName env "%idxprom.lcssa" = some (.int 64 idx))
    (hn : n < 2 ^ 64) (hsub : ee - idx = BitVec.ofNat 64 n)
    (harr : lookupName env "%arrayidx6.le1046" = some (.ptr base))
    (hq : readBytes s.mem base n = some q) :
    ∃ (e : State) (j : Nat), j ≤ 13 ∧ e.mem = s.mem ∧
      ((∃ i, litRefusal e i ∧ neLitCheck q (litBytes neLitNull 4) = some i) ∨
       (litAccept e ∧ neLitCheck q (litBytes neLitNull 4) = none)) ∧
      (∀ k, runFuel calls (j + k) stage2NoEventBody (stateAt env s) =
        runFuel calls k stage2NoEventBody e) :=
  stage2NoEventLitChain_run calls env s "if.then509"
    (lit := neLitNull) (ln := BitVec.ofNat 64 4) (tag := BitVec.ofNat 64 10)
    (b := 1) hpc hpre (by decide) (by decide) (by decide) (by decide)
    hee hidx hn hsub harr hq (Or.inl ⟨rfl, rfl⟩)

end LeanLLVM.Refinement
