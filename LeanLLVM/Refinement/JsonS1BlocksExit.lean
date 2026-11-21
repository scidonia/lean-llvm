/-
`for.end101`: the block's `phi` arm, and its tie to the peel.

The block is the loop's bound's arm.  Seven `phi`s merge the words the phase and
the fused loop carry — the shift register, the DFA's three carried words, the
carried ASCII word, the accumulator and the carried byte — and the block's own
comparison asks whether the document's length leaves a partial block, which is
the peel's test at `%tobool102.not`.  The terminator sends a block-aligned length
to `if.end153` and every other to `if.then103`.

`JsonS1BlocksRefine` states the block's run at the ASCII loop's own latch
(`for_end101_denote`, `asciiExit_denote`) and both of that arm's branches; the
fused loop's arm and the tie to the peel were the loop's remaining obligation.
This module closes them.

## The selections, at both edges

`forEnd101Phis` is the block's leading `phi` run as a table, and
`for_end101Instrs_eq` pins the table to the emitted instruction list.  The two
edge theorems are the model's own selection relation (`PhiSelects`): at `for.inc`
each `phi` selects the latch's register or the constant the arm carries, and at
`if.end98` each selects the fused loop's register — `%u8k.1.lcssa` is `%u8k.2`,
`%ascii.1.lcssa` is `%or.i282`, `%prev_ascii.1.lcssa` is `%75`, the three
`%st.sroa.*` words are `%shr.i.i325`/`%conv13.i.i324`/`%shr.i348`, and
`%prevS.2.lcssa` is `%shr85`.

`forEnd101OutOf` is the block's output at either edge, one cell per `phi`
destination plus the test; `forEnd101Out_eq` identifies the ASCII exit's output
with it, so the two edges differ only in the values the phis select.

## The entry into the peel

The tie is `peelEntryEnv`'s readings: `%n` is the caller's length, `%b` and
`%ent` are the carrier's two pointers, `%shr` is the carrier's bound, `%conv` is
the entry's gate bit, the four carried words are the latch's cells the phis
copied, `%and` is the entry's remainder, and the ASCII word and the carried byte
are the constants the ASCII arm selects.  With those, `for_end101_peel_denote` is
`if_then103`'s twelve segments run at the state the `for.end101` branch hands it,
with the model's `ifThen103Values` at those very inputs.  The accumulator cell
the arm selects is at the same output (`lookupName_peelEntryEnv_u8k`); the peel's
windows do not read it, but the merge's peel arm does.

The peel's slot is the pad's last block when the length is not block-aligned:
`%and` is the length's remainder (`and_sixtythree_toNat`), so a non-zero test is
a non-zero remainder, and `shr + 1 = blocksOf bs.length`
(`ushr_six_succ_eq_blocksOf`).  `for_end101_peel_last_block` reads the two
window loads as that block's halves, at the address the cleared-low-bits mask
gives (`and_high_mask_toNat`).

## What remains, and is not here

**The fused loop's own run.**  The two-step theorem from `if.end98`
(`for_end98_to_peel`) takes the seven fused-edge registers as the loop's own
cells and composes `if_end98`'s latch step with the block's run; the loop's
invariant that establishes those registers is the fused loop's, and the module
does not state a run to it (`JsonS1BlocksRefine` proves the first pass to
`if.then90` and the body's own segments).

**The hand-off's exit.**  `if.end50`'s other branch reaches the same block, and
Refine states only its loop branch (`if_end50_step_loop`).  Its seven phis select
the join's `%st.sroa.15.1485`, `%st.sroa.9.1487`, `%st.sroa.0.1489`,
`%prev_ascii.0`, `%u8k.0`, `%ascii.0` and `%prevS.1491`; the block's run at that
edge is the same `block_eval_b` equation at those cells, and the hand-off's
obligation rather than this block's.

**The fused arm's tie to the peel.**  `forEnd101OutOf` is stated for either edge,
but `for_end101_peel_denote` is the ASCII exit's: at the fused edge the ASCII
word is `%or.i282`, the accumulator `%u8k.2` and the carried byte `%75`, so the
peel's `ifThen103Values` would carry those instead of the constants, and its
`%prev_ascii` is not `1`.  Stating that instance is a lookup substitution on the
same cells.

**The record instance.**  `s1_blocks_satisfies` still owes its verdict conjuncts
(`VerdictStaging`'s `ascii_bytes`, `acc_pack` and `err_def`), the entry array's
prefix words, the escape stream and count, and the four-region
`UnchangedOutside`; the block arm here is one of the arm steps those compose, not
the composition's budget.
-/
import LeanLLVM.Refinement.JsonS1BlocksRefine
import LeanLLVM.Refinement.JsonS1BlocksTail

namespace LeanLLVM.Refinement.JsonS1BlocksExit

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.BlockEvalVector
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1BlocksTail
open LeanLLVM.Refinement.JsonEntrySteps (ofBool_eq_zero)
open LeanLLVM.Refinement.JsonScanSpec (blocksOf padded)

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### The block's `phi` table

The block's leading run is the seven merges, in the order the emission writes
them; the table is stated once so both edges select through the same list, and
`for_end101Instrs_eq` pins it to the emitted instruction list. -/

/-- `for.end101`'s seven `phi`s, in the block's own order. -/
def forEnd101Phis : List PhiSpec :=
  [{ dst := "%st.sroa.15.2.lcssa", ty := .int 64,
     incoming := [("if.end50", .reg "%st.sroa.15.1485"),
       ("if.end98", .reg "%shr.i348"), ("for.inc", .reg "%shr.i")] },
   { dst := "%st.sroa.9.2.lcssa", ty := .int 64,
     incoming := [("if.end50", .reg "%st.sroa.9.1487"),
       ("if.end98", .reg "%conv13.i.i324"), ("for.inc", .reg "%conv13.i.i")] },
   { dst := "%st.sroa.0.2.lcssa", ty := .int 64,
     incoming := [("if.end50", .reg "%st.sroa.0.1489"),
       ("if.end98", .reg "%shr.i.i325"), ("for.inc", .reg "%shr.i.i")] },
   { dst := "%prev_ascii.1.lcssa", ty := .int 32,
     incoming := [("if.end50", .reg "%prev_ascii.0"),
       ("if.end98", .reg "%75"), ("for.inc", .imm (.int 32 1))] },
   { dst := "%u8k.1.lcssa", ty := .vec 4 (.int 64),
     incoming := [("if.end50", .reg "%u8k.0"),
       ("if.end98", .reg "%u8k.2"), ("for.inc", .imm (.splat 4 64 0))] },
   { dst := "%ascii.1.lcssa", ty := .vec 4 (.int 64),
     incoming := [("if.end50", .reg "%ascii.0"),
       ("if.end98", .reg "%or.i282"), ("for.inc", .imm (.splat 4 64 0))] },
   { dst := "%prevS.2.lcssa", ty := .int 64,
     incoming := [("if.end50", .reg "%prevS.1491"),
       ("if.end98", .reg "%shr85"), ("for.inc", .reg "%shr17")] }]

/-- The block's last instruction: the peel's test, `%and`'s zero comparison. -/
def forEnd101Test : Instr :=
  LeanLLVM.Instr.icmp
    "%tobool102.not"
    (LeanLLVM.IPred.eq)
    64
    (LeanLLVM.Operand.reg "%and")
    (LeanLLVM.Operand.imm (LeanLLVM.Const.int 64 0x0000000000000000#64))

/-- The table and the test are the emitted block's instruction list. -/
theorem for_end101Instrs_eq :
    for_end101Instrs = forEnd101Phis.map PhiSpec.instr ++ [forEnd101Test] := rfl

/-! ### The seven selections at the ASCII loop's latch

The latch's arm carries its four words as registers and the ASCII word, the
accumulator and the carried byte as constants: the phase has seen no non-ASCII
byte, so the ASCII word and the accumulator are zero lanes and the carried byte
is set. -/

/-- **The latch's edge, as `PhiSelects`.**  Each `phi` picks the latch's register
or the constant the arm carries. -/
theorem for_end101_phi_selects_latch (env : Env) (s : State) (c : AsciiCarry)
    (hprevS : lookupName env "%shr17" = some (.int 64 c.prevS))
    (hst0 : lookupName env "%shr.i.i" = some (.int 64 c.st0))
    (hst9 : lookupName env "%conv13.i.i" = some (.int 64 c.st9))
    (hst15 : lookupName env "%shr.i" = some (.int 64 c.st15)) :
    PhiSelects (stateAt env s) "for.inc" forEnd101Phis
      [("%st.sroa.15.2.lcssa", .int 64 c.st15),
       ("%st.sroa.9.2.lcssa", .int 64 c.st9),
       ("%st.sroa.0.2.lcssa", .int 64 c.st0),
       ("%prev_ascii.1.lcssa", .int 32 1),
       ("%u8k.1.lcssa", .vec 4 64 (List.replicate 4 0)),
       ("%ascii.1.lcssa", .vec 4 64 (List.replicate 4 0)),
       ("%prevS.2.lcssa", .int 64 c.prevS)] := by
  refine PhiSelects.cons (sp := forEnd101Phis[0]) (op := .reg "%shr.i")
      (v := .int 64 c.st15) ?_ ?_
    (PhiSelects.cons (sp := forEnd101Phis[1]) (op := .reg "%conv13.i.i")
      (v := .int 64 c.st9) ?_ ?_
      (PhiSelects.cons (sp := forEnd101Phis[2]) (op := .reg "%shr.i.i")
        (v := .int 64 c.st0) ?_ ?_
        (PhiSelects.cons (sp := forEnd101Phis[3]) (op := .imm (.int 32 1))
          (v := .int 32 1) ?_ ?_
          (PhiSelects.cons (sp := forEnd101Phis[4]) (op := .imm (.splat 4 64 0))
            (v := .vec 4 64 (List.replicate 4 0)) ?_ ?_
            (PhiSelects.cons (sp := forEnd101Phis[5]) (op := .imm (.splat 4 64 0))
              (v := .vec 4 64 (List.replicate 4 0)) ?_ ?_
              (PhiSelects.cons (sp := forEnd101Phis[6]) (op := .reg "%shr17")
                (v := .int 64 c.prevS) ?_ ?_ PhiSelects.nil))))))
  all_goals
    (first
     | (simp only [forEnd101Phis]; rfl)
     | exact evalOperand_reg_of _ _ _ _ hst15
     | exact evalOperand_reg_of _ _ _ _ hst9
     | exact evalOperand_reg_of _ _ _ _ hst0
     | exact evalOperand_reg_of _ _ _ _ hprevS
     | rfl)

/-! ### The seven selections at the fused loop's exit

The fused loop's arm carries everything as registers: the last body's own three
carried words, the ASCII word it joined, the accumulator `if.end93` selected, the
probe's result as the carried byte, and the shift register. -/

/-- **The fused loop's edge, as `PhiSelects`.**  Each `phi` picks the fused
loop's own register; in particular `%u8k.1.lcssa` is `%u8k.2`, the accumulator
after `if.end93`. -/
theorem for_end101_phi_selects_fused (env : Env) (s : State)
    (prevS : BitVec 64) (ascii u8k : List (BitVec 64)) (prevAscii : BitVec 32)
    (st0 st9 st15 : BitVec 64)
    (hprevS : lookupName env "%shr85" = some (.int 64 prevS))
    (hascii : lookupName env "%or.i282" = some (.vec 4 64 ascii))
    (hu8k : lookupName env "%u8k.2" = some (.vec 4 64 u8k))
    (hprevAscii : lookupName env "%75" = some (.int 32 prevAscii))
    (hst0 : lookupName env "%shr.i.i325" = some (.int 64 st0))
    (hst9 : lookupName env "%conv13.i.i324" = some (.int 64 st9))
    (hst15 : lookupName env "%shr.i348" = some (.int 64 st15)) :
    PhiSelects (stateAt env s) "if.end98" forEnd101Phis
      [("%st.sroa.15.2.lcssa", .int 64 st15),
       ("%st.sroa.9.2.lcssa", .int 64 st9),
       ("%st.sroa.0.2.lcssa", .int 64 st0),
       ("%prev_ascii.1.lcssa", .int 32 prevAscii),
       ("%u8k.1.lcssa", .vec 4 64 u8k),
       ("%ascii.1.lcssa", .vec 4 64 ascii),
       ("%prevS.2.lcssa", .int 64 prevS)] := by
  refine PhiSelects.cons (sp := forEnd101Phis[0]) (op := .reg "%shr.i348")
      (v := .int 64 st15) ?_ ?_
    (PhiSelects.cons (sp := forEnd101Phis[1]) (op := .reg "%conv13.i.i324")
      (v := .int 64 st9) ?_ ?_
      (PhiSelects.cons (sp := forEnd101Phis[2]) (op := .reg "%shr.i.i325")
        (v := .int 64 st0) ?_ ?_
        (PhiSelects.cons (sp := forEnd101Phis[3]) (op := .reg "%75")
          (v := .int 32 prevAscii) ?_ ?_
          (PhiSelects.cons (sp := forEnd101Phis[4]) (op := .reg "%u8k.2")
            (v := .vec 4 64 u8k) ?_ ?_
            (PhiSelects.cons (sp := forEnd101Phis[5]) (op := .reg "%or.i282")
              (v := .vec 4 64 ascii) ?_ ?_
              (PhiSelects.cons (sp := forEnd101Phis[6]) (op := .reg "%shr85")
                (v := .int 64 prevS) ?_ ?_ PhiSelects.nil))))))
  all_goals
    (first
     | (simp only [forEnd101Phis]; rfl)
     | exact evalOperand_reg_of _ _ _ _ hst15
     | exact evalOperand_reg_of _ _ _ _ hst9
     | exact evalOperand_reg_of _ _ _ _ hst0
     | exact evalOperand_reg_of _ _ _ _ hprevAscii
     | exact evalOperand_reg_of _ _ _ _ hu8k
     | exact evalOperand_reg_of _ _ _ _ hascii
     | exact evalOperand_reg_of _ _ _ _ hprevS)

/-! ### The block's output, at either edge

The output has one cell per `phi` destination and the test's cell; the two edges
differ only in the values written there, so one definition carries both and
`forEnd101Out_eq` identifies the ASCII exit's spelling with it. -/

/-- `for.end101`'s output: the seven selected words and the peel's test. -/
def forEnd101OutOf (env : Env) (prevS : BitVec 64) (ascii u8k : List (BitVec 64))
    (prevAscii : BitVec 32) (st0 st9 st15 andv : BitVec 64) : Env :=
  cells [("%tobool102.not", .int 1 (evalICmp .eq andv 0)),
         ("%prevS.2.lcssa", .int 64 prevS),
         ("%ascii.1.lcssa", .vec 4 64 ascii),
         ("%u8k.1.lcssa", .vec 4 64 u8k),
         ("%prev_ascii.1.lcssa", .int 32 prevAscii),
         ("%st.sroa.0.2.lcssa", .int 64 st0),
         ("%st.sroa.9.2.lcssa", .int 64 st9),
         ("%st.sroa.15.2.lcssa", .int 64 st15)] env

/-- The ASCII exit's output, as the generic one: the latch's four words and the
arm's three constants. -/
theorem forEnd101Out_eq (env : Env) (c : AsciiCarry) (andv : BitVec 64) :
    forEnd101Out env c andv =
      forEnd101OutOf env c.prevS (List.replicate 4 0) (List.replicate 4 0) 1
        c.st0 c.st9 c.st15 andv := rfl

/-- **The block's run at the latch's edge**, at the generic output. -/
theorem for_end101_latch_denote (env : Env) (s : State) (c : AsciiCarry)
    (andv : BitVec 64)
    (hpre : s.pre = some "for.inc")
    (hprevS : lookupName env "%shr17" = some (.int 64 c.prevS))
    (hst0 : lookupName env "%shr.i.i" = some (.int 64 c.st0))
    (hst9 : lookupName env "%conv13.i.i" = some (.int 64 c.st9))
    (hst15 : lookupName env "%shr.i" = some (.int 64 c.st15))
    (hand : lookupName env "%and" = some (.int 64 andv)) :
    denoteCode s1BlocksCalls for_end101Instrs (stateAt env s) =
      some (stateAt (forEnd101OutOf env c.prevS (List.replicate 4 0)
        (List.replicate 4 0) 1 c.st0 c.st9 c.st15 andv) s) := by
  rw [← forEnd101Out_eq]
  exact for_end101_denote env s c andv hpre hprevS hst0 hst9 hst15 hand

/-- **The block's run at the fused loop's edge.**  The seven phis select the
fused loop's registers, and the block's own comparison of `%and` with zero is the
peel's test. -/
theorem for_end101_fused_denote (env : Env) (s : State)
    (prevS : BitVec 64) (ascii u8k : List (BitVec 64)) (prevAscii : BitVec 32)
    (st0 st9 st15 andv : BitVec 64)
    (hpre : s.pre = some "if.end98")
    (hprevS : lookupName env "%shr85" = some (.int 64 prevS))
    (hascii : lookupName env "%or.i282" = some (.vec 4 64 ascii))
    (hu8k : lookupName env "%u8k.2" = some (.vec 4 64 u8k))
    (hprevAscii : lookupName env "%75" = some (.int 32 prevAscii))
    (hst0 : lookupName env "%shr.i.i325" = some (.int 64 st0))
    (hst9 : lookupName env "%conv13.i.i324" = some (.int 64 st9))
    (hst15 : lookupName env "%shr.i348" = some (.int 64 st15))
    (hand : lookupName env "%and" = some (.int 64 andv)) :
    denoteCode s1BlocksCalls for_end101Instrs (stateAt env s) =
      some (stateAt (forEnd101OutOf env prevS ascii u8k prevAscii st0 st9 st15 andv) s) := by
  simp only [for_end101Instrs, forEnd101OutOf]
  block_eval_b

/-- The peel's test at the block's output: `%tobool102.not` is `%and`'s zero
comparison. -/
theorem for_end101_tobool102_not (env : Env) (prevS : BitVec 64)
    (ascii u8k : List (BitVec 64)) (prevAscii : BitVec 32)
    (st0 st9 st15 andv : BitVec 64) :
    lookupName (forEnd101OutOf env prevS ascii u8k prevAscii st0 st9 st15 andv)
        "%tobool102.not" = some (.int 1 (evalICmp .eq andv 0)) := by
  simp [forEnd101OutOf, cells]

/-! ### The fused loop's exit into the block

`if.end98`'s own step leaves `for.end101`'s state at the latch's two cells over
the fused loop's environment; the block's run then reads the fused registers
through those two cells, and its branch is the peel's. -/

/-- A fused register read through `if.end98`'s two cells to the environment
beneath them. -/
theorem lookupName_ifEnd98Env_of (env : Env) (i shr : BitVec 64) {k : String}
    {v : Value} (h : lookupName env k = some v)
    (h1 : "%exitcond537.not" ≠ k) (h2 : "%inc100" ≠ k) :
    lookupName (ifEnd98Env env i shr) k = some v := by
  simp only [ifEnd98Env, cells]
  rw [lookupName_cons_ne _ _ h1, lookupName_cons_ne _ _ h2]
  exact h

/-- **The fused loop's exit and the peel's branch.**  `if.end98` takes its exit
at the loop bound, and the block's run over the fused registers leaves for
`if.then103` when `%and` is non-zero. -/
theorem for_end98_to_peel (env : Env) (s : State) (i shr : BitVec 64)
    (prevS : BitVec 64) (ascii u8k : List (BitVec 64)) (prevAscii : BitVec 32)
    (st0 st9 st15 andv : BitVec 64)
    (hpc : s.pc = "if.end98")
    (hi : lookupName env "%i.2523" = some (.int 64 i))
    (hshr : lookupName env "%shr" = some (.int 64 shr))
    (hexit : evalICmp .eq (i + 1) shr = 1)
    (hprevS : lookupName env "%shr85" = some (.int 64 prevS))
    (hascii : lookupName env "%or.i282" = some (.vec 4 64 ascii))
    (hu8k : lookupName env "%u8k.2" = some (.vec 4 64 u8k))
    (hprevAscii : lookupName env "%75" = some (.int 32 prevAscii))
    (hst0 : lookupName env "%shr.i.i325" = some (.int 64 st0))
    (hst9 : lookupName env "%conv13.i.i324" = some (.int 64 st9))
    (hst15 : lookupName env "%shr.i348" = some (.int 64 st15))
    (hand : lookupName env "%and" = some (.int 64 andv))
    (hpeel : evalICmp .eq andv 0 = 0) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
      .jump (stateAt (ifEnd98Env env i shr)
        { s with pc := "for.end101", pre := some "if.end98" }) ∧
    step s1BlocksCalls s1BlocksFunction
        (stateAt (ifEnd98Env env i shr)
          { s with pc := "for.end101", pre := some "if.end98" }) =
      .jump (stateAt (forEnd101OutOf (ifEnd98Env env i shr) prevS ascii u8k prevAscii
        st0 st9 st15 andv)
        { s with pc := "if.then103", pre := some "for.end101" }) := by
  refine ⟨if_end98_step_exit env s i shr hpc hi hshr hexit, ?_⟩
  have hprevS' := lookupName_ifEnd98Env_of env i shr hprevS (by decide) (by decide)
  have hascii' := lookupName_ifEnd98Env_of env i shr hascii (by decide) (by decide)
  have hu8k' := lookupName_ifEnd98Env_of env i shr hu8k (by decide) (by decide)
  have hprevAscii' :=
    lookupName_ifEnd98Env_of env i shr hprevAscii (by decide) (by decide)
  have hst0' := lookupName_ifEnd98Env_of env i shr hst0 (by decide) (by decide)
  have hst9' := lookupName_ifEnd98Env_of env i shr hst9 (by decide) (by decide)
  have hst15' := lookupName_ifEnd98Env_of env i shr hst15 (by decide) (by decide)
  have hand' := lookupName_ifEnd98Env_of env i shr hand (by decide) (by decide)
  have hfind : s1BlocksFunction.findBlock
      (stateAt (ifEnd98Env env i shr)
        { s with pc := "for.end101", pre := some "if.end98" }).pc
      = some for_end101Block := by
    rw [show (stateAt (ifEnd98Env env i shr)
      { s with pc := "for.end101", pre := some "if.end98" }).pc = "for.end101"
      from rfl]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_for_end101
  rw [step_at hfind (for_end101_fused_denote (ifEnd98Env env i shr)
    { s with pc := "for.end101", pre := some "if.end98" } prevS ascii u8k prevAscii
    st0 st9 st15 andv rfl hprevS' hascii' hu8k' hprevAscii' hst0' hst9' hst15' hand')]
  rw [show for_end101Block.term = for_end101Term from rfl]
  simp only [for_end101Term]
  rw [execTerm_condbr_false
    (BlockEval.evalOperand_reg_of _ _ _ _ (for_end101_tobool102_not _ _ _ _ _ _ _ _ _))
    hpeel]
  rfl

/-! ### The tie to the peel

The peel enters at the block's output: its twelve segments read `%n`, `%b`,
`%ent`, `%shr`, `%conv`, the four carried words, the ASCII word, the carried byte
and `%and`, and those are `forEnd101Out`'s cells over the caller's own. -/

/-- The environment the peel enters from the bound's arm: the latch's cells, the
block's seven `phi` cells and the test, over the caller's. -/
abbrev peelEntryEnv (env : Env) (c : AsciiCarry) (andv : BitVec 64) : Env :=
  forEnd101Out (forIncEnv env c.i c.shr) c andv

/-- A caller's register read through the block's eight cells and the latch's two
to the caller's environment. -/
theorem lookupName_peelEntryEnv_of (env : Env) (c : AsciiCarry) (andv : BitVec 64)
    {k : String} {v : Value} (h : lookupName env k = some v)
    (h1 : "%exitcond.not" ≠ k) (h2 : "%inc" ≠ k) (h3 : "%tobool102.not" ≠ k)
    (h4 : "%prevS.2.lcssa" ≠ k) (h5 : "%ascii.1.lcssa" ≠ k)
    (h6 : "%u8k.1.lcssa" ≠ k) (h7 : "%prev_ascii.1.lcssa" ≠ k)
    (h8 : "%st.sroa.0.2.lcssa" ≠ k) (h9 : "%st.sroa.9.2.lcssa" ≠ k)
    (h10 : "%st.sroa.15.2.lcssa" ≠ k) :
    lookupName (peelEntryEnv env c andv) k = some v := by
  simp only [peelEntryEnv, forEnd101Out, forIncEnv, cells]
  rw [lookupName_cons_ne _ _ h3, lookupName_cons_ne _ _ h4,
    lookupName_cons_ne _ _ h5, lookupName_cons_ne _ _ h6,
    lookupName_cons_ne _ _ h7, lookupName_cons_ne _ _ h8,
    lookupName_cons_ne _ _ h9, lookupName_cons_ne _ _ h10,
    lookupName_cons_ne _ _ h1, lookupName_cons_ne _ _ h2]
  exact h

/-- The caller's length, through the latch and the block. -/
theorem lookupName_peelEntryEnv_n (env : Env) (c : AsciiCarry) (andv : BitVec 64)
    {n : BitVec 64} (h : lookupName env "%n" = some (.int 64 n)) :
    lookupName (peelEntryEnv env c andv) "%n" = some (.int 64 n) :=
  lookupName_peelEntryEnv_of env c andv h (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The block's base, through the latch and the block. -/
theorem lookupName_peelEntryEnv_b (env : Env) (c : AsciiCarry) (andv : BitVec 64)
    {b : Nat} (h : lookupName env "%b" = some (.ptr b)) :
    lookupName (peelEntryEnv env c andv) "%b" = some (.ptr b) :=
  lookupName_peelEntryEnv_of env c andv h (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The emit base, through the latch and the block. -/
theorem lookupName_peelEntryEnv_ent (env : Env) (c : AsciiCarry) (andv : BitVec 64)
    {ent : Nat} (h : lookupName env "%ent" = some (.ptr ent)) :
    lookupName (peelEntryEnv env c andv) "%ent" = some (.ptr ent) :=
  lookupName_peelEntryEnv_of env c andv h (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The loop bound, through the latch and the block. -/
theorem lookupName_peelEntryEnv_shr (env : Env) (c : AsciiCarry) (andv : BitVec 64)
    {shr : BitVec 64} (h : lookupName env "%shr" = some (.int 64 shr)) :
    lookupName (peelEntryEnv env c andv) "%shr" = some (.int 64 shr) :=
  lookupName_peelEntryEnv_of env c andv h (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The carried byte test, through the latch and the block. -/
theorem lookupName_peelEntryEnv_conv (env : Env) (c : AsciiCarry) (andv : BitVec 64)
    {conv : BitVec 32} (h : lookupName env "%conv" = some (.int 32 conv)) :
    lookupName (peelEntryEnv env c andv) "%conv" = some (.int 32 conv) :=
  lookupName_peelEntryEnv_of env c andv h (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The entry's remainder, through the latch and the block. -/
theorem lookupName_peelEntryEnv_and (env : Env) (c : AsciiCarry) (andv : BitVec 64)
    {a : BitVec 64} (h : lookupName env "%and" = some (.int 64 a)) :
    lookupName (peelEntryEnv env c andv) "%and" = some (.int 64 a) :=
  lookupName_peelEntryEnv_of env c andv h (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The first carried word: the latch's `%shr.i.i`, which the `phi` copied. -/
theorem lookupName_peelEntryEnv_st0 (env : Env) (c : AsciiCarry) (andv : BitVec 64) :
    lookupName (peelEntryEnv env c andv) "%st.sroa.0.2.lcssa"
      = some (.int 64 c.st0) := by
  simp only [peelEntryEnv, forEnd101Out, cells]
  block_lk_cons

/-- The second carried word: the latch's `%conv13.i.i`. -/
theorem lookupName_peelEntryEnv_st9 (env : Env) (c : AsciiCarry) (andv : BitVec 64) :
    lookupName (peelEntryEnv env c andv) "%st.sroa.9.2.lcssa"
      = some (.int 64 c.st9) := by
  simp only [peelEntryEnv, forEnd101Out, cells]
  block_lk_cons

/-- The third carried word: the latch's `%shr.i`. -/
theorem lookupName_peelEntryEnv_st15 (env : Env) (c : AsciiCarry) (andv : BitVec 64) :
    lookupName (peelEntryEnv env c andv) "%st.sroa.15.2.lcssa"
      = some (.int 64 c.st15) := by
  simp only [peelEntryEnv, forEnd101Out, cells]
  block_lk_cons

/-- The shift register: the latch's `%shr17`. -/
theorem lookupName_peelEntryEnv_prevS (env : Env) (c : AsciiCarry) (andv : BitVec 64) :
    lookupName (peelEntryEnv env c andv) "%prevS.2.lcssa" = some (.int 64 c.prevS) := by
  simp only [peelEntryEnv, forEnd101Out, cells]
  block_lk_cons

/-- The ASCII word the latch's arm carries: zero lanes. -/
theorem lookupName_peelEntryEnv_ascii (env : Env) (c : AsciiCarry) (andv : BitVec 64) :
    lookupName (peelEntryEnv env c andv) "%ascii.1.lcssa"
      = some (.vec 4 64 (List.replicate 4 0)) := by
  simp only [peelEntryEnv, forEnd101Out, cells]
  block_lk_cons

/-- The carried byte the latch's arm carries: set. -/
theorem lookupName_peelEntryEnv_prevAscii (env : Env) (c : AsciiCarry)
    (andv : BitVec 64) :
    lookupName (peelEntryEnv env c andv) "%prev_ascii.1.lcssa" = some (.int 32 1) := by
  simp only [peelEntryEnv, forEnd101Out, cells]
  block_lk_cons

/-- The accumulator the latch's arm carries: zero lanes.  The peel's own windows
do not read it, so its run above does not consume this cell; the merge's peel arm
does, as the accumulator the last whole block left. -/
theorem lookupName_peelEntryEnv_u8k (env : Env) (c : AsciiCarry) (andv : BitVec 64) :
    lookupName (peelEntryEnv env c andv) "%u8k.1.lcssa"
      = some (.vec 4 64 (List.replicate 4 0)) := by
  simp only [peelEntryEnv, forEnd101Out, cells]
  block_lk_cons

/-- **The peel's run from the bound's arm.**  `if.then103`'s twelve segments run
at the state `for.end101` hands them, with `ifThen103Values` at the block's own
cells: the caller's length and pointers, the latch's four carried words, the
entry's remainder, and the ASCII arm's zero word and set carried byte. -/
theorem for_end101_peel_denote (env : Env) (s : State) (c : AsciiCarry)
    (n andv : BitVec 64) (conv : BitVec 32) (bs136 bs137 : List UInt8)
    (hinv : AsciiInv env s c)
    (hn : lookupName env "%n" = some (.int 64 n))
    (hconv : lookupName env "%conv" = some (.int 32 conv))
    (hand : lookupName env "%and" = some (.int 64 andv))
    (hpos : ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat < 2 ^ 63)
    (h136 : readBytes s.mem
      (c.b + ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat) 32 = some bs136)
    (h137 : readBytes s.mem
      ((c.b + ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat)
        + ((0x0000000000000020#64).signExtend 64).toNat) 32 = some bs137)
    (hshr63 : c.shr.toNat < 2 ^ 63) :
    let v := ifThen103Values n c.b bs136 bs137 (List.replicate 4 0) c.st0 c.st9
      c.st15 c.prevS andv c.shr c.ent conv 1
    denoteCode s1BlocksCalls if_then103Instrs
        (stateAt (peelEntryEnv env c andv)
          { s with pc := "if.then103", pre := some "for.end101" }) =
      some (stateAt (ifThen103Out (peelEntryEnv env c andv) v)
        { s with
          pc := "if.then103",
          pre := some "for.end101",
          mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8) }) := by
  intro v
  exact if_then103_denote (peelEntryEnv env c andv)
    { s with pc := "if.then103", pre := some "for.end101" } n c.b bs136 bs137
    (List.replicate 4 0) c.st0 c.st9 c.st15 c.prevS andv c.shr c.ent conv 1
    (lookupName_peelEntryEnv_n env c andv hn)
    (lookupName_peelEntryEnv_b env c andv hinv.base)
    (lookupName_peelEntryEnv_ascii env c andv)
    (by simp)
    hpos h136 h137
    (lookupName_peelEntryEnv_st0 env c andv)
    (lookupName_peelEntryEnv_st9 env c andv)
    (lookupName_peelEntryEnv_st15 env c andv)
    (lookupName_peelEntryEnv_prevS env c andv)
    (lookupName_peelEntryEnv_and env c andv hand)
    (lookupName_peelEntryEnv_ent env c andv hinv.emit)
    (lookupName_peelEntryEnv_shr env c andv hinv.bound)
    (by simpa [BitVec.signExtend] using hshr63)
    (lookupName_peelEntryEnv_conv env c andv hconv)
    (lookupName_peelEntryEnv_prevAscii env c andv)

/-! ### The lengths the bound's arm distinguishes

`%and` is the length's low six bits — the remainder — and the mask that clears
them is `%shr`'s block base.  A non-zero remainder is therefore a non-zero
`%and`, and the pad's block count is the whole-block count plus one, which makes
the peel's slot at `%shr` the last block. -/

/-- The low six bits, at `Nat`. -/
theorem and63_eq (x : Nat) : x &&& 63 = x % 64 := by
  have := Nat.and_two_pow_sub_one_eq_mod x 6
  simpa using this

/-- **`%and` is the length's remainder.**  The entry's mask keeps the low six
bits, which are the remainder modulo sixty-four. -/
theorem and_sixtythree_toNat (n : BitVec 64) :
    (n &&& 0x000000000000003f#64).toNat = n.toNat % 64 := by
  rw [BitVec.toNat_and,
    show (0x000000000000003f#64).toNat = 63 from by decide, and63_eq]

/-- **The cleared-low-bits mask is the block base.**  The mask that clears the
low six bits of a length is its whole-block count times sixty-four. -/
theorem and_high_mask (x : Nat) (hx : x < 2 ^ 64) :
    x &&& (2 ^ 64 - 64) = 64 * (x / 64) := by
  have hm : (2 ^ 64 - 64 : Nat) = (2 ^ 58 - 1) * 2 ^ 6 := by decide
  have h64 : (64 : Nat) = 2 ^ 6 := by decide
  rw [hm, h64, show (2 ^ 6 * (x / 2 ^ 6)) = ((x / 2 ^ 6) * 2 ^ 6) from Nat.mul_comm _ _]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow,
    Nat.testBit_two_pow_sub_one]
  by_cases h6 : 6 ≤ j
  · have hd6 : decide (6 ≤ j) = true := decide_eq_true h6
    have hshift : (x / 2 ^ 6).testBit (j - 6) = x.testBit j := by
      rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight,
        show 6 + (j - 6) = j from by omega]
    rw [hd6, hshift]
    by_cases hj : j < 64
    · rw [show decide (j - 6 < 58) = true from decide_eq_true (by omega)]
      simp
    · rw [show decide (j - 6 < 58) = false from decide_eq_false (by omega)]
      have hxbit : x.testBit j = false :=
        Nat.testBit_lt_two_pow (by
          have h2 : 2 ^ 64 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
          omega)
      rw [hxbit]
      simp
  · rw [show decide (6 ≤ j) = false from decide_eq_false h6]
    simp

/-- The sign extension to the same width is the identity, read at `toNat`. -/
theorem signExtend_self_toNat (x : BitVec 64) : (x.signExtend 64).toNat = x.toNat := by
  simp [BitVec.signExtend]

/-- **The block base, at the register.**  `%n &&& ~63` reads as `64 * (n / 64)`. -/
theorem and_high_mask_toNat (n : BitVec 64) :
    (n &&& 0xffffffffffffffc0#64).toNat = 64 * (n.toNat / 64) := by
  rw [BitVec.toNat_and,
    show (0xffffffffffffffc0#64).toNat = 2 ^ 64 - 64 from by decide]
  exact and_high_mask n.toNat n.isLt

/-- The unaligned length's block count: one more than the whole-block count. -/
theorem blocksOf_eq_div_succ {n : Nat} (h : n % 64 ≠ 0) :
    blocksOf n = n / 64 + 1 := by
  unfold JsonScanSpec.blocksOf
  have hdm := Nat.div_add_mod n 64
  have hrlt : n % 64 < 64 := Nat.mod_lt _ (by decide)
  have hrpos : 0 < n % 64 := Nat.pos_of_ne_zero h
  have heq : n + 63 = 64 * (n / 64 + 1) + (n % 64 - 1) := by omega
  have hzero : (n % 64 - 1) / 64 = 0 := Nat.div_eq_of_lt (by omega)
  rw [heq, Nat.mul_add_div (by decide : 0 < 64), hzero]

/-- **The bound's arm's slot is the last block.**  With a non-zero remainder the
phase's `shr` blocks are the whole blocks before the peel's, so the peel's slot
is the pad's last: `shr + 1` is the pad's block count. -/
theorem ushr_six_succ_eq_blocksOf (x : BitVec 64) (h : x.toNat % 64 ≠ 0) :
    (x >>> 6).toNat + 1 = blocksOf x.toNat := by
  rw [ushr_six_toNat, blocksOf_eq_div_succ h]

/-- A non-zero `%and` is a non-zero remainder: the comparison's bit is `%and`'s
zero test, and a clear bit says the word is not zero. -/
theorem ne_zero_of_evalICmp_eq_zero (a : BitVec 64) (h : evalICmp .eq a 0 = 0) :
    a ≠ 0 := by
  intro hh
  subst hh
  have h1 : evalICmp .eq (0 : BitVec 64) 0 = 1 := rfl
  rw [h1] at h
  exact absurd h (by decide)

/-- **The unaligned arm's block count.**  `%and` is the length's remainder, so a
clear `%tobool102.not` (a non-zero `%and`) says the length leaves a partial block,
and the bound's arm's slot `%shr` is the last one: `shr + 1 = blocksOf` the
document's length. -/
theorem for_end101_unaligned_succ (andv shr n : BitVec 64) (bs : List UInt8)
    (hand : andv = n &&& 0x000000000000003f#64)
    (hbit : evalICmp .eq andv 0 = 0)
    (hshr : shr = n >>> 6)
    (hbs : n.toNat = bs.length) :
    shr.toNat + 1 = blocksOf bs.length := by
  have hne : andv ≠ 0 := ne_zero_of_evalICmp_eq_zero andv hbit
  have hmod : n.toNat % 64 ≠ 0 := by
    intro h0
    apply hne
    apply BitVec.eq_of_toNat_eq
    rw [hand, and_sixtythree_toNat, h0]
    rfl
  rw [hshr, ← hbs]
  exact ushr_six_succ_eq_blocksOf n hmod

/-- **The peel's windows are the last block's halves.**  With a non-zero
remainder the peel's slot is the pad's last block, so its two window loads at the
cleared-low-bits address are that block's two thirty-two-byte halves. -/
theorem for_end101_peel_last_block (m : Mem) (bs : List UInt8) (b : Nat)
    (n : BitVec 64) (c : AsciiCarry)
    (hread : readBytes m b (64 * blocksOf bs.length) = some (padded bs))
    (hbs : n.toNat = bs.length)
    (hb : c.b = b)
    (hshr : c.shr = n >>> 6)
    (hmod : n.toNat % 64 ≠ 0) :
    readBytes m (c.b + ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat) 32
        = some ((docBlock bs c.shr.toNat).take 32) ∧
      readBytes m
          (c.b + ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat + 32) 32
        = some ((docBlock bs c.shr.toNat).drop 32) ∧
      c.shr.toNat + 1 = blocksOf bs.length := by
  have hsucc : c.shr.toNat + 1 = blocksOf bs.length := by
    rw [hshr, ← hbs]
    exact ushr_six_succ_eq_blocksOf n hmod
  have haddr : ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat
      = 64 * c.shr.toNat := by
    rw [signExtend_self_toNat, and_high_mask_toNat, ← ushr_six_toNat, ← hshr]
  have hj : c.shr.toNat < blocksOf bs.length := by omega
  obtain ⟨h1, h2⟩ := readBytes_docBlock_halves m bs b hread hj
  refine ⟨?_, ?_, hsucc⟩
  · rw [hb, haddr]
    exact h1
  · rw [hb, haddr]
    exact h2

/-! ### Axiom footprints -/

#print axioms for_end101Instrs_eq
#print axioms for_end101_phi_selects_latch
#print axioms for_end101_phi_selects_fused
#print axioms forEnd101Out_eq
#print axioms for_end101_latch_denote
#print axioms for_end101_fused_denote
#print axioms for_end101_tobool102_not
#print axioms lookupName_ifEnd98Env_of
#print axioms for_end98_to_peel
#print axioms lookupName_peelEntryEnv_of
#print axioms lookupName_peelEntryEnv_n
#print axioms lookupName_peelEntryEnv_b
#print axioms lookupName_peelEntryEnv_ent
#print axioms lookupName_peelEntryEnv_shr
#print axioms lookupName_peelEntryEnv_conv
#print axioms lookupName_peelEntryEnv_and
#print axioms lookupName_peelEntryEnv_st0
#print axioms lookupName_peelEntryEnv_st9
#print axioms lookupName_peelEntryEnv_st15
#print axioms lookupName_peelEntryEnv_prevS
#print axioms lookupName_peelEntryEnv_ascii
#print axioms lookupName_peelEntryEnv_prevAscii
#print axioms lookupName_peelEntryEnv_u8k
#print axioms for_end101_peel_denote
#print axioms and63_eq
#print axioms and_sixtythree_toNat
#print axioms signExtend_self_toNat
#print axioms and_high_mask
#print axioms and_high_mask_toNat
#print axioms blocksOf_eq_div_succ
#print axioms ushr_six_succ_eq_blocksOf
#print axioms ne_zero_of_evalICmp_eq_zero
#print axioms for_end101_unaligned_succ
#print axioms for_end101_peel_last_block

end LeanLLVM.Refinement.JsonS1BlocksExit
