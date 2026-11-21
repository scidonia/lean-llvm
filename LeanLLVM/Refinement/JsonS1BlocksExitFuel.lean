/-
The exit half's charge, and the run at the record's budget.

`JsonS1BlocksPrefix.asciiExitCells_run` and `fusedExitCells_run` reach the return
from `for.end101`, but state their fuel only inside an `∃`.  The composed run at
`s1BlocksBudget` therefore cannot read it: `JsonS1BlocksLoopRun.s1BlocksRun_at_budget`
needs the exit's `jE` and its containment in the budget above the prefix's charge,
and `JsonS1BlocksPrefixFuel.s1BlocksRun_at_budget_of_boundedPrefix` leaves exactly
that pair as its last two inputs.  This module re-derives the two exit
compositions with their control steps counted, so the exit's fuel is a constant
and the run at the budget is a term.

## The exit's arms, and what each costs

The two exits share `for.end101`'s step and its peel test (`fused_end_denote`,
`asciiExit_denote`); the aligned document leaves for `if.end153`, the partial one
for `if.then103` and the merge at `if.end147`.  The tail arms between them and the
return already state their own step counts (`JsonS1BlocksRefines.tail_aligned_run`
at 2, `tail_byte_run` at 3, `tail_silent_run` at 3), so each branch's charge is
the exit's own step plus the arm's:

| branch | exit steps | tail arm | charge |
|---|---|---|---|
| aligned, empty document | 1 (`for.end101`) | 2 (`if.end153`) | 3 |
| aligned, last byte | 1 | 3 (`if.end153`, `if.then164`) | 4 |
| partial block, silent merge | 1 + 1 (`for.end101`, `if.then103`) | 3 (`if.end147`) | 5 |

`exitCharge` is the largest of them, `5`.  The peel's *escape* merge is the
calling arm (`arm &&& 2 ≠ 0`): its call is the fourth step of
`tail_escape_run`'s arm, so that arm's exit is `1 + 1 + 4 = 6`, and it is not
this module's — the two compositions here are stated at the arm bit the silent
merge is selected at, exactly as the committed `_run` lemmas are.

## The run at the budget

`s1BlocksRun_at_budget_of_chargedStages` joins a charged entry-to-exit segment
(the prefix, at its own charge `8 * (%n >>> 6) + 21`, from the record's own
allocator base) to a charged exit segment at the segment's terminal.  The two
charges fit inside `s1BlocksBudget`: `prefixCharge_le_budget` puts the prefix's
`21` beside the budget's `32`, and `exitCharge_le_room` puts the exit's `5` in
the room that is left, at least `11`.  Neither the prefix's fuel nor the exit's
is a hypothesis of the composed run, and `next` is the caller's:
`s1BlocksRun_at_budget_of_chargedExit` is the same statement at `next = 1`, where
`JsonS1BlocksPrefixFuel.OnePrefixBounded` supplies the prefix segment outright.

## What is still owed

The exit's *hypotheses* are not discharged here.  `asciiExitCells_charged` and
`fusedExitCells_charged` take the same model-side facts as the committed
compositions — the peel's merge bit (`hsilent`), the loop's staging (`hstage`),
the peel's own word as a staging (`hstagePeel`), and the tail byte's error bit
(`hstageByte`), at the arm's values — which `JsonS1BlocksPeelStaging` supplies
from the peel's arithmetic and which the loop's register-to-model identities are
still needed for.  The calling arm's exit (the peel's escape merge) is
`JsonS1BlocksEscapeRun`'s.
-/
import LeanLLVM.Refinement.JsonS1BlocksPrefixFuel
import LeanLLVM.Refinement.JsonS1BlocksRefines

namespace LeanLLVM.Refinement.JsonS1BlocksExitFuel

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1BlocksLoop
open LeanLLVM.Refinement.JsonS1BlocksEntry
open LeanLLVM.Refinement.JsonS1BlocksExit
open LeanLLVM.Refinement.JsonS1BlocksTail
open LeanLLVM.Refinement.JsonS1BlocksCompose
open LeanLLVM.Refinement.JsonS1BlocksStaging
open LeanLLVM.Refinement.JsonS1BlocksVerdict
open LeanLLVM.Refinement.JsonS1BlocksRefines
open LeanLLVM.Refinement.JsonS1BlocksPrefix
open LeanLLVM.Refinement.JsonS1BlocksPrefixFuel
open LeanLLVM.Refinement.JsonS1BlocksLoopRun (s1BlocksInit_entryState)
open LeanLLVM.Refinement.JsonEntryIR (wordsOf)

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### The exit's charge

The exit block's own one or two steps, over the tail arms' two, three and three.
The largest of the three branches is the partial block's silent merge. -/

/-- **The exit half's charge.**  The most control steps any exit arm takes from
`for.end101`'s state to the return: `for.end101`, the peel's `if.then103`, and
the merge's three steps to `if.end170`.  The aligned arms are shorter (three and
four), and the peel's escape merge — the calling arm — is the escape call's
fourth step, one above this. -/
def exitCharge : Nat := 5

/-! ### The exits, charged

The two compositions of `JsonS1BlocksRefines`, with the branch's own step count
witnessed and bounded by `exitCharge` rather than hidden inside the `∃`. -/

/-- **The fused loop's exit to the return, with its fuel.**  From the fused
loop's terminal at `for.end101`, the run reaches the return at one of the three
silent arms' charges: `1 + 2` on the aligned empty document, `1 + 3` on the
aligned last byte, and `1 + (1 + 3)` on the peel's silent merge.  The arm's own
step lemmas are `tail_aligned_run`, `tail_byte_run` and `tail_silent_run`; the
block's test is `fused_end_denote` and the peel's is
`fused_end_peel_denote`/`if_then103_step_end147`. -/
theorem fusedExitCells_charged {esc : Calls} (env : Env) (s : State) (c : FusedCarry)
    (andv n : BitVec 64) (conv : BitVec 32) (bs136 bs137 : List UInt8)
    (bs : List UInt8) (nb : Nat) (gate : Bool) (arm : BitVec 64)
    (h : FusedExit env s c)
    (hand : lookupName env "%and" = some (.int 64 andv))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hb : lookupName env "%b" = some (.ptr c.b))
    (hconv : lookupName env "%conv" = some (.int 32 conv))
    (harm : lookupName env "%arm" = some (.int 64 arm))
    (hasciilen : c.ascii.length = 4)
    (hpos : ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat < 2 ^ 63)
    (h136 : readBytes s.mem
      (c.b + ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat) 32 = some bs136)
    (h137 : readBytes s.mem
      ((c.b + ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat)
        + ((0x0000000000000020#64).signExtend 64).toNat) 32 = some bs137)
    (hshr63 : c.shr.toNat < 2 ^ 63)
    (hnonzero : evalICmp .eq n 0 = 0 → (n.signExtend 64).toNat < 2 ^ 63 ∧ 1 ≤ c.b + (n.signExtend 64).toNat)
    (hlast : evalICmp .eq n 0 = 0 → ∃ last : UInt8, readBytes s.mem (c.b + (n.signExtend 64).toNat - 1) 1 = some [last])
    (hgateZero : arm &&& 2 = 0)
    (hsilent : ∀ (v : IfThen103Values), v = fusedPeelValues env c n andv bs136 bs137 conv →
      lookupName (ifThen103Out
        (forEnd101OutOf env c.prevS c.ascii c.u8k c.prevAscii c.st0 c.st9 c.st15 andv) v)
        "%or.cond191" = some (.int 1 1))
    (hstage : VerdictStaging c.ascii c.u8k bs bs.length nb gate
      (evalICmp .eq (ptestzU8k c.u8k) 0))
    (hstagePeel : ∀ (v : IfThen103Values), v = fusedPeelValues env c n andv bs136 bs137 conv →
      VerdictStaging v.or279 c.u8k bs bs.length nb gate
        (evalICmp .eq (ptestzU8k c.u8k) 0))
    (hstageByte : ∀ (last : UInt8),
      readBytes s.mem (c.b + (n.signExtend 64).toNat - 1) 1 = some [last] →
      VerdictStaging c.ascii c.u8k bs bs.length nb gate
        (evalICmp .eq (ptestzU8k c.u8k) 0 ||| lastByteBits (BitVec.ofNat 8 last.toNat))) :
    ∃ (jE : Nat) (r : BitVec 64) (m : Mem),
      jE ≤ exitCharge ∧
        runFuel (s1BlocksCallsEsc esc) jE s1BlocksFunction (stateAt env s) =
          some (.ret (some (.int 64 r)) m) ∧ VerdictPost r bs := by
  -- the block's own run and its peel test
  have hfind : s1BlocksFunction.findBlock (stateAt env s).pc = some for_end101Block := by
    rw [show (stateAt env s).pc = s.pc from rfl, h.pc]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_for_end101
  have hand' := lookupName_forEnd101OutOf_of env c.prevS c.ascii c.u8k c.prevAscii
    c.st0 c.st9 c.st15 andv hand (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hn' := lookupName_forEnd101OutOf_of env c.prevS c.ascii c.u8k c.prevAscii
    c.st0 c.st9 c.st15 andv hn (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hb' := lookupName_forEnd101OutOf_of env c.prevS c.ascii c.u8k c.prevAscii
    c.st0 c.st9 c.st15 andv hb (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hbitCell := lookupName_forEnd101OutOf_test env c.prevS c.ascii c.u8k c.prevAscii
    c.st0 c.st9 c.st15 andv
  have hrun101 : denoteCode s1BlocksCalls for_end101Instrs (stateAt env s) =
      some (stateAt (forEnd101OutOf env c.prevS c.ascii c.u8k c.prevAscii
        c.st0 c.st9 c.st15 andv) s) :=
    fused_end_denote env s c andv h hand
  have hstep := step_at hfind hrun101
  by_cases hbitAligned : evalICmp .eq andv 0 = 1
  · -- the aligned document: the exit leaves for `if.end153`
    have hstep1 : step (s1BlocksCallsEsc esc) s1BlocksFunction (stateAt env s) =
        .jump (stateAt (forEnd101OutOf env c.prevS c.ascii c.u8k c.prevAscii
          c.st0 c.st9 c.st15 andv) { s with pc := "if.end153", pre := some "for.end101" }) := by
      rw [step_esc_of_free esc s1BlocksFunction _ _ hfind (by decide)]
      rw [hstep]
      rw [show for_end101Block.term = for_end101Term from rfl]
      simp only [for_end101Term]
      rw [execTerm_condbr_true (BlockEval.evalOperand_reg_of _ _ _ _ hbitCell) hbitAligned]
      simp only [stateAt, h.pc]
    by_cases hnz : evalICmp .eq n 0 = 1
    · -- the empty document: `1 + 2`
      have htail := tail_aligned_run (esc := esc) (env := forEnd101OutOf env c.prevS
        c.ascii c.u8k c.prevAscii c.st0 c.st9 c.st15 andv)
        { s with pc := "if.end153", pre := some "for.end101" } n c.u8k c.ascii
        bs nb gate rfl hn' (lookupName_forEnd101OutOf_u8k env _ _ _ _ _ _ _ _)
        (lookupName_forEnd101OutOf_ascii env _ _ _ _ _ _ _ _) hnz
        (by simpa only [stateAt] using hstage)
      exact ⟨1 + 2, _, _, by unfold exitCharge; omega, by
        rw [runFuel_jump_prefix hstep1 2]
        exact htail.1, htail.2⟩
    · -- the last byte: `1 + 3`
      have hnz0 : evalICmp .eq n 0 = 0 := by
        rcases BlockEval.bitVec1_eq_zero_or_one (evalICmp .eq n 0) with h0 | h1
        · exact h0
        · exact absurd h1 hnz
      obtain ⟨hposb, hpb⟩ := hnonzero hnz0
      obtain ⟨last, hlastr⟩ := hlast hnz0
      have htail := tail_byte_run (esc := esc) (env := forEnd101OutOf env c.prevS
        c.ascii c.u8k c.prevAscii c.st0 c.st9 c.st15 andv)
        { s with pc := "if.end153", pre := some "for.end101" } n c.u8k c.ascii
        c.b last bs nb gate rfl hn'
        (lookupName_forEnd101OutOf_u8k env _ _ _ _ _ _ _ _)
        (lookupName_forEnd101OutOf_ascii env _ _ _ _ _ _ _ _) hb' hnz0 hposb hpb
        (by simpa only [stateAt] using hlastr)
        (hstageByte last hlastr)
      exact ⟨1 + 3, _, _, by unfold exitCharge; omega, by
        rw [runFuel_jump_prefix hstep1 3]
        exact htail.1, htail.2⟩
  · -- the partial block: the peel's own run and the merge, `1 + (1 + 3)`
    have hbit : evalICmp .eq andv 0 = 0 := by
      rcases BlockEval.bitVec1_eq_zero_or_one (evalICmp .eq andv 0) with h0 | h1
      · exact h0
      · exact absurd h1 hbitAligned
    have hstep1 : step (s1BlocksCallsEsc esc) s1BlocksFunction (stateAt env s) =
        .jump (stateAt (forEnd101OutOf env c.prevS c.ascii c.u8k c.prevAscii
          c.st0 c.st9 c.st15 andv) { s with pc := "if.then103", pre := some "for.end101" }) := by
      rw [step_esc_of_free esc s1BlocksFunction _ _ hfind (by decide)]
      rw [hstep]
      rw [show for_end101Block.term = for_end101Term from rfl]
      simp only [for_end101Term]
      rw [execTerm_condbr_false (BlockEval.evalOperand_reg_of _ _ _ _ hbitCell) hbit]
      simp only [stateAt, h.pc]
    let A : State := stateAt (forEnd101OutOf env c.prevS c.ascii c.u8k c.prevAscii
      c.st0 c.st9 c.st15 andv) { s with pc := "if.then103", pre := some "for.end101" }
    let v : IfThen103Values := fusedPeelValues env c n andv bs136 bs137 conv
    have hden := fused_end_peel_denote env s c n andv conv bs136 bs137 h hn hconv
      hand hasciilen hpos h136 h137 hshr63
    have hbn := hsilent v rfl
    have hstep2 : step (s1BlocksCallsEsc esc) s1BlocksFunction A =
        .jump (stateAt (ifThen103Out (forEnd101OutOf env c.prevS c.ascii c.u8k
          c.prevAscii c.st0 c.st9 c.st15 andv) v)
          { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
                   pc := "if.end147", pre := some "if.then103" }) := by
      have hfind103 : s1BlocksFunction.findBlock A.pc = some if_then103Block := by
        rw [show A.pc = "if.then103" from rfl]
        exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_then103
      rw [step_esc_of_free esc s1BlocksFunction _ _ hfind103 (by decide)]
      exact if_then103_step_end147 _ A v rfl hbn (by
        rw [show A = stateAt (forEnd101OutOf env c.prevS c.ascii c.u8k c.prevAscii
          c.st0 c.st9 c.st15 andv)
            { s with pc := "if.then103", pre := some "for.end101" } from rfl]
        exact hden)
    have htail := tail_silent_run (esc := esc)
      (env := forEnd101OutOf env c.prevS c.ascii c.u8k c.prevAscii
        c.st0 c.st9 c.st15 andv)
      A v c.u8k arm bs bs.length nb gate
      (lookupName_ifThen103Out_u8k _ v (lookupName_forEnd101OutOf_u8k env c.prevS
        c.ascii c.u8k c.prevAscii c.st0 c.st9 c.st15 andv))
      (lookupName_ifThen103Out_arm _ v (lookupName_forEnd101OutOf_of env c.prevS
        c.ascii c.u8k c.prevAscii c.st0 c.st9 c.st15 andv harm (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)))
      (evalICmp_eq_zero_of_and_two_zero arm hgateZero)
      (hstagePeel v rfl)
    exact ⟨1 + (1 + 3), _, _, by unfold exitCharge; omega, by
      rw [runFuel_jump_prefix hstep1 (1 + 3), runFuel_jump_prefix hstep2 3]
      exact (by simpa only [A, stateAt] using htail.1), htail.2⟩

/-- **The ASCII phase's exit to the return, with its fuel.**  From the bound's
arm at `for.end101`, the same three silent arms at the same charges: `1 + 2` on
the aligned empty document, `1 + 3` on the aligned last byte, and
`1 + (1 + 3)` on the peel's silent merge.  The block's test is
`asciiExit_denote`/`asciiExit_step_peel` and the peel's is
`for_end101_peel_denote`/`if_then103_step_end147`. -/
theorem asciiExitCells_charged {esc : Calls} (env : Env) (s : State) (c : AsciiCarry)
    (bs : List UInt8) (nb : Nat) (gate : Bool) (arm n andv : BitVec 64) (conv : BitVec 32)
    (h : AsciiInv env s c)
    (hread : readBytes c.mem c.b (64 * blocksOf bs.length) = some (padded bs))
    (hbs : n.toNat = bs.length) (hshr : c.shr = n >>> 6)
    (hand : lookupName env "%and" = some (.int 64 andv))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hconv : lookupName env "%conv" = some (.int 32 conv))
    (harm : lookupName env "%arm" = some (.int 64 arm))
    (hgateZero : arm &&& 2 = 0)
    (handEq : andv = n &&& 0x000000000000003f#64)
    (hbs63 : bs.length < 2 ^ 63)
    (hnonzero : evalICmp .eq n 0 = 0 → (n.signExtend 64).toNat < 2 ^ 63 ∧
      1 ≤ c.b + (n.signExtend 64).toNat)
    (hlast : evalICmp .eq n 0 = 0 → ∃ last : UInt8, ∃ p : Nat,
      readBytes s.mem p 1 = some [last] ∧ p = c.b + (n.signExtend 64).toNat - 1)
    (hsilent : ∀ (v : IfThen103Values), v = ifThen103Values n c.b
      ((docBlock bs c.shr.toNat).take 32) ((docBlock bs c.shr.toNat).drop 32)
      (List.replicate 4 0) c.st0 c.st9 c.st15 c.prevS andv c.shr c.ent conv 1 →
      lookupName (ifThen103Out (peelEntryEnv env c andv) v) "%or.cond191"
        = some (.int 1 1))
    (hstage : VerdictStaging (List.replicate 4 0) (List.replicate 4 0) bs bs.length
      nb gate (evalICmp .eq (ptestzU8k (List.replicate 4 0)) 0))
    (hstagePeel : ∀ (v : IfThen103Values), v = ifThen103Values n c.b
      ((docBlock bs c.shr.toNat).take 32) ((docBlock bs c.shr.toNat).drop 32)
      (List.replicate 4 0) c.st0 c.st9 c.st15 c.prevS andv c.shr c.ent conv 1 →
      VerdictStaging v.or279 (List.replicate 4 0) bs bs.length nb gate
        (evalICmp .eq (ptestzU8k (List.replicate 4 0)) 0))
    (hstageByte : ∀ (last : UInt8),
      readBytes s.mem (c.b + (n.signExtend 64).toNat - 1) 1 = some [last] →
      VerdictStaging (List.replicate 4 0) (List.replicate 4 0) bs bs.length nb gate
        (evalICmp .eq (ptestzU8k (List.replicate 4 0)) 0 |||
          lastByteBits (BitVec.ofNat 8 last.toNat))) :
    ∃ (jE : Nat) (r : BitVec 64) (m : Mem),
      jE ≤ exitCharge ∧
        runFuel (s1BlocksCallsEsc esc) jE s1BlocksFunction (asciiExitState env s c) =
          some (.ret (some (.int 64 r)) m) ∧ VerdictPost r bs := by
  have handE := lookupName_forIncEnv_of env c.i c.shr hand (by decide) (by decide)
  have hfind : s1BlocksFunction.findBlock (asciiExitState env s c).pc =
      some for_end101Block := by
    rw [show (asciiExitState env s c).pc = "for.end101" from rfl]
    exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_for_end101
  have hrun101 : denoteCode s1BlocksCalls for_end101Instrs (asciiExitState env s c) =
      some (stateAt (forEnd101Out (forIncEnv env c.i c.shr) c andv)
        (asciiExitState env s c)) :=
    asciiExit_denote env s c andv h hand
  have hbitCell : lookupName (forEnd101Out (forIncEnv env c.i c.shr) c andv)
      "%tobool102.not" = some (.int 1 (evalICmp .eq andv 0)) := by
    rw [forEnd101Out_eq]
    exact for_end101_tobool102_not env c.prevS (List.replicate 4 0)
      (List.replicate 4 0) 1 c.st0 c.st9 c.st15 andv
  have hnOut : lookupName (forEnd101Out (forIncEnv env c.i c.shr) c andv) "%n"
      = some (.int 64 n) := by
    rw [forEnd101Out_eq]
    exact lookupName_forEnd101OutOf_of env c.prevS (List.replicate 4 0)
      (List.replicate 4 0) 1 c.st0 c.st9 c.st15 andv
      (lookupName_forIncEnv_of env c.i c.shr hn (by decide) (by decide))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  have hbOut : lookupName (forEnd101Out (forIncEnv env c.i c.shr) c andv) "%b"
      = some (.ptr c.b) := by
    rw [forEnd101Out_eq]
    exact lookupName_forEnd101OutOf_of env c.prevS (List.replicate 4 0)
      (List.replicate 4 0) 1 c.st0 c.st9 c.st15 andv
      (lookupName_forIncEnv_of env c.i c.shr h.base (by decide) (by decide))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  have hascOut : lookupName (forEnd101Out (forIncEnv env c.i c.shr) c andv)
      "%ascii.1.lcssa" = some (.vec 4 64 (List.replicate 4 0)) := by
    rw [forEnd101Out_eq]
    exact lookupName_forEnd101OutOf_ascii env _ _ _ _ _ _ _ _
  have hu8kOut : lookupName (forEnd101Out (forIncEnv env c.i c.shr) c andv)
      "%u8k.1.lcssa" = some (.vec 4 64 (List.replicate 4 0)) := by
    rw [forEnd101Out_eq]
    exact lookupName_forEnd101OutOf_u8k env _ _ _ _ _ _ _ _
  have harmOut : lookupName (forEnd101Out (forIncEnv env c.i c.shr) c andv) "%arm"
      = some (.int 64 arm) := by
    rw [forEnd101Out_eq]
    exact lookupName_forEnd101OutOf_of env c.prevS (List.replicate 4 0)
      (List.replicate 4 0) 1 c.st0 c.st9 c.st15 andv
      (lookupName_forIncEnv_of env c.i c.shr harm (by decide) (by decide))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  by_cases hbitAligned : evalICmp .eq andv 0 = 1
  · have hstep1 : step (s1BlocksCallsEsc esc) s1BlocksFunction (asciiExitState env s c) =
        .jump (stateAt (forEnd101Out (forIncEnv env c.i c.shr) c andv)
          { s with pc := "if.end153", pre := some "for.end101" }) := by
      rw [step_esc_of_free esc s1BlocksFunction _ _ hfind (by decide)]
      exact asciiExit_step_aligned env s c andv h hand hbitAligned
    by_cases hnz : evalICmp .eq n 0 = 1
    · -- the empty document: `1 + 2`
      have htail := tail_aligned_run (esc := esc)
        (env := forEnd101Out (forIncEnv env c.i c.shr) c andv)
        { s with pc := "if.end153", pre := some "for.end101" } n
        (List.replicate 4 0) (List.replicate 4 0) bs nb gate rfl hnOut
        hu8kOut hascOut hnz hstage
      exact ⟨1 + 2, _, _, by unfold exitCharge; omega, by
        rw [runFuel_jump_prefix hstep1 2]
        exact (by simpa only [stateAt] using htail.1), htail.2⟩
    · -- the last byte: `1 + 3`
      have hnz0 : evalICmp .eq n 0 = 0 := by
        rcases BlockEval.bitVec1_eq_zero_or_one (evalICmp .eq n 0) with h0 | h1
        · exact h0
        · exact absurd h1 hnz
      obtain ⟨hposb, hpb⟩ := hnonzero hnz0
      obtain ⟨last, p, hp_read, hp_eq⟩ := hlast hnz0
      have htail := tail_byte_run (esc := esc)
        (env := forEnd101Out (forIncEnv env c.i c.shr) c andv)
        { s with pc := "if.end153", pre := some "for.end101" } n
        (List.replicate 4 0) (List.replicate 4 0) c.b last bs nb gate rfl hnOut
        hu8kOut hascOut hbOut hnz0 hposb hpb
        (by rw [← hp_eq]; exact hp_read)
        (hstageByte last (by rw [← hp_eq]; exact hp_read))
      exact ⟨1 + 3, _, _, by unfold exitCharge; omega, by
        rw [runFuel_jump_prefix hstep1 3]
        exact (by simpa only [stateAt] using htail.1), htail.2⟩
  · -- the peel's silent merge: `1 + (1 + 3)`
    have hbit : evalICmp .eq andv 0 = 0 := by
      rcases BlockEval.bitVec1_eq_zero_or_one (evalICmp .eq andv 0) with h0 | h1
      · exact h0
      · exact absurd h1 hbitAligned
    have hstep1 : step (s1BlocksCallsEsc esc) s1BlocksFunction (asciiExitState env s c) =
        .jump (stateAt (forEnd101Out (forIncEnv env c.i c.shr) c andv)
          { s with pc := "if.then103", pre := some "for.end101" }) := by
      rw [step_esc_of_free esc s1BlocksFunction _ _ hfind (by decide)]
      exact LeanLLVM.Refinement.JsonS1BlocksRefines.asciiExit_step_peel env s c andv h hand hbit
    have hne : andv ≠ 0 := ne_zero_of_evalICmp_eq_zero andv hbit
    have hmod : n.toNat % 64 ≠ 0 := by
      intro h0
      apply hne
      apply BitVec.eq_of_toNat_eq
      rw [handEq, and_sixtythree_toNat, h0]
      rfl
    have hn63 : n.toNat < 2 ^ 63 := by rw [hbs]; exact hbs63
    have hshr63 : c.shr.toNat < 2 ^ 63 := by
      rw [hshr, ushr_six_toNat]
      omega
    have handv' : (n &&& 0xffffffffffffffc0#64).toNat = 64 * c.shr.toNat := by
      rw [and_high_mask_toNat, ← ushr_six_toNat, ← hshr]
    obtain ⟨h136, h137, hsucc⟩ :=
      for_end101_peel_last_block c.mem bs c.b n c hread hbs rfl hshr hmod
    have hpos : ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat < 2 ^ 63 := by
      rw [signExtend_self_toNat, handv']
      have hle : 64 * c.shr.toNat ≤ n.toNat := by
        rw [hshr, ushr_six_toNat]
        have := Nat.div_mul_le_self n.toNat 64
        omega
      omega
    let A : State := stateAt (peelEntryEnv env c andv)
      { s with pc := "if.then103", pre := some "for.end101" }
    let v : IfThen103Values := ifThen103Values n c.b
      ((docBlock bs c.shr.toNat).take 32) ((docBlock bs c.shr.toNat).drop 32)
      (List.replicate 4 0) c.st0 c.st9 c.st15 c.prevS andv c.shr c.ent conv 1
    have hden := for_end101_peel_denote env s c n andv conv
      ((docBlock bs c.shr.toNat).take 32) ((docBlock bs c.shr.toNat).drop 32)
      h hn hconv hand hpos (by rw [h.mem]; exact h136) (by rw [h.mem]; exact h137)
      hshr63
    have hbn := hsilent v rfl
    have hstep2 : step (s1BlocksCallsEsc esc) s1BlocksFunction A =
        .jump (stateAt (ifThen103Out (peelEntryEnv env c andv) v)
          { s with mem := writeBytes s.mem v.arrayidx (natToBytes v.and137.toNat 8),
                   pc := "if.end147", pre := some "if.then103" }) := by
      have hfind103 : s1BlocksFunction.findBlock A.pc = some if_then103Block := by
        rw [show A.pc = "if.then103" from rfl]
        exact LeanLLVM.Refinement.JsonS1BlocksIR.findBlock_if_then103
      rw [step_esc_of_free esc s1BlocksFunction _ _ hfind103 (by decide)]
      exact if_then103_step_end147 _ A v rfl hbn (by
        rw [show A = stateAt (peelEntryEnv env c andv)
            { s with pc := "if.then103", pre := some "for.end101" } from rfl]
        exact hden)
    have htail := tail_silent_run (esc := esc) (env := peelEntryEnv env c andv)
      A v (List.replicate 4 0) arm bs bs.length nb gate
      (lookupName_ifThen103Out_u8k _ v (lookupName_peelEntryEnv_u8k env c andv))
      (lookupName_ifThen103Out_arm _ v (lookupName_peelEntryEnv_of env c andv harm
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)))
      (evalICmp_eq_zero_of_and_two_zero arm hgateZero)
      (hstagePeel v rfl)
    exact ⟨1 + (1 + 3), _, _, by unfold exitCharge; omega, by
      rw [runFuel_jump_prefix hstep1 (1 + 3), runFuel_jump_prefix hstep2 3]
      exact (by simpa only [A, stateAt] using htail.1), htail.2⟩

/-! ### The exit's charge inside the budget -/

/-- **The exit's charge fits in the budget's room above the prefix.**  The
prefix's exposed charge is `8 * (%n >>> 6) + 21` and the budget is
`8 * blocksOf (%n) + 32`; the shift is at most the block count
(`JsonS1BlocksPrefixFuel.shift_le_blocksOf`), so at least `11` steps are left for
the exit — more than `exitCharge`'s `5`, whatever the document's alignment. -/
theorem exitCharge_le_room {args : List Value} {mem : Mem} {b ent xp nxp xcarry : Nat}
    {n : BitVec 64} {arm : BitVec 64}
    (hargs : args = [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp, .ptr xcarry,
      .int 64 arm]) :
    exitCharge ≤ s1BlocksBudget args mem - (8 * (n >>> 6).toNat + 21) := by
  have hbound := JsonS1BlocksPrefixFuel.prefixCharge_le_budget (args := args)
    (mem := mem) (b := b) (ent := ent) (xp := xp) (nxp := nxp) (xcarry := xcarry)
    (n := n) (arm := arm) hargs
  have hshift := JsonS1BlocksPrefixFuel.shift_le_blocksOf n
  have hbudget : s1BlocksBudget args mem = 8 * blocksOf n.toNat + 32 := by
    rw [hargs, s1BlocksBudget]
    simp only [s1BlocksLength]
  unfold exitCharge
  omega

/-! ### The run at the record's budget

The entry-to-exit segment and the exit's own run compose.  The segment's fuel is
bounded by the prefix's charge and the exit's by `exitCharge`; both charges are
inside the budget, so the joined run completes at `s1BlocksBudget` at the exit's
outcome. -/

/-- **The run at the budget, from a charged prefix and a charged exit.**  The
prefix segment from the record's own allocator base reaches the exit's terminal
at `N ≤ 8 * (%n >>> 6) + 21`, and the exit reaches the return from that terminal
at `jE ≤ exitCharge`.  `prefixCharge_le_budget` puts the first inside the budget
and `exitCharge_le_room` the second inside the room above it, so the joined run
completes at `s1BlocksBudget`, at the exit's own `ret` and memory. -/
theorem s1BlocksRun_at_budget_of_chargedStages {esc : Calls} {args : List Value}
    {mem : Mem} {next : Nat} {b ent xp nxp xcarry : Nat} {n : BitVec 64}
    {conv : BitVec 32} {arm ret : BitVec 64} {M : Mem} {e : State} {N jE : Nat}
    (hargs : args = [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp, .ptr xcarry,
      .int 64 arm])
    (hN : N ≤ 8 * (n >>> 6).toNat + 21)
    (htrace : ∀ k, runFuel (s1BlocksCallsEsc esc) (N + k) s1BlocksFunction
      (EntryState s1BlocksFunction args mem next) =
        runFuel (s1BlocksCallsEsc esc) k s1BlocksFunction e)
    (hjE : jE ≤ exitCharge)
    (hexit : runFuel (s1BlocksCallsEsc esc) jE s1BlocksFunction e =
      some (.ret (some (.int 64 ret)) M)) :
    runFuel (s1BlocksCallsEsc esc) (s1BlocksBudget args mem) s1BlocksFunction
        (EntryState s1BlocksFunction args mem next) = some (.ret (some (.int 64 ret)) M) := by
  have hbudget := JsonS1BlocksPrefixFuel.prefixCharge_le_budget (args := args)
    (mem := mem) (b := b) (ent := ent) (xp := xp) (nxp := nxp) (xcarry := xcarry)
    (n := n) (arm := arm) hargs
  have hroom := exitCharge_le_room (args := args) (mem := mem) (b := b) (ent := ent)
    (xp := xp) (nxp := nxp) (xcarry := xcarry) (n := n) (arm := arm) hargs
  have hexit' : runFuel (s1BlocksCallsEsc esc) exitCharge s1BlocksFunction e =
      some (.ret (some (.int 64 ret)) M) := runFuel_mono_le hjE hexit
  refine runFuel_mono_le ?_ (runFuel_prefix_some htrace hexit')
  omega

/-- **The run at the budget, from the committed prefix and a charged exit.**  The
record's allocator base at `next = 1` is `s1BlocksInit`, so the charged prefix
`JsonS1BlocksPrefixFuel.OnePrefixBounded` gives the segment outright, and the run
is `s1BlocksRun_at_budget_of_chargedStages` at that entry state.  This is the
statement a consumer of the committed prefix reads: the only input left is the
exit's charged run at the segment's terminal. -/
theorem s1BlocksRun_at_budget_of_chargedExit {esc : Calls} {args : List Value}
    {mem : Mem} {b ent xp nxp xcarry : Nat} {n : BitVec 64} {conv : BitVec 32}
    {arm ret : BitVec 64} {M : Mem} {e : State} {jE : Nat}
    (hargs : args = [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp, .ptr xcarry,
      .int 64 arm])
    (hprefix : JsonS1BlocksPrefixFuel.OnePrefixBounded esc args mem b n conv arm)
    (hjE : jE ≤ exitCharge)
    (hexit : ∀ e' : State, ExitTermCells b n conv arm e' →
      runFuel (s1BlocksCallsEsc esc) jE s1BlocksFunction e' =
        some (.ret (some (.int 64 ret)) M)) :
    runFuel (s1BlocksCallsEsc esc) (s1BlocksBudget args mem) s1BlocksFunction
        (EntryState s1BlocksFunction args mem 1) = some (.ret (some (.int 64 ret)) M) := by
  obtain ⟨e', N, hN, htrace, hterm⟩ := hprefix
  refine s1BlocksRun_at_budget_of_chargedStages (args := args) (mem := mem) (next := 1)
    (b := b) (ent := ent) (xp := xp) (nxp := nxp) (xcarry := xcarry) (n := n)
    (conv := conv) (arm := arm) (ret := ret) (M := M) (e := e') (N := N) (jE := jE)
    hargs hN ?_ hjE (hexit e' hterm)
  intro k
  rw [← s1BlocksInit_entryState]
  exact htrace k

/-! ### Axiom footprints

The two charged exits are the committed exit compositions' own block tests and
tail-arm step lemmas, composed by `runFuel`'s prefix rule and closed by
arithmetic; the charge's containment is `shift_le_blocksOf` and the budget's
definition; the joined run is `runFuel`'s prefix composition, its monotonicity
and the two charges' arithmetic.  No statement reaches `sorryAx`. -/

#print axioms LeanLLVM.Refinement.JsonS1BlocksExitFuel.exitCharge
#print axioms LeanLLVM.Refinement.JsonS1BlocksExitFuel.fusedExitCells_charged
#print axioms LeanLLVM.Refinement.JsonS1BlocksExitFuel.asciiExitCells_charged
#print axioms LeanLLVM.Refinement.JsonS1BlocksExitFuel.exitCharge_le_room
#print axioms LeanLLVM.Refinement.JsonS1BlocksExitFuel.s1BlocksRun_at_budget_of_chargedStages
#print axioms LeanLLVM.Refinement.JsonS1BlocksExitFuel.s1BlocksRun_at_budget_of_chargedExit

end LeanLLVM.Refinement.JsonS1BlocksExitFuel
