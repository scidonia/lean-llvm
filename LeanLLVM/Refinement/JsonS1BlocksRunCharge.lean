/-
The run frame's charge, and the tail's third disjunct at the record's budget.

`JsonS1BlocksRunFrame.loopRun_frame` bounds the loop's calling run by
`5 * (%shr - (%i + 1)) + 5` and ends at `for.end101` with a `RunFrame`, and
`JsonS1BlocksRunFrame.tail_third_of_frame` reads that bundle as `S1BlocksTail`'s
calling disjunct.  Neither states the loop's place in `s1BlocksBudget`, and the
tail's disjunct is stated at the peel's own memory, so nothing in the tree yet
joins the run's completion and the tail at the record's fuel.

## The charges

The committed decomposition charges the phase — the entry, the preheader and the
ASCII loop — at `3 * %shr + 8` (`JsonS1BlocksPrefixFuel.s1BlocksPrefix_stream_bounded`)
and the fused loop at `5 * (%shr - (%i + 1)) + 5`; with the partial block's exit
`%shr + 1 = blocksOf bs.length`, `JsonS1BlocksEntry.entry_charge_sum` puts
`3 * (blocks - 1) + 4` and the loop's charge inside `8 * blocksOf + 32`.  The
segment from the phase's terminal to the fused loop's head is the hand-off's two
steps and the first page's `k ≤ 5`
(`JsonS1BlocksPrefixFuel.handoffPrefix_exit_bounded`'s `2 + (k + (1 + j))`),
`7`; so `3 * %shr + 15` is the prefix's charge at that head, and the phase's
`3 * %shr + 8` is the committed half of it.  This module adds the calling arm's
exit: `for.end101`'s step, `if.then103`'s store and `tail_escape_run`'s four,
`6`.  That is one above `JsonS1BlocksExitFuel.exitCharge`: the silent merge's
five leaves the peel's escape call out (`JsonS1BlocksExitFuel`'s header), and the
calling arm takes it — `escapeExitCharge` is `exitCharge + 1`.

The arithmetic is `runFrameCharge_le_budget`: the prefix's `3 * %shr + 15`, the
loop's `5 * (%shr - (%i + 1)) + 5` and the exit's `escapeExitCharge` are inside
`s1BlocksBudget`.  The room above the committed phase and loop charges is `27`
steps at the loop's largest charge, and the hand-off's seven and the exit's six
spend thirteen of them, leaving `14`.

## The composition

`s1BlocksRun_at_budget_of_frame` states the run at the record's budget for the
calling arm.  Its three segments are the caller's:

* the prefix, from `EntryState` at the caller's `next` to the loop's head
  `stateAt env s`, at the phase's committed `3 * %shr + 8` plus the hand-off's
  two steps and the first page's `k ≤ 5`, `3 * %shr + 15`;
* the loop, from that head to `for.end101`, at `loopRun_frame`'s own bound;
* the exit, from `for.end101` to the return at `M`, at `escapeExitCharge`.

`runFuel_prefix_trans` joins the first two and `runFuel_prefix_some` the third;
`runFuel_mono_le` lifts the completed run to `s1BlocksBudget`.  The same exit
memory `M` is the peel's, so the theorem's second conjunct is
`tail_third_of_frame`'s `S1BlocksTail` at `M` — the tail and the run's
completion at one witness, which is the shape the bundle's tail field reads.

## What remains

The theorem's premises are the unit's post and the caller's staging, not fuel:

* **The loop's trace and charge** (`hloop`, `hj`): `loopRun_frame` produces both
  from the head's `LoopInv` and `FrameCarry`; a caller obtains them by
  destructing its conclusion, and the theorem is stated at that exit so the
  tail's disjunct and the exit's run share `M`.
* **The prefix's charge at the loop's head** (`hprefixLe`): `3 * %shr + 15` is
  the committed phase charge `3 * %shr + 8`
  (`JsonS1BlocksPrefixFuel.s1BlocksPrefix_stream_bounded`) plus the hand-off's
  two steps and the first page's `k ≤ 5`.  The committed pieces are
  `handoffPrefix_exit_bounded`'s `2 + (k + (1 + j))`; the split at the fused
  loop's head — before the latch's `1` — is not itself a committed statement,
  so the caller composes the two bounds.
* **The peel's escape record** (`hreach`, `hor`, `hshrEq`, `hand`, `hw`):
  `EscapeReach` at the peel's slot for the calling arm, the peel's word at the
  model's last block, and the classifier's arithmetic.  These are the escape
  unit's post at the peel, as on every page.
* **The document and the staged zeroes at the peel's call**: the peel's
  `EscapeReach` is stated at the memory `if.then103`'s store leaves, and the
  record's frame does not restate the document window.  The caller's staging
  supplies both, as it does for the loop's pages (`hkeep` in `loopRun_frame`).
* **The loop's exit base** (`hentExit`): neither `RunFrame` nor
  `loopRun_frame`'s conclusion states that the loop pages preserve the entry
  base.  `JsonS1BlocksRunFrame.loopPage_zero` proves `c'.ent = c.ent` on one
  page, but the induction's bundle does not carry the equality to the exit, so
  a consumer must supply `c.ent = ent` at its own exit carry.  That is the one
  premise here that a committed theorem does not yet produce.
-/
import LeanLLVM.Refinement.JsonS1BlocksRunFrame
import LeanLLVM.Refinement.JsonS1BlocksExitFuel

namespace LeanLLVM.Refinement.JsonS1BlocksRunCharge

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksExitFuel
open LeanLLVM.Refinement.JsonS1BlocksSatisfies
open LeanLLVM.Refinement.JsonS1BlocksSeparation
open LeanLLVM.Refinement.JsonS1BlocksLoop
open LeanLLVM.Refinement.JsonS1BlocksEscapeRun
open LeanLLVM.Refinement.JsonS1BlocksRecordFrame
open LeanLLVM.Refinement.JsonS1BlocksRunFrame

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### The calling arm's exit charge -/

/-- **The calling arm's exit charge.**  From `for.end101`: the exit block's step,
`if.then103`'s store, and `tail_escape_run`'s four (`JsonS1BlocksRefines`).  The
silent merge's `exitCharge` is five because it takes no call; the calling arm's
fourth tail step is the escape unit. -/
def escapeExitCharge : Nat := exitCharge + 1

/-- The calling arm's charge covers the silent arm's committed charge. -/
theorem exitCharge_le_escapeExitCharge : exitCharge ≤ escapeExitCharge := by
  unfold escapeExitCharge
  omega

/-- The calling arm's charge is `1 + 1 + 4`. -/
theorem escapeExitCharge_eq_six : escapeExitCharge = 6 := by
  unfold escapeExitCharge exitCharge
  rfl

/-! ### The charge inside the record's budget

The committed sum `entry_charge_sum` is the phase's `3` per block plus `4` and
the loop's `5 * (%shr - (%i + 1)) + 5`; the exit's constant is added here.  The
budget's `8 * blocksOf + 32` leaves room, so nothing about the document's
alignment enters besides `%shr + 1 = blocksOf`. -/

/-- **The run frame's charge is inside the record's budget.**  With the partial
block's `%shr + 1 = blocksOf bs.length`, the prefix's `3 * %shr + 15` (the
committed phase charge `3 * %shr + 8` plus the hand-off's two steps and the
first page's five), the loop's `5 * (%shr - (%i + 1)) + 5` and the calling arm's
`escapeExitCharge` sit inside `s1BlocksBudget`'s `8 * blocksOf bs.length + 32`.
The slack is `14` steps at the loop's largest charge, so neither the hand-off's
constants nor the document's alignment is tight. -/
theorem runFrameCharge_le_budget {args : List Value} {mem : Mem}
    {b ent xp nxp xcarry : Nat} {arm : BitVec 64} {bs : List UInt8}
    {shr i j jE : Nat}
    (hargs : args = [.ptr b, .int 64 (BitVec.ofNat 64 bs.length), .ptr ent,
      .ptr xp, .ptr nxp, .ptr xcarry, .int 64 arm])
    (hn : (BitVec.ofNat 64 bs.length).toNat = bs.length)
    (hblocks : shr + 1 = blocksOf bs.length)
    (hj : j ≤ 5 * (shr - (i + 1)) + 5)
    (hjE : jE ≤ escapeExitCharge) :
    3 * shr + 15 + j + jE ≤ s1BlocksBudget args mem := by
  have hbudget : s1BlocksBudget args mem = 8 * blocksOf bs.length + 32 := by
    rw [hargs]
    simp only [s1BlocksBudget, s1BlocksLength]
    rw [hn]
  simp only [escapeExitCharge, exitCharge] at hjE
  omega

/-! ### The run at the budget, and the tail at its memory

The prefix's segment ends at the loop's head; the loop's segment is
`loopRun_frame`'s; the exit's is the caller's run from `for.end101` at the
calling arm's charge.  The exit's memory is the peel's, so `tail_third_of_frame`
supplies the tail at the same witness as the run's completion. -/

/-- **The run at `s1BlocksBudget`, and the tail at its memory.**  From the
prefix to the loop's head at `3 * %shr + 15` (the committed phase charge
`3 * %shr + 8` plus the hand-off's two steps and the first page's five), the
loop's own segment at `5 * (%shr - (%i + 1)) + 5`, and the calling arm's exit at
`escapeExitCharge`, the run at `s1BlocksBudget` completes at the exit's `ret`
and `M`, and the tail's third disjunct holds at that same `M`.  The loop's exit
is given explicitly, so `loopRun_frame`'s conclusion is destructed into these
hypotheses and the tail's reach is stated at the peel's own slot. -/
theorem s1BlocksRun_at_budget_of_frame {esc : Calls} {args : List Value} {mem : Mem}
    {next : Nat} {b ent xp xn nxp xcarry : Nat} {arm : BitVec 64}
    {bs : List UInt8} {env : Env} {s e : State} {cE : FusedCarry}
    {ps : List Nat} {start : Mem} {count pages N i shr j jE : Nat}
    {ret : BitVec 64} {M : Mem}
    {or135 andv w blk0 : BitVec 64} {position : List Nat} {opened ppar : Bool}
    (hargs : args = [.ptr b, .int 64 (BitVec.ofNat 64 bs.length), .ptr ent,
      .ptr xp, .ptr nxp, .ptr xcarry, .int 64 arm])
    (hn : (BitVec.ofNat 64 bs.length).toNat = bs.length)
    (hmem : start = mem)
    (hprefix : ∀ k, runFuel (s1BlocksCallsEsc esc) (N + k) s1BlocksFunction
      (EntryState s1BlocksFunction args mem next) =
        runFuel (s1BlocksCallsEsc esc) k s1BlocksFunction (stateAt env s))
    (hprefixLe : N ≤ 3 * shr + 15)
    (hloop : ∀ k, runFuel (s1BlocksCallsEsc esc) (j + k) s1BlocksFunction
      (stateAt env s) = runFuel (s1BlocksCallsEsc esc) k s1BlocksFunction e)
    (hblocks : shr + 1 = blocksOf bs.length)
    (hj : j ≤ 5 * (shr - (i + 1)) + 5)
    (hframe : RunFrame start xp xn nxp xcarry ps bs cE count pages)
    (hshr : shr = cE.i.toNat)
    (hor : PeelWordAtModel or135 bs shr)
    (hshrEq : shr = ((BitVec.ofNat 64 bs.length) >>> 6).toNat)
    (hand : andv = (BitVec.ofNat 64 bs.length) &&& 0x000000000000003f#64)
    (hw : w = or135 &&& limMask andv.toNat)
    (harm : arm &&& 2 ≠ (0 : BitVec 64))
    (hreach : EscapeReach blk0 xp nxp xcarry count position
      (flagBytes opened ++ flagBytes ppar)
      (writeBytes cE.mem (cE.ent + 8 * shr) (natToBytes w.toNat 8)) M)
    (hlen : position.length ≤ 64)
    (hxpSep : cE.ent + 8 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ cE.ent)
    (hentExit : cE.ent = ent)
    (hjE : jE ≤ escapeExitCharge)
    (hret : runFuel (s1BlocksCallsEsc esc) jE s1BlocksFunction e =
      some (.ret (some (.int 64 ret)) M)) :
    runFuel (s1BlocksCallsEsc esc) (s1BlocksBudget args mem) s1BlocksFunction
        (EntryState s1BlocksFunction args mem next) = some (.ret (some (.int 64 ret)) M) ∧
      S1BlocksTail mem ent xp nxp xcarry xn arm bs M := by
  have hcharge := runFrameCharge_le_budget (args := args) (mem := mem) (b := b)
    (ent := ent) (xp := xp) (nxp := nxp) (xcarry := xcarry) (arm := arm)
    (bs := bs) (shr := shr) (i := i) (j := j) (jE := jE)
    hargs hn hblocks hj hjE
  have hbudget : N + j + jE ≤ s1BlocksBudget args mem := by omega
  have htail : S1BlocksTail start cE.ent xp nxp xcarry xn arm bs M :=
    tail_third_of_frame (hrun := hframe) (hshr := hshr) (hor := hor)
      (hshrEq := hshrEq) (hand := hand) (hw := hw) (harm := harm)
      (hreach := hreach) (hlen := hlen) (hxpSep := hxpSep)
  refine ⟨?_, ?_⟩
  · have hcomp : ∀ k, runFuel (s1BlocksCallsEsc esc) (N + j + k)
        s1BlocksFunction (EntryState s1BlocksFunction args mem next) =
          runFuel (s1BlocksCallsEsc esc) k s1BlocksFunction e :=
      runFuel_prefix_trans hprefix hloop
    exact runFuel_mono_le hbudget (runFuel_prefix_some hcomp hret)
  · rw [hentExit, hmem] at htail
    exact htail

/-! ### Axiom footprints

`escapeExitCharge` and its two readings are `JsonS1BlocksExitFuel.exitCharge`'s
definition; `runFrameCharge_le_budget` is the budget's definition and the
committed phase, loop and exit charges' arithmetic; the composed run is
`runFuel_prefix_trans`, `runFuel_prefix_some` and `runFuel_mono_le`; the tail is
`JsonS1BlocksRunFrame.tail_third_of_frame`, which reports `Classical.choice` for
the peel's slot projection and the store arithmetic `omega` discharges.  No
statement reaches `sorryAx`. -/

#print axioms LeanLLVM.Refinement.JsonS1BlocksRunCharge.escapeExitCharge
#print axioms LeanLLVM.Refinement.JsonS1BlocksRunCharge.exitCharge_le_escapeExitCharge
#print axioms LeanLLVM.Refinement.JsonS1BlocksRunCharge.escapeExitCharge_eq_six
#print axioms LeanLLVM.Refinement.JsonS1BlocksRunCharge.runFrameCharge_le_budget
#print axioms LeanLLVM.Refinement.JsonS1BlocksRunCharge.s1BlocksRun_at_budget_of_frame

end LeanLLVM.Refinement.JsonS1BlocksRunCharge
