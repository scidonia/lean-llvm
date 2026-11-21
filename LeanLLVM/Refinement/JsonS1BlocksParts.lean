/-
The block unit's run parts at the real call, with the exit charged for the arm
that calls.

`JsonS1BlocksFinalAt.S1BlocksRunPartsAt` names the parts at the peel's own call,
but its `exitBounded` field fixes two things that the calling arm cannot supply:

* the charge is `exitCharge` (`5`, the silent merge).  On `arm &&& 2 ≠ 0` the
  exit from a `for.end101` terminal is that block's step, `if.then103`'s store
  and `tail_escape_run`'s four (`JsonS1BlocksRefines`, `runFuel ... 4`), `6` —
  `JsonS1BlocksRunCharge.escapeExitCharge`, `escapeExitCharge_eq_six`.  The
  committed silent exits (`JsonS1BlocksExitFuel.fusedExitCells_charged`,
  `asciiExitCells_charged`) are stated at `arm &&& 2 = 0` and return at
  `VerdictPost`, not at the peel's outcome, so they cannot fill the field.
* the terminal is universally quantified with a single `ret`/`out.mem`.
  Distinct `ExitTermCells` states carry distinct `FusedCarry` memories, so no
  one memory is every terminal's return; `S1BlocksResiduals` only ever reads the
  exit at the prefix's own terminal.

This module is the corrected interface.  `S1BlocksRunPartsAt` bundles the run as
one `∃` over the exit terminal, so the prefix's witness and the exit's run share
`e`, `M` and the charge; the prefix half is the `OnePrefixBounded` shape that
`JsonS1BlocksHeadCompose.onePrefixBounded_of_arms` produces (at the caller's
base, so the phase's trace is read through `s1BlocksRun_entry_next`).  The
calling-arm prefix is a residual field: the committed phase producers
(`JsonS1BlocksPrefixFuel.s1BlocksPrefix_stream_bounded`,
`s1BlocksPrefix_exit_bounded`) carry the silent-arm
`hgate : evalICmp .eq (arm &&& 2) 0 = 1`, and `JsonS1BlocksRunCharge`'s head
trace is a hypothesis, so no committed theorem reaches the calling arm's
phase.

The staging and the returned word are `JsonS1BlocksPageModel`'s and
`JsonS1BlocksAccFold`'s: `staging_of_fusedExit` is
`exit_staging_of_fusedEnd` with the accumulator pack supplied by
`acc_pack_of_alignedExit`.  The tail is
`JsonS1BlocksUnitPost.tail_third_at_ent`'s third disjunct at the peel's own
reach, the position `JsonS1BlocksFinalAt.tail_calling_at_of_pre` produces from
the record's `pre`.

The remainder is `s1BlocksRun_at_budget_of_chargedEscapeExit`: the prefix's
`8 * (%n >>> 6) + 21` and the calling arm's `escapeExitCharge` are inside
`s1BlocksBudget` because the budget leaves `11` steps above the prefix's charge
(`JsonS1BlocksPrefixFuel.shift_le_blocksOf`).  `s1BlocksFacts_of_partsAt` packs
`S1BlocksFacts`, and `s1_blocks_satisfies_of_partsAt` /
`s1_blocks_refines_of_partsAt` are `s1_blocks_satisfies` and
`s1_blocks_refines_of_satisfies` at the unchanged statements.

## What is assumed, and what is proved

The residual is exactly `s1BlocksRunPartsAt_of_components`'s hypothesis list, and
nothing in it is a promise the record's `pre` does not already make except the
run itself:

* **The calling arm's run** (`htrace`, `hN`, `hterm`, `hjE`, `hexit`): the
  entry-to-exit trace from the caller's base, its `8 * (%n >>> 6) + 21` bound,
  the exit terminal's cells, and the exit's `escapeExitCharge` run to `ret`/`M`.
  The committed phase producers
  (`JsonS1BlocksPrefixFuel.s1BlocksPrefix_stream_bounded`,
  `s1BlocksPrefix_exit_bounded`) carry the silent-arm
  `hgate : evalICmp .eq (arm &&& 2) 0 = 1`, so the calling arm's prefix is this
  module's residual interface field; the exit's *shape* is
  `JsonS1BlocksRunCharge.s1BlocksRun_at_budget_of_frame`'s `hret`, corrected to
  the terminal the prefix actually reaches.
* **The staging's inputs** (`hfusedExit`, the two lane lengths, `hascii`,
  `hcarry`, `hic`, `herr`): `PageModel.exit_staging_of_fusedEnd`'s and
  `AccFold.acc_pack_of_alignedExit`'s premises, not the staging itself.
* **The peel and the tail** (`hrunFrame`, `hent`, `hshr`, `hor`, `hshrEq`,
  `hand`, `hw`, `harm`, `hreach`, `hlen`, `hxpSep`): the loop lane's exit frame
  and word, and the record's reach at the peel's own call
  (`JsonS1BlocksFinalAt.tail_calling_at_of_pre`'s conclusion).  The peel's
  `pre` at its own vector is that theorem's input and is not restated here.
* **The base invariance** (`hIrr : CallsNextIrr esc`) and the word equality
  (`hret`), which ties the exit's return to the staging's `verdictWord`.

What is not assumed: the staging (`staging_of_fusedExit`), the tail
(`tail_third_at_ent`), the prefix's `OnePrefixBounded` shape
(`onePrefixBounded_of_partsAt`, through `s1BlocksRun_entry_next`), the run at
`s1BlocksBudget` (`s1BlocksRun_at_budget_of_chargedEscapeExit`), the bundle, the
record instance and the refinement.

`JsonS1BlocksFacts.S1BlocksResiduals` carries the same `jE ≤ exitCharge` as the
FinalAt field, and `JsonS1BlocksFacts.run_of_residuals` composes through
`JsonS1BlocksExitFuel.s1BlocksRun_at_budget_of_chargedStages`, so that path is
the silent-arm path too; this module's composition is the one the calling arm
needs.

## Axiom footprints

The corrected composition is `runFuel`'s prefix rule and monotonicity plus the
budget's definition and `shift_le_blocksOf`; the staging is
`JsonS1BlocksPageModel.exit_staging_of_fusedEnd` and
`JsonS1BlocksAccFold.acc_pack_of_alignedExit`; the tail is
`JsonS1BlocksUnitPost.tail_third_at_ent` (`Classical.choice` for the peel's slot
projection); the instance is `JsonS1BlocksSatisfies.s1_blocks_satisfies` and
`JsonS1BlocksFacts.s1_blocks_refines_of_satisfies`.  No statement reaches
`sorryAx`.
-/
import LeanLLVM.Refinement.JsonS1BlocksFinalAt
import LeanLLVM.Refinement.JsonS1BlocksAccFold
import LeanLLVM.Refinement.JsonS1BlocksRunCharge
import LeanLLVM.Refinement.JsonS1BlocksPageModel
import LeanLLVM.Refinement.JsonS1BlocksStream
import LeanLLVM.Refinement.JsonS1BlocksHeadCompose

namespace LeanLLVM.Refinement.JsonS1BlocksParts

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1BlocksRefines
open LeanLLVM.Refinement.JsonS1BlocksLoop
open LeanLLVM.Refinement.JsonS1BlocksSatisfies
open LeanLLVM.Refinement.JsonS1BlocksVerdict
open LeanLLVM.Refinement.JsonS1BlocksPrefix
open LeanLLVM.Refinement.JsonS1BlocksPrefixFuel
open LeanLLVM.Refinement.JsonS1BlocksExitFuel
open LeanLLVM.Refinement.JsonS1BlocksFacts
open LeanLLVM.Refinement.JsonS1BlocksRunFrame
open LeanLLVM.Refinement.JsonS1BlocksRecordFrame
open LeanLLVM.Refinement.JsonS1BlocksEscapeRun
open LeanLLVM.Refinement.JsonS1BlocksLoopRun
open LeanLLVM.Refinement.JsonS1BlocksPageModel
open LeanLLVM.Refinement.JsonS1BlocksAccFold
open LeanLLVM.Refinement.JsonS1BlocksFinal
open LeanLLVM.Refinement.JsonS1BlocksUnitPost
open LeanLLVM.Refinement.JsonS1BlocksRunCharge
open LeanLLVM.Refinement.JsonS1BlocksHeadCompose
open LeanLLVM.Refinement.JsonS1BlocksStaging
open LeanLLVM.Refinement.JsonS1BlocksStream
open LeanLLVM.Refinement.JsonUtf8Spec

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### The staging at the exit carry

The two committed halves of the exit's staging: `PageModel`'s
`exit_staging_of_fusedEnd` reads the classifier's gate and the error bit, and
`AccFold`'s `acc_pack_of_alignedExit` supplies the accumulator's pack from the
carry's `AccCarry` at the document's block count. -/

/-- **The staging at a fused exit.**  `exit_staging_of_fusedEnd` with its
accumulator pack discharged by `acc_pack_of_alignedExit` at
`c.i.toNat = blocksOf bs.length`.  The returned error bit is the emitted
`%cmp155`/`%or169500` reading. -/
theorem staging_of_fusedExit {bs : List UInt8} {env : Env} {s : State}
    {c : FusedCarry} {gate : Bool}
    (hexit : FusedExit env s c)
    (hasciiLen : c.ascii.length = 4) (hu8kLen : c.u8k.length = 4)
    (hascii : packLanes c.ascii = bytesToNat (asciiAcc bs (blocksOf bs.length)))
    (hcarry : AccCarry bs c)
    (hi : c.i.toNat = blocksOf bs.length)
    (herr : evalICmp .eq (ptestzU8k c.u8k) 0 = 1 ↔
      ¬ (c.u8k.all (fun x => decide (x = 0x00)) = true) ∨
        (bs.length ≠ 0 ∧ klTailByte (klByte bs (bs.length - 1)) = true)) :
    VerdictStaging c.ascii c.u8k bs bs.length (blocksOf bs.length) gate
      (evalICmp .eq (ptestzU8k c.u8k) 0) :=
  exit_staging_of_fusedEnd hexit hasciiLen hu8kLen hascii
    (acc_pack_of_alignedExit hcarry rfl hi) herr

/-! ### The parts at the real call

The run is one `∃` over its exit terminal: the prefix's bound, the trace from
the caller's entry, the terminal's cells, and the exit's charged run to the same
memory.  Naming them together is what removes `JsonS1BlocksFinalAt`'s universal
exit: the exit is read at the terminal the prefix reaches, at the calling arm's
charge. -/

/-- **The run's parts at the peel's call, corrected.**  The prefix's bound is
`OnePrefixBounded`'s `8 * (%n >>> 6) + 21`; the exit is the calling arm's
`escapeExitCharge` at the prefix's own terminal (`e`, `N`, `jE` are one `∃`).
The staging, the returned word and the tail are the committed shapes at the
run's own `M`. -/
structure S1BlocksRunPartsAt (esc : Calls) (args : List Value) (mem : Mem)
    (next b ent xp nxp xcarry xn : Nat) (arm : BitVec 64) (bs : List UInt8) where
  /-- The caller's escape selection answers the same at every allocator base. -/
  nextIrr : CallsNextIrr esc
  /-- The returned word. -/
  ret : BitVec 64
  /-- The run's memory. -/
  M : Mem
  /-- The staging's ASCII word. -/
  ascii : List (BitVec 64)
  /-- The staging's UTF-8 word. -/
  u8k : List (BitVec 64)
  /-- The staging's error bit. -/
  err : BitVec 1
  /-- The classifier's gate. -/
  gate : Bool
  /-- The staging at the document's block count
  (`staging_of_fusedExit`, `JsonS1BlocksPageModel.exit_staging_of_loopCarry`). -/
  staging : VerdictStaging ascii u8k bs bs.length (blocksOf bs.length) gate err
  /-- The returned word is the staging's. -/
  word : ret = verdictWord ascii err
  /-- The entry-to-exit prefix and the exit at its own terminal.  The prefix's
  half is the shape `JsonS1BlocksHeadCompose.onePrefixBounded_of_arms` produces;
  the exit's charge is `escapeExitCharge`, not the silent `exitCharge`. -/
  runBounded : ∃ (e : State) (N jE : Nat),
    N ≤ 8 * ((BitVec.ofNat 64 bs.length) >>> 6).toNat + 21 ∧
      (∀ k, runFuel (s1BlocksCallsEsc esc) (N + k) s1BlocksFunction
          (EntryState s1BlocksFunction args mem next) =
        runFuel (s1BlocksCallsEsc esc) k s1BlocksFunction e) ∧
      ExitTermCells b (BitVec.ofNat 64 bs.length) (entryGate arm) arm e ∧
      jE ≤ escapeExitCharge ∧
      runFuel (s1BlocksCallsEsc esc) jE s1BlocksFunction e =
        some (.ret (some (.int 64 ret)) M)
  /-- The tail's shape at the run's memory. -/
  tail : S1BlocksTail mem ent xp nxp xcarry xn arm bs M

/-! ### The prefix's shape

`JsonS1BlocksHeadCompose.onePrefixBounded_of_arms` produces the bounded
one-prefix from the phase's trace, its terminal and the hand-off carries.  The
parts' run starts at the caller's base, so the trace is moved to
`s1BlocksInit` by `s1BlocksRun_entry_next`. -/

/-- **The prefix's `OnePrefixBounded`, from the parts.**  The parts' run
decomposition is the prefix's trace and terminal at the caller's base; the
selection's base invariance (`nextIrr`) and the body's allocator-freeness move
it to `s1BlocksInit`, which is the shape `onePrefixBounded_of_arms` produces. -/
theorem onePrefixBounded_of_partsAt {esc : Calls} {args : List Value}
    {mem : Mem} {next b ent xp nxp xcarry xn : Nat} {arm : BitVec 64}
    {bs : List UInt8}
    (hargs : args = [.ptr b, .int 64 (BitVec.ofNat 64 bs.length), .ptr ent,
      .ptr xp, .ptr nxp, .ptr xcarry, .int 64 arm])
    (h : S1BlocksRunPartsAt esc args mem next b ent xp nxp xcarry xn arm bs) :
    OnePrefixBounded esc args mem b (BitVec.ofNat 64 bs.length) (entryGate arm) arm := by
  obtain ⟨e, N, _, hN, htrace, hterm, _, _⟩ := h.runBounded
  refine ⟨e, N, hN, ?_, hterm⟩
  intro k
  have h1 := htrace k
  rw [hargs] at h1
  rw [s1BlocksRun_entry_next h.nextIrr (N + k)] at h1
  simpa only [s1BlocksInit_entryState, hargs] using h1

/-- **The prefix from the phase's arms, at the block's arguments.**
`JsonS1BlocksHeadCompose.onePrefixBounded_of_arms` at `args`: the phase's trace,
its terminal and the hand-off carries are that theorem's inputs, and its
`OnePrefixBounded` is the shape the parts' prefix half has.  The calling arm's
phase is not a committed producer (`hgate` is the silent arm's), so this is the
point at which a caller that has the calling arm's phase supplies it. -/
theorem onePrefixBounded_of_armsAt {esc : Calls} {args : List Value} {mem : Mem}
    {b ent xp nxp xcarry : Nat} {n arm : BitVec 64} {bs : List UInt8}
    {doc : Nat → List UInt8} {bs73 bs74 : List UInt8}
    (hargs : args = [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp, .ptr xcarry,
      .int 64 arm])
    (e : State) (N : Nat)
    (hphase : ∀ k, runFuel (s1BlocksCallsEsc esc) (N + k) s1BlocksFunction
      (s1BlocksInit args mem) = runFuel (s1BlocksCallsEsc esc) k s1BlocksFunction e)
    (hN : N ≤ 3 * (n >>> 6).toNat + 8)
    (hterm : AsciiTermStreamCells b n (entryGate arm) arm xp nxp xcarry e)
    (hshr57 : (n >>> 6).toNat < 2 ^ 57)
    (hb3 : 3 ≤ b)
    (hready : ∀ (env : Env) (s : State) (c : AsciiCarry) (bs2 bs3 : List UInt8)
      (v : ForBodyValues),
      AsciiInvCells env s c b n (entryGate arm) arm →
      StreamCells env xp nxp xcarry →
      readBytes c.mem (c.b + 64 * (c.i + 1).toNat) 32 = some bs2 →
      readBytes c.mem (c.b + 64 * (c.i + 1).toNat + 32) 32 = some bs3 →
      c.i + 1 ≠ c.shr →
      v = asciiValues c bs2 bs3 →
      HandoffCarries esc env s c bs2 bs3 v doc bs73 bs74 xp nxp xcarry) :
    OnePrefixBounded esc args mem b n (entryGate arm) arm := by
  rw [hargs] at hphase ⊢
  exact JsonS1BlocksHeadCompose.onePrefixBounded_of_arms (bs := bs) e N hphase
    hN hterm hshr57 hb3 hready

/-! ### The corrected composition at the budget

The prefix's `8 * (%n >>> 6) + 21` and the calling arm's `escapeExitCharge` are
the budget's `8 * blocksOf + 32`: the shift is at most the block count, so
`8 * shift + 27 ≤ 8 * blocksOf + 32`.  The committed
`JsonS1BlocksExitFuel.s1BlocksRun_at_budget_of_chargedStages` uses the silent
`exitCharge`; this is the same join at the arm the parts carry. -/

/-- **The run at the budget, from the prefix and the calling arm's exit.**  The
prefix reaches the exit's terminal at `N ≤ 8 * (%n >>> 6) + 21`, the exit
reaches the return at `jE ≤ escapeExitCharge`, and the two charges fit the
budget's `8 * blocksOf + 32`; the joined run completes at the exit's own `ret`
and memory. -/
theorem s1BlocksRun_at_budget_of_chargedEscapeExit {esc : Calls}
    {args : List Value} {mem : Mem} {next : Nat}
    {b ent xp nxp xcarry : Nat} {n : BitVec 64} {conv : BitVec 32}
    {arm ret : BitVec 64} {M : Mem} {e : State} {N jE : Nat}
    (hargs : args = [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp, .ptr xcarry,
      .int 64 arm])
    (hN : N ≤ 8 * (n >>> 6).toNat + 21)
    (htrace : ∀ k, runFuel (s1BlocksCallsEsc esc) (N + k) s1BlocksFunction
      (EntryState s1BlocksFunction args mem next) =
        runFuel (s1BlocksCallsEsc esc) k s1BlocksFunction e)
    (hjE : jE ≤ escapeExitCharge)
    (hexit : runFuel (s1BlocksCallsEsc esc) jE s1BlocksFunction e =
      some (.ret (some (.int 64 ret)) M)) :
    runFuel (s1BlocksCallsEsc esc) (s1BlocksBudget args mem) s1BlocksFunction
        (EntryState s1BlocksFunction args mem next) =
      some (.ret (some (.int 64 ret)) M) := by
  have hbudget : s1BlocksBudget args mem = 8 * blocksOf n.toNat + 32 := by
    rw [hargs, s1BlocksBudget]
    simp only [s1BlocksLength]
  have hshift := JsonS1BlocksPrefixFuel.shift_le_blocksOf n
  have hle : N + jE ≤ s1BlocksBudget args mem := by
    rw [hbudget]
    unfold escapeExitCharge exitCharge at hjE
    omega
  exact runFuel_mono_le hle (runFuel_prefix_some htrace hexit)

/-! ### The parts from the committed producers

The producer consumes the run's decomposition (the residual: the calling-arm
prefix's trace and the exit's charged run at that terminal), the exit carry's
staging inputs, and the peel's data.  The staging is
`staging_of_fusedExit` and the tail is `tail_third_at_ent`; nothing else is
assumed. -/

/-- **The run's parts, from the committed staging and tail.**  The run and the
exit are the residual at the caller's arguments; the staging is
`staging_of_fusedExit` (PageModel + AccFold) and the tail is
`JsonS1BlocksUnitPost.tail_third_at_ent` at the peel's own reach (the position
`JsonS1BlocksFinalAt.tail_calling_at_of_pre` produces from the record's `pre`).
The returned word is the staging's. -/
def s1BlocksRunPartsAt_of_components {esc : Calls} {args : List Value}
    {mem : Mem} {next b ent xp nxp xcarry xn : Nat} {arm : BitVec 64}
    {bs : List UInt8}
    (hargs : args = [.ptr b, .int 64 (BitVec.ofNat 64 bs.length), .ptr ent,
      .ptr xp, .ptr nxp, .ptr xcarry, .int 64 arm])
    (hIrr : CallsNextIrr esc)
    {e : State} {N jE : Nat} {M : Mem} {ret : BitVec 64}
    (hN : N ≤ 8 * ((BitVec.ofNat 64 bs.length) >>> 6).toNat + 21)
    (htrace : ∀ k, runFuel (s1BlocksCallsEsc esc) (N + k) s1BlocksFunction
      (EntryState s1BlocksFunction args mem next) =
        runFuel (s1BlocksCallsEsc esc) k s1BlocksFunction e)
    (hterm : ExitTermCells b (BitVec.ofNat 64 bs.length) (entryGate arm) arm e)
    (hjE : jE ≤ escapeExitCharge)
    (hexit : runFuel (s1BlocksCallsEsc esc) jE s1BlocksFunction e =
      some (.ret (some (.int 64 ret)) M))
    {env : Env} {s : State} {c : FusedCarry} {gate : Bool}
    (hfusedExit : FusedExit env s c)
    (hasciiLen : c.ascii.length = 4) (hu8kLen : c.u8k.length = 4)
    (hascii : packLanes c.ascii = bytesToNat (asciiAcc bs (blocksOf bs.length)))
    (hcarry : AccCarry bs c)
    (hic : c.i.toNat = blocksOf bs.length)
    (herr : evalICmp .eq (ptestzU8k c.u8k) 0 = 1 ↔
      ¬ (c.u8k.all (fun x => decide (x = 0x00)) = true) ∨
        (bs.length ≠ 0 ∧ klTailByte (klByte bs (bs.length - 1)) = true))
    (hret : ret = verdictWord c.ascii (evalICmp .eq (ptestzU8k c.u8k) 0))
    {ps : List Nat} {count pages shr : Nat}
    {or135 andv w blk0 : BitVec 64}
    {position : List Nat} {opened ppar : Bool}
    (hrunFrame : RunFrame mem xp xn nxp xcarry ps bs c count pages)
    (hent : c.ent = ent)
    (hshr : shr = c.i.toNat)
    (hor : PeelWordAtModel or135 bs shr)
    (hshrEq : shr = (((BitVec.ofNat 64 bs.length) >>> 6)).toNat)
    (hand : andv = (BitVec.ofNat 64 bs.length) &&& 0x000000000000003f#64)
    (hw : w = or135 &&& limMask andv.toNat)
    (harm : arm &&& 2 ≠ (0 : BitVec 64))
    (hreach : EscapeReach blk0 xp nxp xcarry count position
      (flagBytes opened ++ flagBytes ppar)
      (writeBytes c.mem (c.ent + 8 * shr) (natToBytes w.toNat 8)) M)
    (hlen : position.length ≤ 64)
    (hxpSep : c.ent + 8 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ c.ent) :
    S1BlocksRunPartsAt esc args mem next b ent xp nxp xcarry xn arm bs where
  nextIrr := hIrr
  ret := ret
  M := M
  ascii := c.ascii
  u8k := c.u8k
  err := evalICmp .eq (ptestzU8k c.u8k) 0
  gate := gate
  staging := staging_of_fusedExit hfusedExit hasciiLen hu8kLen hascii hcarry hic herr
  word := hret
  runBounded := ⟨e, N, jE, hN, htrace, hterm, hjE, hexit⟩
  tail := tail_third_at_ent hrunFrame hent hshr hor hshrEq hand hw harm hreach
    hlen hxpSep

/-! ### The bundle, the record instance and the refinement

The parts pack `S1BlocksFacts` with the run composed at the corrected charge;
the instance and the refinement are the committed statements. -/

/-- **The bundle, from the corrected parts.**  The run at `s1BlocksBudget` is
`s1BlocksRun_at_budget_of_chargedEscapeExit` at the parts' `e`, `N` and `jE`;
the staging, the returned word and the tail are the parts' own at the same
`M`. -/
theorem s1BlocksFacts_of_partsAt {esc : Calls} {args : List Value} {mem : Mem}
    {next b ent xp nxp xcarry xn : Nat} {arm : BitVec 64} {bs : List UInt8}
    (hargs : args = [.ptr b, .int 64 (BitVec.ofNat 64 bs.length), .ptr ent,
      .ptr xp, .ptr nxp, .ptr xcarry, .int 64 arm])
    (h : S1BlocksRunPartsAt esc args mem next b ent xp nxp xcarry xn arm bs) :
    S1BlocksFacts esc args mem next b ent xp nxp xcarry xn arm bs := by
  obtain ⟨e, N, jE, hN, htrace, hterm, hjE, hexit⟩ := h.runBounded
  have hrun := s1BlocksRun_at_budget_of_chargedEscapeExit (n := BitVec.ofNat 64
    bs.length) (conv := entryGate arm) hargs hN htrace hjE hexit
  exact ⟨h.ret, h.M, h.ascii, h.u8k, h.err, h.gate, h.staging, h.word, hargs,
    hrun, h.tail⟩

/-- **The block unit satisfies its record, from the corrected parts.**  This is
`JsonS1BlocksSatisfies.s1_blocks_satisfies` with its bundle discharged by
`s1BlocksFacts_of_partsAt`; the instance's statement is not restated. -/
theorem s1_blocks_satisfies_of_partsAt {esc : Calls}
    (h : ∀ (args : List Value) (mem : Mem) (next : Nat)
        (b ent xp nxp xcarry xn : Nat) (arm : BitVec 64) (bs : List UInt8),
      s1BlocksPre args mem next →
      args = [.ptr b, .int 64 (BitVec.ofNat 64 bs.length), .ptr ent, .ptr xp,
              .ptr nxp, .ptr xcarry, .int 64 arm] →
      S1BlocksRunPartsAt esc args mem next b ent xp nxp xcarry xn arm bs) :
    Satisfies (s1BlocksCallsEsc esc) s1BlocksFunction Γ_s1_blocks :=
  s1_blocks_satisfies fun args mem next b ent xp nxp xcarry xn arm bs hpre hargs =>
    s1BlocksFacts_of_partsAt hargs
      (h args mem next b ent xp nxp xcarry xn arm bs hpre hargs)

/-- **The block unit satisfies its record, from parts each selection
supplies.** -/
theorem s1_blocks_satisfies_all_of_partsAt
    (h : ∀ (esc : Calls) (args : List Value) (mem : Mem) (next : Nat)
        (b ent xp nxp xcarry xn : Nat) (arm : BitVec 64) (bs : List UInt8),
      s1BlocksPre args mem next →
      args = [.ptr b, .int 64 (BitVec.ofNat 64 bs.length), .ptr ent, .ptr xp,
              .ptr nxp, .ptr xcarry, .int 64 arm] →
      S1BlocksRunPartsAt esc args mem next b ent xp nxp xcarry xn arm bs) :
    ∀ esc : Calls, Satisfies (s1BlocksCallsEsc esc) s1BlocksFunction Γ_s1_blocks :=
  fun esc => s1_blocks_satisfies_of_partsAt (h esc)

/-- **The refinement, from the corrected parts.**  `s1_blocks_refines` is the
record instance's `next = 1` read (`JsonS1BlocksFacts.s1_blocks_refines_of_satisfies`);
the parts are the instance's input, and the refinement statement is not
restated. -/
theorem s1_blocks_refines_of_partsAt
    (h : ∀ (esc : Calls) (args : List Value) (mem : Mem) (next : Nat)
        (b ent xp nxp xcarry xn : Nat) (arm : BitVec 64) (bs : List UInt8),
      s1BlocksPre args mem next →
      args = [.ptr b, .int 64 (BitVec.ofNat 64 bs.length), .ptr ent, .ptr xp,
              .ptr nxp, .ptr xcarry, .int 64 arm] →
      S1BlocksRunPartsAt esc args mem next b ent xp nxp xcarry xn arm bs) :
    s1_blocks_refines :=
  s1_blocks_refines_of_satisfies (s1_blocks_satisfies_all_of_partsAt h)

/-! ### Axiom footprints

`staging_of_fusedExit` is PageModel's and AccFold's exit statements;
`onePrefixBounded_of_armsAt` is `JsonS1BlocksHeadCompose.onePrefixBounded_of_arms`
at the block's argument list; `onePrefixBounded_of_partsAt` is `runFuel_next_irr`
at the two entry states;
the composition is `runFuel_prefix_some` and `runFuel_mono_le` with the budget's
definition and `shift_le_blocksOf`; `s1BlocksRunPartsAt_of_components` is the
structure's fields at `tail_third_at_ent`; the bundle is a constructor; the
instance and the refinement are `JsonS1BlocksSatisfies.s1_blocks_satisfies`'s
and `JsonS1BlocksFacts.s1_blocks_refines_of_satisfies`'s statements unchanged.
No statement reaches `sorryAx`. -/
#print axioms LeanLLVM.Refinement.JsonS1BlocksParts.staging_of_fusedExit
#print axioms LeanLLVM.Refinement.JsonS1BlocksParts.S1BlocksRunPartsAt
#print axioms LeanLLVM.Refinement.JsonS1BlocksParts.onePrefixBounded_of_partsAt
#print axioms LeanLLVM.Refinement.JsonS1BlocksParts.onePrefixBounded_of_armsAt
#print axioms LeanLLVM.Refinement.JsonS1BlocksParts.s1BlocksRun_at_budget_of_chargedEscapeExit
#print axioms LeanLLVM.Refinement.JsonS1BlocksParts.s1BlocksRunPartsAt_of_components
#print axioms LeanLLVM.Refinement.JsonS1BlocksParts.s1BlocksFacts_of_partsAt
#print axioms LeanLLVM.Refinement.JsonS1BlocksParts.s1_blocks_satisfies_of_partsAt
#print axioms LeanLLVM.Refinement.JsonS1BlocksParts.s1_blocks_satisfies_all_of_partsAt
#print axioms LeanLLVM.Refinement.JsonS1BlocksParts.s1_blocks_refines_of_partsAt

end LeanLLVM.Refinement.JsonS1BlocksParts
