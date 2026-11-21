/-
The one-prefix's split at the fused loop's head.

The committed prefix states its charge in two pieces, but neither is stated at
the fused loop's head:

* `JsonS1BlocksPrefixFuel.s1BlocksPrefix_stream_bounded` runs the entry and the
  ASCII phase to a phase terminal at `N ≤ 3 * %shr + 8`;
* `JsonS1BlocksPrefixFuel.handoffPrefix_exit_bounded` runs from the hand-off
  terminal *past* the head to `for.end101`, at `M ≤ 5 * %shr + 13` decomposed
  internally as `2 + (k + (1 + j))`, with the first page's `k ≤ 5`.

A caller that joins the prefix to `JsonS1BlocksRunFrame.loopRun_frame` needs the
segment that ends at the head: the hand-off's two steps and the first page's
`k ≤ 5`, i.e. `2 + k ≤ 7`, on top of the phase's `3 * %shr + 8`.  This module
states that segment.

* `handoffPrefix_head_bounded` — the hand-off's two steps and the first page's
  `k ≤ 5`, from the hand-off terminal to the fused loop's latch
  (`if.end98`), carrying the latch's invariant, the entry's cells, the carry's
  field identities and the document and staged zeroes.  It is
  `handoffPrefix_exit_bounded`'s proof stopped before the latch's own step and
  the loop's induction, so `2 + k` is exposed rather than summed into
  `5 * %shr + 13`.
* `headCharge_split` — the charge identity: the phase's `N ≤ 3 * %shr + 8` and
  the head segment's `k ≤ 5` put `N + (2 + k)` inside `3 * %shr + 15`.
* `s1BlocksPrefix_head_of_handoff` — the composition from `s1BlocksInit`, with
  the phase's trace and the head segment's trace joined by
  `runFuel_prefix_trans`.
* `headCharge_le_budget` — the split's `3 * %shr + 15` is the prefix's share in
  `JsonS1BlocksRunCharge.runFrameCharge_le_budget`: a caller adds only the
  loop's `j` and the exit's `jE` on top, so the phase, the hand-off and the
  first page are counted once.
* `onePrefixBounded_of_head` — the converse join: the head's `3 * %shr + 15`
  plus the remaining `5 * %shr + 6` (the latch's step and the loop's
  `5 * (%shr - (%i + 1)) + 5`, in the committed slack) is exactly
  `JsonS1BlocksPrefixFuel.OnePrefixBounded`'s `8 * %shr + 21`.  The prefix ends
  at the exit terminal, so the exit's own charge is not part of this envelope;
  it is `JsonS1BlocksRunCharge`'s separate `jE`.  A caller with the split's
  head trace and the remainder therefore re-derives the committed prefix's
  envelope without double-counting the hand-off.

What remains is the head's own invariant: the latch bundle here is
`FusedLatch`, and `loopRun_frame` consumes `LoopInv` (the latch's `FusedInv`
plus the model-side `LoopCarry`) and the caller's staging.  Those are the
caller's model facts, exactly as at the peel; this module does not invent them.
-/
import LeanLLVM.Refinement.JsonS1BlocksPrefixFuel
import LeanLLVM.Refinement.JsonS1BlocksRunCharge

namespace LeanLLVM.Refinement.JsonS1BlocksPrefixSplit

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.BlockEvalVector
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
open LeanLLVM.Refinement.JsonS1BlocksStream
open LeanLLVM.Refinement.JsonS1BlocksLoopRun
open LeanLLVM.Refinement.JsonS1BlocksPrefixFuel
open LeanLLVM.Refinement.JsonS1BlocksRunCharge
open LeanLLVM.Refinement.JsonEntryIR (wordsOf)

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### The hand-off and the first page, stopped at the head

`handoffPrefix_exit_bounded` runs the hand-off's two steps, the first page
(`k ≤ 5`), the latch's step and the fused loop's induction as one segment.  The
head is where the latch's step has not yet been taken: the two hand-off steps
and the first page end at `stateAt envL core`, with `FusedLatch` at `if.end98`.
Stopping there exposes `2 + k`. -/

/-- **The hand-off reaches the fused loop's head, with its charge.**  From an
`AsciiInvCells` hand-off terminal (`if.then38`), the two hand-off steps and the
first page's at most five steps reach the latch at `stateAt envL core` — the
fused loop's head before its own step — carrying the latch's `FusedLatch`, the
entry's cells, the carry's field identities, and the document and staged zeroes
at the head's memory.  The run segment is `2 + k` with `k ≤ 5`. -/
theorem handoffPrefix_head_bounded (sel : Calls) (env : Env) (s : State)
    (c : AsciiCarry) (v : ForBodyValues) (bs2 bs3 : List UInt8)
    (doc : Nat → List UInt8) (b : Nat) (n : BitVec 64) (conv : BitVec 32)
    (arm : BitVec 64) (xp nxp xcarry : Nat) (bs73 bs74 : List UInt8)
    (hinv : AsciiInvCells env s c b n conv arm)
    (hv : v = asciiValues c bs2 bs3)
    (hread2 : readBytes c.mem (c.b + 64 * (c.i + 1).toNat) 32 = some bs2)
    (hread3 : readBytes c.mem (c.b + 64 * (c.i + 1).toNat + 32) 32 = some bs3)
    (hne : c.i + 1 ≠ c.shr)
    (hbit : evalICmp .ult (v.i + 1) c.shr = 1)
    (hshr57 : c.shr.toNat < 2 ^ 57)
    (hb3 : 3 ≤ c.b)
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hnxp : lookupName env "%nxp" = some (.ptr nxp))
    (hxcarry : lookupName env "%xcarry" = some (.ptr xcarry))
    (hcar : HandoffCarries sel env s c bs2 bs3 v doc bs73 bs74 xp nxp xcarry) :
    let v38 := ifThen38Values v.addPtr v.i bs2 bs3
        ((doc ((c.i + 1).toNat - 1)).drop 63 ++ (doc ((c.i + 1).toNat)).take 31)
        ((doc ((c.i + 1).toNat - 1)).drop 62 ++ (doc ((c.i + 1).toNat)).take 30)
        ((doc ((c.i + 1).toNat - 1)).drop 61 ++ (doc ((c.i + 1).toNat)).take 29)
        (((doc ((c.i + 1).toNat)).drop 31).take 32)
        (((doc ((c.i + 1).toNat)).drop 30).take 32)
        (((doc ((c.i + 1).toNat)).drop 29).take 32)
    let sH := asciiHandoffState env s c v
    ∃ (envL : Env) (core : State) (c' : FusedCarry) (k : Nat),
      k ≤ 5 ∧
      FusedLatch envL core (v38.inc49) c' (evalICmp .eq conv 0)
        (evalICmp .eq (arm &&& 2) 0) ∧
      EntryCells envL n conv arm ∧
      c'.shr = c.shr ∧ c'.b = c.b ∧ c'.ent = c.ent ∧
      c'.xp = xp ∧ c'.nxp = nxp ∧ c'.xcarry = xcarry ∧
      (∀ j, j < c.shr.toNat →
        readBytes c'.mem (c.b + 64 * j) 64 = some (doc j)) ∧
      readBytes c'.mem (c.b - 3) 3 = some [0, 0, 0] ∧
      (∀ k', runFuel (s1BlocksCallsEsc sel) (2 + k + k') s1BlocksFunction sH =
        runFuel (s1BlocksCallsEsc sel) k' s1BlocksFunction (stateAt envL core)) := by
  intro v38 sH
  let s4 : State := stateAt (ifThen38Out (asciiHandoffEnv env c v) v38)
    { sH with pc := "if.end50", pre := some "if.then38" }
  let s5 : State := stateAt (fb54PageEnv env c v v38)
    { s4 with pc := "for.body54.lr.ph", pre := some "if.end50" }
  obtain ⟨h01, h12⟩ := asciiHandoff_run env s c v bs2 bs3 doc hinv.toAsciiInv hv
    hread2 hread3 hshr57 hne hcar.entGap hcar.docMem hbit
  have h01' : step (s1BlocksCallsEsc sel) s1BlocksFunction sH = .jump s4 := by
    rw [step_esc_of_free sel s1BlocksFunction sH if_then38Block
      (by rw [show sH.pc = "if.then38" from rfl]; exact findBlock_if_then38) (by decide)]
    exact h01
  have h12' : step (s1BlocksCallsEsc sel) s1BlocksFunction s4 = .jump s5 := by
    rw [step_esc_of_free sel s1BlocksFunction s4 if_end50Block
      (by rw [show s4.pc = "if.end50" from rfl]; exact findBlock_if_end50) (by decide)]
    exact h12
  have hcellsPage : EntryCells (fb54PageEnv env c v v38) n conv arm :=
    entryCells_fb54PageEnv env c v v38 hinv.entryCells
  obtain ⟨envL, core, c', k, hk, hl, hcellsL, hshrEq, hbEq, hentEq, hxpEq, hnxpEq,
    hxcEq, hdoc', hzero', hrun⟩ :=
    entryPageCells_latch sel env s5 c v v38 arm conv bs73 bs74 c.b c.ent xp nxp
      xcarry doc n arm rfl hcellsPage hinv.arm_cell hinv.conv_cell hinv.base
      hinv.emit hinv.bound hxp hnxp hxcarry hcar.i63 hcar.shl63 hcar.read73
      hcar.read74 hcar.len73 hcar.len74 hcar.asciiLen hcar.u8kLen hb3 hcar.zeroPage
      hcar.docPage hcar.irow hcar.entGap hshr57 hcar.call hcar.keep
  have hrun5 : ∀ j, runFuel (s1BlocksCallsEsc sel) (k + j) s1BlocksFunction s5 =
      runFuel (s1BlocksCallsEsc sel) j s1BlocksFunction (stateAt envL core) :=
    fun j => hrun j
  refine ⟨envL, core, c', k, hk, hl, hcellsL, hshrEq, hbEq, hentEq, hxpEq, hnxpEq,
    hxcEq, hdoc', hzero', ?_⟩
  intro k'
  rw [show 2 + k + k' = 2 + (k + k') from by omega,
    runFuel_jump2 h01' h12' (k + k'), hrun5 k']

/-! ### The charge split

The phase's `3 * %shr + 8`, the hand-off's two steps and the first page's
`k ≤ 5` compose to `3 * %shr + 15`; the head segment on its own is at most `7`.
These are the arithmetic identities the composed run and the budget both read. -/

/-- The head segment is at most `2 + 5`. -/
theorem handoffSteps_le_seven {k : Nat} (hk : k ≤ 5) : 2 + k ≤ 7 := by omega

/-- **The one-prefix's charge splits at the fused loop's head.**  The phase's
`N ≤ 3 * %shr + 8` and the head segment's `k ≤ 5` put the run to the head inside
`3 * %shr + 15`. -/
theorem headCharge_split {shr N k : Nat} (hN : N ≤ 3 * shr + 8) (hk : k ≤ 5) :
    N + (2 + k) ≤ 3 * shr + 15 := by omega

/-! ### The composed run from the entry to the head

The phase's committed run (`s1BlocksPrefix_stream_bounded`) and the head segment
above are two `runFuel` prefixes; `runFuel_prefix_trans` joins them.  The
hand-off terminal is the phase's witness, so the phase trace is a hypothesis at
that witness, exactly as the committed terminal exposes it. -/

/-- **The entry reaches the fused loop's head, with the split charge.**  Given
the phase's trace from `s1BlocksInit` to the hand-off terminal at
`N ≤ 3 * %shr + 8`, the hand-off's two steps and the first page's `k ≤ 5`
continue to the latch at `N + (2 + k) ≤ 3 * %shr + 15`, with the same head
bundle as `handoffPrefix_head_bounded`. -/
theorem s1BlocksPrefix_head_of_handoff (esc : Calls) (mem : Mem)
    (b ent xp nxp xcarry : Nat) (n arm : BitVec 64)
    (bs : List UInt8) (doc : Nat → List UInt8) (bs73 bs74 : List UInt8)
    (env : Env) (s : State) (c : AsciiCarry) (bs2 bs3 : List UInt8)
    (v : ForBodyValues) (N : Nat)
    (hphase : ∀ k, runFuel (s1BlocksCallsEsc esc) (N + k) s1BlocksFunction
      (s1BlocksInit [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp, .ptr xcarry,
        .int 64 arm] mem) =
      runFuel (s1BlocksCallsEsc esc) k s1BlocksFunction (asciiHandoffState env s c v))
    (hN : N ≤ 3 * (n >>> 6).toNat + 8)
    (hinv : AsciiInvCells env s c b n (entryGate arm) arm)
    (hv : v = asciiValues c bs2 bs3)
    (hread2 : readBytes c.mem (c.b + 64 * (c.i + 1).toNat) 32 = some bs2)
    (hread3 : readBytes c.mem (c.b + 64 * (c.i + 1).toNat + 32) 32 = some bs3)
    (hne : c.i + 1 ≠ c.shr)
    (hbit : evalICmp .ult (v.i + 1) c.shr = 1)
    (hshr57 : c.shr.toNat < 2 ^ 57)
    (hb3 : 3 ≤ c.b)
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hnxp : lookupName env "%nxp" = some (.ptr nxp))
    (hxcarry : lookupName env "%xcarry" = some (.ptr xcarry))
    (hcar : HandoffCarries esc env s c bs2 bs3 v doc bs73 bs74 xp nxp xcarry) :
    let v38 := ifThen38Values v.addPtr v.i bs2 bs3
        ((doc ((c.i + 1).toNat - 1)).drop 63 ++ (doc ((c.i + 1).toNat)).take 31)
        ((doc ((c.i + 1).toNat - 1)).drop 62 ++ (doc ((c.i + 1).toNat)).take 30)
        ((doc ((c.i + 1).toNat - 1)).drop 61 ++ (doc ((c.i + 1).toNat)).take 29)
        (((doc ((c.i + 1).toNat)).drop 31).take 32)
        (((doc ((c.i + 1).toNat)).drop 30).take 32)
        (((doc ((c.i + 1).toNat)).drop 29).take 32)
    ∃ (envL : Env) (core : State) (c' : FusedCarry) (k : Nat),
      k ≤ 5 ∧
      FusedLatch envL core (v38.inc49) c' (evalICmp .eq (entryGate arm) 0)
        (evalICmp .eq (arm &&& 2) 0) ∧
      EntryCells envL n (entryGate arm) arm ∧
      c'.shr = c.shr ∧ c'.b = c.b ∧ c'.ent = c.ent ∧
      c'.xp = xp ∧ c'.nxp = nxp ∧ c'.xcarry = xcarry ∧
      (∀ j, j < c.shr.toNat →
        readBytes c'.mem (c.b + 64 * j) 64 = some (doc j)) ∧
      readBytes c'.mem (c.b - 3) 3 = some [0, 0, 0] ∧
      (∀ k', runFuel (s1BlocksCallsEsc esc) (N + (2 + k) + k') s1BlocksFunction
        (s1BlocksInit [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp, .ptr xcarry,
          .int 64 arm] mem) =
        runFuel (s1BlocksCallsEsc esc) k' s1BlocksFunction (stateAt envL core)) ∧
      N + (2 + k) ≤ 3 * (n >>> 6).toNat + 15 := by
  intro v38
  obtain ⟨envL, core, c', k, hk, hl, hcellsL, hshrEq, hbEq, hentEq, hxpEq, hnxpEq,
    hxcEq, hdoc', hzero', hrun⟩ :=
    handoffPrefix_head_bounded esc env s c v bs2 bs3 doc b n (entryGate arm) arm
      xp nxp xcarry bs73 bs74 hinv hv hread2 hread3 hne hbit hshr57 hb3 hxp hnxp
      hxcarry hcar
  refine ⟨envL, core, c', k, hk, hl, hcellsL, hshrEq, hbEq, hentEq, hxpEq, hnxpEq,
    hxcEq, hdoc', hzero', ?_, ?_⟩
  · intro k'
    rw [Nat.add_assoc, hphase ((2 + k) + k'), hrun k']
  · exact headCharge_split hN hk

/-! ### The split inside the run's budget

`JsonS1BlocksRunCharge.runFrameCharge_le_budget` charges the run at the record's
budget as `3 * %shr + 15 + j + jE`.  The split supplies the first term and the
hand-off's `2` and the first page's `k` are already in it, so a caller adds only
the loop's `j` and the exit's `jE`. -/

/-- **The split is the prefix's share of the run's budget.**  From the phase's
`N ≤ 3 * %shr + 8`, the first page's `k ≤ 5`, the loop's
`j ≤ 5 * (%shr - (%i + 1)) + 5` and the exit's `jE ≤ escapeExitCharge`, the
whole run `N + (2 + k) + j + jE` is inside `s1BlocksBudget`.  The hand-off and
the first page appear once, in `3 * %shr + 15`. -/
theorem headCharge_le_budget {args : List Value} {mem : Mem}
    {b ent xp nxp xcarry : Nat} {arm : BitVec 64} {bs : List UInt8}
    {shr i j jE N k : Nat}
    (hargs : args = [.ptr b, .int 64 (BitVec.ofNat 64 bs.length), .ptr ent,
      .ptr xp, .ptr nxp, .ptr xcarry, .int 64 arm])
    (hn : (BitVec.ofNat 64 bs.length).toNat = bs.length)
    (hblocks : shr + 1 = blocksOf bs.length)
    (hN : N ≤ 3 * shr + 8)
    (hk : k ≤ 5)
    (hj : j ≤ 5 * (shr - (i + 1)) + 5)
    (hjE : jE ≤ escapeExitCharge) :
    N + (2 + k) + j + jE ≤ s1BlocksBudget args mem := by
  have hsplit := headCharge_split hN hk
  have h := runFrameCharge_le_budget (args := args) (mem := mem) (b := b)
    (ent := ent) (xp := xp) (nxp := nxp) (xcarry := xcarry) (arm := arm)
    (bs := bs) (shr := shr) (i := i) (j := j) (jE := jE)
    hargs hn hblocks hj hjE
  omega

/-! ### The split joined back into the committed prefix

The committed `OnePrefixBounded` is `8 * %shr + 21`.  The split's head charge is
`3 * %shr + 15`, and the latch's step, the loop and the exit are at most
`5 * %shr + 6`; their sum is the committed envelope exactly.  A caller that has
the head segment and the remainder therefore re-derives the prefix without
counting the hand-off into both halves. -/

/-- **The one-prefix from its head segment and the remainder.**  The head
segment at `N ≤ 3 * %shr + 15` and the remainder at `M ≤ 5 * %shr + 6` compose
to `OnePrefixBounded`'s `8 * %shr + 21`, ending at the exit terminal. -/
theorem onePrefixBounded_of_head {esc : Calls} {args : List Value} {mem : Mem}
    {b : Nat} {n : BitVec 64} {conv : BitVec 32} {arm : BitVec 64}
    {eH e : State} {N M : Nat}
    (hhead : ∀ k, runFuel (s1BlocksCallsEsc esc) (N + k) s1BlocksFunction
      (s1BlocksInit args mem) = runFuel (s1BlocksCallsEsc esc) k s1BlocksFunction eH)
    (hheadLe : N ≤ 3 * (n >>> 6).toNat + 15)
    (hrest : ∀ k, runFuel (s1BlocksCallsEsc esc) (M + k) s1BlocksFunction eH =
      runFuel (s1BlocksCallsEsc esc) k s1BlocksFunction e)
    (hrestLe : M ≤ 5 * (n >>> 6).toNat + 6)
    (hterm : ExitTermCells b n conv arm e) :
    OnePrefixBounded esc args mem b n conv arm :=
  ⟨e, N + M, by omega, runFuel_prefix_trans hhead hrest, hterm⟩

/-- **The one-prefix from the phase's charge and the head segment.**  The
phase's `N ≤ 3 * %shr + 8` and the head segment's `k ≤ 5` are the split's
`3 * %shr + 15`; with the remainder's `5 * %shr + 6` the committed envelope
holds.  This is the same join as `onePrefixBounded_of_head` with the split's own
charge read at the head. -/
theorem onePrefixBounded_of_split {esc : Calls} {args : List Value} {mem : Mem}
    {b : Nat} {n : BitVec 64} {conv : BitVec 32} {arm : BitVec 64}
    {eH e : State} {N k M : Nat}
    (hhead : ∀ k', runFuel (s1BlocksCallsEsc esc) (N + (2 + k) + k')
      s1BlocksFunction (s1BlocksInit args mem) =
      runFuel (s1BlocksCallsEsc esc) k' s1BlocksFunction eH)
    (hN : N ≤ 3 * (n >>> 6).toNat + 8)
    (hk : k ≤ 5)
    (hrest : ∀ k', runFuel (s1BlocksCallsEsc esc) (M + k') s1BlocksFunction eH =
      runFuel (s1BlocksCallsEsc esc) k' s1BlocksFunction e)
    (hrestLe : M ≤ 5 * (n >>> 6).toNat + 6)
    (hterm : ExitTermCells b n conv arm e) :
    OnePrefixBounded esc args mem b n conv arm :=
  onePrefixBounded_of_head hhead (headCharge_split hN hk) hrest hrestLe hterm

/-! ### Axiom footprints

`handoffPrefix_head_bounded` is `JsonS1BlocksRefine.asciiHandoff_run`'s two
steps and `JsonS1BlocksPrefix.entryPageCells_latch`'s page with the latch's own
step and the loop's induction left out; the composition is `runFuel_jump2` and
`runFuel_prefix_trans`.  The charges are `omega` over the committed `3`, `2` and
`5` constants; the budget is `JsonS1BlocksRunCharge.runFrameCharge_le_budget`;
the join is `runFuel_prefix_trans`.  No statement reaches `sorryAx`. -/

#print axioms LeanLLVM.Refinement.JsonS1BlocksPrefixSplit.handoffSteps_le_seven
#print axioms LeanLLVM.Refinement.JsonS1BlocksPrefixSplit.headCharge_split
#print axioms LeanLLVM.Refinement.JsonS1BlocksPrefixSplit.handoffPrefix_head_bounded
#print axioms LeanLLVM.Refinement.JsonS1BlocksPrefixSplit.s1BlocksPrefix_head_of_handoff
#print axioms LeanLLVM.Refinement.JsonS1BlocksPrefixSplit.headCharge_le_budget
#print axioms LeanLLVM.Refinement.JsonS1BlocksPrefixSplit.onePrefixBounded_of_head
#print axioms LeanLLVM.Refinement.JsonS1BlocksPrefixSplit.onePrefixBounded_of_split

end LeanLLVM.Refinement.JsonS1BlocksPrefixSplit
