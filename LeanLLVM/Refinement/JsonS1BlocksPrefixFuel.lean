/-
The one-prefix's fuel, as a term.

`JsonS1BlocksStream.s1BlocksPrefix_exit` reaches `for.end101` from `s1BlocksInit`
at the escape selection, but states its fuel only inside an `∃`: the two runs it
composes both expose a bound at their own level (the phase's
`streamInvCells_runFuel` gives `j ≤ 3 * (%shr - (%i + 1)) + 4`, the fused loop's
`fusedInvCells_runFuel` gives `j ≤ 5 * (%shr - (%i + 1)) + 5`, and the first
page's `entryPageCells_latch` gives `k ≤ 5`), and the composition discards them.
`JsonS1BlocksLoopRun.s1BlocksRun_at_budget` therefore takes the prefix's fuel
`N` and its containment in `s1BlocksBudget` as hypotheses.

This module re-derives the two composition passes with those charges kept:

* `s1BlocksPrefix_stream_bounded` — the entry's step, the preheader's first pass
  and the phase's induction, at a fuel `N ≤ 3 * (%n >>> 6) + 8`.  The phase's
  term `3 * (%shr - (%i + 1)) + 4` runs from `%i = 0`, and the four constant
  steps are the entry's one and the preheader's three, so the whole is the
  phase's `3` per block plus its constant slack.
* `handoffPrefix_exit_bounded` — the hand-off's two steps, the first page
  (`k ≤ 5`) and the fused loop's induction (`j ≤ 5 * (%shr - (%i + 1)) + 5`), at
  a fuel `M ≤ 5 * %shr + 13`.  The bound drops the loop's own index with
  `5 * (s - i) ≤ 5 * s`, which is why it does not depend on the hand-off's row.
* `s1BlocksPrefix_exit_bounded` — the join, at `N + M ≤ 8 * (%n >>> 6) + 21`.

The constant `21` is slack, not a tight count: the charge's own composition
(`entry_charge_sum`'s `3 * (blocks - 1) + 4 + 5 * (shr - (i + 1)) + 5`) has
enough room that the two passes' constant parts fit beside it.  The shift is at
most the document's block count (`shift_le_blocksOf`), so the bound is inside
`s1BlocksBudget`'s `8 * blocks + 32` (`prefixCharge_le_budget`), and
`s1BlocksRun_at_budget_of_boundedPrefix` applies `s1BlocksRun_at_budget` with no
fuel hypothesis: only the exit's own run `jE` and its containment
`jE ≤ s1BlocksBudget - (8 * (%n >>> 6) + 21)` remain, because the exits
(`asciiExitCells_run`, `fusedExitCells_run`) also state their fuel as an `∃`
without exposing it.

## What the rest of the run now supplies

The exit is charged too, in `JsonS1BlocksExitFuel`: its two compositions count
`for.end101` and, when taken, `if.then103`, `if.end153` and `if.then164` against
the tail arms' own steps, so the aligned empty document costs `3`, the aligned
last byte `4` and the partial block at the silent merge `5`, and `exitCharge` is
their largest.  The peel's escape merge is the calling arm, at `6`, and is
`JsonS1BlocksEscapeRun`'s.  `s1BlocksRun_at_budget_of_chargedExit` takes the
prefix segment at `next = 1` from `OnePrefixBounded` outright, and
`JsonS1BlocksFacts.run_of_residuals` joins the residual's two segments at
`s1BlocksBudget`, so no field of `S1BlocksResiduals` names a whole run.  What is
left owed there is the exit's hypotheses, not its fuel: the peel's merge bit, the
loop's staging and the tail byte's error bit, which `JsonS1BlocksPeelStaging`
supplies from the peel's arithmetic and which the loop's register-to-model
identities still owe.
-/
import LeanLLVM.Refinement.JsonS1BlocksLoopRun
import LeanLLVM.Refinement.JsonS1BlocksStream
import LeanLLVM.Refinement.JsonS1BlocksPrefix

namespace LeanLLVM.Refinement.JsonS1BlocksPrefixFuel

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
open LeanLLVM.Refinement.JsonEntryIR (wordsOf)

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### The prefix's charge, at the record's budget -/

/-- **The shift is at most the block count.**  `%n >>> 6` is the document's
whole-block count and `blocksOf` rounds up, so a padded final block can only add
to it. -/
theorem shift_le_blocksOf (n : BitVec 64) :
    (n >>> 6).toNat ≤ blocksOf n.toNat := by
  rw [ushr_six_toNat]
  show n.toNat / 64 ≤ (n.toNat + 63) / 64
  exact Nat.div_le_div_right (by omega)

/-- **The exposed prefix bound is inside the record's budget.**  The prefix's
`8 * (%n >>> 6) + 21` and the budget's `8 * blocksOf (%n) + 32` differ only by
the shift's bound (`shift_le_blocksOf`) and the budget's slack. -/
theorem prefixCharge_le_budget {args : List Value} {mem : Mem} {b ent xp nxp xcarry : Nat}
    {n : BitVec 64} {arm : BitVec 64}
    (hargs : args = [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp, .ptr xcarry,
      .int 64 arm]) :
    8 * (n >>> 6).toNat + 21 ≤ s1BlocksBudget args mem := by
  rw [hargs, s1BlocksBudget]
  simp only [s1BlocksLength]
  have h := shift_le_blocksOf n
  omega

/-! ### The phase's prefix, at its own charge

The entry's step, the preheader's first pass and the phase's induction against
its stream-carrying invariant.  The body is `JsonS1BlocksStream`'s, with the
induction's bound kept. -/

/-- **The entry reaches the phase's terminal, with its fuel.**  From
`s1BlocksInit`, the run at the escape selection reaches a phase terminal carrying
the stream's cells in at most `3 * (%n >>> 6) + 8` steps: the induction's
`3 * (%shr - (%i + 1)) + 4` at `%i = 0` plus the entry's one step and the
preheader's three. -/
theorem s1BlocksPrefix_stream_bounded (esc : Calls) (mem : Mem)
    (b ent xp nxp xcarry : Nat) (n arm : BitVec 64)
    (bs : List UInt8) (doc : Nat → List UInt8)
    (hlong : evalICmp .ult n 64 = 0)
    (hread2 : readBytes mem b 32 = some ((docBlock bs 0).take 32))
    (hread3 : readBytes mem (b + 32) 32 = some ((docBlock bs 0).drop 32))
    (hgate : evalICmp .eq (arm &&& 2) 0 = 1)
    (hfirst : evalICmp .eq (ifEndTest
      (forBodyValues 0 0 0 0 0 ((docBlock bs 0).take 32) ((docBlock bs 0).drop 32)
        b ent).w2
      (forBodyValues 0 0 0 0 0 ((docBlock bs 0).take 32) ((docBlock bs 0).drop 32)
        b ent).w3) 0 = 0)
    (hgap : b + 64 * (n >>> 6).toNat ≤ ent)
    (hdoc : ∀ j, j < (n >>> 6).toNat →
      readBytes mem (b + 64 * j) 64 = some (doc j))
    (hshr57 : (n >>> 6).toNat < 2 ^ 57) :
    let args := [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp, .ptr xcarry,
      .int 64 arm]
    ∃ (e : State) (N : Nat),
      N ≤ 3 * (n >>> 6).toNat + 8 ∧
      (∀ k, runFuel (s1BlocksCallsEsc esc) (N + k) s1BlocksFunction
          (s1BlocksInit args mem) =
        runFuel (s1BlocksCallsEsc esc) k s1BlocksFunction e) ∧
      AsciiTermStreamCells b n (entryGate arm) arm xp nxp xcarry e := by
  intro args
  let init : State := s1BlocksInit args mem
  let E0 : Env := LeanLLVM.Refinement.JsonS1BlocksRefine.entryEnv init.env n arm
  let sLR : State := { init with pc := "for.body.lr.ph", pre := some "entry" }
  have hn : lookupName init.env "%n" = some (.int 64 n) :=
    s1BlocksInit_env_n mem b ent xp nxp xcarry n arm
  have harm : lookupName init.env "%arm" = some (.int 64 arm) :=
    s1BlocksInit_env_arm mem b ent xp nxp xcarry n arm
  have hb0 : lookupName init.env "%b" = some (.ptr b) :=
    s1BlocksInit_env_b mem b ent xp nxp xcarry n arm
  have hent0 : lookupName init.env "%ent" = some (.ptr ent) :=
    s1BlocksInit_env_ent mem b ent xp nxp xcarry n arm
  have hcells0 : EntryCells E0 n (entryGate arm) arm :=
    entryCells_entryEnv init.env n arm hn harm
  have hstream0 : StreamCells init.env xp nxp xcarry :=
    streamCells_init mem b ent xp nxp xcarry n arm
  have hstreamE0 : StreamCells E0 xp nxp xcarry :=
    streamCells_entryEnv init.env n arm xp nxp xcarry hstream0
  have harm0 : lookupName E0 "%arm" = some (.int 64 arm) :=
    lookupName_entryEnv_arm init.env n arm harm
  have hbE0 : lookupName E0 "%b" = some (.ptr b) :=
    lookupName_entryEnv_of (k := "%b") (v := .ptr b) init.env n arm hb0
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hentE0 : lookupName E0 "%ent" = some (.ptr ent) :=
    lookupName_entryEnv_of (k := "%ent") (v := .ptr ent) init.env n arm hent0
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hshrE0 : lookupName E0 "%shr" = some (.int 64 (n >>> 6)) :=
    LeanLLVM.Refinement.JsonS1BlocksRefine.lookupName_entryEnv_shr init.env n arm
  -- the entry's step
  have hstepEntry : step (s1BlocksCallsEsc esc) s1BlocksFunction init =
      .jump (stateAt E0 sLR) :=
    s1BlocksInit_step_blocks mem b ent xp nxp xcarry n arm hlong
  -- the preheader's first pass
  let v0 : ForBodyValues := forBodyValues 0 0 0 0 0 ((docBlock bs 0).take 32)
    ((docBlock bs 0).drop 32) b ent
  let s1' : State := { sLR with pc := "for.body", pre := some "for.body.lr.ph" }
  let s2' : State := { sLR with
    pc := "if.end"
    pre := some "for.body"
    mem := writeBytes sLR.mem v0.arrayidx (natToBytes v0.or16.toNat 8) }
  let Eseed : Env := ifEndEnv (forBodyOut (lrPhEnv E0 arm) v0) v0.w2 v0.w3
  let sSeed : State := stateAt Eseed { sLR with
    pc := "for.inc"
    pre := some "if.end"
    mem := writeBytes sLR.mem v0.arrayidx (natToBytes v0.or16.toNat 8) }
  obtain ⟨h01, h12, h23⟩ :=
    for_body_lr_ph_page_ascii E0 sLR arm ((docBlock bs 0).take 32)
      ((docBlock bs 0).drop 32) b ent rfl harm0 hgate hbE0 hentE0 hread2 hread3
      hfirst
  have h01' : step (s1BlocksCallsEsc esc) s1BlocksFunction (stateAt E0 sLR) =
      .jump (stateAt (lrPhEnv E0 arm) s1') := by
    rw [step_forBodyLrPh_esc esc E0 sLR rfl]; exact h01
  have h12' : step (s1BlocksCallsEsc esc) s1BlocksFunction
      (stateAt (lrPhEnv E0 arm) s1') =
      .jump (stateAt (forBodyOut (lrPhEnv E0 arm) v0) s2') := by
    rw [step_forBody_esc esc (lrPhEnv E0 arm) s1' rfl]
    exact h12
  have h23' : step (s1BlocksCallsEsc esc) s1BlocksFunction
      (stateAt (forBodyOut (lrPhEnv E0 arm) v0) s2') =
      .jump sSeed := by
    rw [step_forIfEnd_esc esc _ _ rfl]; exact h23
  -- the seed invariant
  let c0 : AsciiCarry :=
    { i := v0.i, prevS := v0.shr17, st0 := v0.shrII, st9 := v0.conv13II,
      st15 := v0.shrI, b := b, ent := ent, shr := n >>> 6,
      mem := writeBytes sLR.mem v0.arrayidx (natToBytes v0.or16.toNat 8) }
  have hseed : StreamInvCells Eseed sSeed c0 b n (entryGate arm) arm xp nxp xcarry :=
    streamInvCells_seed E0 sLR arm ((docBlock bs 0).take 32)
      ((docBlock bs 0).drop 32) b ent (n >>> 6) n (entryGate arm) xp nxp xcarry
      hcells0 harm0 hgate hshrE0 hbE0 hentE0 (by
        rw [ushr_six_toNat]
        have h64 : (64 : BitVec 64).toNat = 64 := by decide
        have hnot : ¬ BitVec.ult n 64 := by
          intro hlt
          have hone : evalICmp .ult n (64 : BitVec 64) = 1 := by
            show BitVec.ofBool (BitVec.ult n 64) = 1
            rw [hlt]; rfl
          rw [hone] at hlong
          exact absurd hlong (by decide)
        rw [BitVec.ult_iff_toNat_lt] at hnot
        rw [h64] at hnot
        omega) hstreamE0
  have hgapSeed : c0.b + 64 * c0.shr.toNat ≤ c0.ent := hgap
  have harr : v0.arrayidx = ent := forBodyValues_zero_arrayidx _ _ b ent
  have hdocSeed : ∀ j, j < c0.shr.toNat →
      readBytes c0.mem (c0.b + 64 * j) 64 = some (doc j) := by
    intro j hj
    have hshr0 : c0.shr = n >>> 6 := rfl
    have hj' : j < (n >>> 6).toNat := by simpa only [hshr0] using hj
    rw [show c0.mem = writeBytes sLR.mem v0.arrayidx (natToBytes v0.or16.toNat 8)
        from rfl, show c0.b = b from rfl]
    rw [readBytes_writeBytes_below sLR.mem (natToBytes v0.or16.toNat 8) 64
      (b + 64 * j) v0.arrayidx (by rw [harr]; omega)]
    exact hdoc j hj'
  obtain ⟨e, j, hjle, hterm, hfuel⟩ :=
    streamInvCells_runFuel esc Eseed sSeed c0 b n (entryGate arm) arm xp nxp xcarry
      doc hshr57 hseed hgapSeed hdocSeed
  refine ⟨e, 1 + (3 + j), ?_, ?_, hterm⟩
  · -- the induction's `3 * (shr - (i + 1)) + 4` at `i = 0`, above the constants
    have hshr0 : c0.shr = n >>> 6 := rfl
    have hle : c0.shr.toNat - (c0.i.toNat + 1) ≤ (n >>> 6).toNat := by
      rw [hshr0]; exact Nat.sub_le _ _
    have hjle' : j ≤ 3 * (n >>> 6).toNat + 4 := by omega
    omega
  · intro k
    rw [show 1 + (3 + j) + k = 1 + (3 + (j + k)) from by omega,
      runFuel_jump_prefix hstepEntry (3 + (j + k)),
      runFuel_jump3 h01' h12' h23' (j + k)]
    exact hfuel k

/-! ### The hand-off's continuation, at its own charge

The hand-off's two steps, the first page's `k ≤ 5`, and the fused loop's
`5 * (%shr - (%i + 1)) + 5`, composed to `5 * %shr + 13`. -/

/-- **The hand-off arm reaches the exit, with its fuel.**  From an `AsciiInvCells`
hand-off terminal, the run reaches `for.end101` on one of the two exit terminals
at a fuel `M ≤ 5 * %shr + 13`: the hand-off's two steps, the first page's at most
five, and the loop's `5 * (shr - (i + 1)) + 5`, bounded above by `5 * shr + 5`
since the index is non-negative. -/
theorem handoffPrefix_exit_bounded (sel : Calls) (env : Env) (s : State)
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
    (hgap : c.b + 64 * c.shr.toNat ≤ c.ent)
    (hdoc : ∀ j, j < c.shr.toNat → readBytes c.mem (c.b + 64 * j) 64 = some (doc j))
    (hb3 : 3 ≤ c.b)
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hnxp : lookupName env "%nxp" = some (.ptr nxp))
    (hxcarry : lookupName env "%xcarry" = some (.ptr xcarry))
    (hdocPage : ∀ j, j < c.shr.toNat →
      readBytes (asciiHandoffState env s c v).mem (c.b + 64 * j) 64 = some (doc j))
    (hzeroPage : readBytes (asciiHandoffState env s c v).mem (c.b - 3) 3 = some [0, 0, 0])
    (hirow : (v.i + 1).toNat < c.shr.toNat)
    (hi63 : ((v.i + 1).signExtend 64).toNat < 2 ^ 63)
    (hshl63 : (((v.i + 1) <<< (0x0000000000000006#64).toNat).signExtend 64).toNat
      < 2 ^ 63)
    (hread73 : readBytes (asciiHandoffState env s c v).mem
      (c.b + (((v.i + 1) <<< (0x0000000000000006#64).toNat).signExtend 64).toNat) 32
      = some bs73)
    (hread74 : readBytes (asciiHandoffState env s c v).mem
      ((c.b + (((v.i + 1) <<< (0x0000000000000006#64).toNat).signExtend 64).toNat)
        + ((0x0000000000000020#64).signExtend 64).toNat) 32 = some bs74)
    (h73len : (unpackLanes 64 4 (bytesToNat bs73)).length = 4)
    (h74len : (unpackLanes 64 4 (bytesToNat bs74)).length = 4)
    (hascii_len : (ifThen38Values v.addPtr v.i bs2 bs3
        ((doc ((c.i + 1).toNat - 1)).drop 63 ++ (doc ((c.i + 1).toNat)).take 31)
        ((doc ((c.i + 1).toNat - 1)).drop 62 ++ (doc ((c.i + 1).toNat)).take 30)
        ((doc ((c.i + 1).toNat - 1)).drop 61 ++ (doc ((c.i + 1).toNat)).take 29)
        (((doc ((c.i + 1).toNat)).drop 31).take 32)
        (((doc ((c.i + 1).toNat)).drop 30).take 32)
        (((doc ((c.i + 1).toNat)).drop 29).take 32)).or284.length = 4)
    (hu8k_len : (ifThen38Values v.addPtr v.i bs2 bs3
        ((doc ((c.i + 1).toNat - 1)).drop 63 ++ (doc ((c.i + 1).toNat)).take 31)
        ((doc ((c.i + 1).toNat - 1)).drop 62 ++ (doc ((c.i + 1).toNat)).take 30)
        ((doc ((c.i + 1).toNat - 1)).drop 61 ++ (doc ((c.i + 1).toNat)).take 29)
        (((doc ((c.i + 1).toNat)).drop 31).take 32)
        (((doc ((c.i + 1).toNat)).drop 30).take 32)
        (((doc ((c.i + 1).toNat)).drop 29).take 32)).or291.length = 4)
    (hcall : ∀ (args : List Value) (mem : Mem) (next : Nat),
      ∃ r : CallOutcome, sel escapeListCallee args mem next = some r)
    (hkeep : ∀ (or14 mask xs i : BitVec 64) (mem : Mem) (next : Nat)
      (r : CallOutcome),
      sel escapeListCallee
        [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
         .ptr xp, .ptr nxp, .ptr xcarry] mem next = some r →
      (∀ j, j < c.shr.toNat → readBytes r.mem (c.b + 64 * j) 64 = some (doc j)) ∧
      readBytes r.mem (c.b - 3) 3 = some [0, 0, 0]) :
    let v38 := ifThen38Values v.addPtr v.i bs2 bs3
        ((doc ((c.i + 1).toNat - 1)).drop 63 ++ (doc ((c.i + 1).toNat)).take 31)
        ((doc ((c.i + 1).toNat - 1)).drop 62 ++ (doc ((c.i + 1).toNat)).take 30)
        ((doc ((c.i + 1).toNat - 1)).drop 61 ++ (doc ((c.i + 1).toNat)).take 29)
        (((doc ((c.i + 1).toNat)).drop 31).take 32)
        (((doc ((c.i + 1).toNat)).drop 30).take 32)
        (((doc ((c.i + 1).toNat)).drop 29).take 32)
    let sH := asciiHandoffState env s c v
    let s4 := stateAt (ifThen38Out (asciiHandoffEnv env c v) v38)
      { sH with pc := "if.end50", pre := some "if.then38" }
    let s5 := stateAt (fb54PageEnv env c v v38)
      { s4 with pc := "for.body54.lr.ph", pre := some "if.end50" }
    ∃ (e : State) (M : Nat),
      M ≤ 5 * c.shr.toNat + 13 ∧
      (∀ k, runFuel (s1BlocksCallsEsc sel) (M + k) s1BlocksFunction sH =
        runFuel (s1BlocksCallsEsc sel) k s1BlocksFunction e) ∧
      ExitTermCells b n conv arm e := by
  intro v38 sH s4 s5
  obtain ⟨h01, h12⟩ := asciiHandoff_run env s c v bs2 bs3 doc hinv.toAsciiInv hv
    hread2 hread3 hshr57 hne hgap hdoc hbit
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
      hinv.emit hinv.bound hxp hnxp hxcarry hi63 hshl63 hread73
      hread74 h73len h74len hascii_len hu8k_len hb3 hzeroPage hdocPage
      hirow
      hgap hshr57 hcall hkeep
  have hrun5 : ∀ j, runFuel (s1BlocksCallsEsc sel) (k + j) s1BlocksFunction s5 =
      runFuel (s1BlocksCallsEsc sel) j s1BlocksFunction (stateAt envL core) :=
    fun j => hrun j
  rcases BlockEval.bitVec1_eq_zero_or_one (evalICmp .eq (v38.inc49 + 1) c'.shr)
    with hbitL | hbitL
  · -- the back edge and the loop's own induction
    obtain ⟨hstep, hinv'⟩ :=
      fused_latch_loop sel envL core (v38.inc49) c' (evalICmp .eq conv 0)
        (evalICmp .eq (arm &&& 2) 0) hl hbitL (by rw [hshrEq]; exact hshr57)
    have hcells' : EntryCells (ifEnd98Env envL (v38.inc49) c'.shr) n conv arm :=
      entryCells_ifEnd98Env envL (v38.inc49) c'.shr hcellsL
    have hshr57' : c'.shr.toNat < 2 ^ 57 := by rw [hshrEq]; exact hshr57
    have hb3' : 3 ≤ c'.b := by rw [hbEq]; exact hb3
    have hgap' : c'.b + 64 * c'.shr.toNat ≤ c'.ent := by
      rw [hbEq, hshrEq, hentEq]; exact hgap
    have hdocLoop : ∀ j, j < c'.shr.toNat →
        readBytes c'.mem (c'.b + 64 * j) 64 = some (doc j) := by
      intro j hj
      rw [hshrEq] at hj
      rw [hbEq]
      exact hdoc' j hj
    have hzeroLoop : readBytes c'.mem (c'.b - 3) 3 = some [0, 0, 0] := by
      rw [hbEq]; exact hzero'
    have hkeepLoop : ∀ (or14 mask xs i : BitVec 64) (mem : Mem) (next : Nat)
        (r' : CallOutcome),
        sel escapeListCallee
          [.int 64 or14, .int 64 mask, .int 64 xs, .int 64 i,
           .ptr c'.xp, .ptr c'.nxp, .ptr c'.xcarry] mem next = some r' →
        (∀ j, j < c'.shr.toNat →
            readBytes r'.mem (c'.b + 64 * j) 64 = some (doc j)) ∧
        readBytes r'.mem (c'.b - 3) 3 = some [0, 0, 0] := by
      intro or14 mask xs i mem next r' hc'
      have h := hkeep or14 mask xs i mem next r' (by
        simpa only [hxpEq, hnxpEq, hxcEq] using hc')
      simpa only [hbEq, hshrEq] using h
    obtain ⟨e', j, hjle, hterm, hrun'⟩ :=
      fusedInvCells_runFuel sel (ifEnd98Env envL (v38.inc49) c'.shr)
        (stateAt (ifEnd98Env envL (v38.inc49) c'.shr)
          { core with pc := "for.body54", pre := some "if.end98" })
        c' (evalICmp .eq conv 0) (evalICmp .eq (arm &&& 2) 0) n conv arm doc
        hshr57'
        { toFusedInv := hinv'
          n_cell := hcells'.n_cell
          conv_cell := hcells'.conv_cell
          arm_cell := hcells'.arm_cell
          and_cell := hcells'.and_cell
          shr_cell := hcells'.shr_cell }
        hb3' hgap' hdocLoop hzeroLoop hcall hkeepLoop
    rcases hterm with ⟨envE, sE, cE, gateE, escE, hcellsE, hasciiE, hexitE⟩
    refine ⟨_, 2 + (k + (1 + j)), ?_, ?_,
      ExitTermCells.fused envE sE cE gateE escE hcellsE hasciiE hexitE⟩
    · -- the loop's `5 * (shr - (i + 1)) + 5` drops its index above `5 * shr + 5`
      have hj' : j ≤ 5 * c'.shr.toNat + 5 := by omega
      rw [← hshrEq]
      omega
    · intro k'
      rw [show 2 + (k + (1 + j)) + k' = 2 + (k + (1 + (j + k'))) from by omega,
        runFuel_jump2 h01' h12' (k + (1 + (j + k'))), hrun5 (1 + (j + k')),
        runFuel_jump_prefix hstep (j + k')]
      exact hrun' k'
  · -- the bound's exit
    obtain ⟨hstep, hexit⟩ :=
      fused_latch_exit sel envL core (v38.inc49) c' (evalICmp .eq conv 0)
        (evalICmp .eq (arm &&& 2) 0) hl hbitL
    refine ⟨_, 2 + (k + 1), ?_, ?_,
      ExitTermCells.fused (ifEnd98Env envL (v38.inc49) c'.shr)
        (stateAt (ifEnd98Env envL (v38.inc49) c'.shr)
          { core with pc := "for.end101", pre := some "if.end98" }) c'
        (evalICmp .eq conv 0) (evalICmp .eq (arm &&& 2) 0)
        (entryCells_ifEnd98Env envL (v38.inc49) c'.shr hcellsL) hl.ascii_len hexit⟩
    · omega
    · intro k'
      rw [show 2 + (k + 1) + k' = 2 + (k + (1 + k')) from by omega,
        runFuel_jump2 h01' h12' (k + (1 + k')), hrun5 (1 + k'),
        runFuel_jump_prefix hstep k']
      rfl

/-! ### The one-prefix with its fuel exposed -/

/-- **The charged one-prefix, bounded.**  A run segment from `s1BlocksInit` at
some fuel `N`, ending at the entry's exit terminal, with `N` inside the
prefix's charge `8 * (%n >>> 6) + 21`. -/
def OnePrefixBounded (esc : Calls) (args : List Value) (mem : Mem) (b : Nat)
    (n : BitVec 64) (conv : BitVec 32) (arm : BitVec 64) : Prop :=
  ∃ (e : State) (N : Nat),
    N ≤ 8 * (n >>> 6).toNat + 21 ∧
    (∀ k, runFuel (s1BlocksCallsEsc esc) (N + k) s1BlocksFunction
      (s1BlocksInit args mem) = runFuel (s1BlocksCallsEsc esc) k s1BlocksFunction e) ∧
    ExitTermCells b n conv arm e

/-- **The entry reaches the exit, with its fuel.**  The phase's bounded prefix
and the hand-off's bounded continuation compose: the phase's terminal is either
its own bound, which already is an exit terminal, or a hand-off, which
`handoffPrefix_exit_bounded` continues at `5 * %shr + 13`.  The two charges sum
to the exposed `8 * (%n >>> 6) + 21`. -/
theorem s1BlocksPrefix_exit_bounded (esc : Calls) (mem : Mem)
    (b ent xp nxp xcarry : Nat) (n arm : BitVec 64)
    (bs : List UInt8) (doc : Nat → List UInt8) (bs73 bs74 : List UInt8)
    (hlong : evalICmp .ult n 64 = 0)
    (hread2 : readBytes mem b 32 = some ((docBlock bs 0).take 32))
    (hread3 : readBytes mem (b + 32) 32 = some ((docBlock bs 0).drop 32))
    (hgate : evalICmp .eq (arm &&& 2) 0 = 1)
    (hfirst : evalICmp .eq (ifEndTest
      (forBodyValues 0 0 0 0 0 ((docBlock bs 0).take 32) ((docBlock bs 0).drop 32)
        b ent).w2
      (forBodyValues 0 0 0 0 0 ((docBlock bs 0).take 32) ((docBlock bs 0).drop 32)
        b ent).w3) 0 = 0)
    (hgap : b + 64 * (n >>> 6).toNat ≤ ent)
    (hdoc : ∀ j, j < (n >>> 6).toNat →
      readBytes mem (b + 64 * j) 64 = some (doc j))
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
    OnePrefixBounded esc [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp, .ptr xcarry,
      .int 64 arm] mem b n (entryGate arm) arm := by
  obtain ⟨e, N, hN, hpref, hterm⟩ :=
    s1BlocksPrefix_stream_bounded esc mem b ent xp nxp xcarry n arm bs doc hlong
      hread2 hread3 hgate hfirst hgap hdoc hshr57
  cases hterm with
  | exit env s c hinv hbound =>
      refine ⟨asciiExitState env s c, N, ?_, hpref,
        ExitTermCells.ascii env s c hinv hbound⟩
      omega
  | handoff env s c bs2 bs3 v hinv hstream h2 h3 hne hv =>
      have hcar := hready env s c bs2 bs3 v hinv hstream h2 h3 hne hv
      have hshreq : c.shr = n >>> 6 := by
        have h1 := hinv.bound
        rw [hinv.shr_cell] at h1
        simpa using (Option.some.inj h1).symm
      have hshr57' : c.shr.toNat < 2 ^ 57 := by rw [hshreq]; exact hshr57
      have hb3' : 3 ≤ c.b := by rw [hinv.b_eq]; exact hb3
      have hbit : evalICmp .ult (v.i + 1) c.shr = 1 := by
        show BitVec.ofBool (BitVec.ult (v.i + 1) c.shr) = 1
        rw [(BitVec.ult_iff_toNat_lt).2 hcar.irow]
        rfl
      obtain ⟨e', M, hM, hcont, hterm'⟩ :=
        handoffPrefix_exit_bounded esc env s c v bs2 bs3 doc b n (entryGate arm) arm
          xp nxp xcarry bs73 bs74 hinv hv h2 h3 hne hbit hshr57' hcar.entGap
          hcar.docMem hb3' hstream.xp_cell hstream.nxp_cell hstream.xcarry_cell
          hcar.docPage hcar.zeroPage hcar.irow hcar.i63 hcar.shl63 hcar.read73
          hcar.read74 hcar.len73 hcar.len74 hcar.asciiLen hcar.u8kLen hcar.call
          hcar.keep
      have hM' : M ≤ 5 * (n >>> 6).toNat + 13 := by
        rw [hshreq] at hM
        exact hM
      refine ⟨e', N + M, ?_, ?_, hterm'⟩
      · omega
      · intro k
        rw [show N + M + k = N + (M + k) from by omega, hpref (M + k)]
        exact hcont k

/-- **The committed prefix's hypotheses give the bounded prefix.**  This is
`JsonS1BlocksLoopRun.onePrefix_of_exit` with the fuel kept: the committed
prefix's inputs, which the record's selection already supplies, are enough. -/
theorem onePrefixBounded_of_exit (esc : Calls) (mem : Mem)
    (b ent xp nxp xcarry : Nat) (n arm : BitVec 64)
    (bs : List UInt8) (doc : Nat → List UInt8) (bs73 bs74 : List UInt8)
    (hlong : evalICmp .ult n 64 = 0)
    (hread2 : readBytes mem b 32 = some ((docBlock bs 0).take 32))
    (hread3 : readBytes mem (b + 32) 32 = some ((docBlock bs 0).drop 32))
    (hgate : evalICmp .eq (arm &&& 2) 0 = 1)
    (hfirst : evalICmp .eq (ifEndTest
      (forBodyValues 0 0 0 0 0 ((docBlock bs 0).take 32) ((docBlock bs 0).drop 32)
        b ent).w2
      (forBodyValues 0 0 0 0 0 ((docBlock bs 0).take 32) ((docBlock bs 0).drop 32)
        b ent).w3) 0 = 0)
    (hgap : b + 64 * (n >>> 6).toNat ≤ ent)
    (hdoc : ∀ j, j < (n >>> 6).toNat →
      readBytes mem (b + 64 * j) 64 = some (doc j))
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
    OnePrefixBounded esc [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp, .ptr xcarry,
      .int 64 arm] mem b n (entryGate arm) arm :=
  s1BlocksPrefix_exit_bounded esc mem b ent xp nxp xcarry n arm bs doc bs73 bs74
    hlong hread2 hread3 hgate hfirst hgap hdoc hshr57 hb3 hready

/-! ### The run at the budget, with the fuel discharged

`JsonS1BlocksLoopRun.s1BlocksRun_at_budget` takes the prefix's fuel `N` and its
containment in the budget.  The bounded prefix supplies both: `N` with
`N ≤ 8 * (%n >>> 6) + 21`, and `prefixCharge_le_budget` inside the record's
term.  What remains is the exit's own run and its charge. -/

/-- **The bounded prefix, at the record's budget.**  The exposed charge
`8 * (%n >>> 6) + 21` lies inside `s1BlocksBudget` (`prefixCharge_le_budget`),
so the bounded prefix is a prefix whose fuel is inside the record's term: the
`N ≤ s1BlocksBudget` hypothesis `s1BlocksRun_at_budget` takes is discharged. -/
theorem OnePrefixBounded.atBudget {esc : Calls} {args : List Value} {mem : Mem}
    {b ent xp nxp xcarry : Nat} {n : BitVec 64} {conv : BitVec 32}
    {arm : BitVec 64}
    (hargs : args = [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp, .ptr xcarry,
      .int 64 arm])
    (h : OnePrefixBounded esc args mem b n conv arm) :
    ∃ (e : State) (N : Nat),
      N ≤ s1BlocksBudget args mem ∧
      (∀ k, runFuel (s1BlocksCallsEsc esc) (N + k) s1BlocksFunction
        (s1BlocksInit args mem) = runFuel (s1BlocksCallsEsc esc) k s1BlocksFunction e) ∧
      ExitTermCells b n conv arm e := by
  obtain ⟨e, N, hN, htrace, hterm⟩ := h
  have hbound := prefixCharge_le_budget (args := args) (mem := mem) (b := b)
    (ent := ent) (xp := xp) (nxp := nxp) (xcarry := xcarry) (n := n) (arm := arm)
    hargs
  exact ⟨e, N, by omega, htrace, hterm⟩

/-- **The run at the budget, from the bounded prefix.**  With the exit's run at
`jE` and `jE` inside the budget above the prefix's charge, the run from
`EntryState` at `next = 1` completes at `s1BlocksBudget`.  The prefix's fuel is
not a hypothesis: it is the bounded prefix's witness, and its containment is
`prefixCharge_le_budget`. -/
theorem s1BlocksRun_at_budget_of_boundedPrefix {esc : Calls} {args : List Value}
    {mem : Mem} {b ent xp nxp xcarry : Nat} {n : BitVec 64} {conv : BitVec 32}
    {arm ret : BitVec 64} {M : Mem} {jE : Nat}
    (hargs : args = [.ptr b, .int 64 n, .ptr ent, .ptr xp, .ptr nxp, .ptr xcarry,
      .int 64 arm])
    (hprefix : OnePrefixBounded esc args mem b n conv arm)
    (hjE : jE ≤ s1BlocksBudget args mem - (8 * (n >>> 6).toNat + 21))
    (hexit : ∀ e : State, ExitTermCells b n conv arm e →
      runFuel (s1BlocksCallsEsc esc) jE s1BlocksFunction e =
        some (.ret (some (.int 64 ret)) M)) :
    runFuel (s1BlocksCallsEsc esc) (s1BlocksBudget args mem) s1BlocksFunction
        (EntryState s1BlocksFunction args mem 1) = some (.ret (some (.int 64 ret)) M) := by
  obtain ⟨e, N, hN, htrace, hterm⟩ := hprefix
  have hbound := prefixCharge_le_budget (args := args) (mem := mem) (b := b)
    (ent := ent) (xp := xp) (nxp := nxp) (xcarry := xcarry) (n := n) (arm := arm)
    hargs
  refine LeanLLVM.Refinement.JsonS1BlocksLoopRun.s1BlocksRun_at_budget htrace ?_ ?_
    (hexit e hterm)
  · omega
  · omega

/-! ### Axiom footprints

The two compositions are `JsonS1BlocksStream`'s and `JsonS1BlocksPrefix`'s own
step and induction lemmas with their arithmetic kept; the budget step is
`ushr_six_toNat`, `Nat.div_le_div_right` and `s1BlocksBudget`'s definition, and
the final composition is `s1BlocksRun_at_budget`'s monotonicity.  No statement
reaches `sorryAx`. -/

#print axioms LeanLLVM.Refinement.JsonS1BlocksPrefixFuel.shift_le_blocksOf
#print axioms LeanLLVM.Refinement.JsonS1BlocksPrefixFuel.prefixCharge_le_budget
#print axioms LeanLLVM.Refinement.JsonS1BlocksPrefixFuel.s1BlocksPrefix_stream_bounded
#print axioms LeanLLVM.Refinement.JsonS1BlocksPrefixFuel.handoffPrefix_exit_bounded
#print axioms LeanLLVM.Refinement.JsonS1BlocksPrefixFuel.OnePrefixBounded
#print axioms LeanLLVM.Refinement.JsonS1BlocksPrefixFuel.s1BlocksPrefix_exit_bounded
#print axioms LeanLLVM.Refinement.JsonS1BlocksPrefixFuel.onePrefixBounded_of_exit
#print axioms LeanLLVM.Refinement.JsonS1BlocksPrefixFuel.OnePrefixBounded.atBudget
#print axioms LeanLLVM.Refinement.JsonS1BlocksPrefixFuel.s1BlocksRun_at_budget_of_boundedPrefix

end LeanLLVM.Refinement.JsonS1BlocksPrefixFuel
