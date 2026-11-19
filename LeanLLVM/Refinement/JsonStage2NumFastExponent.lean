/-
Tier 1's exponent route: the run's carry to the conversion past its exit.

`JsonStage2NumFastGate.nest_expRun_run` reaches `cleanup223.thread` with the
run's exit word, the four carried cells by value and the stop word, but the
merge past the run reads more than those: `JsonStage2NumFastRun.t1_arm_run`
reads `%out`, the two table symbols and the sign at `if.end230`, and the two
table rows at the staging memory.  This module closes that seam, one stage
before the exponent merge itself:

1. **The run's carry.**  `expRunEndFrameCarried` frames
   `NumFastGate.expRunEndBoundLoopStop` on the caller's kept cells, its sign
   (`NumFastCarried`) and the staging the run reads (`s.mem = mem0`).
   `expRun_step_loop`'s and `expRun_step_exit`'s arms hand the carried words
   back, and both also hand the endpoint's memory, which is the step's source's
   (`stateAt` writes the environment and nothing else).
2. **The run at the whole distance.**  `expRun_run_carried` is the framed
   induction: from `expRunInv` at the head, the four cells, the caller's words
   and the staging, the run reaches `cleanup223.thread` within
   `(n - i0 + 1) * cost` control steps carrying the exit word, the four cells,
   `expRunStop`, the caller's words and the same memory.
3. **The nest handoff.**  `nest_expRun_run_carried` composes the marker nest's
   own seams (`nestTo157_e`/`_E`, `nestFrom157_nosign`/`_sign`) and
   `expRun_start` with the framed run: from the marker's block, the route
   reaches `cleanup223.thread` carrying the exit word, the four cells, the stop
   word, the caller's kept cells and sign, and the staging memory, within
   `10 + (n - i11 + 1) * 4` control steps.
4. **The control.**  `expRunStop_not_carried` exhibits an exit state of the
   run's stop word whose `%out` is unbound, so no reference environment binding
   `%out` carries through it: the frame's property is load-bearing and not a
   consequence of the run's exit.

There is no `sorry`, `admit` or `native_decide` below.
-/
import LeanLLVM.Refinement.JsonStage2NumFastGate

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.BlockEval

/-! ### The run framed on the caller's words

The loop is `NumFastGate.expRunEndBoundLoopStop`, so its exit word is the triple
`expRunExit ∧ ExpRunCells ∧ expRunStop`; the caller's property is the two words
`if.end230` reads besides the cells — the kept registers and the sign, and the
staging the two table rows come from.  Each arm hands it back at its own
endpoint: the carried words through the arm's conditional transport, and the
staging through the endpoint's own memory. -/

/-- **The exponent run's loop, framed on the caller's kept cells, its sign and
the staging memory.**  The loop is `NumFastGate.expRunEndBoundLoopStop`, so the
exit word keeps `expRunStop`; the property is `NumFastCarried` and
`s.mem = mem0`. -/
def expRunEndFrameCarried {calls : Calls} (mem0 : Mem) (p n i0 : Nat)
    (bs : List UInt8) (cost : Nat) (hcost : 4 ≤ cost)
    (idig5 ip5 fr5 fd5 : BitVec 64) (env0 : Env) (sign : BitVec 1) :
    BoundLoopFrame calls numFastBody :=
  { loop := NumFastGate.expRunEndBoundLoopStop calls mem0 p n i0 bs cost hcost
      idig5 ip5 fr5 fd5
    P := fun s => NumFastCarried env0 sign s ∧ s.mem = mem0
    step_exit := by
      intro r s c hinv hb
      obtain ⟨e, j, hj, hpc, hword, hstop, hcell, hcarried, hmem, hrun⟩ :=
        expRun_step_exit hinv.1 hb
      refine ⟨e, j, by simp only [NumFastGate.expRunEndBoundLoopStop]; omega, hpc,
        ⟨hword, hcell idig5 ip5 fr5 fd5 hinv.2, hstop⟩, ?_, hrun⟩
      intro hP
      exact ⟨hcarried env0 sign hP.1, by rw [hmem]; exact hP.2⟩
    step_loop := by
      intro r s c hinv hb
      obtain ⟨e, c', j, hj, hpc, hlt, hinv', hcell, hcarried, hmem, hrun⟩ :=
        expRun_step_loop hinv.1 hb
      refine ⟨e, c', j, by simp only [NumFastGate.expRunEndBoundLoopStop]; omega, hpc,
        hlt, ⟨hinv', hcell idig5 ip5 fr5 fd5 hinv.2⟩, ?_, hrun⟩
      intro hP
      exact ⟨hcarried env0 sign hP.1, by rw [hmem]; exact hP.2⟩ }

/-- **The exponent run reaches its exit with the caller's words.**  At the whole
distance as its budget, the head reaches `cleanup223.thread` within
`(n - i0 + 1) * cost` control steps carrying the exit word, the four cells, the
stop word, the kept cells and sign, and the staging the exit read. -/
theorem expRun_run_carried {calls : Calls} (mem0 : Mem) (p n i0 : Nat)
    (bs : List UInt8) (cost : Nat) (hcost : 4 ≤ cost)
    (idig5 ip5 fr5 fd5 : BitVec 64) (env0 : Env) (sign : BitVec 1)
    (s : State) (c : Nat)
    (hinv : expRunInv mem0 p n i0 bs (n - i0) s c)
    (hpart : ExpRunCells idig5 ip5 fr5 fd5 s)
    (hcarried : NumFastCarried env0 sign s) (hmem : s.mem = mem0) (k : Nat) :
    ∃ (e : State) (j : Nat), j ≤ (n - i0 + 1) * cost ∧
      e.pc = "cleanup223.thread" ∧ expRunExit e ∧
      ExpRunCells idig5 ip5 fr5 fd5 e ∧ expRunStop p n i0 e ∧
      NumFastCarried env0 sign e ∧ e.mem = mem0 ∧
      runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e := by
  obtain ⟨e, j, hj, hexit, ⟨hword, hcells, hstop⟩, ⟨hcar, hmemE⟩, hrun⟩ :=
    (expRunEndFrameCarried (calls := calls) mem0 p n i0 bs cost hcost
      idig5 ip5 fr5 fd5 env0 sign).run s c ⟨hinv, hpart⟩ ⟨hcarried, hmem⟩ k
  exact ⟨e, j, hj, hexit, hword, hcells, hstop, hcar, hmemE, hrun⟩

/-! ### The nest handoff

`NumFastGate.nest_expRun_run` composes the marker nest with the run, but the
carries it names are only those of the run's own start: the caller's kept cells
and sign, and the staging memory, do not appear in its conclusion.  The nest's
lower seams hand both forward (`nestTo157_e`/`_E`, `nestFrom157_nosign`/`_sign`,
`nestEntry_run`), `expRun_start` hands the run's own, and the run's frame
(`expRunEndFrameCarried`) carries them to its exit.  This section spends them in
one composition from the marker's block. -/

/-- **The exponent route's carried chain.**  From the marker's block at `%i.10`,
with the byte there an `'e'` or an `'E'`, the sign byte after it, every byte from
the exponent's first index a digit, the four cells `if.end230`'s `phi`s read
carried at the marker's start, and the caller's kept registers, sign and staging
memory, the nest's steps and the exponent run reach `cleanup223.thread` within
`10 + (n - i11 + 1) * 4` control steps.  At the exit the chain hands the run's
exit word, the four cells by value, the stop word, the caller's kept cells and
sign, and the same memory: `%i.11` is the exponent's first index, and the stop
index is the length on the back edge and a non-digit byte inside the lexeme on
the head's.  What the chain does not supply is the accumulator's reading as the
exponent digits' `expAcc`, which the merge's seam still takes as its own
hypothesis. -/
theorem nest_expRun_run_carried {calls : Calls} {e : State} {a n i10 : Nat}
    {b1 b2 : UInt8} {bs : List UInt8} {idig5 ip5 fr5 fd5 : BitVec 64}
    {env0 : Env} {sign : BitVec 1}
    (hpc : e.pc = "land.lhs.true147")
    (hp : lookupName e.env "%p" = some (.ptr a))
    (hi : lookupName e.env "%i.10" = some (.int 64 (BitVec.ofNat 64 i10)))
    (hn : lookupName e.env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hnlt : n < 2 ^ 63)
    (hread : readBytes e.mem a n = some bs)
    (hmarker : readByte e.mem (a + i10) = some b1)
    (hmarkerAt : b1 = 0x65 ∨ b1 = 0x45)
    (hin : i10 + 3 ≤ n)
    (hread2 : readByte e.mem (a + (i10 + 1)) = some b2)
    (hdigits : ∀ k, i10 + 1 ≤ k → k < n → IsDigitB (bs.getD k 0) = true)
    (hcarry : ExpRunCells idig5 ip5 fr5 fd5 (stateAt e.env e))
    (hcarried : NumFastCarried env0 sign (stateAt e.env e)) :
    ∃ (i11 : Nat) (esign : BitVec 1) (e' : State) (j : Nat),
      j ≤ 10 + (n - i11 + 1) * 4 ∧
      e'.pc = "cleanup223.thread" ∧
      expRunExit e' ∧ ExpRunCells idig5 ip5 fr5 fd5 e' ∧ expRunStop a n i11 e' ∧
      NumFastCarried env0 sign e' ∧ e'.mem = e.mem ∧
      lookupName e'.env "%esign.0" = some (.int 1 esign) ∧
      (i11 = i10 + 1 ∨ i11 = i10 + 2) ∧
      ∀ k, runFuel calls (j + k) numFastBody (stateAt e.env e) =
        runFuel calls k numFastBody e' := by
  rcases hmarkerAt with rfl | rfl
  · -- the marker is `'e'`: the pivot takes `LeafBlock1`
    let env1 : Env := NumFastScanRun.leafBlock1Env
      (NumFastScanRun.nodeBlockEnv (NumFastScanRun.t147Env e.env a i10 0x65) 0x65) 0x65
    have hnest := NumFastScanRun.nestTo157_e (calls := calls) hpc hp hi (by omega) hmarker
    have hrun3 : ∀ k, runFuel calls (3 + k) numFastBody (stateAt e.env e) =
        runFuel calls k numFastBody
          (stateAt env1 { e with pc := "if.then157", pre := some "LeafBlock1" }) :=
      hnest.2.2
    have hc1 : ExpRunCells idig5 ip5 fr5 fd5
        (stateAt env1 { e with pc := "if.then157", pre := some "LeafBlock1" }) :=
      hnest.1 idig5 ip5 fr5 fd5 hcarry
    have hcar1 : NumFastCarried env0 sign
        (stateAt env1 { e with pc := "if.then157", pre := some "LeafBlock1" }) :=
      hnest.2.1 env0 sign hcarried
    have hp1 : lookupName env1 "%p" = some (.ptr a) := by
      simp only [env1, NumFastScanRun.leafBlock1Env, NumFastScanRun.nodeBlockEnv,
        NumFastScanRun.t147Env]
      block_lk
    have hi1 : lookupName env1 "%i.10" = some (.int 64 (BitVec.ofNat 64 i10)) := by
      simp only [env1, NumFastScanRun.leafBlock1Env, NumFastScanRun.nodeBlockEnv,
        NumFastScanRun.t147Env]
      block_lk
    have hn1 : lookupName env1 "%n" = some (.int 64 (BitVec.ofNat 64 n)) := by
      simp only [env1, NumFastScanRun.leafBlock1Env, NumFastScanRun.nodeBlockEnv,
        NumFastScanRun.t147Env]
      block_lk
    by_cases hsign : b2 = 0x2b ∨ b2 = 0x2d
    · -- a sign follows the marker: `%i.11 = %i.10 + 2`
      obtain ⟨e', hpc', hmem', hp2, hn2, hi11, hes, hcell', hcar', hrun6⟩ :=
        NumFastScanRun.nestFrom157_sign (calls := calls) (env := env1)
          (s := { e with pc := "if.then157", pre := some "LeafBlock1" })
          rfl hp1 hi1 hn1 hnlt (by omega) hread2 hsign
      have hmemE : e'.mem = e.mem := hmem'
      have hcE : ExpRunCells idig5 ip5 fr5 fd5 e' := hcell' idig5 ip5 fr5 fd5 hc1
      have hcarE : NumFastCarried env0 sign e' := hcar' env0 sign hcar1
      have hcarry' : expRunCarried e'.env := by
        obtain ⟨h1, h2, h3, h4⟩ := hcE
        exact ⟨idig5, ip5, fr5, fd5, h1, h2, h3, h4⟩
      have hjlt : i10 + 2 < n := by omega
      have hd : readByte e'.mem (a + (i10 + 2)) = some (bs.getD (i10 + 2) 0) := by
        rw [hmemE]
        exact readByte_of_readBytes hread hjlt
      have hdigB : IsDigitB (bs.getD (i10 + 2) 0) = true :=
        hdigits (i10 + 2) (by omega) hjlt
      obtain ⟨e'', hinv, hcellsT, hcarriedT, hrun1⟩ :=
        NumFastStarts.expRun_start (calls := calls) (env := e'.env) (s := e')
          hpc' hp2 hn2 (by rw [hmemE]; exact hread) hi11 ⟨_, hes⟩ hcarry' hd hdigB
          (by omega) hnlt
      have hc2 : ExpRunCells idig5 ip5 fr5 fd5 e'' :=
        hcellsT idig5 ip5 fr5 fd5 (by rw [NumFastTaken.stateAt_env_self e']; exact hcE)
      have hcar2 : NumFastCarried env0 sign e'' :=
        hcarriedT env0 sign (by rw [NumFastTaken.stateAt_env_self e']; exact hcarE)
      obtain ⟨e3, j3, hj3, hexit3, ⟨hword3, hcells3, hstop3⟩, ⟨hcar3, hmem3⟩, hrun3'⟩ :=
        (expRunEndFrameCarried (calls := calls) e'.mem a n (i10 + 2) bs 4 (by omega)
            idig5 ip5 fr5 fd5 env0 sign).run_from (n - (i10 + 2)) e'' 0 ⟨hinv, hc2⟩
            ⟨hcar2, hinv.2.1⟩
      obtain ⟨esign, hes'⟩ := hword3.2.2.1
      refine ⟨i10 + 2, esign, e3, (3 + 6 + 1) + j3, ?_, hexit3, hword3, hcells3,
        hstop3, hcar3, hmem3.trans hmemE, hes', Or.inr rfl, ?_⟩
      · have hb : j3 ≤ (n - (i10 + 2) + 1) * 4 := hj3
        omega
      · intro k
        rw [show 3 + 6 + 1 + j3 + k = 3 + (6 + (1 + (j3 + k))) from by omega,
          hrun3 (6 + (1 + (j3 + k))), hrun6 (1 + (j3 + k)),
          ← NumFastTaken.stateAt_env_self e', hrun1 (j3 + k)]
        exact hrun3' k
    · -- no sign: `%i.11 = %i.10 + 1`
      have hnosign : b2 ≠ 0x2b ∧ b2 ≠ 0x2d :=
        ⟨fun h => hsign (Or.inl h), fun h => hsign (Or.inr h)⟩
      obtain ⟨e', hpc', hmem', hp2, hn2, hi11, hes, hcell', hcar', hrun5⟩ :=
        NumFastScanRun.nestFrom157_nosign (calls := calls) (env := env1)
          (s := { e with pc := "if.then157", pre := some "LeafBlock1" })
          rfl hp1 hi1 hn1 hnlt (by omega) hread2 hnosign
      have hmemE : e'.mem = e.mem := hmem'
      have hcE : ExpRunCells idig5 ip5 fr5 fd5 e' := hcell' idig5 ip5 fr5 fd5 hc1
      have hcarE : NumFastCarried env0 sign e' := hcar' env0 sign hcar1
      have hcarry' : expRunCarried e'.env := by
        obtain ⟨h1, h2, h3, h4⟩ := hcE
        exact ⟨idig5, ip5, fr5, fd5, h1, h2, h3, h4⟩
      have hjlt : i10 + 1 < n := by omega
      have hd : readByte e'.mem (a + (i10 + 1)) = some (bs.getD (i10 + 1) 0) := by
        rw [hmemE]
        exact readByte_of_readBytes hread hjlt
      have hdigB : IsDigitB (bs.getD (i10 + 1) 0) = true :=
        hdigits (i10 + 1) (by omega) hjlt
      obtain ⟨e'', hinv, hcellsT, hcarriedT, hrun1⟩ :=
        NumFastStarts.expRun_start (calls := calls) (env := e'.env) (s := e')
          hpc' hp2 hn2 (by rw [hmemE]; exact hread) hi11 ⟨_, hes⟩ hcarry' hd hdigB
          (by omega) hnlt
      have hc2 : ExpRunCells idig5 ip5 fr5 fd5 e'' :=
        hcellsT idig5 ip5 fr5 fd5 (by rw [NumFastTaken.stateAt_env_self e']; exact hcE)
      have hcar2 : NumFastCarried env0 sign e'' :=
        hcarriedT env0 sign (by rw [NumFastTaken.stateAt_env_self e']; exact hcarE)
      obtain ⟨e3, j3, hj3, hexit3, ⟨hword3, hcells3, hstop3⟩, ⟨hcar3, hmem3⟩, hrun3'⟩ :=
        (expRunEndFrameCarried (calls := calls) e'.mem a n (i10 + 1) bs 4 (by omega)
            idig5 ip5 fr5 fd5 env0 sign).run_from (n - (i10 + 1)) e'' 0 ⟨hinv, hc2⟩
            ⟨hcar2, hinv.2.1⟩
      obtain ⟨esign, hes'⟩ := hword3.2.2.1
      refine ⟨i10 + 1, esign, e3, (3 + 5 + 1) + j3, ?_, hexit3, hword3, hcells3,
        hstop3, hcar3, hmem3.trans hmemE, hes', Or.inl rfl, ?_⟩
      · have hb : j3 ≤ (n - (i10 + 1) + 1) * 4 := hj3
        omega
      · intro k
        rw [show 3 + 5 + 1 + j3 + k = 3 + (5 + (1 + (j3 + k))) from by omega,
          hrun3 (5 + (1 + (j3 + k))), hrun5 (1 + (j3 + k)),
          ← NumFastTaken.stateAt_env_self e', hrun1 (j3 + k)]
        exact hrun3' k
  · -- the marker is `'E'`: the pivot takes `LeafBlock`
    let env1 : Env := NumFastScanRun.leafBlockEnv
      (NumFastScanRun.nodeBlockEnv (NumFastScanRun.t147Env e.env a i10 0x45) 0x45) 0x45
    have hnest := NumFastScanRun.nestTo157_E (calls := calls) hpc hp hi (by omega) hmarker
    have hrun3 : ∀ k, runFuel calls (3 + k) numFastBody (stateAt e.env e) =
        runFuel calls k numFastBody
          (stateAt env1 { e with pc := "if.then157", pre := some "LeafBlock" }) :=
      hnest.2.2
    have hc1 : ExpRunCells idig5 ip5 fr5 fd5
        (stateAt env1 { e with pc := "if.then157", pre := some "LeafBlock" }) :=
      hnest.1 idig5 ip5 fr5 fd5 hcarry
    have hcar1 : NumFastCarried env0 sign
        (stateAt env1 { e with pc := "if.then157", pre := some "LeafBlock" }) :=
      hnest.2.1 env0 sign hcarried
    have hp1 : lookupName env1 "%p" = some (.ptr a) := by
      simp only [env1, NumFastScanRun.leafBlockEnv, NumFastScanRun.nodeBlockEnv,
        NumFastScanRun.t147Env]
      block_lk
    have hi1 : lookupName env1 "%i.10" = some (.int 64 (BitVec.ofNat 64 i10)) := by
      simp only [env1, NumFastScanRun.leafBlockEnv, NumFastScanRun.nodeBlockEnv,
        NumFastScanRun.t147Env]
      block_lk
    have hn1 : lookupName env1 "%n" = some (.int 64 (BitVec.ofNat 64 n)) := by
      simp only [env1, NumFastScanRun.leafBlockEnv, NumFastScanRun.nodeBlockEnv,
        NumFastScanRun.t147Env]
      block_lk
    by_cases hsign : b2 = 0x2b ∨ b2 = 0x2d
    · obtain ⟨e', hpc', hmem', hp2, hn2, hi11, hes, hcell', hcar', hrun6⟩ :=
        NumFastScanRun.nestFrom157_sign (calls := calls) (env := env1)
          (s := { e with pc := "if.then157", pre := some "LeafBlock" })
          rfl hp1 hi1 hn1 hnlt (by omega) hread2 hsign
      have hmemE : e'.mem = e.mem := hmem'
      have hcE : ExpRunCells idig5 ip5 fr5 fd5 e' := hcell' idig5 ip5 fr5 fd5 hc1
      have hcarE : NumFastCarried env0 sign e' := hcar' env0 sign hcar1
      have hcarry' : expRunCarried e'.env := by
        obtain ⟨h1, h2, h3, h4⟩ := hcE
        exact ⟨idig5, ip5, fr5, fd5, h1, h2, h3, h4⟩
      have hjlt : i10 + 2 < n := by omega
      have hd : readByte e'.mem (a + (i10 + 2)) = some (bs.getD (i10 + 2) 0) := by
        rw [hmemE]
        exact readByte_of_readBytes hread hjlt
      have hdigB : IsDigitB (bs.getD (i10 + 2) 0) = true :=
        hdigits (i10 + 2) (by omega) hjlt
      obtain ⟨e'', hinv, hcellsT, hcarriedT, hrun1⟩ :=
        NumFastStarts.expRun_start (calls := calls) (env := e'.env) (s := e')
          hpc' hp2 hn2 (by rw [hmemE]; exact hread) hi11 ⟨_, hes⟩ hcarry' hd hdigB
          (by omega) hnlt
      have hc2 : ExpRunCells idig5 ip5 fr5 fd5 e'' :=
        hcellsT idig5 ip5 fr5 fd5 (by rw [NumFastTaken.stateAt_env_self e']; exact hcE)
      have hcar2 : NumFastCarried env0 sign e'' :=
        hcarriedT env0 sign (by rw [NumFastTaken.stateAt_env_self e']; exact hcarE)
      obtain ⟨e3, j3, hj3, hexit3, ⟨hword3, hcells3, hstop3⟩, ⟨hcar3, hmem3⟩, hrun3'⟩ :=
        (expRunEndFrameCarried (calls := calls) e'.mem a n (i10 + 2) bs 4 (by omega)
            idig5 ip5 fr5 fd5 env0 sign).run_from (n - (i10 + 2)) e'' 0 ⟨hinv, hc2⟩
            ⟨hcar2, hinv.2.1⟩
      obtain ⟨esign, hes'⟩ := hword3.2.2.1
      refine ⟨i10 + 2, esign, e3, (3 + 6 + 1) + j3, ?_, hexit3, hword3, hcells3,
        hstop3, hcar3, hmem3.trans hmemE, hes', Or.inr rfl, ?_⟩
      · have hb : j3 ≤ (n - (i10 + 2) + 1) * 4 := hj3
        omega
      · intro k
        rw [show 3 + 6 + 1 + j3 + k = 3 + (6 + (1 + (j3 + k))) from by omega,
          hrun3 (6 + (1 + (j3 + k))), hrun6 (1 + (j3 + k)),
          ← NumFastTaken.stateAt_env_self e', hrun1 (j3 + k)]
        exact hrun3' k
    · obtain ⟨e', hpc', hmem', hp2, hn2, hi11, hes, hcell', hcar', hrun5⟩ :=
        NumFastScanRun.nestFrom157_nosign (calls := calls) (env := env1)
          (s := { e with pc := "if.then157", pre := some "LeafBlock" })
          rfl hp1 hi1 hn1 hnlt (by omega) hread2
          ⟨fun h => hsign (Or.inl h), fun h => hsign (Or.inr h)⟩
      have hmemE : e'.mem = e.mem := hmem'
      have hcE : ExpRunCells idig5 ip5 fr5 fd5 e' := hcell' idig5 ip5 fr5 fd5 hc1
      have hcarE : NumFastCarried env0 sign e' := hcar' env0 sign hcar1
      have hcarry' : expRunCarried e'.env := by
        obtain ⟨h1, h2, h3, h4⟩ := hcE
        exact ⟨idig5, ip5, fr5, fd5, h1, h2, h3, h4⟩
      have hjlt : i10 + 1 < n := by omega
      have hd : readByte e'.mem (a + (i10 + 1)) = some (bs.getD (i10 + 1) 0) := by
        rw [hmemE]
        exact readByte_of_readBytes hread hjlt
      have hdigB : IsDigitB (bs.getD (i10 + 1) 0) = true :=
        hdigits (i10 + 1) (by omega) hjlt
      obtain ⟨e'', hinv, hcellsT, hcarriedT, hrun1⟩ :=
        NumFastStarts.expRun_start (calls := calls) (env := e'.env) (s := e')
          hpc' hp2 hn2 (by rw [hmemE]; exact hread) hi11 ⟨_, hes⟩ hcarry' hd hdigB
          (by omega) hnlt
      have hc2 : ExpRunCells idig5 ip5 fr5 fd5 e'' :=
        hcellsT idig5 ip5 fr5 fd5 (by rw [NumFastTaken.stateAt_env_self e']; exact hcE)
      have hcar2 : NumFastCarried env0 sign e'' :=
        hcarriedT env0 sign (by rw [NumFastTaken.stateAt_env_self e']; exact hcarE)
      obtain ⟨e3, j3, hj3, hexit3, ⟨hword3, hcells3, hstop3⟩, ⟨hcar3, hmem3⟩, hrun3'⟩ :=
        (expRunEndFrameCarried (calls := calls) e'.mem a n (i10 + 1) bs 4 (by omega)
            idig5 ip5 fr5 fd5 env0 sign).run_from (n - (i10 + 1)) e'' 0 ⟨hinv, hc2⟩
            ⟨hcar2, hinv.2.1⟩
      obtain ⟨esign, hes'⟩ := hword3.2.2.1
      refine ⟨i10 + 1, esign, e3, (3 + 5 + 1) + j3, ?_, hexit3, hword3, hcells3,
        hstop3, hcar3, hmem3.trans hmemE, hes', Or.inl rfl, ?_⟩
      · have hb : j3 ≤ (n - (i10 + 1) + 1) * 4 := hj3
        omega
      · intro k
        rw [show 3 + 5 + 1 + j3 + k = 3 + (5 + (1 + (j3 + k))) from by omega,
          hrun3 (5 + (1 + (j3 + k))), hrun5 (1 + (j3 + k)),
          ← NumFastTaken.stateAt_env_self e', hrun1 (j3 + k)]
        exact hrun3' k

/-! ### The control

The run's stop word says where the run stopped and with which accumulator, and
nothing about the registers the merge past it reads: the exit's `cleanup223.thread`
leaves `%out` alone, and the frame's property is the caller's, not the run's.  The
witness is the back edge's end-of-lexeme stop at an empty lexeme, with `%out`
unbound. -/

/-- **The run's stop word does not carry the caller's words.**  There is an exit
state of `expRunStop` whose `%out` is unbound, so no reference environment that
binds `%out` satisfies `NumFastCarried` there.  This is the control that the
frame's property is load-bearing rather than a consequence of the run. -/
theorem expRunStop_not_carried :
    ∃ (env0 : Env) (sign : BitVec 1) (s : State),
      expRunStop 0 0 0 s ∧ ¬ NumFastCarried env0 sign s := by
  let env : Env :=
    [("%p", .ptr 0), ("%n", .int 64 (BitVec.ofNat 64 0)),
      ("%inc217", .int 64 (BitVec.ofNat 64 0)), ("%exp10.1", .int 64 0)]
  let s : State :=
    { env := env, mem := ([] : Mem), next := 0, pc := "cleanup223.thread",
      pre := some "if.end216" }
  refine ⟨("%out", .ptr 0) :: env, 0, s, ?_, ?_⟩
  · refine ⟨?_, ?_, Or.inr ⟨rfl, 0, 0, ?_, ?_, rfl⟩⟩
    · simp only [s, env]
      block_lk
    · simp only [s, env]
      block_lk
    · simp only [s, env]
      block_lk
    · simp only [s, env]
      block_lk
  · intro h
    have hout := h.1 "%out" (by simp [numFastKept])
    have hnone : lookupName s.env "%out" = none := by
      simp only [s, env]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      rfl
    have hsome : lookupName (("%out", .ptr 0) :: env) "%out" = some (.ptr 0) :=
      lookupName_cons_self ..
    rw [hnone, hsome] at hout
    cases hout

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.expRunEndFrameCarried' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expRunEndFrameCarried

/-- info: 'LeanLLVM.Refinement.expRun_run_carried' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expRun_run_carried

/-- info: 'LeanLLVM.Refinement.nest_expRun_run_carried' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nest_expRun_run_carried

/-- info: 'LeanLLVM.Refinement.expRunStop_not_carried' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expRunStop_not_carried

end LeanLLVM.Refinement
