/-
`num_fast_el1`'s conversion on the fraction route, and the exponent route's
chain from the marker nest to the run's exit.

`JsonStage2NumFastSeams.t1_fracRun_tie` reads the fraction run's end-of-lexeme
edge into `if.then241` with the merge's five registers the model's, but it stops
there: a single step's conclusion is an existential state, so its environment is
not a term a caller can rewrite and no continuation can be appended to it.
`t1_fracEnd230_run` is the same edge as one `runFuel` chain — the gate's step,
`t1_then241_store_run`'s four and `cleanup300`'s return, six control steps from
the fraction run's exit word to the returned value — with `%out`, the sign and
the two table symbols read at the state the caller stages, because no block of
the route writes them.

The exponent route has the same shape one stage earlier.  `nest_marker_start`
hands `%i.11` and `%esign.0`, and `expRun_start` takes the run from there, but
the four cells `if.end230`'s `phi`s read are lost at the nest's existential
exit: its environment is not a term, so the cells have to be named where the run
starts.  `JsonStage2NumFastScanRun.nestFrom157_nosign`/`_sign` hand them back
now, and `nest_expRun_run` composes the marker's two shapes and the sign's
presence, the nest's steps, the gate's dispatch step and the run's loop,
concluding `cleanup223.thread` with the exit word, the four cells by value and
the stop word `expRunStop` — the index the run stopped at and the byte there.
The back arm's index is the length, which is `expExit_merge_back`'s equality
test; the head arm's is short of it, which is `expExit_refuse_head`'s refusal.

There is no `sorry`, `admit` or `native_decide` below.
-/
import LeanLLVM.Refinement.JsonStage2NumFastRun
import LeanLLVM.Refinement.JsonStage2NumFastSeams

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.StrtodRefine
open LeanLLVM.StrtodTier1
open ByteString

namespace NumFastGate

/-- A state's environment is the one it is denoted at. -/
theorem stateAt_env_get (env : Env) (s : State) : (stateAt env s).env = env := rfl

/-! ### The fraction-predecessor gate chain

`if.end230`'s fraction edge reads the integer part's two cells and the run's
accumulator and count; the gate's two tests are the tier-1 window's at the
model's counters, so the block takes `if.then241` with the merge's five
registers the model's.  `t1_then241_store_run` is the arithmetic behind the
block, and `cleanup300`'s return is the last step. -/

/-- **The fraction edge's conversion.**  At the fraction run's end-of-lexeme
exit (`if.end230` from `if.end140`), with the integer part's two cells the
model's, the fraction's bytes the lexeme's and no exponent, the gate's step and
the conversion's five reach the return: one chain of six control steps writes
`strtodSpec`'s eight bytes at `%out` and leaves every byte outside the two slots
as it was. -/
theorem t1_fracEnd230_run {calls : Calls} {s : State} {bs : List UInt8} {d : Decimal}
    {fs : Bytes} {sign : BitVec 1} {out p10 pd err : Nat} {ten : BitVec 64} {c : Code}
    {a n i0 d0 : Nat}
    (he : fracRunEndWord bs a n i0 d0 s)
    (hpart : NumFastIntPart (BitVec.ofNat 64 (intDigits d))
      (BitVec.ofNat 64 (Decimal.digitsNat d.ip)) s)
    (hi0 : i0 ≤ n) (hbn : d0 + n < 2 ^ 64)
    (hfs : d.fr = some fs)
    (hintF : fracDigits d = d0 + (n - i0))
    (hshape : fs.data.toList = (bs.drop (i0 - d0)).take (d0 + (n - i0)))
    (hdig : digitCount d ≤ 15)
    (hex0 : d.ex = none)
    (hsig : lookupName s.env "%tobool274.not" = some (.int 1 sign))
    (hout : lookupName s.env "%out" = some (.ptr out))
    (hp10 : lookupName s.env "@NUMF_EL1_P10" = some (.ptr p10))
    (hpwt : lookupName s.env "@NUMF_EL1_POW10" = some (.ptr pd))
    (hten : ten = BitVec.ofNat 64 (10 ^ fs.length))
    (hrow10 : readBytes s.mem (p10 + fracDigits d * 8) 8
      = some (natToBytes ten.toNat 8))
    (hrowP : ∀ j, j ≤ 22 → readBytes s.mem (pd + j * 8) 8
      = some (natToBytes (uitofpBits ((10 : Nat) ^ j)).toNat 8))
    (hwf : d.wellFormed) (h1 : Tier1 d)
    (hsign : (sign = 1) ↔ d.neg = false)
    (hrc : roundMag (opP d) (opD d) = .fin c) (hcM : c.IsMag) :
    ∃ (k : Nat) (o : CallOutcome),
      runFuel calls k numFastBody (stateAt s.env s) = some (.ret (some o.ret) o.mem) ∧
      o.ret = .int 32 1 ∧
      o.mem = writeBytes s.mem out (wordBytes 8 (strtodSpec d).toBits) ∧
      UnchangedOutside s.mem o.mem [(out, 8), (err, 8)] := by
  obtain ⟨hpc0, hpre, _hn64, _hp, _hn, _hinc142, _hinc141, hfr4, h17, _hcells⟩ := he
  -- the count is the model's fraction digit count
  have h17' : lookupName s.env "%17"
      = some (.int 64 (BitVec.ofNat 64 (fracDigits d))) := by
    rw [h17, NumFastSeams.seven_tie hi0 hbn, ← hintF]
  -- the accumulator is the fraction's digits
  have hlen : d0 + (n - i0) ≤ 19 := by
    have h := hdig
    rw [digitCount, hintF] at h
    omega
  have hfr' : lookupName s.env "%fr.4"
      = some (.int 64 (BitVec.ofNat 64 (Decimal.digitsNat fs))) := by
    rw [hfr4, NumFastScanRun.fr_word_digitsNat (start := i0 - d0)
      (len := d0 + (n - i0)) hshape hlen rfl]
  -- the gate's two tests at the model's counters
  have hsum : BitVec.ofNat 64 (fracDigits d) + BitVec.ofNat 64 (intDigits d)
      = BitVec.ofNat 64 (digitCount d) := by
    rw [digitCount]
    bv_omega
  have hbit1 : evalICmp .ult
      (BitVec.ofNat 64 (fracDigits d) + BitVec.ofNat 64 (intDigits d)) (20#64) = 1 := by
    rw [hsum]
    simpa using NumFastSeams.ult_ofNat_one (i := digitCount d) (n := 20)
      (by omega) (by decide)
  have hbit2 : evalICmp .ult
      ((0 - BitVec.ofNat 64 (fracDigits d)) + (45#64)) (91#64) = 1 := by
    have hsub : (0 - BitVec.ofNat 64 (fracDigits d)) + (45#64)
        = BitVec.ofNat 64 (45 - fracDigits d) := by
      have h := hdig
      rw [digitCount] at h
      bv_omega
    rw [hsub]
    simpa using NumFastSeams.ult_ofNat_one (i := 45 - fracDigits d) (n := 91)
      (by omega) (by decide)
  -- the gate's step
  have hgate : step calls numFastBody (stateAt s.env s) =
      .jump (stateAt (NumFastTier1.t1GateEnv s.env 0
          (BitVec.ofNat 64 (intDigits d))
          (BitVec.ofNat 64 (Decimal.digitsNat d.ip))
          (BitVec.ofNat 64 (Decimal.digitsNat fs))
          (BitVec.ofNat 64 (fracDigits d)))
        { s with pc := "if.then241", pre := some "if.end230" }) :=
    NumFastSeams.ifEnd230_step_end140 (calls := calls) hpc0 hpre hpart.1 hpart.2
      hfr' h17' ⟨hbit1, hbit2⟩
  -- the arithmetic behind the gate
  have hE' : (0 : BitVec 64) = BitVec.ofInt 64 (expVal d) := by
    rw [show expVal d = 0 from by simp only [expVal, hex0]]
    rfl
  have hten' : ten = BitVec.ofNat 64 (10 ^ (d.fr.getD empty).length) := by
    rw [hfs]
    exact hten
  have hfr'' : BitVec.ofNat 64 (Decimal.digitsNat fs)
      = BitVec.ofNat 64 (Decimal.digitsNat (d.fr.getD empty)) := by
    rw [hfs]
    rfl
  obtain ⟨e, hepc, hepre, hemem, hrun⟩ :=
    NumFastTier1.t1_then241_store_run (calls := calls) (env := s.env)
      (s := { s with pc := "if.then241", pre := some "if.end230" })
      (d := d) (sign := sign) (out := out) (p10 := p10) (pd := pd)
      (ten := ten) (c := c)
      (exp10 := 0) (idig := BitVec.ofNat 64 (intDigits d))
      (ip := BitVec.ofNat 64 (Decimal.digitsNat d.ip))
      (fr := BitVec.ofNat 64 (Decimal.digitsNat fs))
      (fdig := BitVec.ofNat 64 (fracDigits d))
      rfl rfl hE' rfl rfl hfr'' rfl hsig hout hp10 hpwt hten' hrow10 hrowP
      hwf h1 hsign hrc hcM
  have hret : step calls numFastBody e =
      .ret (some (.int 32 1)) (stateAt (("%retval.8", .int 32 1) :: e.env) e) :=
    numFast_step_cleanup300_one (calls := calls) (env := e.env) (s := e) hepc hepre
  refine ⟨6, ⟨.int 32 1, writeBytes s.mem out (wordBytes 8 (strtodSpec d).toBits),
    e.next⟩, ?_, rfl, rfl, ?_⟩
  · rw [show (6 : Nat) = 1 + (4 + 1) from rfl, runFuel_jump_prefix hgate, hrun 1]
    simp only [runFuel, hret, stateAt]
    rw [hemem]
  · exact (UnchangedOutside.refl' s.mem [(out, 8), (err, 8)]).write_le
      (a := out) (w := 8) (bs := wordBytes 8 (strtodSpec d).toBits)
      ⟨(out, 8), by simp, le_rfl, by omega⟩
      (by simp only [wordBytes, natToBytes_length, le_refl])

/-! ### The exponent route: the nest and the run

`nest_marker_start` composes the nest's steps, but its exit is an existential
state whose environment is not a term, so a caller cannot re-read the four cells
`if.end230`'s `phi`s read there; `expRun_start` therefore takes them by name at
the gate's state.  `JsonStage2NumFastScanRun.nestFrom157_nosign`/`_sign` now hand
the cells back, and the chain below names them at the marker's start. -/

/-- The exponent run's loop with the four carried cells and the stop word.  The
invariant carries `ExpRunCells` and the exit word carries both it and
`expRunStop`, so a composition past the run reads `%idig.4`, `%ip.5`, `%fr.5`,
`%fdig.4` and the stop index at the state the run leaves rather than through an
existential. -/
def expRunEndBoundLoopStop (calls : Calls) (mem0 : Mem) (p n i0 : Nat)
    (bs : List UInt8) (cost : Nat) (hcost : 4 ≤ cost)
    (idig5 ip5 fr5 fd5 : BitVec 64) : BoundLoop calls numFastBody where
  head := "land.lhs.true195"
  exitBlock := "cleanup223.thread"
  N := n - i0
  cost := cost
  Inv := fun r s c => expRunInv mem0 p n i0 bs r s c ∧ ExpRunCells idig5 ip5 fr5 fd5 s
  atBound := expRunAtBound mem0 p n i0
  Exit := fun e => e.pc = "cleanup223.thread"
  ExitWord := fun e =>
    expRunExit e ∧ ExpRunCells idig5 ip5 fr5 fd5 e ∧ expRunStop p n i0 e
  step_exit := by
    intro r s c hinv hb
    obtain ⟨hinv, hcells⟩ := hinv
    obtain ⟨e, j, hj, hpc, hword, hstop, hcell, _hcarried, _hmem, hrun⟩ :=
      expRun_step_exit hinv hb
    exact ⟨e, j, by omega, hpc, ⟨hword, hcell idig5 ip5 fr5 fd5 hcells, hstop⟩, hrun⟩
  step_loop := by
    intro r s c hinv hb
    obtain ⟨hinv, hcells⟩ := hinv
    obtain ⟨e, c', j, hj, hpc, hlt, hinv', hcell, _hcarried, _hmem, hrun⟩ :=
      expRun_step_loop hinv hb
    exact ⟨e, c', j, by omega, hpc, hlt, ⟨hinv', hcell idig5 ip5 fr5 fd5 hcells⟩, hrun⟩
  exit_at_zero := by
    intro s c h
    obtain ⟨hinv, _⟩ := h
    obtain ⟨_, _, hsum, _, _, _, _, _, _, _, _⟩ := hinv
    unfold expRunAtBound
    have hle : decide (n - i0 ≤ c + 1) = true := decide_eq_true (by omega)
    rw [hle]
    simp
  budget := by
    intro r s c h
    obtain ⟨hinv, _⟩ := h
    obtain ⟨_, _, hsum, _, _, _, _, _, _, _, _⟩ := hinv
    omega

/-- **The exponent route's chain.**  From the marker's block at `%i.10`, with the
byte there an `'e'` or an `'E'`, the sign byte after it, every byte from the
exponent's first index a digit, and the four cells `if.end230`'s `phi`s read
carried at the marker's start, the nest's steps and the exponent run reach
`cleanup223.thread` within `10 + (n - i11 + 1) * 4` control steps.  At the exit
the chain hands the run's exit word, the four cells by value and the stop word:
`%i.11` is the exponent's first index, one past the marker's byte or past a sign
at it, and the stop index is the length on the back edge and a non-digit byte
inside the lexeme on the head's.  The stop word also names the cursor and the
length, so a composition past this chain holds `expExit_merge_back`'s `%n`; the
head exit's counter is the premise `expExit_refuse_head` reads.  What the chain
does not supply is the accumulator's reading as the exponent digits' `expAcc`,
which the back seam still takes as its own hypothesis. -/
theorem nest_expRun_run {calls : Calls} {e : State} {a n i10 : Nat} {b1 b2 : UInt8}
    {bs : List UInt8} {idig5 ip5 fr5 fd5 : BitVec 64}
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
    (hcarry : ExpRunCells idig5 ip5 fr5 fd5 (stateAt e.env e)) :
    ∃ (i11 : Nat) (esign : BitVec 1) (e' : State) (j : Nat),
      j ≤ 10 + (n - i11 + 1) * 4 ∧
      e'.pc = "cleanup223.thread" ∧
      expRunExit e' ∧ ExpRunCells idig5 ip5 fr5 fd5 e' ∧ expRunStop a n i11 e' ∧
      lookupName e'.env "%esign.0" = some (.int 1 esign) ∧
      (i11 = i10 + 1 ∨ i11 = i10 + 2) ∧
      ∀ k, runFuel calls (j + k) numFastBody (stateAt e.env e) =
        runFuel calls k numFastBody e' := by
  have hc0 : ExpRunCells idig5 ip5 fr5 fd5 e := by
    obtain ⟨h1, h2, h3, h4⟩ := hcarry
    exact ⟨by simpa only [stateAt_env_get] using h1, by simpa only [stateAt_env_get] using h2,
      by simpa only [stateAt_env_get] using h3, by simpa only [stateAt_env_get] using h4⟩
  rcases hmarkerAt with rfl | rfl
  · -- the marker is `'e'`: the pivot takes `LeafBlock1`
    let env1 : Env := NumFastScanRun.leafBlock1Env
      (NumFastScanRun.nodeBlockEnv (NumFastScanRun.t147Env e.env a i10 0x65) 0x65) 0x65
    have hrun3 : ∀ k, runFuel calls (3 + k) numFastBody (stateAt e.env e) =
        runFuel calls k numFastBody
          (stateAt env1 { e with pc := "if.then157", pre := some "LeafBlock1" }) :=
      NumFastScanRun.nestTo157_e (calls := calls) hpc hp hi (by omega) hmarker
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
    have hc1 : ExpRunCells idig5 ip5 fr5 fd5
        (stateAt env1 { e with pc := "if.then157", pre := some "LeafBlock1" }) := by
      obtain ⟨h1, h2, h3, h4⟩ := hc0
      refine ⟨?_, ?_, ?_, ?_⟩
      all_goals
        simp only [stateAt_env_get, env1, NumFastScanRun.leafBlock1Env,
          NumFastScanRun.nodeBlockEnv, NumFastScanRun.t147Env]
        block_lk
    by_cases hsign : b2 = 0x2b ∨ b2 = 0x2d
    · -- a sign follows the marker: `%i.11 = %i.10 + 2`
      obtain ⟨e', hpc', hmem', hp2, hn2, hi11, hes, hcell', hrun6⟩ :=
        NumFastScanRun.nestFrom157_sign (calls := calls) (env := env1)
          (s := { e with pc := "if.then157", pre := some "LeafBlock1" })
          rfl hp1 hi1 hn1 hnlt (by omega) hread2 hsign
      have hmemE : e'.mem = e.mem := hmem'
      have hcE : ExpRunCells idig5 ip5 fr5 fd5 e' :=
        hcell' idig5 ip5 fr5 fd5 hc1
      have hcarry' : expRunCarried e'.env := by
        obtain ⟨h1, h2, h3, h4⟩ := hcE
        exact ⟨idig5, ip5, fr5, fd5, h1, h2, h3, h4⟩
      have hjlt : i10 + 2 < n := by omega
      have hd : readByte e'.mem (a + (i10 + 2)) = some (bs.getD (i10 + 2) 0) := by
        rw [hmemE]
        exact readByte_of_readBytes hread hjlt
      have hdigB : IsDigitB (bs.getD (i10 + 2) 0) = true :=
        hdigits (i10 + 2) (by omega) hjlt
      obtain ⟨e'', hinv, hcellsT, _hcarriedT, hrun1⟩ :=
        NumFastStarts.expRun_start (calls := calls) (env := e'.env) (s := e')
          hpc' hp2 hn2 (by rw [hmemE]; exact hread) hi11 ⟨_, hes⟩ hcarry' hd hdigB
          (by omega) hnlt
      have hc2 : ExpRunCells idig5 ip5 fr5 fd5 e'' :=
        hcellsT idig5 ip5 fr5 fd5 (by rw [NumFastTaken.stateAt_env_self e']; exact hcE)
      obtain ⟨e3, j3, hj3, hpc3, ⟨hword3, hcells3, hstop3⟩, hrun3'⟩ :=
        (expRunEndBoundLoopStop calls e'.mem a n (i10 + 2) bs 4 (by omega)
            idig5 ip5 fr5 fd5).run_from (n - (i10 + 2)) e'' 0 ⟨hinv, hc2⟩
      obtain ⟨esign, hes'⟩ := hword3.2.2.1
      refine ⟨i10 + 2, esign, e3, (3 + 6 + 1) + j3, ?_, hpc3, hword3, hcells3,
        hstop3, hes', Or.inr rfl, ?_⟩
      · have hb := hj3
        simp only [expRunEndBoundLoopStop] at hb
        omega
      · intro k
        rw [show 3 + 6 + 1 + j3 + k = 3 + (6 + (1 + (j3 + k))) from by omega,
          hrun3 (6 + (1 + (j3 + k))), hrun6 (1 + (j3 + k)),
          ← NumFastTaken.stateAt_env_self e', hrun1 (j3 + k)]
        exact hrun3' k
    · -- no sign: `%i.11 = %i.10 + 1`
      have hnosign : b2 ≠ 0x2b ∧ b2 ≠ 0x2d :=
        ⟨fun h => hsign (Or.inl h), fun h => hsign (Or.inr h)⟩
      obtain ⟨e', hpc', hmem', hp2, hn2, hi11, hes, hcell', hrun5⟩ :=
        NumFastScanRun.nestFrom157_nosign (calls := calls) (env := env1)
          (s := { e with pc := "if.then157", pre := some "LeafBlock1" })
          rfl hp1 hi1 hn1 hnlt (by omega) hread2 hnosign
      have hmemE : e'.mem = e.mem := hmem'
      have hcE : ExpRunCells idig5 ip5 fr5 fd5 e' :=
        hcell' idig5 ip5 fr5 fd5 hc1
      have hcarry' : expRunCarried e'.env := by
        obtain ⟨h1, h2, h3, h4⟩ := hcE
        exact ⟨idig5, ip5, fr5, fd5, h1, h2, h3, h4⟩
      have hjlt : i10 + 1 < n := by omega
      have hd : readByte e'.mem (a + (i10 + 1)) = some (bs.getD (i10 + 1) 0) := by
        rw [hmemE]
        exact readByte_of_readBytes hread hjlt
      have hdigB : IsDigitB (bs.getD (i10 + 1) 0) = true :=
        hdigits (i10 + 1) (by omega) hjlt
      obtain ⟨e'', hinv, hcellsT, _hcarriedT, hrun1⟩ :=
        NumFastStarts.expRun_start (calls := calls) (env := e'.env) (s := e')
          hpc' hp2 hn2 (by rw [hmemE]; exact hread) hi11 ⟨_, hes⟩ hcarry' hd hdigB
          (by omega) hnlt
      have hc2 : ExpRunCells idig5 ip5 fr5 fd5 e'' :=
        hcellsT idig5 ip5 fr5 fd5 (by rw [NumFastTaken.stateAt_env_self e']; exact hcE)
      obtain ⟨e3, j3, hj3, hpc3, ⟨hword3, hcells3, hstop3⟩, hrun3'⟩ :=
        (expRunEndBoundLoopStop calls e'.mem a n (i10 + 1) bs 4 (by omega)
            idig5 ip5 fr5 fd5).run_from (n - (i10 + 1)) e'' 0 ⟨hinv, hc2⟩
      obtain ⟨esign, hes'⟩ := hword3.2.2.1
      refine ⟨i10 + 1, esign, e3, (3 + 5 + 1) + j3, ?_, hpc3, hword3, hcells3,
        hstop3, hes', Or.inl rfl, ?_⟩
      · have hb := hj3
        simp only [expRunEndBoundLoopStop] at hb
        omega
      · intro k
        rw [show 3 + 5 + 1 + j3 + k = 3 + (5 + (1 + (j3 + k))) from by omega,
          hrun3 (5 + (1 + (j3 + k))), hrun5 (1 + (j3 + k)),
          ← NumFastTaken.stateAt_env_self e', hrun1 (j3 + k)]
        exact hrun3' k
  · -- the marker is `'E'`: the pivot takes `LeafBlock`
    let env1 : Env := NumFastScanRun.leafBlockEnv
      (NumFastScanRun.nodeBlockEnv (NumFastScanRun.t147Env e.env a i10 0x45) 0x45) 0x45
    have hrun3 : ∀ k, runFuel calls (3 + k) numFastBody (stateAt e.env e) =
        runFuel calls k numFastBody
          (stateAt env1 { e with pc := "if.then157", pre := some "LeafBlock" }) :=
      NumFastScanRun.nestTo157_E (calls := calls) hpc hp hi (by omega) hmarker
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
    have hc1 : ExpRunCells idig5 ip5 fr5 fd5
        (stateAt env1 { e with pc := "if.then157", pre := some "LeafBlock" }) := by
      obtain ⟨h1, h2, h3, h4⟩ := hc0
      refine ⟨?_, ?_, ?_, ?_⟩
      all_goals
        simp only [stateAt_env_get, env1, NumFastScanRun.leafBlockEnv,
          NumFastScanRun.nodeBlockEnv, NumFastScanRun.t147Env]
        block_lk
    by_cases hsign : b2 = 0x2b ∨ b2 = 0x2d
    · obtain ⟨e', hpc', hmem', hp2, hn2, hi11, hes, hcell', hrun6⟩ :=
        NumFastScanRun.nestFrom157_sign (calls := calls) (env := env1)
          (s := { e with pc := "if.then157", pre := some "LeafBlock" })
          rfl hp1 hi1 hn1 hnlt (by omega) hread2 hsign
      have hmemE : e'.mem = e.mem := hmem'
      have hcE : ExpRunCells idig5 ip5 fr5 fd5 e' :=
        hcell' idig5 ip5 fr5 fd5 hc1
      have hcarry' : expRunCarried e'.env := by
        obtain ⟨h1, h2, h3, h4⟩ := hcE
        exact ⟨idig5, ip5, fr5, fd5, h1, h2, h3, h4⟩
      have hjlt : i10 + 2 < n := by omega
      have hd : readByte e'.mem (a + (i10 + 2)) = some (bs.getD (i10 + 2) 0) := by
        rw [hmemE]
        exact readByte_of_readBytes hread hjlt
      have hdigB : IsDigitB (bs.getD (i10 + 2) 0) = true :=
        hdigits (i10 + 2) (by omega) hjlt
      obtain ⟨e'', hinv, hcellsT, _hcarriedT, hrun1⟩ :=
        NumFastStarts.expRun_start (calls := calls) (env := e'.env) (s := e')
          hpc' hp2 hn2 (by rw [hmemE]; exact hread) hi11 ⟨_, hes⟩ hcarry' hd hdigB
          (by omega) hnlt
      have hc2 : ExpRunCells idig5 ip5 fr5 fd5 e'' :=
        hcellsT idig5 ip5 fr5 fd5 (by rw [NumFastTaken.stateAt_env_self e']; exact hcE)
      obtain ⟨e3, j3, hj3, hpc3, ⟨hword3, hcells3, hstop3⟩, hrun3'⟩ :=
        (expRunEndBoundLoopStop calls e'.mem a n (i10 + 2) bs 4 (by omega)
            idig5 ip5 fr5 fd5).run_from (n - (i10 + 2)) e'' 0 ⟨hinv, hc2⟩
      obtain ⟨esign, hes'⟩ := hword3.2.2.1
      refine ⟨i10 + 2, esign, e3, (3 + 6 + 1) + j3, ?_, hpc3, hword3, hcells3,
        hstop3, hes', Or.inr rfl, ?_⟩
      · have hb := hj3
        simp only [expRunEndBoundLoopStop] at hb
        omega
      · intro k
        rw [show 3 + 6 + 1 + j3 + k = 3 + (6 + (1 + (j3 + k))) from by omega,
          hrun3 (6 + (1 + (j3 + k))), hrun6 (1 + (j3 + k)),
          ← NumFastTaken.stateAt_env_self e', hrun1 (j3 + k)]
        exact hrun3' k
    · have hnosign : b2 ≠ 0x2b ∧ b2 ≠ 0x2d :=
        ⟨fun h => hsign (Or.inl h), fun h => hsign (Or.inr h)⟩
      obtain ⟨e', hpc', hmem', hp2, hn2, hi11, hes, hcell', hrun5⟩ :=
        NumFastScanRun.nestFrom157_nosign (calls := calls) (env := env1)
          (s := { e with pc := "if.then157", pre := some "LeafBlock" })
          rfl hp1 hi1 hn1 hnlt (by omega) hread2 hnosign
      have hmemE : e'.mem = e.mem := hmem'
      have hcE : ExpRunCells idig5 ip5 fr5 fd5 e' :=
        hcell' idig5 ip5 fr5 fd5 hc1
      have hcarry' : expRunCarried e'.env := by
        obtain ⟨h1, h2, h3, h4⟩ := hcE
        exact ⟨idig5, ip5, fr5, fd5, h1, h2, h3, h4⟩
      have hjlt : i10 + 1 < n := by omega
      have hd : readByte e'.mem (a + (i10 + 1)) = some (bs.getD (i10 + 1) 0) := by
        rw [hmemE]
        exact readByte_of_readBytes hread hjlt
      have hdigB : IsDigitB (bs.getD (i10 + 1) 0) = true :=
        hdigits (i10 + 1) (by omega) hjlt
      obtain ⟨e'', hinv, hcellsT, _hcarriedT, hrun1⟩ :=
        NumFastStarts.expRun_start (calls := calls) (env := e'.env) (s := e')
          hpc' hp2 hn2 (by rw [hmemE]; exact hread) hi11 ⟨_, hes⟩ hcarry' hd hdigB
          (by omega) hnlt
      have hc2 : ExpRunCells idig5 ip5 fr5 fd5 e'' :=
        hcellsT idig5 ip5 fr5 fd5 (by rw [NumFastTaken.stateAt_env_self e']; exact hcE)
      obtain ⟨e3, j3, hj3, hpc3, ⟨hword3, hcells3, hstop3⟩, hrun3'⟩ :=
        (expRunEndBoundLoopStop calls e'.mem a n (i10 + 1) bs 4 (by omega)
            idig5 ip5 fr5 fd5).run_from (n - (i10 + 1)) e'' 0 ⟨hinv, hc2⟩
      obtain ⟨esign, hes'⟩ := hword3.2.2.1
      refine ⟨i10 + 1, esign, e3, (3 + 5 + 1) + j3, ?_, hpc3, hword3, hcells3,
        hstop3, hes', Or.inl rfl, ?_⟩
      · have hb := hj3
        simp only [expRunEndBoundLoopStop] at hb
        omega
      · intro k
        rw [show 3 + 5 + 1 + j3 + k = 3 + (5 + (1 + (j3 + k))) from by omega,
          hrun3 (5 + (1 + (j3 + k))), hrun5 (1 + (j3 + k)),
          ← NumFastTaken.stateAt_env_self e', hrun1 (j3 + k)]
        exact hrun3' k

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.NumFastGate.expRunEndBoundLoopStop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expRunEndBoundLoopStop

/-- info: 'LeanLLVM.Refinement.NumFastGate.t1_fracEnd230_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms t1_fracEnd230_run

/-- info: 'LeanLLVM.Refinement.NumFastGate.nest_expRun_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nest_expRun_run

end NumFastGate

end LeanLLVM.Refinement
