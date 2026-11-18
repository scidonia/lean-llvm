/-
`num_fast_el1`'s conversion at the pinned body: the tail from the merge block to
the return, and the boundary the scan's seams still leave.

`JsonStage2NumFastTier1` composes tier 1's five-block chain from `if.end230`,
entered from the exponent merge, to the store at `%out` (`t1_store_run`), and
`JsonStage2NumFastArm` states the arm that chain is part of.  This module adds
the body's last step — `cleanup300`'s return at the edge every accepting arm
takes — the chain entered from the integer run's own exit (`t1_end230_run`), and
the arm's own conclusion at the merge: six control steps to the returned word,
`1` in the answer's value slot, `strtodSpec`'s eight bytes at `out`, and every
byte outside the two slots the caller's.

**The chain from the run's exit.**  `t1_end230_run` is tier 1's arithmetic as
one `runFuel` identity: the integer run's end-of-lexeme exit word
(`JsonStage2NumFastDigitRuns.intRunEndWord`, which now carries the run's memory)
supplies the merge's predecessor, the accumulator and the digit count; the
gate's step, the mantissa block's four and the returning edge are the five
remaining steps.  The registers are read as the model's — `ip_word_digitsNat`
for the folded integer part, `intDigits d` for the count, the lexeme's zeros for
the fraction and the exponent — so the conclusion is `strtodSpec`'s bytes and not
the body's expression.  What the exit word does not carry is the three cells no
block on the path writes (`%out`, `%tobool274.not`, the two table symbols): they
are the caller's environment, and `JsonStage2NumFastCells`'
`NumFastChain` is the transport that reads them at a later state, one the scan's
run has to be read as a chain of steps to use.


**The returning edge is shared by all three accepting arms.**  Tier 1's store
block `cleanup282.thread`, the kernel's `cleanup282` and the fallback's
`if.end291` all reach `cleanup300` with `1` in their incoming; the block's `phi`
selects it from the edge the state's predecessor names, so
`numFast_step_cleanup300_one` is the tail of every arm, and the tier-1 statement
below differs from the kernel's and the fallback's only in the word their own
store blocks write.

**The boundary the scan leaves.**  The merge block's `phi`s read cells from
blocks before the run they end: the integer part's end-of-lexeme edge reads `%7`
— the count `land.lhs.true41.preheader` formed — and `%ip.4`, and the fraction's
end-of-lexeme edge reads `%idig.4`, `%ip.5`, `%fr.4` and `%17`.  The run-exit
predicates hand those cells on: `intRunEndWord` carries the predecessor
`if.end62`, the length as the index, `%7` in the preheader's raw form, `%p` and
`%n`, and `fracRunEndWord` carries `if.end140`, `%17`, `%idig.4`/`%ip.5` and
`%fr.4`, so the block denotes at either non-exponent edge from the exit alone.
`numFast_merge_end62_needs_seven` and `numFast_merge_end140_needs_idig` remain
the mechanical record of why each cell is needed: at those edges a state whose
earlier cell is unbound does not denote at all.  What the composition takes
beyond the predicate is the scan's own trace to the exit, and that is
`JsonStage2NumFastScanRun.intScan_end230` and
`JsonStage2NumFastSeams.intScan_merge` for a lexeme whose integer part runs to
the lexeme's end; the fraction and exponent routes are threaded one seam at a
time.

**Tier 2 and tier 3.**  The same returning edge closes them once their store
blocks' words are proved: the kernel's answer at `cleanup282` is
`JsonStage2NumFastCalls`' model with its bound
(`JsonStage2NumFastTier3.numFast_ifEnd268_domain`, `w < 2 ^ 64` met at the
body's own word), and the fallback's region from `for.body.i.i566.i.i.epil` is
`JsonStage2NumFastTier3`'s.  Neither is this module's; what they share with the
tier-1 statement below is `numFast_step_cleanup300_one`.
-/
import LeanLLVM.Refinement.JsonStage2NumFastArm
import LeanLLVM.Refinement.JsonStage2NumFastTier1
import LeanLLVM.Refinement.JsonStage2NumFastScanFast

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.JSON
open ByteString
open LeanLLVM.StrtodRefine
open LeanLLVM.StrtodTier1

/-! ### `cleanup300`'s returning edge

The block's thirteen-member `phi` carries the arm's return word, and the two
accepting store blocks' edge is the one whose incoming is the literal `1`.  The
refusing arm's edge (`if.then5`) is `JsonStage2NumFastBody`'s
`numFast_step_cleanup300`; this is the accepting one. -/

/-- `cleanup300`'s environment at the accepting edge: the `phi` binds the return
word to the `1` its `cleanup282.thread` incoming carries. -/
theorem numFast_cleanup300_denote_one {calls : Calls} {env : Env} {s : State}
    (hpre : s.pre = some "cleanup282.thread") :
    denoteCode calls numFastCleanup300Instrs (stateAt env s) =
      some (stateAt (("%retval.8", .int 32 1) :: env) s) := by
  unfold numFastCleanup300Instrs
  block_eval

/-- **The conversion's return.**  At `cleanup300` entered from an accepting
arm's store block, the body returns `1` and leaves the memory the store wrote. -/
theorem numFast_step_cleanup300_one {calls : Calls} {env : Env} {s : State}
    (hpc : s.pc = "cleanup300") (hpre : s.pre = some "cleanup282.thread") :
    step calls numFastBody (stateAt env s) =
      .ret (some (.int 32 1)) (stateAt (("%retval.8", .int 32 1) :: env) s) := by
  refine numFast_step_at
    (s' := stateAt (("%retval.8", .int 32 1) :: env) s)
    (b := ⟨"cleanup300", numFastCleanup300Instrs,
      Term.ret (Ty.int 32) (some (Operand.reg "%retval.8"))⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_cleanup300
  · simpa only [denoteCode_nil] using
      numFast_cleanup300_denote_one (calls := calls) (env := env) (s := s) hpre
  · simp only [execTerm, evalOperand, stateAt, lookupName_cons_self]

/-! ### The tier-1 conversion's run, at the arm's conclusion

`t1_store_run` is the chain from the merge block to the store, and the returning
edge finishes it.  The hypotheses are the merge's own staging: the five counters
the model's, the sign's cell, the two tables and the tier-1 window. -/

/-- **The tier-1 conversion's run.**  At the merge block entered from the
exponent merge, with the five counters the model's, the sign's cell, the two
tables staged and the lexeme inside tier 1's window, six control steps return
`1` with `strtodSpec`'s eight bytes at `%out`, and every byte outside the two
slots reads as it did. -/
theorem t1_arm_run {calls : Calls} {env : Env} {s : State} {d : Decimal}
    {fs : Bytes} {sign : BitVec 1} {out err : Nat} {p10 pd : Nat}
    {ten : BitVec 64} {c : Code}
    (hpc : s.pc = "if.end230") (hpre : s.pre = some "if.end226")
    (hE : lookupName env "%exp10.4" = some (.int 64 (BitVec.ofInt 64 (expVal d))))
    (hI : lookupName env "%idig.4"
      = some (.int 64 (BitVec.ofNat 64 (intDigits d))))
    (hip : lookupName env "%ip.5"
      = some (.int 64 (BitVec.ofNat 64 (Decimal.digitsNat d.ip))))
    (hfr : lookupName env "%fr.5"
      = some (.int 64 (BitVec.ofNat 64 (Decimal.digitsNat fs))))
    (hfd : lookupName env "%fdig.4"
      = some (.int 64 (BitVec.ofNat 64 (fracDigits d))))
    (hfs : d.fr = some fs)
    (hsig : lookupName env "%tobool274.not" = some (.int 1 sign))
    (hout : lookupName env "%out" = some (.ptr out))
    (hp10 : lookupName env "@NUMF_EL1_P10" = some (.ptr p10))
    (hpwt : lookupName env "@NUMF_EL1_POW10" = some (.ptr pd))
    (hten : ten = BitVec.ofNat 64 (10 ^ fs.length))
    (hrow10 : readBytes s.mem (p10 + fracDigits d * 8) 8
      = some (natToBytes ten.toNat 8))
    (hrowP : ∀ j, j ≤ 22 → readBytes s.mem (pd + j * 8) 8
      = some (natToBytes (uitofpBits (10 ^ j)).toNat 8))
    (hwf : d.wellFormed) (h1 : Tier1 d)
    (hsign : (sign = 1) ↔ d.neg = false)
    (hrc : roundMag (opP d) (opD d) = .fin c) (hcM : c.IsMag) :
    runFuel calls 6 numFastBody (stateAt env s) =
      some (.ret (some (.int 32 1))
        (writeBytes s.mem out (wordBytes 8 (strtodSpec d).toBits))) ∧
    UnchangedOutside s.mem
      (writeBytes s.mem out (wordBytes 8 (strtodSpec d).toBits))
      [(out, 8), (err, 8)] := by
  obtain ⟨e, hepc, hepre, hemem, hrun⟩ :=
    NumFastTier1.t1_store_run (calls := calls) (env := env) (s := s) (d := d)
      (fs := fs) (sign := sign) (out := out) (p10 := p10) (pd := pd) (ten := ten)
      (c := c)
      hpc hpre hE hI hip hfr hfd hfs hsig hout hp10 hpwt hten hrow10 hrowP
      hwf h1 hsign hrc hcM
  have hstep : step calls numFastBody e =
      .ret (some (.int 32 1)) (stateAt (("%retval.8", .int 32 1) :: e.env) e) :=
    numFast_step_cleanup300_one (calls := calls) (env := e.env) (s := e) hepc hepre
  refine ⟨?_, ?_⟩
  · rw [show (6 : Nat) = 5 + 1 from rfl, hrun 1]
    simp only [runFuel, hstep, stateAt]
    rw [hemem]
  · exact (UnchangedOutside.refl' s.mem [(out, 8), (err, 8)]).write_le
      (a := out) (w := 8) (bs := wordBytes 8 (strtodSpec d).toBits)
      ⟨(out, 8), by simp, le_rfl, by omega⟩
      (by simp only [wordBytes, natToBytes_length, le_refl])

/-- **The arm's conclusion at the merge block.**  The same run in the arm's own
`∃`-form: an answer whose value is `1`, whose memory is `strtodSpec`'s eight
bytes at `out`, whose cursor is the caller's, and whose frame is the two slots. -/
theorem numFastArm_tier1_at_merge {calls : Calls} {env : Env} {s : State}
    {d : Decimal} {fs : Bytes} {sign : BitVec 1} {out err : Nat} {p10 pd : Nat}
    {ten : BitVec 64} {c : Code}
    (hpc : s.pc = "if.end230") (hpre : s.pre = some "if.end226")
    (hE : lookupName env "%exp10.4" = some (.int 64 (BitVec.ofInt 64 (expVal d))))
    (hI : lookupName env "%idig.4"
      = some (.int 64 (BitVec.ofNat 64 (intDigits d))))
    (hip : lookupName env "%ip.5"
      = some (.int 64 (BitVec.ofNat 64 (Decimal.digitsNat d.ip))))
    (hfr : lookupName env "%fr.5"
      = some (.int 64 (BitVec.ofNat 64 (Decimal.digitsNat fs))))
    (hfd : lookupName env "%fdig.4"
      = some (.int 64 (BitVec.ofNat 64 (fracDigits d))))
    (hfs : d.fr = some fs)
    (hsig : lookupName env "%tobool274.not" = some (.int 1 sign))
    (hout : lookupName env "%out" = some (.ptr out))
    (hp10 : lookupName env "@NUMF_EL1_P10" = some (.ptr p10))
    (hpwt : lookupName env "@NUMF_EL1_POW10" = some (.ptr pd))
    (hten : ten = BitVec.ofNat 64 (10 ^ fs.length))
    (hrow10 : readBytes s.mem (p10 + fracDigits d * 8) 8
      = some (natToBytes ten.toNat 8))
    (hrowP : ∀ j, j ≤ 22 → readBytes s.mem (pd + j * 8) 8
      = some (natToBytes (uitofpBits (10 ^ j)).toNat 8))
    (hwf : d.wellFormed) (h1 : Tier1 d)
    (hsign : (sign = 1) ↔ d.neg = false)
    (hrc : roundMag (opP d) (opD d) = .fin c) (hcM : c.IsMag) :
    ∃ (k : Nat) (o : CallOutcome),
      runFuel calls k numFastBody (stateAt env s) = some (.ret (some o.ret) o.mem) ∧
      o.ret = .int 32 1 ∧
      o.mem = writeBytes s.mem out (wordBytes 8 (strtodSpec d).toBits) ∧
      o.next = s.next ∧
      UnchangedOutside s.mem o.mem [(out, 8), (err, 8)] := by
  obtain ⟨hrun, hframe⟩ :=
    t1_arm_run hpc hpre hE hI hip hfr hfd hfs hsig hout hp10 hpwt hten hrow10 hrowP
      hwf h1 hsign hrc hcM
  refine ⟨6, ⟨.int 32 1,
    writeBytes s.mem out (wordBytes 8 (strtodSpec d).toBits), s.next⟩,
    hrun, rfl, rfl, rfl, hframe⟩

/-! ### The tier-1 conversion from the run's own exit

`t1_arm_run` enters at the merge block with the five counters as hypotheses; the
scan's exit word is what supplies them.  This theorem is that seam: from the
integer run's end-of-lexeme exit (`intRunEndWord`), the gate's step, the
mantissa block's four steps and the returning edge are one `runFuel` chain of six
control steps, and the registers the gate reads are the model's — the folded
integer part, its digit count, and the fraction's and exponent's zeros.

**What the exit word supplies, and what it does not.**  `intRunEndWord` carries
the cursor, the length, the count, the accumulator, `%7`, the predecessor and
the run's memory, which is what the gate and the store need.  The three cells the
store *reads* but no block on the path writes — `%out`, `%tobool274.not` and the
two table symbols — are not in it: they are the caller's environment, and the
scan's `runFuel` prefix does not expose the environment it leaves.  They are
therefore hypotheses of this seam, and closing them at the entry state is the
transport `JsonStage2NumFastCells`' `NumFastChain` states for a chain of steps
(one the scan's run must be read as, since a `runFuel` prefix alone does not name
the blocks it crossed).  `JsonStage2NumFastCarried.t1_chain_run` spends it: the
same six steps from a state a caller stages, with the kept cells read through
the chain and the sign through its `if.end`-free filter. -/

/-- **The tier-1 conversion from the run's exit.**  At the integer run's
end-of-lexeme exit, with the fraction absent and the exponent absent, the
gate's step and the conversion's five reach `cleanup300` and the return: one
chain of six control steps writes `strtodSpec`'s eight bytes at `%out` and leaves
every byte outside the two slots as it was. -/
theorem t1_end230_run {calls : Calls} {s : State} {bs : List UInt8} {d : Decimal}
    {sign : BitVec 1} {out p10 pd err : Nat} {ten : BitVec 64} {c : Code}
    {a n i0 d0 : Nat}
    (he : intRunEndWord s.mem bs a n i0 d0 s)
    (hi0 : i0 ≤ n) (hbn : d0 + n < 2 ^ 64)
    (hshape : d.ip.data.toList = (bs.drop (i0 - d0)).take (d0 + (n - i0)))
    (hint : intDigits d = d0 + (n - i0))
    (hfr0 : d.fr = none) (hex0 : d.ex = none)
    (hsig : lookupName s.env "%tobool274.not" = some (.int 1 sign))
    (hout : lookupName s.env "%out" = some (.ptr out))
    (hp10 : lookupName s.env "@NUMF_EL1_P10" = some (.ptr p10))
    (hpwt : lookupName s.env "@NUMF_EL1_POW10" = some (.ptr pd))
    (hten : ten = BitVec.ofNat 64 (10 ^ (d.fr.getD empty).length))
    (hrow10 : readBytes s.mem (p10 + fracDigits d * 8) 8
      = some (natToBytes ten.toNat 8))
    (hrowP : ∀ j, j ≤ 22 → readBytes s.mem (pd + j * 8) 8
      = some (natToBytes (uitofpBits (10 ^ j)).toNat 8))
    (hwf : d.wellFormed) (h1 : Tier1 d)
    (hsign : (sign = 1) ↔ d.neg = false)
    (hrc : roundMag (opP d) (opD d) = .fin c) (hcM : c.IsMag) :
    ∃ (k : Nat) (o : CallOutcome),
      runFuel calls k numFastBody (stateAt s.env s) = some (.ret (some o.ret) o.mem) ∧
      o.ret = .int 32 1 ∧
      o.mem = writeBytes s.mem out (wordBytes 8 (strtodSpec d).toBits) ∧
      UnchangedOutside s.mem o.mem [(out, 8), (err, 8)] := by
  obtain ⟨hpc, hpre, hn64, hmem, hp, hn, hinc64, hinc63, hip4, h7⟩ := he
  have hfd0 : fracDigits d = 0 := by rw [fracDigits, hfr0]; rfl
  have hnd : digitCount d ≤ 19 := by have := h1.1; omega
  have hnd_eq : digitCount d = d0 + (n - i0) := by
    rw [digitCount, fracDigits, hfr0]
    simp only [Option.getD_none, ByteString.length_empty, Nat.add_zero]
    exact hint
  have hlen : d0 + (n - i0) ≤ 19 := by omega
  have hdig : d0 + (n - i0) < 20 := by omega
  -- the accumulator is the model's integer part
  have hipv : BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + (n - i0)) 19))
      = BitVec.ofNat 64 (Decimal.digitsNat d.ip) :=
    NumFastScanRun.ip_word_digitsNat hshape hlen rfl
  have h7' : lookupName s.env "%7"
      = some (.int 64 (BitVec.ofNat 64 (d0 + (n - i0)))) := by
    rw [h7, NumFastSeams.seven_tie hi0 hbn]
  have hzero : (0 : BitVec 64) + BitVec.ofNat 64 (d0 + (n - i0))
      = BitVec.ofNat 64 (d0 + (n - i0)) := by bv_omega
  have hbit1 : evalICmp .ult (0 + BitVec.ofNat 64 (d0 + (n - i0))) (20#64) = 1 := by
    rw [NumFastStarts.ult_iff_one, hzero, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), show (20#64).toNat = 20 from by decide]
    exact hdig
  have hbit2 : evalICmp .ult ((0 - 0) + (45#64)) (91#64) = 1 := by decide
  have hgate : step calls numFastBody (stateAt s.env s) =
      .jump (stateAt (NumFastTier1.t1GateEnv s.env 0
          (BitVec.ofNat 64 (d0 + (n - i0)))
          (BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + (n - i0)) 19)))
          0 0)
        { s with pc := "if.then241", pre := some "if.end230" }) :=
    NumFastScanRun.ifEnd230_step_end62 hpc hpre h7' hip4 ⟨hbit1, hbit2⟩
  -- the mantissa block's five
  have hE' : (0 : BitVec 64) = BitVec.ofInt 64 (expVal d) := by
    rw [show expVal d = 0 from by simp only [expVal, hex0]]
    rfl
  have hI' : BitVec.ofNat 64 (d0 + (n - i0)) = BitVec.ofNat 64 (intDigits d) := by
    rw [hint]
  have hfr' : (0 : BitVec 64) = BitVec.ofNat 64 (Decimal.digitsNat (d.fr.getD empty)) := by
    rw [hfr0]; rfl
  have hfd' : (0 : BitVec 64) = BitVec.ofNat 64 (fracDigits d) := by rw [hfd0]; rfl
  have hrow10' : readBytes s.mem (p10 + fracDigits d * 8) 8
      = some (natToBytes ten.toNat 8) := hrow10
  obtain ⟨e, hepc, hepre, hemem, hrun⟩ :=
    NumFastTier1.t1_then241_store_run (calls := calls) (env := s.env)
      (s := { s with pc := "if.then241", pre := some "if.end230" })
      (d := d) (sign := sign) (out := out) (p10 := p10) (pd := pd)
      (ten := ten) (c := c)
      (exp10 := 0) (idig := BitVec.ofNat 64 (d0 + (n - i0)))
      (ip := BitVec.ofNat 64 (digitFold bs (i0 - d0) (min (d0 + (n - i0)) 19)))
      (fr := 0) (fdig := 0)
      rfl rfl hE' hI' hipv hfr' hfd' hsig hout hp10 hpwt hten hrow10' hrowP hwf h1 hsign hrc hcM
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

/-! ### The merge block's non-exponent edges read earlier cells

Two controls on the seam.  The block's `phi`s at `if.end62` and `if.end140`
select cells the digit runs' registers name, and a state whose cell is unbound
does not denote: the selection fails and the block's chain is `none`, which
`step` reads as `ub`.  The exit predicates carry those cells
(`intRunEndWord`, `fracRunEndWord`), which is what lets
`JsonStage2NumFastSeams.intRunExit_gate` read them off the exit; the controls
below keep each cell's necessity on the record at the block. -/

/-- A leading `phi` run whose *second* selection is empty is `none`, whatever
the first selection was: the run's first phi installs its binding and the second
blocks it. -/
theorem denoteRun_phi_two_none {calls : Calls} {pend : List (String × Value)}
    {d1 : String} {ty1 : Ty} {inc1 : List (String × Operand)}
    {d2 : String} {ty2 : Ty} {inc2 : List (String × Operand)}
    {is : List Instr} {s : State} (h : phiSelect s inc2 = none) :
    denoteRun calls pend
      (Instr.phi d1 ty1 inc1 :: Instr.phi d2 ty2 inc2 :: is) s = none := by
  simp only [denoteRun]
  cases h1 : phiSelect s inc1 with
  | none => rfl
  | some v =>
      exact denoteRun_phi_none (calls := calls) (pend := pend ++ [(d1, v)])
        (d := d2) (ty := ty2) (inc := inc2) (is := is) (s := s) h

/-- The `%idig` phi's incoming at `if.end62`, as the block's pin writes it. -/
theorem numFast_merge_idig_incoming_end62 :
    phiIncoming "if.end62"
      [("if.end226", (Operand.reg "%idig.4")),
       ("if.end140", (Operand.reg "%idig.4")),
       ("if.end62", (Operand.reg "%7"))]
      = some (Operand.reg "%7") := rfl

/-- The `%idig` phi's incoming at `if.end140`, as the block's pin writes it. -/
theorem numFast_merge_idig_incoming_end140 :
    phiIncoming "if.end140"
      [("if.end226", (Operand.reg "%idig.4")),
       ("if.end140", (Operand.reg "%idig.4")),
       ("if.end62", (Operand.reg "%7"))]
      = some (Operand.reg "%idig.4") := rfl

/-- The integer part's end-of-lexeme edge reads `%7`: with the cell unbound the
merge block's `phi` run does not denote. -/
theorem numFast_merge_end62_needs_seven (calls : Calls) {env : Env} {s : State}
    (hpre : s.pre = some "if.end62") (h7 : lookupName env "%7" = none) :
    denoteCode calls numFastIfEnd230Instrs (stateAt env s) = none := by
  have hpre' : (stateAt env s).pre = some "if.end62" := hpre
  have hlook : lookupName (stateAt env s).env "%7" = none := h7
  have hsel : phiSelect (stateAt env s)
      [("if.end226", (Operand.reg "%idig.4")),
       ("if.end140", (Operand.reg "%idig.4")),
       ("if.end62", (Operand.reg "%7"))] = none := by
    simp only [phiSelect, hpre', numFast_merge_idig_incoming_end62, evalOperand,
      hlook]
  change denoteRun calls [] numFastIfEnd230Instrs (stateAt env s) = none
  simp only [numFastIfEnd230Instrs]
  exact denoteRun_phi_two_none hsel

/-- The fraction's end-of-lexeme edge reads `%idig.4`: with the cell unbound the
merge block's `phi` run does not denote. -/
theorem numFast_merge_end140_needs_idig (calls : Calls) {env : Env} {s : State}
    (hpre : s.pre = some "if.end140") (hi : lookupName env "%idig.4" = none) :
    denoteCode calls numFastIfEnd230Instrs (stateAt env s) = none := by
  have hpre' : (stateAt env s).pre = some "if.end140" := hpre
  have hlook : lookupName (stateAt env s).env "%idig.4" = none := hi
  have hsel : phiSelect (stateAt env s)
      [("if.end226", (Operand.reg "%idig.4")),
       ("if.end140", (Operand.reg "%idig.4")),
       ("if.end62", (Operand.reg "%7"))] = none := by
    simp only [phiSelect, hpre', numFast_merge_idig_incoming_end140, evalOperand,
      hlook]
  change denoteRun calls [] numFastIfEnd230Instrs (stateAt env s) = none
  simp only [numFastIfEnd230Instrs]
  exact denoteRun_phi_two_none hsel

/-! ### Axiom footprints

The tail's declarations, pinned with `#guard_msgs` so the build checks the
footprint rather than printing it.  None carries `sorryAx`; the tier-1 chain's
exact-value declarations carry `Classical.choice` through the adapter's `Rat`
construction, as `StrtodTier1` records. -/

/-- info: 'LeanLLVM.Refinement.numFast_step_cleanup300_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numFast_step_cleanup300_one

/-- info: 'LeanLLVM.Refinement.t1_arm_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms t1_arm_run

/-- info: 'LeanLLVM.Refinement.numFastArm_tier1_at_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms numFastArm_tier1_at_merge

/-- info: 'LeanLLVM.Refinement.t1_end230_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms t1_end230_run

/-- info: 'LeanLLVM.Refinement.numFast_merge_end62_needs_seven' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numFast_merge_end62_needs_seven

/-- info: 'LeanLLVM.Refinement.numFast_merge_end140_needs_idig' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numFast_merge_end140_needs_idig

end LeanLLVM.Refinement
