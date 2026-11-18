/-
`num_fast_el1`'s conversion from a supplied chain: the tier-1 arm at the cells a
caller stages, with the scan's exit reached by a chain rather than assumed.

`JsonStage2NumFastRun.t1_end230_run` takes the four cells no block on the path
writes — `%out`, `@NUMF_EL1_P10`, `@NUMF_EL1_POW10` and the sign
`%tobool274.not` — as hypotheses at the run's exit, because a `runFuel` prefix
does not expose the environments it crosses.  `JsonStage2NumFastCells` is the
transport that closes them: a `NumFastChain` of the body's jumps, whose kept
cells no block writes and whose sign survives every block but `if.end`.  This
module spends that transport at the two ends it is needed at.

**The dispatch's sign, produced.**  `sign_at_ifEnd6` is the one segment the sign
needs to be *established* rather than carried: from `entry` at a non-empty
lexeme, `entry`'s test, `land.lhs.true`'s sign check and `if.end`'s two `phi`s
are three control steps, and the state they leave at `if.end6` holds
`%tobool274.not = 1` exactly at a lexeme whose first byte is not `-`.  It is a
`NumFastChain`, so its conclusion is the kept cells at `if.end6` and its fuel,
as well as the sign's word; the sign is `if.end`'s value, not a cell the caller
staged.

**The conversion from a supplied chain.**  `t1_chain_run` is the tier-1 arm's
conclusion at a state the caller stages: given a `NumFastChain` from that state
to the integer run's end-of-lexeme exit word — the chain a dispatch composition
supplies — the cells at its start are the cells at the exit, and the gate, the
mantissa block, the scale's arm, the store and the return are one `runFuel` run
from the caller's state.  The three kept cells are read at the caller's
environment by `NumFastChain.kept`; the sign by `NumFastChain.sign`, on the
chain whose blocks avoid `if.end`.

**The fraction edge's integer cells.**  `fracRunEndWord_tie_cells` is the same
spending on the other stopper: the integer part's two cells, which
`fracRunEndWord` binds by name only (`fracPartCells`), are named at the state
`if.end68` formed them and carried to the fraction run's exit by the run's own
arms (`JsonStage2NumFastDigitRuns.fracRunEndBoundLoopCells`), so the merge's five
registers are the model's from the run's start rather than from two lookups at
the exit.

**What is not here.**  No chain across the digit run is produced by this tree.
The runs are stated as `runFuel` prefixes (`intScan_run`, `intScan_end230`), and
the step-level facts the loop's arms are proved from are local to those proofs;
`BoundLoop`'s induction consumes `runFuel` arms, so a chain across the loop is a
statement its arms do not carry — the cells are, instead, an arm conclusion on
both digit routes.  `t1_chain_run` is therefore the arm at the supplied
environment *and* the supplied chain, and `t1_chain_run_of_entry` is the
composition from `entry`: the dispatch's three steps are produced, the
conversion's six follow, and the digit run's chain is the one input the
composition takes that the tree does not supply.

There is no `sorry`, `admit` or `native_decide` below.
-/
import LeanLLVM.Refinement.JsonStage2NumFastCells
import LeanLLVM.Refinement.JsonStage2NumFastEntry
import LeanLLVM.Refinement.JsonStage2NumFastSign
import LeanLLVM.Refinement.JsonStage2NumFastStarts
import LeanLLVM.Refinement.JsonStage2NumFastScanRun
import LeanLLVM.Refinement.JsonStage2NumFastRun

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

/-! ### The dispatch's sign

`entry` tests the length, `land.lhs.true` reads the lexeme's first byte and
forms `%cmp1 = (%0 != '-')`, and `if.end`'s `phi` takes that bit as
`%tobool274.not`.  The three steps are the first segment of a chain, and the
state they leave carries the sign's word and the caller's kept cells. -/

/-- The state the dispatch leaves: `if.end6`, entered from `entry`'s test, with
`land.lhs.true`'s sign check and `if.end`'s two `phi`s run.  Named so a chain
that continues past the dispatch can start at it. -/
def numFastDispatchState (env : Env) (s : State) (b : UInt8) (n : Nat) : State :=
  stateAt (NumFastStarts.ifEndEnv (NumFastStarts.signEnv (numFastEntryEnv env s.next
      (evalICmp .eq (BitVec.ofNat 64 n) 0x0000000000000000#64)) b) b n)
    { s with next := s.next + 768 + 1568 + 4 + 4 + 8,
             pc := "if.end6", pre := some "if.end" }

/-- **The sign's three steps.**  From `entry` at a non-empty lexeme, the
dispatch's test, the sign check and `if.end`'s `phi` run reach `if.end6` in
three control steps; the state there holds the sign's word,
`evalICmp .ne (%0) '-'`, and the kept cells are the caller's.

That word is the lexeme's sign by `NumFastSign.sign_tie` as soon as the byte the
sign check read is the lexeme's head, so the `hsign` a conversion reads —
`(sign = 1) ↔ d.neg = false` — is this theorem's with that byte hypothesis. -/
theorem sign_at_ifEnd6 {calls : Calls} {env : Env} {s : State} {a n : Nat}
    {b : UInt8}
    (hpc : s.pc = "entry")
    (hp : lookupName env "%p" = some (.ptr a))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hnpos : 0 < n) (hltn : NumFastStarts.negIndex b < n) (hnlt : n < 2 ^ 64)
    (hread : readByte s.mem a = some b) :
    NumFastChain calls (fun _ => True) (stateAt env s)
        (numFastDispatchState env s b n) ∧
      NumFastSign (numFastSignWord b) (numFastDispatchState env s b n) ∧
      NumFastKept env (numFastDispatchState env s b n) ∧
      (numFastDispatchState env s b n).mem = s.mem ∧
      ∀ k, LeanLLVM.runFuel calls (3 + k) numFastBody (stateAt env s)
        = LeanLLVM.runFuel calls k numFastBody (numFastDispatchState env s b n) := by
  have hne : BitVec.ofNat 64 n ≠ 0x0000000000000000#64 := by
    intro h
    have h2 := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnlt] at h2
    simp at h2
    omega
  have hbit : evalICmp .eq (BitVec.ofNat 64 n) 0x0000000000000000#64 = 0 :=
    NumFastStarts.eq_zero_iff _ _ |>.mpr hne
  let s1 : State := { s with next := s.next + 768 + 1568 + 4 + 4 + 8,
                              pc := "land.lhs.true", pre := some "entry" }
  let env1 : Env := numFastEntryEnv env s.next
    (evalICmp .eq (BitVec.ofNat 64 n) 0x0000000000000000#64)
  have h1 : LeanLLVM.step calls numFastBody (stateAt env s) =
      .jump (stateAt env1 s1) :=
    NumFastScanRun.entry_step_land (calls := calls) hpc hn hbit
  have hp1 : lookupName env1 "%p" = some (.ptr a) := by
    simp only [env1, numFastEntryEnv]
    block_lk
  have h2 : LeanLLVM.step calls numFastBody (stateAt env1 s1) =
      .jump (stateAt (NumFastStarts.signEnv env1 b)
        { s1 with pc := "if.end", pre := some "land.lhs.true" }) :=
    NumFastStarts.sign_step (calls := calls) rfl hp1 hread
  have hn2 : lookupName (NumFastStarts.signEnv env1 b) "%n"
      = some (.int 64 (BitVec.ofNat 64 n)) := by
    simp only [NumFastStarts.signEnv, env1, numFastEntryEnv]
    block_lk
  have hbit3 : evalICmp .ult (BitVec.ofNat 64 (NumFastStarts.negIndex b))
      (BitVec.ofNat 64 n) = 1 := by
    rw [NumFastStarts.ult_iff_one, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := NumFastStarts.negIndex_le_one b; omega),
      Nat.mod_eq_of_lt hnlt]
    exact hltn
  have h3 : LeanLLVM.step calls numFastBody
      (stateAt (NumFastStarts.signEnv env1 b)
        { s1 with pc := "if.end", pre := some "land.lhs.true" }) =
      .jump (numFastDispatchState env s b n) :=
    NumFastStarts.ifEnd_step (calls := calls) rfl rfl
      (NumFastStarts.signEnv_cmp1 env1 b) (NumFastStarts.signEnv_spec env1 b)
      hn2 hbit3
  have hchain : NumFastChain calls (fun _ => True) (stateAt env s)
      (numFastDispatchState env s b n) :=
    .step trivial h1 (.step trivial h2 (.step trivial h3
      (.refl (numFastDispatchState env s b n))))
  refine ⟨hchain, ?_, ?_, rfl, ?_⟩
  · simp only [NumFastSign, numFastSignWord, numFastDispatchState, stateAt,
      NumFastStarts.ifEndEnv, NumFastStarts.ifEndPhiEnv]
    block_lk
  · exact hchain.kept (numFastKept_stateAt env s)
  · intro k
    rw [show 3 + k = 1 + (1 + (1 + k)) from by omega,
      runFuel_jump_prefix h1 (1 + (1 + k)),
      runFuel_jump_prefix h2 (1 + k),
      runFuel_jump_prefix h3 k]

/-! ### The conversion from a supplied chain

The exit word at `e`, the chain from the caller's state to it, and the cells at
the caller's environment: the three kept cells are read at `e` through the
chain, the sign through the chain's `if.end`-free filter, and the six-step
tier-1 run is `t1_end230_run` at those cells. -/

/-- **The tier-1 conversion from the caller's staging.**  Given the integer run's
end-of-lexeme exit word at `e`, a chain from the staged state `s0` to `e` whose
blocks avoid `if.end`, the kept cells at `s0` read against the caller's
environment, the sign at `s0` and the three kept cells at the caller's
environment, the gate, the mantissa block, the scale's arm, the store and the
return are one run from `s0`: it returns `1`, writes `strtodSpec`'s eight bytes
at `%out`, and leaves every byte outside the two slots as it was. -/
theorem t1_chain_run {calls : Calls} {d : Decimal} {s0 e : State} {env0 : Env}
    {sign : BitVec 1} {bs : List UInt8} {out err p10 pd : Nat}
    {ten : BitVec 64} {c : Code} {a n i0 d0 : Nat}
    (hchain : NumFastChain calls (fun pc => pc ≠ "if.end") s0 e)
    (hkeep0 : NumFastKept env0 s0)
    (hsign0 : NumFastSign sign s0)
    (hout0 : lookupName env0 "%out" = some (.ptr out))
    (hp10_0 : lookupName env0 "@NUMF_EL1_P10" = some (.ptr p10))
    (hpwt_0 : lookupName env0 "@NUMF_EL1_POW10" = some (.ptr pd))
    (he : intRunEndWord s0.mem bs a n i0 d0 e)
    (hi0 : i0 ≤ n) (hbn : d0 + n < 2 ^ 64)
    (hshape : d.ip.data.toList = (bs.drop (i0 - d0)).take (d0 + (n - i0)))
    (hint : intDigits d = d0 + (n - i0))
    (hfr0 : d.fr = none) (hex0 : d.ex = none)
    (hten : ten = BitVec.ofNat 64 (10 ^ (d.fr.getD empty).length))
    (hrow10 : readBytes s0.mem (p10 + fracDigits d * 8) 8
      = some (natToBytes ten.toNat 8))
    (hrowP : ∀ j, j ≤ 22 → readBytes s0.mem (pd + j * 8) 8
      = some (natToBytes (uitofpBits ((10 : Nat) ^ j)).toNat 8))
    (hwf : d.wellFormed) (h1 : Tier1 d)
    (hsign : (sign = 1) ↔ d.neg = false)
    (hrc : roundMag (opP d) (opD d) = .fin c) (hcM : c.IsMag) :
    ∃ (k : Nat) (o : CallOutcome),
      LeanLLVM.runFuel calls k numFastBody (stateAt s0.env s0)
        = some (.ret (some o.ret) o.mem) ∧
      o.ret = .int 32 1 ∧
      o.mem = writeBytes s0.mem out (wordBytes 8 (strtodSpec d).toBits) ∧
      UnchangedOutside s0.mem o.mem [(out, 8), (err, 8)] := by
  obtain ⟨hpc, hpre, hn64, hmem, hp, hn, hinc64, hinc63, hip4, h7⟩ := he
  have hkeep : NumFastKept env0 e := hchain.kept hkeep0
  have hout : lookupName e.env "%out" = some (.ptr out) := by
    rw [hkeep "%out" (by simp [numFastKept])]
    exact hout0
  have hp10 : lookupName e.env "@NUMF_EL1_P10" = some (.ptr p10) := by
    rw [hkeep "@NUMF_EL1_P10" (by simp [numFastKept])]
    exact hp10_0
  have hpwt : lookupName e.env "@NUMF_EL1_POW10" = some (.ptr pd) := by
    rw [hkeep "@NUMF_EL1_POW10" (by simp [numFastKept])]
    exact hpwt_0
  have hsig : lookupName e.env "%tobool274.not" = some (.int 1 sign) :=
    hchain.sign (fun _ h => h) hsign0
  have he' : intRunEndWord e.mem bs a n i0 d0 e :=
    ⟨hpc, hpre, hn64, rfl, hp, hn, hinc64, hinc63, hip4, h7⟩
  have hrow10' : readBytes e.mem (p10 + fracDigits d * 8) 8
      = some (natToBytes ten.toNat 8) := by
    rw [hmem]; exact hrow10
  have hrowP' : ∀ j, j ≤ 22 → readBytes e.mem (pd + j * 8) 8
      = some (natToBytes (uitofpBits ((10 : Nat) ^ j)).toNat 8) := by
    intro j hj
    rw [hmem]; exact hrowP j hj
  obtain ⟨k, o, hrun, hret, hmem', hframe⟩ :=
    t1_end230_run (calls := calls) (s := e) (bs := bs) (d := d) (sign := sign)
      (out := out) (p10 := p10) (pd := pd) (err := err) (ten := ten) (c := c)
      (a := a) (n := n) (i0 := i0) (d0 := d0)
      he' hi0 hbn hshape hint hfr0 hex0 hsig hout hp10 hpwt hten hrow10' hrowP'
      hwf h1 hsign hrc hcM
  obtain ⟨j, hj⟩ := hchain.runFuel
  refine ⟨j + k, o, ?_, hret, ?_, ?_⟩
  · show LeanLLVM.runFuel calls (j + k) numFastBody s0
      = some (.ret (some o.ret) o.mem)
    rw [hj k]
    exact hrun
  · rw [hmem']
    rw [hmem]
  · simpa only [hmem] using hframe

/-! ### The conversion from `entry`, modulo the digit run's chain

The dispatch's three steps are produced (`sign_at_ifEnd6`); the conversion's six
follow a chain from the state they leave.  The composition is the arm's
conclusion at `entry`, and its one input is the chain across the digit run. -/

/-- **The tier-1 conversion from `entry`.**  From `entry` at a non-empty lexeme
whose first byte is the lexeme's, the dispatch's test, sign check and `if.end`'s
`phi`s reach `if.end6` with the sign's word set and the caller's kept cells
carried; a chain from there to the integer run's end-of-lexeme exit word, and the
six-step tier-1 run behind it, are one run from `entry` that returns `1` and
writes `strtodSpec`'s eight bytes at `%out`.  The chain is the digit run's, and it
is the only input the tree does not produce. -/
theorem t1_chain_run_of_entry {calls : Calls} {env : Env} {s : State} {d : Decimal}
    {bs : List UInt8} {out err p10 pd : Nat} {ten : BitVec 64} {c : Code}
    {a n i0 d0 : Nat} {b : UInt8}
    (hpc : s.pc = "entry")
    (hp : lookupName env "%p" = some (.ptr a))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hnpos : 0 < n) (hltn : NumFastStarts.negIndex b < n) (hnlt : n < 2 ^ 64)
    (hread : readByte s.mem a = some b)
    (hout0 : lookupName env "%out" = some (.ptr out))
    (hp10_0 : lookupName env "@NUMF_EL1_P10" = some (.ptr p10))
    (hpwt_0 : lookupName env "@NUMF_EL1_POW10" = some (.ptr pd))
    (hd : d.wellFormed) (hl : d.lexeme.toList.head? = some b)
    {e : State}
    (hchain : NumFastChain calls (fun pc => pc ≠ "if.end")
      (numFastDispatchState env s b n) e)
    (he : intRunEndWord (numFastDispatchState env s b n).mem bs a n i0 d0 e)
    (hi0 : i0 ≤ n) (hbn : d0 + n < 2 ^ 64)
    (hshape : d.ip.data.toList = (bs.drop (i0 - d0)).take (d0 + (n - i0)))
    (hint : intDigits d = d0 + (n - i0))
    (hfr0 : d.fr = none) (hex0 : d.ex = none)
    (hten : ten = BitVec.ofNat 64 (10 ^ (d.fr.getD empty).length))
    (hrow10 : readBytes (numFastDispatchState env s b n).mem
      (p10 + fracDigits d * 8) 8 = some (natToBytes ten.toNat 8))
    (hrowP : ∀ j, j ≤ 22 → readBytes (numFastDispatchState env s b n).mem
      (pd + j * 8) 8 = some (natToBytes (uitofpBits ((10 : Nat) ^ j)).toNat 8))
    (h1 : Tier1 d)
    (hrc : roundMag (opP d) (opD d) = .fin c) (hcM : c.IsMag) :
    ∃ (k : Nat) (o : CallOutcome),
      LeanLLVM.runFuel calls k numFastBody (stateAt env s)
        = some (.ret (some o.ret) o.mem) ∧
      o.ret = .int 32 1 ∧
      o.mem = writeBytes s.mem out (wordBytes 8 (strtodSpec d).toBits) ∧
      UnchangedOutside s.mem o.mem [(out, 8), (err, 8)] := by
  obtain ⟨_, hsignAt, hkeptAt, hmemAt, hfuel⟩ :=
    sign_at_ifEnd6 (calls := calls) hpc hp hn hnpos hltn hnlt hread
  have hsign : (numFastSignWord b = 1) ↔ d.neg = false :=
    NumFastSign.sign_tie_of_read hd hl rfl
  obtain ⟨k, o, hrun, hret, hmem', hframe⟩ :=
    t1_chain_run (calls := calls) (d := d)
      (s0 := numFastDispatchState env s b n) (env0 := env)
      (sign := numFastSignWord b) (bs := bs) (out := out) (err := err)
      (p10 := p10) (pd := pd) (ten := ten) (c := c)
      (a := a) (n := n) (i0 := i0) (d0 := d0)
      hchain hkeptAt hsignAt hout0 hp10_0 hpwt_0 he hi0 hbn hshape hint hfr0 hex0
      hten hrow10 hrowP hd h1 hsign hrc hcM
  refine ⟨3 + k, o, ?_, hret, ?_, ?_⟩
  · rw [hfuel k]
    exact hrun
  · rw [hmem', hmemAt]
  · simpa only [hmemAt] using hframe

/-! ### The fraction edge's integer cells

`fracRunEndWord_tie` reads the merge's five registers off the fraction run's
end-of-lexeme exit.  Two of them are the integer part's cells, which the exit
word binds by name only (`fracPartCells`); the two values are named at the
state `if.end68` formed them and carried to the exit by the run's own arms
(`fracRunEndBoundLoopCells`), so the merge's five registers are the model's from
the run's start rather than from two lookups at the exit. -/

/-- **The fraction edge from the run's start.**  Given the integer part's two
cells at the state the fraction run was entered at — the state `if.end68` left —
and the run's end-of-lexeme exit word, the merge takes `if.then241` with its five
registers as the model's.  The cells are the run's own: no block of it writes
them, so `fracRunEndBoundLoopCells` hands them back at the exit. -/
theorem fracRunEndWord_tie_cells {calls : Calls} {d : Decimal}
    {bs : List UInt8} {fs : Bytes} {a n i0 d0 : Nat} {e : State}
    (hpc : e.pc = "if.end230")
    (he : fracRunEndWord bs a n i0 d0 e)
    (hpart : NumFastIntPart (BitVec.ofNat 64 (intDigits d))
      (BitVec.ofNat 64 (Decimal.digitsNat d.ip)) e)
    (hi0 : i0 ≤ n) (hbn : d0 + n < 2 ^ 64)
    (hfs : d.fr = some fs)
    (hintF : fracDigits d = d0 + (n - i0))
    (hshape : fs.data.toList = (bs.drop (i0 - d0)).take (d0 + (n - i0)))
    (hdig : digitCount d ≤ 15) :
    ∃ o : State, o.pc = "if.then241" ∧ o.pre = some "if.end230" ∧ o.mem = e.mem ∧
      lookupName o.env "%exp10.4731" = some (.int 64 0) ∧
      lookupName o.env "%idig.4709716730"
        = some (.int 64 (BitVec.ofNat 64 (intDigits d))) ∧
      lookupName o.env "%ip.5708717729"
        = some (.int 64 (BitVec.ofNat 64 (Decimal.digitsNat d.ip))) ∧
      lookupName o.env "%fr.5718728"
        = some (.int 64 (BitVec.ofNat 64 (Decimal.digitsNat fs))) ∧
      lookupName o.env "%fdig.4719727"
        = some (.int 64 (BitVec.ofNat 64 (fracDigits d))) ∧
      ∀ k, LeanLLVM.runFuel calls (1 + k) numFastBody (stateAt e.env e) =
        LeanLLVM.runFuel calls k numFastBody o :=
  NumFastEntry.fracRunEndWord_tie hpc he hi0 hbn hpart.1 hpart.2 hfs hintF
    hshape hdig

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.sign_at_ifEnd6' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sign_at_ifEnd6

/-- info: 'LeanLLVM.Refinement.t1_chain_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms t1_chain_run

/-- info: 'LeanLLVM.Refinement.t1_chain_run_of_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms t1_chain_run_of_entry

/-- info: 'LeanLLVM.Refinement.fracRunEndWord_tie_cells' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fracRunEndWord_tie_cells

end LeanLLVM.Refinement
