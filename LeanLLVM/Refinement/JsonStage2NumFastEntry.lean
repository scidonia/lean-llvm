/-
`num_fast_el1`'s scan: the dispatch's entry into the digit runs, and the runs'
exits into the merge's five registers, read as the model's.

`JsonStage2NumFastScanRun` composes `entry` to the integer run's exit and the
merge block's own step, and `JsonStage2NumFastSeams` states the merge's register
ties one edge at a time: `t1_intRun_tie` at `if.end62`, `t1_headTie` at
`if.end68`, `t1_fracRun_tie` at `if.end140`.  What none of them does is carry the
*model* through the whole route: `intScan_merge` reaches `if.then241` with the
body's word, and `t1_intRun_tie` reaches it with the model's, but neither starts
where the other ends.

This module states the three joins at the model.

**The integer route.**  `intScan_tie_merge` is `entry` to `if.then241` as one
`runFuel` chain whose five registers are `Decimal`'s: `%ip` is `d.ip`'s
`digitsNat`, `%idig` its length, and the fraction's and exponent's cells are the
no-fraction, no-exponent zeroes.  It composes `intScan_end230` with
`t1_intRun_tie`; the shape hypotheses `t1_end230_run` reads (`intDigits d` and
`d.ip`'s bytes inside the lexeme) are this theorem's, because reading them off
`ByteString.literal lex = d.lexeme` is the lexeme's decomposition, not the
scan's — a lexeme's bytes are the caller's staging, and the decomposition that
makes them `d.ip` is stated where the arm is stated.

**The decimal point.**  `intScan_to_dot` is the dispatch's other exit: from
`entry` the same chain reaches either the `.` test (`land71Entry`, with the run's
stop index) or the lexeme's end at the integer part (`intRunEndWord`).  The
disjunction is the run's own: which of its two exits it takes is a byte fact the
scan's exit predicate names, and the composition keeps both.

**The fraction edge.**  `fracRunEndWord_tie` reads the fraction run's
end-of-lexeme exit word into the merge's five registers as the model's.  The
integer part's two cells (`%idig.4`, `%ip.5`) are the run's carried cells, and
the exit word carries them as `fracPartCells`, which binds the names without
their values: their tie is `t1_headTie`'s, at the block that formed them, and the
transport from there to the fraction run's exit is not this module's (see the
note below).

**What the composition cannot carry.**  `%out`, `%tobool274.not` and the two
table symbols are the caller's cells, and none of the bodies on these routes
writes them.  A `runFuel` prefix does not expose the environments it crosses, so
a composition that spans a digit run cannot re-read them at the run's exit: they
are read at the state the caller stages
(`JsonStage2NumFastRun.t1_end230_run`'s hypotheses) or carried through a
`NumFastChain` (`JsonStage2NumFastSign`), which a caller has to supply.  The
same holds for `fracPartCells`'s two integer cells.  Nothing below claims
otherwise; the two joins that need those cells state them as their hypotheses.

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

namespace NumFastEntry

/-! ### `entry` to the merge, as the model's five registers

The integer part's route: `intScan_end230` reaches `if.end230` with the run's
end-of-lexeme exit word, and `t1_intRun_tie` reads that word as the merge's five
registers.  The composition is the run's own append, so the fuel is a term of the
arguments. -/

/-- **The integer route, at the model.**  From `entry` at a lexeme whose integer
part is all digits to the lexeme's end, with the run's lead and eight-digit guard
the dispatch's, the body reaches `if.then241` within
`9 + (n - i0 + 1) * 4` control steps carrying the merge's five registers as the
model's: the folded integer part, its digit count, and the fraction's and
exponent's zeroes. -/
theorem intScan_tie_merge {calls : Calls} {env : Env} {s : State} {a n : Nat} {bs : List UInt8}
    {b b0 : UInt8} {d : Decimal}
    (hpc : s.pc = "entry")
    (hp : lookupName env "%p" = some (.ptr a))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem a n = some bs)
    (hsign : readByte s.mem a = some b)
    (hbyte : readByte s.mem (a + NumFastStarts.negIndex b) = some b0)
    (hlead : 0x31 ≤ b0 ∧ b0 ≤ 0x39)
    (hnpos : 0 < n) (hltn : NumFastStarts.negIndex b < n)
    (hnext : NumFastStarts.negIndex b + 1 < n)
    (hfast : n < NumFastStarts.negIndex b + 9) (hnlt : n < 2 ^ 63)
    (hdigits : ∀ k, NumFastStarts.negIndex b + 1 ≤ k → k < n →
      IsDigitB (bs.getD k 0) = true)
    (hint : intDigits d = 1 + (n - (NumFastStarts.negIndex b + 1)))
    (hshape : d.ip.data.toList
      = (bs.drop (NumFastStarts.negIndex b + 1 - 1)).take
          (1 + (n - (NumFastStarts.negIndex b + 1))))
    (hdig : digitCount d ≤ 15) :
    ∃ (o : State) (j : Nat),
      j ≤ 9 + (n - (NumFastStarts.negIndex b + 1) + 1) * 4 ∧
      o.pc = "if.then241" ∧ o.pre = some "if.end230" ∧
      lookupName o.env "%exp10.4731" = some (.int 64 0) ∧
      lookupName o.env "%idig.4709716730"
        = some (.int 64 (BitVec.ofNat 64 (intDigits d))) ∧
      lookupName o.env "%ip.5708717729"
        = some (.int 64 (BitVec.ofNat 64 (Decimal.digitsNat d.ip))) ∧
      lookupName o.env "%fr.5718728" = some (.int 64 0) ∧
      lookupName o.env "%fdig.4719727" = some (.int 64 0) ∧
      ∀ k, runFuel calls (j + k) numFastBody (stateAt env s) =
        runFuel calls k numFastBody o := by
  obtain ⟨e, j0, hj0, hend, hrun0⟩ :=
    NumFastScanRun.intScan_end230 hpc hp hn hread hsign hbyte hlead hnpos hltn hnext
      hfast hnlt hdigits
  have h230 : e.pc = "if.end230" := hend.1
  have hpre : e.pre = some "if.end62" := hend.2.1
  have hi0 : NumFastStarts.negIndex b + 1 ≤ n := by omega
  have hbn : 1 + n < 2 ^ 64 := by omega
  obtain ⟨o, hpc', hpre', _, hexp, hid', hip', hfr, hfd, hrun1⟩ :=
    NumFastSeams.t1_intRun_tie (calls := calls) (d := d) (bs := bs)
      (mem0 := s.mem) (p := a) (n := n)
      (i0 := NumFastStarts.negIndex b + 1) (d0 := 1) (e := e)
      h230 (Or.inr hend) hi0 hbn hint hshape hdig
  refine ⟨o, j0 + 1, by omega, hpc', hpre', hexp, hid', hip', hfr, hfd, ?_⟩
  intro k
  rw [show j0 + 1 + k = j0 + (1 + k) from by omega]
  exact (hrun0 (1 + k)).trans (hrun1 k)

/-! ### `entry` to the `.` test

The dispatch's other exit.  The integer run's non-digit exit leaves for
`land.lhs.true71` in one step (`intRunExit_land71`), and its end-of-lexeme exit is
the merge's own edge instead; the composition keeps the run's two answers rather
than deciding a byte the exit predicate already names. -/

/-- **The scan reaches the `.` test, or the lexeme ends at the integer part.**
From `entry` at a lexeme whose integer part leads with `'1' … '9'` and whose
eight-digit guard is refused, the body reaches, within
`9 + (n - i0 + 1) * 4` control steps, either the dispatch's `.` test (with the
run's stop index) or the integer run's end-of-lexeme exit word. -/
theorem intScan_to_dot {calls : Calls} {env : Env} {s : State} {a n : Nat} {bs : List UInt8}
    {b b0 : UInt8}
    (hpc : s.pc = "entry")
    (hp : lookupName env "%p" = some (.ptr a))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hread : readBytes s.mem a n = some bs)
    (hsign : readByte s.mem a = some b)
    (hbyte : readByte s.mem (a + NumFastStarts.negIndex b) = some b0)
    (hlead : 0x31 ≤ b0 ∧ b0 ≤ 0x39)
    (hnpos : 0 < n) (hltn : NumFastStarts.negIndex b < n)
    (hnext : NumFastStarts.negIndex b + 1 < n)
    (hfast : n < NumFastStarts.negIndex b + 9) (hnlt : n < 2 ^ 63) :
    ∃ (e : State) (j : Nat),
      j ≤ 9 + (n - (NumFastStarts.negIndex b + 1) + 1) * 4 ∧
      ((∃ i1, NumFastSeams.land71Entry e.mem a n i1 e) ∨
        intRunEndWord s.mem bs a n (NumFastStarts.negIndex b + 1) 1 e) ∧
      ∀ k, runFuel calls (j + k) numFastBody (stateAt env s) =
        runFuel calls k numFastBody e := by
  obtain ⟨e0, j0, hj0, hexit, hrun0⟩ :=
    NumFastScanRun.intScan_run (calls := calls) hpc hp hn hread hsign hbyte hlead
      hnpos hltn hnext hfast hnlt
  rcases hexit with hleft | hend
  · obtain ⟨i1, e1, hland, hrun1⟩ :=
      NumFastSeams.intRunExit_land71 (calls := calls) (mem0 := s.mem) (bs := bs)
        (p := a) (n := n) (i0 := NumFastStarts.negIndex b + 1) (d0 := 1) (e := e0)
        hleft.1 (Or.inl hleft) hnlt
    refine ⟨e1, j0 + 1, by omega, Or.inl ⟨i1, ?_⟩, ?_⟩
    · have hmem : e1.mem = e0.mem := hland.2.2.1
      rw [hmem]
      exact hland
    · intro k
      rw [show j0 + 1 + k = j0 + (1 + k) from by omega]
      exact (hrun0 (1 + k)).trans (hrun1 k)
  · exact ⟨e0, j0, by omega, Or.inr hend, hrun0⟩

/-! ### The fraction run's exit into the merge's cells

`fracRunEndWord` names the fraction edge's registers; `t1_fracRun_tie` reads them
as the model's.  The one rewrite between the two is the count `%17`, which the
head's preheader formed as `%fdig + %n - %i.5` and which is the run's digit count
when the run starts inside the lexeme (`seven_tie`). -/

/-- **The fraction edge, at the model.**  From the fraction run's
end-of-lexeme exit word, with the integer part's two cells the model's and the
fraction's bytes the lexeme's, the merge takes `if.then241` with its five
registers as the model's: one control step. -/
theorem fracRunEndWord_tie {calls : Calls} {d : Decimal} {bs : List UInt8} {fs : Bytes}
    {a n i0 d0 : Nat} {e : State}
    (hpc : e.pc = "if.end230")
    (he : fracRunEndWord bs a n i0 d0 e)
    (hi0 : i0 ≤ n) (hbn : d0 + n < 2 ^ 64)
    (hid : lookupName e.env "%idig.4"
      = some (.int 64 (BitVec.ofNat 64 (intDigits d))))
    (hip : lookupName e.env "%ip.5"
      = some (.int 64 (BitVec.ofNat 64 (Decimal.digitsNat d.ip))))
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
      ∀ k, runFuel calls (1 + k) numFastBody (stateAt e.env e) =
        runFuel calls k numFastBody o := by
  obtain ⟨_, hpre, _, _, _, _, _, hfr4, h17, _⟩ := he
  have h17' : lookupName e.env "%17"
      = some (.int 64 (BitVec.ofNat 64 (d0 + (n - i0)))) := by
    rw [h17, NumFastSeams.seven_tie hi0 hbn]
  exact NumFastSeams.t1_fracRun_tie (calls := calls) (d := d) (bs := bs) (fs := fs)
    (i0 := i0) (d0 := d0) (n := n) (e := e) hpc hpre hid hip hfr4 h17' hfs hintF
    hshape hdig

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.NumFastEntry.intScan_tie_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms intScan_tie_merge

/-- info: 'LeanLLVM.Refinement.NumFastEntry.intScan_to_dot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms intScan_to_dot

/-- info: 'LeanLLVM.Refinement.NumFastEntry.fracRunEndWord_tie' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fracRunEndWord_tie

end NumFastEntry

end LeanLLVM.Refinement
