/-
Tier 1's fraction route: the dispatch's `.` answer, the run's carry, and the
conversion at the merge.

`JsonStage2NumFastSeams.fracScan_end230Cells` carries the integer part's two
cells through the fraction dispatch and the run, and
`JsonStage2NumFastGate.t1_fracEnd230_run` is the conversion from the run's
end-of-lexeme exit.  The two do not compose as they stand: the conversion reads
`%out`, the two table symbols and the sign at the *exit* state, and the fraction
run carried only the integer part's cells there.  This module closes that seam,
which is what the `.` answer of the dispatch has to hand a conversion:

1. **The run's carry.**  `fracRunEndFrameCarried` frames
   `fracRunEndBoundLoop` on the integer part's cells, the caller's kept cells and
   sign (`NumFastCarried`), and the staging the run reads (`s.mem = mem`).
   `fracRun_step_loop`'s and `fracRun_step_exit`'s arms hand the first two back,
   and the exit arm hand the staging back too; the loop's own invariant carries
   it at each head, so the frame's back edge spends the arm's conditional
   transport at both endpoints.
2. **The seam.**  `fracScan_end230Carried` composes the dispatch's six steps,
   `JsonStage2NumFastStarts.fracRun_start`, and the framed run: from the `.`
   test it reaches `if.end230` with the run's end-of-lexeme exit word, the
   integer part's cells, the kept cells and sign, and the staging — the words
   `t1_fracEnd230_run` reads, at the state it reads them.
3. **The arm at the `.` test.**  `fracScan_t1_arm` spends them: the gate's step
   and the conversion's five, and `strtodSpec`'s eight bytes at `%out` with the
   caller's cursor and frame.  `fracScan_t1_arm_of_dispatch` is the same
   statement at the staged entry state, with the integer part's two cells the
   dispatch's own — `if.end68`'s `%idig.4`/`%ip.5`, the run's count and
   `digitFold` — tied to the model's `intDigits`/`digitsNat d.ip`.

The `.` answer itself is `JsonStage2NumFastEntry.intScan_to_dot`'s left
disjunct, which now carries the two cells `if.end68` installed; whether the
integer run leaves by that disjunct or at the lexeme's end is the run's two
answers, and the caller chooses the disjunct it has.

There is no `sorry`, `admit` or `native_decide` below.
-/
import LeanLLVM.Refinement.JsonStage2NumFastGate
import LeanLLVM.Refinement.JsonStage2NumFastEntry

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

namespace NumFastFraction

/-! ### The fraction run framed on the caller's words

The loop is `fracRunEndBoundLoop`: its exit is `if.end230` from `if.end140`, its
exit word `fracRunEndWord`, its budget the lexeme's remainder.  The caller's
property is what the conversion at the merge reads — the integer part's two
cells, the kept cells and the sign, and the staging the two table rows come
from.  Each arm hands it back at its own endpoint: the cells and the carried
sign through the arm's conditional transport, and the staging through the
endpoint's own memory, which is the step's source's (`stateAt` writes the
environment and nothing else). -/

/-- **The fraction run's end-of-lexeme loop, framed on the merge's reads.** -/
def fracRunEndFrameCarried {calls : Calls} (mem0 : Mem) (p n i0 d0 : Nat) (bs : List UInt8)
    (cost : Nat) (hcost : 4 ≤ cost)
    (hdigits : ∀ k, i0 ≤ k → k < n → IsDigitB (bs.getD k 0) = true)
    (idig ip : BitVec 64) (env0 : Env) (sign : BitVec 1) (mem : Mem) :
    BoundLoopFrame calls numFastBody :=
  { loop := fracRunEndBoundLoop mem0 p n i0 d0 bs cost hcost hdigits
    P := fun s => NumFastIntPart idig ip s ∧ NumFastCarried env0 sign s ∧ s.mem = mem
    step_exit := by
      intro r s c hinv hb
      obtain ⟨e, j, hj, hword, hcell, hcarried, hmem, hrun⟩ :=
        fracRun_step_end230 hinv hb hdigits
      refine ⟨e, j, by simp only [fracRunEndBoundLoop]; omega, hword.1, hword,
        fun hP => ⟨hcell idig ip hP.1, hcarried env0 sign hP.2.1, ?_⟩, hrun⟩
      rw [hmem]
      exact hP.2.2
    step_loop := by
      intro r s c hinv hb
      obtain ⟨e, c', j, hj, hpc, hlt, hinv', hcell, hcarried, hrun⟩ :=
        fracRun_step_loop hinv hb
      have hsmem : s.mem = mem0 := hinv.2.1
      have hemem : e.mem = mem0 := hinv'.2.1
      refine ⟨e, c', j, by simp only [fracRunEndBoundLoop]; omega, hpc, hlt, hinv',
        fun hP => ⟨hcell idig ip hP.1, hcarried env0 sign hP.2.1, ?_⟩, hrun⟩
      rw [hemem, ← hsmem]
      exact hP.2.2 }

/-! ### The `.` answer runs the fraction, cells and all

The dispatch's six steps install the run's head; the framed run then leaves the
merge with the exit word and the caller's words.  The staging is `land71Entry`'s
own memory, which is the state the dispatch entered at. -/

/-- **The fraction route ends at the merge with the merge's reads.**  From the
`.` test with a digit after the `.`, the length past it and the eight-digit
guard refused, the dispatch and the run reach `if.end230` within
`6 + (n - i0 + 1) * 4` control steps, `i0 = i1 + 1` the index after the decimal
point, carrying the run's end-of-lexeme exit word, the integer part's cells, the
caller's kept cells and sign, and the staging the exit read. -/
theorem fracScan_end230Carried {calls : Calls} {mem : Mem} {e : State} {a n i1 : Nat}
    {bs : List UInt8} {bd bd2 : UInt8} {idig ip : BitVec 64}
    {env0 : Env} {sign : BitVec 1}
    (h : NumFastSeams.land71Entry mem a n i1 e)
    (hpart : NumFastIntPart idig ip e) (hcarried : NumFastCarried env0 sign e)
    (hread : readBytes mem a n = some bs)
    (hdot : readByte mem (a + i1) = some bd) (hdoteq : bd = 0x2E)
    (hd2 : readByte mem (a + (i1 + 1)) = some bd2) (hd2digit : IsDigitB bd2 = true)
    (hltn : i1 + 1 < n) (hfast : n < i1 + 9) (hnlt : n < 2 ^ 63)
    (hdigits : ∀ k, i1 + 1 ≤ k → k < n → IsDigitB (bs.getD k 0) = true) :
    ∃ (e' : State) (j : Nat), j ≤ 6 + (n - (i1 + 1) + 1) * 4 ∧
      fracRunEndWord bs a n (i1 + 1) 0 e' ∧ NumFastIntPart idig ip e' ∧
      NumFastCarried env0 sign e' ∧ e'.mem = mem ∧
      ∀ k, runFuel calls (j + k) numFastBody e = runFuel calls k numFastBody e' := by
  rcases h with ⟨hpc, _, hmem, hp, hn, hi5, hparts⟩
  obtain ⟨e0, hinv0, hcell0, hcarried0, hrun0⟩ :=
    NumFastStarts.fracRun_start (calls := calls) (env := e.env) (s := e)
      hpc hp hn (by rw [hmem]; exact hread) hi5 hparts
      (by rw [hmem]; exact hdot) hdoteq (by rw [hmem]; exact hd2) hd2digit
      hltn hfast hnlt
  have hpart0 : NumFastIntPart idig ip (stateAt e.env e) := by
    simpa only [stateAt] using hpart
  have hcarried0' : NumFastCarried env0 sign (stateAt e.env e) := by
    simpa only [stateAt] using hcarried
  have hmem0 : e0.mem = mem := hinv0.2.1.trans hmem
  obtain ⟨e1, j1, hj1, _, hend, ⟨hpart1, hcarried1, hmem1⟩, hrun1⟩ :=
    (fracRunEndFrameCarried e.mem a n (i1 + 1) 0 bs 4 (by omega) hdigits idig ip
      env0 sign mem).run_from (n - (i1 + 1)) e0 0 hinv0
      ⟨hcell0 idig ip hpart0, hcarried0 env0 sign hcarried0', hmem0⟩
  refine ⟨e1, 6 + j1, Nat.add_le_add_left hj1 6, hend, hpart1, hcarried1, hmem1, ?_⟩
  intro k
  rw [show 6 + j1 + k = 6 + (j1 + k) from by omega]
  exact (hrun0 (j1 + k)).trans (hrun1 k)

/-! ### The arm at the `.` test

The merge's gate takes `if.then241` at the model's counters and the conversion's
five steps write `strtodSpec`'s bytes.  Everything the conversion reads at the
merge — `%out`, the two symbols, the sign — is the run's carry, not a
hypothesis. -/

/-- **The tier-1 arm at the `.` test.**  At the dispatch's `.` entry, for a
well-formed lexeme whose integer part stops on the `.`, whose fraction is the
bytes after it to the lexeme's end, and whose counters are inside tier 1's
window, the body reaches its return: it returns `1`, writes `strtodSpec`'s eight
bytes at `%out`, leaves the cursor where the caller had it, and leaves every byte
outside the two slots as it was. -/
theorem fracScan_t1_arm {calls : Calls} {mem : Mem} {e : State} {a n i1 : Nat}
    {bs : List UInt8} {bd bd2 : UInt8} {fs : Bytes} {d : Decimal}
    {env0 : Env} {sign : BitVec 1} {out err p10 pd : Nat} {ten : BitVec 64}
    {c : Code}
    (h : NumFastSeams.land71Entry mem a n i1 e)
    (hpart : NumFastIntPart (BitVec.ofNat 64 (intDigits d))
      (BitVec.ofNat 64 (Decimal.digitsNat d.ip)) e)
    (hcarried : NumFastCarried env0 sign e)
    (hread : readBytes mem a n = some bs)
    (hdot : readByte mem (a + i1) = some bd) (hdoteq : bd = 0x2E)
    (hd2 : readByte mem (a + (i1 + 1)) = some bd2) (hd2digit : IsDigitB bd2 = true)
    (hltn : i1 + 1 < n) (hfast : n < i1 + 9) (hnlt : n < 2 ^ 63)
    (hdigits : ∀ k, i1 + 1 ≤ k → k < n → IsDigitB (bs.getD k 0) = true)
    (hfs : d.fr = some fs)
    (hintF : fracDigits d = 0 + (n - (i1 + 1)))
    (hshape : fs.data.toList = (bs.drop ((i1 + 1) - 0)).take (0 + (n - (i1 + 1))))
    (hdig : digitCount d ≤ 15)
    (hex0 : d.ex = none)
    (hout : lookupName env0 "%out" = some (.ptr out))
    (hp10 : lookupName env0 "@NUMF_EL1_P10" = some (.ptr p10))
    (hpwt : lookupName env0 "@NUMF_EL1_POW10" = some (.ptr pd))
    (hten : ten = BitVec.ofNat 64 (10 ^ fs.length))
    (hrow10 : readBytes mem (p10 + fracDigits d * 8) 8
      = some (natToBytes ten.toNat 8))
    (hrowP : ∀ j, j ≤ 22 → readBytes mem (pd + j * 8) 8
      = some (natToBytes (uitofpBits ((10 : Nat) ^ j)).toNat 8))
    (hwf : d.wellFormed) (h1 : Tier1 d)
    (hsign : (sign = 1) ↔ d.neg = false)
    (hrc : roundMag (opP d) (opD d) = .fin c) (hcM : c.IsMag) :
    ∃ (k : Nat) (o : CallOutcome),
      runFuel calls k numFastBody e = some (.ret (some o.ret) o.mem) ∧
      o.ret = .int 32 1 ∧
      o.mem = writeBytes mem out (wordBytes 8 (strtodSpec d).toBits) ∧
      o.next = e.next ∧
      UnchangedOutside mem o.mem [(out, 8), (err, 8)] := by
  obtain ⟨e1, j, _hj, hend, hpart1, hcarried1, hmem, hrun⟩ :=
    fracScan_end230Carried h hpart hcarried hread hdot hdoteq hd2 hd2digit hltn
      hfast hnlt hdigits
  obtain ⟨hkeep, hsig⟩ := hcarried1
  have hout1 : lookupName e1.env "%out" = some (.ptr out) := by
    rw [hkeep "%out" (by simp [numFastKept])]
    exact hout
  have hp10₁ : lookupName e1.env "@NUMF_EL1_P10" = some (.ptr p10) := by
    rw [hkeep "@NUMF_EL1_P10" (by simp [numFastKept])]
    exact hp10
  have hpwt1 : lookupName e1.env "@NUMF_EL1_POW10" = some (.ptr pd) := by
    rw [hkeep "@NUMF_EL1_POW10" (by simp [numFastKept])]
    exact hpwt
  obtain ⟨k2, o, hrun2, hret, hmemOut, hframe⟩ :=
    NumFastGate.t1_fracEnd230_run (calls := calls) (s := e1) (bs := bs) (d := d)
      (fs := fs) (sign := sign) (out := out) (p10 := p10) (pd := pd) (err := err)
      (ten := ten) (c := c) (a := a) (n := n) (i0 := i1 + 1) (d0 := 0)
      hend hpart1 (by omega) (by omega) hfs hintF hshape hdig hex0 hsig hout1
      hp10₁ hpwt1 hten (by rw [hmem]; exact hrow10)
      (fun j' hj' => by rw [hmem]; exact hrowP j' hj')
      hwf h1 hsign hrc hcM
  refine ⟨j + k2, ⟨o.ret, o.mem, e.next⟩, ?_, hret, ?_, rfl, ?_⟩
  · rw [hrun k2]
    exact hrun2
  · rw [hmemOut, hmem]
  · simpa only [hmem] using hframe

/-! ### From the staged entry state

The dispatch's `.` answer is `JsonStage2NumFastEntry.intScan_to_dot`'s left
disjunct, and what it carries beyond the test's state is the two cells
`if.end68` installed.  Their values are the run's own count and accumulator —
`1 + (i1 - i0)` and `digitFold bs (i0 - d0) …` at the dispatch's `i0`/`d0` — and
the two equalities below are the model's statement of them.  So the arm's
fraction route at the caller's staged state is one `runFuel` append. -/

/-- **The tier-1 arm at the staged entry, on the `.` route.**  `hcont` is the
dispatch's fuel prefix (from `intScan_to_dot`'s left disjunct), `hcells` the two
cells that disjunct carries, and `hid`/`hip` the model's reading of them. -/
theorem fracScan_t1_arm_of_dispatch {calls : Calls} {env : Env} {s : State}
    {a n i1 : Nat} {bs : List UInt8} {bd bd2 : UInt8} {b : UInt8}
    {fs : Bytes} {d : Decimal} {e : State} {j : Nat}
    {env0 : Env} {sign : BitVec 1} {out err p10 pd : Nat} {ten : BitVec 64}
    {c : Code}
    (h : NumFastSeams.land71Entry e.mem a n i1 e)
    (hcells : NumFastIntPart
      (BitVec.ofNat 64 (1 + (i1 - (NumFastStarts.negIndex b + 1))))
      (BitVec.ofNat 64 (digitFold bs ((NumFastStarts.negIndex b + 1) - 1)
        (min (1 + (i1 - (NumFastStarts.negIndex b + 1))) 19))) e)
    (hid : intDigits d = 1 + (i1 - (NumFastStarts.negIndex b + 1)))
    (hip : Decimal.digitsNat d.ip = digitFold bs ((NumFastStarts.negIndex b + 1) - 1)
      (min (1 + (i1 - (NumFastStarts.negIndex b + 1))) 19))
    (hcont : ∀ k, runFuel calls (j + k) numFastBody (stateAt env s) =
      runFuel calls k numFastBody e)
    (hcarried : NumFastCarried env0 sign e)
    (hread : readBytes e.mem a n = some bs)
    (hdot : readByte e.mem (a + i1) = some bd) (hdoteq : bd = 0x2E)
    (hd2 : readByte e.mem (a + (i1 + 1)) = some bd2) (hd2digit : IsDigitB bd2 = true)
    (hltn : i1 + 1 < n) (hfast : n < i1 + 9) (hnlt : n < 2 ^ 63)
    (hdigits : ∀ k, i1 + 1 ≤ k → k < n → IsDigitB (bs.getD k 0) = true)
    (hfs : d.fr = some fs)
    (hintF : fracDigits d = 0 + (n - (i1 + 1)))
    (hshape : fs.data.toList = (bs.drop ((i1 + 1) - 0)).take (0 + (n - (i1 + 1))))
    (hdig : digitCount d ≤ 15)
    (hex0 : d.ex = none)
    (hout : lookupName env0 "%out" = some (.ptr out))
    (hp10 : lookupName env0 "@NUMF_EL1_P10" = some (.ptr p10))
    (hpwt : lookupName env0 "@NUMF_EL1_POW10" = some (.ptr pd))
    (hten : ten = BitVec.ofNat 64 (10 ^ fs.length))
    (hrow10 : readBytes e.mem (p10 + fracDigits d * 8) 8
      = some (natToBytes ten.toNat 8))
    (hrowP : ∀ j', j' ≤ 22 → readBytes e.mem (pd + j' * 8) 8
      = some (natToBytes (uitofpBits ((10 : Nat) ^ j')).toNat 8))
    (hwf : d.wellFormed) (h1 : Tier1 d)
    (hsign : (sign = 1) ↔ d.neg = false)
    (hrc : roundMag (opP d) (opD d) = .fin c) (hcM : c.IsMag) :
    ∃ (k : Nat) (o : CallOutcome),
      runFuel calls k numFastBody (stateAt env s) = some (.ret (some o.ret) o.mem) ∧
      o.ret = .int 32 1 ∧
      o.mem = writeBytes e.mem out (wordBytes 8 (strtodSpec d).toBits) ∧
      o.next = s.next ∧
      UnchangedOutside e.mem o.mem [(out, 8), (err, 8)] := by
  have hpart : NumFastIntPart (BitVec.ofNat 64 (intDigits d))
      (BitVec.ofNat 64 (Decimal.digitsNat d.ip)) e := by
    simpa only [hid, hip] using hcells
  obtain ⟨k, o, hrun, hret, hmem, _, hframe⟩ :=
    fracScan_t1_arm h hpart hcarried hread hdot hdoteq hd2 hd2digit hltn hfast
      hnlt hdigits hfs hintF hshape hdig hex0 hout hp10 hpwt hten hrow10 hrowP
      hwf h1 hsign hrc hcM
  exact ⟨j + k, ⟨o.ret, o.mem, s.next⟩, by rw [hcont k]; exact hrun, hret, hmem,
    rfl, hframe⟩

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.NumFastFraction.fracRunEndFrameCarried' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fracRunEndFrameCarried

/-- info: 'LeanLLVM.Refinement.NumFastFraction.fracScan_end230Carried' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fracScan_end230Carried

/-- info: 'LeanLLVM.Refinement.NumFastFraction.fracScan_t1_arm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fracScan_t1_arm

/-- info: 'LeanLLVM.Refinement.NumFastFraction.fracScan_t1_arm_of_dispatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fracScan_t1_arm_of_dispatch

end NumFastFraction

end LeanLLVM.Refinement
