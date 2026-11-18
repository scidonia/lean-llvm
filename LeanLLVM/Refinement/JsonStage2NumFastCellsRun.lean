/-
`num_fast_el1`'s caller's cells across the integer digit run, and the tier-1 arm
at `entry`.

`JsonStage2NumFastRun.t1_end230_run` reads four cells at the integer run's
end-of-lexeme exit that no block on the path writes: `%out`, `%tobool274.not`
and the two table symbols.  A `runFuel` prefix does not expose the environments
it crosses, so the scan's own exit word (`intRunEndWord`) names only what a
successor's `phi`s read, and a composition that spans the digit run could not
re-read those cells at the exit.  `JsonStage2NumFastCells` supplies the
transport — the kept cells are nobody's destination, the sign is `if.end`'s
alone — and `JsonStage2NumFastDigitRuns`' arms carry it: `intRun_step_loop`,
`intRun_step_exit` and `intRun_step_end230` each hand back the cells their
starting state carried, as one iteration's chain of jumps at blocks that are not
`if.end`.

This module spends that transport on the integer route.

**The loop with the cells.**  `intRunEndBoundLoopCells` is `intRunEndBoundLoop`'s
`BoundLoop` with the cells conjoined to the invariant and to the exit word, so
`run_from` hands back both the end-of-lexeme exit word and the cells at it, and
the fuel stays an identity of prefixes.  Nothing about `intRunInv`'s own shape
changes: the scan's other users (`intScan_run`, the fast path's appended runs)
keep the invariant they were stated at, because the arms' cell conclusion is
conditional on the starting state's cells and its old projection is the old
statement.

**The scan to the exit, with the cells.**  `intScan_end230Cells` is
`JsonStage2NumFastScanRun.intScan_end230` with the cells concluded at its exit:
`entry`'s step, the dispatch's seven (`intRun_start`, whose conclusion now names
the loop entry's cells) and the loop at the whole distance.

**The arm at `entry`.**  `intScan_t1_arm_at_entry` is the integer route's
instance: from the staged `entry` state, with the lexeme's integer part the whole
lexeme inside tier 1's window and the two tables staged, the body returns `1`
writing `strtodSpec`'s eight bytes at `%out`, leaving `%err` and every byte
outside the two slots as they were.  The hypotheses that remain are the model's
own ties — the lexeme's bytes as `d.ip`, the sign's word as `d.neg`, the two
tables' rows — not a cell of the body's.  `NumFastBodyArm`'s statement needs the
fraction and exponent routes, tier 1's arithmetic and tier 3's traversal as well;
this module does not claim it (see `JsonStage2NumFastArm`'s header).

There is no `sorry`, `admit` or `native_decide` below.
-/
import LeanLLVM.Refinement.JsonStage2NumFastCarried

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

/-! ### The kept cells at the dispatch's own environment

`intRun_start` is stated at `land.lhs.true`, so the state it reads is the
`entry` block's: its allocations are cells over the caller's environment, and
the kept cells are the caller's once the allocations have been peeled. -/

/-- **The entry block's allocation cells are other names.** -/
theorem numFast_lookup_entry_ne (env : Env) (nxt : Nat) (cmp : BitVec 1) {nm : String}
    (h1 : "%cmp.not" ≠ nm) (h2 : "%d269" ≠ nm) (h3 : "%v8101" ≠ nm)
    (h4 : "%v8" ≠ nm) (h5 : "%v.i.i" ≠ nm) (h6 : "%dig.i.i" ≠ nm) :
    lookupName (numFastEntryEnv env nxt cmp) nm = lookupName env nm := by
  simp only [numFastEntryEnv]
  rw [lookupName_cons_ne (k := "%cmp.not") (n := nm) _ _ h1,
    lookupName_cons_ne (k := "%d269") (n := nm) _ _ h2,
    lookupName_cons_ne (k := "%v8101") (n := nm) _ _ h3,
    lookupName_cons_ne (k := "%v8") (n := nm) _ _ h4,
    lookupName_cons_ne (k := "%v.i.i") (n := nm) _ _ h5,
    lookupName_cons_ne (k := "%dig.i.i") (n := nm) _ _ h6]

/-- **The entry block's allocations leave the kept cells at the caller's.** -/
theorem numFastEntryEnv_kept (env : Env) (nxt : Nat) (cmp : BitVec 1) (s : State) :
    NumFastKept env (stateAt (numFastEntryEnv env nxt cmp) s) := by
  intro nm hnm
  have h : nm = "%out" ∨ nm = "@NUMF_EL1_P10" ∨ nm = "@NUMF_EL1_POW10" := by
    simpa only [numFastKept, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] using hnm
  rcases h with rfl | rfl | rfl
  · exact numFast_lookup_entry_ne env nxt cmp (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact numFast_lookup_entry_ne env nxt cmp (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact numFast_lookup_entry_ne env nxt cmp (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)

/-! ### The loop at the run's exit, carrying the cells

The instance is `intRunEndBoundLoop`'s invariant and exit word with
`NumFastCarried` conjoined to both.  Its arms are the digit run's own: the loop
arm hands back the cells its iteration carried, and the end-of-lexeme exit hands
back the ones its starting state had, because the exit's blocks are not
`if.end`. -/

/-- **The integer run's end-of-lexeme loop, with the caller's cells.** -/
def intRunEndBoundLoopCells (calls : Calls) (mem0 : Mem) (p n i0 d0 : Nat)
    (bs : List UInt8) (cost : Nat) (hcost : 4 ≤ cost)
    (hdigits : ∀ k, i0 ≤ k → k < n → IsDigitB (bs.getD k 0) = true)
    (env0 : Env) (sign : BitVec 1) : BoundLoop calls numFastBody where
  head := "land.lhs.true41"
  exitBlock := "if.end230"
  N := n - i0
  cost := cost
  Inv := fun r s c => intRunInv mem0 p n i0 d0 bs r s c ∧ NumFastCarried env0 sign s
  atBound := intRunAtBound mem0 p n i0
  Exit := fun e => e.pc = "if.end230"
  ExitWord := fun e => intRunEndWord mem0 bs p n i0 d0 e ∧ NumFastCarried env0 sign e
  step_exit := by
    intro r s c hinv hb
    obtain ⟨hinv, hcells⟩ := hinv
    obtain ⟨e, j, hj, hword, hcarried, hrun⟩ := intRun_step_end230 hinv hb hdigits
    exact ⟨e, j, by omega, hword.1, ⟨hword, hcarried env0 sign hcells⟩, hrun⟩
  step_loop := by
    intro r s c hinv hb
    obtain ⟨hinv, hcells⟩ := hinv
    obtain ⟨e, c', j, hj, hpc, hlt, hinv', hcarried, hrun⟩ := intRun_step_loop hinv hb
    exact ⟨e, c', j, by omega, hpc, hlt, ⟨hinv', hcarried env0 sign hcells⟩, hrun⟩
  exit_at_zero := by
    intro s c h
    obtain ⟨hinv, _⟩ := h
    obtain ⟨_, _, hsum, _, _, _, _, _, _, _, _⟩ := hinv
    unfold intRunAtBound
    have hle : decide (n - i0 ≤ c + 1) = true := decide_eq_true (by omega)
    rw [hle]
    simp
  budget := by
    intro r s c h
    obtain ⟨hinv, _⟩ := h
    obtain ⟨_, _, hsum, _, _, _, _, _, _, _, _⟩ := hinv
    omega

/-- **The scan's end-of-lexeme exit, with the caller's cells.**  `entry`'s step,
the dispatch's seven and the digit run at the whole distance leave
`if.end230`'s exit word carrying the cells the staged environment bound. -/
theorem intScan_end230Cells {calls : Calls} {env : Env} {s : State} {a n : Nat}
    {bs : List UInt8} {b b0 : UInt8}
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
      IsDigitB (bs.getD k 0) = true) :
    ∃ (e : State) (j : Nat), j ≤ 8 + (n - (NumFastStarts.negIndex b + 1) + 1) * 4 ∧
      intRunEndWord s.mem bs a n (NumFastStarts.negIndex b + 1) 1 e ∧
      NumFastCarried env (numFastSignWord b) e ∧
      ∀ k, runFuel calls (j + k) numFastBody (stateAt env s) =
        runFuel calls k numFastBody e := by
  have hn64 : n < 2 ^ 64 := by omega
  have hne : BitVec.ofNat 64 n ≠ 0x0000000000000000#64 := by
    intro h
    have h2 := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64] at h2
    simp at h2
    omega
  let cmp : BitVec 1 := evalICmp .eq (BitVec.ofNat 64 n) 0x0000000000000000#64
  have hbit0 : cmp = 0 := NumFastStarts.eq_zero_iff _ _ |>.mpr hne
  let s1 : State := { s with next := s.next + 768 + 1568 + 4 + 4 + 8,
                              pc := "land.lhs.true", pre := some "entry" }
  have h1 : step calls numFastBody (stateAt env s) =
      .jump (stateAt (numFastEntryEnv env s.next cmp) s1) :=
    NumFastScanRun.entry_step_land (calls := calls) hpc hn hbit0
  obtain ⟨e0, hinv0, hcells0, hrun0⟩ :=
    NumFastStarts.intRun_start (calls := calls)
      (env := numFastEntryEnv env s.next cmp) (s := s1) (env0 := env)
      rfl rfl
      (NumFastScanRun.entry_env_lookup_p hp) (NumFastScanRun.entry_env_lookup_n hn)
      hread hsign hbyte hlead hltn hnext hfast hnlt
      (numFastEntryEnv_kept env s.next cmp s1)
  obtain ⟨e1, j1, hj1, _hepc, hword, hrun1⟩ :=
    (intRunEndBoundLoopCells calls s.mem a n (NumFastStarts.negIndex b + 1) 1 bs 4
      (by omega) hdigits env (numFastSignWord b)).run_from
      (n - (NumFastStarts.negIndex b + 1)) e0 0 ⟨hinv0, hcells0⟩
  obtain ⟨hexit, hcells1⟩ := hword
  refine ⟨e1, 1 + (7 + j1), ?_, hexit, hcells1, ?_⟩
  · rw [show 1 + (7 + j1) = 8 + j1 from by omega]
    exact Nat.add_le_add_left hj1 8
  · intro k
    rw [show 1 + (7 + j1) + k = 1 + (7 + (j1 + k)) from by omega,
      runFuel_jump_prefix h1 (7 + (j1 + k))]
    exact (hrun0 (j1 + k)).trans (hrun1 k)

/-! ### The tier-1 arm at `entry`

The scan hands the exit word with the cells; `t1_end230_run` is the six-step
conversion from it, with the sign read off the cell the dispatch wrote and the
three kept cells off the staged environment. -/

/-- **The tier-1 arm at `entry`, on the integer route.**  At a staging whose four
argument cells are the caller's, whose lexeme at `p` is a well-formed number's
integer part — the lead a `'1' … '9'`, the rest digits, the whole inside tier 1's
window, no fraction and no exponent — and whose two tables are staged, the body
runs from `entry` to its return: it returns `1`, writes `strtodSpec`'s eight
bytes at `%out`, leaves the cursor where the caller had it, and leaves every byte
outside the two slots as it was.

The hypotheses are the model's ties: `d`'s integer part is the lexeme's bytes,
its digit count the run's, its sign the dispatch's word, and the two tables' rows
the ones `strtodSpec` reads.  Everything the body itself must carry — `%out`, the
two symbols, the sign — is the scan's, by `intScan_end230Cells`. -/
theorem intScan_t1_arm_at_entry {calls : Calls} {env : Env} {s : State} {a n : Nat}
    {bs : List UInt8} {b b0 : UInt8} {d : Decimal} {out err p10 pd : Nat}
    {ten : BitVec 64} {c : Code}
    (hpc : s.pc = "entry")
    (hp : lookupName env "%p" = some (.ptr a))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hout : lookupName env "%out" = some (.ptr out))
    (hp10 : lookupName env "@NUMF_EL1_P10" = some (.ptr p10))
    (hpwt : lookupName env "@NUMF_EL1_POW10" = some (.ptr pd))
    (hread : readBytes s.mem a n = some bs)
    (hsign : readByte s.mem a = some b)
    (hbyte : readByte s.mem (a + NumFastStarts.negIndex b) = some b0)
    (hlead : 0x31 ≤ b0 ∧ b0 ≤ 0x39)
    (hnpos : 0 < n) (hltn : NumFastStarts.negIndex b < n)
    (hnext : NumFastStarts.negIndex b + 1 < n)
    (hfast : n < NumFastStarts.negIndex b + 9) (hnlt : n < 2 ^ 63)
    (hdigits : ∀ k, NumFastStarts.negIndex b + 1 ≤ k → k < n →
      IsDigitB (bs.getD k 0) = true)
    (hshape : d.ip.data.toList
      = (bs.drop (NumFastStarts.negIndex b + 1 - 1)).take
          (1 + (n - (NumFastStarts.negIndex b + 1))))
    (hint : intDigits d = 1 + (n - (NumFastStarts.negIndex b + 1)))
    (hfr0 : d.fr = none) (hex0 : d.ex = none)
    (hsigw : (numFastSignWord b = 1) ↔ d.neg = false)
    (hten : ten = BitVec.ofNat 64 (10 ^ (d.fr.getD empty).length))
    (hrow10 : readBytes s.mem (p10 + fracDigits d * 8) 8
      = some (natToBytes ten.toNat 8))
    (hrowP : ∀ j, j ≤ 22 → readBytes s.mem (pd + j * 8) 8
      = some (natToBytes (uitofpBits (10 ^ j)).toNat 8))
    (hwf : d.wellFormed) (h1 : Tier1 d)
    (hrc : roundMag (opP d) (opD d) = .fin c) (hcM : c.IsMag) :
    ∃ (k : Nat) (o : CallOutcome),
      runFuel calls k numFastBody (stateAt env s) = some (.ret (some o.ret) o.mem) ∧
      o.ret = .int 32 1 ∧
      o.mem = writeBytes s.mem out (wordBytes 8 (strtodSpec d).toBits) ∧
      o.next = s.next ∧
      UnchangedOutside s.mem o.mem [(out, 8), (err, 8)] := by
  obtain ⟨e1, jscan, hjscan, hexit, hcells1, hrun1⟩ :=
    intScan_end230Cells (calls := calls) hpc hp hn hread hsign hbyte hlead hnpos
      hltn hnext hfast hnlt hdigits
  have hmem1 : e1.mem = s.mem := hexit.2.2.2.1
  have hexit' : intRunEndWord e1.mem bs a n (NumFastStarts.negIndex b + 1) 1 e1 := by
    rw [hmem1]
    exact hexit
  have hout1 : lookupName e1.env "%out" = some (.ptr out) := by
    rw [hcells1.1 "%out" (by simp [numFastKept])]
    exact hout
  have hp10₁ : lookupName e1.env "@NUMF_EL1_P10" = some (.ptr p10) := by
    rw [hcells1.1 "@NUMF_EL1_P10" (by simp [numFastKept])]
    exact hp10
  have hpwt1 : lookupName e1.env "@NUMF_EL1_POW10" = some (.ptr pd) := by
    rw [hcells1.1 "@NUMF_EL1_POW10" (by simp [numFastKept])]
    exact hpwt
  obtain ⟨k2, o, hrun2, hret, hmem, hframe⟩ :=
    t1_end230_run (calls := calls) (s := e1) (bs := bs) (d := d)
      (sign := numFastSignWord b) (out := out) (p10 := p10) (pd := pd)
      (err := err) (ten := ten) (c := c)
      (a := a) (n := n) (i0 := NumFastStarts.negIndex b + 1) (d0 := 1)
      hexit' (by omega) (by omega) hshape hint hfr0 hex0 hcells1.2 hout1 hp10₁ hpwt1
      hten (by rw [hmem1]; exact hrow10)
      (fun j hj => by rw [hmem1]; exact hrowP j hj) hwf h1 hsigw hrc hcM
  have hmem' : o.mem = writeBytes s.mem out (wordBytes 8 (strtodSpec d).toBits) := by
    rw [hmem, hmem1]
  have hframe' : UnchangedOutside s.mem o.mem [(out, 8), (err, 8)] := by
    rw [← hmem1]
    exact hframe
  refine ⟨jscan + k2, ⟨o.ret, o.mem, s.next⟩, ?_, hret, hmem', rfl, hframe'⟩
  rw [hrun1 k2]
  exact hrun2

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.numFastEntryEnv_kept' depends on axioms: [propext] -/
#guard_msgs in
#print axioms numFastEntryEnv_kept

/-- info: 'LeanLLVM.Refinement.intRunEndBoundLoopCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms intRunEndBoundLoopCells

/-- info: 'LeanLLVM.Refinement.intScan_end230Cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms intScan_end230Cells

/-- info: 'LeanLLVM.Refinement.intScan_t1_arm_at_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms intScan_t1_arm_at_entry

end LeanLLVM.Refinement
