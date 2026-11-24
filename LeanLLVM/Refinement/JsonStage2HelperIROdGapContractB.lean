/-
`od_gap_recover`'s first-scan bridges to `if.end`.

The committed `JsonStage2HelperIROdGapContract` carries the staging, the rule,
the no-write row, the byte vocabulary, the `gapAfterLoop` rewrites and the three
non-literal write rows.  What it does not carry is the composed first scan: the
entry prefix, the position test's true edge, `gapScanLoop_run`, the strengthened
`gapScanExit` (whose `while.end` arm now carries the entry's allocator cursor) and
the `while.end` continuation, exposing every cell the write rows read at `if.end`,
including `s.next = next + (Ty.double).sizeBytes + (Ty.int 64).sizeBytes`.
-/
import LeanLLVM.Refinement.JsonStage2HelperIROdGapContract
import LeanLLVM.Refinement.JsonStage2HelperIROdGapRun

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR (stage2Calls)
open LeanLLVM.Refinement.BlockEval

/-- The `while.end` continuation's state carries the scan's cells. -/
theorem odGap_run_to_ifEnd_true {mem : Mem} {next c pos lt lf ln : Nat} {win : List UInt8}
    (P : OdGapPrep mem next c pos lt lf ln win)
    (hklt : P.k < P.nix) (hposlt : pos < P.ip)
    (hne : gapEe win P.ip pos ≠ P.ip) :
    ∃ (s : State) (j : Nat), j ≤ (P.ip + 1) * 5 + 4 ∧
      s.pc = "if.end" ∧ s.pre = some "while.end" ∧ s.mem = mem ∧
      s.next = next + (Ty.double).sizeBytes + (Ty.int 64).sizeBytes ∧
      lookupName s.env "%0" = some (.ptr P.b) ∧
      lookupName s.env "%c" = some (.ptr c) ∧
      lookupName s.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 pos)) ∧
      lookupName s.env "%cond" = some (.int 64 (BitVec.ofNat 64 P.ip)) ∧
      lookupName s.env "%d" = some (.ptr next) ∧
      lookupName s.env "%ei" = some (.ptr (next + (Ty.double).sizeBytes)) ∧
      lookupName s.env "%littrue" = some (.ptr lt) ∧
      lookupName s.env "%litfalse" = some (.ptr lf) ∧
      lookupName s.env "%litnull" = some (.ptr ln) ∧
      lookupName s.env "%ee.0.lcssa" =
        some (.int 64 (BitVec.ofNat 64 (gapEe win P.ip pos))) ∧
      (∀ k, runFuel (stage2Calls stage2SubCalls) (4 + j + k) odGapRecoverBody
        (EntryState odGapRecoverBody (odGapEntryArgs c pos lt lf ln) mem next) =
        runFuel (stage2Calls stage2SubCalls) k odGapRecoverBody s) := by
  obtain ⟨s, hrun, hpc, hpre, hmem, hnextP, h0, hc, ht, hd, hei, hlt, hlf, hln, hconv⟩ :=
    gapPrefix_true P hklt
  let sH : State := stateAt (("%cmp310", .int 1 (evalICmp .ult (BitVec.ofNat 64 pos)
      (BitVec.ofNat 64 P.ip))) :: ("%cond", .int 64 (BitVec.ofNat 64 P.ip)) :: s.env)
    { s with pc := "land.rhs", pre := some "cond.end" }
  have hstep : step (stage2Calls stage2SubCalls) odGapRecoverBody s = .jump sH :=
    gapCondEnd_landRhs_true (s := s) hpc hpre ht hconv P.hip64 hposlt
  have h0H : lookupName sH.env "%0" = some (.ptr P.b) := by
    simp only [sH, stateAt]; block_lk
  have hcH : lookupName sH.env "%c" = some (.ptr c) := by
    simp only [sH, stateAt]; block_lk
  have htH : lookupName sH.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 pos)) := by
    simp only [sH, stateAt]; block_lk
  have hcondH : lookupName sH.env "%cond" = some (.int 64 (BitVec.ofNat 64 P.ip)) := by
    simp only [sH, stateAt]; block_lk
  have hdH : lookupName sH.env "%d" = some (.ptr next) := by
    simp only [sH, stateAt]; block_lk
  have heiH : lookupName sH.env "%ei" = some (.ptr (next + (Ty.double).sizeBytes)) := by
    simp only [sH, stateAt]; block_lk
  have hltH : lookupName sH.env "%littrue" = some (.ptr lt) := by
    simp only [sH, stateAt]; block_lk
  have hlfH : lookupName sH.env "%litfalse" = some (.ptr lf) := by
    simp only [sH, stateAt]; block_lk
  have hlnH : lookupName sH.env "%litnull" = some (.ptr ln) := by
    simp only [sH, stateAt]; block_lk
  have hmemH : sH.mem = mem := by simp only [sH, stateAt]; exact hmem
  have hnextH : sH.next = next + (Ty.double).sizeBytes + (Ty.int 64).sizeBytes := by
    simp only [sH, stateAt]; exact hnextP
  have hinv : gapScanInv win P.ip P.b pos c next lt lf ln mem P.ip sH pos :=
    gapScanInv_seed hposlt P.hip63 rfl rfl hmemH hnextH h0H hcH htH hcondH hdH heiH hltH hlfH hlnH
  obtain ⟨e, j, hj, hexitBlock, hexit, hrun2⟩ :=
    gapScanLoop_run_from (calls := stage2Calls stage2SubCalls) P.hbytes P.hlen P.ip sH pos hinv
  rcases hexit with
      ⟨leaf, cc, hpcW, hpreW, hmemW, hnextE, hincW, h6W, hcondW, h0W, hcW, htW, hdW, heiW,
        hltW, hlfW, hlnW, heeW, hltWW⟩ | ⟨hpcC, hmemC, hEeC⟩
  · obtain ⟨leaf', cc', hpre', hee', hlt', hstep2⟩ :=
      gap_scan_whileEnd_continue (bytes := win) (b := P.b) (cur := c) (next := next)
        (lt := lt) (lf := lf) (ln := ln) (ip := P.ip) (p := pos) (mem := mem) hpcW
        (Or.inl ⟨leaf, cc, hpcW, hpreW, hmemW, hnextE, hincW, h6W, hcondW, h0W, hcW, htW, hdW,
          heiW, hltW, hlfW, hlnW, heeW, hltWW⟩) P.hip64
    let sF : State := stateAt
      (("%cmp6", .int 1 (evalICmp .eq (BitVec.ofNat 64 cc')
          (BitVec.ofNat 64 P.ip))) ::
        ("%ee.0.lcssa", .int 64 (BitVec.ofNat 64 cc')) :: e.env)
      { e with pc := "if.end", pre := some "while.end" }
    have hpcF : sF.pc = "if.end" := rfl
    have hpreF : sF.pre = some "while.end" := rfl
    have hmemF : sF.mem = mem := by simp only [sF, stateAt]; exact hmemW
    have hnextF : sF.next = next + (Ty.double).sizeBytes + (Ty.int 64).sizeBytes := by
      simp only [sF, stateAt]; exact hnextE
    have h0F : lookupName sF.env "%0" = some (.ptr P.b) := by
      simp only [sF, stateAt]; block_lk
    have hcF : lookupName sF.env "%c" = some (.ptr c) := by
      simp only [sF, stateAt]; block_lk
    have htF : lookupName sF.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 pos)) := by
      simp only [sF, stateAt]; block_lk
    have hcondF : lookupName sF.env "%cond" = some (.int 64 (BitVec.ofNat 64 P.ip)) := by
      simp only [sF, stateAt]; block_lk
    have hdF : lookupName sF.env "%d" = some (.ptr next) := by
      simp only [sF, stateAt]; block_lk
    have heiF : lookupName sF.env "%ei" =
        some (.ptr (next + (Ty.double).sizeBytes)) := by
      simp only [sF, stateAt]; block_lk
    have hltF : lookupName sF.env "%littrue" = some (.ptr lt) := by
      simp only [sF, stateAt]; block_lk
    have hlfF : lookupName sF.env "%litfalse" = some (.ptr lf) := by
      simp only [sF, stateAt]; block_lk
    have hlnF : lookupName sF.env "%litnull" = some (.ptr ln) := by
      simp only [sF, stateAt]; block_lk
    have heeF : lookupName sF.env "%ee.0.lcssa" =
        some (.int 64 (BitVec.ofNat 64 (gapEe win P.ip pos))) := by
      simp only [sF, stateAt]
      rw [← hee']
      block_lk
    refine ⟨sF, j, by omega, hpcF, hpreF, hmemF, hnextF, h0F, hcF, htF, hcondF, hdF,
      heiF, hltF, hlfF, hlnF, heeF, ?_⟩
    intro k
    rw [show 4 + j + k = 2 + (1 + (j + (1 + k))) from by omega,
      hrun (1 + (j + (1 + k))), runFuel_jump_prefix hstep (j + (1 + k)),
      hrun2 (1 + k), runFuel_jump_prefix hstep2 k]
  · exact absurd hEeC hne


/-- The same bridge through `cond.false`. -/
theorem odGap_run_to_ifEnd_false {mem : Mem} {next c pos lt lf ln : Nat} {win : List UInt8}
    (P : OdGapPrep mem next c pos lt lf ln win)
    (hnk : ¬ P.k < P.nix) (hposlt : pos < P.ip)
    (hne : gapEe win P.ip pos ≠ P.ip) :
    ∃ (s : State) (j : Nat), j ≤ (P.ip + 1) * 5 + 4 ∧
      s.pc = "if.end" ∧ s.pre = some "while.end" ∧ s.mem = mem ∧
      s.next = next + (Ty.double).sizeBytes + (Ty.int 64).sizeBytes ∧
      lookupName s.env "%0" = some (.ptr P.b) ∧
      lookupName s.env "%c" = some (.ptr c) ∧
      lookupName s.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 pos)) ∧
      lookupName s.env "%cond" = some (.int 64 (BitVec.ofNat 64 P.ip)) ∧
      lookupName s.env "%d" = some (.ptr next) ∧
      lookupName s.env "%ei" = some (.ptr (next + (Ty.double).sizeBytes)) ∧
      lookupName s.env "%littrue" = some (.ptr lt) ∧
      lookupName s.env "%litfalse" = some (.ptr lf) ∧
      lookupName s.env "%litnull" = some (.ptr ln) ∧
      lookupName s.env "%ee.0.lcssa" =
        some (.int 64 (BitVec.ofNat 64 (gapEe win P.ip pos))) ∧
      (∀ k, runFuel (stage2Calls stage2SubCalls) (4 + j + k) odGapRecoverBody
        (EntryState odGapRecoverBody (odGapEntryArgs c pos lt lf ln) mem next) =
        runFuel (stage2Calls stage2SubCalls) k odGapRecoverBody s) := by
  obtain ⟨s, hrun, hpc, hpre, hmem, hnextP, h0, hc, ht, hd, hei, hlt, hlf, hln, h5⟩ :=
    gapPrefix_false P hnk
  let sH : State := stateAt (("%cmp310", .int 1 (evalICmp .ult (BitVec.ofNat 64 pos)
      (BitVec.ofNat 64 P.ip))) :: ("%cond", .int 64 (BitVec.ofNat 64 P.ip)) :: s.env)
    { s with pc := "land.rhs", pre := some "cond.end" }
  have hstep : step (stage2Calls stage2SubCalls) odGapRecoverBody s = .jump sH :=
    gapCondEnd_landRhs_false (s := s) hpc hpre ht h5 P.hip64 hposlt
  have h0H : lookupName sH.env "%0" = some (.ptr P.b) := by
    simp only [sH, stateAt]; block_lk
  have hcH : lookupName sH.env "%c" = some (.ptr c) := by
    simp only [sH, stateAt]; block_lk
  have htH : lookupName sH.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 pos)) := by
    simp only [sH, stateAt]; block_lk
  have hcondH : lookupName sH.env "%cond" = some (.int 64 (BitVec.ofNat 64 P.ip)) := by
    simp only [sH, stateAt]; block_lk
  have hdH : lookupName sH.env "%d" = some (.ptr next) := by
    simp only [sH, stateAt]; block_lk
  have heiH : lookupName sH.env "%ei" = some (.ptr (next + (Ty.double).sizeBytes)) := by
    simp only [sH, stateAt]; block_lk
  have hltH : lookupName sH.env "%littrue" = some (.ptr lt) := by
    simp only [sH, stateAt]; block_lk
  have hlfH : lookupName sH.env "%litfalse" = some (.ptr lf) := by
    simp only [sH, stateAt]; block_lk
  have hlnH : lookupName sH.env "%litnull" = some (.ptr ln) := by
    simp only [sH, stateAt]; block_lk
  have hmemH : sH.mem = mem := by simp only [sH, stateAt]; exact hmem
  have hnextH : sH.next = next + (Ty.double).sizeBytes + (Ty.int 64).sizeBytes := by
    simp only [sH, stateAt]; exact hnextP
  have hinv : gapScanInv win P.ip P.b pos c next lt lf ln mem P.ip sH pos :=
    gapScanInv_seed hposlt P.hip63 rfl rfl hmemH hnextH h0H hcH htH hcondH hdH heiH hltH hlfH hlnH
  obtain ⟨e, j, hj, hexitBlock, hexit, hrun2⟩ :=
    gapScanLoop_run_from (calls := stage2Calls stage2SubCalls) P.hbytes P.hlen P.ip sH pos hinv
  rcases hexit with
      ⟨leaf, cc, hpcW, hpreW, hmemW, hnextE, hincW, h6W, hcondW, h0W, hcW, htW, hdW, heiW,
        hltW, hlfW, hlnW, heeW, hltWW⟩ | ⟨hpcC, hmemC, hEeC⟩
  · obtain ⟨leaf', cc', hpre', hee', hlt', hstep2⟩ :=
      gap_scan_whileEnd_continue (bytes := win) (b := P.b) (cur := c) (next := next)
        (lt := lt) (lf := lf) (ln := ln) (ip := P.ip) (p := pos) (mem := mem) hpcW
        (Or.inl ⟨leaf, cc, hpcW, hpreW, hmemW, hnextE, hincW, h6W, hcondW, h0W, hcW, htW, hdW,
          heiW, hltW, hlfW, hlnW, heeW, hltWW⟩) P.hip64
    let sF : State := stateAt
      (("%cmp6", .int 1 (evalICmp .eq (BitVec.ofNat 64 cc')
          (BitVec.ofNat 64 P.ip))) ::
        ("%ee.0.lcssa", .int 64 (BitVec.ofNat 64 cc')) :: e.env)
      { e with pc := "if.end", pre := some "while.end" }
    have hpcF : sF.pc = "if.end" := rfl
    have hpreF : sF.pre = some "while.end" := rfl
    have hmemF : sF.mem = mem := by simp only [sF, stateAt]; exact hmemW
    have hnextF : sF.next = next + (Ty.double).sizeBytes + (Ty.int 64).sizeBytes := by
      simp only [sF, stateAt]; exact hnextE
    have h0F : lookupName sF.env "%0" = some (.ptr P.b) := by
      simp only [sF, stateAt]; block_lk
    have hcF : lookupName sF.env "%c" = some (.ptr c) := by
      simp only [sF, stateAt]; block_lk
    have htF : lookupName sF.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 pos)) := by
      simp only [sF, stateAt]; block_lk
    have hcondF : lookupName sF.env "%cond" = some (.int 64 (BitVec.ofNat 64 P.ip)) := by
      simp only [sF, stateAt]; block_lk
    have hdF : lookupName sF.env "%d" = some (.ptr next) := by
      simp only [sF, stateAt]; block_lk
    have heiF : lookupName sF.env "%ei" =
        some (.ptr (next + (Ty.double).sizeBytes)) := by
      simp only [sF, stateAt]; block_lk
    have hltF : lookupName sF.env "%littrue" = some (.ptr lt) := by
      simp only [sF, stateAt]; block_lk
    have hlfF : lookupName sF.env "%litfalse" = some (.ptr lf) := by
      simp only [sF, stateAt]; block_lk
    have hlnF : lookupName sF.env "%litnull" = some (.ptr ln) := by
      simp only [sF, stateAt]; block_lk
    have heeF : lookupName sF.env "%ee.0.lcssa" =
        some (.int 64 (BitVec.ofNat 64 (gapEe win P.ip pos))) := by
      simp only [sF, stateAt]
      rw [← hee']
      block_lk
    refine ⟨sF, j, by omega, hpcF, hpreF, hmemF, hnextF, h0F, hcF, htF, hcondF, hdF,
      heiF, hltF, hlfF, hlnF, heeF, ?_⟩
    intro k
    rw [show 4 + j + k = 2 + (1 + (j + (1 + k))) from by omega,
      hrun (1 + (j + (1 + k))), runFuel_jump_prefix hstep (j + (1 + k)),
      hrun2 (1 + k), runFuel_jump_prefix hstep2 k]
  · exact absurd hEeC hne

/-! ### Axiom footprints -/

#print axioms odGap_run_to_ifEnd_true
#print axioms odGap_run_to_ifEnd_false

end LeanLLVM.Refinement
