/-
`od_gap_recover`'s literal unit, as the model's write.

`JsonStage2HelperIROdGapLiteral` proves the compare loop's run to its exit word
and the exit's continuations; `JsonStage2HelperIROdGapSecondScan` proves the
second scan from `if.end67`.  This module composes them into the two outcomes the
model's `gapLiteralWrite` names: a refusal at `pos + i` with tag 2 when
`litCheck` finds a position, or the extra-token refusal at `gapS2` with tag 4
when it does not.

The statements are the model's two branches.  The loop's compare bound is
`min n ln` (`hm`), the window's total length is `ip` (`hblen`), and the literal's
own length and width are `ln` (`hlitLen`, `hln64`).  The empty token takes the
`if.then57` edge from `for.end.i`, whose `phi` reads `%cond.i` (zero at length
zero), so that cell is a premise of the empty outcome.
-/
import LeanLLVM.Refinement.JsonStage2HelperIROdGapContract

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval

/-! ### The second scan to `cleanup82`

`gapWs_secondScan_run` completes through the return `void`; the outcome contract
stops at the state `cleanup82` holds, whose memory is the record.  This is the
same composition — `if.end67`'s edge, the scan's `BoundLoop`, `while.end78`'s
three stores — read as a prefix. -/
private theorem gapWs_toCleanup {calls : Calls} {mem : Mem} {bytes : List UInt8}
    {ip b ee c e : Nat} {s : State}
    (hpc : s.pc = "if.end67") (hmem : s.mem = mem)
    (hb : lookupName s.env "%0" = some (.ptr b))
    (hcur : lookupName s.env "%c" = some (.ptr c))
    (hee : lookupName s.env "%ee.0.lcssa" = some (.int 64 (BitVec.ofNat 64 ee)))
    (hcond : lookupName s.env "%cond" = some (.int 64 (BitVec.ofNat 64 ip)))
    (he : readBytes mem (c + odGapCurE) 8 = some (natToBytes e 8)) (he64 : e < 2 ^ 64)
    (hbytes : gapBytesAt mem bytes b ip) (hblen : bytes.length = ip)
    (heele : ee ≤ ip) (hiplt : ip < 2 ^ 63) :
    ∃ (s' : State) (j : Nat), s'.pc = "cleanup82" ∧ j ≤ 1 + (ip + 1) * 5 + 1 ∧
      s'.mem = stage2ErrSetMsg mem e (gapS2 bytes ip ee) 4 ∧
      ∀ k, runFuel calls (j + k) odGapRecoverBody s = runFuel calls k odGapRecoverBody s' := by
  by_cases hlt : ee < ip
  · -- the head is entered
    have hbit : evalICmp .ult (BitVec.ofNat 64 ee) (BitVec.ofNat 64 ip) = 1#1 :=
      gap_ult_one (by omega) (by omega) hlt
    let s1 : State := stateAt
      (("%cmp6919", .int 1 (evalICmp .ult (BitVec.ofNat 64 ee)
        (BitVec.ofNat 64 ip))) :: s.env)
      { s with pc := "land.rhs71", pre := some "if.end67" }
    have hstep1 : step calls odGapRecoverBody s = .jump s1 := by
      have hh := gapWs_step_ifEnd67 (calls := calls) (env := s.env) (s := s)
        (ee := ee) (ip := ip) hpc hee hcond
      rw [if_pos hbit] at hh
      have hst : stateAt s.env s = s := rfl
      simpa only [hst, s1] using hh
    have hseed : gapWsScanInv bytes ip b ee c mem ip s1 ee := by
      refine ⟨rfl, ?_, ?_, ?_, ?_, Or.inl ⟨rfl, ?_⟩, le_rfl, hlt, hiplt, by omega,
        by simp [gapWsRun]⟩
      · simp only [s1, stateAt]; exact hmem
      · simp only [s1, stateAt]; block_lk
      · simp only [s1, stateAt]; block_lk
      · simp only [s1, stateAt]; block_lk
      · simp only [s1, stateAt]; block_lk
    obtain ⟨e0, jl, hjl, hpcE, hexitE, hrunLoop⟩ :=
      gapWsScanLoop_run_from (calls := calls) hbytes hblen ip s1 ee hseed
    obtain ⟨hpc0, hmem0, hcur0, leaf, cell, hpre0, hinc0, hcell0⟩ := hexitE
    have hs2 : gapS2 bytes ip ee < 2 ^ 64 := by
      have hle := gapWsS2_le (bytes := bytes) (ip := ip) (ee := ee) heele
      omega
    have he0 : readBytes e0.mem (c + odGapCurE) 8 = some (natToBytes e 8) := by
      rw [hmem0]; exact he
    let s' : State := stateAt
      (("%msg2.i138", .ptr (e + 16)) :: ("%off1.i137", .ptr (e + 8)) ::
        ("%16", .ptr e) :: ("%e79", .ptr (c + odGapCurE)) ::
        ("%s2.0.lcssa", .int 64 (BitVec.ofNat 64 (gapS2 bytes ip ee))) :: e0.env)
      { e0 with pc := "cleanup82", pre := some "while.end78", mem := stage2ErrSetMsg e0.mem e (gapS2 bytes ip ee) 4 }
    have hwhile : step calls odGapRecoverBody e0 = .jump s' := by
      have hh := gapWs_step_whileEnd78 (calls := calls) (env := e0.env) (s := e0)
        (p := leaf) (cell := cell) (c := c) (s2 := gapS2 bytes ip ee) (e := e)
        hpc0 hpre0 hcur0 hinc0 hcell0 he0 he64 hs2
      have hst : stateAt e0.env e0 = e0 := rfl
      simpa only [hst, s', odGapCurE] using hh
    refine ⟨s', 1 + jl + 1, by simp only [s', stateAt], by omega, ?_, ?_⟩
    · simp only [s', stateAt, hmem0]
    · intro k
      rw [show 1 + jl + 1 + k = 1 + (jl + (1 + k)) from by omega,
        runFuel_jump_prefix hstep1 (jl + (1 + k)), hrunLoop (1 + k),
        runFuel_jump_prefix hwhile k]
  · -- the first loop already reached `ip`
    have heq : ee = ip := by omega
    have hbit : evalICmp .ult (BitVec.ofNat 64 ee) (BitVec.ofNat 64 ip) = 0#1 := by
      rw [heq]
      exact gap_ult_self _
    let e0 : State := stateAt
      (("%cmp6919", .int 1 (evalICmp .ult (BitVec.ofNat 64 ee)
        (BitVec.ofNat 64 ip))) :: s.env)
      { s with pc := "while.end78", pre := some "if.end67" }
    have hstep1 : step calls odGapRecoverBody s = .jump e0 := by
      have hh := gapWs_step_ifEnd67 (calls := calls) (env := s.env) (s := s)
        (ee := ee) (ip := ip) hpc hee hcond
      rw [if_neg (by rw [hbit]; decide)] at hh
      have hst : stateAt s.env s = s := rfl
      simpa only [hst, e0] using hh
    have hmem0 : e0.mem = mem := by
      simp only [e0, stateAt]; exact hmem
    have hS2 : gapS2 bytes ip ee = ee := by
      unfold gapS2
      rw [show ip - ee = 0 from by omega]
      simp [gapWsRun]
    have hexit : gapWsScanExit bytes ip ee c mem e0 := by
      refine ⟨rfl, hmem0, ?_, ?_⟩
      · simp only [e0, stateAt]; block_lk
      · refine ⟨"if.end67", "%ee.0.lcssa", rfl, by decide, ?_⟩
        rw [hS2]
        simp only [e0, stateAt]; block_lk
    obtain ⟨hpc0, hmem0', hcur0, leaf, cell, hpre0, hinc0, hcell0⟩ := hexit
    have hs2 : gapS2 bytes ip ee < 2 ^ 64 := by
      have hle := gapWsS2_le (bytes := bytes) (ip := ip) (ee := ee) heele
      omega
    have he0 : readBytes e0.mem (c + odGapCurE) 8 = some (natToBytes e 8) := by
      rw [hmem0]; exact he
    let s' : State := stateAt
      (("%msg2.i138", .ptr (e + 16)) :: ("%off1.i137", .ptr (e + 8)) ::
        ("%16", .ptr e) :: ("%e79", .ptr (c + odGapCurE)) ::
        ("%s2.0.lcssa", .int 64 (BitVec.ofNat 64 (gapS2 bytes ip ee))) :: e0.env)
      { e0 with pc := "cleanup82", pre := some "while.end78", mem := stage2ErrSetMsg e0.mem e (gapS2 bytes ip ee) 4 }
    have hwhile : step calls odGapRecoverBody e0 = .jump s' := by
      have hh := gapWs_step_whileEnd78 (calls := calls) (env := e0.env) (s := e0)
        (p := leaf) (cell := cell) (c := c) (s2 := gapS2 bytes ip ee) (e := e)
        hpc0 hpre0 hcur0 hinc0 hcell0 he0 he64 hs2
      have hst : stateAt e0.env e0 = e0 := rfl
      simpa only [hst, s', odGapCurE] using hh
    refine ⟨s', 1 + 1, by simp only [s', stateAt], by omega, ?_, ?_⟩
    · simp only [s', stateAt, hmem0]
    · intro k
      rw [show 1 + 1 + k = 1 + (1 + k) from by omega,
        runFuel_jump_prefix hstep1 (1 + k), runFuel_jump_prefix hwhile k]

/-! ### The two outcomes -/

/-- **The loop's outcome.**  From the compare head with the whole bound as budget,
the run reaches a `cleanup82` state whose memory is the model's write: the tag-2
refusal at `t + i` for the `litCheck` position, or the tag-4 extra-token refusal
at `gapS2` when `litCheck` finds none. -/
theorem gapLit_outcome_loop {calls : Calls} {mem : Mem} {bytes litBytes : List UInt8}
    {b ip cur t n ln litBase m r : Nat} {s : State} (hpr : ip < 2 ^ 63)
    (hinv : gapLitInv bytes litBytes b ip cur (b + t) litBase t n ln m mem (m - 1) s 0)
    (hrec : readBytes mem (cur + odGapCurE) 8 = some (natToBytes r 8)) (hr64 : r < 2 ^ 64)
    (hbytes : gapBytesAt mem bytes b ip) (hlt : t + n ≤ ip)
    (hlit : gapBytesAt mem litBytes litBase ln)
    (hn64 : t + n < 2 ^ 64) (hm : m = min n ln)
    (hblen : bytes.length = ip) (hlitLen : litBytes.length = ln) (hln64 : ln < 2 ^ 64) :
    ∃ (s' : State) (j : Nat), s'.pc = "cleanup82" ∧ j ≤ ((m - 1) + 1) * 2 + 3 + (1 + (ip + 1) * 5 + 2) ∧
      ((∃ i, litCheck (gapSegment bytes t (t + n)) litBytes = some i ∧
              s'.mem = stage2ErrSetMsg mem r (t + i) 2)
       ∨ (litCheck (gapSegment bytes t (t + n)) litBytes = none ∧
              s'.mem = stage2ErrSetMsg mem r (gapS2 bytes ip (t + n)) 4)) ∧
      (∀ k, runFuel calls (j + k) odGapRecoverBody s = runFuel calls k odGapRecoverBody s') := by
  have hinv' := hinv
  obtain ⟨hpcI, hmemI, harr, hlit0, hcondiI, hsubI, hln0, ht0, hcurI, h0I,
    hcndI, heeI, hcar, hmn, hml, hcm, hm63, hpfxI, hbud⟩ := hinv
  have hmpos : 0 < m := by omega
  obtain ⟨e, jl, hjl, hblock, hw, hrun_loop⟩ :=
    (gapLitLoop calls bytes litBytes cur (b + t) litBase b t n ln m ip mem r
      hrec hr64 rfl hbytes hlt hlit).run_from (m - 1) s 0 hinv'
  have hjl' : jl ≤ ((m - 1) + 1) * 2 := by simpa [gapLitLoop] using hjl
  have hw' := hw
  obtain ⟨hmemE, hcurE, htE, hcondiE, hsubE, hlnE, h0E, hcndE, heeE, hdisjE, _⟩ := hw
  rcases hblock with hpcE | hpcE
  · -- the loop left at `if.then57`
    rcases hdisjE with
      ⟨c, hpcE57, hpreE, hidxE, hcmE, hpfxE, hneE⟩ |
      ⟨hpcFE, _hpreFE, _hincFE, _hallFE⟩
    · -- a differing byte at `c`
      obtain ⟨e1, j1, hj1, hpc1, hpre1, hmem1, hei1, hadd1, hmsg1, hoff1, hrun1⟩ :=
        gapLit_exitThen57 hpcE57 hpreE hidxE hw' hrec hr64
      have hseg_len : (gapSegment bytes t (t + n)).length = n := by
        rw [odGapSegment_length (pos := t) (ee := t + n) (by omega)
          (by rw [hblen]; exact hlt)]
        omega
      have hca : c < (gapSegment bytes t (t + n)).length := by
        rw [hseg_len]
        omega
      have hcb : c < litBytes.length := by
        rw [hlitLen]
        omega
      have hpre' : ∀ j, j < c →
          (gapSegment bytes t (t + n)).getD j 0 = litBytes.getD j 0 := by
        intro j hj
        rw [odGapSegment_getD (by omega)]
        exact hpfxE j hj
      have hne' : (gapSegment bytes t (t + n)).getD c 0 ≠ litBytes.getD c 0 := by
        rw [odGapSegment_getD (by omega)]
        exact hneE
      have hlitCheck : litCheck (gapSegment bytes t (t + n)) litBytes = some c :=
        odGapLitCheck_of_firstDiff hca hcb hpre' hne'
      have hoff : ((BitVec.ofNat 64 c) + (BitVec.ofNat 64 t)).toNat = t + c := by
        rw [odGap_add_toNat (a := c) (b := t) (by omega)]
        omega
      have hmemEq : gapLitThen57Mem e r (BitVec.ofNat 64 c) (BitVec.ofNat 64 t)
          = stage2ErrSetMsg mem r (t + c) 2 := by
        unfold gapLitThen57Mem stage2ErrSetMsg stage2ErrSet wordBytes
        rw [hmemE, hoff]
      have hmem1' : e1.mem = stage2ErrSetMsg mem r (t + c) 2 := by
        rw [hmem1]; exact hmemEq
      refine ⟨e1, jl + j1, hpc1, by omega, Or.inl ⟨c, hlitCheck, hmem1'⟩, ?_⟩
      exact runFuel_prefix_trans hrun_loop hrun1
    · rw [hpcE] at hpcFE
      exact absurd hpcFE (by decide)
  · -- the loop left at `for.end.i`
    rcases hdisjE with
      ⟨c, hpc57, _hpre57, _hidx57, _hcm57, _hpfx57, _hne57⟩ |
      ⟨hpcFE, hpreFE, hincFE, hallFE⟩
    · rw [hpcE] at hpc57
      exact absurd hpc57 (by decide)
    · rcases bitVec1_eq_zero_or_one
        (evalICmp .eq (BitVec.ofNat 64 n) (BitVec.ofNat 64 ln)) with hbit | hbit
      · -- the lengths differ: the bound exit refuses at `m`
        obtain ⟨e1, j1, hj1, hpc1, hpre1, hmem1, hei1, hadd1, hmsg1, hoff1, hrun1⟩ :=
          gapLit_exitForEndRefuse hpcE hw' hrec hr64 hbit
        have hneq : n ≠ ln := by
          intro h
          have h1 : evalICmp .eq (BitVec.ofNat 64 n) (BitVec.ofNat 64 ln) = 1#1 := by
            rw [h]; exact gapICmpEq_one_iff.mpr rfl
          rw [h1] at hbit
          exact absurd hbit (by decide)
        have hseg_len : (gapSegment bytes t (t + n)).length = n := by
          rw [odGapSegment_length (pos := t) (ee := t + n) (by omega)
            (by rw [hblen]; exact hlt)]
          omega
        have hlitCheck : litCheck (gapSegment bytes t (t + n)) litBytes = some m := by
          rcases lt_or_gt_of_ne hneq with hltn | hgtn
          · have hm_eq : m = n := by rw [hm, Nat.min_eq_left (le_of_lt hltn)]
            have h := odGapLitCheck_of_short (a := gapSegment bytes t (t + n))
              (b := litBytes)
              (by rw [hseg_len, hlitLen]; omega)
              (by intro j hj
                  rw [hseg_len] at hj
                  rw [odGapSegment_getD (by omega)]
                  exact hallFE j (by rw [hm_eq]; exact hj))
            have hlenm : (gapSegment bytes t (t + n)).length = m := by
              rw [hseg_len]; omega
            simpa only [hlenm] using h
          · have hm_eq : m = ln := by rw [hm, Nat.min_eq_right (le_of_lt hgtn)]
            have h := odGapLitCheck_of_long (a := gapSegment bytes t (t + n))
              (b := litBytes)
              (by rw [hlitLen, hseg_len]; omega)
              (by intro j hj
                  rw [hlitLen] at hj
                  rw [odGapSegment_getD (by omega)]
                  exact hallFE j (by rw [hm_eq]; exact hj))
            have hlenm : litBytes.length = m := by rw [hlitLen]; omega
            simpa only [hlenm] using h
        have hoff : ((BitVec.ofNat 64 m) + (BitVec.ofNat 64 t)).toNat = t + m := by
          rw [odGap_add_toNat (a := m) (b := t) (by omega)]
          omega
        have hmemEq : gapLitThen57Mem e r (BitVec.ofNat 64 m) (BitVec.ofNat 64 t)
            = stage2ErrSetMsg mem r (t + m) 2 := by
          unfold gapLitThen57Mem stage2ErrSetMsg stage2ErrSet wordBytes
          rw [hmemE, hoff]
        have hmem1' : e1.mem = stage2ErrSetMsg mem r (t + m) 2 := by
          rw [hmem1]; exact hmemEq
        refine ⟨e1, jl + j1, hpc1, by omega, Or.inl ⟨m, hlitCheck, hmem1'⟩, ?_⟩
        exact runFuel_prefix_trans hrun_loop hrun1
      · -- the lengths agree: the bound exit falls through to the second scan
        have hxeq : BitVec.ofNat 64 n = BitVec.ofNat 64 ln := gapICmpEq_one_iff.mp hbit
        have hnlt : n < 2 ^ 64 := by omega
        have hneq : n = ln := by
          have h := congrArg BitVec.toNat hxeq
          simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnlt,
            Nat.mod_eq_of_lt hln64] using h
        let e' : State := stateAt (gapLitEndEnv e.env (BitVec.ofNat 64 n)
          (BitVec.ofNat 64 ln)) { e with pc := "if.end67", pre := some "for.end.i" }
        have hstepE : step calls odGapRecoverBody e = .jump e' := by
          have hh := gapLit_step_forEnd (calls := calls) (env := e.env) (s := e)
            (nw := BitVec.ofNat 64 n) (lnw := BitVec.ofNat 64 ln) hpcE hsubE hlnE
          have hif : (if evalICmp .eq (BitVec.ofNat 64 n) (BitVec.ofNat 64 ln) = 1
              then "if.end67" else "if.then57") = "if.end67" := by
            rw [hbit]; decide
          rw [hif] at hh
          have hst : stateAt e.env e = e := rfl
          simpa only [hst, e'] using hh
        have hb' : lookupName e'.env "%0" = some (.ptr b) := by
          simp only [e', stateAt, gapLitEndEnv]; block_lk
        have hcur' : lookupName e'.env "%c" = some (.ptr cur) := by
          simp only [e', stateAt, gapLitEndEnv]; block_lk
        have hee' : lookupName e'.env "%ee.0.lcssa" =
            some (.int 64 (BitVec.ofNat 64 (t + n))) := by
          simp only [e', stateAt, gapLitEndEnv]; block_lk
        have hcond' : lookupName e'.env "%cond" =
            some (.int 64 (BitVec.ofNat 64 ip)) := by
          simp only [e', stateAt, gapLitEndEnv]; block_lk
        have hmem' : e'.mem = mem := by simp only [e', stateAt, hmemE]
        obtain ⟨s', j2, hpc2, hj2, hmemS, hrun_scan⟩ :=
          gapWs_toCleanup (calls := calls) (mem := mem) (bytes := bytes)
            (ip := ip) (b := b) (ee := t + n) (c := cur) (e := r) (s := e')
            rfl hmem' hb' hcur' hee' hcond' hrec hr64 hbytes hblen hlt hpr
        have hlitCheck : litCheck (gapSegment bytes t (t + n)) litBytes = none := by
          have hdrop : n ≤ (bytes.drop t).length := by
            rw [List.length_drop, hblen]; omega
          have hlitn : n ≤ litBytes.length := by rw [hlitLen]; omega
          have htake : (bytes.drop t).take n = litBytes.take n :=
            odGap_take_eq hdrop hlitn (by
              intro j hj
              rw [gap_getD_drop_add]
              exact hallFE j (by rw [hm, hneq]; simp; omega))
          have hseg : gapSegment bytes t (t + n) = (bytes.drop t).take n := by
            unfold gapSegment
            rw [show t + n - t = n from by omega]
          rw [hseg, htake, List.take_of_length_le (by rw [hlitLen]; omega)]
          exact odGapLitCheck_eq_none rfl
        refine ⟨s', jl + (1 + j2), hpc2, by omega, Or.inr ⟨hlitCheck, hmemS⟩, ?_⟩
        have hstep2 : ∀ k, runFuel calls (1 + j2 + k) odGapRecoverBody e =
            runFuel calls k odGapRecoverBody s' :=
          runFuel_prefix_trans (fun k => runFuel_jump_prefix hstepE k) hrun_scan
        exact runFuel_prefix_trans hrun_loop hstep2

/-- **The empty token's outcome.**  From `if.then57` on the `for.end.i` edge with
`%cond.i` zero, the run writes the tag-2 record at `t` and reaches `cleanup82` in
one step. -/
theorem gapLit_outcome_empty {calls : Calls} {mem : Mem} {bytes litBytes : List UInt8}
    {b ip cur t n ln litBase m r : Nat} {s : State}
    (hpc : s.pc = "if.then57") (hpre : s.pre = some "for.end.i") (hmem : s.mem = mem)
    (h0 : lookupName s.env "%0" = some (.ptr b)) (hcur : lookupName s.env "%c" = some (.ptr cur))
    (ht : lookupName s.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 t)))
    (hcond : lookupName s.env "%cond" = some (.int 64 (BitVec.ofNat 64 ip)))
    (hee : lookupName s.env "%ee.0.lcssa" = some (.int 64 (BitVec.ofNat 64 (t + n))))
    (hrec : readBytes mem (cur + odGapCurE) 8 = some (natToBytes r 8)) (hr64 : r < 2 ^ 64)
    (hn : n = 0)
    (hcondi : lookupName s.env "%cond.i" = some (.int 64 (BitVec.ofNat 64 0)))
    (ht64 : t < 2 ^ 64) :
    ∃ (s' : State) (j : Nat), s'.pc = "cleanup82" ∧ j ≤ 5 ∧ s'.mem = stage2ErrSetMsg mem r t 2 ∧
      (∀ k, runFuel calls (j + k) odGapRecoverBody s = runFuel calls k odGapRecoverBody s') := by
  have hinc : phiIncoming "for.end.i"
      [("for.end.i", Operand.reg "%cond.i"), ("for.body.i", Operand.reg "%i.029.i")] =
      some (Operand.reg "%cond.i") := by decide
  have hop : evalOperand (stateAt s.env s) (Operand.reg "%cond.i") =
      some (.int 64 (BitVec.ofNat 64 0)) := by
    simp only [evalOperand, stateAt]
    rw [hcondi]
  have hrecs : readBytes s.mem (cur + odGapCurE) 8 = some (natToBytes r 8) := by
    rw [hmem]; exact hrec
  have hstep := gapLit_step_ifThen57 (calls := calls) (env := s.env) (s := s)
    (p := "for.end.i") (cur := cur) (r := r)
    (ew := BitVec.ofNat 64 0) (tw := BitVec.ofNat 64 t) (op := Operand.reg "%cond.i")
    hpc hpre hinc hop hcur hrecs hr64 ht
  let s' : State := stateAt
    (gapLitThen57Env s.env cur r (BitVec.ofNat 64 0) (BitVec.ofNat 64 t))
    (gapLitSet s "cleanup82" "if.then57"
      (gapLitThen57Mem s r (BitVec.ofNat 64 0) (BitVec.ofNat 64 t)))
  have hmemS : s'.mem = stage2ErrSetMsg mem r t 2 := by
    have hoff : ((BitVec.ofNat 64 0) + (BitVec.ofNat 64 t)).toNat = t := by
      rw [odGap_add_toNat (a := 0) (b := t) (by omega)]
      omega
    have hmemEq : gapLitThen57Mem s r (BitVec.ofNat 64 0) (BitVec.ofNat 64 t)
        = stage2ErrSetMsg mem r t 2 := by
      unfold gapLitThen57Mem stage2ErrSetMsg stage2ErrSet wordBytes
      rw [hmem, hoff]
    simp only [s', stateAt, gapLitSet_mem]
    exact hmemEq
  refine ⟨s', 1, by simp only [s', stateAt, gapLitSet], by omega, hmemS, ?_⟩
  intro k
  exact runFuel_jump_prefix hstep k

/-! ### Axiom footprints -/

#print axioms gapLit_outcome_loop
#print axioms gapLit_outcome_empty

end LeanLLVM.Refinement
