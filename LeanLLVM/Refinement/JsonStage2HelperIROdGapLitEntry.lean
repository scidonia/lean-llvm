/-
`od_gap_recover`'s literal dispatch and the compare loop's seed.

`if.else` is the number test's false arm: three signed byte comparisons select a
leaf block, each leaf compares the byte with its literal's first character, and
the three accepted bytes reach `if.end48`.  That block's two `phi`s select the
literal and its width, `%sub54` is the token's length, and the unsigned minimum
of the two is the compare bound.  A zero-length token takes `for.end.i`'s own
branch to `if.then57` without entering the loop; otherwise the block's cells are
exactly the compare loop's invariant at its first visit, which is the seed
`gapLitInv_seed` consumes.

The composition is of the committed units: the three dispatch lemmas,
`gapLit_step_ifEnd48`, `gapLit_step_forEnd` and `gapLitInv_seed`.
-/
import LeanLLVM.Refinement.JsonStage2HelperIROdGapContract

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval (stateAt)

/-! ### `if.end48` and the seed

The two phis, the subtraction, the minimum and the terminator, then the seed at
`for.body.i` or the empty token's edge to `if.then57`.  The literal and its width
are the block's phi values, so the caller names the literal's cell and the width
as a `Nat`; every other cell is the environment's. -/

theorem gapLit_end48_run {calls : Calls} {mem : Mem} {env : Env} {s : State}
    {bytes litBytes : List UInt8}
    {b ip cur t n lt : Nat} {p litName : String} {ln : Nat} {opN : Operand}
    (hpc : s.pc = "if.end48") (hpre : s.pre = some p)
    (hincL : phiIncoming p
      [("if.then37", Operand.reg "%litfalse"), ("if.then42", Operand.reg "%litnull"),
       ("LeafBlock11", Operand.reg "%littrue")] = some (Operand.reg litName))
    (hlit : lookupName env litName = some (.ptr lt))
    (hincN : phiIncoming p
      [("if.then37", Operand.imm (Const.int 64 0x0000000000000005#64)),
       ("if.then42", Operand.imm (Const.int 64 0x0000000000000004#64)),
       ("LeafBlock11", Operand.imm (Const.int 64 0x0000000000000004#64))] = some opN)
    (hopN : evalOperand (stateAt env s) opN = some (.int 64 (BitVec.ofNat 64 ln)))
    (hln : ln = 4 ∨ ln = 5)
    (hee : lookupName env "%ee.0.lcssa" = some (.int 64 (BitVec.ofNat 64 (t + n))))
    (htt : lookupName env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 t)))
    (hcnd : lookupName env "%cond" = some (.int 64 (BitVec.ofNat 64 ip)))
    (h0 : lookupName env "%0" = some (.ptr b))
    (hcur : lookupName env "%c" = some (.ptr cur))
    (harr : lookupName env "%arrayidx9" = some (.ptr (b + t)))
    (hmem : s.mem = mem)
    (hn64 : t + n < 2 ^ 64) :
    ∃ (s' : State) (j : Nat), j ≤ 2 ∧
      (n = 0 →
        s'.pc = "if.then57" ∧ s'.pre = some "for.end.i" ∧ s'.mem = mem ∧
        lookupName s'.env "%0" = some (.ptr b) ∧
        lookupName s'.env "%c" = some (.ptr cur) ∧
        lookupName s'.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 t)) ∧
        lookupName s'.env "%cond.i" = some (.int 64 (BitVec.ofNat 64 0)) ∧
        lookupName s'.env "%cond" = some (.int 64 (BitVec.ofNat 64 ip)) ∧
        lookupName s'.env "%ee.0.lcssa" =
          some (.int 64 (BitVec.ofNat 64 (t + n)))) ∧
      (0 < n →
        gapLitInv bytes litBytes b ip cur (b + t) lt t n ln (min n ln) mem
          (min n ln - 1) s' 0) ∧
      (∀ k, runFuel calls (j + k) odGapRecoverBody (stateAt env s) =
        runFuel calls k odGapRecoverBody s') := by
  have hopL : evalOperand (stateAt env s) (Operand.reg litName) = some (.ptr lt) :=
    BlockEval.evalOperand_reg_of env (stateAt env s) litName (.ptr lt) hlit
  have hstep1 := gapLit_step_ifEnd48 (calls := calls) (env := env) (s := s) (p := p)
    (litBase := lt) (lnw := BitVec.ofNat 64 ln) (ee := BitVec.ofNat 64 (t + n))
    (t := BitVec.ofNat 64 t) (opL := Operand.reg litName) (opN := opN)
    hpc hpre hincL hopL hincN hopN hee htt
  by_cases hn : n = 0
  · -- the empty token: `for.end.i` and its own branch to `if.then57`
    subst n
    have hbit1 : evalICmp .eq (BitVec.ofNat 64 (t + 0)) (BitVec.ofNat 64 t) = 1#1 :=
      gap_eq_one rfl
    have hif1 : (if evalICmp .eq (BitVec.ofNat 64 (t + 0)) (BitVec.ofNat 64 t) = 1
        then "for.end.i" else "for.body.i") = "for.end.i" := by
      rw [hbit1]; decide
    let E : Env :=
      gapLitEnd48Env env lt (BitVec.ofNat 64 ln) (BitVec.ofNat 64 (t + 0)) (BitVec.ofNat 64 t)
    let nw : BitVec 64 := BitVec.ofNat 64 (t + 0) - BitVec.ofNat 64 t
    let sB : State := stateAt E { s with pc := "for.end.i", pre := some "if.end48" }
    let s' : State :=
      stateAt (gapLitEndEnv E nw (BitVec.ofNat 64 ln))
        { s with pc := "if.then57", pre := some "for.end.i" }
    have hstep1' : step calls odGapRecoverBody (stateAt env s) = .jump sB := by
      rw [hif1] at hstep1
      simpa only [sB, E] using hstep1
    have hzb : nw = 0 := by
      have h : nw = BitVec.ofNat 64 (t + 0 - t) :=
        gapSub_eq_ofNat (a := t + 0) (b := t) (by omega) hn64 (by omega)
      rw [h, show t + 0 - t = 0 from by omega]
      rfl
    have hsub1 : lookupName E "%sub54" = some (.int 64 nw) := by
      simp only [E, nw, gapLitEnd48Env]; block_lk
    have hln1 : lookupName E "%ln.0" = some (.int 64 (BitVec.ofNat 64 ln)) := by
      simp only [E, gapLitEnd48Env]; block_lk
    have hstep2 := gapLit_step_forEnd (calls := calls) (env := E)
      (s := { s with pc := "for.end.i", pre := some "if.end48" })
      (nw := nw) (lnw := BitVec.ofNat 64 ln) rfl hsub1 hln1
    have hbit2 : evalICmp .eq nw (BitVec.ofNat 64 ln) = 0#1 := by
      apply gap_eq_zero
      rw [hzb]
      rcases hln with h | h <;> (rw [h]; decide)
    have hif2 : (if evalICmp .eq nw (BitVec.ofNat 64 ln) = 1
        then "if.end67" else "if.then57") = "if.then57" := by
      rw [hbit2]; decide
    have hstep2' : step calls odGapRecoverBody sB = .jump s' := by
      rw [hif2] at hstep2
      simpa only [s', sB, E] using hstep2
    have hcondraw : lookupName E "%cond.i" = some (.int 64
        (if evalICmp .ult nw (BitVec.ofNat 64 ln) = 1 then nw
         else BitVec.ofNat 64 ln)) := by
      simp only [E, nw, gapLitEnd48Env]; block_lk
    have hcondi0 : (if evalICmp .ult nw (BitVec.ofNat 64 ln) = 1 then nw
        else BitVec.ofNat 64 ln) = BitVec.ofNat 64 0 := by
      rw [hzb]
      rcases hln with h | h <;> (rw [h]; decide)
    have hcondi : lookupName (gapLitEndEnv E nw (BitVec.ofNat 64 ln)) "%cond.i" =
        some (.int 64 (BitVec.ofNat 64 0)) := by
      rw [show gapLitEndEnv E nw (BitVec.ofNat 64 ln) =
          ("%cmp11.not.i", .int 1 (evalICmp .eq nw (BitVec.ofNat 64 ln))) :: E from rfl,
        lookupName_cons_ne _ _ (by decide), hcondraw, hcondi0]
    refine ⟨s', 2, by omega, ?_, ?_, ?_⟩
    · intro _
      refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, hcondi, ?_, ?_⟩
      · simp only [s', stateAt]; exact hmem
      · simp only [s', stateAt, gapLitEndEnv, E, gapLitEnd48Env]; block_lk
      · simp only [s', stateAt, gapLitEndEnv, E, gapLitEnd48Env]; block_lk
      · simp only [s', stateAt, gapLitEndEnv, E, gapLitEnd48Env]; block_lk
      · simp only [s', stateAt, gapLitEndEnv, E, gapLitEnd48Env]; block_lk
      · simp only [s', stateAt, gapLitEndEnv, E, gapLitEnd48Env]; block_lk
    · intro hpos; omega
    · intro k
      rw [show 2 + k = 1 + (1 + k) from by omega,
        runFuel_jump_prefix hstep1' (1 + k), runFuel_jump_prefix hstep2' k]
  · -- a non-empty token: the seed at `for.body.i`
    have hpos : 0 < n := by omega
    have hbit1 : evalICmp .eq (BitVec.ofNat 64 (t + n)) (BitVec.ofNat 64 t) = 0#1 := by
      apply gap_eq_zero
      exact gap_ofNat_ne hn64 (by omega) (by omega)
    have hif1 : (if evalICmp .eq (BitVec.ofNat 64 (t + n)) (BitVec.ofNat 64 t) = 1
        then "for.end.i" else "for.body.i") = "for.body.i" := by
      rw [hbit1]; decide
    let E : Env :=
      gapLitEnd48Env env lt (BitVec.ofNat 64 ln) (BitVec.ofNat 64 (t + n)) (BitVec.ofNat 64 t)
    let sA : State := stateAt E { s with pc := "for.body.i", pre := some "if.end48" }
    have hstep1' : step calls odGapRecoverBody (stateAt env s) = .jump sA := by
      rw [hif1] at hstep1
      simpa only [sA, E] using hstep1
    have hsubn : BitVec.ofNat 64 (t + n) - BitVec.ofNat 64 t = BitVec.ofNat 64 n := by
      rw [gapSub_eq_ofNat (a := t + n) (b := t) (by omega) hn64 (by omega)]
      rw [show t + n - t = n from by omega]
    have hsub54 : lookupName E "%sub54" = some (.int 64 (BitVec.ofNat 64 n)) := by
      have hraw : lookupName E "%sub54" =
          some (.int 64 (BitVec.ofNat 64 (t + n) - BitVec.ofNat 64 t)) := by
        simp only [E, gapLitEnd48Env]; block_lk
      rw [hraw, hsubn]
    have hln0 : lookupName E "%ln.0" = some (.int 64 (BitVec.ofNat 64 ln)) := by
      simp only [E, gapLitEnd48Env]; block_lk
    have hcondi : lookupName E "%cond.i" = some (.int 64 (BitVec.ofNat 64 (min n ln))) := by
      have hraw : lookupName E "%cond.i" = some (.int 64
          (if evalICmp .ult (BitVec.ofNat 64 (t + n) - BitVec.ofNat 64 t)
              (BitVec.ofNat 64 ln) = 1
           then BitVec.ofNat 64 (t + n) - BitVec.ofNat 64 t
           else BitVec.ofNat 64 ln)) := by
        simp only [E, gapLitEnd48Env]; block_lk
      rw [hraw, hsubn]
      rw [gapLit_cond_min (a := n) (b := ln) (by omega)
        (by rcases hln with h | h <;> omega)]
    have hlit0 : lookupName E "%lit.0" = some (.ptr lt) := by
      simp only [E, gapLitEnd48Env]; block_lk
    have harrE : lookupName E "%arrayidx9" = some (.ptr (b + t)) := by
      simp only [E, gapLitEnd48Env]; block_lk
    have ht0 : lookupName E "%t.0.val" = some (.int 64 (BitVec.ofNat 64 t)) := by
      simp only [E, gapLitEnd48Env]; block_lk
    have hcurE : lookupName E "%c" = some (.ptr cur) := by
      simp only [E, gapLitEnd48Env]; block_lk
    have h0E : lookupName E "%0" = some (.ptr b) := by
      simp only [E, gapLitEnd48Env]; block_lk
    have hcndE : lookupName E "%cond" = some (.int 64 (BitVec.ofNat 64 ip)) := by
      simp only [E, gapLitEnd48Env]; block_lk
    have heeE : lookupName E "%ee.0.lcssa" =
        some (.int 64 (BitVec.ofNat 64 (t + n))) := by
      simp only [E, gapLitEnd48Env]; block_lk
    have hmemA : sA.mem = mem := by simp only [sA, stateAt]; exact hmem
    have hlnpos : 0 < ln := by rcases hln with h | h <;> (rw [h]; decide)
    have hm : 0 < min n ln := by
      by_cases hle : n ≤ ln
      · rwa [Nat.min_eq_left hle]
      · rw [Nat.min_eq_right (by omega)]; exact hlnpos
    have hm63 : min n ln ≤ 2 ^ 63 := by
      have h := Nat.min_le_right n ln
      rcases hln with h' | h' <;> (rw [h'] at h; omega)
    refine ⟨sA, 1, by omega, ?_, ?_, ?_⟩
    · intro hzero; omega
    · intro _
      exact gapLitInv_seed (bytes := bytes) (litBytes := litBytes) (b := b) (ip := ip)
        (cur := cur) (base := b + t) (litBase := lt) (t := t) (n := n) (ln := ln)
        (m := min n ln) (mem := mem) (s := sA)
        hm rfl rfl hmemA harrE hlit0 hcondi hsub54 hln0 ht0 hcurE h0E hcndE heeE
        (Nat.min_le_left _ _) (Nat.min_le_right _ _) hm63
    · intro k
      exact runFuel_jump_prefix hstep1' k

/-! ### The entry

From `if.else` with an accepted first byte, the dispatch selects the literal,
`if.end48` seeds the loop, and the run reaches either `for.body.i` with the
loop's invariant or `if.then57` on an empty token. -/

theorem gapLit_entry {calls : Calls} {mem : Mem}
    {bytes litBytes : List UInt8}
    {b ip cur t n lt lf lnn : Nat} {ch : BitVec 8} {s0 : State}
    (hpc : s0.pc = "if.else") (hmem : s0.mem = mem)
    (h0 : lookupName s0.env "%0" = some (.ptr b))
    (hcur : lookupName s0.env "%c" = some (.ptr cur))
    (ht : lookupName s0.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 t)))
    (hee : lookupName s0.env "%ee.0.lcssa" = some (.int 64 (BitVec.ofNat 64 (t + n))))
    (hcond : lookupName s0.env "%cond" = some (.int 64 (BitVec.ofNat 64 ip)))
    (h7 : lookupName s0.env "%7" = some (.int 8 ch))
    (hltT : lookupName s0.env "%littrue" = some (.ptr lt))
    (hltF : lookupName s0.env "%litfalse" = some (.ptr lf))
    (hltN : lookupName s0.env "%litnull" = some (.ptr lnn))
    (harr : lookupName s0.env "%arrayidx9" = some (.ptr (b + t)))
    (hch : ch = 0x74 ∨ ch = 0x66 ∨ ch = 0x6E)
    (hn64 : t + n < 2 ^ 64) :
    ∃ (s : State) (j : Nat), j ≤ 12 ∧
      (n = 0 →
        s.pc = "if.then57" ∧ s.pre = some "for.end.i" ∧ s.mem = mem ∧
        lookupName s.env "%0" = some (.ptr b) ∧
        lookupName s.env "%c" = some (.ptr cur) ∧
        lookupName s.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 t)) ∧
        lookupName s.env "%cond.i" = some (.int 64 (BitVec.ofNat 64 0)) ∧
        lookupName s.env "%cond" = some (.int 64 (BitVec.ofNat 64 ip)) ∧
        lookupName s.env "%ee.0.lcssa" =
          some (.int 64 (BitVec.ofNat 64 (t + n)))) ∧
      (0 < n → ∃ (litBase lnw m : Nat), m = min n lnw ∧
        gapLitInv bytes litBytes b ip cur (b + t) litBase t n lnw m mem (m - 1) s 0 ∧
        ((ch = 0x74 ∧ litBase = lt ∧ lnw = 4) ∨
         (ch = 0x66 ∧ litBase = lf ∧ lnw = 5) ∨
         (ch = 0x6E ∧ litBase = lnn ∧ lnw = 4))) ∧
      (∀ k, runFuel calls (j + k) odGapRecoverBody (stateAt s0.env s0) =
        runFuel calls k odGapRecoverBody s) := by
  rcases hch with hch | hch | hch
  · -- `"true"`: `LeafBlock11` in four control steps
    subst ch
    let envD : Env := ("%SwitchLeaf12", .int 1 1#1) :: ("%Pivot14", .int 1 0#1) ::
      ("%Pivot16", .int 1 0#1) :: s0.env
    let s0D : State := { s0 with pc := "if.end48", pre := some "LeafBlock11" }
    have hdisp : ∀ k, runFuel calls (4 + k) odGapRecoverBody (stateAt s0.env s0) =
        runFuel calls k odGapRecoverBody (stateAt envD s0D) :=
      gapLit_dispatch_true (calls := calls) (env := s0.env) (s := s0) hpc h7
    have hlitD : lookupName envD "%littrue" = some (.ptr lt) := by
      simp only [envD]; block_lk
    have harrD : lookupName envD "%arrayidx9" = some (.ptr (b + t)) := by
      simp only [envD]; block_lk
    have heeD : lookupName envD "%ee.0.lcssa" =
        some (.int 64 (BitVec.ofNat 64 (t + n))) := by
      simp only [envD]; block_lk
    have httD : lookupName envD "%t.0.val" = some (.int 64 (BitVec.ofNat 64 t)) := by
      simp only [envD]; block_lk
    have hcndD : lookupName envD "%cond" = some (.int 64 (BitVec.ofNat 64 ip)) := by
      simp only [envD]; block_lk
    have h0D : lookupName envD "%0" = some (.ptr b) := by
      simp only [envD]; block_lk
    have hcurD : lookupName envD "%c" = some (.ptr cur) := by
      simp only [envD]; block_lk
    obtain ⟨s', j, hj, hA, hB, hrun⟩ :=
      gapLit_end48_run (calls := calls) (mem := mem) (env := envD) (s := s0D)
        (bytes := bytes) (litBytes := litBytes) (b := b) (ip := ip) (cur := cur)
        (t := t) (n := n) (lt := lt) (p := "LeafBlock11") (litName := "%littrue")
        (ln := 4) (opN := Operand.imm (Const.int 64 0x0000000000000004#64))
        rfl rfl (by decide) hlitD (by decide) (by rfl) (Or.inl rfl)
        heeD httD hcndD h0D hcurD harrD (by simpa [s0D] using hmem) hn64
    refine ⟨s', 4 + j, by omega, hA, ?_, ?_⟩
    · intro hpos
      exact ⟨lt, 4, min n 4, rfl, hB hpos, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · intro k
      rw [show 4 + j + k = 4 + (j + k) from by omega, hdisp (j + k)]
      exact hrun k
  · -- `"false"`: `if.then37` in four control steps
    subst ch
    let envD : Env := ("%SwitchLeaf8", .int 1 1#1) :: ("%Pivot16", .int 1 1#1) :: s0.env
    let s0D : State := { s0 with pc := "if.end48", pre := some "if.then37" }
    have hdisp : ∀ k, runFuel calls (4 + k) odGapRecoverBody (stateAt s0.env s0) =
        runFuel calls k odGapRecoverBody (stateAt envD s0D) :=
      gapLit_dispatch_false (calls := calls) (env := s0.env) (s := s0) hpc h7
    have hlitD : lookupName envD "%litfalse" = some (.ptr lf) := by
      simp only [envD]; block_lk
    have harrD : lookupName envD "%arrayidx9" = some (.ptr (b + t)) := by
      simp only [envD]; block_lk
    have heeD : lookupName envD "%ee.0.lcssa" =
        some (.int 64 (BitVec.ofNat 64 (t + n))) := by
      simp only [envD]; block_lk
    have httD : lookupName envD "%t.0.val" = some (.int 64 (BitVec.ofNat 64 t)) := by
      simp only [envD]; block_lk
    have hcndD : lookupName envD "%cond" = some (.int 64 (BitVec.ofNat 64 ip)) := by
      simp only [envD]; block_lk
    have h0D : lookupName envD "%0" = some (.ptr b) := by
      simp only [envD]; block_lk
    have hcurD : lookupName envD "%c" = some (.ptr cur) := by
      simp only [envD]; block_lk
    obtain ⟨s', j, hj, hA, hB, hrun⟩ :=
      gapLit_end48_run (calls := calls) (mem := mem) (env := envD) (s := s0D)
        (bytes := bytes) (litBytes := litBytes) (b := b) (ip := ip) (cur := cur)
        (t := t) (n := n) (lt := lf) (p := "if.then37") (litName := "%litfalse")
        (ln := 5) (opN := Operand.imm (Const.int 64 0x0000000000000005#64))
        rfl rfl (by decide) hlitD (by decide) (by rfl) (Or.inr rfl)
        heeD httD hcndD h0D hcurD harrD (by simpa [s0D] using hmem) hn64
    refine ⟨s', 4 + j, by omega, hA, ?_, ?_⟩
    · intro hpos
      exact ⟨lf, 5, min n 5, rfl, hB hpos, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
    · intro k
      rw [show 4 + j + k = 4 + (j + k) from by omega, hdisp (j + k)]
      exact hrun k
  · -- `"null"`: `if.then42` in five control steps
    subst ch
    let envD : Env := ("%SwitchLeaf10", .int 1 1#1) :: ("%Pivot14", .int 1 1#1) ::
      ("%Pivot16", .int 1 0#1) :: s0.env
    let s0D : State := { s0 with pc := "if.end48", pre := some "if.then42" }
    have hdisp : ∀ k, runFuel calls (5 + k) odGapRecoverBody (stateAt s0.env s0) =
        runFuel calls k odGapRecoverBody (stateAt envD s0D) :=
      gapLit_dispatch_null (calls := calls) (env := s0.env) (s := s0) hpc h7
    have hlitD : lookupName envD "%litnull" = some (.ptr lnn) := by
      simp only [envD]; block_lk
    have harrD : lookupName envD "%arrayidx9" = some (.ptr (b + t)) := by
      simp only [envD]; block_lk
    have heeD : lookupName envD "%ee.0.lcssa" =
        some (.int 64 (BitVec.ofNat 64 (t + n))) := by
      simp only [envD]; block_lk
    have httD : lookupName envD "%t.0.val" = some (.int 64 (BitVec.ofNat 64 t)) := by
      simp only [envD]; block_lk
    have hcndD : lookupName envD "%cond" = some (.int 64 (BitVec.ofNat 64 ip)) := by
      simp only [envD]; block_lk
    have h0D : lookupName envD "%0" = some (.ptr b) := by
      simp only [envD]; block_lk
    have hcurD : lookupName envD "%c" = some (.ptr cur) := by
      simp only [envD]; block_lk
    obtain ⟨s', j, hj, hA, hB, hrun⟩ :=
      gapLit_end48_run (calls := calls) (mem := mem) (env := envD) (s := s0D)
        (bytes := bytes) (litBytes := litBytes) (b := b) (ip := ip) (cur := cur)
        (t := t) (n := n) (lt := lnn) (p := "if.then42") (litName := "%litnull")
        (ln := 4) (opN := Operand.imm (Const.int 64 0x0000000000000004#64))
        rfl rfl (by decide) hlitD (by decide) (by rfl) (Or.inl rfl)
        heeD httD hcndD h0D hcurD harrD (by simpa [s0D] using hmem) hn64
    refine ⟨s', 5 + j, by omega, hA, ?_, ?_⟩
    · intro hpos
      exact ⟨lnn, 4, min n 4, rfl, hB hpos, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩
    · intro k
      rw [show 5 + j + k = 5 + (j + k) from by omega, hdisp (j + k)]
      exact hrun k

/-! ### Axiom footprints -/

#print axioms gapLit_entry
#print axioms gapLit_end48_run

end LeanLLVM.Refinement
