/-
`od_gap_recover`'s literal row, the second half: from the state the entry prefix
hands over to the record and the return, and the whole-function contract at
`OdGapPrep` alone.

`JsonStage2HelperIROdGapFinalSplitEntry` proves `odGapFinal_litRow_entry`: from
`if.end` with a literal's first byte, one control step reaches the compare
loop's head, and the run from there reaches either the empty `if.then57` state or
the loop's invariant at index zero, carrying the branch's literal identity
(`(0x74, lt, 4) | (0x66, lf, 5) | (0x6E, ln, 4)`).

This module closes the row at that seam, one lemma per branch the entry hands
over.  The empty state's `litCheck` refuses at `0`, and the loop's run either
refuses at its first differing position or falls through to the second token's
scan; both reach `cleanup82`, where the body returns `void` with the record.  The
model's `gapAfterLoop` names the same two writes, so `odGapFinal_litRow` composes
the entry's fuel identity with the branch outcome, and the assembly's `hLit` is
`odGapFinal_litRow_weak`.
-/
import LeanLLVM.Refinement.JsonStage2HelperIROdGapFinalSplitEntry
import LeanLLVM.Refinement.JsonStage2HelperIROdGapLitOutcome

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR (stage2Calls)
open LeanLLVM.Refinement.BlockEval

/-- The literal the dispatch compares against, by the token's first byte. -/
def gapLitFor (ch : UInt8) : List UInt8 :=
  if ch = 0x74 then gapTrueLit else if ch = 0x66 then gapFalseLit else gapNullLit

/-- The dispatch's literal identity, as the three arms the entry selects. -/
def gapLitBranch (ch : UInt8) (litBase lnw lt lf ln : Nat) : Prop :=
  (ch = 0x74 ∧ litBase = lt ∧ lnw = 4) ∨
    (ch = 0x66 ∧ litBase = lf ∧ lnw = 5) ∨
      (ch = 0x6E ∧ litBase = ln ∧ lnw = 4)

/-- The literal arm's refusal: the model's write at the first differing position. -/
theorem odGapFinal_litRow_model {win : List UInt8} {ip pos ee i : Nat}
    (hch : win.getD pos 0 = 0x74 ∨ win.getD pos 0 = 0x66 ∨ win.getD pos 0 = 0x6E)
    (hnotnum : ¬ (win.getD pos 0 = 0x2D ∨
      (0x30 ≤ win.getD pos 0 ∧ win.getD pos 0 ≤ 0x39)))
    (hcheck : litCheck (gapSegment win pos ee) (gapLitFor (win.getD pos 0)) = some i) :
    gapAfterLoop win ip pos ee = GapWrite.err (pos + i) gapTagLiteral := by
  have hlitT : win.getD pos 0 = 0x74 → gapLitFor (win.getD pos 0) = gapTrueLit := by
    intro h; simp only [gapLitFor, if_pos h]
  have hlitF : win.getD pos 0 = 0x66 → gapLitFor (win.getD pos 0) = gapFalseLit := by
    intro h
    simp only [gapLitFor, if_neg (by rw [h]; decide : ¬ (win.getD pos 0 = 0x74)), if_pos h]
  have hlitN : win.getD pos 0 = 0x6E → gapLitFor (win.getD pos 0) = gapNullLit := by
    intro h
    simp only [gapLitFor, if_neg (by rw [h]; decide : ¬ (win.getD pos 0 = 0x74)),
      if_neg (by rw [h]; decide : ¬ (win.getD pos 0 = 0x66))]
  exact odGapAfterLoop_literal (bytes := win) (lit := gapLitFor (win.getD pos 0))
    (ip := ip) (pos := pos) (ee := ee) (i := i) (ch := win.getD pos 0) rfl hnotnum hch
    hlitT hlitF hlitN hcheck

/-- The literal arm's acceptance: the fall-through to the extra token's write. -/
theorem odGapFinal_litRow_model_accept {win : List UInt8} {ip pos ee : Nat}
    (hch : win.getD pos 0 = 0x74 ∨ win.getD pos 0 = 0x66 ∨ win.getD pos 0 = 0x6E)
    (hnotnum : ¬ (win.getD pos 0 = 0x2D ∨
      (0x30 ≤ win.getD pos 0 ∧ win.getD pos 0 ≤ 0x39)))
    (hcheck : litCheck (gapSegment win pos ee) (gapLitFor (win.getD pos 0)) = none) :
    gapAfterLoop win ip pos ee = GapWrite.err (gapS2 win ip ee) gapTagExtra := by
  have hlitT : win.getD pos 0 = 0x74 → gapLitFor (win.getD pos 0) = gapTrueLit := by
    intro h; simp only [gapLitFor, if_pos h]
  have hlitF : win.getD pos 0 = 0x66 → gapLitFor (win.getD pos 0) = gapFalseLit := by
    intro h
    simp only [gapLitFor, if_neg (by rw [h]; decide : ¬ (win.getD pos 0 = 0x74)), if_pos h]
  have hlitN : win.getD pos 0 = 0x6E → gapLitFor (win.getD pos 0) = gapNullLit := by
    intro h
    simp only [gapLitFor, if_neg (by rw [h]; decide : ¬ (win.getD pos 0 = 0x74)),
      if_neg (by rw [h]; decide : ¬ (win.getD pos 0 = 0x66))]
  have h := odGapAfterLoop_literal_accept (bytes := win)
    (lit := gapLitFor (win.getD pos 0)) (ip := ip) (pos := pos) (ee := ee)
    (ch := win.getD pos 0) rfl hnotnum hch hlitT hlitF hlitN hcheck
  simpa only [gapExtraWrite] using h

/-- The number-arm exclusion the literal first byte carries. -/
theorem odGapFinal_litRow_notNum {ch : UInt8}
    (h : ch = 0x74 ∨ ch = 0x66 ∨ ch = 0x6E) :
    ¬ (ch = 0x2D ∨ (0x30 ≤ ch ∧ ch ≤ 0x39)) := by
  rcases h with h | h | h <;> rw [h] <;> decide

/-- A run that reaches `cleanup82` at the record returns `void` with it. -/
private theorem odGapFinal_cleanup_row {mem : Mem} {e next off tag : Nat} {s s' : State}
    {j : Nat}
    (hpc : s'.pc = "cleanup82") (hmem : s'.mem = stage2ErrSetMsg mem e off tag)
    (hrun : ∀ k, runFuel (stage2Calls stage2SubCalls) (j + k) odGapRecoverBody s =
      runFuel (stage2Calls stage2SubCalls) k odGapRecoverBody s') :
    ∃ (j' : Nat) (m : Mem),
      runFuel (stage2Calls stage2SubCalls) j' odGapRecoverBody s = some (.ret none m) ∧
      readBytes m e 4 = some (wordBytes 4 0) ∧
      readBytes m (e + 8) 8 = some (wordBytes 8 off) ∧
      readBytes m (e + 16) 8 = some (wordBytes 8 tag) ∧
      UnchangedOutside mem m
        [(e, 4), (e + 8, 8), (e + 16, 8),
         (next, (Ty.double).sizeBytes),
         (next + (Ty.double).sizeBytes, (Ty.int 64).sizeBytes)] := by
  have hret : runFuel (stage2Calls stage2SubCalls) 1 odGapRecoverBody s' =
      some (.ret none (stage2ErrSetMsg mem e off tag)) :=
    odGapFinal_cleanup_ret hpc hmem
  obtain ⟨h4, h8, h16, hfr⟩ :=
    odGapFinal_memory_wrote (mem := mem) (e := e) (next := next) (off := off) (tag := tag)
  exact ⟨j + 1, _, by rw [hrun 1]; exact hret, h4, h8, h16, hfr⟩

/-- **The empty token's outcome.**  From the `if.then57` state the entry hands
over, `litCheck` on the empty segment refuses at `0`, so the run reaches
`cleanup82` with the tag-2 record at `pos` and the model names the same write. -/
theorem odGapFinal_litRow_outcome_empty {mem : Mem} {next c pos lt lf ln : Nat}
    {win : List UInt8} (P : OdGapPrep mem next c pos lt lf ln win) {s2 : State}
    (hzero : gapEe win P.ip pos - pos = 0)
    (hpc2 : s2.pc = "if.then57") (hpre2 : s2.pre = some "for.end.i")
    (hmem2 : s2.mem = mem)
    (h0 : lookupName s2.env "%0" = some (.ptr P.b))
    (hc : lookupName s2.env "%c" = some (.ptr c))
    (ht : lookupName s2.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 pos)))
    (hcondi : lookupName s2.env "%cond.i" = some (.int 64 (BitVec.ofNat 64 0)))
    (hcond : lookupName s2.env "%cond" = some (.int 64 (BitVec.ofNat 64 P.ip)))
    (hee2 : lookupName s2.env "%ee.0.lcssa" =
      some (.int 64 (BitVec.ofNat 64 (pos + (gapEe win P.ip pos - pos)))))
    (hch : OdGapLitFirst (win.getD pos 0)) (hnum : ¬ gapNumStart (win.getD pos 0)) :
    ∃ (off tag : Nat),
      gapAfterLoop win P.ip pos (gapEe win P.ip pos) = GapWrite.err off tag ∧
      OdGapRow P s2 off tag := by
  classical
  have hsel : win.getD pos 0 = 0x74 ∨ win.getD pos 0 = 0x66 ∨ win.getD pos 0 = 0x6E :=
    hch
  have hnotnum : ¬ (win.getD pos 0 = 0x2D ∨
      (0x30 ≤ win.getD pos 0 ∧ win.getD pos 0 ≤ 0x39)) := by
    simpa only [gapNumStart] using hnum
  have hlitne : gapLitFor (win.getD pos 0) ≠ [] := by
    rcases hsel with h | h | h
    · rw [show gapLitFor (win.getD pos 0) = gapTrueLit by
        simp only [gapLitFor, if_pos h]]
      exact (by decide : gapTrueLit ≠ [])
    · rw [show gapLitFor (win.getD pos 0) = gapFalseLit by
        simp only [gapLitFor, if_neg (by rw [h]; decide : ¬ (win.getD pos 0 = 0x74)),
          if_pos h]]
      exact (by decide : gapFalseLit ≠ [])
    · rw [show gapLitFor (win.getD pos 0) = gapNullLit by
        simp only [gapLitFor, if_neg (by rw [h]; decide : ¬ (win.getD pos 0 = 0x74)),
          if_neg (by rw [h]; decide : ¬ (win.getD pos 0 = 0x66))]]
      exact (by decide : gapNullLit ≠ [])
  obtain ⟨s', j, hpc', _hj, hmem', hrunE⟩ :=
    gapLit_outcome_empty (calls := stage2Calls stage2SubCalls) (mem := mem)
      (bytes := win) (litBytes := gapLitFor (win.getD pos 0)) (b := P.b)
      (ip := P.ip) (cur := c) (t := pos) (n := 0) (ln := 0) (litBase := 0) (m := 0)
      (r := P.e) (s := s2)
      hpc2 hpre2 hmem2 h0 hc ht hcond (by simpa [hzero] using hee2) P.he P.he64
      rfl hcondi (by have h1 := P.hposip; have h2 := P.hip63; omega)
  have hseg : gapSegment win pos (gapEe win P.ip pos) = [] := by
    unfold gapSegment
    have hz : gapEe win P.ip pos = pos := by
      have := odGapFinal_gapEe_ge win P.ip pos
      omega
    rw [hz, Nat.sub_self, List.take_zero]
  have hcheck : litCheck (gapSegment win pos (gapEe win P.ip pos))
      (gapLitFor (win.getD pos 0)) = some 0 := by
    rw [hseg]; exact odGapLitCheck_nil_left hlitne
  have hA : gapAfterLoop win P.ip pos (gapEe win P.ip pos) =
      GapWrite.err pos gapTagLiteral := by
    have h := odGapFinal_litRow_model (ip := P.ip) (ee := gapEe win P.ip pos)
      (i := 0) hsel hnotnum hcheck
    simpa using h
  exact ⟨pos, gapTagLiteral, hA,
    odGapFinal_cleanup_row (mem := mem) (e := P.e) (next := next)
      (off := pos) (tag := 2) hpc' hmem' (fun k => by simpa using hrunE k)⟩

/-- **The compare loop's outcome.**  From the loop's invariant at index zero with
the branch's literal identity, the run reaches `cleanup82` with the tag-2 record
at `litCheck`'s first differing position, or the tag-4 record at `gapS2` when
there is none; the model names the same write in both arms. -/
theorem odGapFinal_litRow_outcome_loop {mem : Mem} {next c pos lt lf ln : Nat}
    {win : List UInt8} (P : OdGapPrep mem next c pos lt lf ln win) {s2 : State}
    {litBase lnw m : Nat}
    (hm : m = min (gapEe win P.ip pos - pos) lnw)
    (hinv : gapLitInv win (gapLitFor (win.getD pos 0)) P.b P.ip c (P.b + pos) litBase pos
      (gapEe win P.ip pos - pos) lnw m mem (m - 1) s2 0)
    (hid : gapLitBranch (win.getD pos 0) litBase lnw lt lf ln)
    (hch : OdGapLitFirst (win.getD pos 0)) (hnum : ¬ gapNumStart (win.getD pos 0)) :
    ∃ (off tag : Nat),
      gapAfterLoop win P.ip pos (gapEe win P.ip pos) = GapWrite.err off tag ∧
      OdGapRow P s2 off tag := by
  classical
  have hsel : win.getD pos 0 = 0x74 ∨ win.getD pos 0 = 0x66 ∨ win.getD pos 0 = 0x6E :=
    hch
  have hnotnum : ¬ (win.getD pos 0 = 0x2D ∨
      (0x30 ≤ win.getD pos 0 ∧ win.getD pos 0 ≤ 0x39)) := by
    simpa only [gapNumStart] using hnum
  have hge : pos ≤ gapEe win P.ip pos := odGapFinal_gapEe_ge win P.ip pos
  have hle : gapEe win P.ip pos ≤ P.ip := odGapFinal_gapEe_le P.hposip
  have hlitForT : win.getD pos 0 = 0x74 → gapLitFor (win.getD pos 0) = gapTrueLit := by
    intro h; simp only [gapLitFor, if_pos h]
  have hlitForF : win.getD pos 0 = 0x66 → gapLitFor (win.getD pos 0) = gapFalseLit := by
    intro h
    simp only [gapLitFor, if_neg (by rw [h]; decide : ¬ (win.getD pos 0 = 0x74)), if_pos h]
  have hlitForN : win.getD pos 0 = 0x6E → gapLitFor (win.getD pos 0) = gapNullLit := by
    intro h
    simp only [gapLitFor, if_neg (by rw [h]; decide : ¬ (win.getD pos 0 = 0x74)),
      if_neg (by rw [h]; decide : ¬ (win.getD pos 0 = 0x66))]
  have hlit : gapBytesAt mem (gapLitFor (win.getD pos 0)) litBase lnw := by
    rcases hid with ⟨hb, a, b⟩ | ⟨hb, a, b⟩ | ⟨hb, a, b⟩
    · rw [hlitForT hb, a, b]; exact gapBytesAt_of_readBytes P.hlt
    · rw [hlitForF hb, a, b]; exact gapBytesAt_of_readBytes P.hlf
    · rw [hlitForN hb, a, b]; exact gapBytesAt_of_readBytes P.hln
  have hlitLen : (gapLitFor (win.getD pos 0)).length = lnw := by
    rcases hid with ⟨hb, a, b⟩ | ⟨hb, a, b⟩ | ⟨hb, a, b⟩
    · rw [hlitForT hb, b]; exact (by decide : gapTrueLit.length = 4)
    · rw [hlitForF hb, b]; exact (by decide : gapFalseLit.length = 5)
    · rw [hlitForN hb, b]; exact (by decide : gapNullLit.length = 4)
  have hln64 : lnw < 2 ^ 64 := by
    have hcases : lnw = 4 ∨ lnw = 5 ∨ lnw = 4 := by
      rcases hid with ⟨_, _, b⟩ | ⟨_, _, b⟩ | ⟨_, _, b⟩
      · exact Or.inl b
      · exact Or.inr (Or.inl b)
      · exact Or.inr (Or.inr b)
    rcases hcases with h | h | h <;> omega
  have hltn : pos + (gapEe win P.ip pos - pos) ≤ P.ip := by omega
  have hn64 : pos + (gapEe win P.ip pos - pos) < 2 ^ 64 := by
    have hip64 := P.hip64
    omega
  obtain ⟨s', j, hpc', _hj, hout, hrunL⟩ :=
    gapLit_outcome_loop (calls := stage2Calls stage2SubCalls) (mem := mem)
      (bytes := win) (litBytes := gapLitFor (win.getD pos 0)) (b := P.b)
      (ip := P.ip) (cur := c) (t := pos) (n := gapEe win P.ip pos - pos)
      (ln := lnw) (litBase := litBase) (m := m) (r := P.e) (s := s2)
      P.hip63 hinv P.he P.he64 P.hbytes hltn hlit hn64 hm P.hlen hlitLen hln64
  have hposn : pos + (gapEe win P.ip pos - pos) = gapEe win P.ip pos :=
    Nat.add_sub_cancel' hge
  rcases hout with ⟨i, hcheck, hmem'⟩ | ⟨hcheck, hmem'⟩
  · have hcheck' : litCheck (gapSegment win pos (gapEe win P.ip pos))
        (gapLitFor (win.getD pos 0)) = some i := by
      rw [← hposn]; exact hcheck
    have hA := odGapFinal_litRow_model (ip := P.ip) (ee := gapEe win P.ip pos)
      (i := i) hsel hnotnum hcheck'
    have hmm : s'.mem = stage2ErrSetMsg mem P.e (pos + i) 2 := hmem'
    exact ⟨pos + i, gapTagLiteral, hA,
      odGapFinal_cleanup_row (mem := mem) (e := P.e) (next := next)
        (off := pos + i) (tag := 2) hpc' hmm (fun k => hrunL k)⟩
  · have hcheck' : litCheck (gapSegment win pos (gapEe win P.ip pos))
        (gapLitFor (win.getD pos 0)) = none := by
      rw [← hposn]; exact hcheck
    have hA := odGapFinal_litRow_model_accept (ip := P.ip) (ee := gapEe win P.ip pos)
      hsel hnotnum hcheck'
    have hmm : s'.mem = stage2ErrSetMsg mem P.e (gapS2 win P.ip (gapEe win P.ip pos)) 4 := by
      rw [hmem', hposn]
    exact ⟨gapS2 win P.ip (gapEe win P.ip pos), gapTagExtra, hA,
      odGapFinal_cleanup_row (mem := mem) (e := P.e) (next := next)
        (off := gapS2 win P.ip (gapEe win P.ip pos)) (tag := 4) hpc' hmm
        (fun k => hrunL k)⟩

/-- **The literal row.**  The entry prefix reaches the seam, the seam's branch
outcome writes the record and returns, and the entry's fuel identity carries the
row back to `if.end`. -/
theorem odGapFinal_litRow {mem : Mem} {next c pos lt lf ln : Nat} {win : List UInt8}
    (P : OdGapPrep mem next c pos lt lf ln win)
    (s : State) (hs : OdGapIfEndCells P s) (hposlt : pos < P.ip)
    (hnum : ¬ gapNumStart (win.getD pos 0)) (hch : OdGapLitFirst (win.getD pos 0)) :
    ∃ (off tag : Nat), gapAfterLoop win P.ip pos (gapEe win P.ip pos) = GapWrite.err off tag ∧
      OdGapRow P s off tag := by
  classical
  obtain ⟨_s1, s2, j0, _hstep, hEmpty, hLoop, hrun0⟩ :=
    odGapFinal_litRow_entry P s hs hposlt hnum hch
  by_cases hzero : gapEe win P.ip pos - pos = 0
  · obtain ⟨hpc2, hpre2, hmem2, h0, hc, ht, hcondi, hcond, hee2⟩ := hEmpty hzero
    obtain ⟨off, tag, hA, j2, m, hrun2, h4, h8, h16, hfr⟩ :=
      odGapFinal_litRow_outcome_empty P hzero hpc2 hpre2 hmem2 h0 hc ht hcondi
        hcond hee2 hch hnum
    exact ⟨off, tag, hA, 1 + (j0 + j2), m, by rw [hrun0 j2]; exact hrun2,
      h4, h8, h16, hfr⟩
  · obtain ⟨litBase, lnw, m, hm, hinv, hid⟩ := hLoop (Nat.pos_of_ne_zero hzero)
    obtain ⟨off, tag, hA, j2, m', hrun2, h4, h8, h16, hfr⟩ :=
      odGapFinal_litRow_outcome_loop P hm
        (by simpa only [gapLitFor] using hinv) (by simpa only [gapLitBranch] using hid)
        hch hnum
    exact ⟨off, tag, hA, 1 + (j0 + j2), m', by rw [hrun0 j2]; exact hrun2,
      h4, h8, h16, hfr⟩

/-- The literal row at the weak premise set the model dispatch consumes: a
literal first byte already excludes the number arm and places the token inside
the window, so neither premise is a caller's. -/
theorem odGapFinal_litRow_weak {mem : Mem} {next c pos lt lf ln : Nat}
    {win : List UInt8} (P : OdGapPrep mem next c pos lt lf ln win)
    (s : State) (hs : OdGapIfEndCells P s) (hch : OdGapLitFirst (win.getD pos 0)) :
    ∃ (off tag : Nat), gapAfterLoop win P.ip pos (gapEe win P.ip pos) = GapWrite.err off tag ∧
      OdGapRow P s off tag := by
  have hposlt : pos < P.ip := by
    have hin : pos < win.length := by
      by_contra h
      have hle : win.length ≤ pos := Nat.le_of_not_lt h
      have h0 : win.getD pos 0 = 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle]
        rfl
      rcases hch with h | h | h
      · rw [h] at h0; exact absurd h0.symm (by decide)
      · rw [h] at h0; exact absurd h0.symm (by decide)
      · rw [h] at h0; exact absurd h0.symm (by decide)
    rwa [P.hlen] at hin
  have hnum : ¬ gapNumStart (win.getD pos 0) := by
    simpa only [gapNumStart] using odGapFinal_litRow_notNum hch
  exact odGapFinal_litRow P s hs hposlt hnum hch

/-- **The whole-function contract, hypothesis-free.**  The scan bridges, the
three non-literal rows and the literal row are all discharged, so the body runs
to `void` and leaves exactly the record the model's case table names. -/
theorem odGapRecover_run_post_of_prep {mem : Mem} {next c pos lt lf ln : Nat}
    {win : List UInt8} (P : OdGapPrep mem next c pos lt lf ln win) :
    ∃ (B : Nat) (m : Mem),
      runFuel (stage2Calls stage2SubCalls) B odGapRecoverBody
        (EntryState odGapRecoverBody (odGapEntryArgs c pos lt lf ln) mem next) =
        some (.ret none m) ∧
      (∃ eff, stage2GapRecoverRule mem c pos = some eff ∧
        (eff = .unchanged → m = mem) ∧
        (∀ (e off tag : Nat), eff = .wrote e off tag →
          readBytes m e 4 = some (wordBytes 4 0) ∧
          readBytes m (e + 8) 8 = some (wordBytes 8 off) ∧
          readBytes m (e + 16) 8 = some (wordBytes 8 tag) ∧
          UnchangedOutside mem m
            [(e, 4), (e + 8, 8), (e + 16, 8),
             (next, (Ty.double).sizeBytes),
             (next + (Ty.double).sizeBytes, (Ty.int 64).sizeBytes)])) :=
  odGapRecover_run_post_of_lit P fun s hs _hposlt _hnum hch =>
    odGapFinal_litRow_weak P s hs hch

/-! ### Axiom footprints -/

#print axioms odGapFinal_litRow_outcome_empty
#print axioms odGapFinal_litRow_outcome_loop
#print axioms odGapFinal_litRow
#print axioms odGapFinal_litRow_weak
#print axioms odGapRecover_run_post_of_prep

end LeanLLVM.Refinement
