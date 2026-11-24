/-
`od_gap_recover`'s whole-function contract, assembled from its rows.

The committed `JsonStage2HelperIROdGapContract` proves the staging, the model
rule at it, and the no-write row.  The write rows are proved separately: the
number refusal and acceptance at `if.end`, the scalar refusal through
`if.else43`, and the literal arms (dispatch, compare loop, second scan).  This
module states the assembly once: given the first scan's bridge to `if.end` and
one run-plus-record theorem per first-byte class, the whole body runs to `void`
and leaves exactly the record the model's case table names.

Every row is an explicit hypothesis (`OdGapRow`), so the assembly typechecks
before the rows land, and each row's own proof discharges its hypothesis.  The
body's answer is compared to the model's record, not to its memory: the write
arm names the record's three words at `P.e` and agrees with the caller outside
that record and the entry's two staging slots.
-/
import LeanLLVM.Refinement.JsonStage2HelperIROdGapContract
import LeanLLVM.Refinement.JsonStage2HelperIROdGapRuleCases
import LeanLLVM.Refinement.JsonStage2HelperIROdGapContractB
import LeanLLVM.Refinement.JsonStage2HelperIROdGapLitEntry

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR (stage2Calls)
open LeanLLVM.Refinement.BlockEval

/-- The cells every write row reads at the state the first scan leaves.  The
allocator cursor is the entry's two slots past the caller's base. -/
def OdGapIfEndCells {mem : Mem} {next c pos lt lf ln : Nat} {win : List UInt8}
    (P : OdGapPrep mem next c pos lt lf ln win) (s : State) : Prop :=
  s.pc = "if.end" ∧ s.mem = mem ∧
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
      some (.int 64 (BitVec.ofNat 64 (gapEe win P.ip pos)))

/-- One write row at `if.end`: a completed run to `void` whose memory is the
model's record at `P.e` with the row's offset and tag, and the caller's bytes
outside that record and the two staging slots. -/
def OdGapRow {mem : Mem} {next c pos lt lf ln : Nat} {win : List UInt8}
    (P : OdGapPrep mem next c pos lt lf ln win) (s : State) (off tag : Nat) : Prop :=
  ∃ (j : Nat) (m : Mem),
    runFuel (stage2Calls stage2SubCalls) j odGapRecoverBody s = some (.ret none m) ∧
    readBytes m P.e 4 = some (wordBytes 4 0) ∧
    readBytes m (P.e + 8) 8 = some (wordBytes 8 off) ∧
    readBytes m (P.e + 16) 8 = some (wordBytes 8 tag) ∧
    UnchangedOutside mem m
      [(P.e, 4), (P.e + 8, 8), (P.e + 16, 8),
       (next, (Ty.double).sizeBytes),
       (next + (Ty.double).sizeBytes, (Ty.int 64).sizeBytes)]

/-- The first byte is a literal's first byte. -/
def OdGapLitFirst (ch : UInt8) : Prop :=
  ch = 0x74 ∨ ch = 0x66 ∨ ch = 0x6E

/-- **The whole-function contract, assembled.**  The entry prefix and the first
scan reach `if.end`; the first byte then selects the model's row, whose run and
record the hypotheses supply; and the model's rule at the staging is the effect
of that row's write. -/
theorem odGapRecover_run_post {mem : Mem} {next c pos lt lf ln : Nat} {win : List UInt8}
    (P : OdGapPrep mem next c pos lt lf ln win)
    (hBridgeT : pos < P.ip → gapEe win P.ip pos ≠ P.ip → P.k < P.nix →
      ∃ (sF : State) (jF : Nat), OdGapIfEndCells P sF ∧
        (∀ k, runFuel (stage2Calls stage2SubCalls) (4 + jF + k) odGapRecoverBody
          (EntryState odGapRecoverBody (odGapEntryArgs c pos lt lf ln) mem next) =
          runFuel (stage2Calls stage2SubCalls) k odGapRecoverBody sF))
    (hBridgeF : pos < P.ip → gapEe win P.ip pos ≠ P.ip → ¬ P.k < P.nix →
      ∃ (sF : State) (jF : Nat), OdGapIfEndCells P sF ∧
        (∀ k, runFuel (stage2Calls stage2SubCalls) (4 + jF + k) odGapRecoverBody
          (EntryState odGapRecoverBody (odGapEntryArgs c pos lt lf ln) mem next) =
          runFuel (stage2Calls stage2SubCalls) k odGapRecoverBody sF))
    (hRefuse : ∀ (s : State), OdGapIfEndCells P s → pos < P.ip →
      gapNumStart (win.getD pos 0) →
      (numLexScan (gapSegment win pos (gapEe win P.ip pos))).2 = false →
      OdGapRow P s (pos + (numLexScan (gapSegment win pos (gapEe win P.ip pos))).1)
        gapTagNumber)
    (hAccept : ∀ (s : State), OdGapIfEndCells P s → pos < P.ip →
      gapNumStart (win.getD pos 0) →
      (numLexScan (gapSegment win pos (gapEe win P.ip pos))).2 = true →
      OdGapRow P s (gapS2 win P.ip (gapEe win P.ip pos)) gapTagExtra)
    (hScalar : ∀ (s : State), OdGapIfEndCells P s → pos < P.ip →
      ¬ gapNumStart (win.getD pos 0) →
      win.getD pos 0 ≠ 0x74 → win.getD pos 0 ≠ 0x66 → win.getD pos 0 ≠ 0x6E →
      OdGapRow P s pos gapTagScalar)
    (hLit : ∀ (s : State), OdGapIfEndCells P s → pos < P.ip →
      ¬ gapNumStart (win.getD pos 0) → OdGapLitFirst (win.getD pos 0) →
      ∃ (off tag : Nat), gapAfterLoop win P.ip pos (gapEe win P.ip pos) =
        GapWrite.err off tag ∧ OdGapRow P s off tag) :
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
             (next + (Ty.double).sizeBytes, (Ty.int 64).sizeBytes)])) := by
  classical
  by_cases hnone : gapRecoverWrite win P.ip pos = GapWrite.none
  · obtain ⟨B, _hB, hrun, hclause⟩ := odGapRecover_run_none P hnone
    exact ⟨B, mem, hrun, hclause⟩
  · have hne : gapEe win P.ip pos ≠ P.ip := by
      intro h
      apply hnone
      rw [show gapRecoverWrite win P.ip pos =
        (if gapEe win P.ip pos = P.ip then GapWrite.none
         else gapAfterLoop win P.ip pos (gapEe win P.ip pos)) from rfl, if_pos h]
    have hposlt : pos < P.ip := by
      rcases lt_or_ge pos P.ip with h | h
      · exact h
      · have hposip : pos = P.ip := le_antisymm P.hposip h
        have hEe : gapEe win P.ip pos = P.ip := by
          simp only [gapEe, hposip, Nat.sub_self, gapNonWsRun, Nat.add_zero]
        exact absurd hEe hne
    have hbridge : ∃ (sF : State) (jF : Nat), OdGapIfEndCells P sF ∧
        (∀ k, runFuel (stage2Calls stage2SubCalls) (4 + jF + k) odGapRecoverBody
          (EntryState odGapRecoverBody (odGapEntryArgs c pos lt lf ln) mem next) =
          runFuel (stage2Calls stage2SubCalls) k odGapRecoverBody sF) := by
      by_cases hk : P.k < P.nix
      · exact hBridgeT hposlt hne hk
      · exact hBridgeF hposlt hne hk
    obtain ⟨sF, hbridge2⟩ := hbridge
    obtain ⟨jF, hcells⟩ := hbridge2
    obtain ⟨hbridgeCells, hrunF⟩ := hcells
    have hcells' := hbridgeCells
    obtain ⟨hpcF, hmemF, hnextF, h0F, hcF, htF, hcondF, hdF, heiF, hltF, hlfF,
      hlnF, heeF⟩ := hbridgeCells
    have hw : gapRecoverWrite win P.ip pos =
        gapAfterLoop win P.ip pos (gapEe win P.ip pos) := by
      rw [show gapRecoverWrite win P.ip pos =
        (if gapEe win P.ip pos = P.ip then GapWrite.none
         else gapAfterLoop win P.ip pos (gapEe win P.ip pos)) from rfl, if_neg hne]
    -- one row, by first-byte class
    obtain ⟨j, m, off, tag, hrunRow, hAfter, hrec4, hrec8, hrec16, hframe⟩ :
      ∃ (j : Nat) (m : Mem) (off tag : Nat),
        runFuel (stage2Calls stage2SubCalls) j odGapRecoverBody sF =
          some (.ret none m) ∧
        gapAfterLoop win P.ip pos (gapEe win P.ip pos) = GapWrite.err off tag ∧
        readBytes m P.e 4 = some (wordBytes 4 0) ∧
        readBytes m (P.e + 8) 8 = some (wordBytes 8 off) ∧
        readBytes m (P.e + 16) 8 = some (wordBytes 8 tag) ∧
        UnchangedOutside mem m
          [(P.e, 4), (P.e + 8, 8), (P.e + 16, 8),
           (next, (Ty.double).sizeBytes),
           (next + (Ty.double).sizeBytes, (Ty.int 64).sizeBytes)] := by
      by_cases hnum : gapNumStart (win.getD pos 0)
      · by_cases hacc : (numLexScan (gapSegment win pos (gapEe win P.ip pos))).2
        · have haccT : (numLexScan (gapSegment win pos (gapEe win P.ip pos))).2 = true :=
            by simpa using hacc
          obtain ⟨j, m, hrun, h4, h8, h16, hfr⟩ := hAccept sF hcells' hposlt hnum haccT
          have hA : gapAfterLoop win P.ip pos (gapEe win P.ip pos) =
              GapWrite.err (gapS2 win P.ip (gapEe win P.ip pos)) gapTagExtra :=
            odGapAfterLoop_number_accept (bytes := win) (ip := P.ip) (pos := pos)
              (ee := gapEe win P.ip pos)
              (by simpa only [gapNumStart] using hnum) haccT
          exact ⟨j, m, _, _, hrun, hA, h4, h8, h16, hfr⟩
        · have haccF : (numLexScan (gapSegment win pos (gapEe win P.ip pos))).2 = false :=
            by simpa using hacc
          obtain ⟨j, m, hrun, h4, h8, h16, hfr⟩ := hRefuse sF hcells' hposlt hnum haccF
          have hA : gapAfterLoop win P.ip pos (gapEe win P.ip pos) =
              GapWrite.err (pos + (numLexScan
                (gapSegment win pos (gapEe win P.ip pos))).1) gapTagNumber :=
            odGapAfterLoop_number (bytes := win) (ip := P.ip) (pos := pos)
              (ee := gapEe win P.ip pos)
              (by simpa only [gapNumStart] using hnum) haccF
          exact ⟨j, m, _, _, hrun, hA, h4, h8, h16, hfr⟩
      · by_cases hlf : OdGapLitFirst (win.getD pos 0)
        · obtain ⟨off, tag, hA, j, m, hrun, h4, h8, h16, hfr⟩ := hLit sF hcells' hposlt hnum hlf
          exact ⟨j, m, off, tag, hrun, hA, h4, h8, h16, hfr⟩
        · have h74 : win.getD pos 0 ≠ 0x74 := fun h => hlf (Or.inl h)
          have h66 : win.getD pos 0 ≠ 0x66 := fun h => hlf (Or.inr (Or.inl h))
          have h6E : win.getD pos 0 ≠ 0x6E := fun h => hlf (Or.inr (Or.inr h))
          obtain ⟨j, m, hrun, h4, h8, h16, hfr⟩ :=
            hScalar sF hcells' hposlt hnum h74 h66 h6E
          have hA : gapAfterLoop win P.ip pos (gapEe win P.ip pos) =
              GapWrite.err pos gapTagScalar :=
            odGapAfterLoop_scalar (ch := win.getD pos 0) rfl
              (by simpa only [gapNumStart] using hnum) h74 h66 h6E
          exact ⟨j, m, _, _, hrun, hA, h4, h8, h16, hfr⟩
    -- the rule at the staging is the row's write
    have hrule : stage2GapRecoverRule mem c pos = some (.wrote P.e off tag) := by
      rw [stage2GapRecoverRule_of_prep P, hw, hAfter]
      rfl
    have hrun : runFuel (stage2Calls stage2SubCalls) (4 + jF + j) odGapRecoverBody
        (EntryState odGapRecoverBody (odGapEntryArgs c pos lt lf ln) mem next) =
        some (.ret none m) := by
      rw [hrunF j]
      exact hrunRow
    refine ⟨4 + jF + j, m, hrun, ?_⟩
    refine ⟨.wrote P.e off tag, hrule, ?_, ?_⟩
    · intro h
      cases h
    · intro e' off' tag' h
      cases h
      exact ⟨hrec4, hrec8, hrec16, hframe⟩


/-! ### The literal row -/

/-- One `cleanup82` step returns `void` with the state's memory. -/
theorem odGapFinal_cleanup_ret {m : Mem} {s : State}
    (hpc : s.pc = "cleanup82") (hmem : s.mem = m) :
    runFuel (stage2Calls stage2SubCalls) 1 odGapRecoverBody s = some (.ret none m) := by
  have hret : step (stage2Calls stage2SubCalls) odGapRecoverBody s = .ret none s :=
    gap_step_cleanup82 (calls := stage2Calls stage2SubCalls) (env := s.env) (s := s) hpc
  refine gapNum_runFuel_ret_void hret ?_
  rw [hmem]

/-! ### Axiom footprints -/

#print axioms odGapRecover_run_post
#print axioms OdGapRow
#print axioms OdGapIfEndCells


/-! ### Discharging the bridges and the non-literal rows -/

/-- The first loop's count never exceeds its budget. -/
theorem odGapFinal_nonWsRun_le (k : Nat) (bs : List UInt8) : gapNonWsRun k bs ≤ k := by
  induction k generalizing bs with
  | zero => simp [gapNonWsRun]
  | succ k ih =>
      cases bs with
      | nil => simp [gapNonWsRun]
      | cons b bs =>
          simp only [gapNonWsRun]
          split
          · omega
          · have := ih bs; omega

/-- `gapEe` never leaves the window. -/
theorem odGapFinal_gapEe_le {win : List UInt8} {ip pos : Nat} (hpos : pos ≤ ip) :
    gapEe win ip pos ≤ ip := by
  unfold gapEe
  have := odGapFinal_nonWsRun_le (ip - pos) (win.drop pos)
  omega

/-- `gapEe` starts at or after the token's position. -/
theorem odGapFinal_gapEe_ge (win : List UInt8) (ip pos : Nat) : pos ≤ gapEe win ip pos := by
  unfold gapEe
  exact Nat.le_add_right _ _

/-- The record field is outside the two staging slots. -/
theorem odGapFinal_hfield {mem : Mem} {next c pos lt lf ln : Nat} {win : List UInt8}
    (P : OdGapPrep mem next c pos lt lf ln win) :
    c + odGapCurE + 8 ≤ next ∨ next + 16 ≤ c + odGapCurE := by
  have h := odGapPrep_sep P
  simp only [odGapCurE] at h ⊢
  omega

/-- The refusal record written directly over the caller's memory. -/
theorem odGapFinal_memory_wrote {mem : Mem} {e next off tag : Nat} :
    readBytes (stage2ErrSetMsg mem e off tag) e 4 = some (wordBytes 4 0) ∧
      readBytes (stage2ErrSetMsg mem e off tag) (e + 8) 8 = some (wordBytes 8 off) ∧
      readBytes (stage2ErrSetMsg mem e off tag) (e + 16) 8 = some (wordBytes 8 tag) ∧
      UnchangedOutside mem (stage2ErrSetMsg mem e off tag)
        [(e, 4), (e + 8, 8), (e + 16, 8),
         (next, (Ty.double).sizeBytes),
         (next + (Ty.double).sizeBytes, (Ty.int 64).sizeBytes)] :=
  ⟨stage2ErrSetMsg_ok_read mem e off tag, stage2ErrSetMsg_off_read mem e off tag,
    stage2ErrSetMsg_msg_read mem e off tag,
    by
      simpa only [odGapSizeBytes_double, odGapSizeBytes_i64] using
        (odGap_unchangedOutside_errSetMsg (ref := mem) (m := mem) (e := e) (next := next)
          (off := off) (tag := tag) (fun _ _ => rfl))⟩

/-- **The whole-function contract with only the literal row left as a
hypothesis.**  The scan bridges and the three non-literal rows are discharged
from the committed modules. -/
theorem odGapRecover_run_post_of_lit {mem : Mem} {next c pos lt lf ln : Nat}
    {win : List UInt8}
    (P : OdGapPrep mem next c pos lt lf ln win)
    (hLit : ∀ (s : State), OdGapIfEndCells P s → pos < P.ip →
      ¬ gapNumStart (win.getD pos 0) → OdGapLitFirst (win.getD pos 0) →
      ∃ (off tag : Nat), gapAfterLoop win P.ip pos (gapEe win P.ip pos) = GapWrite.err off tag ∧
        OdGapRow P s off tag) :
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
             (next + (Ty.double).sizeBytes, (Ty.int 64).sizeBytes)])) := by
  refine odGapRecover_run_post P ?_ ?_ ?_ ?_ ?_ hLit
  · intro hposlt hne hklt
    obtain ⟨sF, jF, _hjF, hpc, hpre, hmem, hnext, h0, hc, ht, hcond, hd, hei, hltv,
      hlfv, hlnv, hee, hrun⟩ := odGap_run_to_ifEnd_true P hklt hposlt hne
    exact ⟨sF, jF, ⟨hpc, hmem, hnext, h0, hc, ht, hcond, hd, hei, hltv, hlfv, hlnv, hee⟩,
      hrun⟩
  · intro hposlt hne hnk
    obtain ⟨sF, jF, _hjF, hpc, hpre, hmem, hnext, h0, hc, ht, hcond, hd, hei, hltv,
      hlfv, hlnv, hee, hrun⟩ := odGap_run_to_ifEnd_false P hnk hposlt hne
    exact ⟨sF, jF, ⟨hpc, hmem, hnext, h0, hc, ht, hcond, hd, hei, hltv, hlfv, hlnv, hee⟩,
      hrun⟩
  · intro s hs hposlt hnum hacc
    obtain ⟨hpc, hmem, hnext, h0, hc, ht, hcond, hd, hei, hltv, hlfv, hlnv, hee⟩ := hs
    have hnumByte : gapNumberByte (gapByte (win.getD pos 0)) :=
      (odGapNumberByte_iff' (win.getD pos 0)).2 (by simpa only [gapNumStart] using hnum)
    have hposee : pos ≤ gapEe win P.ip pos := odGapFinal_gapEe_ge win P.ip pos
    have heele : gapEe win P.ip pos ≤ P.ip := odGapFinal_gapEe_le P.hposip
    have hfield : c + odGapCurE + 8 ≤ next ∨ next + 16 ≤ c + odGapCurE := odGapFinal_hfield P
    have hpos64 : pos < 2 ^ 64 := lt_of_le_of_lt P.hposip P.hip64
    have hrun := odGap_numberRefusal_ifEnd (mem := mem) (c := c) (pos := pos) (b := P.b)
      (e := P.e) (ip := P.ip) (ee := gapEe win P.ip pos) (next := next) (bytes := win)
      (s := s) hpc hmem h0 ht hee hd hei hc hnext P.hbytes P.hlen hposlt hposee heele
      hpos64 P.hip64 P.hip63 P.he P.he64 hfield hnumByte hacc
    obtain ⟨h4, h8, h16, hfr⟩ := odGap_memory_numberRefusal (mem := mem) (next := next)
      (e := P.e) (pos := pos) (off := (numLexScan (gapSegment win pos (gapEe win P.ip pos))).1)
    have hfr' : UnchangedOutside mem
        (stage2ErrSetMsg (writeBytes mem (next + 8)
          (wordBytes 8 (numLexScan (gapSegment win pos (gapEe win P.ip pos))).1)) P.e
          (pos + (numLexScan (gapSegment win pos (gapEe win P.ip pos))).1) 1)
        [(P.e, 4), (P.e + 8, 8), (P.e + 16, 8),
         (next, (Ty.double).sizeBytes),
         (next + (Ty.double).sizeBytes, (Ty.int 64).sizeBytes)] := by
      simpa only [odGapSizeBytes_double, odGapSizeBytes_i64] using hfr
    exact ⟨4,
      stage2ErrSetMsg (writeBytes mem (next + 8)
        (wordBytes 8 (numLexScan (gapSegment win pos (gapEe win P.ip pos))).1)) P.e
        (pos + (numLexScan (gapSegment win pos (gapEe win P.ip pos))).1) 1,
      hrun, h4, h8, h16, hfr'⟩
  · intro s hs hposlt hnum hacc
    obtain ⟨hpc, hmem, hnext, h0, hc, ht, hcond, hd, hei, hltv, hlfv, hlnv, hee⟩ := hs
    have hnumByte : gapNumberByte (gapByte (win.getD pos 0)) :=
      (odGapNumberByte_iff' (win.getD pos 0)).2 (by simpa only [gapNumStart] using hnum)
    have hposee : pos ≤ gapEe win P.ip pos := odGapFinal_gapEe_ge win P.ip pos
    have heele : gapEe win P.ip pos ≤ P.ip := odGapFinal_gapEe_le P.hposip
    have hfield : c + odGapCurE + 8 ≤ next ∨ next + 16 ≤ c + odGapCurE := odGapFinal_hfield P
    have hpos64 : pos < 2 ^ 64 := lt_of_le_of_lt P.hposip P.hip64
    have hval : (wordBytes 8 (numFastEmitted (JSON.ByteString.literal
        (gapSegment win pos (gapEe win P.ip pos)))).toBits).length = 8 := by
      simp only [wordBytes, natToBytes_length]
    obtain ⟨j, hj, hrun, h4, h8, h16, hfr⟩ := odGap_numberAccept_ifEnd (mem := mem)
      (c := c) (pos := pos) (b := P.b) (e := P.e) (ip := P.ip) (ee := gapEe win P.ip pos)
      (next := next) (bytes := win) (s := s) hpc hmem h0 ht hee hd hei hc hcond hnext
      P.hbytes P.hlen hposlt hposee heele hpos64 P.hip64 P.hip63 P.he P.he64 hfield P.hwin
      hnumByte hacc
    have hfr' : UnchangedOutside mem
        (stage2ErrSetMsg (writeBytes mem next
          (wordBytes 8 (numFastEmitted (JSON.ByteString.literal
            (gapSegment win pos (gapEe win P.ip pos)))).toBits)) P.e
          (gapS2 win P.ip (gapEe win P.ip pos)) 4)
        [(P.e, 4), (P.e + 8, 8), (P.e + 16, 8),
         (next, (Ty.double).sizeBytes),
         (next + (Ty.double).sizeBytes, (Ty.int 64).sizeBytes)] := by
      simpa only [odGapSizeBytes_double, odGapSizeBytes_i64] using hfr
    exact ⟨j, _, hrun, h4, h8, h16, hfr'⟩
  · intro s hs hposlt hnum h74 h66 h6E
    obtain ⟨hpc, hmem, hnext, h0, hc, ht, hcond, hd, hei, hltv, hlfv, hlnv, hee⟩ := hs
    have hpos64 : pos < 2 ^ 64 := lt_of_le_of_lt P.hposip P.hip64
    obtain ⟨j, hj, hrun⟩ := odGap_scalar_ifEnd (mem := mem) (c := c) (pos := pos)
      (b := P.b) (e := P.e) (ip := P.ip) (next := next) (win := win) (s := s)
      hpc hmem h0 ht hc P.hbytes P.hlen hposlt hpos64 P.hip63 P.he P.he64
      ⟨hnum, h74, h66, h6E⟩
    obtain ⟨h4, h8, h16, hfr⟩ := odGapFinal_memory_wrote (mem := mem) (e := P.e)
      (next := next) (off := pos) (tag := gapTagScalar)
    exact ⟨j, stage2ErrSetMsg mem P.e pos gapTagScalar, hrun, h4, h8, h16, hfr⟩


theorem odGapFinal_litRow_entry {mem : Mem} {next c pos lt lf ln : Nat}
    {win : List UInt8}
    (P : OdGapPrep mem next c pos lt lf ln win)
    (s : State) (hs : OdGapIfEndCells P s) (hposlt : pos < P.ip)
    (hnum : ¬ gapNumStart (win.getD pos 0)) (hch : OdGapLitFirst (win.getD pos 0)) :
    ∃ (s1 s2 : State) (j0 : Nat),
      step (stage2Calls stage2SubCalls) odGapRecoverBody s = .jump s1 ∧
      (gapEe win P.ip pos - pos = 0 →
        s2.pc = "if.then57" ∧ s2.pre = some "for.end.i" ∧ s2.mem = mem ∧
        lookupName s2.env "%0" = some (.ptr P.b) ∧
        lookupName s2.env "%c" = some (.ptr c) ∧
        lookupName s2.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 pos)) ∧
        lookupName s2.env "%cond.i" = some (.int 64 (BitVec.ofNat 64 0)) ∧
        lookupName s2.env "%cond" = some (.int 64 (BitVec.ofNat 64 P.ip)) ∧
        lookupName s2.env "%ee.0.lcssa" =
          some (.int 64 (BitVec.ofNat 64 (pos + (gapEe win P.ip pos - pos))))) ∧
      (0 < gapEe win P.ip pos - pos →
        ∃ (litBase lnw m : Nat), m = min (gapEe win P.ip pos - pos) lnw ∧
          gapLitInv win
            (if win.getD pos 0 = 0x74 then gapTrueLit
             else if win.getD pos 0 = 0x66 then gapFalseLit else gapNullLit)
            P.b P.ip c (P.b + pos) litBase pos (gapEe win P.ip pos - pos) lnw m
            mem (m - 1) s2 0 ∧
          ((win.getD pos 0 = 0x74 ∧ litBase = lt ∧ lnw = 4) ∨
           (win.getD pos 0 = 0x66 ∧ litBase = lf ∧ lnw = 5) ∨
           (win.getD pos 0 = 0x6E ∧ litBase = ln ∧ lnw = 4))) ∧
      (∀ k, runFuel (stage2Calls stage2SubCalls) (1 + (j0 + k)) odGapRecoverBody s =
        runFuel (stage2Calls stage2SubCalls) k odGapRecoverBody s2) := by
  classical
  obtain ⟨hpc, hmem, hnext, h0, hc, ht, hcond, hd, hei, hltv, hlfv, hlnv, hee⟩ := hs
  have hnotnum : ¬ gapNumberByte (gapByte (win.getD pos 0)) :=
    fun h => hnum ((odGapNumberByte_iff' (win.getD pos 0)).mp h)
  have hbit : (evalICmp .eq (gapByte (win.getD pos 0)) (BitVec.ofNat 8 45) |||
      evalICmp .ult (gapByte (win.getD pos 0) + BitVec.ofNat 8 208)
        (BitVec.ofNat 8 10)) = 0#1 := by
    have h1 : evalICmp .eq (gapByte (win.getD pos 0)) (BitVec.ofNat 8 45) = 0#1 := by
      rcases bitVec1_eq_zero_or_one _ with h | h
      · exact h
      · exact absurd (Or.inl h) hnotnum
    have h2 : evalICmp .ult (gapByte (win.getD pos 0) + BitVec.ofNat 8 208)
        (BitVec.ofNat 8 10) = 0#1 := by
      rcases bitVec1_eq_zero_or_one _ with h | h
      · exact h
      · exact absurd (Or.inr h) hnotnum
    rw [h1, h2]
    rfl
  have hbyte : readBytes s.mem (P.b + pos) 1 =
      some (natToBytes (gapByte (win.getD pos 0)).toNat 1) := by
    rw [hmem]
    exact gap_readOne (h := P.hbytes) (hc := hposlt) (hbyte := rfl)
  have hpos64 : pos < 2 ^ 64 := by
    have h1 := hposlt; have h2 := P.hip63; omega
  have hse : ((BitVec.ofNat 64 pos).signExtend 64).toNat = pos :=
    gap_signExtend_ofNat pos hpos64
  have hse63 : pos < 2 ^ 63 := by
    have h1 := hposlt; have h2 := P.hip63; omega
  have hstep1 : step (stage2Calls stage2SubCalls) odGapRecoverBody (stateAt s.env s) =
      .jump (stateAt (gapNumIfEndEnv s.env P.b pos (gapByte (win.getD pos 0)))
        { s with pc := "if.else", pre := some "if.end" }) :=
    gapNum_step_ifEnd_nonNum (calls := stage2Calls stage2SubCalls) (env := s.env)
      (s := s) hpc h0 ht hse hse63 hbyte hbit
  let s1 : State := stateAt (gapNumIfEndEnv s.env P.b pos (gapByte (win.getD pos 0)))
    { s with pc := "if.else", pre := some "if.end" }
  have h7 : lookupName s1.env "%7" = some (.int 8 (gapByte (win.getD pos 0))) := by
    simp only [s1, stateAt, gapNumIfEndEnv]; block_lk
  have h0' : lookupName s1.env "%0" = some (.ptr P.b) := by
    simp only [s1, stateAt, gapNumIfEndEnv]; block_lk
  have hc' : lookupName s1.env "%c" = some (.ptr c) := by
    simp only [s1, stateAt, gapNumIfEndEnv]; block_lk
  have ht' : lookupName s1.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 pos)) := by
    simp only [s1, stateAt, gapNumIfEndEnv]; block_lk
  have hee' : lookupName s1.env "%ee.0.lcssa" =
      some (.int 64 (BitVec.ofNat 64 (gapEe win P.ip pos))) := by
    simp only [s1, stateAt, gapNumIfEndEnv]; block_lk
  have hcond' : lookupName s1.env "%cond" = some (.int 64 (BitVec.ofNat 64 P.ip)) := by
    simp only [s1, stateAt, gapNumIfEndEnv]; block_lk
  have harr' : lookupName s1.env "%arrayidx9" = some (.ptr (P.b + pos)) := by
    simp only [s1, stateAt, gapNumIfEndEnv]; block_lk
  have hltT' : lookupName s1.env "%littrue" = some (.ptr lt) := by
    simp only [s1, stateAt, gapNumIfEndEnv]; block_lk
  have hltF' : lookupName s1.env "%litfalse" = some (.ptr lf) := by
    simp only [s1, stateAt, gapNumIfEndEnv]; block_lk
  have hltN' : lookupName s1.env "%litnull" = some (.ptr ln) := by
    simp only [s1, stateAt, gapNumIfEndEnv]; block_lk
  have hmem1 : s1.mem = mem := by simp only [s1, stateAt]; exact hmem
  have hposee : pos ≤ gapEe win P.ip pos := odGapFinal_gapEe_ge win P.ip pos
  have heele : gapEe win P.ip pos ≤ P.ip := odGapFinal_gapEe_le P.hposip
  have hn64 : pos + (gapEe win P.ip pos - pos) < 2 ^ 64 := by
    have h1 := heele; have h2 := P.hip64; omega
  -- the literal the branch selects
  let lit : List UInt8 := if win.getD pos 0 = 0x74 then gapTrueLit
    else if win.getD pos 0 = 0x66 then gapFalseLit else gapNullLit
  have hlitT : win.getD pos 0 = 0x74 → lit = gapTrueLit := by
    intro h; simp only [lit]; rw [if_pos h]
  have hlitF : win.getD pos 0 = 0x66 → lit = gapFalseLit := by
    intro h; simp only [lit]
    rw [if_neg (by rw [h]; decide : ¬ (win.getD pos 0 = 0x74)), if_pos h]
  have hlitN : win.getD pos 0 = 0x6E → lit = gapNullLit := by
    intro h; simp only [lit]
    rw [if_neg (by rw [h]; decide : ¬ (win.getD pos 0 = 0x74)),
      if_neg (by rw [h]; decide : ¬ (win.getD pos 0 = 0x66))]
  have hnot8 : ¬ (win.getD pos 0 = 0x2D ∨
      (0x30 ≤ win.getD pos 0 ∧ win.getD pos 0 ≤ 0x39)) := by
    simpa only [gapNumStart] using hnum
  have hnotnumNat : ¬ ((win.getD pos 0).toNat = 45 ∨
      (48 ≤ (win.getD pos 0).toNat ∧ (win.getD pos 0).toNat ≤ 57)) :=
    fun h => hnot8 ((odGapNumberCondition_iff (win.getD pos 0)).mpr h)
  have hlitne : lit ≠ [] := by
    rcases hch with h | h | h
    · rw [hlitT h]; exact (by decide : gapTrueLit ≠ [])
    · rw [hlitF h]; exact (by decide : gapFalseLit ≠ [])
    · rw [hlitN h]; exact (by decide : gapNullLit ≠ [])
  -- the dispatch to the loop's seed
  have hposn : pos + (gapEe win P.ip pos - pos) = gapEe win P.ip pos :=
    Nat.add_sub_cancel' hposee
  have hee'' : lookupName s1.env "%ee.0.lcssa" =
      some (.int 64 (BitVec.ofNat 64 (pos + (gapEe win P.ip pos - pos)))) := by
    rw [hposn]; exact hee'
  have hchb : gapByte (win.getD pos 0) = 116 ∨ gapByte (win.getD pos 0) = 102 ∨
      gapByte (win.getD pos 0) = 110 := by
    rcases hch with h | h | h
    · exact Or.inl (by rw [h]; decide)
    · exact Or.inr (Or.inl (by rw [h]; decide))
    · exact Or.inr (Or.inr (by rw [h]; decide))
  obtain ⟨s2, j0, hj0, hEmpty, hLoop, hrun0⟩ :=
    gapLit_entry (calls := stage2Calls stage2SubCalls) (mem := mem)
      (litBytes := lit) (b := P.b) (ip := P.ip) (cur := c) (t := pos)
      (n := gapEe win P.ip pos - pos) (lt := lt) (lf := lf) (lnn := ln)
      rfl hmem1 h0' hc' ht' hee'' hcond' h7 hltT' hltF' hltN' harr' hchb hn64
  have hrun0' : ∀ k, runFuel (stage2Calls stage2SubCalls) (j0 + k) odGapRecoverBody s1 =
      runFuel (stage2Calls stage2SubCalls) k odGapRecoverBody s2 := fun k => by
    simpa only [s1, stateAt] using hrun0 k
  have hstep1' : step (stage2Calls stage2SubCalls) odGapRecoverBody s = .jump s1 := by
    simpa only [s1, stateAt] using hstep1
  refine ⟨s1, s2, j0, hstep1', ?_, ?_, ?_⟩
  · exact hEmpty
  · intro hpos
    obtain ⟨litBase, lnw, m, hm, hinv, hEq⟩ := hLoop hpos
    refine ⟨litBase, lnw, m, hm, hinv, ?_⟩
    rcases hEq with ⟨hb, a, b⟩ | ⟨hb, a, b⟩ | ⟨hb, a, b⟩
    · have h74 : win.getD pos 0 = 0x74 := by
        have h := hb
        rw [show (116 : BitVec 8) = gapByte (0x74 : UInt8) from by decide] at h
        exact (gapLit_gapByte_eq).mp h
      exact Or.inl ⟨h74, a, b⟩
    · have h66 : win.getD pos 0 = 0x66 := by
        have h := hb
        rw [show (102 : BitVec 8) = gapByte (0x66 : UInt8) from by decide] at h
        exact (gapLit_gapByte_eq).mp h
      exact Or.inr (Or.inl ⟨h66, a, b⟩)
    · have h6E : win.getD pos 0 = 0x6E := by
        have h := hb
        rw [show (110 : BitVec 8) = gapByte (0x6E : UInt8) from by decide] at h
        exact (gapLit_gapByte_eq).mp h
      exact Or.inr (Or.inr ⟨h6E, a, b⟩)
  · intro k
    exact (runFuel_jump_prefix hstep1' (j0 + k)).trans (hrun0' k)

end LeanLLVM.Refinement
