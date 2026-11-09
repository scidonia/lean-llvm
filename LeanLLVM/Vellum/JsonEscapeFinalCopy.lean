/-
The final copy's run, from `while.end35` to the return.

`JsonEscapeCopyLoops` proves the copy after the walk (`while.body.i`) as a
`BoundLoop` and its exit word; what it does not carry is where the copy's
destination sits in the caller's buffer.  `while.end35` sets the copy's bases to
`%p + %i.0.lcssa` and `%dst + %j.0.lcssa`, so the walk's decoded prefix — the bytes
`DecodeInv.stored` records at `%dst` — lies *below* every address the copy writes.
`copyPreLoop` is the same loop with that prefix conjoined to its invariant and its
exit word, so a run of the copy leaves both the decoded prefix and the bytes it
moved.  The prefix survives every visit because both of a visit's stores start at
`dst + k` with `dst = dst0 + j`, and the same `j + sub + 64 ≤ regw` bound puts the
visits inside the destination extent the record promises; `UnchangedOutside` is
carried beside the reads for the same reason.

`finalSource_read` / `finalSource_take` read the copy's source range out of the
record's own clauses: the body from the walk's cursor, plus the thirty-two bytes
the record promises past its end.  `DecodeInv.out_length_le_cursor` is the relation
between `%i.0.lcssa` and `%j.0.lcssa` the continuation needs — the decoded prefix is
no longer than its cursor — stated from the staging's spacing.

The relation `DecodeInv.out_length_le_cursor` states is *derived* rather than
assumed: the list the staging decodes is `(ps.map …).drop k0`, `Spaced` is not
suffix-closed on the nose — a `control`/`refuse` constructor's tail is
unconstrained — but a suffix of the body's own position list is still a cursor
list, and `JsonEscapeSteps.escAt_drop_spaced` is that fact (`Spaced.mono` lowers
the cursor back to the resumed walk's own zero; it lives beside `Spaced` in
`JsonEscapeSpec`).

`whileEnd35_run` is the suffix itself: `while.end35` into the copy,
`us_run_long.exit` through `if.then.i109` and `us_run.exit112` into `cleanup41`,
and the return, from the block's own `phi` cells at any of its four incoming
edges.  Three facts the exit word once left to the run are the branch's: the body's
bytes and its thirty-two trailing bytes at the *exit* state's memory
(`exitBody_read`, `exitTail_read`), the offset slot's read (the destination-extent
frame), and — at the latch — the byte cursor's bound inside the body
(`AssemblyLatchExit`'s `%add24 ≤ n`).  `entryExit_admits_clobbered_err` and
`latchExit_admits_cursor_past_body` are the states that forced each, and they stay
as the recorded reason.

`expandExit_satisfied` consumes that run at the exit word's six branches, so the
record's `ExpandFacts.exit` field is discharged: the two `cleanup41` predecessors
by `refusalExit_post` and `successExit_post`, the two `while.end35` edges by
`whileEnd35_run`, and the two edges the staging's range clause excludes by
`assemblyWhileBody6Exit_vacuous` / `assemblyWhileBodyExit_vacuous`.
-/
import LeanLLVM.Vellum.JsonEscapeExpandFacts

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Vellum

open LeanLLVM
open LeanLLVM.Vellum.JsonEscapeIR
open LeanLLVM.Vellum.JsonEscapeIntrinsics
open LeanLLVM.Vellum.JsonScanSpec

macro "ud_lk" : tactic => `(tactic|
  ((repeat rw [lookupName_cons_ne _ _ (by decide)]) <;>
   (first | rw [lookupName_cons_self] | rfl)))

/-- A thirty-two-byte store at `dst + k` extends a prefix the caller holds at
`dst`. -/
theorem readBytes_writeBytes_thirtyTwo {m : Mem} {dst k : Nat} {out bs : List UInt8}
    (hout : readBytes m dst k = some out) (hlen : bs.length = 32) :
    readBytes (writeBytes m (dst + k) bs) dst (k + 32) = some (out ++ bs) := by
  have hbelow : readBytes (writeBytes m (dst + k) bs) dst k = some out := by
    rw [readBytes_writeBytes_below m bs k dst (dst + k) (by omega)]
    exact hout
  have hsame : readBytes (writeBytes m (dst + k) bs) (dst + k) bs.length = some bs :=
    readBytes_writeBytes_same m bs (addr := dst + k)
  rw [hlen] at hsame
  exact JsonEntrySteps.readBytes_append (m := writeBytes m (dst + k) bs) k dst out 32 bs
    hbelow hsame

/-- The prefix, at an address below every write of one copy visit, survives it. -/
theorem readBytes_copy2Mem_prefix {mem : Mem} {dst dst0 j d : Nat}
    {out bs1 bs2 : List UInt8}
    (hshift : dst0 + j = dst) (hle : dst ≤ d)
    (hout : readBytes mem dst0 j = some out) :
    readBytes (udCopy2Mem mem d bs1 bs2) dst0 j = some out := by
  have h1 : dst0 + j ≤ d + 32 := by rw [hshift]; omega
  have h0 : dst0 + j ≤ d := by rw [hshift]; exact hle
  simp only [udCopy2Mem]
  rw [readBytes_writeBytes_below _ _ j dst0 (d + 32) h1]
  rw [readBytes_writeBytes_below _ _ j dst0 d h0]
  exact hout

/-- The head's back-edge counter cell. -/
theorem copyNEnv_knext (env : Env) (src dst : Nat) (k : BitVec 64) (bs1 bs2 : List UInt8)
    (subv : BitVec 64) :
    lookupName (udCopyBodyNEnv env src dst k bs1 bs2 subv) copyBodyNNames.knext =
      some (.int 64 (k + BitVec.ofInt 64 64)) := by
  simp only [udCopyBodyNEnv]; ud_lk

/-- The head's back-edge residual cell. -/
theorem copyNEnv_snext (env : Env) (src dst : Nat) (k : BitVec 64) (bs1 bs2 : List UInt8)
    (subv : BitVec 64) :
    lookupName (udCopyBodyNEnv env src dst k bs1 bs2 subv) copyBodyNNames.snext =
      some (.int 64 (subv - (k + BitVec.ofInt 64 64))) := by
  simp only [udCopyBodyNEnv]; ud_lk

/-- The head's source base, carried unchanged. -/
theorem copyNEnv_src (env : Env) (src dst : Nat) (k : BitVec 64) (bs1 bs2 : List UInt8)
    (subv : BitVec 64) :
    lookupName (udCopyBodyNEnv env src dst k bs1 bs2 subv) copyBodyNNames.srcreg =
      lookupName env copyBodyNNames.srcreg := by
  simp only [udCopyBodyNEnv]; ud_lk

/-- The head's destination base, carried unchanged. -/
theorem copyNEnv_dst (env : Env) (src dst : Nat) (k : BitVec 64) (bs1 bs2 : List UInt8)
    (subv : BitVec 64) :
    lookupName (udCopyBodyNEnv env src dst k bs1 bs2 subv) copyBodyNNames.dstreg =
      lookupName env copyBodyNNames.dstreg := by
  simp only [udCopyBodyNEnv]; ud_lk

/-- The head's residual, carried unchanged. -/
theorem copyNEnv_sub (env : Env) (src dst : Nat) (k : BitVec 64) (bs1 bs2 : List UInt8)
    (subv : BitVec 64) :
    lookupName (udCopyBodyNEnv env src dst k bs1 bs2 subv) copyBodyNNames.subreg =
      lookupName env copyBodyNNames.subreg := by
  simp only [udCopyBodyNEnv]; ud_lk

/-- Two frames compose when the first's regions are among the second's: a byte
outside the first's regions is outside the second's too, so the second leaves it as
the run found it and the first leaves it as the caller had it. -/
theorem UnchangedOutside.comp {m0 m1 m2 : Mem} {R₁ R₂ : List (Nat × Nat)}
    (h1 : UnchangedOutside m0 m1 R₁) (h2 : UnchangedOutside m1 m2 R₂)
    (hsub : ∀ r ∈ R₂, r ∈ R₁) : UnchangedOutside m0 m2 R₁ :=
  fun a ha => (h2 a (fun r hr => ha r (hsub r hr))).trans (h1 a ha)

/-- **A store inside one of the regions leaves the frame.**  The written bytes are
inside a region the frame already excludes, so every byte the frame talks about is
outside the store. -/
theorem UnchangedOutside.writeBytes_in {m0 m : Mem} {regions : List (Nat × Nat)}
    {a : Nat} {bs : List UInt8} (h : UnchangedOutside m0 m regions)
    (hin : ∃ r ∈ regions, r.1 ≤ a ∧ a + bs.length ≤ r.1 + r.2) :
    UnchangedOutside m0 (writeBytes m a bs) regions := by
  intro x hx
  have houtside : x < a ∨ a + bs.length ≤ x := by
    rcases Nat.lt_or_ge x a with hlt | hge
    · exact Or.inl hlt
    · refine Or.inr (Nat.le_of_not_lt ?_)
      intro hlt
      obtain ⟨r, hr, hlo, hhi⟩ := hin
      exact hx r hr ⟨by omega, by omega⟩
  rw [readByte_writeBytes_outside m bs houtside]
  exact h x hx

/-- A write inside a region leaves every byte outside the region as it was, so a
frame over that region carries through it. -/
theorem UnchangedOutside.writeBytes_inside {m0 m : Mem} {lo w a : Nat} {bs : List UInt8}
    (h : UnchangedOutside m0 m [(lo, w)]) (ha : lo ≤ a) (hb : a + bs.length ≤ lo + w) :
    UnchangedOutside m0 (writeBytes m a bs) [(lo, w)] :=
  UnchangedOutside.writeBytes_in h ⟨(lo, w), by simp, ha, hb⟩

/-- **The final copy's loop, with the caller's prefix carried.**  `CopyInv` states
the copy's own prefix at the block's `%dst`; this instance conjoins the bytes the
walk already wrote at the caller's destination base, which every visit leaves
below its first write. -/
def copyPreLoop (src dst sub : Nat) (B : List UInt8) (dst0 j : Nat) (out : List UInt8)
    (m0 : Mem) (regw : Nat) (kv xjv : Nat) (hshift : dst0 + j = dst)
    (hfit : j + sub + 64 ≤ regw) : BoundLoop escapeCalls usDecFunction where
  head := copyBodyNNames.head
  exitBlock := copyBodyNNames.tail
  N := copyIterBound sub
  cost := 1
  Inv := fun r s c =>
    CopyInv copyBodyNNames src dst sub B r c s ∧ readBytes s.mem dst0 j = some out ∧
      UnchangedOutside m0 s.mem [(dst0, regw)] ∧
      lookupName s.env "%j.0.lcssa" = some (.int 64 (BitVec.ofNat 64 j)) ∧
      lookupName s.env "%k.1.lcssa" = some (.int 64 (BitVec.ofNat 64 kv)) ∧
      lookupName s.env "%xj" = some (.ptr xjv)
  atBound := copyAtBound sub
  Exit := fun e => e.pc = copyBodyNNames.tail
  ExitWord := fun e =>
    CopyExitWord copyBodyNNames src dst sub B e ∧ readBytes e.mem dst0 j = some out ∧
      UnchangedOutside m0 e.mem [(dst0, regw)] ∧
      lookupName e.env "%j.0.lcssa" = some (.int 64 (BitVec.ofNat 64 j)) ∧
      lookupName e.env "%k.1.lcssa" = some (.int 64 (BitVec.ofNat 64 kv)) ∧
      lookupName e.env "%xj" = some (.ptr xjv)
  step_exit := by
    intro r s c h hat
    obtain ⟨hcopy, hpref, hframe, hjc, hkc, hxjc⟩ := h
    obtain ⟨prev, op, k, hpc, hprev, hinc, hop, hkval, hsrc, hdst, hsubc, hwhole,
      hBlen, hprefix, hdisj, hsub63, hgate, hlo, hhi⟩ := hcopy
    have hat' : copyIterBound sub ≤ c := by
      have := hat
      simp only [copyAtBound] at this
      exact of_decide_eq_true this
    have hc : c = copyIterBound sub := by omega
    have hbnd := copyIterBound_mul_le sub
    have hkN : k.toNat = 64 * c := by
      rw [hkval, BitVec.toNat_ofNat]
      omega
    have hkNlt : k.toNat < 2 ^ 63 := by omega
    have hspan : 64 * c + 64 ≤ sub := copyIterBound_step_le hlo hat' hgate
    have hgap : sub - (64 * c + 64) ≤ 64 := copyIterBound_exit hlo hat' hgate
    have hle : k.toNat ≤ sub := by omega
    have hmid : k.toNat + 32 ≤ sub := by omega
    have h64v : (BitVec.ofInt 64 64).toNat = 64 := by decide
    have hr1 : readBytes s.mem (src + k.toNat) 32 = some ((B.drop k.toNat).take 32) :=
      copySrc_read hwhole hle
    have hm : readBytes s.mem (src + k.toNat + 32) 32
        = some ((B.drop (k.toNat + 32)).take 32) := copySrc_read_mid hwhole hmid
    have hl1 : ((B.drop k.toNat).take 32).length = 32 := by
      refine copyChunk_length ?_
      rw [hBlen]; omega
    have hl2 : ((B.drop (k.toNat + 32)).take 32).length = 32 := by
      refine copyChunk_length ?_
      rw [hBlen]; omega
    have hfr := JsonEntrySteps.readBytes_writeBytes_frame s.mem ((B.drop k.toNat).take 32)
      (dst + k.toNat) (src + k.toNat + 32) 32 (by
        rcases hdisj with hd | hd
        · right; omega
        · left; omega)
    have hr2 : readBytes (writeBytes s.mem (dst + k.toNat) ((B.drop k.toNat).take 32))
        (src + k.toNat + 32) 32 = some ((B.drop (k.toNat + 32)).take 32) := by
      rw [hfr]
      exact hm
    have htest : copyTest sub k = (0 : BitVec 1) := by
      refine (evalICmp_ugt_zero_iff _ _).2 ?_
      rw [h64v, copyTest_toNat hkval hsub63 hspan]
      omega
    let e : State := CopyStepState copyBodyNNames udCopyBodyNEnv s src dst sub k
      ((B.drop k.toNat).take 32) ((B.drop (k.toNat + 32)).take 32) copyBodyNNames.tail
    have he : e = CopyStepState copyBodyNNames udCopyBodyNEnv s src dst sub k
        ((B.drop k.toNat).take 32) ((B.drop (k.toNat + 32)).take 32) copyBodyNNames.tail := rfl
    have hstep : step escapeCalls usDecFunction s = .jump e := by
      rw [he]
      exact udCopyBodyN_step_zero s.env s prev op src dst k _ _ (BitVec.ofNat 64 sub)
        hpc hprev hinc hop hsrc hdst hsubc hkNlt (by rw [BitVec.signExtend_eq]) hr1 hr2
        hl1 hl2 htest
    refine ⟨e, 1, by omega, ?_, ?_, fun k' => runFuel_jump_prefix hstep k'⟩
    · rw [he, CopyStepState_pc]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [he, CopyStepState_pc]
        · rw [he, CopyStepState_pre]
        · rw [he, CopyStepState_env,
            copyNEnv_knext s.env src dst k _ _ (BitVec.ofNat 64 sub),
            copyK_sum hkval, ← hc]
        · rw [he, CopyStepState_env, copyNEnv_snext s.env src dst k _ _ (BitVec.ofNat 64 sub)]
          have hv : BitVec.ofNat 64 sub - (k + BitVec.ofInt 64 64)
              = BitVec.ofNat 64 (sub - (64 * copyIterBound sub + 64)) := by
            refine BitVec.toNat_inj.1 ?_
            rw [copyTest_toNat hkval hsub63 hspan, BitVec.toNat_ofNat, ← hc,
              Nat.mod_eq_of_lt (by omega)]
          rw [hv]
        · rw [he, CopyStepState_env, copyNEnv_src s.env src dst k _ _ (BitVec.ofNat 64 sub)]
          exact hsrc
        · rw [he, CopyStepState_env, copyNEnv_dst s.env src dst k _ _ (BitVec.ofNat 64 sub)]
          exact hdst
        · rw [he, CopyStepState_env, copyNEnv_sub s.env src dst k _ _ (BitVec.ofNat 64 sub)]
          exact hsubc
        · rw [he, CopyStepState_mem, hkN]
          have hp : readBytes s.mem dst (64 * c) = some (B.take (64 * c)) := hprefix
          have hh := readBytes_copy2Mem_dst s.mem dst (64 * c) B _ _ hp rfl rfl
            (by rw [hBlen]; omega)
          rw [← hc]
          exact hh
        · rw [he, CopyStepState_mem]
          exact readBytes_copy2Mem_src hwhole hdisj hl1 hl2 (by omega)
      · -- the caller's prefix is below both writes
        rw [he, CopyStepState_mem]
        exact readBytes_copy2Mem_prefix hshift (by omega) hpref
      · -- and the visit's writes lie inside the destination extent
        rw [he, CopyStepState_mem]
        refine UnchangedOutside.writeBytes_inside
          (UnchangedOutside.writeBytes_inside hframe (by omega) (by omega))
          (by omega) (by omega)
      · -- the three carried cells survive the visit
        rw [he, CopyStepState_env]
        simp only [udCopyBodyNEnv]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact hjc
      · rw [he, CopyStepState_env]
        simp only [udCopyBodyNEnv]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact hkc
      · rw [he, CopyStepState_env]
        simp only [udCopyBodyNEnv]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact hxjc
  step_loop := by
    intro r s c h hat
    obtain ⟨hcopy, hpref, hframe, hjc, hkc, hxjc⟩ := h
    obtain ⟨prev, op, k, hpc, hprev, hinc, hop, hkval, hsrc, hdst, hsubc, hwhole,
      hBlen, hprefix, hdisj, hsub63, hgate, hlo, hhi⟩ := hcopy
    have hat' : ¬ copyIterBound sub ≤ c := by
      have := hat
      simp only [copyAtBound] at this
      exact of_decide_eq_false this
    have hcN : c < copyIterBound sub := by omega
    have hbnd := copyIterBound_mul_le sub
    have hkN : k.toNat = 64 * c := by
      rw [hkval, BitVec.toNat_ofNat]
      omega
    have hkNlt : k.toNat < 2 ^ 63 := by omega
    have hspan : 64 * c + 128 < sub := copyIterBound_advance hcN
    have hspan' : 64 * c + 64 ≤ sub := by omega
    have hle : k.toNat ≤ sub := by omega
    have hmid : k.toNat + 32 ≤ sub := by omega
    have h64v : (BitVec.ofInt 64 64).toNat = 64 := by decide
    have hr1 : readBytes s.mem (src + k.toNat) 32 = some ((B.drop k.toNat).take 32) :=
      copySrc_read hwhole hle
    have hm : readBytes s.mem (src + k.toNat + 32) 32
        = some ((B.drop (k.toNat + 32)).take 32) := copySrc_read_mid hwhole hmid
    have hl1 : ((B.drop k.toNat).take 32).length = 32 := by
      refine copyChunk_length ?_
      rw [hBlen]; omega
    have hl2 : ((B.drop (k.toNat + 32)).take 32).length = 32 := by
      refine copyChunk_length ?_
      rw [hBlen]; omega
    have hfr := JsonEntrySteps.readBytes_writeBytes_frame s.mem ((B.drop k.toNat).take 32)
      (dst + k.toNat) (src + k.toNat + 32) 32 (by
        rcases hdisj with hd | hd
        · right; omega
        · left; omega)
    have hr2 : readBytes (writeBytes s.mem (dst + k.toNat) ((B.drop k.toNat).take 32))
        (src + k.toNat + 32) 32 = some ((B.drop (k.toNat + 32)).take 32) := by
      rw [hfr]
      exact hm
    have htest : copyTest sub k = (1 : BitVec 1) := by
      refine (evalICmp_ugt_one_iff_toNat _ _).2 ?_
      rw [h64v, copyTest_toNat hkval hsub63 hspan']
      omega
    let e : State := CopyStepState copyBodyNNames udCopyBodyNEnv s src dst sub k
      ((B.drop k.toNat).take 32) ((B.drop (k.toNat + 32)).take 32) copyBodyNNames.head
    have he : e = CopyStepState copyBodyNNames udCopyBodyNEnv s src dst sub k
        ((B.drop k.toNat).take 32) ((B.drop (k.toNat + 32)).take 32) copyBodyNNames.head := rfl
    have hstep : step escapeCalls usDecFunction s = .jump e := by
      rw [he]
      exact udCopyBodyN_step s.env s prev op src dst k _ _ (BitVec.ofNat 64 sub)
        hpc hprev hinc hop hsrc hdst hsubc hkNlt (by rw [BitVec.signExtend_eq]) hr1 hr2
        hl1 hl2 htest
    refine ⟨e, c + 1, 1, by omega, ?_, by omega, ?_,
      fun k' => runFuel_jump_prefix hstep k'⟩
    · rw [he, CopyStepState_pc]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · refine ⟨copyBodyNNames.head, .reg copyBodyNNames.knext,
          k + BitVec.ofInt 64 64, rfl, rfl, copyBodyNNames_head_phi, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [he]
          simp only [evalOperand, CopyStepState_env]
          exact copyNEnv_knext s.env src dst k _ _ (BitVec.ofNat 64 sub)
        · exact copyNext_counter hkval
        · rw [he, CopyStepState_env, copyNEnv_src s.env src dst k _ _ (BitVec.ofNat 64 sub)]
          exact hsrc
        · rw [he, CopyStepState_env, copyNEnv_dst s.env src dst k _ _ (BitVec.ofNat 64 sub)]
          exact hdst
        · rw [he, CopyStepState_env, copyNEnv_sub s.env src dst k _ _ (BitVec.ofNat 64 sub)]
          exact hsubc
        · rw [he, CopyStepState_mem]
          exact readBytes_copy2Mem_src hwhole hdisj hl1 hl2 (by omega)
        · exact hBlen
        · rw [he, CopyStepState_mem, hkN]
          have hp : readBytes s.mem dst (64 * c) = some (B.take (64 * c)) := hprefix
          have hh := readBytes_copy2Mem_dst s.mem dst (64 * c) B _ _ hp rfl rfl
            (by rw [hBlen]; omega)
          rw [show 64 * c + 64 = 64 * (c + 1) from by omega] at hh
          exact hh
        · exact hdisj
        · exact hsub63
        · exact hgate
        · omega
        · omega
      · -- the caller's prefix is below both writes
        rw [he, CopyStepState_mem]
        exact readBytes_copy2Mem_prefix hshift (by omega) hpref
      · -- and the visit's writes lie inside the destination extent
        rw [he, CopyStepState_mem]
        refine UnchangedOutside.writeBytes_inside
          (UnchangedOutside.writeBytes_inside hframe (by omega) (by omega))
          (by omega) (by omega)
      · rw [he, CopyStepState_env]
        simp only [udCopyBodyNEnv]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact hjc
      · rw [he, CopyStepState_env]
        simp only [udCopyBodyNEnv]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact hkc
      · rw [he, CopyStepState_env]
        simp only [udCopyBodyNEnv]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact hxjc
  exit_at_zero := by
    intro s c h
    obtain ⟨hcopy, _, _, _, _, _⟩ := h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hhi⟩ := hcopy
    show decide (copyIterBound sub ≤ c) = true
    exact decide_eq_true (by omega)
  budget := by
    intro r s c h
    obtain ⟨hcopy, _, _, _, _, _⟩ := h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hlo, hhi⟩ := hcopy
    exact ⟨hlo, hhi⟩


/-! ### The source range past the walk's cursor -/

/-- The bytes at the final copy's source base: the body from the cursor plus the
thirty-two bytes the record promises past its end. -/
theorem finalSource_read {mem : Mem} {b n i : Nat} {body extra : List UInt8}
    (hb : readBytes mem b n = some body) (hi : i ≤ n)
    (hextra : readBytes mem (b + n) 32 = some extra) :
    readBytes mem (b + i) ((n - i) + 32) = some (body.drop i ++ extra) ∧
      (body.drop i ++ extra).length = (n - i) + 32 := by
  have hblen : body.length = n := JsonEntrySteps.readBytes_length mem b n hb
  have hextralen : extra.length = 32 := JsonEntrySteps.readBytes_length mem (b + n) 32 hextra
  have hb' : readBytes mem b (i + (n - i)) = some body := by
    rw [show i + (n - i) = n from by omega]
    exact hb
  obtain ⟨-, hmid⟩ := readBytes_split mem b i (n - i) hb'
  have hboth : readBytes mem (b + i) ((n - i) + 32) =
      some (body.drop i ++ extra) := by
    refine JsonEntrySteps.readBytes_append (m := mem) (n - i) (b + i) (body.drop i) 32 extra
      hmid ?_
    rwa [show b + i + (n - i) = b + n from by omega]
  refine ⟨hboth, ?_⟩
  rw [List.length_append, List.length_drop, hblen, hextralen]

/-- The source range's prefix at a counter inside the residual is the body from the
cursor. -/
theorem finalSource_take {body extra : List UInt8} {n i k : Nat}
    (hb : body.length = n) (h : i ≤ n) (hk : k ≤ n - i) :
    (body.drop i ++ extra).take k = (body.drop i).take k := by
  rw [List.take_append, List.length_drop, hb,
    show k - (n - i) = 0 from by omega, List.take_zero, List.append_nil]

/-! ### The decoded prefix is no longer than its cursor -/

/-- **The decoded prefix fits its cursor, from the staging's spacing.**  The
staging's walk and the exit's walk are the same decode written two ways:
`goal = .decoded (out ++ body.drop i) k`, and a walk whose position list is spaced
writes at most the body's length.  The list the staging decodes is
`(ps.map …).drop k0` — a *suffix* of the caller's list — and `Spaced` is not
suffix-closed on the nose (a `control`/`refuse` constructor's tail is unconstrained);
what carries the spacing across the drop is that the list is the body's own position
list, so every suffix of it is the cursor list at a later lane and
`escAt_drop_spaced` supplies the spacing.  The record's list clause is the only
thing read here beyond the invariant and the goal's own shape. -/
theorem DecodeInv.out_length_le_cursor {body : List UInt8} {st : ClassState}
    {M mem : Mem} {dst nps i k : Nat} {out : List UInt8} {goal : EscapeOutcome}
    {b n pos0 k0 : Nat} {ps : List Nat}
    (hinv : DecodeInv body st M dst nps i k out goal) (hk : k = nps)
    (hbody : readBytes mem b n = some body)
    (hwalkeq : goal = escapeDecodeGo body 0 k0
      ((ps.map (fun q => q - pos0)).drop k0) [])
    (hmap : ps.map (fun q => q - pos0) = escapePositionsFrom body st) :
    out.length ≤ i := by
  have hsp : Spaced body 0 ((ps.map (fun q => q - pos0)).drop k0) :=
    escapeExpand_spaced_drop hmap k0
  have hblen : body.length = n := JsonEntrySteps.readBytes_length mem b n hbody
  have hgoal := DecodeInv.exit hinv hk
  have hdec : escapeDecodeGo body 0 k0 ((ps.map (fun q => q - pos0)).drop k0) [] =
      .decoded (out ++ body.drop i) nps := by
    rw [← hwalkeq]
    simpa [hk] using hgoal
  have hle := escapeDecodeGo_length_le body hsp k0 [] (out ++ body.drop i) nps hdec
  simp only [List.length_nil, Nat.zero_add] at hle
  have h1 : (out ++ body.drop i).length = out.length + (body.length - i) := by
    rw [List.length_append, List.length_drop]
  rw [h1, hblen] at hle
  rcases Nat.le_total i n with hi | hi
  · have hsub : n - i + i = n := Nat.sub_add_cancel hi
    omega
  · have hsub : n - i = 0 := Nat.sub_eq_zero_of_le hi
    omega


/-! ### Reads outside the run's regions

The frame the exit words carry is a per-byte statement, and the final copy reads
regions the run does not write — the body and its thirty-two trailing bytes, the
offset slot.  These are the two lemmas that turn the frame into reads, and the two
that keep it across a store.
-/

/-- **Two reads of one range agree byte by byte.**  The read is a fold over the
per-byte form, so a pointwise equality on the range is a whole-read equality. -/
theorem readBytes_congr (m m' : Mem) :
    ∀ (k : Nat) {a : Nat}, (∀ x, a ≤ x → x < a + k → readByte m x = readByte m' x) →
      readBytes m a k = readBytes m' a k
  | 0, a, _ => rfl
  | k + 1, a, h => by
      simp only [readBytes]
      rw [h a (by omega) (by omega)]
      cases hb : readByte m' a with
      | none => rfl
      | some b =>
          rw [readBytes_congr m m' k (a := a + 1)
            (fun x h1 h2 => h x (by omega) (by omega))]

/-- **A read outside the run's regions is the caller's read.**  A whole range read
is the per-byte form of `UnchangedOutside`: if every address the read touches is
outside every region, the bytes are the caller's. -/
theorem readBytes_of_UnchangedOutside {m0 m : Mem} {regions : List (Nat × Nat)}
    {a k : Nat} (h : UnchangedOutside m0 m regions)
    (hout : ∀ x, a ≤ x → x < a + k → ∀ r ∈ regions, ¬ (r.1 ≤ x ∧ x < r.1 + r.2)) :
    readBytes m a k = readBytes m0 a k :=
  readBytes_congr m m0 k (fun x h1 h2 => h x (hout x h1 h2))

/-! ### The final copy's arithmetic

`while.end35` forms `%sub38 = %n - %i.0.lcssa` in 64-bit arithmetic and
`us_run.exit112` forms `%add40 = %sub38 + %j.0.lcssa`.  At a cursor inside the body
both are the `Nat` operations the record's `post` names, which is what these facts
state; outside it the subtraction wraps, which is the clause the latch's word does
not carry. -/

/-- **The residual's `Nat` reading.** -/
theorem ofNat_sub_toNat {n i : Nat} (hi : i ≤ n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n - BitVec.ofNat 64 i).toNat = n - i := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have hi' : (BitVec.ofNat 64 i).toNat = i := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hle : BitVec.ofNat 64 i ≤ BitVec.ofNat 64 n := by
    rw [BitVec.le_def, hi', hn']
    omega
  rw [BitVec.toNat_sub_of_le hle, hn', hi']

/-- The residual at a cursor inside the body, in the form the copy's invariant
carries. -/
theorem ofNat_sub_ofNat {n i : Nat} (hi : i ≤ n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 i = BitVec.ofNat 64 (n - i) := by
  refine BitVec.toNat_inj.1 ?_
  rw [ofNat_sub_toNat hi hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- A body's remainder is the source range's first `n - i` bytes. -/
theorem take_left_of_body {body extra : List UInt8} {i n : Nat}
    (hblen : body.length = n) (hi : i ≤ n) :
    (body.drop i ++ extra).take (n - i) = body.drop i := by
  rw [List.take_append, List.length_drop, hblen,
    show n - i - (n - i) = 0 from by omega, List.take_zero, List.append_nil,
    List.take_of_length_le (by rw [List.length_drop, hblen]; omega)]


/-! ### What the two `while.end35` branches do not carry

The final copy reads, at an exit state, three things the exit words do not mention,
and each is needed by the continuation:

* **the body's bytes, and its thirty-two trailing bytes**, at the *exit* state's
  memory — the copy's source range.  The frame the words carry excludes
  `(dst, n + 64)` and nothing else about the body's own region: the staging relates
  the body to the destination only, so a body byte that falls inside another region
  the frame excludes (the position list, the offset slot, the cursor) may differ at
  the exit memory and the words cannot tell;
* **the offset slot's read**, which the record's post reads back.  `(err, 8)` is one
  of the frame's regions, so the frame says nothing about it, and the success path
  never writes the slot — whatever the exit memory holds there is what the run
  returns;
* **at the latch, a byte cursor inside the body**.  `while.end35` forms
  `%sub38 = %n - %i.0.lcssa`, and `DecodeLatchExit`'s walk cursor is unbounded, so a
  cursor past `n` wraps the subtraction and the residual the copy is handed is
  `2 ^ 64 - (i - n)`.

The two witnesses below are reached at one staging, so what separates them from a
state the run leaves is exactly the clause named.  The staging is the same for both
because none of its clauses mentions any of the three: an empty body at `100`, an
empty position list at `700`, the rule's table at `400`, the offset slot at `800`,
the cursor at `900` and the destination at `200`, in a zero memory with the table
written at `400`.
-/

/-- The memory both witnesses are stated at. -/
def exitWitnessMem : Mem := writeBytes (zeroMem 1000) 400 unescapeTable

/-- The caller's argument list: the empty body at `100`, the destination at `200`,
the table at `400`, the empty list at `700`, the offset slot at `800` and the cursor
at `900`. -/
def exitWitnessArgs : List Value :=
  [.ptr 100, .int 64 (BitVec.ofNat 64 0), .ptr 200, .ptr 800, .ptr 700,
   .ptr 900, .int 64 (BitVec.ofNat 64 0), .int 64 (BitVec.ofNat 64 0), .ptr 400]

/-- A read below the table, out of the zero memory. -/
theorem exitWitness_zeros {a k : Nat} (h : a + k ≤ 400) :
    readBytes exitWitnessMem a k = some (List.replicate k (0 : UInt8)) := by
  unfold exitWitnessMem
  rw [readBytes_writeBytes_below (zeroMem 1000) unescapeTable k a 400 h]
  exact readBytes_zeroMem k 1000 a (by omega)

/-- A read above the table, out of the zero memory. -/
theorem exitWitness_zeros_high {a k : Nat} (hlow : 656 ≤ a) (hN : a + k ≤ 1000) :
    readBytes exitWitnessMem a k = some (List.replicate k (0 : UInt8)) := by
  unfold exitWitnessMem
  rw [JsonEntrySteps.readBytes_writeBytes_above (zeroMem 1000) unescapeTable k a 400
    (by rw [unescapeTable_length]; omega)]
  exact readBytes_zeroMem k 1000 a (by omega)

/-- The table's own read. -/
theorem exitWitness_table :
    readBytes exitWitnessMem 400 256 = some unescapeTable := by
  unfold exitWitnessMem
  simpa [unescapeTable_length] using
    readBytes_writeBytes_same (zeroMem 1000) unescapeTable (addr := 400)

/-- The zero word's own eight bytes. -/
theorem wordBytes_rep_eight : wordBytes 8 0 = List.replicate 8 (0 : UInt8) := by decide

/-- The empty position list is the body's own. -/
theorem exitWitness_escAt : escAt ([] : List UInt8) ⟨true, false⟩ 0 = [] := by
  simp [escAt]

/-- **The staging both witnesses are reached from.** -/
theorem exitWitness_staging :
    ExpandStaging exitWitnessArgs exitWitnessMem 0 [] ⟨true, false⟩ 200 0
      (.decoded [] 0) 100 700 400 0 0 [] 800 900 := by
  unfold ExpandStaging Γ_escape_expand_at
  have hz32 : readBytes exitWitnessMem 100 32 = some (List.replicate 32 (0 : UInt8)) :=
    exitWitness_zeros (by omega)
  have hz64 : ∃ vs, readBytes exitWitnessMem 200 64 = some vs :=
    ⟨_, exitWitness_zeros (by omega)⟩
  have hz8e : readBytes exitWitnessMem 800 8 = some (wordBytes 8 0) := by
    rw [exitWitness_zeros_high (by omega) (by omega), wordBytes_rep_eight]
  have hz8x : readBytes exitWitnessMem 900 8 = some (wordBytes 8 0) := by
    rw [exitWitness_zeros_high (by omega) (by omega), wordBytes_rep_eight]
  have hpre : readBytes exitWitnessMem 100 0 = some [] := rfl
  have hxp0 : readBytes exitWitnessMem 700 0 = some (positionsBytes 4 []) := rfl
  refine ⟨?_, rfl, rfl, hpre, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the record's `pre`
    refine ⟨100, 0, 200, 800, 700, 900, 0, 0, 400, [], [], 0, 0, rfl, hpre,
      hxp0, rfl, (fun q hq => absurd hq (by simp)), (by simp [escapePositionsFrom, escAt]),
      (by omega), hz8x, (by omega), hz8e, exitWitness_table, ⟨_, hz32⟩, hz64,
      (by omega), (by omega), (by omega), (by omega), (by omega), (by omega)⟩
  · -- `DecodeStaging`
    exact ⟨0, hxp0, rfl, (fun j q hq => absurd hq (by simp)), rfl⟩
  · simp [escapePositionsFrom, escAt]
  · unfold DecodeNoAlias
    refine ⟨by omega, by omega, by omega, by omega⟩
  · omega
  · omega
  · refine ⟨0, hz8x, by omega, ?_⟩
    simp [escapeDecodeGo_nil]

/-- **The entry branch as the exit word stated it before the written extent was
pinned.**  The frame names the position list, the cursor slot and the offset slot
among its regions, so it says nothing about any of them, and the branch states no
read of the body's own bytes.

This is the shape `entryExit_admits_clobbered_err` and
`bodyExit_admits_clobbered_body` are stated at, and no consumer reads it: the exit
word's own branch is `AssemblyEntryExit`, whose frame is the destination extent
alone.  The two witnesses stay as the executable reason for that pinning. -/
def AssemblyEntryExitFrameOnly (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (b xp tab : Nat) (pos0 n : Nat) (ps : List Nat)
    (err xj : Nat) (mem : Mem) (e : State) : Prop :=
  e.pc = "while.end35" ∧ e.pre = some "while.end" ∧
  DecodeInv body st e.mem dst nps 0 nps [] goal ∧
  lookupName e.env "%k.0.lcssa" = some (.int 64 (BitVec.ofNat 64 nps)) ∧
  lookupName e.env "%p" = some (.ptr b) ∧
  lookupName e.env "%xp" = some (.ptr xp) ∧
  lookupName e.env "%tab" = some (.ptr tab) ∧
  lookupName e.env "%pos0" = some (.int 64 (BitVec.ofNat 64 pos0)) ∧
  lookupName e.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) ∧
  lookupName e.env "%err" = some (.ptr err) ∧
  lookupName e.env "%xj" = some (.ptr xj) ∧
  UnchangedOutside mem e.mem [(dst, n + 64), (xp, 4 * nps), (xj, 8), (err, 8)]

/-- **The latch branch without the cursor's bound.**  The frame again names the
position list, the cursor slot and the offset slot, and `%add24` is free.  This is
the shape `latchExit_admits_cursor_past_body` is stated at. -/
def AssemblyLatchExitUnbounded (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (b xp tab : Nat) (pos0 n : Nat) (ps : List Nat)
    (err xj : Nat) (mem : Mem) (e : State) : Prop :=
  e.pc = "while.end35" ∧ e.pre = some "cleanup32" ∧
  (∃ c : Nat, DecodeLatchExit body st dst nps goal c e) ∧
  lookupName e.env "%p" = some (.ptr b) ∧
  lookupName e.env "%xp" = some (.ptr xp) ∧
  lookupName e.env "%tab" = some (.ptr tab) ∧
  lookupName e.env "%pos0" = some (.int 64 (BitVec.ofNat 64 pos0)) ∧
  lookupName e.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) ∧
  lookupName e.env "%err" = some (.ptr err) ∧
  lookupName e.env "%xj" = some (.ptr xj) ∧
  UnchangedOutside mem e.mem [(dst, n + 64), (xp, 4 * nps), (xj, 8), (err, 8)]

/-- The entry-edge state whose offset slot holds `7`s where the caller holds
zeros: the walk's seed, the `while.end35` cells, and the frame's regions. -/
def entryClobberedErrState : State :=
  modelState
    [("%k.0.lcssa", .int 64 0), ("%p", .ptr 100), ("%xp", .ptr 700),
     ("%tab", .ptr 400), ("%pos0", .int 64 0), ("%n", .int 64 0),
     ("%err", .ptr 800), ("%xj", .ptr 900), ("%dst", .ptr 200)]
    (writeBytes exitWitnessMem 800 (List.replicate 8 (7 : UInt8)))
    "while.end35" (some "while.end")

theorem entryClobberedErr_frame :
    UnchangedOutside exitWitnessMem entryClobberedErrState.mem
      [(200, 0 + 64), (700, 4 * 0), (900, 8), (800, 8)] := by
  intro a ha
  have hd : a < 800 ∨ 800 + 8 ≤ a := by
    rcases Nat.lt_or_ge a 800 with h | h
    · exact Or.inl h
    · exact Or.inr (by
        have := ha (800, 8) (by simp)
        omega)
  rw [show entryClobberedErrState.mem
      = writeBytes exitWitnessMem 800 (List.replicate 8 (7 : UInt8)) from rfl,
    readByte_writeBytes_outside _ _ (by simpa using hd)]

theorem entryClobberedErr_slot :
    readBytes entryClobberedErrState.mem 800 8
      = some (List.replicate 8 (7 : UInt8)) := by
  unfold entryClobberedErrState modelState
  exact readBytes_writeBytes_same exitWitnessMem (List.replicate 8 (7 : UInt8))
    (addr := 800)

/-- **The entry branch admits an offset slot the run will not overwrite.**  The
state is the word's entry edge at the witness staging, with the offset slot's eight
bytes replaced: the frame names `(err, 8)` as a region, so the word does not read the
slot, and the success path writes only the destination and the cursor. -/
theorem entryExit_admits_clobbered_err :
    ∃ e : State,
      AssemblyEntryExitFrameOnly [] ⟨true, false⟩ 200 0 (.decoded [] 0) 100 700 400
        0 0 [] 800 900 exitWitnessMem e ∧
      readBytes e.mem 800 8 ≠ readBytes exitWitnessMem 800 8 := by
  refine ⟨entryClobberedErrState, ?_, ?_⟩
  · refine ⟨rfl, rfl, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- the walk's seed
      show escapeDecodeGo [] 0 0 ((escAt [] ⟨true, false⟩ 0).drop 0) [] = .decoded [] 0
      rw [exitWitness_escAt, List.drop_zero]
      exact escapeDecodeGo_nil ([] : List UInt8) 0 0 []
    · rfl
    · show (escAt ([] : List UInt8) ⟨true, false⟩ 0).length = 0
      rw [exitWitness_escAt]; rfl
    all_goals (first
      | exact entryClobberedErr_frame
      | rfl
      | (simp only [entryClobberedErrState, modelState, lookupName]; simp))
  · -- the slot differs
    intro hcontra
    have h2 : readBytes exitWitnessMem 800 8 = some (List.replicate 8 (0 : UInt8)) :=
      exitWitness_zeros_high (by omega) (by omega)
    rw [entryClobberedErr_slot, h2] at hcontra
    exact absurd hcontra (by decide)

/-- **The repaired entry branch excludes the clobbered offset slot.**  The frame now
names only the destination extent, so the slot's bytes are the caller's by
`UnchangedOutside`, and the word cannot admit a state that rewrites them. -/
theorem entryExit_clobbered_err_excluded :
    ¬ assemblyExitWord exitWitnessArgs exitWitnessMem 0 [] ⟨true, false⟩ 200 0
        (.decoded [] 0) 100 700 400 0 0 [] 800 900 entryClobberedErrState := by
  intro h
  have h2 : readBytes exitWitnessMem 800 8 = some (List.replicate 8 (0 : UInt8)) :=
    exitWitness_zeros_high (by omega) (by omega)
  rcases h.2 with hL | hE | h6 | hB | hS | hR
  · obtain ⟨-, hpre, -⟩ := hL
    exact absurd hpre (by decide)
  · -- the repaired entry branch's frame relates the slot
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hfr⟩ := hE
    have hread := readBytes_of_UnchangedOutside hfr
      (a := 800) (k := 8) (fun x h1 h2 r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr
        omega)
    rw [entryClobberedErr_slot, h2] at hread
    exact absurd hread (by decide)
  · obtain ⟨-, hpre, -⟩ := h6
    exact absurd hpre (by decide)
  · obtain ⟨-, hpre, -⟩ := hB
    exact absurd hpre (by decide)
  · obtain ⟨hpc, -⟩ := hS
    exact absurd hpc (by decide)
  · obtain ⟨hdref, -⟩ := hR
    obtain ⟨hpc, -⟩ := hdref
    exact absurd hpc (by decide)

/-- The latch-edge state whose `%add24` is `5` for a zero-length body. -/
def latchCursorPastBodyState : State :=
  modelState
    [("%j.3", .int 64 0), ("%add24", .int 64 (BitVec.ofNat 64 5)),
     ("%add28", .int 64 0), ("%p", .ptr 100), ("%dst", .ptr 200),
     ("%xp", .ptr 700), ("%tab", .ptr 400), ("%err", .ptr 800),
     ("%xj", .ptr 900), ("%pos0", .int 64 0), ("%add", .int 64 0),
     ("%n", .int 64 0)]
    exitWitnessMem "while.end35" (some "cleanup32")

theorem latchCursorPastBody_add24 :
    lookupName latchCursorPastBodyState.env "%add24"
      = some (.int 64 (BitVec.ofNat 64 5)) := by
  simp only [latchCursorPastBodyState, modelState, lookupName]
  simp

/-- **The latch branch admits a byte cursor past the body.**  At the same staging, a
state whose `%add24` — the cell `while.end35` copies into `%i.0.lcssa` — is `5` for a
zero-length body satisfies the word: the walk at cursor `5` has the same outcome
(`.decoded [] 0`), because the trailing copy's `body.drop 5` is empty.  `while.end35`
then forms `%sub38 = 0 - 5`, and the copy's residual wraps. -/
theorem latchExit_admits_cursor_past_body :
    ∃ e : State,
      AssemblyLatchExitUnbounded [] ⟨true, false⟩ 200 0 (.decoded [] 0) 100 700 400
        0 0 [] 800 900 exitWitnessMem e ∧
      lookupName e.env "%add24" = some (.int 64 (BitVec.ofNat 64 5)) := by
  have hframe : UnchangedOutside exitWitnessMem latchCursorPastBodyState.mem
      [(200, 0 + 64), (700, 4 * 0), (900, 8), (800, 8)] := fun a _ => rfl
  refine ⟨latchCursorPastBodyState, ?_, latchCursorPastBody_add24⟩
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the walk's exit data, at cursor `5`
    refine ⟨0, 5, [], BitVec.ofNat 64 0, BitVec.ofNat 64 5, BitVec.ofNat 64 0,
      100, 700, 400, 800, 900, BitVec.ofNat 64 0, 0, BitVec.ofNat 64 0, ?_⟩
    refine ⟨rfl, ⟨?_, ?_, ?_⟩, rfl, rfl, (by decide), rfl, (by decide), rfl,
      (by decide), rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · show escapeDecodeGo [] 5 0 ((escAt [] ⟨true, false⟩ 0).drop 0) [] = .decoded [] 0
      rw [exitWitness_escAt, List.drop_zero]
      exact escapeDecodeGo_nil ([] : List UInt8) 0 0 []
    · rfl
    · show (escAt ([] : List UInt8) ⟨true, false⟩ 0).length = 0
      rw [exitWitness_escAt]; rfl
  all_goals solve
    | exact hframe
    | (simp only [latchCursorPastBodyState, modelState, lookupName]; simp)

/-- **The repaired latch branch excludes the cursor past the body.**  The branch now
bounds `%add24` by `n`, and the witness's cell is `5` where `n` is `0`. -/
theorem latchExit_cursor_excluded :
    ¬ assemblyExitWord exitWitnessArgs exitWitnessMem 0 [] ⟨true, false⟩ 200 0
        (.decoded [] 0) 100 700 400 0 0 [] 800 900 latchCursorPastBodyState := by
  intro h
  rcases h.2 with hL | hE | h6 | hB | hS | hR
  · obtain ⟨-, -, -, ⟨add24, hcell, hle⟩, -⟩ := hL
    rw [latchCursorPastBody_add24] at hcell
    have hadd : (BitVec.ofNat 64 5 : BitVec 64) = add24 := by
      injection hcell with hv
      injection hv with _ h
    rw [← hadd] at hle
    exact absurd hle (by decide)
  · obtain ⟨-, hpre, -⟩ := hE
    exact absurd hpre (by decide)
  · obtain ⟨-, hpre, -⟩ := h6
    exact absurd hpre (by decide)
  · obtain ⟨-, hpre, -⟩ := hB
    exact absurd hpre (by decide)
  · obtain ⟨hpc, -⟩ := hS
    exact absurd hpc (by decide)
  · obtain ⟨hdref, -⟩ := hR
    obtain ⟨hpc, -⟩ := hdref
    exact absurd hpc (by decide)

/-! ### The body's own bytes at the exit memory

The continuation from `while.end35` is the final copy, and the copy's source range
is read at the **exit state's** memory: `body.drop i` from `b + i` and the
thirty-two bytes the record promises past the body's end.  The frame was the only
clause relating the exit memory to the caller's, and it named the position list,
the cursor slot and the offset slot as regions, so a body byte that falls inside
one of them was free at the exit — even though the run writes none of them before
`while.end35`.  The witness below is such a state: a four-byte body at `100`, an
empty position list, and the offset slot at `101`, inside the body's own bytes.  The
run writes the offset slot only on a refusal, so the caller's body must read back
unchanged; the wide frame admits a state where it does not.

The narrower frame — the destination extent alone — is what excludes it. -/

/-- The body the body-bytes witness decodes: a quote, which takes the classifier
out of the string, and three control bytes that are therefore not escape
positions. -/
def bodyWitnessBody : List UInt8 := [0x22, 0x00, 0x00, 0x00]

/-- The witness memory: the exit witness's memory with the body written at `100`. -/
def bodyWitnessMem : Mem := writeBytes exitWitnessMem 100 bodyWitnessBody

/-- A read past the body's four bytes is the exit witness's read. -/
theorem bodyWitness_above {a k : Nat} (h : 104 ≤ a) :
    readBytes bodyWitnessMem a k = readBytes exitWitnessMem a k := by
  unfold bodyWitnessMem
  exact JsonEntrySteps.readBytes_writeBytes_above exitWitnessMem bodyWitnessBody k a 100
    (by simp [bodyWitnessBody]; omega)

theorem bodyWitness_body : readBytes bodyWitnessMem 100 4 = some bodyWitnessBody := by
  unfold bodyWitnessMem
  have hlen : bodyWitnessBody.length = 4 := rfl
  rw [← hlen]
  exact readBytes_writeBytes_same exitWitnessMem bodyWitnessBody (addr := 100)

/-- The offset slot at `101` lies inside the body's own four bytes; the three bytes
it shares with them are zeros, so the slot still reads the zero word. -/
theorem bodyWitness_err : readBytes bodyWitnessMem 101 8 = some (wordBytes 8 0) := by
  obtain ⟨-, htail⟩ := readBytes_split bodyWitnessMem 100 1 3 (bs := bodyWitnessBody) (by
    rw [show (1 : Nat) + 3 = 4 from rfl]; exact bodyWitness_body)
  have h3 : readBytes bodyWitnessMem 101 3 = some [0, 0, 0] := by
    simpa [bodyWitnessBody] using htail
  have h5 : readBytes bodyWitnessMem 104 5 = some (List.replicate 5 0) := by
    rw [bodyWitness_above (by omega)]
    exact exitWitness_zeros (by omega)
  have h8 := JsonEntrySteps.readBytes_append bodyWitnessMem 3 101 [0, 0, 0] 5
    (List.replicate 5 0) h3 h5
  rw [show (3 : Nat) + 5 = 8 from rfl] at h8
  rw [h8, wordBytes_rep_eight]
  rfl

theorem bodyWitness_xj : readBytes bodyWitnessMem 300 8 = some (wordBytes 8 0) := by
  rw [bodyWitness_above (by omega), exitWitness_zeros (by omega), wordBytes_rep_eight]

theorem bodyWitness_table :
    readBytes bodyWitnessMem 400 256 = some unescapeTable := by
  rw [bodyWitness_above (by omega)]
  exact exitWitness_table

theorem bodyWitness_tail : ∃ bs, readBytes bodyWitnessMem 104 32 = some bs :=
  ⟨_, by rw [bodyWitness_above (by omega)]; exact exitWitness_zeros (by omega)⟩

theorem bodyWitness_dst : ∃ bs, readBytes bodyWitnessMem 200 68 = some bs :=
  ⟨_, by rw [bodyWitness_above (by omega)]; exact exitWitness_zeros (by omega)⟩

/-- The caller's argument list at the body-bytes witness. -/
def bodyWitnessArgs : List Value :=
  [.ptr 100, .int 64 (BitVec.ofNat 64 4), .ptr 200, .ptr 101, .ptr 500,
   .ptr 300, .int 64 (BitVec.ofNat 64 0), .int 64 (BitVec.ofNat 64 0), .ptr 400]

theorem bodyWitness_escAt :
    escAt bodyWitnessBody ⟨true, false⟩ 0 = [] := by decide

theorem bodyWitness_positions :
    escapePositionsFrom bodyWitnessBody ⟨true, false⟩ = [] := by decide

theorem bodyWitness_staging :
    ExpandStaging bodyWitnessArgs bodyWitnessMem 0 bodyWitnessBody ⟨true, false⟩ 200 0
      (.decoded bodyWitnessBody 0) 100 500 400 0 4 [] 101 300 := by
  unfold ExpandStaging Γ_escape_expand_at
  refine ⟨?_, rfl, rfl, bodyWitness_body, by omega, ?_, ?_, ?_, by omega, by omega, ?_⟩
  · -- the record's `pre`
    refine ⟨100, 4, 200, 101, 500, 300, 0, 0, 400, bodyWitnessBody, [], 0, 0, rfl,
      bodyWitness_body, ?_, rfl, (fun q hq => absurd hq (by simp)), ?_, by omega,
      bodyWitness_xj, by omega, bodyWitness_err, bodyWitness_table,
      bodyWitness_tail, bodyWitness_dst, by omega, by omega, by omega, by omega,
      by omega, by omega⟩
    · rfl
    · show ([] : List Nat).map (fun q => q - 0)
          = escapePositionsFrom bodyWitnessBody ⟨true, false⟩
      rw [bodyWitness_positions]
      rfl
  · -- `DecodeStaging`
    refine ⟨BitVec.ofNat 64 4, ?_, rfl, (fun j q hq => absurd hq (by simp)), by decide⟩
    rfl
  · show ([] : List Nat).map (fun q => q - 0)
        = escapePositionsFrom bodyWitnessBody ⟨true, false⟩
    rw [bodyWitness_positions]
    rfl
  · unfold DecodeNoAlias
    refine ⟨by omega, by omega, by omega, by omega⟩
  · refine ⟨0, bodyWitness_xj, by omega, ?_⟩
    simp [List.drop_zero, escapeDecodeGo_nil]

/-- The body-bytes state: the same exit edge, with the eight bytes at the offset
slot replaced by `0xFF` — inside the body's own four bytes, so the body's read
differs from the caller's. -/
def bodyClobberedWitnessState : State :=
  modelState
    [("%k.0.lcssa", .int 64 0), ("%p", .ptr 100), ("%xp", .ptr 500),
     ("%tab", .ptr 400), ("%pos0", .int 64 0), ("%n", .int 64 4),
     ("%err", .ptr 101), ("%xj", .ptr 300), ("%dst", .ptr 200)]
    (writeBytes bodyWitnessMem 101 (List.replicate 8 (0xFF : UInt8)))
    "while.end35" (some "while.end")

theorem bodyClobberedWitness_frame :
    UnchangedOutside bodyWitnessMem bodyClobberedWitnessState.mem
      [(200, 4 + 64), (500, 4 * 0), (300, 8), (101, 8)] := by
  intro a ha
  have hd : a < 101 ∨ 101 + 8 ≤ a := by
    rcases Nat.lt_or_ge a 101 with h | h
    · exact Or.inl h
    · exact Or.inr (by
        have := ha (101, 8) (by simp)
        omega)
  rw [show bodyClobberedWitnessState.mem
      = writeBytes bodyWitnessMem 101 (List.replicate 8 (0xFF : UInt8)) from rfl,
    readByte_writeBytes_outside _ _ (by simpa using hd)]

/-- The clobbered state's body read: the first body byte survives the write at
`101`, and the next three are the write's own bytes. -/
theorem bodyClobberedWitness_body :
    readBytes bodyClobberedWitnessState.mem 100 4
      = some ([0x22, 0xFF, 0xFF, 0xFF] : List UInt8) := by
  have h0 : readBytes bodyClobberedWitnessState.mem 100 1 = some [0x22] := by
    rw [show bodyClobberedWitnessState.mem
        = writeBytes bodyWitnessMem 101 (List.replicate 8 (0xFF : UInt8)) from rfl,
      readBytes_writeBytes_below bodyWitnessMem _ 1 100 101 (by omega)]
    obtain ⟨h1, -⟩ := readBytes_split bodyWitnessMem 100 1 3
      (bs := bodyWitnessBody) (by
        rw [show (1 : Nat) + 3 = 4 from rfl]; exact bodyWitness_body)
    simpa [bodyWitnessBody] using h1
  have h3 : readBytes bodyClobberedWitnessState.mem 101 3
      = some (List.replicate 3 (0xFF : UInt8)) := by
    rw [show bodyClobberedWitnessState.mem
        = writeBytes bodyWitnessMem 101 (List.replicate 8 (0xFF : UInt8)) from rfl]
    obtain ⟨h1, -⟩ := readBytes_split
      (writeBytes bodyWitnessMem 101 (List.replicate 8 (0xFF : UInt8))) 101 3 5
      (bs := List.replicate 8 (0xFF : UInt8)) (readBytes_writeBytes_same _ _)
    simpa using h1
  have hw := JsonEntrySteps.readBytes_append bodyClobberedWitnessState.mem 1 100 [0x22] 3
    (List.replicate 3 (0xFF : UInt8)) h0 h3
  rw [show (1 : Nat) + 3 = 4 from rfl] at hw
  rw [hw]
  rfl

/-- **The entry branch admits a body read the run does not leave.**  The offset slot
sits inside the body's own four bytes, and the frame names it as a region, so the
word admits a state whose body read at the exit memory differs from the caller's.
The continuation's source range is exactly that read. -/
theorem bodyExit_admits_clobbered_body :
    ∃ e : State,
      AssemblyEntryExitFrameOnly bodyWitnessBody ⟨true, false⟩ 200 0
        (.decoded bodyWitnessBody 0) 100 500 400 0 4 [] 101 300 bodyWitnessMem e ∧
      readBytes e.mem 100 4 ≠ some bodyWitnessBody := by
  refine ⟨bodyClobberedWitnessState, ?_, ?_⟩
  · refine ⟨rfl, rfl, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- the walk's seed: the body, nothing stored, no positions
      show escapeDecodeGo bodyWitnessBody 0 0
        ((escAt bodyWitnessBody ⟨true, false⟩ 0).drop 0) [] =
          .decoded bodyWitnessBody 0
      rw [bodyWitness_escAt]
      simp [escapeDecodeGo_nil]
    · rfl
    · show (escAt bodyWitnessBody ⟨true, false⟩ 0).length = 0
      rw [bodyWitness_escAt]
      rfl
    all_goals (first
      | exact bodyClobberedWitness_frame
      | rfl
      | (simp only [bodyClobberedWitnessState, modelState, lookupName]; simp))
  · rw [bodyClobberedWitness_body]
    decide
/-- **The repaired entry branch excludes the clobbered body.**  Its frame names only
the destination extent, so every byte of the body's four-byte read is the caller's,
and `body.drop 0` is the body the staging names. -/
theorem bodyExit_clobbered_body_excluded :
    ¬ assemblyExitWord bodyWitnessArgs bodyWitnessMem 0 bodyWitnessBody ⟨true, false⟩
        200 0 (.decoded bodyWitnessBody 0) 100 500 400 0 4 [] 101 300
        bodyClobberedWitnessState := by
  intro h
  rcases h.2 with hL | hE | h6 | hB | hS | hR
  · obtain ⟨-, hpre, -⟩ := hL
    exact absurd hpre (by decide)
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hfr⟩ := hE
    have hread := readBytes_of_UnchangedOutside hfr
      (a := 100) (k := 4) (fun x h1 h2 r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr
        omega)
    rw [bodyWitness_body, bodyClobberedWitness_body] at hread
    exact absurd hread (by decide)
  · obtain ⟨-, hpre, -⟩ := h6
    exact absurd hpre (by decide)
  · obtain ⟨-, hpre, -⟩ := hB
    exact absurd hpre (by decide)
  · obtain ⟨hpc, -⟩ := hS
    exact absurd hpc (by decide)
  · obtain ⟨hdref, -⟩ := hR
    obtain ⟨hpc, -⟩ := hdref
    exact absurd hpc (by decide)

/-! ### The destination cell at the entry edge

`while.end35` forms the final copy's destination base as `%add.ptr37 = %dst +
%j.0.lcssa`, so the block reads the register.  The entry branch named every cell of
the edge except `%dst`: the walk's `stored` clause and the frame speak about the
number `dst`, not about the register, so nothing tied the two, and a state with
`%dst` moved by thirty-two bytes satisfied every clause.  At such a state the run
copies the body at `dst + 32` — inside the destination extent, which is why the
frame is no help — and `cleanup41` returns the decoded length, while the post
reads the caller's bytes at `dst`.  The sibling branch pins the cell through
`DecodeLatchExit`, so the omission was the entry edge's alone.

The witness below is stated at the branch as it stood, and the exclusion at the
word as it now stands. -/

/-- **The entry branch as it stood before the destination cell was pinned.**  The
seed's walk, the edge's cells and the destination extent as the frame, with `%dst`
free.  This is the shape `entryExit_admits_free_dst` is stated at; no consumer
reads it, because the exit word's own branch is `AssemblyEntryExit`. -/
def AssemblyEntryExitFreeDst (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (b xp tab : Nat) (pos0 n : Nat) (ps : List Nat)
    (err xj : Nat) (mem : Mem) (e : State) : Prop :=
  e.pc = "while.end35" ∧ e.pre = some "while.end" ∧
  DecodeInv body st e.mem dst nps 0 nps [] goal ∧
  lookupName e.env "%k.0.lcssa" = some (.int 64 (BitVec.ofNat 64 nps)) ∧
  lookupName e.env "%p" = some (.ptr b) ∧
  lookupName e.env "%xp" = some (.ptr xp) ∧
  lookupName e.env "%tab" = some (.ptr tab) ∧
  lookupName e.env "%pos0" = some (.int 64 (BitVec.ofNat 64 pos0)) ∧
  lookupName e.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) ∧
  lookupName e.env "%err" = some (.ptr err) ∧
  lookupName e.env "%xj" = some (.ptr xj) ∧
  UnchangedOutside mem e.mem [(dst, n + 64)]

/-- The entry-edge state whose `%dst` is `dst + 32`: the body-bytes witness's
staging cells and memory, with the destination cell moved. -/
def entryDstWitnessState : State :=
  modelState
    [("%k.0.lcssa", .int 64 0), ("%p", .ptr 100), ("%xp", .ptr 500),
     ("%tab", .ptr 400), ("%pos0", .int 64 0), ("%n", .int 64 4),
     ("%err", .ptr 101), ("%xj", .ptr 300), ("%dst", .ptr 232)]
    bodyWitnessMem "while.end35" (some "while.end")

theorem entryDstWitness_dst :
    lookupName entryDstWitnessState.env "%dst" = some (.ptr 232) := by
  simp only [entryDstWitnessState, modelState, lookupName]
  simp

/-- **The entry branch admits a destination cell the run does not honour.**  Every
other cell is the staging's, and the frame is the destination extent written at the
caller's `dst`; the register the block reads for `%add.ptr37` is thirty-two bytes
away from it. -/
theorem entryExit_admits_free_dst :
    ∃ e : State,
      AssemblyEntryExitFreeDst bodyWitnessBody ⟨true, false⟩ 200 0
        (.decoded bodyWitnessBody 0) 100 500 400 0 4 [] 101 300 bodyWitnessMem e ∧
      lookupName e.env "%dst" = some (.ptr 232) := by
  refine ⟨entryDstWitnessState, ?_, entryDstWitness_dst⟩
  unfold AssemblyEntryExitFreeDst
  refine ⟨rfl, rfl, ⟨?_, ?_, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · -- the seed's walk: the body, nothing stored, no positions
    show escapeDecodeGo bodyWitnessBody 0 0
      ((escAt bodyWitnessBody ⟨true, false⟩ 0).drop 0) [] =
        .decoded bodyWitnessBody 0
    rw [bodyWitness_escAt]
    simp [escapeDecodeGo_nil]
  · rfl
  · show (escAt bodyWitnessBody ⟨true, false⟩ 0).length = 0
    rw [bodyWitness_escAt]
    rfl
  · intro a _
    rfl

/-- **The repaired entry branch excludes the moved destination cell.**  The branch
now pins `%dst`, and the witness's cell is `dst + 32`. -/
theorem entryExit_free_dst_excluded :
    ¬ assemblyExitWord bodyWitnessArgs bodyWitnessMem 0 bodyWitnessBody ⟨true, false⟩
        200 0 (.decoded bodyWitnessBody 0) 100 500 400 0 4 [] 101 300
        entryDstWitnessState := by
  intro h
  rcases h.2 with hL | hE | h6 | hB | hS | hR
  · obtain ⟨-, hpre, -⟩ := hL
    exact absurd hpre (by decide)
  · obtain ⟨-, -, -, -, -, hdst, -⟩ := hE
    rw [entryDstWitness_dst] at hdst
    exact absurd hdst (by decide)
  · obtain ⟨-, hpre, -⟩ := h6
    exact absurd hpre (by decide)
  · obtain ⟨-, hpre, -⟩ := hB
    exact absurd hpre (by decide)
  · obtain ⟨hpc, -⟩ := hS
    exact absurd hpc (by decide)
  · obtain ⟨hdref, -⟩ := hR
    obtain ⟨hpc, -⟩ := hdref
    exact absurd hpc (by decide)

/-! ### The exit's allowance

The final copy's whole contribution is its trip bound plus the return: `while.end35`
into the copy, `copyIterBound (n - i) + 1` steps round it, the tail's two or three
steps, and `cleanup41`'s return.  The residual is at most the body's length, so
`copyIterBound_le_div` places the bound inside `n / 64 + 1`, and the total inside the
`n / 64 + 7` the exit budget names — the arithmetic the composition's last stage
consumes.
-/

/-- **The exit's allowance covers the final copy and the return.** -/
theorem finalCopy_fuel_le {n i : Nat} (hi : i ≤ n) :
    copyIterBound (n - i) + 6 ≤ n / 64 + 7 := by
  have hle := copyIterBound_le_div (n := n) (Nat.sub_le n i)
  unfold copyIterBound at hle ⊢
  omega

/-- The exit's allowance at the caller's own `n`. -/
theorem expandExitFuel_eq {b n dst err xp xj nps pos0 tab : Nat} (hn : n < 2 ^ 64) :
    expandExitFuel [.ptr b, .int 64 (BitVec.ofNat 64 n), .ptr dst, .ptr err, .ptr xp,
      .ptr xj, .int 64 (BitVec.ofNat 64 nps), .int 64 (BitVec.ofNat 64 pos0), .ptr tab]
      = n / 64 + 7 := by
  simp only [expandExitFuel, expandBodyLen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

/-- **A narrower frame implies a wider one.**  A frame over fewer regions says more:
a byte outside the wider list is outside the narrower one too, so the narrower
frame's equality is the wider frame's.  The exit word's region list is the
destination extent alone, and the record's `post` names four. -/
theorem UnchangedOutside.mono {m0 m : Mem} {R R' : List (Nat × Nat)}
    (h : UnchangedOutside m0 m R') (hsub : ∀ r ∈ R', r ∈ R) :
    UnchangedOutside m0 m R :=
  fun a ha => h a (fun r hr => ha r (hsub r hr))

/-- **The body reads as the caller's at the exit memory.**  The body's extent is
disjoint from the destination extent the run writes; the exit word's frame is that
extent alone. -/
theorem exitBody_read {mem M : Mem} {b n dst : Nat} {body : List UInt8}
    (hdisj : b + n + 32 ≤ dst ∨ dst + n + 64 ≤ b)
    (hframe : UnchangedOutside mem M [(dst, n + 64)])
    (hbody : readBytes mem b n = some body) :
    readBytes M b n = some body := by
  rw [readBytes_of_UnchangedOutside hframe (a := b) (k := n) (fun x h1 h2 r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    omega)]
  exact hbody

/-- **The thirty-two bytes past the body read as the caller's at the exit
memory.** -/
theorem exitTail_read {mem M : Mem} {b n dst : Nat}
    (hdisj : b + n + 32 ≤ dst ∨ dst + n + 64 ≤ b)
    (hframe : UnchangedOutside mem M [(dst, n + 64)])
    {extra : List UInt8} (hextra : readBytes mem (b + n) 32 = some extra) :
    readBytes M (b + n) 32 = some extra := by
  rw [readBytes_of_UnchangedOutside hframe (a := b + n) (k := 32) (fun x h1 h2 r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    omega)]
  exact hextra

theorem take32_drop {B : List UInt8} {k : Nat} :
    List.take k B ++ List.take 32 (List.drop k B) = List.take (k + 32) B := by
  rw [List.take_add]

theorem take_of_take {B : List UInt8} {K a : Nat} (h : a ≤ K) :
    List.take a (List.take K B) = List.take a B := by
  rw [List.take_take, Nat.min_eq_left h]

theorem copyIterBound_succ_mul_le {sub : Nat} (h : 64 < sub) :
    64 * copyIterBound sub + 64 ≤ sub := by
  unfold copyIterBound
  have hd : ((sub - 128 + 63) / 64) * 64 ≤ sub - 128 + 63 := Nat.div_mul_le_self _ _
  by_cases hs : 128 ≤ sub
  · have he : sub - 128 + 63 = sub - 65 := by omega
    rw [he] at hd
    omega
  · have hz : sub - 128 = 0 := by omega
    rw [hz]
    have hz2 : (0 + 63) / 64 = 0 := by decide
    rw [hz2]
    omega

theorem tailDst_read {m : Mem} {Tal k : Nat} {B : List UInt8}
    (hread : readBytes m Tal k = some (List.take k B))
    (hK : k + 32 ≤ B.length) :
    readBytes (writeBytes m (Tal + k) (List.take 32 (List.drop k B))) Tal (k + 32) =
      some (List.take (k + 32) B) := by
  have hlen : (List.take 32 (List.drop k B)).length = 32 := copyChunk_length hK
  rw [readBytes_writeBytes_thirtyTwo hread hlen]
  rw [take32_drop]

theorem tailPost
    {args : List Value} {mem : Mem} {next : Nat} {body : List UInt8}
    {st : ClassState} {dst0 nps : Nat} {goal : EscapeOutcome} {b xp tab : Nat}
    {pos0 n : Nat} {ps : List Nat} {err xj : Nat}
    (hstaging : ExpandStaging args mem next body st dst0 nps goal b xp tab pos0 n ps err xj)
    {iN jN : Nat} {out : List UInt8}
    (hi : iN ≤ n) (hjN : jN = out.length)
    (hgoal : goal = .decoded (out ++ body.drop iN) nps)
    (M : Mem)
    (hd : readBytes M dst0 (jN + (n - iN)) = some (out ++ body.drop iN))
    (hx : readBytes M xj 8 = some (wordBytes 8 nps))
    (hframeM : UnchangedOutside mem M [(dst0, n + 64), (xp, 4 * nps), (xj, 8), (err, 8)])
    (herrM : readBytes M err 8 = readBytes mem err 8) :
    (Γ_escape_expand escapeExpandBudget).post args mem next
      (.ret (some (.int 64 (BitVec.ofNat 64 (n - iN) + BitVec.ofNat 64 jN))) M) := by
  obtain ⟨hpre, hargs, -, hbodyW, h32, hdec, hmap, hnoalias, hdisj1, hdisj2, hwalk⟩ := hstaging
  obtain ⟨b', n', dst', err', xp', xj', nps', pos0', tab', body', ps', err0', k0',
    hargs', hbody', hposbytes', hpslen', hrange', hmap', hwidth', hk0r', hk0le',
    herr0', htab', hhas32, hhasdst, hbo, hxo, htbo, hebo, hexo, hxdo⟩ := hpre
  obtain ⟨-, -, herreq', -, -, -⟩ := staging_ptr_slots hargs hargs'
  rw [herreq'] at herr0'
  obtain ⟨k0, hk0read, hk0le, hwalkeq⟩ := hwalk
  obtain ⟨addv, hstage⟩ := hdec
  obtain ⟨hposbytes, hpslen, hrange, haddv⟩ := hstage
  simp only [Γ_escape_expand, escapeExpandPost]
  refine ⟨b, n, dst0, err, xp, xj, nps, pos0, tab, body, ps, err0', k0,
    hargs, hbodyW, hposbytes, herr0', hk0read, hk0le, ?_⟩
  rw [← hwalkeq, hgoal]
  have hlen : List.length (out ++ List.drop iN body) = (n - iN) + jN := by
    rw [List.length_append, List.length_drop, ← hjN,
      JsonEntrySteps.readBytes_length mem b n hbodyW]
    omega
  refine ⟨?_, ?_, hx, ?_, hframeM⟩
  · rw [BitVec.ofNat_add_ofNat, hlen]
  · rw [hlen, show (n - iN) + jN = jN + (n - iN) from by omega]
    exact hd
  · exact herrM.trans herr0'

theorem copyTail_run
    {args : List Value} {mem : Mem} {next : Nat} {body : List UInt8}
    {st : ClassState} {dst0 nps : Nat} {goal : EscapeOutcome} {b xp tab : Nat}
    {pos0 n : Nat} {ps : List Nat} {err xj : Nat}
    (hzz : ExpandStaging args mem next body st dst0 nps goal b xp tab pos0 n ps err xj)
    {iN jN : Nat} {out extra B : List UInt8}
    (hi : iN ≤ n) (hjN : jN = out.length) (hji : jN ≤ iN)
    (hnpsle : nps ≤ n)
    (hbodyE : readBytes mem b n = some body)
    (hextraE : readBytes mem (b + n) 32 = some extra)
    (hgoal : goal = .decoded (out ++ body.drop iN) nps)
    (hB : B = body.drop iN ++ extra)
    {e : State} {prev : String} {opk ops : Operand} {k subB : BitVec 64}
    (hpc : e.pc = "us_run_long.exit")
    (hprev : e.pre = some prev)
    (hinck : phiIncoming prev udCopyTailNIncomingK = some opk)
    (hopk : evalOperand (withEnv e.env e) opk = some (.int 64 k))
    (hincs : phiIncoming prev udCopyTailNIncomingS = some ops)
    (hops : evalOperand (withEnv (("%k.0.i.lcssa", .int 64 k) :: e.env) e) ops =
      some (.int 64 subB))
    (hsrcb : lookupName e.env "%add.ptr36" = some (.ptr (b + iN)))
    (hdstb : lookupName e.env "%add.ptr37" = some (.ptr (dst0 + jN)))
    (hsub38c : lookupName e.env "%sub38" = some (.int 64 (BitVec.ofNat 64 (n - iN))))
    (hjcell : lookupName e.env "%j.0.lcssa" = some (.int 64 (BitVec.ofNat 64 jN)))
    (hkcell : lookupName e.env "%k.1.lcssa" = some (.int 64 (BitVec.ofNat 64 nps)))
    (hxjcell : lookupName e.env "%xj" = some (.ptr xj))
    (hkres : k.toNat + subB.toNat = n - iN)
    (hsub64 : subB.toNat ≤ 64)
    (hpref : readBytes e.mem dst0 jN = some out)
    (hdstread : readBytes e.mem (dst0 + jN) k.toNat = some (List.take k.toNat B))
    (hsrcfull : readBytes e.mem (b + iN) ((n - iN) + 32) = some B)
    (hframe : UnchangedOutside mem e.mem [(dst0, n + 64)])
    (hdisj : copyDisjoint (b + iN) (dst0 + jN) (n - iN)) :
    ∃ (o : Outcome) (jf : Nat), jf ≤ 4 ∧
      runFuel escapeCalls jf usDecFunction e = some o ∧
      (Γ_escape_expand escapeExpandBudget).post args mem next o := by
  have hstageKeep := hzz
  obtain ⟨hpre, hargs, -, hbodyW, h32, hdec, hmap, hnoalias, hdisj1, hdisj2, hwalk⟩ := hzz
  obtain ⟨b', n', dst', err', xp', xj', nps', pos0', tab', body', ps', err0', k0',
    hargs', hbody', hposbytes', hpslen', hrange', hmap', hwidth', hk0r', hk0le',
    herr0', htab', hhas32, hhasdst, hbo, hxo, htbo, hebo, hexo, hxdo⟩ := hpre
  obtain ⟨-, hdstq, herreq', -, hxjq, -⟩ := staging_ptr_slots hargs hargs'
  rw [herreq'] at herr0' hexo hebo
  rw [hxjq] at hexo hxdo
  rw [hdstq] at hebo hxdo hbo hxo htbo
  have hn' : n = n' := staging_len_eq hargs hargs' (by omega) (by omega)
  rw [← hn'] at hebo hxdo hbo hxo htbo
  obtain ⟨k0, hk0read, hk0le, hwalkeq⟩ := hwalk
  have hn64 : n < 2 ^ 64 := by omega
  have hnps64 : nps < 2 ^ 64 := by omega
  have hkN : k.toNat ≤ n - iN := by omega
  have hknlt : k.toNat < 2 ^ 63 := by omega
  have hSR : n - iN = k.toNat + subB.toNat := hkres.symm
  have hBlen : B.length = (n - iN) + 32 := by
    rw [hB, List.length_append, List.length_drop,
      JsonEntrySteps.readBytes_length mem b n hbodyE,
      JsonEntrySteps.readBytes_length mem (b + n) 32 hextraE]
  have htakesub : List.take (n - iN) B = body.drop iN := by
    rw [hB, take_left_of_body (JsonEntrySteps.readBytes_length mem b n hbodyE) hi]
  have htakesub' : List.take (k.toNat + subB.toNat) B = body.drop iN := by
    rw [← hSR]; exact htakesub
  have hr1 : readBytes e.mem (b + iN + k.toNat) 32 =
      some (List.take 32 (List.drop k.toNat B)) := copySrc_read hsrcfull hkN
  have hlen1 : (List.take 32 (List.drop k.toNat B)).length = 32 := by
    refine copyChunk_length ?_
    rw [hBlen]; omega
  by_cases hgt : 32 < subB.toNat
  · -- the second half of the store, then `us_run.exit112`
    have hk32 : k.toNat + 32 ≤ n - iN := by omega
    have hr2 : readBytes (writeBytes e.mem (dst0 + jN + k.toNat)
        (List.take 32 (List.drop k.toNat B))) (b + iN + k.toNat + 32) 32 =
        some (List.take 32 (List.drop (k.toNat + 32) B)) := by
      rw [JsonEntrySteps.readBytes_writeBytes_frame _ _ _ _ _ (by
        rcases hdisj with hd | hd
        · right; omega
        · left; omega)]
      exact copySrc_read_mid (B := B) hsrcfull hk32
    have hlen2 : (List.take 32 (List.drop (k.toNat + 32) B)).length = 32 := by
      refine copyChunk_length ?_; rw [hBlen]; omega
    let envA : Env := udCopyTailNEnv e.env (b + iN) (dst0 + jN) k
      (List.take 32 (List.drop k.toNat B)) subB
    let s1 : State := State.mk e.env
      (writeBytes e.mem (dst0 + jN + k.toNat) (List.take 32 (List.drop k.toNat B)))
      e.next "if.then.i109" (some "us_run_long.exit")
    let e1 : State := withEnv envA s1
    have hstep1 : step escapeCalls usDecFunction e = .jump e1 := by
      have h := udCopyTailN_step e.env e prev opk ops (b + iN) (dst0 + jN) k
        (List.take 32 (List.drop k.toNat B)) subB hpc hprev hinck hopk
        hincs hops hsrcb hdstb hknlt (by rw [BitVec.signExtend_eq]) hr1 hlen1
        ((evalICmp_ugt_one_iff_toNat _ _).2 (by
          rw [show (BitVec.ofInt 64 32).toNat = 32 from by decide]; exact hgt))
      simpa only [e1, s1, envA, withEnv] using h
    have he1mem : e1.mem = writeBytes e.mem (dst0 + jN + k.toNat)
        (List.take 32 (List.drop k.toNat B)) := by simp only [e1, s1, withEnv]
    have hd1 : readBytes
        (writeBytes e.mem (dst0 + jN + k.toNat) (List.take 32 (List.drop k.toNat B)))
        (dst0 + jN) (k.toNat + 32) = some (List.take (k.toNat + 32) B) :=
      tailDst_read (Tal := dst0 + jN) hdstread (by rw [hBlen]; omega)
    -- the second block
    let t2 : State := State.mk e.env e.mem e.next "if.then.i109" (some "us_run_long.exit")
    let envB : Env := udCopyTailIfNEnv envA (b + iN) (dst0 + jN) k
      (List.take 32 (List.drop (k.toNat + 32) B))
    let s2 : State := State.mk e.env
      (udCopy2Mem e.mem (dst0 + jN + k.toNat) (List.take 32 (List.drop k.toNat B))
        (List.take 32 (List.drop (k.toNat + 32) B)))
      e.next "us_run.exit112" (some "if.then.i109")
    let e2 : State := withEnv envB s2
    have hstep2 : step escapeCalls usDecFunction e1 = .jump e2 := by
      have h8 : lookupName envA "%add.ptr8.i" = some (.ptr (dst0 + jN + k.toNat)) := by
        simp only [envA, udCopyTailNEnv]; ud_lk
      have h7 : lookupName envA "%add.ptr7.i" = some (.ptr (b + iN + k.toNat)) := by
        simp only [envA, udCopyTailNEnv]; ud_lk
      have h := udCopyTailIfN_step envA t2 (b + iN) (dst0 + jN) k
        (List.take 32 (List.drop k.toNat B))
        (List.take 32 (List.drop (k.toNat + 32) B)) (by rfl) h7 h8 hr2 hlen2
      simpa only [e1, s1, t2, e2, s2, envA, envB, withEnv] using h
    have he2mem : e2.mem = writeBytes (writeBytes e.mem (dst0 + jN + k.toNat)
        (List.take 32 (List.drop k.toNat B)))
        (dst0 + jN + k.toNat + 32) (List.take 32 (List.drop (k.toNat + 32) B)) := by
      simp only [e2, s2, withEnv, udCopy2Mem]
    have hd2 : readBytes
        (writeBytes (writeBytes e.mem (dst0 + jN + k.toNat)
          (List.take 32 (List.drop k.toNat B)))
          (dst0 + jN + k.toNat + 32) (List.take 32 (List.drop (k.toNat + 32) B)))
        (dst0 + jN) (k.toNat + 64) = some (List.take (k.toNat + 64) B) := by
      rw [show dst0 + jN + k.toNat + 32 = dst0 + jN + (k.toNat + 32) from by omega,
        readBytes_writeBytes_thirtyTwo hd1 hlen2,
        show List.take (k.toNat + 32) B ++ List.take 32 (List.drop (k.toNat + 32) B)
          = List.take (k.toNat + 32 + 32) B from take32_drop,
        show k.toNat + 32 + 32 = k.toNat + 64 from by omega]
    have hd2S : readBytes
        (writeBytes (writeBytes e.mem (dst0 + jN + k.toNat)
          (List.take 32 (List.drop k.toNat B)))
          (dst0 + jN + k.toNat + 32) (List.take 32 (List.drop (k.toNat + 32) B)))
        (dst0 + jN) (k.toNat + subB.toNat) = some (List.take (k.toNat + subB.toNat) B) := by
      have hsplit := readBytes_split
        (writeBytes (writeBytes e.mem (dst0 + jN + k.toNat)
          (List.take 32 (List.drop k.toNat B)))
          (dst0 + jN + k.toNat + 32) (List.take 32 (List.drop (k.toNat + 32) B)))
        (dst0 + jN) (k.toNat + subB.toNat)
        (64 - subB.toNat) (bs := List.take (k.toNat + 64) B) (by
          rw [show k.toNat + subB.toNat + (64 - subB.toNat) = k.toNat + 64 from by omega]
          exact hd2)
      rw [show List.take (k.toNat + subB.toNat) (List.take (k.toNat + 64) B) =
          List.take (k.toNat + subB.toNat) B from take_of_take (by omega)] at hsplit
      exact hsplit.1
    have hd2S' : readBytes
        (writeBytes (writeBytes e.mem (dst0 + jN + k.toNat)
          (List.take 32 (List.drop k.toNat B)))
          (dst0 + jN + k.toNat + 32) (List.take 32 (List.drop (k.toNat + 32) B)))
        (dst0 + jN) (n - iN) = some (body.drop iN) := by
      rw [hSR, ← htakesub']; exact hd2S
    have hd : readBytes
        (writeBytes (writeBytes e.mem (dst0 + jN + k.toNat)
          (List.take 32 (List.drop k.toNat B)))
          (dst0 + jN + k.toNat + 32) (List.take 32 (List.drop (k.toNat + 32) B)))
        dst0 (jN + (n - iN)) = some (out ++ body.drop iN) := by
      have hpref2 : readBytes
          (writeBytes (writeBytes e.mem (dst0 + jN + k.toNat)
            (List.take 32 (List.drop k.toNat B)))
            (dst0 + jN + k.toNat + 32) (List.take 32 (List.drop (k.toNat + 32) B)))
          dst0 jN = some out := by
        rw [readBytes_writeBytes_below _ _ jN dst0 (dst0 + jN + k.toNat + 32) (by omega)]
        rw [readBytes_writeBytes_below _ _ jN dst0 (dst0 + jN + k.toNat) (by omega)]
        exact hpref
      exact JsonEntrySteps.readBytes_append _ jN dst0 out (n - iN) (body.drop iN)
        hpref2 hd2S'
    rw [← he2mem] at hd
    -- `us_run.exit112`
    let envC : Env := udUsRunExit112Env e2.env (BitVec.ofNat 64 (n - iN))
      (BitVec.ofNat 64 jN)
    let s3 : State := State.mk e2.env
      (writeBytes e2.mem xj (natToBytes (BitVec.ofNat 64 nps).toNat 8))
      e2.next "cleanup41" (some "us_run.exit112")
    let e3 : State := withEnv envC s3
    have he3mem : e3.mem = writeBytes e2.mem xj
        (natToBytes (BitVec.ofNat 64 nps).toNat 8) := by simp only [e3, s3, withEnv]
    have hf3pc : e3.pc = "cleanup41" := by simp only [e3, s3, withEnv]
    have hf3pre : e3.pre = some "us_run.exit112" := by simp only [e3, s3, withEnv]
    have hstep3 : step escapeCalls usDecFunction e2 = .jump e3 := by
      have hk : lookupName e2.env "%k.1.lcssa" = some (.int 64 (BitVec.ofNat 64 nps)) := by
        simp only [e2, s2, envB, envA, withEnv, udCopyTailIfNEnv, udCopyTailNEnv]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact hkcell
      have hr : lookupName e2.env "%sub38" =
          some (.int 64 (BitVec.ofNat 64 (n - iN))) := by
        simp only [e2, s2, envB, envA, withEnv, udCopyTailIfNEnv, udCopyTailNEnv]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact hsub38c
      have hj : lookupName e2.env "%j.0.lcssa" = some (.int 64 (BitVec.ofNat 64 jN)) := by
        simp only [e2, s2, envB, envA, withEnv, udCopyTailIfNEnv, udCopyTailNEnv]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact hjcell
      have hx : lookupName e2.env "%xj" = some (.ptr xj) := by
        simp only [e2, s2, envB, envA, withEnv, udCopyTailIfNEnv, udCopyTailNEnv]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact hxjcell
      have h := udUsRunExit112_step e2.env e2 (BitVec.ofNat 64 nps)
        (BitVec.ofNat 64 (n - iN)) (BitVec.ofNat 64 jN) xj (by simp only [e2, s2, withEnv])
        hk hr hj hx
      simpa only [e3, s3, envC, withEnv] using h
    have hframe2 : UnchangedOutside mem e2.mem [(dst0, n + 64)] := by
      rw [he2mem]
      have hb1 : dst0 ≤ dst0 + jN + k.toNat := by omega
      have hb2 : dst0 + jN + k.toNat + (List.take 32 (List.drop k.toNat B)).length ≤
          dst0 + (n + 64) := by rw [hlen1]; omega
      have hb3 : dst0 ≤ dst0 + jN + k.toNat + 32 := by omega
      have hb4 : dst0 + jN + k.toNat + 32 +
          (List.take 32 (List.drop (k.toNat + 32) B)).length ≤ dst0 + (n + 64) := by
        rw [hlen2]; omega
      exact UnchangedOutside.writeBytes_inside
        (UnchangedOutside.writeBytes_inside hframe hb1 hb2) hb3 hb4
    have hx3 : readBytes e3.mem xj 8 = some (wordBytes 8 nps) := by
      rw [he3mem, show natToBytes (BitVec.ofNat 64 nps).toNat 8 = wordBytes 8 nps from by
        rw [wordBytes, show (BitVec.ofNat 64 nps).toNat = nps from by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnps64]]]
      rw [show (8 : Nat) = (wordBytes 8 nps).length from by rw [wordBytes, natToBytes_length]]
      exact readBytes_writeBytes_same e2.mem (wordBytes 8 nps) (addr := xj)
    have he3 : readBytes e3.mem err 8 = readBytes mem err 8 := by
      rw [he3mem,
        JsonEntrySteps.readBytes_writeBytes_frame _ _ xj err 8 (by
          rcases hexo with hd | hd
          · left; exact hd
          · right; rw [natToBytes_length]; exact hd),
        readBytes_of_UnchangedOutside hframe2 (a := err) (k := 8) (fun x h1 h2 r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          subst hr
          rcases hebo with hb | hb <;> omega)]
    have hf3 : UnchangedOutside mem e3.mem
        [(dst0, n + 64), (xp, 4 * nps), (xj, 8), (err, 8)] := by
      refine UnchangedOutside.writeBytes_in
        (UnchangedOutside.mono hframe2 (by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          subst hr
          exact List.mem_cons_self ..)) ?_
      refine ⟨(xj, 8), by simp, by omega, ?_⟩
      rw [natToBytes_length]; omega
    have hd3 : readBytes e3.mem dst0 (jN + (n - iN)) = some (out ++ body.drop iN) := by
      rw [he3mem, JsonEntrySteps.readBytes_writeBytes_frame _ _ xj dst0 (jN + (n - iN)) (by
        rcases hxdo with hd' | hd'
        · right; rw [natToBytes_length]; exact hd'
        · left; omega)]
      exact hd
    have hpost3 := tailPost hstageKeep hi hjN hgoal e3.mem hd3 hx3 hf3 he3
    refine ⟨_, 4, by omega, ?_, hpost3⟩
    rw [show 4 = 1 + (1 + (1 + 1)) from by omega]
    rw [runFuel_jump_prefix hstep1 (1 + (1 + 1))]
    rw [runFuel_jump_prefix hstep2 (1 + 1)]
    rw [runFuel_jump_prefix hstep3 1]
    exact cleanup41SuccessReturn e3 hf3pc hf3pre _
      (by simp only [e3, envC, s3, udUsRunExit112Env, withEnv]; ud_lk)
  · -- the residual fits one block
    have hle : subB.toNat ≤ 32 := by omega
    let envA : Env := udCopyTailNEnv e.env (b + iN) (dst0 + jN) k
      (List.take 32 (List.drop k.toNat B)) subB
    let s1 : State := State.mk e.env
      (writeBytes e.mem (dst0 + jN + k.toNat) (List.take 32 (List.drop k.toNat B)))
      e.next "us_run.exit112" (some "us_run_long.exit")
    let e1 : State := withEnv envA s1
    have hstep1 : step escapeCalls usDecFunction e = .jump e1 := by
      have h := udCopyTailN_step_zero e.env e prev opk ops (b + iN) (dst0 + jN) k
        (List.take 32 (List.drop k.toNat B)) subB hpc hprev hinck hopk
        hincs hops hsrcb hdstb hknlt (by rw [BitVec.signExtend_eq]) hr1 hlen1
        ((evalICmp_ugt_zero_iff _ _).2 (by
          rw [show (BitVec.ofInt 64 32).toNat = 32 from by decide]; omega))
      simpa only [e1, s1, envA, withEnv] using h
    have he1mem : e1.mem = writeBytes e.mem (dst0 + jN + k.toNat)
        (List.take 32 (List.drop k.toNat B)) := by simp only [e1, s1, withEnv]
    have hd1 : readBytes
        (writeBytes e.mem (dst0 + jN + k.toNat) (List.take 32 (List.drop k.toNat B)))
        (dst0 + jN) (k.toNat + 32) = some (List.take (k.toNat + 32) B) :=
      tailDst_read (Tal := dst0 + jN) hdstread (by rw [hBlen]; omega)
    have hd1S : readBytes
        (writeBytes e.mem (dst0 + jN + k.toNat) (List.take 32 (List.drop k.toNat B)))
        (dst0 + jN) (k.toNat + subB.toNat) = some (List.take (k.toNat + subB.toNat) B) := by
      have hsplit := readBytes_split
        (writeBytes e.mem (dst0 + jN + k.toNat) (List.take 32 (List.drop k.toNat B)))
        (dst0 + jN) (k.toNat + subB.toNat)
        (32 - subB.toNat) (bs := List.take (k.toNat + 32) B) (by
          rw [show k.toNat + subB.toNat + (32 - subB.toNat) = k.toNat + 32 from by omega]
          exact hd1)
      rw [show List.take (k.toNat + subB.toNat) (List.take (k.toNat + 32) B) =
          List.take (k.toNat + subB.toNat) B from take_of_take (by omega)] at hsplit
      exact hsplit.1
    have hd1S' : readBytes
        (writeBytes e.mem (dst0 + jN + k.toNat) (List.take 32 (List.drop k.toNat B)))
        (dst0 + jN) (n - iN) = some (body.drop iN) := by
      rw [hSR, ← htakesub']; exact hd1S
    have hd : readBytes
        (writeBytes e.mem (dst0 + jN + k.toNat) (List.take 32 (List.drop k.toNat B)))
        dst0 (jN + (n - iN)) = some (out ++ body.drop iN) := by
      have hpref2 : readBytes
          (writeBytes e.mem (dst0 + jN + k.toNat) (List.take 32 (List.drop k.toNat B)))
          dst0 jN = some out := by
        rw [readBytes_writeBytes_below _ _ jN dst0 (dst0 + jN + k.toNat) (by omega)]
        exact hpref
      exact JsonEntrySteps.readBytes_append _ jN dst0 out (n - iN) (body.drop iN)
        hpref2 hd1S'
    rw [← he1mem] at hd
    let envC : Env := udUsRunExit112Env e1.env (BitVec.ofNat 64 (n - iN))
      (BitVec.ofNat 64 jN)
    let s3 : State := State.mk e1.env
      (writeBytes e1.mem xj (natToBytes (BitVec.ofNat 64 nps).toNat 8))
      e1.next "cleanup41" (some "us_run.exit112")
    let e3 : State := withEnv envC s3
    have he3mem : e3.mem = writeBytes e1.mem xj
        (natToBytes (BitVec.ofNat 64 nps).toNat 8) := by simp only [e3, s3, withEnv]
    have hf3pc : e3.pc = "cleanup41" := by simp only [e3, s3, withEnv]
    have hf3pre : e3.pre = some "us_run.exit112" := by simp only [e3, s3, withEnv]
    have hstep3 : step escapeCalls usDecFunction e1 = .jump e3 := by
      have hk : lookupName e1.env "%k.1.lcssa" = some (.int 64 (BitVec.ofNat 64 nps)) := by
        simp only [e1, s1, envA, withEnv, udCopyTailNEnv]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact hkcell
      have hr : lookupName e1.env "%sub38" =
          some (.int 64 (BitVec.ofNat 64 (n - iN))) := by
        simp only [e1, s1, envA, withEnv, udCopyTailNEnv]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact hsub38c
      have hj : lookupName e1.env "%j.0.lcssa" = some (.int 64 (BitVec.ofNat 64 jN)) := by
        simp only [e1, s1, envA, withEnv, udCopyTailNEnv]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact hjcell
      have hx : lookupName e1.env "%xj" = some (.ptr xj) := by
        simp only [e1, s1, envA, withEnv, udCopyTailNEnv]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact hxjcell
      have h := udUsRunExit112_step e1.env e1 (BitVec.ofNat 64 nps)
        (BitVec.ofNat 64 (n - iN)) (BitVec.ofNat 64 jN) xj (by simp only [e1, s1, withEnv])
        hk hr hj hx
      simpa only [e3, s3, envC, withEnv] using h
    have hframe1 : UnchangedOutside mem e1.mem [(dst0, n + 64)] := by
      rw [he1mem]
      have hb1 : dst0 ≤ dst0 + jN + k.toNat := by omega
      have hb2 : dst0 + jN + k.toNat + (List.take 32 (List.drop k.toNat B)).length ≤
          dst0 + (n + 64) := by rw [hlen1]; omega
      exact UnchangedOutside.writeBytes_inside hframe hb1 hb2
    have hx3 : readBytes e3.mem xj 8 = some (wordBytes 8 nps) := by
      rw [he3mem, show natToBytes (BitVec.ofNat 64 nps).toNat 8 = wordBytes 8 nps from by
        rw [wordBytes, show (BitVec.ofNat 64 nps).toNat = nps from by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnps64]]]
      rw [show (8 : Nat) = (wordBytes 8 nps).length from by rw [wordBytes, natToBytes_length]]
      exact readBytes_writeBytes_same e1.mem (wordBytes 8 nps) (addr := xj)
    have he3 : readBytes e3.mem err 8 = readBytes mem err 8 := by
      rw [he3mem,
        JsonEntrySteps.readBytes_writeBytes_frame _ _ xj err 8 (by
          rcases hexo with hd | hd
          · left; exact hd
          · right; rw [natToBytes_length]; exact hd),
        readBytes_of_UnchangedOutside hframe1 (a := err) (k := 8) (fun x h1 h2 r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          subst hr
          rcases hebo with hb | hb <;> omega)]
    have hf3 : UnchangedOutside mem e3.mem
        [(dst0, n + 64), (xp, 4 * nps), (xj, 8), (err, 8)] := by
      refine UnchangedOutside.writeBytes_in
        (UnchangedOutside.mono hframe1 (by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          subst hr
          exact List.mem_cons_self ..)) ?_
      refine ⟨(xj, 8), by simp, by omega, ?_⟩
      rw [natToBytes_length]; omega
    have hd3 : readBytes e3.mem dst0 (jN + (n - iN)) = some (out ++ body.drop iN) := by
      rw [he3mem, JsonEntrySteps.readBytes_writeBytes_frame _ _ xj dst0 (jN + (n - iN)) (by
        rcases hxdo with hd' | hd'
        · right; rw [natToBytes_length]; exact hd'
        · left; omega)]
      exact hd
    have hpost3 := tailPost hstageKeep hi hjN hgoal e3.mem hd3 hx3 hf3 he3
    refine ⟨_, 3, by omega, ?_, hpost3⟩
    rw [show 3 = 1 + (1 + 1) from by omega]
    rw [runFuel_jump_prefix hstep1 (1 + 1)]
    rw [runFuel_jump_prefix hstep3 1]
    exact cleanup41SuccessReturn e3 hf3pc hf3pre _
      (by simp only [e3, envC, s3, udUsRunExit112Env, withEnv]; ud_lk)

/-- **The final copy's run.**  From `while.end35` at any of the four `phi` edges,
the run copies the body's residual into the caller's buffer, then the tail's last
block or two, and returns through `cleanup41`.

The invariant that carries it is `copyPreLoop`'s instance conjoined with the
caller's own facts, and each is named before the instance is built: the walk's
decoded prefix at `dst0`, the frame over the destination extent, and the three
cells `us_run.exit112` reads.  The cells `while.end35` writes are read back at the
`Nat`s the block's own arithmetic names — the two copy bases at `%i.0.lcssa` and
`%j.0.lcssa`, and `%sub38` at its subtraction, which is the `Nat` residual only
through `ofNat_sub_ofNat`.

The exit's allowance is `finalCopy_fuel_le`: the copy's bound, the tail's at most
four steps, and the return fit in `n / 64 + 7`, which `expandExitFuel_eq` identifies
with the record's exit budget at this staging. -/
theorem whileEnd35_run
    {args : List Value} {mem : Mem} {next : Nat} {body : List UInt8}
    {st : ClassState} {dst0 nps : Nat} {goal : EscapeOutcome} {b xp tab : Nat}
    {pos0 n : Nat} {ps : List Nat} {err xj : Nat}
    (hstaging : ExpandStaging args mem next body st dst0 nps goal b xp tab pos0 n ps err xj)
    {iN jN : Nat} {out extra : List UInt8}
    (hi : iN ≤ n) (hjN : jN = out.length) (hji : jN ≤ iN) (hnpsle : nps ≤ n)
    (hbodyE : readBytes mem b n = some body)
    (hextraE : readBytes mem (b + n) 32 = some extra)
    (hgoal : goal = .decoded (out ++ body.drop iN) nps)
    {e : State} {prev : String} {opj opi opk : Operand}
    (hpc : e.pc = "while.end35") (hprev : e.pre = some prev)
    (hinj : phiIncoming prev udWhileEnd35IncomingJ = some opj)
    (hini : phiIncoming prev udWhileEnd35IncomingI = some opi)
    (hink : phiIncoming prev udWhileEnd35IncomingK = some opk)
    (hopj : evalOperand (withEnv e.env e) opj = some (.int 64 (BitVec.ofNat 64 jN)))
    (hopi : evalOperand (withEnv (("%j.0.lcssa", .int 64 (BitVec.ofNat 64 jN)) :: e.env) e) opi =
      some (.int 64 (BitVec.ofNat 64 iN)))
    (hopk : evalOperand (withEnv (("%i.0.lcssa", .int 64 (BitVec.ofNat 64 iN)) ::
      ("%j.0.lcssa", .int 64 (BitVec.ofNat 64 jN)) :: e.env) e) opk =
      some (.int 64 (BitVec.ofNat 64 nps)))
    (hp : lookupName e.env "%p" = some (.ptr b))
    (hdstc : lookupName e.env "%dst" = some (.ptr dst0))
    (hnc : lookupName e.env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hxjc : lookupName e.env "%xj" = some (.ptr xj))
    (hpref : readBytes e.mem dst0 jN = some out)
    (hframe : UnchangedOutside mem e.mem [(dst0, n + 64)]) :
    ∃ (o : Outcome) (jf : Nat), jf ≤ n / 64 + 7 ∧
      runFuel escapeCalls jf usDecFunction e = some o ∧
      (Γ_escape_expand escapeExpandBudget).post args mem next o := by
  have hstageKeep := hstaging
  obtain ⟨-, hargs, -, hbodyW, h32, hdec, hmap, hnoalias, hdisj1, hdisj2, hwalk⟩ := hstaging
  have hn64 : n < 2 ^ 64 := by omega
  have hsubeq : BitVec.ofNat 64 n - BitVec.ofNat 64 iN = BitVec.ofNat 64 (n - iN) :=
    ofNat_sub_ofNat hi hn64
  have hbodyEm : readBytes e.mem b n = some body := exitBody_read hdisj1 hframe hbodyE
  have hextraEm : readBytes e.mem (b + n) 32 = some extra :=
    exitTail_read hdisj1 hframe hextraE
  have hi63 : (BitVec.ofNat 64 iN).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  have hj63 : (BitVec.ofNat 64 jN).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  let B : List UInt8 := body.drop iN ++ extra
  have hBdef : B = body.drop iN ++ extra := rfl
  have hsrcfullAll : readBytes e.mem (b + iN) ((n - iN) + 32) = some B := by
    rw [hBdef]; exact (finalSource_read hbodyEm hi hextraEm).1
  have hBlen : B.length = (n - iN) + 32 := by
    rw [hBdef]; exact (finalSource_read hbodyEm hi hextraEm).2
  have hdisj : copyDisjoint (b + iN) (dst0 + jN) (n - iN) := by
    rcases hdisj1 with hd | hd
    · right; omega
    · left; omega
  by_cases hgt : 64 < n - iN
  · -- the copy loop, then the tail
    have hcond : evalICmp .ugt (BitVec.ofNat 64 n - BitVec.ofNat 64 iN)
        (BitVec.ofInt 64 64) = (1 : BitVec 1) := by
      rw [hsubeq]
      refine (evalICmp_ugt_one_iff_toNat _ _).2 ?_
      rw [show (BitVec.ofInt 64 64).toNat = 64 from by decide, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
      omega
    let envW : Env := udWhileEnd35Env e.env b dst0 (BitVec.ofNat 64 jN)
      (BitVec.ofNat 64 iN) (BitVec.ofNat 64 nps) (BitVec.ofNat 64 n)
    let s1 : State := State.mk e.env e.mem e.next "while.body.i" (some "while.end35")
    let e1 : State := withEnv envW s1
    have hstep : step escapeCalls usDecFunction e = .jump e1 := by
      have h := udWhileEnd35_step e.env e prev opj opi opk b dst0 (BitVec.ofNat 64 jN)
        (BitVec.ofNat 64 iN) (BitVec.ofNat 64 nps) (BitVec.ofNat 64 n) hpc hprev
        hinj hini hink hopj hopi hopk hp hdstc hnc hi63 hj63
        (by rw [BitVec.signExtend_eq]) (by rw [BitVec.signExtend_eq]) hcond
      rw [show withEnv e.env e = e from rfl] at h
      simpa only [e1, s1, envW, withEnv] using h
    have he1pc : e1.pc = "while.body.i" := by simp only [e1, s1, withEnv]
    have he1pre : e1.pre = some "while.end35" := by simp only [e1, s1, withEnv]
    have he1mem : e1.mem = e.mem := by simp only [e1, s1, withEnv]
    have hsrcfull : readBytes e1.mem (b + iN) ((n - iN) + 32) = some B := by
      rw [he1mem]; exact hsrcfullAll
    -- The copy's invariant, conjunct by conjunct.  Every cell is named at the
    -- state the loop is entered at, so each proof sees the expected type and the
    -- assembler is a plain anonymous constructor over names.
    have hpc1 : e1.pc = "while.body.i" := he1pc
    have hpre1 : e1.pre = some "while.end35" := he1pre
    have hphi1 : phiIncoming "while.end35" copyBodyNNames.incoming =
        some (.imm (.int 64 (BitVec.ofInt 64 0))) := by decide
    have hk0 : BitVec.ofInt 64 0 = BitVec.ofNat 64 (64 * 0) := by decide
    have hop1 : evalOperand e1 (.imm (.int 64 (BitVec.ofInt 64 0))) =
        some (.int 64 (BitVec.ofNat 64 (64 * 0))) := by
      rw [hk0]; rfl
    -- The block reads the two copy bases off the cells `while.end35` wrote.  The
    -- cells are `paddr + i.toNat`, so the byte indices must be their own `Nat`s.
    have hsrc36 : lookupName e1.env "%add.ptr36" = some (.ptr (b + iN)) := by
      simp only [e1, envW, s1, withEnv, udWhileEnd35Env]
      rw [show (BitVec.ofNat 64 iN).toNat = iN from by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega]
      ud_lk
    have hdst37 : lookupName e1.env "%add.ptr37" = some (.ptr (dst0 + jN)) := by
      simp only [e1, envW, s1, withEnv, udWhileEnd35Env]
      rw [show (BitVec.ofNat 64 jN).toNat = jN from by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega]
      ud_lk
    -- `%sub38` is the block's subtraction, so it is the `Nat` residual only after
    -- `ofNat_sub_ofNat`.
    have hsub38v : lookupName e1.env "%sub38" =
        some (.int 64 (BitVec.ofNat 64 (n - iN))) := by
      simp only [e1, envW, s1, withEnv, udWhileEnd35Env]
      rw [← hsubeq]
      ud_lk
    have hrd1 : readBytes e1.mem (b + iN) ((n - iN) + 32) = some B := hsrcfull
    have hlen1 : B.length = (n - iN) + 32 := hBlen
    have hdst1 : readBytes e1.mem (dst0 + jN) (64 * 0) =
        some (List.take (64 * 0) B) := by
      rw [show 64 * 0 = 0 from rfl]; rfl
    have hdisj1' : copyDisjoint (b + iN) (dst0 + jN) (n - iN) := hdisj
    have hlt63 : n - iN < 2 ^ 63 := by omega
    have hcle : 0 ≤ copyIterBound (n - iN) := Nat.zero_le _
    have hbnd1 : copyIterBound (n - iN) ≤ 0 + copyIterBound (n - iN) := by omega
    have hinv : CopyInv copyBodyNNames (b + iN) (dst0 + jN) (n - iN) B
        (copyIterBound (n - iN)) 0 e1 :=
      ⟨"while.end35", .imm (.int 64 (BitVec.ofInt 64 0)), BitVec.ofNat 64 (64 * 0),
        hpc1, hpre1, hphi1, hop1, hk0, hsrc36, hdst37, hsub38v, hrd1, hlen1, hdst1,
        hdisj1', hlt63, hgt, hcle, hbnd1⟩
    let L : BoundLoop escapeCalls usDecFunction :=
      copyPreLoop (b + iN) (dst0 + jN) (n - iN) B dst0 jN out mem (n + 64) nps xj
        rfl (by omega)
    -- The caller's prefix, its frame and its three carried cells, each named.
    have hpref1 : readBytes e1.mem dst0 jN = some out := by rw [he1mem]; exact hpref
    have hframe1 : UnchangedOutside mem e1.mem [(dst0, n + 64)] := by
      rw [he1mem]; exact hframe
    have hj1 : lookupName e1.env "%j.0.lcssa" = some (.int 64 (BitVec.ofNat 64 jN)) := by
      simp only [e1, envW, s1, withEnv, udWhileEnd35Env]; ud_lk
    have hk1 : lookupName e1.env "%k.1.lcssa" = some (.int 64 (BitVec.ofNat 64 nps)) := by
      simp only [e1, envW, s1, withEnv, udWhileEnd35Env]; ud_lk
    have hxj1 : lookupName e1.env "%xj" = some (.ptr xj) := by
      simp only [e1, envW, s1, withEnv]; exact hxjc
    have hinvFull : L.Inv L.N e1 0 :=
      ⟨hinv, hpref1, hframe1, hj1, hk1, hxj1⟩
    have hrun0 : ∃ (e' : State) (j' : Nat), j' ≤ (L.N + 1) * L.cost ∧ L.Exit e' ∧
        L.ExitWord e' ∧ ∀ k, runFuel escapeCalls (j' + k) usDecFunction e1 =
          runFuel escapeCalls k usDecFunction e' :=
      L.run_from L.N e1 0 hinvFull
    obtain ⟨e', j', hrest⟩ := hrun0
    obtain ⟨hj', hexit', hexitw', hrun'⟩ := hrest
    obtain ⟨hcopyw, hprefw, hframew, hjcellw, hkcellw, hxjcellw⟩ := hexitw'
    obtain ⟨-, hprevw, hknext, hsnext, hsrcw, hdstw, hsubw, hdstreadw, hsrcwfull⟩ := hcopyw
    -- the tail's inputs from the copy's exit word
    have hbm := copyIterBound_mul_le (n - iN)
    have hk : (BitVec.ofNat 64 (64 * copyIterBound (n - iN) + 64)).toNat =
        64 * copyIterBound (n - iN) + 64 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega
    have hsuble : 64 * copyIterBound (n - iN) + 64 ≤ n - iN :=
      copyIterBound_succ_mul_le hgt
    have hsubB : (BitVec.ofNat 64 ((n - iN) - (64 * copyIterBound (n - iN) + 64))).toNat =
        (n - iN) - (64 * copyIterBound (n - iN) + 64) := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega
    have hkres : (BitVec.ofNat 64 (64 * copyIterBound (n - iN) + 64)).toNat +
        (BitVec.ofNat 64 ((n - iN) - (64 * copyIterBound (n - iN) + 64))).toNat = n - iN := by
      rw [hk, hsubB]; omega
    have hsub64 : (BitVec.ofNat 64 ((n - iN) - (64 * copyIterBound (n - iN) + 64))).toNat ≤ 64 := by
      rw [hsubB]
      exact copyIterBound_exit (by omega) (by omega) hgt
    have hknext' : lookupName e'.env "%add.i" =
        some (.int 64 (BitVec.ofNat 64 (64 * copyIterBound (n - iN) + 64))) := hknext
    have hsnext' : lookupName e'.env "%sub.i" =
        some (.int 64 (BitVec.ofNat 64 ((n - iN) - (64 * copyIterBound (n - iN) + 64)))) := hsnext
    have hdstread' : readBytes e'.mem (dst0 + jN)
        (BitVec.ofNat 64 (64 * copyIterBound (n - iN) + 64)).toNat =
        some (List.take (BitVec.ofNat 64 (64 * copyIterBound (n - iN) + 64)).toNat B) := by
      rw [hk]; exact hdstreadw
    obtain ⟨o, jt, hjt, htailrun, hpost⟩ :=
      copyTail_run hstageKeep hi hjN hji hnpsle hbodyE hextraE hgoal hBdef
        (e := e') (prev := "while.body.i") (opk := .reg "%add.i") (ops := .reg "%sub.i")
        (k := BitVec.ofNat 64 (64 * copyIterBound (n - iN) + 64))
        (subB := BitVec.ofNat 64 ((n - iN) - (64 * copyIterBound (n - iN) + 64)))
        hexit' hprevw (by decide)
        (by
          show evalOperand (withEnv e'.env e') (.reg "%add.i") =
            some (.int 64 (BitVec.ofNat 64 (64 * copyIterBound (n - iN) + 64)))
          rw [show withEnv e'.env e' = e' from rfl]
          exact hknext')
        (by decide)
        (by
          show evalOperand (withEnv (("%k.0.i.lcssa",
            .int 64 (BitVec.ofNat 64 (64 * copyIterBound (n - iN) + 64))) :: e'.env) e')
            (.reg "%sub.i") =
            some (.int 64 (BitVec.ofNat 64
              ((n - iN) - (64 * copyIterBound (n - iN) + 64))))
          simp only [withEnv, evalOperand]
          rw [lookupName_cons_ne _ _ (by decide)]
          exact hsnext')
        hsrcw hdstw hsubw hjcellw hkcellw hxjcellw hkres hsub64 hprefw hdstread'
        hsrcwfull hframew hdisj
    refine ⟨o, 1 + (j' + jt), ?_, ?_, hpost⟩
    · have := finalCopy_fuel_le hi
      simp only [L, copyPreLoop] at hj'
      omega
    · rw [runFuel_jump_prefix hstep (j' + jt)]
      rw [hrun' jt]
      exact htailrun
  · -- no copy: straight to the tail
    have hcond : evalICmp .ugt (BitVec.ofNat 64 n - BitVec.ofNat 64 iN)
        (BitVec.ofInt 64 64) = (0 : BitVec 1) := by
      rw [hsubeq]
      refine (evalICmp_ugt_zero_iff _ _).2 ?_
      rw [show (BitVec.ofInt 64 64).toNat = 64 from by decide, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
      omega
    let envW : Env := udWhileEnd35Env e.env b dst0 (BitVec.ofNat 64 jN)
      (BitVec.ofNat 64 iN) (BitVec.ofNat 64 nps) (BitVec.ofNat 64 n)
    let s1 : State := State.mk e.env e.mem e.next "us_run_long.exit" (some "while.end35")
    let e1 : State := withEnv envW s1
    have hstep : step escapeCalls usDecFunction e = .jump e1 := by
      have h := udWhileEnd35_step_zero e.env e prev opj opi opk b dst0 (BitVec.ofNat 64 jN)
        (BitVec.ofNat 64 iN) (BitVec.ofNat 64 nps) (BitVec.ofNat 64 n) hpc hprev
        hinj hini hink hopj hopi hopk hp hdstc hnc hi63 hj63
        (by rw [BitVec.signExtend_eq]) (by rw [BitVec.signExtend_eq]) hcond
      rw [show withEnv e.env e = e from rfl] at h
      simpa only [e1, s1, envW, withEnv] using h
    have he1pc : e1.pc = "us_run_long.exit" := by simp only [e1, s1, withEnv]
    have he1pre : e1.pre = some "while.end35" := by simp only [e1, s1, withEnv]
    have he1mem : e1.mem = e.mem := by simp only [e1, s1, withEnv]
    have hsrcfull : readBytes e1.mem (b + iN) ((n - iN) + 32) = some B := by
      rw [he1mem]; exact hsrcfullAll
    have hsub38c : lookupName e1.env "%sub38" =
        some (.int 64 (BitVec.ofNat 64 (n - iN))) := by
      simp only [e1, envW, s1, withEnv, udWhileEnd35Env]
      rw [← hsubeq]
      ud_lk
    have hjcell : lookupName e1.env "%j.0.lcssa" =
        some (.int 64 (BitVec.ofNat 64 jN)) := by
      simp only [e1, envW, s1, withEnv, udWhileEnd35Env]; ud_lk
    have hkcell : lookupName e1.env "%k.1.lcssa" =
        some (.int 64 (BitVec.ofNat 64 nps)) := by
      simp only [e1, envW, s1, withEnv, udWhileEnd35Env]; ud_lk
    have hxjcell : lookupName e1.env "%xj" = some (.ptr xj) := by
      simp only [e1, envW, s1, withEnv]; exact hxjc
    have hsrcb : lookupName e1.env "%add.ptr36" = some (.ptr (b + iN)) := by
      simp only [e1, envW, s1, withEnv, udWhileEnd35Env]
      rw [show (BitVec.ofNat 64 iN).toNat = iN from by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega]
      ud_lk
    have hdstb : lookupName e1.env "%add.ptr37" = some (.ptr (dst0 + jN)) := by
      simp only [e1, envW, s1, withEnv, udWhileEnd35Env]
      rw [show (BitVec.ofNat 64 jN).toNat = jN from by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega]
      ud_lk
    have hsub64 : (BitVec.ofNat 64 (n - iN)).toNat ≤ 64 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hkres : (BitVec.ofNat 64 (64 * 0)).toNat + (BitVec.ofNat 64 (n - iN)).toNat = n - iN := by
      rw [show (BitVec.ofNat 64 (64 * 0)).toNat = 0 from by decide,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hdstread : readBytes e1.mem (dst0 + jN) (BitVec.ofNat 64 (64 * 0)).toNat =
        some (List.take (BitVec.ofNat 64 (64 * 0)).toNat B) := by
      rw [show (BitVec.ofNat 64 (64 * 0)).toNat = 0 from by decide]
      rfl
    obtain ⟨o, jt, hjt, htailrun, hpost⟩ :=
      copyTail_run hstageKeep hi hjN hji hnpsle hbodyE hextraE hgoal hBdef
        (e := e1) (prev := "while.end35") (opk := .imm (.int 64 (BitVec.ofInt 64 0)))
        (ops := .reg "%sub38") (k := BitVec.ofNat 64 (64 * 0))
        (subB := BitVec.ofNat 64 (n - iN))
        he1pc he1pre (by decide)
        (by show evalOperand (withEnv e1.env e1) (.imm (.int 64 (BitVec.ofInt 64 0))) =
              some (.int 64 (BitVec.ofNat 64 (64 * 0)))
            rw [show BitVec.ofInt 64 0 = BitVec.ofNat 64 (64 * 0) from by decide]; rfl)
        (by decide)
        (by show evalOperand (withEnv (("%k.0.i.lcssa", .int 64 (BitVec.ofNat 64 (64 * 0))) ::
              e1.env) e1) (.reg "%sub38") = some (.int 64 (BitVec.ofNat 64 (n - iN)))
            simp only [withEnv, evalOperand]
            rw [lookupName_cons_ne _ _ (by decide)]
            exact hsub38c)
        hsrcb hdstb hsub38c hjcell hkcell hxjcell hkres hsub64 hpref hdstread hsrcfull
        hframe hdisj
    refine ⟨o, 1 + jt, ?_, ?_, hpost⟩
    · omega
    · rw [runFuel_jump_prefix hstep jt]
      exact htailrun


/-- **The exit stage.**  Every state the exit word admits completes at the record's
post within the exit allowance.

The six branches split along what the running block does.  The two `cleanup41`
predecessors are the two continuations already proved here: the refusal and the
successful return are one control step each and their stores are the branch's.  The two
`while.end35` branches are the final copy's whole run, `whileEnd35_run`: the latch
enters it with the walk's cursor and prefix, and the entry enters it with the
seed's zero cursor and empty prefix, both supplied by the block's own `phi`
operands.  The two remaining edges — `while.body6`'s and `while.body`'s — are the
positions the staging's range clause excludes, so a state admitting either is
absurd at an admissible staging.

The exit allowance is the staging's own `n / 64 + 7`: `expandExitFuel_eq` reads
`expandBodyLen` off the argument list `ExpandStaging` pins, and the final copy's
`finalCopy_fuel_le` is what fits the copy, the tail and the return inside it. -/
theorem expandExit_satisfied
    {args : List Value} {mem : Mem} {next : Nat} {body : List UInt8}
    {st : ClassState} {dst0 nps : Nat} {goal : EscapeOutcome} {b xp tab : Nat}
    {pos0 n : Nat} {ps : List Nat} {err xj : Nat} :
    ExpandExit args mem next body st dst0 nps goal b xp tab pos0 n ps err xj := by
  intro e hexit hword
  -- the word's own staging, kept whole: the branches read it and its clauses are
  -- destructured below, which would consume it
  obtain ⟨hstage, hbr⟩ := hword
  have hstaging := hstage
  obtain ⟨-, hargs, -, hbodyE, h32, hdec, hmap, -, -, -, hwalk⟩ := hstage
  obtain ⟨addv, hdecv⟩ := hdec
  obtain ⟨extra, hextraE⟩ := ExpandStaging.tail_read hstaging
  obtain ⟨k0, -, -, hwalkeq⟩ := hwalk
  have hn64 : n < 2 ^ 64 := by omega
  have hfuel : expandExitFuel args = n / 64 + 7 := by
    rw [hargs, expandExitFuel_eq hn64]
  rcases hbr with hL | hE | hB6 | hB | hS | hR
  · -- the latch: `cleanup32 → while.end35`, the copy loop then the tail
    obtain ⟨hpc, hprevL, ⟨c, hdl⟩, ⟨add24o, hcell24, hle24⟩, hp, hxpL, htabL,
      hpos0L, hnL, herrL, hxjL, hframeL⟩ := hL
    obtain ⟨i, out, j, add24, add28, paddr, xpaddr, tabaddr, errL, xjaddr, pos0v,
      addvL, nv, hpcD, hinvd, hc, hj3, hjlen, hadd24, hadd24i, hadd28, hadd28c,
      hpD, hdstD, hxpD, htabD, herrD, hxjD, hpos0D, haddD, hnD⟩ := hdl
    have hadd24eq : add24o = add24 := by
      have hv : (Value.int 64 add24o) = (Value.int 64 add24) :=
        Option.some.inj (hcell24.symm.trans hadd24)
      cases hv; rfl
    rw [hadd24eq] at hle24
    have hile : i ≤ n := by omega
    have hji : out.length ≤ i :=
      DecodeInv.out_length_le_cursor hinvd hc hbodyE hwalkeq hmap
    have hout64 : out.length < 2 ^ 64 := by omega
    have hnpsle : nps ≤ n := by
      have hlen := hinvd.length
      have hble := escAt_length_le body st 0
      have hblen : body.length = n := JsonEntrySteps.readBytes_length mem b n hbodyE
      omega
    have hgoal : goal = .decoded (out ++ body.drop i) nps := by
      have h := DecodeInv.exit hinvd hc
      rw [h, hc]
    have hjEq : j = BitVec.ofNat 64 out.length := by
      refine BitVec.toNat_inj.1 ?_
      rw [hjlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hout64]
    have hiEq : add24 = BitVec.ofNat 64 i := by
      refine BitVec.toNat_inj.1 ?_
      rw [hadd24i, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hkEq : add28 = BitVec.ofNat 64 nps := by
      refine BitVec.toNat_inj.1 ?_
      rw [hadd28c, hc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hopj : evalOperand (withEnv e.env e) (.reg "%j.3") =
        some (.int 64 (BitVec.ofNat 64 out.length)) := by
      show lookupName e.env "%j.3" = some (.int 64 (BitVec.ofNat 64 out.length))
      rw [← hjEq]; exact hj3
    have hopi : evalOperand (withEnv (("%j.0.lcssa", .int 64 (BitVec.ofNat 64 out.length)) ::
        e.env) e) (.reg "%add24") = some (.int 64 (BitVec.ofNat 64 i)) := by
      show lookupName (("%j.0.lcssa", .int 64 (BitVec.ofNat 64 out.length)) :: e.env)
        "%add24" = some (.int 64 (BitVec.ofNat 64 i))
      rw [lookupName_cons_ne _ _ (by decide), ← hiEq]
      exact hadd24
    have hopk : evalOperand (withEnv (("%i.0.lcssa", .int 64 (BitVec.ofNat 64 i)) ::
        ("%j.0.lcssa", .int 64 (BitVec.ofNat 64 out.length)) :: e.env) e)
        (.reg "%add28") = some (.int 64 (BitVec.ofNat 64 nps)) := by
      show lookupName (("%i.0.lcssa", .int 64 (BitVec.ofNat 64 i)) ::
        ("%j.0.lcssa", .int 64 (BitVec.ofNat 64 out.length)) :: e.env)
        "%add28" = some (.int 64 (BitVec.ofNat 64 nps))
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide), ← hkEq]
      exact hadd28
    obtain ⟨o, jf, hjf, hrun, hpost⟩ :=
      whileEnd35_run (iN := i) (jN := out.length) hstaging hile rfl hji hnpsle
        hbodyE hextraE hgoal hpc hprevL
        (by decide) (by decide) (by decide) hopj hopi hopk hp hdstD hnL hxjL
        hinvd.stored hframeL
    exact ⟨o, by rw [hfuel]; exact runFuel_mono_le hjf hrun, hpost⟩
  · -- the entry: `while.end → while.end35`, the copy from the body's first byte
    obtain ⟨hpc, hprevE, hinvd, hkcell, hp, hdst, hxpE, htabE, hpos0E, hnE, herrE,
      hxjE, hframeE⟩ := hE
    have hnpsle : nps ≤ n := by
      have hlen := hinvd.length
      have hble := escAt_length_le body st 0
      have hblen : body.length = n := JsonEntrySteps.readBytes_length mem b n hbodyE
      omega
    have hgoal : goal = .decoded ([] ++ body.drop 0) nps := DecodeInv.exit hinvd rfl
    have hopj : evalOperand (withEnv e.env e) (.imm (.int 64 (BitVec.ofInt 64 0))) =
        some (.int 64 (BitVec.ofNat 64 0)) := by
      show evalOperand e (.imm (.int 64 (BitVec.ofInt 64 0))) = some (.int 64 (BitVec.ofNat 64 0))
      rw [show BitVec.ofInt 64 0 = BitVec.ofNat 64 0 from by decide]
      rfl
    have hopi : evalOperand (withEnv (("%j.0.lcssa", .int 64 (BitVec.ofNat 64 0)) ::
        e.env) e) (.imm (.int 64 (BitVec.ofInt 64 0))) =
        some (.int 64 (BitVec.ofNat 64 0)) := by
      show evalOperand e (.imm (.int 64 (BitVec.ofInt 64 0))) = some (.int 64 (BitVec.ofNat 64 0))
      rw [show BitVec.ofInt 64 0 = BitVec.ofNat 64 0 from by decide]
      rfl
    have hopk : evalOperand (withEnv (("%i.0.lcssa", .int 64 (BitVec.ofNat 64 0)) ::
        ("%j.0.lcssa", .int 64 (BitVec.ofNat 64 0)) :: e.env) e)
        (.reg "%k.0.lcssa") = some (.int 64 (BitVec.ofNat 64 nps)) := by
      show lookupName (("%i.0.lcssa", .int 64 (BitVec.ofNat 64 0)) ::
        ("%j.0.lcssa", .int 64 (BitVec.ofNat 64 0)) :: e.env) "%k.0.lcssa" =
        some (.int 64 (BitVec.ofNat 64 nps))
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      exact hkcell
    obtain ⟨o, jf, hjf, hrun, hpost⟩ :=
      whileEnd35_run (iN := 0) (jN := 0) (out := []) hstaging (by omega) rfl (by omega)
        hnpsle hbodyE hextraE hgoal hpc hprevE
        (by decide) (by decide) (by decide) hopj hopi hopk hp hdst hnE hxjE
        hinvd.stored hframeE
    exact ⟨o, by rw [hfuel]; exact runFuel_mono_le hjf hrun, hpost⟩
  · exact absurd hB6 (assemblyWhileBody6Exit_vacuous hdecv)
  · exact absurd hB (assemblyWhileBodyExit_vacuous hdecv)
  · exact successExit_post hstaging e hS
  · exact refusalExit_post hstaging e hR

/-- info: 'LeanLLVM.Vellum.expandExit_satisfied' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expandExit_satisfied

/-- info: 'LeanLLVM.Vellum.whileEnd35_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms whileEnd35_run

/-- info: 'LeanLLVM.Vellum.readBytes_writeBytes_thirtyTwo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_writeBytes_thirtyTwo

/-- info: 'LeanLLVM.Vellum.readBytes_copy2Mem_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_copy2Mem_prefix

/-- info: 'LeanLLVM.Vellum.UnchangedOutside.writeBytes_inside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms UnchangedOutside.writeBytes_inside

/-- info: 'LeanLLVM.Vellum.copyPreLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms copyPreLoop

/-- info: 'LeanLLVM.Vellum.finalSource_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms finalSource_read

/-- info: 'LeanLLVM.Vellum.finalSource_take' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms finalSource_take

/-- info: 'LeanLLVM.Vellum.DecodeInv.out_length_le_cursor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms DecodeInv.out_length_le_cursor

/-- info: 'LeanLLVM.Vellum.readBytes_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_congr

/-- info: 'LeanLLVM.Vellum.readBytes_of_UnchangedOutside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_of_UnchangedOutside

/-- info: 'LeanLLVM.Vellum.UnchangedOutside.comp' does not depend on any axioms -/
#guard_msgs in
#print axioms UnchangedOutside.comp

/-- info: 'LeanLLVM.Vellum.UnchangedOutside.writeBytes_in' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms UnchangedOutside.writeBytes_in

/-- info: 'LeanLLVM.Vellum.ofNat_sub_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ofNat_sub_toNat

/-- info: 'LeanLLVM.Vellum.ofNat_sub_ofNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ofNat_sub_ofNat

/-- info: 'LeanLLVM.Vellum.take_left_of_body' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms take_left_of_body

/-- info: 'LeanLLVM.Vellum.finalCopy_fuel_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms finalCopy_fuel_le

/-- info: 'LeanLLVM.Vellum.expandExitFuel_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms expandExitFuel_eq

/-- info: 'LeanLLVM.Vellum.entryExit_admits_clobbered_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entryExit_admits_clobbered_err

/-- info: 'LeanLLVM.Vellum.latchExit_admits_cursor_past_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms latchExit_admits_cursor_past_body

/-- info: 'LeanLLVM.Vellum.entryExit_clobbered_err_excluded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms entryExit_clobbered_err_excluded

/-- info: 'LeanLLVM.Vellum.latchExit_cursor_excluded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms latchExit_cursor_excluded

/-- info: 'LeanLLVM.Vellum.bodyExit_admits_clobbered_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bodyExit_admits_clobbered_body

/-- info: 'LeanLLVM.Vellum.bodyExit_clobbered_body_excluded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bodyExit_clobbered_body_excluded

/-- info: 'LeanLLVM.Vellum.entryExit_admits_free_dst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entryExit_admits_free_dst

/-- info: 'LeanLLVM.Vellum.entryExit_free_dst_excluded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entryExit_free_dst_excluded

/-- info: 'LeanLLVM.Vellum.take_of_take' depends on axioms: [propext] -/
#guard_msgs in
#print axioms take_of_take

/-- info: 'LeanLLVM.Vellum.take32_drop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms take32_drop

/-- info: 'LeanLLVM.Vellum.copyIterBound_succ_mul_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms copyIterBound_succ_mul_le

/-- info: 'LeanLLVM.Vellum.tailDst_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tailDst_read

/-- info: 'LeanLLVM.Vellum.copyTail_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms copyTail_run

end LeanLLVM.Vellum
