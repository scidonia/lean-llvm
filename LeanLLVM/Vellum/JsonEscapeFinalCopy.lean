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

**What is here and what is not.**  The copy loop, the two source facts and the
relation `DecodeInv.out_length_le_cursor` states are proved, and the relation is
*derived* rather than assumed: the list the staging decodes is `(ps.map …).drop k0`,
`Spaced` is not suffix-closed on the nose — a `control`/`refuse` constructor's tail is
unconstrained — but a suffix of the body's own position list is still a cursor list,
and `JsonEscapeSteps.escAt_drop_spaced` is that fact (`Spaced.mono` lowers the cursor
back to the resumed walk's own zero; it lives beside `Spaced` in `JsonEscapeSpec`).

The suffix itself — `while.end35` into the copy, `us_run_long.exit` through
`if.then.i109` and `us_run.exit112` into `cleanup41`, and the two `while.end35`
branch continuations that consume it — is *not* written, and the reason is not a
lemma: the exit words do not carry what it reads.  The final copy needs the body's
bytes and its thirty-two trailing bytes at the *exit* state's memory, the offset
slot's read, and (at the latch) a byte cursor inside the body, and the words'
clauses are silent on all three — `entryExit_admits_clobbered_err` and
`latchExit_admits_cursor_past_body` are states that satisfy `assemblyExitWord` and
differ from what the run leaves in exactly one of them.  `finalCopy_fuel_le` is the
arithmetic that composition ends in, so the segment's allowance is not what is
missing.
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
    (m0 : Mem) (regw : Nat) (hshift : dst0 + j = dst)
    (hfit : j + sub + 64 ≤ regw) : BoundLoop escapeCalls usDecFunction where
  head := copyBodyNNames.head
  exitBlock := copyBodyNNames.tail
  N := copyIterBound sub
  cost := 1
  Inv := fun r s c =>
    CopyInv copyBodyNNames src dst sub B r c s ∧ readBytes s.mem dst0 j = some out ∧
      UnchangedOutside m0 s.mem [(dst0, regw)]
  atBound := copyAtBound sub
  Exit := fun e => e.pc = copyBodyNNames.tail
  ExitWord := fun e =>
    CopyExitWord copyBodyNNames src dst sub B e ∧ readBytes e.mem dst0 j = some out ∧
      UnchangedOutside m0 e.mem [(dst0, regw)]
  step_exit := by
    intro r s c h hat
    obtain ⟨hcopy, hpref, hframe⟩ := h
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
    · refine ⟨?_, ?_, ?_⟩
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
  step_loop := by
    intro r s c h hat
    obtain ⟨hcopy, hpref, hframe⟩ := h
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
    · refine ⟨?_, ?_, ?_⟩
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
  exit_at_zero := by
    intro s c h
    obtain ⟨hcopy, _, _⟩ := h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hhi⟩ := hcopy
    show decide (copyIterBound sub ≤ c) = true
    exact decide_eq_true (by omega)
  budget := by
    intro r s c h
    obtain ⟨hcopy, _, _⟩ := h
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

/-- **The entry branch admits an offset slot the run will not overwrite.**  The
state is the word's entry edge at the witness staging, with the offset slot's eight
bytes replaced: the frame names `(err, 8)` as a region, so the word does not read the
slot, and the success path writes only the destination and the cursor. -/
theorem entryExit_admits_clobbered_err :
    ∃ e : State,
      assemblyExitWord exitWitnessArgs exitWitnessMem 0 [] ⟨true, false⟩ 200 0
        (.decoded [] 0) 100 700 400 0 0 [] 800 900 e ∧
      readBytes e.mem 800 8 ≠ readBytes exitWitnessMem 800 8 := by
  have hframe : UnchangedOutside exitWitnessMem
      (writeBytes exitWitnessMem 800 (List.replicate 8 (7 : UInt8)))
      [(200, 0 + 64), (700, 4 * 0), (900, 8), (800, 8)] := by
    intro a ha
    have hd : a < 800 ∨ 800 + 8 ≤ a := by
      rcases Nat.lt_or_ge a 800 with h | h
      · exact Or.inl h
      · exact Or.inr (by
          have := ha (800, 8) (by simp)
          omega)
    rw [readByte_writeBytes_outside _ _ (by simpa using hd)]
  refine ⟨modelState
    [("%k.0.lcssa", .int 64 0), ("%p", .ptr 100), ("%xp", .ptr 700),
     ("%tab", .ptr 400), ("%pos0", .int 64 0), ("%n", .int 64 0),
     ("%err", .ptr 800), ("%xj", .ptr 900), ("%dst", .ptr 200)]
    (writeBytes exitWitnessMem 800 (List.replicate 8 (7 : UInt8)))
    "while.end35" (some "while.end"), ⟨?_, ?_⟩⟩
  · -- the word
    refine ⟨exitWitness_staging, Or.inr (Or.inl ?_)⟩
    refine ⟨rfl, rfl, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- the walk's seed
      show escapeDecodeGo [] 0 0 ((escAt [] ⟨true, false⟩ 0).drop 0) [] = .decoded [] 0
      rw [exitWitness_escAt, List.drop_zero]
      exact escapeDecodeGo_nil ([] : List UInt8) 0 0 []
    · rfl
    · show (escAt ([] : List UInt8) ⟨true, false⟩ 0).length = 0
      rw [exitWitness_escAt]; rfl
    all_goals (first | exact hframe | rfl | (simp only [modelState, lookupName]; simp))
  · -- the slot differs
    intro hcontra
    have hmem : (modelState
        [("%k.0.lcssa", .int 64 0), ("%p", .ptr 100), ("%xp", .ptr 700),
         ("%tab", .ptr 400), ("%pos0", .int 64 0), ("%n", .int 64 0),
         ("%err", .ptr 800), ("%xj", .ptr 900), ("%dst", .ptr 200)]
        (writeBytes exitWitnessMem 800 (List.replicate 8 (7 : UInt8)))
        "while.end35" (some "while.end")).mem
        = writeBytes exitWitnessMem 800 (List.replicate 8 (7 : UInt8)) := rfl
    have h1 : readBytes (writeBytes exitWitnessMem 800 (List.replicate 8 (7 : UInt8)))
        800 8 = some (List.replicate 8 (7 : UInt8)) := by
      simpa using readBytes_writeBytes_same exitWitnessMem
        (List.replicate 8 (7 : UInt8)) (addr := 800)
    have h2 : readBytes exitWitnessMem 800 8 = some (List.replicate 8 (0 : UInt8)) :=
      exitWitness_zeros_high (by omega) (by omega)
    rw [hmem, h1, h2] at hcontra
    exact absurd hcontra (by decide)

/-- **The latch branch admits a byte cursor past the body.**  At the same staging, a
state whose `%add24` — the cell `while.end35` copies into `%i.0.lcssa` — is `5` for a
zero-length body satisfies the word: the walk at cursor `5` has the same outcome
(`.decoded [] 0`), because the trailing copy's `body.drop 5` is empty.  `while.end35`
then forms `%sub38 = 0 - 5`, and the copy's residual wraps. -/
theorem latchExit_admits_cursor_past_body :
    ∃ e : State,
      assemblyExitWord exitWitnessArgs exitWitnessMem 0 [] ⟨true, false⟩ 200 0
        (.decoded [] 0) 100 700 400 0 0 [] 800 900 e ∧
      lookupName e.env "%add24" = some (.int 64 (BitVec.ofNat 64 5)) := by
  have hframe : UnchangedOutside exitWitnessMem exitWitnessMem
      [(200, 0 + 64), (700, 4 * 0), (900, 8), (800, 8)] := fun a _ => rfl
  refine ⟨modelState
    [("%j.3", .int 64 0), ("%add24", .int 64 (BitVec.ofNat 64 5)),
     ("%add28", .int 64 0), ("%p", .ptr 100), ("%dst", .ptr 200),
     ("%xp", .ptr 700), ("%tab", .ptr 400), ("%err", .ptr 800),
     ("%xj", .ptr 900), ("%pos0", .int 64 0), ("%add", .int 64 0),
     ("%n", .int 64 0)]
    exitWitnessMem "while.end35" (some "cleanup32"), ⟨?_, ?_⟩⟩
  · -- the word
    refine ⟨exitWitness_staging, Or.inl ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · rfl
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
    · simp only [modelState, lookupName]; simp
    · simp only [modelState, lookupName]; simp
    · simp only [modelState, lookupName]; simp
    · simp only [modelState, lookupName]; simp
    · simp only [modelState, lookupName]; simp
    · simp only [modelState, lookupName]; simp
    · simp only [modelState, lookupName]; simp
    · exact hframe
  · -- `%add24` is the cursor
    simp only [modelState, lookupName]
    simp

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

end LeanLLVM.Vellum
