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

**What is here and what is not.**  The copy loop and the two source facts are
proved.  `DecodeInv.out_length_le_cursor` takes the spacing of the *resumed* list —
the staging list after its first `k0` entries — as a hypothesis: the list the
staging decodes is `(ps.map …).drop k0`, and `Spaced` is not suffix-closed on the
nose, because a `control`/`refuse` constructor's tail is unconstrained.  Deriving
that spacing needs the walk's own non-refusal, which is not in this module.  The
suffix from `us_run_long.exit` through `us_run.exit112` and `cleanup41`, and the
two `while.end35` branch continuations that consume it, are not written here.
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

/-- A write inside a region leaves every byte outside the region as it was, so a
frame over that region carries through it. -/
theorem UnchangedOutside.writeBytes_inside {m0 m : Mem} {lo w a : Nat} {bs : List UInt8}
    (h : UnchangedOutside m0 m [(lo, w)]) (ha : lo ≤ a) (hb : a + bs.length ≤ lo + w) :
    UnchangedOutside m0 (writeBytes m a bs) [(lo, w)] := by
  intro x hx
  have hx' : ¬ (lo ≤ x ∧ x < lo + w) := hx (lo, w) (by simp) 
  rw [readByte_writeBytes_outside m bs (show x < a ∨ a + bs.length ≤ x by omega)]
  exact h x (by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact hx')

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

/-- A list spaced at a cursor is still spaced at a smaller one. -/
theorem Spaced.mono {bs : List UInt8} : ∀ {i : Nat} {ps : List Nat},
    Spaced bs i ps → ∀ {i' : Nat}, i' ≤ i → Spaced bs i' ps
  | _, _, Spaced.nil i, i', _ => Spaced.nil i'
  | _, _, Spaced.control i q qs b hiq hb hctl, i', hi =>
      Spaced.control i' q qs b (by omega) hb hctl
  | _, _, Spaced.refuse i q qs hiq hlt hnone, i', hi =>
      Spaced.refuse i' q qs (by omega) hlt hnone
  | _, _, Spaced.step i q qs adv bytes b hiq hb hctl hesc hlen hadv ih, i', hi =>
      Spaced.step i' q qs adv bytes b (by omega) hb hctl hesc hlen hadv
        (Spaced.mono ih (by omega))

/-- **The decoded prefix fits its cursor, from the staging's spacing.**  The
staging's walk and the exit's walk are the same decode written two ways:
`goal = .decoded (out ++ body.drop i) k`, and a walk whose position list is spaced
writes at most the body's length.  The spacing of the *resumed* list — the staging
list after its first `k0` entries — is a hypothesis here rather than derived: the
list the staging decodes is `(ps.map …).drop k0`, and `Spaced` is not suffix-closed
on the nose (a `control`/`refuse` constructor's tail is unconstrained), so the
drop needs the walk's own non-refusal, not the relation alone.  That derivation is
the remaining obligation; everything below it is stated at this fact. -/
theorem DecodeInv.out_length_le_cursor {body : List UInt8} {st : ClassState}
    {M mem : Mem} {dst nps i k : Nat} {out : List UInt8} {goal : EscapeOutcome}
    {b n pos0 k0 : Nat} {ps : List Nat}
    (hinv : DecodeInv body st M dst nps i k out goal) (hk : k = nps)
    (hbody : readBytes mem b n = some body)
    (hwalkeq : goal = escapeDecodeGo body 0 k0
      ((ps.map (fun q => q - pos0)).drop k0) [])
    (hsp : Spaced body 0 ((ps.map (fun q => q - pos0)).drop k0)) :
    out.length ≤ i := by
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


/-! ### Axiom footprints

The pins are the module's instrument.  `copyPreLoop` and
`UnchangedOutside.writeBytes_inside` carry the one `Classical.choice` the copy
already carries — `BitVec.signExtend_eq`, the sign-extension width equality the
trace's step facts take as a hypothesis — and nothing else leaves the ceiling. -/

/-- info: 'LeanLLVM.Vellum.readBytes_writeBytes_thirtyTwo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_writeBytes_thirtyTwo

/-- info: 'LeanLLVM.Vellum.readBytes_copy2Mem_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_copy2Mem_prefix

/-- info: 'LeanLLVM.Vellum.UnchangedOutside.writeBytes_inside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
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

/-- info: 'LeanLLVM.Vellum.Spaced.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Spaced.mono

/-- info: 'LeanLLVM.Vellum.DecodeInv.out_length_le_cursor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms DecodeInv.out_length_le_cursor

end LeanLLVM.Vellum
