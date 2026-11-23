import LeanLLVM.Refinement.JsonStage2StringBodyJoin
import LeanLLVM.Refinement.JsonStage2StringBodyNoList

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)

/-! ### The decoded arm's stage, and the refusal's offset

The two facts the remaining arms need and this module did not yet have.  The
decoded answer's clause at variable leaves is the refused one's dual: its memory is
the callee's chain with `Woff`/`Wj` as lists, so a consumer that names the stage
unifies by structure rather than comparing a chain whose leaves are literals.  The
refusal's offset is bounded by the body's length, because the walk refuses only at a
position it has just found below it — which is what makes the offset's `Nat` and its
64-bit spelling the same number at the record. -/

theorem s2StringBodyExpand_decoded_named {mem xmem : Mem} {p dst xp xj : Nat}
    {len nxp : BitVec 64} {base c1 ei next lane k : Nat} {ps : List Nat}
    {body out : List UInt8} {Woff Wj : List UInt8}
    (hmem : xmem = writeBytes mem xj (wordBytes 8 c1))
    (hps : readLanes32 mem xp nxp.toNat = some ps)
    (hbody : readBytes mem p len.toNat = some body)
    (hlane : ps[c1]? = some lane) (hge : p - base ≤ lane)
    (hp0 : p - base < 2 ^ 64) (hc1 : c1 < 2 ^ 64)
    (hWoff : Woff = wordBytes 8 out.length) (hWj : Wj = wordBytes 8 (c1 + k))
    (hxjp : RegionsApart xj 8 p len.toNat)
    (heip : RegionsApart ei 8 p len.toNat)
    (heixj : RegionsApart ei 8 xj 8)
    (heilan : ∀ j, j < nxp.toNat → xp + 4 * j + 4 ≤ ei ∨ ei + 8 ≤ xp + 4 * j)
    (hjlan : ∀ j, j < nxp.toNat → xp + 4 * j + 4 ≤ xj ∨ xj + 8 ≤ xp + 4 * j)
    (hdec : escapeDecodeGo body 0 0
      (((ps.drop c1).takeWhile (fun q => decide (q < p - base + len.toNat))).map
        (fun q => q - (p - base))) [] = .decoded out k) :
    s2StringBodyCalls "leanllvm_json_escape_expand"
      [.ptr p, .int 64 len, .ptr dst, .ptr ei, .ptr xp, .ptr xj, .int 64 nxp,
       .int 64 (BitVec.ofNat 64 (p - base))]
      (writeBytes xmem ei (natToBytes (0#64).toNat 8)) next =
    some { ret := .int 64 (BitVec.ofNat 64 out.length),
           mem := writeBytes
             (writeBytes (writeBytes (writeBytes xmem ei (natToBytes (0#64).toNat 8))
               dst out) xj Wj) ei Woff,
           next := next } := by
  rw [hWoff, hWj]
  exact s2StringBodyExpand_decoded_at_exit (ch := 0) (dst := dst) (next := next)
    (hps := hps) (hbody := hbody) (hlane := hlane) (hge := hge) (hp0 := hp0)
    (hc1 := hc1) (hxjp := hxjp) (heip := heip) (heixj := heixj)
    (heilan := heilan) (hjlan := hjlan) (hmem := hmem) (hdec := hdec)


theorem s2StringBodyMemory_decoded_cursor (mem : Mem) {ei dst xj outn c1 k : Nat}
    {out : List UInt8}
    (hdst : readBytes mem dst out.length ≠ none)
    (hxj : readBytes mem xj 8 ≠ none)
    (houtn : readBytes mem outn 8 ≠ none)
    (hd_ei : ei + 8 ≤ dst ∨ dst + out.length ≤ ei)
    (hx_ei : ei + 8 ≤ xj ∨ xj + 8 ≤ ei)
    (hd_xj : dst + out.length ≤ xj ∨ xj + 8 ≤ dst)
    (ho_ei : ei + 8 ≤ outn ∨ outn + 8 ≤ ei)
    (ho_d : outn + 8 ≤ dst ∨ dst + out.length ≤ outn)
    (ho_x : outn + 8 ≤ xj ∨ xj + 8 ≤ outn) :
    writeBytes
        (s2StringBodyExpandMem (writeBytes mem xj (wordBytes 8 c1)) ei dst xj out
          (wordBytes 8 (c1 + k)))
        outn (natToBytes out.length 8)
      = s2StringBodyDecodedMem mem dst xj outn ei (wordBytes 8 (c1 + k)) out := by
  simp only [s2StringBodyExpandMem, s2StringBodyDecodedMem]
  have hX : (natToBytes (0#64).toNat 8).length = 8 := natToBytes_length _ _
  have hc1l : (wordBytes 8 c1).length = 8 := natToBytes_length _ _
  have hWl : (wordBytes 8 (c1 + k)).length = 8 := natToBytes_length _ _
  obtain ⟨C₀, hC₀⟩ := exists_readBytes_of_ne hxj
  -- 1. the cursor write crosses the slot's clear, spending the cursor word's
  --    presence — the slot's own is not read
  rw [writeBytes_comm_of_present_left mem xj (wordBytes 8 c1) ei
    (natToBytes (0#64).toNat 8) ⟨C₀, by rw [hc1l]; exact hC₀⟩
    (by rw [hc1l, hX]; exact hx_ei.symm)]
  -- 2. and then the body's window write
  have hxj' : readBytes (writeBytes mem ei (natToBytes (0#64).toNat 8)) xj 8 ≠ none := by
    rcases hx_ei with h | h
    · rw [s2StringBodyReadBytes_above mem (natToBytes (0#64).toNat 8) 8 xj ei
        (by rw [hX]; exact h)]
      exact hxj
    · rw [readBytes_writeBytes_below mem (natToBytes (0#64).toNat 8) 8 xj ei h]
      exact hxj
  have hdst' : readBytes (writeBytes mem ei (natToBytes (0#64).toNat 8)) dst
      out.length ≠ none := by
    rcases hd_ei with h | h
    · rw [s2StringBodyReadBytes_above mem (natToBytes (0#64).toNat 8) out.length dst ei
        (by rw [hX]; exact h)]
      exact hdst
    · rw [readBytes_writeBytes_below mem (natToBytes (0#64).toNat 8) out.length dst ei h]
      exact hdst
  obtain ⟨C₁, hC₁⟩ := exists_readBytes_of_ne hxj'
  obtain ⟨D₁, hD₁⟩ := exists_readBytes_of_ne hdst'
  rw [writeBytes_comm_of_present (writeBytes mem ei (natToBytes (0#64).toNat 8)) xj
    (wordBytes 8 c1) dst out ⟨C₁, by rw [hc1l]; exact hC₁⟩ ⟨D₁, hD₁⟩
    (by rw [hc1l]; exact hd_xj.symm)]
  -- 3. the two cursor writes are adjacent: the first is erased
  rw [writeBytes_writeBytes_same (writeBytes (writeBytes mem ei (natToBytes (0#64).toNat 8))
    dst out) xj (wordBytes 8 c1) (wordBytes 8 (c1 + k)) (by rw [hc1l, hWl])]
  -- 4. the join, at its named memories
  exact s2StringBodyMemory_decoded_named mem hdst hxj houtn hd_ei hx_ei hd_xj
    ho_ei ho_d ho_x


theorem escapeDecodeGo_refused_lt (bs : List UInt8) :
    ∀ (ps : List Nat) (i k : Nat) (out : List UInt8) (off ks : Nat),
      escapeDecodeGo bs i k ps out = .refused off ks → off < bs.length := by
  have key : ∀ (n : Nat) (ps : List Nat), ps.length ≤ n →
      ∀ (i k : Nat) (out : List UInt8) (off ks : Nat),
        escapeDecodeGo bs i k ps out = .refused off ks → off < bs.length := by
    intro n
    induction n with
    | zero =>
        intro ps hps i k out off ks h
        cases ps with
        | nil => simp only [escapeDecodeGo] at h; exact absurd h (by simp)
        | cons q qs => simp at hps
    | succ n ih =>
        intro ps hps i k out off ks h
        cases ps with
        | nil => simp only [escapeDecodeGo] at h; exact absurd h (by simp)
        | cons q qs =>
            simp only [escapeDecodeGo] at h
            split at h
            · exact absurd h (by simp)
            · split at h
              · exact absurd h (by simp)
              · split at h
                · simp only [EscapeOutcome.refused.injEq] at h
                  obtain ⟨rfl, -⟩ := h
                  exact lt_length_of_getElem?_eq_some (by assumption)
                · split at h
                  · simp only [EscapeOutcome.refused.injEq] at h
                    obtain ⟨rfl, -⟩ := h
                    exact lt_length_of_getElem?_eq_some (by assumption)
                  · split at h
                    · split at h
                      · exact ih [] (by simp) _ _ _ off ks h
                      · exact ih _ (by simp at hps; omega) _ _ _ off ks h
                    · exact ih qs (by simp at hps; omega) _ _ _ off ks h
  exact fun ps => key ps.length ps (le_rfl)


set_option maxHeartbeats 12000000 in
theorem s2StringBodyArm_scan_refused {mem extra : Mem} {x : State}
    {ch p dst outn xp xj : Nat} {len nxp : BitVec 64}
    {base j0 c1 ei next lane offN k e' : Nat} {ps : List Nat} {body : List UInt8}
    {conv : BitVec 64} {Woff Wj : List UInt8} {bs : List UInt8}
    (hpc : x.pc = "land.lhs.true")
    (hmem : x.mem = writeBytes mem xj (wordBytes 8 c1))
    (hC0 : s2StringBodyRefusedC0 mem xj c1 = writeBytes mem xj (wordBytes 8 c1))
    (hexpMem : extra
      = writeBytes
          (writeBytes (writeBytes (s2StringBodyRefusedC0 mem xj c1) ei
            (natToBytes (0#64).toNat 8)) ei Woff) xj Wj)
    (hWoff : Woff = wordBytes 8 offN) (hWj : Wj = wordBytes 8 (c1 + k))
    (hlane : ps[c1]? = some lane) (hge : p - base ≤ lane)
    (hlt : lane < p - base + len.toNat)
    (hconv : lookupName x.env "%conv" = some (.int 64 conv)) (hconvq : conv.toNat = lane)
    (hc : lookupName x.env "%c" = some (.ptr ch))
    (hsub : lookupName x.env "%sub.ptr.sub" =
      some (.int 64 (BitVec.ofNat 64 (p - base))))
    (hlen : lookupName x.env "%len" = some (.int 64 len))
    (hp : lookupName x.env "%p" = some (.ptr p))
    (hdst : lookupName x.env "%dst" = some (.ptr dst))
    (hei : lookupName x.env "%ei" = some (.ptr ei))
    (hxp : lookupName x.env "%xp" = some (.ptr xp))
    (hxj : lookupName x.env "%xj" = some (.ptr xj))
    (hnxp : lookupName x.env "%nxp" = some (.int 64 nxp))
    (hps : readLanes32 mem xp nxp.toNat = some ps)
    (hbody : readBytes mem p len.toNat = some body)
    (hrec : stage2ReadWord mem (ch + 1112) 8 = some e')
    (hj0 : stage2ReadWord mem xj 8 = some j0)
    (hp0 : p - base < 2 ^ 64) (hpw : p - base + len.toNat < 2 ^ 64) (hc1 : c1 < 2 ^ 64)
    (hoffN : offN < 2 ^ 64)
    (hxjp : RegionsApart xj 8 p len.toNat)
    (heip : RegionsApart ei 8 p len.toNat)
    (heixj : RegionsApart ei 8 xj 8)
    (heilan : ∀ j, j < nxp.toNat → xp + 4 * j + 4 ≤ ei ∨ ei + 8 ≤ xp + 4 * j)
    (hjlan : ∀ j, j < nxp.toNat → xp + 4 * j + 4 ≤ xj ∨ xj + 8 ≤ xp + 4 * j)
    (hc1k : c1 + k = c1 + k)
    (hxje : RegionsApart xj 8 (ch + 1112) 8)
    (heie : RegionsApart ei 8 (ch + 1112) 8)
    (hoff : readBytes extra ei 8 = some Woff)
    (hr : escapeDecodeGo body 0 0
      (((ps.drop c1).takeWhile (fun q => decide (q < p - base + len.toNat))).map
        (fun q => q - (p - base))) [] = .refused offN k)
    (hnext : ei = next)
    (hrec_bs : readBytes mem e' stage2ErrorExtent = some bs)
    (hsumW : offN + (p - base) < 2 ^ 64)
    (hmodel : stage2StringBody mem ch p len.toNat dst outn xp xj nxp.toNat =
      some (writeBytes (stage2ErrSetMsg mem e' (p - base + offN) 0) xj
        (wordBytes 8 (c1 + k)), 0, wordBytes 8 offN))
    (hm1 : ei + (wordBytes 8 offN).length ≤ xj ∨
      xj + (wordBytes 8 (c1 + k)).length ≤ ei)
    (hm2 : ei + (wordBytes 8 offN).length ≤ e' ∨
      e' + (natToBytes (0#32).toNat 4).length ≤ ei)
    (hm3 : ei + (wordBytes 8 offN).length ≤ e' + (8#64).toNat ∨
      e' + (8#64).toNat +
        (natToBytes ((BitVec.ofNat 64 offN) + (BitVec.ofNat 64 (p - base))).toNat 8).length
        ≤ ei)
    (hm4 : ei + (wordBytes 8 offN).length ≤ e' + (16#64).toNat ∨
      e' + (16#64).toNat + (natToBytes (0#64).toNat 8).length ≤ ei)
    (hm5 : xj + (wordBytes 8 (c1 + k)).length ≤ e' ∨
      e' + (natToBytes (0#32).toNat 4).length ≤ xj)
    (hm6 : xj + (wordBytes 8 (c1 + k)).length ≤ e' + (8#64).toNat ∨
      e' + (8#64).toNat +
        (natToBytes ((BitVec.ofNat 64 offN) + (BitVec.ofNat 64 (p - base))).toNat 8).length
        ≤ xj)
    (hm7 : xj + (wordBytes 8 (c1 + k)).length ≤ e' + (16#64).toNat ∨
      e' + (16#64).toNat + (natToBytes (0#64).toNat 8).length ≤ xj)
    (hm8 : e' + (natToBytes (0#32).toNat 4).length ≤ e' + (8#64).toNat ∨
      e' + (8#64).toNat +
        (natToBytes ((BitVec.ofNat 64 offN) + (BitVec.ofNat 64 (p - base))).toNat 8).length
        ≤ e')
    (hm9 : e' + (natToBytes (0#32).toNat 4).length ≤ e' + (16#64).toNat ∨
      e' + (16#64).toNat + (natToBytes (0#64).toNat 8).length ≤ e')
    (hm10 : e' + (8#64).toNat +
        (natToBytes ((BitVec.ofNat 64 offN) + (BitVec.ofNat 64 (p - base))).toNat 8).length
        ≤ e' + (16#64).toNat ∨
      e' + (16#64).toNat + (natToBytes (0#64).toNat 8).length ≤ e' + (8#64).toNat) :
    s2StringBodyConcludes
      [.ptr ch, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj,
        .int 64 nxp] mem next 4 x := by
  have hchain : writeBytes
        (writeBytes (writeBytes (s2StringBodyRefusedC0 mem xj c1) ei
          (natToBytes (0#64).toNat 8)) ei Woff) xj Wj
      = s2StringBodyRefusedExtra mem ei xj c1 offN k := by
    rw [s2StringBodyRefusedExtra, s2StringBodyRefusedC3, s2StringBodyRefusedC2,
      s2StringBodyRefusedC1, ← hWoff, ← hWj]
  have hxj8 : readBytes mem xj (wordBytes 8 c1).length ≠ none := by
    intro h
    rw [show (wordBytes 8 c1).length = 8 from natToBytes_length _ _] at h
    rw [readBytes_of_stage2ReadWord hj0] at h
    cases h
  have hC6join := s2StringBodyRefusedC6_join mem hxj8
    (by rw [wordBytes, natToBytes_length, wordBytes, natToBytes_length])
    (by rcases heixj with h | h
        · exact Or.inr (by rw [show (wordBytes 8 offN).length = 8 from natToBytes_length _ _]; exact h)
        · exact Or.inl (by rw [show (wordBytes 8 c1).length = 8 from natToBytes_length _ _]; exact h))
    (by simp only [wordBytes, natToBytes_length]) hxj8
    (s2StringBodyErr_presence hrec_bs).1
    (s2StringBodyErr_presence hrec_bs).2.1 (s2StringBodyErr_presence hrec_bs).2.2
    hm1 hm2 hm3 hm4 hm5 hm6 hm7 hm8 hm9 hm10
    (offN := offN) (k := k) (p := p) (base := base)
  have hM0 : s2StringBodyIfThen12Mem extra e' (BitVec.ofNat 64 offN)
        (BitVec.ofNat 64 (p - base))
      = writeBytes (writeBytes (stage2ErrSetMsg mem e' (p - base + offN) 0) xj
          (wordBytes 8 (c1 + k))) next (wordBytes 8 offN) := by
    rw [hexpMem, hchain, s2StringBodyIfThen12Mem_staged, hC6join,
      s2StringBodyRefusedModel_reconciles mem hoffN hp0 hsumW,
      s2StringBodyRefusedM0, hnext]
  refine ⟨⟨.int 32 (BitVec.ofNat 32 0),
      s2StringBodyIfThen12Mem extra e' (BitVec.ofNat 64 offN)
        (BitVec.ofNat 64 (p - base)),
      next + 8⟩, ?_, ?_, ?_⟩
  · exact s2StringBodyArm_scan_refused_run (outn := outn) (j0 := j0) (next := next)
      (hpc := hpc) (hmem := hmem) (hC0 := hC0)
      (hexpMem := hexpMem) (hWoff := hWoff) (hWj := hWj)
      (hlane := hlane) (hge := hge) (hlt := hlt) (hconv := hconv) (hconvq := hconvq)
      (hc := hc) (hsub := hsub) (hlen := hlen) (hp := hp) (hdst := hdst) (hei := hei)
      (hxp := hxp) (hxj := hxj) (hnxp := hnxp) (hps := hps) (hbody := hbody)
      (hrec := hrec) (hp0 := hp0) (hpw := hpw) (hc1 := hc1) (hoffN := hoffN)
      (hxjp := hxjp) (heip := heip) (heixj := heixj) (heilan := heilan)
      (hjlan := hjlan) (hwjLen := by rw [hWj, wordBytes, natToBytes_length])
      (hc1k := hc1k) (hxje := hxje) (heie := heie) (hoff := hoff) (hr := hr)
  · exact ⟨writeBytes (stage2ErrSetMsg mem e' (p - base + offN) 0) xj
      (wordBytes 8 (c1 + k)), 0, wordBytes 8 offN, hmodel, rfl, hM0, rfl⟩
  · rw [hM0]
    simp only [s2StringBodyFoot, hrec]
    exact ((stage2ErrSetMsg_frame (R := [(xj, 8), (outn, 8), (dst, len.toNat),
        (next, 8), (e', stage2ErrorExtent)])
        ⟨(e', stage2ErrorExtent), by simp, le_rfl, by simp [stage2ErrorExtent]⟩).write_le
      (a := xj) (w := 8) ⟨(xj, 8), by simp, le_rfl, le_rfl⟩
      (by rw [wordBytes, natToBytes_length])).write_le (a := next) (w := 8)
      ⟨(next, 8), by simp, le_rfl, le_rfl⟩ (by rw [wordBytes, natToBytes_length])


set_option maxHeartbeats 12000000 in
set_option maxHeartbeats 12000000 in
/-- **The scan's accepting exit finishes form `2`** at the staging's argument list:
the callee's decoded answer, the model's decoded memory, and the arm's chain joined
by the cursor write's absorption.  The memory's hypotheses are the three regions the
join takes present — `dst`, `xj`, `outn` — pairwise separated, the same facts the
refusing arm spends, at the shorter distance the accepting answer writes.  The
fourth region the chain writes, the slot, is never replaced in: every crossing moves
that write, so its own presence is not a hypothesis. -/
theorem s2StringBodyArm_scan_decoded {mem : Mem} {x : State}
    {ch p dst outn xp xj : Nat} {len nxp : BitVec 64}
    {base c1 ei next lane k e' : Nat} {ps : List Nat} {body out : List UInt8}
    {conv : BitVec 64} {outj : List UInt8}
    (hpc : x.pc = "land.lhs.true")
    (hmem : x.mem = writeBytes mem xj (wordBytes 8 c1))
    (hexp : s2StringBodyCalls "leanllvm_json_escape_expand"
      [.ptr p, .int 64 len, .ptr dst, .ptr ei, .ptr xp, .ptr xj, .int 64 nxp,
       .int 64 (BitVec.ofNat 64 (p - base))]
      (writeBytes x.mem ei (natToBytes (0#64).toNat 8)) x.next =
      some { ret := .int 64 (BitVec.ofNat 64 out.length),
             mem := s2StringBodyExpandMem x.mem ei dst xj out outj, next := x.next })
    (hWj : outj = wordBytes 8 (c1 + k))
    (hsub : lookupName x.env "%sub.ptr.sub" =
      some (.int 64 (BitVec.ofNat 64 (p - base))))
    (hlen : lookupName x.env "%len" = some (.int 64 len))
    (hconv : lookupName x.env "%conv" = some (.int 64 conv))
    (hbit7 : evalICmpNat .ugt 64
      ((BitVec.ofNat 64 (p - base)) + len).toNat conv.toNat = 1#1)
    (hp : lookupName x.env "%p" = some (.ptr p))
    (hdst : lookupName x.env "%dst" = some (.ptr dst))
    (hei : lookupName x.env "%ei" = some (.ptr ei))
    (hxp : lookupName x.env "%xp" = some (.ptr xp))
    (hxj : lookupName x.env "%xj" = some (.ptr xj))
    (hnxp : lookupName x.env "%nxp" = some (.int 64 nxp))
    (houtn : lookupName x.env "%outn" = some (.ptr outn))
    (hbit9 : evalICmp .eq (BitVec.ofNat 64 out.length) 0xffffffffffffffff#64 = 0#1)
    (hlenOut : out.length < 2 ^ 64)
    (hnext : ei = next)
    (hrec : stage2ReadWord mem (ch + 1112) 8 = some e')
    (hmodel : stage2StringBody mem ch p len.toNat dst outn xp xj nxp.toNat =
      some (writeBytes (writeBytes (writeBytes mem dst out) xj
        (wordBytes 8 (c1 + k))) outn (wordBytes 8 out.length), 2,
        wordBytes 8 out.length))
    (hlenOutLen : out.length ≤ len.toNat)
    (hdst_p : readBytes mem dst out.length ≠ none)
    (hxj_p : readBytes mem xj 8 ≠ none)
    (houtn_p : readBytes mem outn 8 ≠ none)
    (hd_ei : ei + 8 ≤ dst ∨ dst + out.length ≤ ei)
    (hx_ei : ei + 8 ≤ xj ∨ xj + 8 ≤ ei)
    (hd_xj : dst + out.length ≤ xj ∨ xj + 8 ≤ dst)
    (ho_ei : ei + 8 ≤ outn ∨ outn + 8 ≤ ei)
    (ho_d : outn + 8 ≤ dst ∨ dst + out.length ≤ outn)
    (ho_x : outn + 8 ≤ xj ∨ xj + 8 ≤ outn) :
    s2StringBodyConcludes
      [.ptr ch, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj,
        .int 64 nxp] mem next 4 x := by
  have hmemEq : writeBytes
        (s2StringBodyExpandMem x.mem ei dst xj out outj) outn
        (natToBytes out.length 8)
      = s2StringBodyDecodedMem mem dst xj outn ei outj out := by
    rw [hmem, hWj]
    exact s2StringBodyMemory_decoded_cursor mem hdst_p hxj_p houtn_p
      hd_ei hx_ei hd_xj ho_ei ho_d ho_x
  refine ⟨⟨.int 32 (BitVec.ofNat 32 2),
      s2StringBodyDecodedMem mem dst xj outn ei outj out, next + 8⟩, ?_, ?_, ?_⟩
  · have hrun := s2StringBodyExit_decoded_named (e := x) (extra :=
      s2StringBodyExpandMem x.mem ei dst xj out outj) (nx := x.next)
      (call := BitVec.ofNat 64 out.length) (outj := outj) (out := out)
      hpc hsub hlen hconv hbit7 hp hdst hei hxp hxj hnxp hexp hbit9 houtn rfl rfl
      hlenOut
    rw [hmemEq] at hrun
    exact hrun
  · refine ⟨writeBytes (writeBytes (writeBytes mem dst out) xj
        (wordBytes 8 (c1 + k))) outn (wordBytes 8 out.length), 2,
      wordBytes 8 out.length, hmodel, rfl, ?_, rfl⟩
    rw [← hnext, hWj]
    rfl
  · simp only [s2StringBodyFoot, hrec]
    have hWjl : outj.length = 8 := by rw [hWj, wordBytes, natToBytes_length]
    have hsl : (wordBytes 8 out.length).length = 8 := natToBytes_length _ _
    refine ((((UnchangedOutside.refl' mem _).write_le (a := dst) (w := out.length)
      ⟨(dst, len.toNat), by simp, le_rfl, by omega⟩ le_rfl).write_le (a := xj)
      (w := outj.length) ⟨(xj, 8), by simp, le_rfl, by omega⟩ le_rfl).write_le
      (a := outn) (w := 8) ⟨(outn, 8), by simp, le_rfl, le_rfl⟩
      (le_of_eq hsl)).write_le (a := ei) (w := 8) ⟨(next, 8), by simp, by omega,
      by omega⟩ (le_of_eq hsl)

-- The closing composes four terminal runs; each arm's *proof* is not re-elaborated
-- here, so the cost is the four applications and the scan's induction.  The
-- ceiling is the arms' own, which is headroom rather than a measurement: the
-- closing lands inside a quarter of it.
set_option maxHeartbeats 12000000 in
/-- **`s2_string_body`'s contract, proved of the emitted body.** -/
theorem s2StringBodyBody_contract {args : List Value} {mem : Mem} {next : Nat}
    (hpre : s2StringBodyPre args mem next) :
    ∃ o : CallOutcome,
      runFuel s2StringBodyCalls (s2StringBodyBudget args) s2StringBodyBody
        (stagedState s2StringBodyBody args mem next) = some (.ret (some o.ret) o.mem) ∧
      s2StringBodyPost args mem next o ∧
      UnchangedOutside mem o.mem (s2StringBodyFoot args mem next) := by
  obtain ⟨c, p, len, dst, outn, xp, xj, nxp, base, j0, ps, body, e, rfl, hbase, hj0,
    hps, hbody, he, hspace, hp64, hble, hpw, hlen1, hj063, hN63, houtnp, hdstp,
    hep,
    hxjn, hxjo, hxjd, hxje, hnou, hnod, hnoe, hode, hoee, hde, hxjp, hxje2, hnpe,
    hne2, hdpe, hdpe2, houpe, houpe2, hepe, hepe2, hdis, hdisnext⟩ := hpre
  generalize hst : stagedState s2StringBodyBody
    [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj, .int 64 nxp]
    mem next = st
  obtain ⟨hpcS, hcS, hpS, hlenS, hdstS, houtnS, hxpS, hxjS, hnxpS, hmemS, hnextS⟩ :=
    s2StringBodyStaged_entry mem next
  have hpcS' : st.pc = "entry" := by simpa only [← hst] using hpcS
  have hcS' : lookupName st.env "%c" = some (.ptr c) := by simpa only [← hst] using hcS
  have hpS' : lookupName st.env "%p" = some (.ptr p) := by simpa only [← hst] using hpS
  have hlenS' : lookupName st.env "%len" = some (.int 64 len) := by
    simpa only [← hst] using hlenS
  have hdstS' : lookupName st.env "%dst" = some (.ptr dst) := by simpa only [← hst] using hdstS
  have houtnS' : lookupName st.env "%outn" = some (.ptr outn) := by
    simpa only [← hst] using houtnS
  have hxpS' : lookupName st.env "%xp" = some (.ptr xp) := by simpa only [← hst] using hxpS
  have hxjS' : lookupName st.env "%xj" = some (.ptr xj) := by simpa only [← hst] using hxjS
  have hnxpS' : lookupName st.env "%nxp" = some (.int 64 nxp) := by
    simpa only [← hst] using hnxpS
  have hmemS' : st.mem = mem := by simpa only [← hst] using hmemS
  have hnextS' : st.next = next := by simpa only [← hst] using hnextS
  have hb64 : base < 2 ^ 64 := stage2ReadWord_lt_64 hbase
  have hj64 : j0 < 2 ^ 64 := by omega
  have hbaseR : readBytes st.mem c 8 = some (wordBytes 8 base) := by
    rw [hmemS']; exact readBytes_of_stage2ReadWord hbase
  have hj0R : readBytes st.mem xj 8 = some (wordBytes 8 j0) := by
    rw [hmemS']; exact readBytes_of_stage2ReadWord hj0
  have hpsR : readLanes32 st.mem xp nxp.toNat = some ps := by rw [hmemS']; exact hps
  have hwordR : stage2ReadWord st.mem xj 8 = some j0 := by rw [hmemS']; exact hj0
  by_cases hj0N : j0 < nxp.toNat
  · have hnxp0 : nxp.toNat ≠ 0 := by omega
    have hbit1 : evalICmp .ult (BitVec.ofNat 64 j0) nxp = 1#1 :=
      s2StringBodyBit_cmp3_one hj063 hN63 hj0N
    have hbit0 : evalICmp .eq nxp (BitVec.ofNat 64 0) = 0#1 := by
      apply evalICmp_eq_zero
      intro hzero
      apply hnxp0
      have := congrArg BitVec.toNat hzero
      simpa using this
    have hseat := s2StringBodyEntry_seat_landRhs (env := st.env) (s := st)
      hpcS' hcS' hpS' hxjS' hnxpS' hxpS' hbaseR hb64 hp64 hj0R hj64 hbit0 hbit1
      hble hwordR hpsR hj0N
    have hstep := hseat.1
    have hinvP : s2StringBodyScanInvP mem xj (p - base) xp nxp.toNat j0 ps st.env
        st.next (nxp.toNat - j0)
        (s2StringBodyHeadState st.env st base p j0 nxp) j0 := by
      rw [← hmemS']
      exact s2StringBodyScanInvP_seat st.env st base p xj xp j0 ps nxp hpcS' hble hp64
        hwordR hpsR hj0N hxpS' hxjS' hnxpS'
    -- the seated invariant carries the scan's *remaining* budget, `nxp.toNat - j0`,
    -- while `s2StringBodyScan_reaches_exitP` states its own hypothesis at the whole
    -- bound; the loop is entered at the remaining budget instead — the same run, and
    -- the arms' arithmetic is unchanged
    obtain ⟨ex, jx, hjle, hexited, hexword, hscan⟩ :=
      (s2StringBodyScanLoopP mem xj (p - base) xp nxp.toNat j0 ps st.env st.next
        hps hdis hN63 (by omega)).run_from (nxp.toNat - j0) _ j0 hinvP
    have hexword' := hexword
    obtain ⟨c1, hmemx, hfix, hshape, heix, hsubx, hxpx, hxjx, hnxpx, hif, hland⟩ := hexword'
    -- `cost` is a structure projection, so the bound the loop hands back mentions it
    -- opaquely and `omega` cannot read it as `2`; stated at the numeral, the three
    -- arms' budget steps close
    have hjle2 : jx ≤ (nxp.toNat - j0 + 1) * 2 := hjle
    have hlenE : lookupName ex.env "%len" = some (.int 64 len) :=
      s2StringBodyScan_lookup_env0 hshape (by decide) hlenS'
    have houtnE : lookupName ex.env "%outn" = some (.ptr outn) :=
      s2StringBodyScan_lookup_env0 hshape (by decide) houtnS'
    have hcE : lookupName ex.env "%c" = some (.ptr c) :=
      s2StringBodyScan_lookup_env0 hshape (by decide) hcS'
    have hpE : lookupName ex.env "%p" = some (.ptr p) :=
      s2StringBodyScan_lookup_env0 hshape (by decide) hpS'
    have hdstE : lookupName ex.env "%dst" = some (.ptr dst) :=
      s2StringBodyScan_lookup_env0 hshape (by decide) hdstS'
    have hlen_ps : ps.length = nxp.toNat := (readLanes32_lane hps).1
    -- the exit word's `%nxp` cell carries `BitVec.ofNat 64 nxp.toNat`; the arms state
    -- it at `nxp`, and this is the one rewrite that reconciles them
    have hnxpWord : BitVec.ofNat 64 nxp.toNat = nxp := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt nxp.isLt]
    have hE : st.next = next := hnextS'
    rcases hexited with hpcx | hpcx
    · obtain ⟨lane, conv, hqlane, hqge, hconvx, hconvq⟩ := hland hpcx
      have hc1lt : c1 < 2 ^ 64 := by
        have hcl : c1 < ps.length := by
          by_contra h
          rw [List.getElem?_eq_none (by omega)] at hqlane
          cases hqlane
        omega
      have hxj_p : readBytes mem xj 8 ≠ none := by
        rw [readBytes_of_stage2ReadWord hj0]; simp
      have houtn_p : readBytes mem outn 8 ≠ none := houtnp
      have hdst_p : readBytes mem dst len.toNat ≠ none := hdstp
      by_cases hpast : p - base + len.toNat ≤ lane
      · obtain ⟨o, hrun, hpost, hfoot⟩ :=
          s2StringBodyArm_scan_landLhsTrue (mem := mem) (next := next) (c1 := c1)
            (lane := lane) (conv := conv) (env0 := ex.env) (ei := st.next) (ch := c) hbase hj0 hps hpcx hmemx hfix hqlane hqge
            hconvx hconvq hsubx hpast (by omega) hpw hlenE houtnE heix hnxp0
        refine ⟨o, ?_, hpost, hfoot⟩
        have hS : runFuel s2StringBodyCalls (2 + (jx + 3)) s2StringBodyBody st =
            some (.ret (some o.ret) o.mem) := by
          rw [hstep (jx + 3), hscan 3]
          exact hrun
        have hle : 2 + (jx + 3) ≤ s2StringBodyBudget
            [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj,
              .int 64 nxp] := by
          simp only [s2StringBodyBudget]; omega
        exact runFuel_mono_le hle hS
      · have hltlane : lane < p - base + len.toNat := by omega
        have hne : ((ps.drop c1).takeWhile
            (fun q => decide (q < p - base + len.toNat))).isEmpty = false :=
          s2StringBodyWindow_cons_of_lane hqlane hltlane
        have hj1 : c1 = j0 + ((ps.drop j0).takeWhile
            (fun q => decide (q < p - base))).length :=
          s2StringBodyScanExit_j1 hfix (Or.inr ⟨lane, hqlane, hqge⟩) hlen_ps
        -- the two `Nat.mod_eq_of_lt`s are separated: written as one `rw` list the
        -- second instantiates on the outer `% 2 ^ 64` and leaves `p - base`
        -- unreduced
        have hsum : ((BitVec.ofNat 64 (p - base)) + len).toNat = p - base + len.toNat := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat]
          rw [show (p - base) % 2 ^ 64 = p - base from Nat.mod_eq_of_lt (by omega)]
          exact Nat.mod_eq_of_lt hpw
        have hbit7 : evalICmpNat .ugt 64 ((BitVec.ofNat 64 (p - base)) + len).toNat
            conv.toNat = 1#1 := by
          rw [hsum, hconvq]
          exact evalICmpNat_ugt_one hpw (by omega) hltlane
        have heip : RegionsApart st.next 8 p len.toNat := by rw [hE]; exact hnpe
        have heixj : st.next + 8 ≤ xj ∨ xj + 8 ≤ st.next := by
          rw [hE]; exact hxjn.symm
        have heilan : ∀ j, j < nxp.toNat →
            xp + 4 * j + 4 ≤ st.next ∨ st.next + 8 ≤ xp + 4 * j := by
          intro j hj
          have := hdisnext j hj
          rw [hE]
          exact this
        cases hdecg : escapeDecodeGo body 0 0
          (((ps.drop c1).takeWhile (fun q => decide (q < p - base + len.toNat))).map
            (fun q => q - (p - base))) [] with
        | decoded out k =>
          -- `hspace` states the spacing at `j0 + takeWhile …`; `hj1` is the
          -- direction that turns it into the statement at `c1`, and applied to the
          -- goal it would have no occurrence to fire on
          have hsp : Spaced body 0
              (((ps.drop c1).takeWhile (fun q => decide (q < p - base + len.toNat))).map
                (fun q => q - (p - base))) := by
            have h := hspace base j0 ps body hbase hj0 hps hbody
            rw [show j0 + ((ps.drop j0).takeWhile (fun q => decide (q < p - base))).length
              = c1 from hj1.symm] at h
            exact h
          have hblen : body.length = len.toNat := readBytes_length_some hbody
          have hlenOutLen : out.length ≤ len.toNat := by
            have h := escapeDecodeGo_length_le body hsp 0 [] out k hdecg
            simp only [List.length_nil, Nat.sub_zero] at h
            omega
          -- `hbit9`'s bound comes from the decoded length's own bound: `len` is a
          -- bit vector and `out` a list, so `hlenOut` is derived, not read off
          have hlen64 : len.toNat < 2 ^ 64 := len.isLt
          have hlenOut : out.length < 2 ^ 64 := by omega
          have hlenCap : out.length < 2 ^ 64 - 1 := by omega
          have hbit9 : evalICmp .eq (BitVec.ofNat 64 out.length)
              0xffffffffffffffff#64 = 0#1 :=
            (evalICmp_eq_zero_iff _ _).2 (by
              intro hcon
              have h2 : (BitVec.ofNat 64 out.length).toNat
                  = (0xffffffffffffffff#64).toNat := by rw [hcon]
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlenOut] at h2
              have h3 : (0xffffffffffffffff#64).toNat = 2 ^ 64 - 1 := by decide
              have h4 : out.length = 2 ^ 64 - 1 := by rw [h2, h3]
              omega)
          have hmodel : stage2StringBody mem c p len.toNat dst outn xp xj nxp.toNat =
              some (writeBytes (writeBytes (writeBytes mem dst out) xj
                (wordBytes 8 (c1 + k))) outn (wordBytes 8 out.length), 2,
                wordBytes 8 out.length) :=
            s2StringBodyModel_decoded (k := k) hbase hj0 hps hbody hnxp0 hj1 hne hdecg
          have hexp := s2StringBodyExpand_decoded_named (xmem := ex.mem)
            (Woff := wordBytes 8 out.length) (Wj := wordBytes 8 (c1 + k))
            (ei := st.next) (next := ex.next) (dst := dst)
            hmemx hps hbody hqlane hqge (by omega) hc1lt rfl rfl hxjp heip heixj heilan
            hdis hdecg
          -- `readBytes … ≠ none` is not an inductive type, so this splits the staged
          -- read at `out.length` instead of introducing a witness
          have hdst_some : readBytes mem dst out.length ≠ none := by
            intro hnone
            obtain ⟨bsd, hbsd⟩ := exists_readBytes_of_ne hdstp
            have h24 : readBytes mem dst (out.length + (len.toNat - out.length)) = some bsd := by
              rw [show out.length + (len.toNat - out.length) = len.toNat from by omega]
              exact hbsd
            rw [(readBytes_split mem dst out.length (len.toNat - out.length) h24).1] at hnone
            cases hnone
          obtain ⟨o, hrun, hpost, hfoot⟩ :=
            -- every implicit is named: left to inference, one becomes a metavariable
            -- inside the arm's own hypothesis goals, which `omega` and the interval
            -- proofs cannot read
            s2StringBodyArm_scan_decoded (mem := mem) (x := ex) (ch := c) (dst := dst)
              (outn := outn) (xp := xp) (xj := xj) (len := len)
              (base := base) (c1 := c1) (ei := st.next) (next := next) (lane := lane)
              (k := k) (e' := e) (ps := ps) (body := body) (out := out)
              (conv := conv) (outj := wordBytes 8 (c1 + k))
              (hpc := hpcx) (hmem := hmemx) (hexp := hexp) (hWj := rfl) (hsub := hsubx)
              (hlen := hlenE) (hconv := hconvx) (hbit7 := hbit7) (hp := hpE)
              (hdst := hdstE) (hei := heix) (hxp := hxpx) (hxj := hxjx)
              (hnxp := by rw [← hnxpWord]; exact hnxpx) (houtn := houtnE) (hbit9 := hbit9)
              (hlenOut := hlenOut) (hnext := hE) (hrec := he) (hmodel := hmodel)
              (hlenOutLen := hlenOutLen) (hdst_p := hdst_some)
              (hxj_p := hxj_p) (houtn_p := houtn_p)
              (hd_ei := by
                rw [hE]
                rcases hnod with h | h
                · exact Or.inl h
                · exact Or.inr (by omega))
              (hx_ei := heixj) (hd_xj := by
                rcases hxjd with h | h
                · exact Or.inr h
                · exact Or.inl (by omega))
              (ho_ei := by
                rw [hE]; exact hnou)
              (ho_d := by
                rcases hode with h | h
                · exact Or.inl h
                · exact Or.inr (by omega))
              (ho_x := hxjo.symm)
          refine ⟨o, ?_, hpost, hfoot⟩
          have hS : runFuel s2StringBodyCalls (2 + (jx + 4)) s2StringBodyBody st =
              some (.ret (some o.ret) o.mem) := by
            rw [hstep (jx + 4), hscan 4]
            exact hrun
          have hle : 2 + (jx + 4) ≤ s2StringBodyBudget
              [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj,
                .int 64 nxp] := by
            simp only [s2StringBodyBudget]; omega
          exact runFuel_mono_le hle hS
        | refused offN k =>
          have h24 : stage2ErrorExtent = 24 := rfl
          rw [h24] at hnoe hxje
          have hblen : body.length = len.toNat := readBytes_length_some hbody
          -- the offset is below the body's length, which is the document's extent
          have hoffL : offN < len.toNat :=
            (escapeDecodeGo_refused_lt body _ _ _ _ offN k hdecg).trans_le (le_of_eq hblen)
          have hoffN : offN < 2 ^ 64 := by omega
          have hsumW : offN + (p - base) < 2 ^ 64 :=
            calc offN + (p - base) < len.toNat + (p - base) := Nat.add_lt_add_right hoffL _
              _ = p - base + len.toNat := Nat.add_comm _ _
              _ < 2 ^ 64 := hpw
          have hC0 : s2StringBodyRefusedC0 mem xj c1 = writeBytes mem xj (wordBytes 8 c1) :=
            rfl
          have hexpR := s2StringBodyExpand_refused_named (xmem :=
              s2StringBodyRefusedC0 mem xj c1)
            (Woff := wordBytes 8 offN) (Wj := wordBytes 8 (c1 + k))
            (next := ex.next) (dst := dst) hC0 hps hbody hqlane hqge (by omega) hc1lt
            rfl rfl hxjp heip heixj heilan hdis hdecg
          have hmodel : stage2StringBody mem c p len.toNat dst outn xp xj nxp.toNat =
              some (writeBytes (stage2ErrSetMsg mem e (p - base + offN) 0) xj
                (wordBytes 8 (c1 + k)), 0, wordBytes 8 offN) :=
            s2StringBodyModel_refused (k := k) (off := offN) (e' := e)
              hbase hj0 hps hbody he hnxp0 hj1 hne hdecg
          obtain ⟨bs, hbs⟩ := exists_readBytes_of_ne hep
          obtain ⟨o, hrun, hpost, hfoot⟩ :=
            s2StringBodyArm_scan_refused (mem := mem) (x := ex) (ch := c) (dst := dst)
              (outn := outn) (xp := xp) (xj := xj) (len := len) (base := base)
              (j0 := j0) (c1 := c1) (ei := st.next) (next := next) (lane := lane)
              (offN := offN) (k := k) (e' := e) (ps := ps) (body := body)
              (conv := conv) (Woff := wordBytes 8 offN) (Wj := wordBytes 8 (c1 + k))
              (bs := bs)
              (hpc := hpcx) (hmem := hmemx) (hC0 := hC0) (hexpMem := rfl)
              (hWoff := rfl) (hWj := rfl) (hlane := hqlane) (hge := hqge)
              (hlt := hltlane) (hconv := hconvx) (hconvq := hconvq) (hc := hcE)
              (hsub := hsubx) (hlen := hlenE) (hp := hpE) (hdst := hdstE) (hei := heix)
              (hxp := hxpx) (hxj := hxjx) (hnxp := by rw [← hnxpWord]; exact hnxpx)
              (hps := hps) (hbody := hbody)
              (hrec := he) (hj0 := hj0) (hp0 := by omega) (hpw := hpw) (hc1 := hc1lt)
              (hoffN := hoffN) (hxjp := hxjp) (heip := heip) (heixj := heixj)
              (heilan := heilan) (hjlan := hdis) (hc1k := rfl)
              (hxje := hxje2) (heie := by rw [hE]; exact hne2)
              (hoff := by
                rw [readBytes_writeBytes_apart (ws := wordBytes 8 (c1 + k)) (by
                  rw [show (wordBytes 8 (c1 + k)).length = 8 from natToBytes_length _ _]
                  rw [hE]
                  exact hxjn)]
                exact readBytes_wordBytes_same)
              (hr := hdecg) (hnext := hE)
              (hrec_bs := hbs) (hsumW := hsumW)
              (hmodel := hmodel)
              (hm1 := by
                rw [show (wordBytes 8 offN).length = 8 from by rw [wordBytes, natToBytes_length],
                  show (wordBytes 8 (c1 + k)).length = 8 from by rw [wordBytes, natToBytes_length],
                  hE]
                rcases hxjn with h | h
                · exact Or.inr h
                · exact Or.inl h)
              (hm2 := by
                rw [hE,
                  show (wordBytes 8 offN).length = 8 from by rw [wordBytes, natToBytes_length],
                  show (natToBytes (0#32).toNat 4).length = 4 from natToBytes_length _ _]
                rcases hnoe with h | h
                · exact Or.inl h
                · exact Or.inr (by omega))
              (hm3 := by
                rw [hE,
                  show (wordBytes 8 offN).length = 8 from by rw [wordBytes, natToBytes_length],
                  show (8#64).toNat = 8 from by decide,
                  show (natToBytes ((BitVec.ofNat 64 offN) + (BitVec.ofNat 64 (p - base))).toNat 8).length = 8
                    from natToBytes_length _ _]
                rcases hnoe with h | h
                · exact Or.inl (by omega)
                · exact Or.inr (by omega))
              (hm4 := by
                rw [hE,
                  show (wordBytes 8 offN).length = 8 from by rw [wordBytes, natToBytes_length],
                  show (16#64).toNat = 16 from by decide,
                  show (natToBytes (0#64).toNat 8).length = 8 from natToBytes_length _ _]
                rcases hnoe with h | h
                · exact Or.inl (by omega)
                · exact Or.inr (by omega))
              (hm5 := by
                rw [show (wordBytes 8 (c1 + k)).length = 8 from by rw [wordBytes, natToBytes_length],
                  show (natToBytes (0#32).toNat 4).length = 4 from natToBytes_length _ _]
                rcases hxje with h | h
                · exact Or.inl h
                · exact Or.inr (by omega))
              (hm6 := by
                rw [show (wordBytes 8 (c1 + k)).length = 8 from by rw [wordBytes, natToBytes_length],
                  show (8#64).toNat = 8 from by decide,
                  show (natToBytes ((BitVec.ofNat 64 offN) + (BitVec.ofNat 64 (p - base))).toNat 8).length = 8
                    from natToBytes_length _ _]
                rcases hxje with h | h
                · exact Or.inl (by omega)
                · exact Or.inr (by omega))
              (hm7 := by
                rw [show (wordBytes 8 (c1 + k)).length = 8 from by rw [wordBytes, natToBytes_length],
                  show (16#64).toNat = 16 from by decide,
                  show (natToBytes (0#64).toNat 8).length = 8 from natToBytes_length _ _]
                rcases hxje with h | h
                · exact Or.inl (by omega)
                · exact Or.inr (by omega))
              (hm8 := by
                rw [show (natToBytes (0#32).toNat 4).length = 4 from natToBytes_length _ _,
                  show (8#64).toNat = 8 from by decide,
                  show (natToBytes ((BitVec.ofNat 64 offN) + (BitVec.ofNat 64 (p - base))).toNat 8).length = 8
                    from natToBytes_length _ _]
                exact Or.inl (by omega))
              (hm9 := by
                rw [show (natToBytes (0#32).toNat 4).length = 4 from natToBytes_length _ _,
                  show (16#64).toNat = 16 from by decide,
                  show (natToBytes (0#64).toNat 8).length = 8 from natToBytes_length _ _]
                exact Or.inl (by omega))
              (hm10 := by
                rw [show (8#64).toNat = 8 from by decide,
                  show (natToBytes ((BitVec.ofNat 64 offN) + (BitVec.ofNat 64 (p - base))).toNat 8).length = 8
                    from natToBytes_length _ _,
                  show (16#64).toNat = 16 from by decide,
                  show (natToBytes (0#64).toNat 8).length = 8 from natToBytes_length _ _]
                exact Or.inl (by omega))
          refine ⟨o, ?_, hpost, hfoot⟩
          have hS : runFuel s2StringBodyCalls (2 + (jx + 4)) s2StringBodyBody st =
              some (.ret (some o.ret) o.mem) := by
            rw [hstep (jx + 4), hscan 4]
            exact hrun
          have hle : 2 + (jx + 4) ≤ s2StringBodyBudget
              [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj,
                .int 64 nxp] := by
            simp only [s2StringBodyBudget]; omega
          exact runFuel_mono_le hle hS
    · obtain ⟨o, hrun, hpost, hfoot⟩ :=
        s2StringBodyArm_scan_ifThen (mem := mem) (next := next) hbase hj0 hps hpcx
          hexword hlenE houtnE heix hnxp0
      refine ⟨o, ?_, hpost, hfoot⟩
      have hS : runFuel s2StringBodyCalls (2 + (jx + 2)) s2StringBodyBody st =
          some (.ret (some o.ret) o.mem) := by
        rw [hstep (jx + 2), hscan 2]
        exact hrun
      have hle : 2 + (jx + 2) ≤ s2StringBodyBudget
          [.ptr c, .ptr p, .int 64 len, .ptr dst, .ptr outn, .ptr xp, .ptr xj,
            .int 64 nxp] := by
        simp only [s2StringBodyBudget]; omega
      exact runFuel_mono_le hle hS
  · by_cases hnxp0 : nxp.toNat = 0
    · -- the list-free arm: `nxp = 0` scans the body's own span
      have hc0 := s2StringBodyArm_noList (mem := mem) (next := next) (c := c) (p := p)
        (dst := dst) (outn := outn) (xp := xp) (xj := xj) (len := len) (nxp := nxp)
        (base := base) (body := body) (e := e)
        (hbase := hbase) (hbody := hbody) (he := he) (hp64 := hp64) (hble := hble)
        (hpw := hpw) (hlen1 := hlen1) (hnxp0 := hnxp0) (houtnp := houtnp)
        (hdstp := hdstp) (hep := hep) (hnod := hnod) (hnou := hnou) (hnoe := hnoe)
        (hnpe := hnpe) (hdpe := hdpe) (hode := hode) (hne2 := hne2)
      rw [← hst]
      obtain ⟨o, hrun, hpost, hfoot⟩ := hc0
      exact ⟨o, runFuel_mono_le (by simp only [s2StringBodyBudget]; omega) hrun, hpost, hfoot⟩
    · obtain ⟨o, hrun, hpost, hfoot⟩ :=
        s2StringBodyArm_entry_ifThen (mem := mem) (next := next) (body := body)
          hbase hj0 hps he hp64
          hble hj063 hN63 (by omega) (by omega)
      refine ⟨o, ?_, hpost, hfoot⟩
      rw [← hst]
      refine runFuel_mono_le ?_ hrun
      simp only [s2StringBodyBudget]
      omega

/-! ### Axiom footprints

The runs, the loop's shape and the contract print their footprints with
`#guard_msgs`, so the build checks them rather than printing them.
`Classical.choice` appears exactly where a `getelementptr`'s sign-extension enters
(`s2StringBody_landRhs_denote`, and the loop that composes it), which is the `gep`
step's core lemma and not a choice any proof here makes; the blocks with no
`getelementptr` carry the frame lemmas' `[propext, Quot.sound]`.  The closing
carries it for the same reason: it composes the loop. -/
/-- info: 'LeanLLVM.Refinement.sb_step_lifetime' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sb_step_lifetime

/-- info: 'LeanLLVM.Refinement.s2StringBody_ifEnd_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms s2StringBody_ifEnd_denote

/-- info: 'LeanLLVM.Refinement.s2StringBody_landRhs_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms s2StringBody_landRhs_denote

/-- info: 'LeanLLVM.Refinement.s2StringBodyScanAtBound_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms s2StringBodyScanAtBound_eq

/-- info: 'LeanLLVM.Refinement.s2StringBodyScanBoundLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms s2StringBodyScanBoundLoop

/-- info: 'LeanLLVM.Refinement.s2StringBodyScan_run_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms s2StringBodyScan_run_at

/-- info: 'LeanLLVM.Refinement.s2StringBodyBody_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms s2StringBodyBody_contract


end LeanLLVM.Refinement
