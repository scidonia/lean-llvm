/-
# `[1]`'s caller result, from the staged entry and the seam's window

`evb_caller_result` (`JsonEventCallerResult`) takes the five counted segments, the
carry equations, the numeral's record and the merge's readings from its caller.
`JsonEventCallerResultStaged` produces the staged words (the cursor record's base
and error pointer, the root slot) and the seam's token words; this module composes
the run from them.

The seam's five-byte window is *derived*, not taken: `evbSeam_window` reads it at
the seam's own memory from the document and its staged read-past tail across the
walk's frame and the four token-record stores.  With that row the seam's staged
words are complete (`HcontSeamStage`), the three calls follow
(`hcontSeamCallsAt`), the tail is `consumerTailSegEmptyAt` at the numeral's own
record (`s2ScalarValue_numberAppend` fixes the bytes the scalar call appends), and
the number's revolution closes through `walkRevolutionMergeSegScalar`.

What a caller supplies is the entry's staging and the document: the layout
(`routePre`), the staged event cursor, the seed's invariant with the entry block's
memory, and `[1]`'s bytes and entry stream.  The refusal record's address width is
the staging's own clause (`WalkStage.eLt`), so the cursor record's error word
decodes from `natToBytes8_readWord` without a bound beside it.  No segment, carry
equation, token word, window or numeral record is assumed.

The five segments are counted `9 + 2 + 16 + 2 + 11`: the opener's nine links, the
header's two, the numeral's revolution at its high leaf (`8 + 4 + 3 + 1`), the
second header's two and the closer's eleven.

There is no `sorry`, `admit` or `native_decide`.
-/
import LeanLLVM.Refinement.JsonEventCallerResultWindow
import LeanLLVM.Refinement.JsonEventCallerResultSeamH1

set_option autoImplicit false

namespace LeanLLVM.Refinement
namespace WalkScope

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.BlockEval

/-! ### The entry's two counts -/

/-- `[1]`'s document is three bytes. -/
theorem evb_n3 {m0 : Mem} {G : WalkGeom m0} (hbs : G.bs = evbDoc) : G.n = 3 := by
  have h := walkReadBytes_length G.doc
  rw [hbs] at h
  simp [evbDoc] at h
  omega

/-- `[1]`'s entry stream has three entries. -/
theorem evb_nep3 {m0 : Mem} {G : WalkGeom m0} (hent : G.ent = [0, 1, 2]) : G.nep = 3 := by
  have h := readLanes32_length m0 G.ep G.nep G.ent G.entries
  rw [hent] at h
  exact h.symm

/-! ### The staged words at the opener's merge -/

/-- **The root slot's word at the opener's merge** is the entry's staged zero: the
opener's four tail stores write inside the staged objects and the event stream, all
below the watermark. -/
theorem evbOpenRoot {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G} {s₀ : State}
    (hnev0 : G.nev0 = 0) {r : CallOutcome} {rd : BitVec 32} {b : BitVec 8}
    (hrmem : r.mem = s₀.mem)
    (hroot : readBytes s₀.mem (G.next0 + 8) 4 = some (natToBytes 0 4)) :
    readBytes (openS₉ (openHeadC (walkSeed G S)) (openBrS₄ s₀) r rd b).mem
      (G.next0 + 8) 4 = some (natToBytes 0 4) := by
  rw [evbOpenMem (S := S) hrmem hnev0]
  rw [walkReadBytes_writeBytes_outside (start := S.z + 8) (v := wordBytes 8 (0 + 1)) (by
        rw [wordBytes, natToBytes_length]
        have h := S.sevenEnd (S.z, stage2LogExtent) (by simp [stage2StagedWrites])
        simp only [stage2LogExtent] at h
        omega),
      walkReadBytes_writeBytes_outside (start := G.ev + 0)
        (v := natToBytes (ifEnd24St b).toNat 1) (by
          rw [natToBytes_length]
          have h := G.watermark (G.ev, G.evcap) (by simp [stage2Regions])
          omega),
      walkReadBytes_writeBytes_outside (start := S.cst + 0) (v := natToBytes 0 1) (by
          rw [natToBytes_length]
          have h := S.sevenEnd (S.cst, stage2StackExtent) (by simp [stage2StagedWrites])
          simp only [stage2StackExtent] at h
          omega),
      walkReadBytes_writeBytes_outside (start := S.ctype + 0)
        (v := natToBytes (ifEnd24Ty b).toNat 1) (by
          rw [natToBytes_length]
          have h := S.sevenEnd (S.ctype, stage2StackExtent) (by simp [stage2StagedWrites])
          simp only [stage2StackExtent] at h
          omega)]
  exact hroot

/-! ### The composition -/

/-- **`[1]`'s accepting return and the caller-visible reads, from the staged
entry.**  The opener and the first header pass run at the seed; the numeral's
revolution, its seam and the record it appends are produced from the staged words
(the seam's window included, `evbSeam_window`); the second header pass and the
closing bracket's merge follow; and `evb_caller_result` reads the result off the
composed run. -/
theorem evb_caller_result_staged {m0 : Mem} {G : WalkGeom m0} {S : WalkStage G}
    {s₀ : State}
    -- (1) the caller's staging and the call's layout
    (hpre : routePre evbLayout evbDoc)
    (hstageWord : readBytes m0 G.ndst 8 = readBytes evbMem evbLayout.ndst 8)
    (hndstG : G.ndst = evbLayout.ndst)
    (hnevG : G.nev = evbLayout.nev)
    (hdstG : G.dst = evbLayout.dst)
    (hevG : G.ev = evbLayout.ev)
    (hnev0 : G.nev0 = 0)
    -- (2) the staged entry: the seed's invariant and the entry block's memory
    (hInv₀ : WalkInv G (walkSeed G S) s₀) (hmem : s₀.mem = walkEntryMem G S)
    -- (3) the document and its entry stream
    (hbs : G.bs = evbDoc) (hent : G.ent = [0, 1, 2]) :
    ∃ (q : Nat) (m : Mem) (nev' : Nat),
      q + 2 ≤ 27 ∧
      runFuel (stage2Calls stage2SubCalls) (9 + 2 + 16 + 2 + 11 + (q + 2)) stage2Body s₀ =
        some (.ret (some (.int 64 1)) m) ∧
      JsonWalkReads G
        (closeCEnd (closeC₁₀b (headPassC (scMergeC (headPassC
            (openC₉ (openHeadC (walkSeed G S)) (BitVec.ofNat 8 0x5B)) 1 1)
            (EventRecord.number evbBits)) 2 1))
          (BitVec.ofNat 32 1 + BitVec.ofNat 32 4294967295) (BitVec.ofNat 8 4)) m ∧
      readBytes m evbLayout.ndst 8 = some (wordBytes 8 0) ∧
      readBytes m evbLayout.nev 8 = some (wordBytes 8 nev') ∧
      nev' = evbEvents.length ∧
      readBytes m evbLayout.dst 0 = some ([] : List UInt8) ∧
      readBytes m evbLayout.ev nev' = some evbEvents ∧
      (eventsOfBytesIndexed (ByteString.literal evbDoc)
          (ByteString.literal evbEvents) (ByteString.literal ([] : List UInt8))).bind
        valueOfEvents = scalarCanonValueOfBytes evbDoc ∧
      Nonempty EvbCertificate := by
  have hn3 : G.n = 3 := evb_n3 hbs
  have hnep3 : G.nep = 3 := evb_nep3 hent
  have hnep_lt : G.nep < 2 ^ 64 := by
    have h := G.nep_le
    have h2 := G.maxDoc
    simp only [stage2MaxDocument] at h2
    omega
  -- the opener, from the seed and the staged root word
  have hroot₀ : readBytes s₀.mem (G.next0 + 8) 4 =
      some (natToBytes (0 : BitVec 32).toNat 4) := evbStagedRoot hmem
  obtain ⟨r, rd, hrmem, -, hsegO⟩ := evbOpenExact hInv₀ hbs hent hroot₀
  let b : BitVec 8 := BitVec.ofNat 8 0x5B
  let C₁ : WalkCarry G := openC₉ (openHeadC (walkSeed G S)) b
  let s₁ : State := openS₉ (openHeadC (walkSeed G S)) (openBrS₄ s₀) r rd b
  have hInv₁ : WalkInv G C₁ s₁ := hsegO.inv'
  have hb3 : (ifEnd24St b).toNat = 3 := evb_tag_bracket
  -- the cursor record's words at the opener's merge
  have hbase₁ : readBytes s₁.mem S.c 8 = some (natToBytes G.b 8) :=
    evbOpenBase (G := G) (S := S) (s₀ := s₀) hInv₀ hnev0 hn3 (r := r) (rd := rd) (b := b)
      hrmem (evbStagedBase hmem)
  have herr₁ : readBytes s₁.mem (S.c + 1112) 8 = some (natToBytes S.e 8) :=
    evbOpenErr (G := G) (S := S) (s₀ := s₀) hInv₀ hnev0 hn3 (r := r) (rd := rd) (b := b)
      hrmem (evbStagedErr hmem)
  have hroot₁ : readBytes s₁.mem (G.next0 + 8) 4 =
      some (natToBytes (0 : BitVec 32).toNat 4) :=
    evbOpenRoot (S := S) (s₀ := s₀) hnev0 (r := r) (rd := rd) (b := b) hrmem hroot₀
  -- the first header pass
  let H₁ : WalkCarry G := headPassC C₁ 1 1
  have hblock₁ : C₁.block = "cleanup478.i" := rfl
  have hpreO : s₁.pre = some "out_reserve.exit.i.i" := openS₉_pre _ _ _ _ _
  have hspO : phiIncoming "out_reserve.exit.i.i" cleanupSpIncoming =
      some (.reg "%inc33.i") := by decide
  have hspvO : evalOperand s₁ (.reg "%inc33.i") =
      some (.int 32 (BitVec.ofNat 32 (C₁.sp + 1))) := by
    simp only [evalOperand]
    rw [openS₉_inc33]
  have hkO : phiIncoming "out_reserve.exit.i.i" cleanupKIncoming = some (.reg "%inc.i") :=
    by decide
  have hkvO : evalOperand s₁ (.reg "%inc.i") =
      some (.int 64 (BitVec.ofNat 64 (C₁.k + 1))) := by
    simp only [evalOperand]
    rw [openS₉_incAt]
    rw [openBrS₄_other _ _ (by decide) (by decide) (by decide) (by decide)]
    rw [evbSeed_inc hInv₀]
  have hnepvO : lookupName s₁.env "%nep" = some (.int 64 (BitVec.ofNat 64 G.nep)) := by
    rw [openS₉_nepAt]
    rw [openBrS₄_other _ _ (by decide) (by decide) (by decide) (by decide)]
    exact evbSeed_nep hInv₀
  have hguardO : C₁.k + 1 < (BitVec.ofNat 64 G.nep).toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnep_lt]
    show 0 + 1 < G.nep
    omega
  have hcapO : C₁.k + 1 < G.nep := by
    show 0 + 1 < G.nep
    omega
  have hadvO : C₁.k < C₁.k + 1 := by omega
  have hspcapO : C₁.sp + 1 ≤ stage2StackExtent := by
    show 0 + 1 ≤ stage2StackExtent
    decide
  have hspwO : C₁.sp + 1 ≤ C₁.wlen := by
    show 0 + 1 ≤ max (walkSeed G S).wlen ((walkSeed G S).sp + 1)
    rw [evbSeed_wlen, evbSeed_sp]
    decide
  obtain ⟨sh₁, hsegH₁, hInvH₁, hmemH₁⟩ :=
    evbHeadPassAt (G := G) (C := C₁) (s := s₁) hInv₁ hblock₁
      (prev := "out_reserve.exit.i.i") (spv := C₁.sp + 1) (k2 := C₁.k + 1)
      (spOp := .reg "%inc33.i") (kOp := .reg "%inc.i")
      (nepv := BitVec.ofNat 64 G.nep)
      hpreO hspO hspvO hkO hkvO hnepvO hguardO hcapO hadvO hspcapO hspwO
      (hent := hent) hnep3 (Or.inl rfl)
  -- the first head's cells
  have hkH₁ : H₁.k = 1 := rfl
  have hspH₁ : H₁.sp = 1 := rfl
  have hblockH₁ : H₁.block = walkLoopHead := rfl
  have hbaseH : readBytes sh₁.mem H₁.stage.c 8 = some (natToBytes G.b 8) := by
    rw [hmemH₁, evbCursorHeader (S := C₁.stage) (k := C₁.k + 1 + 1)
      (addr := H₁.stage.c) (Or.inl rfl)]
    exact hbase₁
  have herrH : readBytes sh₁.mem (H₁.stage.c + 1112) 8 = some (natToBytes S.e 8) := by
    rw [hmemH₁, evbCursorHeader (S := C₁.stage) (k := C₁.k + 1 + 1)
      (addr := H₁.stage.c + 1112) (Or.inr rfl)]
    exact herr₁
  have hrootH : readBytes sh₁.mem (G.next0 + 8) 4 =
      some (natToBytes (0 : BitVec 32).toNat 4) := by
    rw [hmemH₁]
    rw [walkReadBytes_writeBytes_outside (start := C₁.stage.c + 32)
      (v := wordBytes 8 (C₁.k + 1 + 1)) (Or.inr (by
        have h := C₁.stage.sevenEnd (C₁.stage.c, stage2CursorExtent)
          (by simp [stage2StagedWrites])
        simp only [stage2CursorExtent, wordBytes, natToBytes_length] at h ⊢
        omega))]
    exact hroot₁
  -- the document row at the head
  have hklt₁ : H₁.k + 1 < G.nep := by
    rw [hkH₁]; omega
  have hx : (BitVec.ofNat 8 0x31) = hlastByte G H₁ := by
    show BitVec.ofNat 8 0x31 = BitVec.ofNat 8 (entryByte G H₁.k).toNat
    rw [hkH₁, evbByte_one hbs hent]
    rfl
  let hb35 : HcontByteRoute (cont35 (contB35 G (BitVec.ofNat 32 2))) :=
    HcontByteRoute.highLeaf (by rw [evbContB35 hbs]; decide)
      (by rw [evbContB35 hbs]; decide) (by rw [evbContB35 hbs]; decide)
  let hdoc : HcontScalarPrefix G H₁ sh₁ :=
    hcontScalarPrefix_of_inv (G := G) (C := H₁) (s := sh₁) hInvH₁ hklt₁
      (x := BitVec.ofNat 8 0x31) hx (by decide) (by decide) (by decide) (by decide)
      (v := BitVec.ofNat 32 2)
      (by
        show readBytes sh₁.mem (G.ep + (BitVec.ofNat 64 (H₁.k + 1)).toNat * 4) 4 =
          some (natToBytes (BitVec.ofNat 32 2).toNat 4)
        rw [show (BitVec.ofNat 64 (H₁.k + 1)).toNat = 2 from by
          rw [hkH₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]]
        show readBytes sh₁.mem (G.ep + 2 * 4) 4 = some (natToBytes 2 4)
        have h := evbLaneRead (G := G) (C := H₁) (s := sh₁) hInvH₁ (j := 2)
          (Or.inr rfl) hent hnep3
        rw [evbPos_two hent] at h
        simpa only [show 2 * 4 = 4 * 2 from by decide] using h)
      (by
        show (BitVec.ofNat 32 2).toNat ≤ entryPos G (H₁.k + 1)
        rw [show (BitVec.ofNat 32 2).toNat = 2 from by decide, hkH₁, evbPos_two hent])
      (by
        show evalICmp .ugt (BitVec.ofNat 64 (BitVec.ofNat 32 2).toNat)
          (BitVec.ofNat 64 (entryPos G H₁.k)) = 1
        rw [show (BitVec.ofNat 32 2).toNat = 2 from by decide, hkH₁, evbPos_one hent]
        decide)
      hb35
  -- the seam's invariant and the seam's own cells
  let Cs : WalkCarry G := HeadC₄₁₃ (ContAC₇ H₁)
  let seam : State :=
    scSeamByte (sLand H₁ sh₁ hdoc.x hdoc.inc hdoc.nep hdoc.ep hdoc.v hdoc.ix hdoc.b35)
      hdoc.v.toNat hdoc.x H₁.stage.tok hdoc.b35 hdoc.hb
  have hInvS : WalkInv G Cs seam := scSeamInv_of_cells hInvH₁ hblockH₁ hdoc
  have hspCs : Cs.sp = 1 := rfl
  have hwlenCs : Cs.wlen = 1 := rfl
  have hcell := evb_H₁_pushCells (G := G) (S := S)
  have htyH₁ : H₁.tyMap (H₁.sp - 1) = (2 : UInt8) := by
    rw [show H₁.sp = 1 from hcell.1]
    exact hcell.2.1
  have hstH₁ : H₁.stMap (H₁.sp - 1) = (0 : UInt8) := by
    rw [show H₁.sp = 1 from hcell.1]
    exact hcell.2.2
  have hval : stage2ValuePos seam.mem Cs.sp (0 : BitVec 32).toNat Cs.stage.ctype
      Cs.stage.cst = some 1 := by
    have h := walkValuePos_answer (G := G) (C := Cs) (s := seam) hInvS
      (sp := Cs.sp) (rd := (0 : BitVec 32).toNat) (by rw [hspCs]; decide)
      (by rw [hspCs, hwlenCs])
    rw [h]
    have hty : Cs.tyMap (Cs.sp - 1) = (2 : UInt8) := htyH₁
    have hst : Cs.stMap (Cs.sp - 1) = (0 : UInt8) := hstH₁
    rw [hty, hst]
    decide
  -- the root slot's word at the seam
  have hrootS : readBytes seam.mem (G.next0 + 8) 4 =
      some (natToBytes (0 : BitVec 32).toNat 4) := by
    have h := scSeamByte_rootRead (G := G) (C := H₁)
      (q4 := sLand H₁ sh₁ hdoc.x hdoc.inc hdoc.nep hdoc.ep hdoc.v hdoc.ix hdoc.b35)
      hdoc.v.toNat hdoc.x hdoc.b35 hdoc.hb (cA := BitVec.ofNat 32 7)
      (rdv := (0 : BitVec 32))
      (sLand_rootRead (G := G) (C := H₁) (s := sh₁) hdoc.x hdoc.inc hdoc.nep hdoc.ep
        hdoc.v hdoc.ix hdoc.b35 hrootH)
    rwa [walkReadBytes_rootSlot_of_tokStore (C := H₁) (off := 16) (len := 4)
      (v := natToBytes (BitVec.ofNat 32 7).toNat 4) (by decide) (natToBytes_length _ _)]
      at h
  -- the seam's calls' memory is `evbSeamCallsMem`
  have hmemSeam : evbSeamCallsMem H₁ sh₁ hdoc.x hdoc.inc hdoc.nep hdoc.ep hdoc.v
      hdoc.ix hdoc.b35 hdoc.hb (BitVec.ofNat 32 7) = seamKindStore Cs seam
        (BitVec.ofNat 32 7) :=
    evbSeamCallsMem_seam (C := H₁) (s := sh₁) hdoc.x hdoc.inc hdoc.nep hdoc.ep hdoc.v
      hdoc.ix hdoc.b35 hdoc.hb (BitVec.ofNat 32 7)
  -- the window, derived
  obtain ⟨win, hwin, hlex⟩ :=
    evbSeam_window (G := G) (C := H₁) (s := sh₁) hInvH₁ hbs hn3
      hdoc.x hdoc.inc hdoc.nep hdoc.ep hdoc.v hdoc.ix hdoc.b35 hdoc.hb
      (BitVec.ofNat 32 7)
  have hwinK : readBytes (seamKindStore Cs seam (BitVec.ofNat 32 7)) (G.b + 1)
      (max (2 - 1) 5) = some win := by
    rw [← hmemSeam]
    rw [show max (2 - 1) 5 = 5 from by decide]
    exact hwin
  -- the scalar call's staged words
  have hbaseK : stage2ReadWord (seamKindStore Cs seam (BitVec.ofNat 32 7))
      Cs.stage.c 8 = some G.b := by
    have hread : readBytes (seamKindStore Cs seam (BitVec.ofNat 32 7)) Cs.stage.c 8 =
        some (wordBytes 8 G.b) := by
      rw [← hmemSeam]
      exact evbSeamBase (G := G) (H₁ := H₁) (sh := sh₁) hbaseH
    rw [stage2ReadWord, hread]
    show some (bytesToNat (wordBytes 8 G.b)) = some G.b
    rw [bytesToNat_wordBytes8 G.bLt]
  have herrK : stage2ReadWord (seamKindStore Cs seam (BitVec.ofNat 32 7))
      (Cs.stage.c + 1112) 8 = some S.e := by
    refine natToBytes8_readWord ?_ S.eLt
    rw [← hmemSeam]
    exact evbSeamErr (G := G) (H₁ := H₁) (sh := sh₁) herrH
  have hposK : stage2ReadWord (seamKindStore Cs seam (BitVec.ofNat 32 7))
      Cs.stage.tok 8 = some 1 := by
    rw [← hmemSeam]
    exact evbSeam_pos (C := H₁) (s := sh₁) hdoc.x hdoc.inc hdoc.nep hdoc.ep hdoc.v
      hdoc.ix hdoc.b35 hdoc.hb (BitVec.ofNat 32 7)
      (by
        show (contIx G H₁).toNat = 1
        rw [contIx_toNat G H₁ (by rw [hkH₁]; omega), hkH₁, evbPos_one hent])
  have hendK : stage2ReadWord (seamKindStore Cs seam (BitVec.ofNat 32 7))
      (Cs.stage.tok + 8) 8 = some 2 := by
    rw [← hmemSeam]
    exact evbSeam_end (C := H₁) (s := sh₁) hdoc.x hdoc.inc hdoc.nep hdoc.ep hdoc.v
      hdoc.ix hdoc.b35 hdoc.hb (BitVec.ofNat 32 7)
      (by
        show (BitVec.ofNat 32 2).toNat = 2
        decide)
  have hkindK : stage2ReadWord (seamKindStore Cs seam (BitVec.ofNat 32 7))
      (Cs.stage.tok + 16) 4 = some 7 := by
    rw [← hmemSeam]
    exact evbSeam_kind (C := H₁) (s := sh₁) hdoc.x hdoc.inc hdoc.nep hdoc.ep hdoc.v
      hdoc.ix hdoc.b35 hdoc.hb (BitVec.ofNat 32 7) (by decide)
  have hbufK : stage2ReadWord (seamKindStore Cs seam (BitVec.ofNat 32 7))
      Cs.stage.z 8 = some G.ev := by
    have hread : readBytes (seamKindStore Cs seam (BitVec.ofNat 32 7)) Cs.stage.z 8 =
        some (wordBytes 8 G.ev) :=
      seam_kindStore_keeps_log (G := G) (cA := BitVec.ofNat 32 7) Cs seam (off := 0) (by decide) hInvS.log_base
    rw [stage2ReadWord, hread]
    show some (bytesToNat (wordBytes 8 G.ev)) = some G.ev
    rw [bytesToNat_wordBytes8 G.evLt]
  have hlenK : stage2ReadWord (seamKindStore Cs seam (BitVec.ofNat 32 7))
      (Cs.stage.z + 8) 8 = some C₁.evlen := by
    have hread : readBytes (seamKindStore Cs seam (BitVec.ofNat 32 7))
        (Cs.stage.z + 8) 8 = some (wordBytes 8 C₁.evlen) := by
      have h := seam_kindStore_keeps_log (G := G) (cA := BitVec.ofNat 32 7) Cs seam (off := 8) (by decide)
        hInvS.log_len
      simpa using h
    have h64 : C₁.evlen < 2 ^ 64 := by
      have h1 : C₁.evlen ≤ G.nev0 + stage2RecordBytes * G.n := hInvH₁.evlen_le
      have h2 := G.ev63
      simp only [stage2RecordBytes] at h1 h2
      omega
    rw [stage2ReadWord, hread]
    show some (bytesToNat (wordBytes 8 C₁.evlen)) = some C₁.evlen
    rw [bytesToNat_wordBytes8 h64]
  have hcapK : stage2ReadWord (seamKindStore Cs seam (BitVec.ofNat 32 7))
      (Cs.stage.z + 16) 8 = some G.evcap := by
    have hread : readBytes (seamKindStore Cs seam (BitVec.ofNat 32 7))
        (Cs.stage.z + 16) 8 = some (wordBytes 8 G.evcap) :=
      seam_kindStore_keeps_log (G := G) (cA := BitVec.ofNat 32 7) Cs seam (off := 16) (by decide) hInvS.log_cap
    rw [stage2ReadWord, hread]
    show some (bytesToNat (wordBytes 8 G.evcap)) = some G.evcap
    rw [bytesToNat_wordBytes8 G.evcapLt]
  have hroom : C₁.evlen + stage2RecordBytes ≤ G.evcap := by
    have h := (walkEventReserve_clear (G := G) (C := H₁) (s := sh₁) hInvH₁
      (by rw [hblockH₁]; decide) (by rw [hkH₁]; omega)).2
    simpa [stage2RecordBytes] using h
  -- the seam's staged words
  let hstage : HcontSeamStage G Cs seam (BitVec.ofNat 32 7) :=
    { hInv := hInvS
      rdv := 0
      hroot := hrootS
      hval := hval
      hpreS := ⟨Cs.stage.c, Cs.stage.tok, Cs.stage.z, rfl, G.b, S.e, 1, 2, 7, G.ev,
        C₁.evlen, G.evcap, win, hbaseK, herrK, hposK, hendK, hkindK, hbufK, hlenK,
        hcapK, hroom, hwinK⟩
      heErr := herrK }
  -- the emit row
  have hemit : ∀ rr, stage2Calls stage2SubCalls "od_scalar_value"
      [.ptr Cs.stage.c, .ptr Cs.stage.tok, .ptr Cs.stage.z]
      (seamKindStore Cs seam (BitVec.ofNat 32 7)) seam.next = some rr →
      rr.ret = .int 32 (BitVec.ofNat 32 1) := by
    intro rr hcall
    exact s2ScalarValue_numberRet (mem := seamKindStore Cs seam (BitVec.ofNat 32 7))
      (next := seam.next) (c := Cs.stage.c) (t := Cs.stage.tok) (o := Cs.stage.z)
      (base := G.b) (e := S.e) (pos := 1) (endp := 2) (kind := 7) (buf := G.ev)
      (len := C₁.evlen) (cap := G.evcap) (win := win)
      hcall hbaseK herrK hposK hendK hkindK hbufK hlenK hcapK hroom hwinK (by decide) hlex
  let es : HcontSeamEmitStage G Cs seam (BitVec.ofNat 32 7) := ⟨hstage, hemit⟩
  obtain ⟨calls, hcA, hrdv⟩ := hcontSeamCallsAt es
  have hrdv0 : calls.rdv = 0 := by
    have h : es.stage.rdv = 0 := rfl
    rw [hrdv, h]
  -- the value-position call's post, and the answer it hands back
  obtain ⟨v₁, hv₁, hret₁, hmem₁, hnext₁⟩ :=
    s2ValuePos_sound (args := [.int 32 (BitVec.ofNat 32 Cs.sp), .int 32 calls.rdv,
      .ptr Cs.stage.ctype, .ptr Cs.stage.cst])
      (mem := writeBytes seam.mem (Cs.stage.tok + 16) (natToBytes calls.cA.toNat 4))
      (next := seam.next) calls.hpre₁ calls.hcall₁
  have hvalK : stage2ValuePos
      (writeBytes seam.mem (Cs.stage.tok + 16) (natToBytes calls.cA.toNat 4))
      (BitVec.ofNat 32 Cs.sp).toNat calls.rdv.toNat Cs.stage.ctype Cs.stage.cst =
      some 1 := by
    rw [walkAfterValue_sp hInvS]
    have h := stage2ValuePos_writeBytes_outside (m := seam.mem) (a := Cs.stage.tok + 16)
      (v := natToBytes calls.cA.toNat 4) (sp := Cs.sp) (rd := calls.rdv.toNat)
      (ct := Cs.stage.ctype) (cs := Cs.stage.cst)
      (seamStore_ctype_sep Cs) (seamStore_cst_sep Cs) hInvS.depth_cap
    rw [h]
    have h2 := walkValuePos_answer (G := G) (C := Cs) (s := seam) hInvS
      (sp := Cs.sp) (rd := calls.rdv.toNat) (by rw [hspCs]; decide)
      (by rw [hspCs, hwlenCs])
    rw [h2]
    have hty : Cs.tyMap (Cs.sp - 1) = (2 : UInt8) := htyH₁
    have hst : Cs.stMap (Cs.sp - 1) = (0 : UInt8) := hstH₁
    rw [hty, hst]
    decide
  have hret₁' : calls.r₁.ret = .int 32 (BitVec.ofNat 32 1) := by
    have hv1 : v₁ = 1 := (Option.some.inj (by rw [hvalK] at hv₁; exact hv₁)).symm
    rw [hret₁, hv1]
  have hxA : calls.xA = BitVec.ofNat 32 1 := by
    have h : Value.int 32 calls.xA = Value.int 32 (BitVec.ofNat 32 1) := by
      rw [← calls.hret₁]
      exact hret₁'
    injection h with _ h2
  -- the scalar call's append, at the numeral's own record
  have hmem₁' : calls.r₁.mem = seamKindStore Cs seam (BitVec.ofNat 32 7) := by
    rw [hmem₁, hcA]
  have hcall₂P : stage2Calls stage2SubCalls "od_scalar_value"
      [.ptr Cs.stage.c, .ptr Cs.stage.tok, .ptr Cs.stage.z]
      (seamKindStore Cs seam (BitVec.ofNat 32 7)) seam.next = some calls.r₂ := by
    rw [← hmem₁', ← hnext₁]
    exact calls.hcall₂
  have happ₂ : s2ScalarValueAppend calls.r₁.mem calls.r₂.mem
      (TailCarry₂ Cs).stage.z (EventRecord.number evbBits).encodedBytes := by
    have happ := s2ScalarValue_numberAppend
      (mem := seamKindStore Cs seam (BitVec.ofNat 32 7)) (next := seam.next)
      (c := Cs.stage.c) (t := Cs.stage.tok) (o := Cs.stage.z)
      (base := G.b) (e := S.e) (pos := 1) (endp := 2) (kind := 7) (buf := G.ev)
      (len := C₁.evlen) (cap := G.evcap) (win := win)
      hcall₂P hbaseK herrK hposK hendK hkindK hbufK hlenK hcapK hroom hwinK (by decide) hlex
    rwa [← hmem₁'] at happ
  -- the tail's own cells
  have hreadS : readBytes (writeBytes seam.mem (Cs.stage.tok + 16)
      (natToBytes calls.cA.toNat 4)) (G.next0 + 8) 4 =
      some (natToBytes calls.rdv.toNat 4) := by
    rw [hrdv0, walkReadBytes_rootSlot_of_tokStore (C := H₁) (off := 16) (len := 4)
      (v := natToBytes calls.cA.toNat 4) (by decide) (natToBytes_length _ _)]
    exact hrootS
  have hzreadJ : readBytes calls.r₁.mem Cs.stage.z 8 = some (wordBytes 8 G.ev) := by
    rw [hmem₁']
    simpa only [seamKindStore, hcA] using calls.hzread
  have hkindS : lookupName seam.env "%kind404.i" = some (.ptr (Cs.stage.tok + 16)) :=
    hInvS.regs ("%kind404.i", .ptr (Cs.stage.tok + 16)) (by simp [walkStaticRegs])
  have hrdS : lookupName seam.env "%root_done.i" = some (.ptr (G.next0 + 8)) :=
    hInvS.regs ("%root_done.i", .ptr (G.next0 + 8)) (by simp [walkStaticRegs])
  have hcS : lookupName seam.env "%c.i" = some (.ptr (TailCarry₂ Cs).stage.c) :=
    hInvS.regs ("%c.i", .ptr (TailCarry₂ Cs).stage.c) (by simp [walkStaticRegs])
  have htS : lookupName seam.env "%t352.i" = some (.ptr (TailCarry₂ Cs).stage.tok) :=
    hInvS.regs ("%t352.i", .ptr (TailCarry₂ Cs).stage.tok) (by simp [walkStaticRegs])
  have hzS : lookupName seam.env "%z" = some (.ptr (TailCarry₂ Cs).stage.z) :=
    hInvS.regs ("%z", .ptr (TailCarry₂ Cs).stage.z) (by simp [walkStaticRegs])
  have hopS : evalOperand (stateAt seam.env seam) (.imm (.int 32 (BitVec.ofNat 32 7))) =
      some (.int 32 calls.cA) := by
    rw [hcA]
    rfl
  have hbit0 : evalICmp .eq calls.xA (BitVec.ofNat 32 0) = 0 := by
    rw [hxA]; decide
  have hevlen64 : Cs.evlen < 2 ^ 64 := by
    show C₁.evlen < 2 ^ 64
    have h1 : C₁.evlen ≤ G.nev0 + stage2RecordBytes * G.n := hInvH₁.evlen_le
    have h2 := G.ev63
    simp only [stage2RecordBytes] at h1 h2
    omega
  have htightS : Cs.events.length ≤ Cs.k := by
    have h := hInvH₁.events_le_of_tight (by rw [hblockH₁]; decide)
    show C₁.events.length ≤ C₁.k + 1
    exact h
  have hkltS : Cs.k < G.nep := by
    rw [hkH₁]
    omega
  have hpre₃S : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 Cs.sp), .ptr (G.next0 + 8),
       .ptr (TailCarry₃ Cs (EventRecord.number evbBits)).stage.ctype,
       .ptr (TailCarry₃ Cs (EventRecord.number evbBits)).stage.cst] calls.r₂.mem
      calls.r₂.next :=
    calls.hpre₃
  have hcall₃S : stage2Calls stage2SubCalls "s2_after_value"
      [.int 32 (BitVec.ofNat 32 Cs.sp), .ptr (G.next0 + 8),
       .ptr (TailCarry₃ Cs (EventRecord.number evbBits)).stage.ctype,
       .ptr (TailCarry₃ Cs (EventRecord.number evbBits)).stage.cst] calls.r₂.mem
      calls.r₂.next = some calls.r₃ :=
    calls.hcall₃
  have heiS : lookupName seam.env "%ee.1.i" =
      some (.int 64 (BitVec.ofNat 64 hdoc.v.toNat)) :=
    scSeamByte_ee _ _ _ _ _ _
  have hcdS : lookupName seam.env "%cond350.i" =
      some (.int 64 (BitVec.ofNat 64 hdoc.v.toNat)) := by
    rw [scSeamByte_cond]
    exact sLand_cond H₁ sh₁ hdoc.x hdoc.inc hdoc.nep hdoc.ep hdoc.v hdoc.ix hdoc.b35
  have hcd64 : hdoc.v.toNat < 2 ^ 64 := by
    have := hdoc.v.isLt
    omega
  -- the tail's segment, at the numeral's record
  have hSegT := consumerTailSegEmptyAt (G := G) (C := Cs) (s := seam)
    calls.r₁ calls.r₂ calls.r₃ (EventRecord.number evbBits) hdoc.v.toNat
    hInvS (by rfl) "if.end372.i" "if.end372.i" calls.cA
    (.imm (.int 32 (BitVec.ofNat 32 7))) calls.rdv calls.xA
    (scSeamByte_pre _ _ _ _ _ _) (by decide) hopS hkindS hrdS hreadS calls.hpre₁
    calls.hcall₁ calls.hret₁ hbit0 hzreadJ hcS htS hzS calls.hcall₂ happ₂ calls.hret₂
    G.evLt hevlen64 htightS hkltS hpre₃S hcall₃S heiS hcdS hcd64
  -- the number's revolution
  have hTail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ (ContAC₇ H₁))
      (scSeamByte (sLand H₁ sh₁ hdoc.x hdoc.inc hdoc.nep hdoc.ep hdoc.v hdoc.ix hdoc.b35)
        hdoc.v.toNat hdoc.x H₁.stage.tok hdoc.b35 hdoc.hb)
      (TailCarryEnd (HeadC₄₁₃ (ContAC₇ H₁)) (EventRecord.number evbBits))
      (scEndByte (sLand H₁ sh₁ hdoc.x hdoc.inc hdoc.nep hdoc.ep hdoc.v hdoc.ix hdoc.b35)
        hdoc.v.toNat hdoc.x H₁.stage.tok hdoc.b35 hdoc.hb
        calls.r₁ calls.r₂ calls.r₃ calls.cA calls.rdv calls.xA) 3 :=
    Seg.measure hSegT
  let f : HcontScalarFacts G H₁ sh₁ :=
    { x := hdoc.x
      h8 := hdoc.h8
      hlt91 := hdoc.hlt91
      h44 := hdoc.h44
      h58 := hdoc.h58
      hne44 := hdoc.hne44
      hbit := hdoc.hbit
      inc := hdoc.inc
      nep := hdoc.nep
      hinc := hdoc.hinc
      hnep := hdoc.hnep
      hnext := hdoc.hnext
      ep := hdoc.ep
      v := hdoc.v
      h5 := hdoc.h5
      hi63 := hdoc.hi63
      hread := hdoc.hread
      ix := hdoc.ix
      hidx5 := hdoc.hidx5
      htok5 := hdoc.htok5
      hgap5 := hdoc.hgap5
      hugt := hdoc.hugt
      b35 := hdoc.b35
      hread35 := hdoc.hread35
      hb := hdoc.hb
      r₁ := calls.r₁
      r₂ := calls.r₂
      r₃ := calls.r₃
      ev := EventRecord.number evbBits
      cA := calls.cA
      rdv := calls.rdv
      xA := calls.xA
      hTail := hTail }
  obtain ⟨hsegN, hInvN, hblkN, hpreN, hkN, hincN, hnepN, -⟩ :=
    walkRevolutionMergeSegScalar G H₁ sh₁ hInvH₁ hblockH₁ hklt₁ f
  -- the numeral's route is the high leaf's four links
  have hcount : hlastByteCount f.hb = 4 := rfl
  have hsegN16 : WalkSegment (stage2Calls stage2SubCalls) G H₁ sh₁
      (scMergeC H₁ f.ev) (scMergeF f) 16 := by
    rw [hcount] at hsegN
    exact hsegN
  -- the second header pass
  have hspv₂ : evalOperand (scMergeF f) (.reg "%sp.i.0248") =
      some (.int 32 (BitVec.ofNat 32 1)) := by
    simp only [evalOperand]
    rw [hInvN.depth_reg]
  have hkv₂ : evalOperand (scMergeF f) (.reg "%inc.i") =
      some (.int 64 (BitVec.ofNat 64 2)) := by
    simp only [evalOperand]
    rw [hincN]
  have hguard₂ : 2 < (BitVec.ofNat 64 G.nep).toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnep_lt]
    omega
  have hcap₂ : 2 < G.nep := by omega
  have hadv₂ : (scMergeC H₁ f.ev).k < 2 := by
    rw [hkN, hkH₁]
    omega
  have hspcap₂ : 1 ≤ stage2StackExtent := by decide
  have hspw₂ : 1 ≤ (scMergeC H₁ f.ev).wlen := by
    rw [← show (scMergeC H₁ f.ev).sp = 1 from rfl]
    exact hInvN.sp_le_wlen
  obtain ⟨sh₂, hsegH₂, hInvH₂, hmemH₂⟩ :=
    evbHeadPassAt (G := G) (C := scMergeC H₁ f.ev) (s := scMergeF f) hInvN hblkN
      (prev := "if.end473.i") (spv := 1) (k2 := 2)
      (spOp := .reg "%sp.i.0248") (kOp := .reg "%inc.i")
      (nepv := BitVec.ofNat 64 G.nep)
      hpreN (by decide) hspv₂ (by decide) hkv₂ hnepN hguard₂ hcap₂ hadv₂ hspcap₂ hspw₂
      (hent := hent) hnep3 (Or.inr rfl)
  -- the second head's cells
  let H₂ : WalkCarry G := headPassC (scMergeC H₁ f.ev) 2 1
  have hkH₂ : H₂.k = 2 := rfl
  have hspH₂ : H₂.sp = 1 := rfl
  have hblockH₂ : H₂.block = walkLoopHead := rfl
  have h8₂ : evalOperand sh₂ (.reg "%8") = some (.int 8 (BitVec.ofNat 8 93)) := by
    have h := hInvH₂.iter.reg8
    rw [hkH₂, evbByte_two hbs hent] at h
    simp only [evalOperand]
    rw [h]
    rfl
  have hbe₂ : BitVec.ofNat 8 (entryByte G H₂.k).toNat = BitVec.ofNat 8 93 := by
    rw [hkH₂, evbByte_two hbs hent]
    rfl
  have hmark : H₂.tyMap (H₂.sp - 1) = (2 : UInt8) := by
    show (scMergeC H₁ f.ev).tyMap 0 = 2
    show H₁.tyMap (H₁.sp - 1) = 2
    exact htyH₁
  have hstate : H₂.stMap (H₂.sp - 1) = (1 : UInt8) := by
    show walkAfterValueMap (TailCarry₃ (HeadC₄₁₃ (ContAC₇ H₁))
      (EventRecord.number evbBits)) 0 = 1
    rw [walkAfterValueMap, walkAfterValueMapAt_pos (by
      rw [show (TailCarry₃ (HeadC₄₁₃ (ContAC₇ H₁)) (EventRecord.number evbBits)).sp = 1
        from rfl]
      decide)]
    show UInt8.ofNat (if ((TailCarry₃ (HeadC₄₁₃ (ContAC₇ H₁))
      (EventRecord.number evbBits)).tyMap (1 - 1)).toNat = 1 then 3 else 1) = 1
    have hty : ((TailCarry₃ (HeadC₄₁₃ (ContAC₇ H₁)) (EventRecord.number evbBits)).tyMap
        (1 - 1)).toNat = 2 := by
      show (H₁.tyMap (H₁.sp - 1)).toNat = 2
      rw [htyH₁]
      rfl
    rw [hty]
    decide
  have hpreA : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 H₂.sp + BitVec.ofNat 32 4294967295), .ptr (G.next0 + 8),
       .ptr H₂.stage.ctype, .ptr H₂.stage.cst] sh₂.mem sh₂.next := by
    refine ⟨BitVec.ofNat 32 H₂.sp + BitVec.ofNat 32 4294967295, G.next0 + 8,
      H₂.stage.ctype, H₂.stage.cst, rfl, Or.inl ?_⟩
    show (BitVec.ofNat 32 1 + BitVec.ofNat 32 4294967295).toNat = 0
    decide
  -- the closing bracket's merge
  obtain ⟨s₃, hsegC, hpreC, hsubC, hincC, hnepC, hrootC⟩ :=
    closeBracketMerge_term (G := G) (C := H₂) (s := sh₂) hInvH₂ hblockH₂ h8₂ hbe₂
      (by rw [hspH₂]; decide) hspH₂ hmark hstate (by decide) (by decide) hpreA
  -- the merge's readings
  have hmergePre : s₃.pre = some "out_reserve.exit.i.i60" := hpreC
  have hspM : phiIncoming "out_reserve.exit.i.i60" cleanupSpIncoming =
      some (.reg "%sub.i") := by decide
  have hspvM : evalOperand s₃ (.reg "%sub.i") =
      some (.int 32 (BitVec.ofNat 32 (H₂.sp - 1))) := by
    simpa only [evalOperand] using hsubC
  have hkM : phiIncoming "out_reserve.exit.i.i60" cleanupKIncoming =
      some (.reg "%inc.i") := by decide
  have hkvM : evalOperand s₃ (.reg "%inc.i") =
      some (.int 64 (BitVec.ofNat 64 (H₂.k + 1))) := by
    simpa only [evalOperand] using hincC
  have hnpM : lookupName s₃.env "%nep" = some (.int 64 (BitVec.ofNat 64 G.nep)) := hnepC
  have htermM : H₂.k + 1 = (BitVec.ofNat 64 G.nep).toNat := by
    rw [hkH₂, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnep_lt, hnep3]
  have hsp0M : evalICmp .eq (BitVec.ofNat 32 (H₂.sp - 1)) (BitVec.ofNat 32 0) = 1 := by
    rw [hspH₂]
    decide
  have hrootM : readBytes s₃.mem (G.next0 + 8) 4 =
      some (natToBytes (1 : BitVec 32).toNat 4) := by
    simpa using hrootC
  have hroot0M : evalICmp .eq (1 : BitVec 32) (BitVec.ofNat 32 0) = 0 := by decide
  -- the public result
  exact evb_caller_result (m0 := m0) (G := G) (S := S)
    (C₁ := C₁) (H₁ := H₁) (C₂ := scMergeC H₁ f.ev) (H₂ := H₂)
    (C₃ := closeCEnd (closeC₁₀b H₂)
      (BitVec.ofNat 32 H₂.sp + BitVec.ofNat 32 4294967295) (BitVec.ofNat 8 4))
    (s₀ := s₀) (s₁ := s₁) (sh₁ := sh₁) (s₂ := scMergeF f) (sh₂ := sh₂) (s₃ := s₃)
    (p₁ := 9) (p₂ := 16) (p₃ := 11) (b := b) (ev := EventRecord.number evbBits)
    (spz := BitVec.ofNat 32 H₂.sp + BitVec.ofNat 32 4294967295) (c8 := BitVec.ofNat 8 4)
    (k₁ := 1) (sp₁ := 1) (k₂ := 2) (sp₂ := 1)
    hpre hstageWord hndstG hnevG hdstG hevG hnev0
    hsegO hsegH₁ hsegN16 hsegH₂ hsegC rfl rfl rfl rfl rfl
    hb3 rfl rfl
    (p := "out_reserve.exit.i.i60")
    (spOp := .reg "%sub.i") (kOp := .reg "%inc.i")
    (spv := H₂.sp - 1) (k2 := H₂.k + 1) (nepv := BitVec.ofNat 64 G.nep)
    hmergePre hspM hspvM hkM hkvM hnpM htermM hsp0M hrootM
    (rv := 1) hroot0M

/-! ### Axiom footprints -/

#print axioms evb_n3
#print axioms evb_nep3
#print axioms evbOpenRoot
#print axioms evb_caller_result_staged

end WalkScope
end LeanLLVM.Refinement
