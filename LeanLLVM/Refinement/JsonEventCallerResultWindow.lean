/-
# The seam's five-byte window, from the staged separation

`s2ScalarValuePre` asks for the document's window at the seam: `max (endp - pos) 5`
bytes at `base + pos`, and `s2ScalarValue_numberRet` reads the numeral's lexeme off
its `(endp - pos)`-byte prefix.  At `[1]` the token's words fix `pos = 1` and
`end = 2`, so the window starts at the document's second byte and the extent is
five.

This module *derives* that read at the seam's own memory rather than taking it as a
row.  The five bytes are the document's second and third (`1` and `]`) followed by
three bytes of the decoder's staged read-past tail: the region the staging reserves
for the document is `(b, n + stage2ReadTail)`, so the tail the caller stages at
`b + n` is part of the same object.  The walk's frame is silent on that whole
region (`WalkInv.docTail_outside`, the extension of `doc_outside` from the `n`
document bytes to the reserved width), and the token record is separate from it by
the staging's own `DisjointRegions` (`stage2StagedWrites_against`), so the four
stores the seam makes inside the record (`condEnd349OutAt`'s position and marker,
`seamFin`'s end, and `if.then413.i`'s kind) leave the five bytes alone.

The result is one row: the window's bytes at `evbSeamCallsMem`, with its one-byte
lexeme `[0x31]` — the numeral `1`.  Nothing about the window is assumed.

There is no `sorry`, `admit` or `native_decide`.
-/
import LeanLLVM.Refinement.JsonEventCallerResultStaged

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2IR

/-! ### The document's reserved region is outside the walk's frame -/

/-- **The document and its staged read-past tail are outside the walk's whole
frame.**  `doc_outside` excludes the `n` document bytes; the staging reserves
`n + stage2ReadTail` for the object (`stage2Regions`' first entry), and the same
two arguments cover the reservation: the staged objects are separate from the
region as a whole, and the cursor's interval starts at the watermark, above the
region's end. -/
theorem WalkInv.docTail_outside {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (h : WalkInv G C s) {e : Nat}
    (ha : G.b ≤ e) (he : e < G.b + (G.n + stage2ReadTail)) :
    ¬ inRegions (walkWideAt G C (s.next - G.next0)) e := by
  have hpresent : ¬ inRegions (walkPresent G C) e := by
    have hsep := disjointRegions_staged_prefix C.stage.separate
    have h03 := stage2Regions_sep hsep (i := 0) (j := 3)
      (by simp [stage2Regions]) (by simp [stage2Regions]) (by decide)
    have h04 := stage2Regions_sep hsep (i := 0) (j := 4)
      (by simp [stage2Regions]) (by simp [stage2Regions]) (by decide)
    simp only [stage2Regions, List.getElem_cons_zero, List.getElem_cons_succ] at h03 h04
    refine walkPresent_outside h (a := G.b) (m := G.n + stage2ReadTail) (e := e)
      ?_ ?_ ?_ ?_ ha he
    · omega
    · omega
    · intro r hr
      have hout := stage2StagedWrites_against C.stage.separate
        (a := G.b) (m := G.n + stage2ReadTail) (by simp [stage2Regions]) r hr
      rcases hout with h' | h' <;> omega
    · rcases C.stage.dSep (G.b, G.n + stage2ReadTail)
        (by simp [stage2WalkRegions, stage2Regions]) with hd | hd
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
  have hlt : e < G.next0 :=
    Nat.lt_of_lt_of_le he
      (G.watermark (G.b, G.n + stage2ReadTail) (by simp [stage2Regions]))
  intro hw
  obtain ⟨r, hr, hlo, hhi⟩ := hw
  simp only [walkWideAt] at hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hpresent ⟨r, hr, hlo, hhi⟩
  · exact not_interval_of_lt hlt ⟨r, hr, hlo, hhi⟩

namespace WalkScope

/-! ### The five bytes of `[1]` at the staging -/

/-- **The document's five bytes at `b + 1`.**  `[1]` is three bytes, so the first
two of the five are its second and third (`1`, `]`) and the last three are the
staged tail's; the concatenation is the read.  Its one-byte prefix is the numeral. -/
theorem evbDoc_read5 {m0 : Mem} {G : WalkGeom m0}
    (hbs : G.bs = evbDoc) (hn : G.n = 3) :
    ∃ win, readBytes m0 (G.b + 1) 5 = some win ∧ win.take 1 = [0x31] := by
  obtain ⟨t, ht⟩ := G.tail
  have hdoc : readBytes m0 (G.b + 1) (G.n - 1) = some (G.bs.drop 1) :=
    (readBytes_split m0 G.b 1 (G.n - 1) (by
      rw [show 1 + (G.n - 1) = G.n by omega]; exact G.doc)).2
  have hdoc2 : readBytes m0 (G.b + 1) 2 = some (G.bs.drop 1) := by
    have h2 : G.n - 1 = 2 := by omega
    rwa [h2] at hdoc
  have ht3 : readBytes m0 ((G.b + 1) + 2) 3 = some (t.take 3) := by
    have h := readBytes_take_prefix (mem := m0) (a := G.b + G.n) (n := 3)
      (m := stage2ReadTail) (bs := t) (by decide) ht
    rwa [show (G.b + 1) + 2 = G.b + G.n by omega]
  have happ : readBytes m0 (G.b + 1) (2 + 3) =
      some ((G.bs.drop 1) ++ t.take 3) :=
    JsonEntrySteps.readBytes_append m0 2 (G.b + 1) (G.bs.drop 1) 3 (t.take 3) hdoc2 ht3
  refine ⟨(G.bs.drop 1) ++ t.take 3, by simpa using happ, ?_⟩
  rw [hbs]
  simp [evbDoc]

/-! ### Across the walk's frame and the seam's four stores -/

/-- **The seam's five-byte window, at the memory its three calls are made at.**  The
staged read (`evbDoc_read5`) crosses the walk's frame (`docTail_outside`), and then
the four token-record stores: the record is one of the seven the caller stages, and
the document's reserved region is another entry of the staging's list, so the two
are separate (`stage2StagedWrites_against`) and each store misses the window. -/
theorem evbSeam_window {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hbs : G.bs = evbDoc) (hn : G.n = 3)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32)
    (ix : BitVec 64) (b35 : UInt8) (hb : HcontByteRoute (cont35 b35)) (cA : BitVec 32) :
    ∃ win, readBytes (evbSeamCallsMem C s x inc nep ep v ix b35 hb cA) (G.b + 1) 5 =
      some win ∧ win.take 1 = [0x31] := by
  obtain ⟨w0, hw0, hlex⟩ := evbDoc_read5 (G := G) (m0 := m0) hbs hn
  have hframe : readBytes s.mem (G.b + 1) 5 = some w0 := by
    have h := readBytes_eq_of_UnchangedOn (mem := m0) (m := s.mem)
      (unchangedOutside_iff_inRegions.mp hInv.frame) (a := G.b + 1) (n := 5) ?_
    · rw [h]; exact hw0
    · intro k hk
      have hc : stage2ReadTail = 32 := rfl
      exact hInv.docTail_outside (by omega) (by omega)
  have hsep := stage2StagedWrites_against C.stage.separate (a := G.b)
    (m := G.n + stage2ReadTail) (by simp [stage2Regions])
    (r := (C.stage.tok, stage2TokenExtent)) (by simp [stage2StagedWrites])
  simp only [stage2TokenExtent, stage2ReadTail] at hsep
  refine ⟨w0, ?_, hlex⟩
  simp only [evbSeamCallsMem]
  rw [walkReadBytes_writeBytes_outside (start := C.stage.tok + 16)
        (v := natToBytes cA.toNat 4) (by
          rw [natToBytes_length]; rcases hsep with h | h <;> omega),
      walkReadBytes_writeBytes_outside (start := C.stage.tok + 8)
        (v := natToBytes (BitVec.ofNat 64 v.toNat).toNat 8) (by
          rw [natToBytes_length]; rcases hsep with h | h <;> omega),
      walkReadBytes_writeBytes_outside (start := C.stage.tok + 20)
        (v := natToBytes (BitVec.ofNat 32 1).toNat 4) (by
          rw [natToBytes_length]; rcases hsep with h | h <;> omega),
      walkReadBytes_writeBytes_outside (start := C.stage.tok)
        (v := natToBytes ix.toNat 8) (by
          rw [natToBytes_length]; rcases hsep with h | h <;> omega)]
  exact hframe

/-- **The window row `s2ScalarValuePre` reads**, at the token's `pos = 1` and
`end = 2`: the read's extent is `max (endp - pos) 5 = 5` and its `(endp - pos)`-byte
prefix is the numeral. -/
theorem evbSeam_windowAt {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hbs : G.bs = evbDoc) (hn : G.n = 3)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32)
    (ix : BitVec 64) (b35 : UInt8) (hb : HcontByteRoute (cont35 b35)) (cA : BitVec 32)
    {base pos endp : Nat} (hbase : base = G.b) (hpos : pos = 1) (hend : endp = 2) :
    ∃ win, readBytes (evbSeamCallsMem C s x inc nep ep v ix b35 hb cA)
        (base + pos) (max (endp - pos) 5) = some win ∧
      win.take (endp - pos) = [0x31] := by
  obtain ⟨win, hw, hlex⟩ :=
    evbSeam_window (G := G) (C := C) (s := s) hInv hbs hn x inc nep ep v ix b35 hb cA
  refine ⟨win, ?_, ?_⟩
  · rw [hbase, hpos, hend]; simpa using hw
  · rw [hpos, hend]; exact hlex

/-! ### Axiom footprints -/

#print axioms WalkInv.docTail_outside
#print axioms evbDoc_read5
#print axioms evbSeam_window
#print axioms evbSeam_windowAt

end WalkScope
end LeanLLVM.Refinement
