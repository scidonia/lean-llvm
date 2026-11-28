/-
# The seam's window is the numeral's lexeme

The scalar seam's window is read at `base + pos` for `max (endp - pos) 5` bytes.
The token's words fix `pos = 1`, `end = 2`, so the window starts at the document's
second byte; the environment row `hbase` fixes `base = G.b`.  The *five-byte* read
is at the seam's own memory already (`s2ScalarValuePre`'s `hwin`), so only the
one-byte document fact `readBytes s.mem (G.b + 1) 1 = some [0x31]` is transported
across the seam's four token stores.  The separation needed is the token record's
from that one byte, and `WalkInv.doc_outside` supplies it because the token record
is inside `walkWideAt`'s list while the document's byte is not.  The window's
prefix is then the one-byte read (`readBytes_take_prefix`), not a second
transport of the five-byte extent.

There is no `sorry`, `admit` or `native_decide`.
-/
import LeanLLVM.Refinement.JsonEventCallerResultSeamWords
import LeanLLVM.Refinement.JsonStage2WalkAlignment

set_option autoImplicit false

namespace LeanLLVM.Refinement
namespace WalkScope

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2IR

/-- **The token record's interval misses the document's second byte** (or lies
wholly to its left).  The record is one of the seven appended objects, hence in
`walkWideAt`; the document's byte is outside it (`WalkInv.doc_outside`). -/
theorem evbSeam_tok_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hbs : G.bs = evbDoc) (hent : G.ent = [0, 1, 2]) :
    G.b + 2 ≤ C.stage.tok ∨ C.stage.tok + stage2TokenExtent ≤ G.b + 1 := by
  have hmem2 : entryPos G 2 ∈ G.ent := by
    simp [entryPos, hent]
  have h1n : 1 < G.n := by
    have h := G.inside (entryPos G 2) hmem2
    rw [show entryPos G 2 = 2 from by simp [entryPos, hent]] at h
    omega
  have hnot : ¬ inRegions (walkWideAt G C (s.next - G.next0)) (G.b + 1) :=
    hInv.doc_outside (e := G.b + 1) (by omega) (by omega)
  by_contra h
  push_neg at h
  refine hnot ⟨(C.stage.tok, stage2TokenExtent), ?_, by omega, by
    simp only [stage2TokenExtent] at h ⊢; omega⟩
  simp only [walkWideAt, walkPresent]
  exact List.mem_append_left _ (List.mem_append_right _
    (by simp [stage2ReportScratch, stage2StagedWrites]))

/-- **The document's second byte survives the seam's four token stores.**  Each
store is at `tok + off` with `off` one of `0, 8, 16, 20`, and the separation above
puts the whole 24-byte record away from the one byte. -/
theorem evbSeam_docByte {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hbs : G.bs = evbDoc) (hent : G.ent = [0, 1, 2])
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32)
    (ix : BitVec 64) (b35 : UInt8) (hb : HcontByteRoute (cont35 b35))
    (cA : BitVec 32) :
    readBytes (evbSeamCallsMem C s x inc nep ep v ix b35 hb cA) (G.b + 1) 1 =
      some [0x31] := by
  have hsep := evbSeam_tok_sep (G := G) (C := C) (s := s) hInv hbs hent
  have hsep' := hsep
  simp only [stage2TokenExtent] at hsep'
  have hdoc : readBytes s.mem (G.b + 1) 1 = some [0x31] := by
    have hmem2 : entryPos G 2 ∈ G.ent := by
      simp [entryPos, hent]
    have h1n : 1 < G.n := by
      have h := G.inside (entryPos G 2) hmem2
      rw [show entryPos G 2 = 2 from by simp [entryPos, hent]] at h
      omega
    have hA : readBytes s.mem (G.b + 1) (G.n - 1) = some (G.bs.drop 1) := by
      have := (readBytes_split s.mem G.b 1 (G.n - 1) (by
        rw [show 1 + (G.n - 1) = G.n by omega]; exact hInv.doc_read)).2
      simpa using this
    have hB : readBytes s.mem (G.b + 1) 1 = some ((G.bs.drop 1).take 1) := by
      have := (readBytes_split s.mem (G.b + 1) 1 (G.n - 1 - 1) (by
        rw [show 1 + (G.n - 1 - 1) = G.n - 1 by omega]; exact hA)).1
      simpa using this
    rw [hbs] at hB
    simpa [evbDoc] using hB
  simp only [evbSeamCallsMem]
  rw [walkReadBytes_writeBytes_outside (start := C.stage.tok + 16)
        (v := natToBytes cA.toNat 4) (by
          rw [natToBytes_length]; rcases hsep' with h | h
          · left; omega
          · right; omega),
      walkReadBytes_writeBytes_outside (start := C.stage.tok + 8)
        (v := natToBytes (BitVec.ofNat 64 v.toNat).toNat 8) (by
          rw [natToBytes_length]; rcases hsep' with h | h
          · left; omega
          · right; omega),
      walkReadBytes_writeBytes_outside (start := C.stage.tok + 20)
        (v := natToBytes (BitVec.ofNat 32 1).toNat 4) (by
          rw [natToBytes_length]; rcases hsep' with h | h
          · left; omega
          · right; omega),
      walkReadBytes_writeBytes_outside (start := C.stage.tok)
        (v := natToBytes ix.toNat 8) (by
          rw [natToBytes_length]; rcases hsep' with h | h
          · left; omega
          · right; omega)]
  exact hdoc

/-- **The window's lexeme is the numeral's.**  Given the base row and the three
token words, the window starts at the document's second byte and its one-byte
prefix is `[0x31]`; hence its `(end - pos)`-byte prefix (which is one byte) is the
numeral's lexeme. -/
theorem evbSeam_lexeme {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hbs : G.bs = evbDoc) (hent : G.ent = [0, 1, 2])
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32)
    (ix : BitVec 64) (b35 : UInt8) (hb : HcontByteRoute (cont35 b35))
    (cA : BitVec 32)
    {base pos endp : Nat} {win : List UInt8}
    (hbase : base = G.b) (hpos : pos = 1) (hend : endp = 2)
    (hwin : readBytes (evbSeamCallsMem C s x inc nep ep v ix b35 hb cA)
      (base + pos) (max (endp - pos) 5) = some win) :
    win.take (endp - pos) = [0x31] := by
  have hdoc := evbSeam_docByte (G := G) (C := C) (s := s) hInv hbs hent
    x inc nep ep v ix b35 hb cA
  have hwin' : readBytes (evbSeamCallsMem C s x inc nep ep v ix b35 hb cA)
      (G.b + 1) 5 = some win := by
    rw [← hwin]
    simp [hbase, hpos, hend]
  have hwin1 : readBytes (evbSeamCallsMem C s x inc nep ep v ix b35 hb cA)
      (G.b + 1) 1 = some (win.take 1) :=
    readBytes_take_prefix (by decide) hwin'
  have hlex1 : win.take 1 = [0x31] :=
    Option.some.inj (hwin1.symm.trans hdoc)
  rw [show endp - pos = 1 by omega]
  exact hlex1

/-! ### Axiom footprints -/

#print axioms evbSeam_tok_sep
#print axioms evbSeam_docByte
#print axioms evbSeam_lexeme

end WalkScope
end LeanLLVM.Refinement
