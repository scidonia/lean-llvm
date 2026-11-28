/-
# The scalar seam's token words, and the field the record needs

The scalar route's seam `scSeamByte (sLand C s …) v.toNat x tok b35 hb` stores the
token's two words (`condEnd349OutAt` writes the position at `%t352.i` and `seamFin`
the end at `%t352.i + 8`) and `if.then413.i` stores the kind at `+ 16`.  This module
reads the three words back at the memory the three calls are made at, so a caller
holds `pos`, `end` and `kind` as consequences of the seam's own stores.

What is *not* here is `%c.i`'s base word.  The cursor record is staged by the
entry's third segment (`walkSeg3Stores`, `JsonStage2WalkRun:883`, `%c.i + 0 =
natToBytes b 8`), but `WalkInv` carries the record's *address* (`ptrs`, `regs`),
the objects' *presence* (`owned`) and silence outside them (`frame`) — not the four
words inside it.  So the base is the one field a caller must stage beside the seam;
`JsonStage2WalkDispatchSeamCalls`' `hpreS` names the same two words (`hbase`, `he`)
and its docstring records why no producer exists.

There is no `sorry`, `admit` or `native_decide`.
-/
import LeanLLVM.Refinement.JsonStage2WalkSpansChain

set_option autoImplicit false

namespace LeanLLVM.Refinement
namespace WalkScope

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR

/-- The memory the seam's three calls are made at: the seam's own with the kind
store (`if.then413.i`'s first instruction) applied, written out as its four
stores. -/
abbrev evbSeamCallsMem {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32)
    (ix : BitVec 64) (b35 : UInt8) (hb : HcontByteRoute (cont35 b35))
    (cA : BitVec 32) : Mem :=
  writeBytes
    (writeBytes
      (writeBytes
        (writeBytes (scS₅ s x inc nep).mem C.stage.tok (natToBytes ix.toNat 8))
        (C.stage.tok + 20) (natToBytes (BitVec.ofNat 32 1).toNat 4))
      (C.stage.tok + 8) (natToBytes (BitVec.ofNat 64 v.toNat).toNat 8))
    (C.stage.tok + 16) (natToBytes cA.toNat 4)

/-- **The seam's memory is the call's memory.**  The four stores are, in order,
`condEnd349OutAt`'s position and marker, `seamFin`'s end and the kind store. -/
theorem evbSeamCallsMem_seam {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32)
    (ix : BitVec 64) (b35 : UInt8) (hb : HcontByteRoute (cont35 b35))
    (cA : BitVec 32) :
    evbSeamCallsMem C s x inc nep ep v ix b35 hb cA =
      writeBytes
        (scSeamByte (sLand C s x inc nep ep v ix b35) v.toNat x C.stage.tok b35 hb).mem
        (C.stage.tok + 16) (natToBytes cA.toNat 4) := by
  simp only [evbSeamCallsMem]
  rw [scSeamByte_mem]
  rfl

/-- **The token's position at the seam.**  The position store is the last write at
`%t352.i`; the end, marker and kind stores start above it. -/
theorem evbSeam_pos {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32)
    (ix : BitVec 64) (b35 : UInt8) (hb : HcontByteRoute (cont35 b35))
    (cA : BitVec 32) (hix : ix.toNat = 1) :
    stage2ReadWord (evbSeamCallsMem C s x inc nep ep v ix b35 hb cA)
      C.stage.tok 8 = some 1 := by
  have hread : readBytes
      (evbSeamCallsMem C s x inc nep ep v ix b35 hb cA) C.stage.tok 8 =
      some (natToBytes ix.toNat 8) := by
    simp only [evbSeamCallsMem]
    rw [walkReadBytes_writeBytes_outside (start := C.stage.tok + 16)
          (v := natToBytes cA.toNat 4) (by rw [natToBytes_length]; omega),
        walkReadBytes_writeBytes_outside (start := C.stage.tok + 8)
          (v := natToBytes (BitVec.ofNat 64 v.toNat).toNat 8)
          (by rw [natToBytes_length]; omega),
        walkReadBytes_writeBytes_outside (start := C.stage.tok + 20)
          (v := natToBytes (BitVec.ofNat 32 1).toNat 4)
          (by rw [natToBytes_length]; omega)]
    simpa only [natToBytes_length] using
      (readBytes_writeBytes_same (m := (scS₅ s x inc nep).mem)
        (addr := C.stage.tok) (bs := natToBytes ix.toNat 8))
  have hval : bytesToNat (natToBytes ix.toNat 8) = 1 := by
    rw [natToBytes_toNat, show (256 : Nat) ^ 8 = 2 ^ 64 from by decide,
      Nat.mod_eq_of_lt ix.isLt, hix]
  rw [stage2ReadWord, hread]
  simp only [hval, Option.map]

/-- **The token's end at the seam**, from `seamFin`'s store at `%t352.i + 8`. -/
theorem evbSeam_end {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32)
    (ix : BitVec 64) (b35 : UInt8) (hb : HcontByteRoute (cont35 b35))
    (cA : BitVec 32) (hv : v.toNat = 2) :
    stage2ReadWord (evbSeamCallsMem C s x inc nep ep v ix b35 hb cA)
      (C.stage.tok + 8) 8 = some 2 := by
  have hread : readBytes
      (evbSeamCallsMem C s x inc nep ep v ix b35 hb cA) (C.stage.tok + 8) 8 =
      some (natToBytes (BitVec.ofNat 64 v.toNat).toNat 8) := by
    simp only [evbSeamCallsMem]
    rw [walkReadBytes_writeBytes_outside (start := C.stage.tok + 16)
          (v := natToBytes cA.toNat 4) (by rw [natToBytes_length]; omega)]
    simpa only [natToBytes_length] using
      (readBytes_writeBytes_same (m :=
        (writeBytes (writeBytes (scS₅ s x inc nep).mem C.stage.tok
          (natToBytes ix.toNat 8)) (C.stage.tok + 20)
          (natToBytes (BitVec.ofNat 32 1).toNat 4)))
        (addr := C.stage.tok + 8)
        (bs := natToBytes (BitVec.ofNat 64 v.toNat).toNat 8))
  have hval : bytesToNat (natToBytes (BitVec.ofNat 64 v.toNat).toNat 8) = 2 := by
    rw [natToBytes_toNat, show (256 : Nat) ^ 8 = 2 ^ 64 from by decide,
      Nat.mod_eq_of_lt (BitVec.ofNat 64 v.toNat).isLt, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), hv]
  rw [stage2ReadWord, hread]
  simp only [hval, Option.map]

/-- **The token's kind at the seam**: the kind store is the last write at
`%t352.i + 16`. -/
theorem evbSeam_kind {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32)
    (ix : BitVec 64) (b35 : UInt8) (hb : HcontByteRoute (cont35 b35))
    (cA : BitVec 32) (hcA : cA.toNat = 7) :
    stage2ReadWord (evbSeamCallsMem C s x inc nep ep v ix b35 hb cA)
      (C.stage.tok + 16) 4 = some 7 := by
  have hread : readBytes
      (evbSeamCallsMem C s x inc nep ep v ix b35 hb cA) (C.stage.tok + 16) 4 =
      some (natToBytes cA.toNat 4) := by
    simp only [evbSeamCallsMem]
    simpa only [natToBytes_length] using readBytes_writeBytes_same (m :=
      (writeBytes (writeBytes (writeBytes (scS₅ s x inc nep).mem C.stage.tok
        (natToBytes ix.toNat 8)) (C.stage.tok + 20)
        (natToBytes (BitVec.ofNat 32 1).toNat 4)) (C.stage.tok + 8)
        (natToBytes (BitVec.ofNat 64 v.toNat).toNat 8)))
      (addr := C.stage.tok + 16) (bs := natToBytes cA.toNat 4)
  have hval : bytesToNat (natToBytes cA.toNat 4) = 7 := by
    rw [natToBytes_toNat, show (256 : Nat) ^ 4 = 2 ^ 32 from by decide,
      Nat.mod_eq_of_lt (by rw [hcA]; decide), hcA]
  rw [stage2ReadWord, hread]
  simp only [hval, Option.map]

/-! ### What the record is missing

The three words above are the whole of the record's *token*; the fourth and fifth
of `s2ScalarValuePre`'s words are the log's (`WalkInv.log_base`, `log_len`,
`log_cap`) and the sixth is the delivered window.  The staging's first word at
`%c.i` is the cursor record's base, which no clause of `WalkInv` carries; the
entry writes it (`walkSeg3Stores`, `JsonStage2WalkRun:883`) and no block of the
walk rewrites it, but that no-write fact is not part of the invariant.  So the
numeral's record is fixed by the seam's three words plus the base, and the base is
the field a caller stages. -/

/-- **The token's three words, together**: position `1`, end `2`, kind `7` at the
memory the seam's calls are made at. -/
theorem evbSeam_token_words {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (x : BitVec 8) (inc nep : BitVec 64) (ep : Nat) (v : BitVec 32)
    (ix : BitVec 64) (b35 : UInt8) (hb : HcontByteRoute (cont35 b35))
    (cA : BitVec 32) (hix : ix.toNat = 1) (hv : v.toNat = 2) (hcA : cA.toNat = 7) :
    stage2ReadWord (evbSeamCallsMem C s x inc nep ep v ix b35 hb cA)
        C.stage.tok 8 = some 1 ∧
      stage2ReadWord (evbSeamCallsMem C s x inc nep ep v ix b35 hb cA)
        (C.stage.tok + 8) 8 = some 2 ∧
      stage2ReadWord (evbSeamCallsMem C s x inc nep ep v ix b35 hb cA)
        (C.stage.tok + 16) 4 = some 7 :=
  ⟨evbSeam_pos C s x inc nep ep v ix b35 hb cA hix,
    evbSeam_end C s x inc nep ep v ix b35 hb cA hv,
    evbSeam_kind C s x inc nep ep v ix b35 hb cA hcA⟩

/-! ### Axiom footprints -/

#print axioms evbSeamCallsMem_seam
#print axioms evbSeam_pos
#print axioms evbSeam_end
#print axioms evbSeam_kind
#print axioms evbSeam_token_words

end WalkScope
end LeanLLVM.Refinement
