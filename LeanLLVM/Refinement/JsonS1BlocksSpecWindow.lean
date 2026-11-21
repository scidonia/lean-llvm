/-
The peel's DFA word at the specification's window.

`JsonS1BlocksPeelWindows` reads the peel's six offset windows from the document's
padded last block and states `%or.i` as `klErrBlk` over
`(peelWindow bs shr).take 3` and `((peelWindow bs shr).drop 3).take 64`.  The
specification's window is the unpadded `0x00 :: 0x00 :: 0x00 :: bs`, whose
`klBlk` at the last block is the document's bytes and may be shorter than sixty-
four.  The two words agree because `klErrBlk` reads past either end through
`klByte`, whose past-the-end byte is `0x00`, exactly the padding `padded` adds.

The identity is stated first over the peel's window (`klErrBlk_peelWindow_eq_spec`)
and then composed twice: with `ifThen144_orI_eq_peelWindow`, so `%or.i` is
`klErrBlk` at the specification's window, and with `peel_orI_eq_docBlock`, so the
same word is stated at the six memory reads the emitted body performs.  The last
block is the document's last block padded to sixty-four bytes; at a partial block
the padding is what the equality consumes.

What remains outside this module is not a read and not a byte identity: the
loop's carried word must still satisfy `packLanes u8k = bytesToNat acc`, its own
accumulator invariant.
-/
import LeanLLVM.Refinement.JsonS1BlocksPeelWindows

namespace LeanLLVM.Refinement.JsonS1BlocksSpecWindow

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1BlocksExit
open LeanLLVM.Refinement.JsonS1BlocksTail
open LeanLLVM.Refinement.JsonS1BlocksWordIdentities
open LeanLLVM.Refinement.JsonS1BlocksPeelWindows
open LeanLLVM.Refinement.JsonEntrySteps
open LeanLLVM.Refinement.JsonS1MasksSteps
open LeanLLVM.Refinement.JsonUtf8Spec
open LeanLLVM.Refinement.JsonUtf8Steps
open LeanLLVM.Refinement.JsonUtf8IR (utf8Window)

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### The padded document as the unit's staged window

The UTF-8 unit's window at the document's own length is three zero bytes, the
document, and zero padding to the block count — the same list as the specifi-
cation's `0x00 :: 0x00 :: 0x00 :: padded bs`.  `klErrBlk_window` moves between
that window and the unpadded one; this spelling lets the peel's window use it.
-/

/-- The unit's staged window at the document's length is the specification's
padded window. -/
theorem utf8Window_doc (bs : List UInt8) :
    utf8Window bs bs.length (blocksOf bs.length)
      = 0x00 :: 0x00 :: 0x00 :: padded bs := by
  simp [utf8Window, padded]

/-! ### The peel's window's two arguments

`peelWindow`'s first three bytes and its block argument, read as the
specification's `klPre`/`klBlk` at the same block index of the padded window.
The block argument is the padded block; the prefix is the previous block's tail,
or the staged zeroes at the first block.
-/

/-- The peel window's three carry bytes are the specification's `klPre` at the
padded window. -/
theorem peelWindow_take3 (bs : List UInt8) {shr : Nat}
    (hshr : shr < blocksOf bs.length) :
    (peelWindow bs shr).take 3
      = klPre (0x00 :: 0x00 :: 0x00 :: padded bs) shr := by
  by_cases h0 : shr = 0
  · subst h0
    rw [peelWindow_zero]
    unfold klPre
    rfl
  · rw [peelWindow_succ h0]
    have hprev : (docBlock bs (shr - 1)).length = 64 :=
      docBlock_length bs (by omega)
    have htake : ((docBlock bs (shr - 1)).drop 61 ++ docBlock bs shr).take 3
        = (docBlock bs (shr - 1)).drop 61 := by
      rw [List.take_append]
      have h3 : ((docBlock bs (shr - 1)).drop 61).length = 3 := by
        rw [List.length_drop, hprev]
      rw [h3, List.take_of_length_le (by omega), Nat.sub_self, List.take_zero,
        List.append_nil]
    rw [htake]
    unfold klPre
    have hshr1 : 1 ≤ shr := Nat.one_le_iff_ne_zero.mpr h0
    have hd : (0x00 :: 0x00 :: 0x00 :: padded bs).drop (64 * shr)
        = (padded bs).drop (64 * shr - 3) := by
      rw [show (0x00 :: 0x00 :: 0x00 :: padded bs)
          = [0x00, 0x00, 0x00] ++ padded bs from rfl, List.drop_append]
      rw [List.drop_eq_nil_of_le (by
          show ([0x00, 0x00, 0x00] : List UInt8).length ≤ 64 * shr
          simp only [List.length_cons, List.length_nil]
          omega), List.nil_append,
        show ([0x00, 0x00, 0x00] : List UInt8).length = 3 from rfl]
    unfold docBlock
    rw [drop_take', List.drop_drop, show 64 - 61 = 3 from by decide,
      show 64 * (shr - 1) + 61 = 64 * shr - 3 from by omega, hd]

/-- The peel window's block argument is the specification's `klBlk` at the
padded window. -/
theorem peelWindow_block (bs : List UInt8) {shr : Nat}
    (hshr : shr < blocksOf bs.length) :
    ((peelWindow bs shr).drop 3).take 64
      = klBlk (0x00 :: 0x00 :: 0x00 :: padded bs) shr := by
  rw [peelWindow_drop3 hshr,
    List.take_of_length_le (by rw [docBlock_length bs hshr]; decide)]
  have hd : (0x00 :: 0x00 :: 0x00 :: padded bs).drop (64 * shr + 3)
      = (padded bs).drop (64 * shr) := by
    rw [show (0x00 :: 0x00 :: 0x00 :: padded bs)
        = [0x00, 0x00, 0x00] ++ padded bs from rfl, List.drop_append]
    rw [List.drop_eq_nil_of_le (by
        show ([0x00, 0x00, 0x00] : List UInt8).length ≤ 64 * shr + 3
        simp only [List.length_cons, List.length_nil]
        omega), List.nil_append,
      show ([0x00, 0x00, 0x00] : List UInt8).length = 3 from rfl,
      show 64 * shr + 3 - 3 = 64 * shr from by omega]
  unfold klBlk docBlock
  rw [hd]

/-! ### The zero-fill identity

The peel's block is the document's last block padded to sixty-four bytes; the
specification's is the document's own bytes at the same block, shorter when the
block is partial.  `klErrBlk` reads through `klByte`, whose past-the-end byte is
zero, so the padding changes nothing.  `klErrBlk_window` states exactly that for
the whole staged window; with `peelWindow` read as the padded window's slices,
the two arguments are the same bytes. -/

/-- **`klErrBlk` over the zero-padded window is the specification's over the
unpadded one.**  The left window pads each block to sixty-four bytes with zeroes
(`padded`); the right is the document itself, so `klBlk` is short at a partial
last block.  `klErrBlk` reads through `klByte`, whose past-the-end byte is zero,
so the padding is invisible. -/
theorem klErrBlk_padded_eq_spec (bs : List UInt8) (shr : Nat) :
    klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: padded bs) shr)
        (klBlk (0x00 :: 0x00 :: 0x00 :: padded bs) shr)
      = klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) shr)
          (klBlk (0x00 :: 0x00 :: 0x00 :: bs) shr) := by
  rw [← utf8Window_doc bs]
  exact klErrBlk_window bs bs.length (blocksOf bs.length) shr

/-- The same identity at the document's last block. -/
theorem klErrBlk_padded_eq_spec_last (bs : List UInt8) {shr : Nat}
    (hsucc : shr + 1 = blocksOf bs.length) :
    klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: padded bs) shr)
        (klBlk (0x00 :: 0x00 :: 0x00 :: padded bs) shr)
      = klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) shr)
          (klBlk (0x00 :: 0x00 :: 0x00 :: bs) shr) :=
  klErrBlk_padded_eq_spec bs shr

/-- **`klErrBlk` over the peel's padded window is the specification's over the
unpadded document.** -/
theorem klErrBlk_peelWindow_eq_spec (bs : List UInt8) {shr : Nat}
    (hshr : shr < blocksOf bs.length) :
    klErrBlk ((peelWindow bs shr).take 3) (((peelWindow bs shr).drop 3).take 64)
      = klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) shr)
          (klBlk (0x00 :: 0x00 :: 0x00 :: bs) shr) := by
  rw [peelWindow_take3 bs hshr, peelWindow_block bs hshr, ← utf8Window_doc bs]
  exact klErrBlk_window bs bs.length (blocksOf bs.length) shr

/-- **The identity at the document's last block.**  The peel's slot is the last
whole block, `shr + 1 = blocksOf bs.length`; at a partial block the padding is
what the equality consumes. -/
theorem klErrBlk_peelWindow_eq_spec_last (bs : List UInt8) {shr : Nat}
    (hsucc : shr + 1 = blocksOf bs.length) :
    klErrBlk ((peelWindow bs shr).take 3) (((peelWindow bs shr).drop 3).take 64)
      = klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) shr)
          (klBlk (0x00 :: 0x00 :: 0x00 :: bs) shr) :=
  klErrBlk_peelWindow_eq_spec bs (by omega)

/-! ### The peel's DFA word at the specification's window

`ifThen144_orI_eq_peelWindow` states `%or.i` as `klErrBlk` over the peel's
window; the identity above rewrites that argument to the specification's
window.  `peel_orI_eq_specWindow` states the same at the six memory reads the
emitted body performs, composing `peel_orI_eq_docBlock`.
-/

/-- **The peel's `%or.i` at the specification's window.** -/
theorem ifThen144_orI_eq_specWindow (bs : List UInt8) {shr : Nat}
    (hshr : shr < blocksOf bs.length)
    (a : Nat) (lo103 lo161 : List (BitVec 8)) (u8k : List (BitVec 64))
    (bs136 bs137 : List UInt8) (acc : List UInt8)
    (h136 : bs136 = ((peelWindow bs shr).drop 3).take 32)
    (h137 : bs137 = (((peelWindow bs shr).drop 32).drop 3).take 32)
    (h103 : lo103 = hiNibbleLanes (bytesToNat bs136))
    (h161 : lo161 = hiNibbleLanes (bytesToNat bs137))
    (hacc32 : acc.length = 32) (hu8k : u8k.length = 4)
    (hacc : packLanes u8k = bytesToNat acc) :
    (ifThen144Values a lo103 lo161 u8k
        (((peelWindow bs shr).drop 2).take 32)
        (((peelWindow bs shr).drop 1).take 32)
        ((peelWindow bs shr).take 32)
        ((((peelWindow bs shr).drop 32).drop 2).take 32)
        ((((peelWindow bs shr).drop 32).drop 1).take 32)
        (((peelWindow bs shr).drop 32).take 32)).orI
      = unpackLanes 64 4 (bytesToNat (List.zipWith (· ||| ·) acc
          (klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) shr)
            (klBlk (0x00 :: 0x00 :: 0x00 :: bs) shr)))) := by
  rw [ifThen144_orI_eq_peelWindow bs hshr a lo103 lo161 u8k bs136 bs137 acc
      h136 h137 h103 h161 hacc32 hu8k hacc,
    klErrBlk_peelWindow_eq_spec bs hshr]

/-- **The peel's `%or.i` at the document's last block.**  The specification's
window at `shr + 1 = blocksOf bs.length`. -/
theorem ifThen144_orI_eq_specLast (bs : List UInt8) {shr : Nat}
    (hsucc : shr + 1 = blocksOf bs.length)
    (a : Nat) (lo103 lo161 : List (BitVec 8)) (u8k : List (BitVec 64))
    (bs136 bs137 : List UInt8) (acc : List UInt8)
    (h136 : bs136 = ((peelWindow bs shr).drop 3).take 32)
    (h137 : bs137 = (((peelWindow bs shr).drop 32).drop 3).take 32)
    (h103 : lo103 = hiNibbleLanes (bytesToNat bs136))
    (h161 : lo161 = hiNibbleLanes (bytesToNat bs137))
    (hacc32 : acc.length = 32) (hu8k : u8k.length = 4)
    (hacc : packLanes u8k = bytesToNat acc) :
    (ifThen144Values a lo103 lo161 u8k
        (((peelWindow bs shr).drop 2).take 32)
        (((peelWindow bs shr).drop 1).take 32)
        ((peelWindow bs shr).take 32)
        ((((peelWindow bs shr).drop 32).drop 2).take 32)
        ((((peelWindow bs shr).drop 32).drop 1).take 32)
        (((peelWindow bs shr).drop 32).take 32)).orI
      = unpackLanes 64 4 (bytesToNat (List.zipWith (· ||| ·) acc
          (klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) shr)
            (klBlk (0x00 :: 0x00 :: 0x00 :: bs) shr)))) :=
  ifThen144_orI_eq_specWindow bs (by omega) a lo103 lo161 u8k bs136 bs137 acc
    h136 h137 h103 h161 hacc32 hu8k hacc

/-- **The peel's DFA word, at the document's reads and the specification's
window.**  From the six memory reads, the classifier's two controls and the
block's halves, `%or.i` is the accumulator or-ed with the specification's
`klErrBlk` at the last block. -/
theorem peel_orI_eq_specWindow (mem : Mem) (bs : List UInt8) (b shr : Nat)
    (hb3 : 3 ≤ b) (hshr : shr < blocksOf bs.length)
    (hzero : readBytes mem (b - 3) 3 = some [0, 0, 0])
    (hdoc : readBytes mem b (64 * blocksOf bs.length) = some (padded bs))
    (a : Nat) (ha : a = b + 64 * shr)
    (lo103 lo161 : List (BitVec 8)) (u8k : List (BitVec 64))
    (bs171 bs172 bs173 bs183 bs184 bs185 bs136 bs137 : List UInt8)
    (w171 : readBytes mem (a - 1) 32 = some bs171)
    (w172 : readBytes mem (a - 2) 32 = some bs172)
    (w173 : readBytes mem (a - 3) 32 = some bs173)
    (w183 : readBytes mem (a + 31) 32 = some bs183)
    (w184 : readBytes mem (a + 30) 32 = some bs184)
    (w185 : readBytes mem (a + 29) 32 = some bs185)
    (h136 : bs136 = (docBlock bs shr).take 32)
    (h137 : bs137 = (docBlock bs shr).drop 32)
    (h103 : lo103 = hiNibbleLanes (bytesToNat bs136))
    (h161 : lo161 = hiNibbleLanes (bytesToNat bs137))
    (acc : List UInt8) (hacc32 : acc.length = 32) (hu8k : u8k.length = 4)
    (hacc : packLanes u8k = bytesToNat acc) :
    (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).orI
      = unpackLanes 64 4 (bytesToNat (List.zipWith (· ||| ·) acc
          (klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) shr)
            (klBlk (0x00 :: 0x00 :: 0x00 :: bs) shr)))) := by
  rw [peel_orI_eq_docBlock mem bs b shr hb3 hshr hzero hdoc a ha lo103 lo161 u8k
      bs171 bs172 bs173 bs183 bs184 bs185 bs136 bs137 w171 w172 w173 w183 w184 w185
      h136 h137 h103 h161 acc hacc32 hu8k hacc,
    klErrBlk_peelWindow_eq_spec bs hshr]

/-- **The peel's DFA word at the document's last block, from its reads.** -/
theorem peel_orI_eq_specLast (mem : Mem) (bs : List UInt8) (b shr : Nat)
    (hb3 : 3 ≤ b) (hsucc : shr + 1 = blocksOf bs.length)
    (hzero : readBytes mem (b - 3) 3 = some [0, 0, 0])
    (hdoc : readBytes mem b (64 * blocksOf bs.length) = some (padded bs))
    (a : Nat) (ha : a = b + 64 * shr)
    (lo103 lo161 : List (BitVec 8)) (u8k : List (BitVec 64))
    (bs171 bs172 bs173 bs183 bs184 bs185 bs136 bs137 : List UInt8)
    (w171 : readBytes mem (a - 1) 32 = some bs171)
    (w172 : readBytes mem (a - 2) 32 = some bs172)
    (w173 : readBytes mem (a - 3) 32 = some bs173)
    (w183 : readBytes mem (a + 31) 32 = some bs183)
    (w184 : readBytes mem (a + 30) 32 = some bs184)
    (w185 : readBytes mem (a + 29) 32 = some bs185)
    (h136 : bs136 = (docBlock bs shr).take 32)
    (h137 : bs137 = (docBlock bs shr).drop 32)
    (h103 : lo103 = hiNibbleLanes (bytesToNat bs136))
    (h161 : lo161 = hiNibbleLanes (bytesToNat bs137))
    (acc : List UInt8) (hacc32 : acc.length = 32) (hu8k : u8k.length = 4)
    (hacc : packLanes u8k = bytesToNat acc) :
    (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).orI
      = unpackLanes 64 4 (bytesToNat (List.zipWith (· ||| ·) acc
          (klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) shr)
            (klBlk (0x00 :: 0x00 :: 0x00 :: bs) shr)))) :=
  peel_orI_eq_specWindow mem bs b shr hb3 (by omega) hzero hdoc a ha lo103 lo161
    u8k bs171 bs172 bs173 bs183 bs184 bs185 bs136 bs137 w171 w172 w173 w183 w184
    w185 h136 h137 h103 h161 acc hacc32 hu8k hacc

/-! ### Axiom footprints

The identity is `klErrBlk_window`'s and list arithmetic at the window's slices;
the DFA compositions are `ifThen144_orI_eq_peelWindow`/
`peel_orI_eq_docBlock`'s.  No statement carries `sorryAx`. -/

#print axioms LeanLLVM.Refinement.JsonS1BlocksSpecWindow.utf8Window_doc
#print axioms LeanLLVM.Refinement.JsonS1BlocksSpecWindow.peelWindow_take3
#print axioms LeanLLVM.Refinement.JsonS1BlocksSpecWindow.peelWindow_block
#print axioms LeanLLVM.Refinement.JsonS1BlocksSpecWindow.klErrBlk_padded_eq_spec
#print axioms LeanLLVM.Refinement.JsonS1BlocksSpecWindow.klErrBlk_padded_eq_spec_last
#print axioms LeanLLVM.Refinement.JsonS1BlocksSpecWindow.klErrBlk_peelWindow_eq_spec
#print axioms LeanLLVM.Refinement.JsonS1BlocksSpecWindow.klErrBlk_peelWindow_eq_spec_last
#print axioms LeanLLVM.Refinement.JsonS1BlocksSpecWindow.ifThen144_orI_eq_specWindow
#print axioms LeanLLVM.Refinement.JsonS1BlocksSpecWindow.ifThen144_orI_eq_specLast
#print axioms LeanLLVM.Refinement.JsonS1BlocksSpecWindow.peel_orI_eq_specWindow
#print axioms LeanLLVM.Refinement.JsonS1BlocksSpecWindow.peel_orI_eq_specLast

end LeanLLVM.Refinement.JsonS1BlocksSpecWindow
