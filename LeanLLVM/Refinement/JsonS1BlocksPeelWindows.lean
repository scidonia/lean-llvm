/-
The peel's six DFA offset windows, at the document.

`JsonS1BlocksPeelWord` ties the peeled block's entry word `%or135` to the
document's last block; the DFA arm at `if.then144` still reads six thirty-two-byte
windows around the peel's pointer `a = b + 64 * shr`: one, two and three bytes
below `a`, and thirty-one, thirty and twenty-nine bytes above it
(`%171`…`%173` and `%183`…`%185`).  This module reads all six from the document.

The block index is the peel's slot, the last whole block, so the three below
windows are the previous block's last bytes joined to the block's head, and
above, each is an interior window of the block.  At the document's first block
there is no previous block: the three windows are the caller's three staged zero
bytes joined to the block's head.  `peelWindow` is that sixty-seven-byte list —
the three carry bytes and the block — so `peelWindow.drop k |>.take 32` names
each window uniformly, and `peelWindow_reads` is the six reads.

`ifThen144_orI_eq_peelWindow` is then the peel's DFA word identity at the
document's own window: `%or.i` is `klErrBlk`'s word at `peelWindow.take 3` and
the block.  `peel_orI_eq_docBlock` composes the two, so the six reads and the
classifier's two halves (`if103_low152_eq_hiNibbleLanes` and its high-half twin)
are all the document's; the peel's pointer is `if103_addPtr106`'s
`b + 64 * (n >>> 6)`.

What remains outside this module is not a memory read.  The loop's accumulator
packing `packLanes u8k = bytesToNat acc` is its invariant's, and the last block
here is the document's zero-padded block while the specification's window
`klPre (0x00 :: 0x00 :: 0x00 :: bs)`/`klBlk` is the unpadded document; the two
agree because `klErrBlk` reads past either end as `klByte`'s zero, and that
zero-fill identity is the separate spec-facing step.  Every byte the peel reads
is accounted for above.
-/
import LeanLLVM.Refinement.JsonS1BlocksPeelWord
import LeanLLVM.Refinement.JsonS1BlocksExit

namespace LeanLLVM.Refinement.JsonS1BlocksPeelWindows

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1BlocksExit
open LeanLLVM.Refinement.JsonS1BlocksTail
open LeanLLVM.Refinement.JsonS1BlocksWordIdentities
open LeanLLVM.Refinement.JsonS1BlocksPeelWord
open LeanLLVM.Refinement.JsonEntrySteps
open LeanLLVM.Refinement.JsonS1MasksSteps
open LeanLLVM.Refinement.JsonUtf8Spec

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### The peel's pointer

`if.then103` aligns the length down (`%shl105 = %n &&& ~63`) and binds the
peel's slot's address as `%b` plus that word.  The mask is the whole-block base,
so the pointer is `b + 64 * shr` at the peel's index. -/

/-- `%n &&& ~63` at the peel's register is the block base. -/
theorem addptr106_eq (n : BitVec 64) (b : Nat) :
    b + ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat
      = b + 64 * (n >>> 6).toNat := by
  rw [signExtend_self_toNat, and_high_mask_toNat, ← ushr_six_toNat]

/-- The peel's `%add.ptr106` at its own `let` chain. -/
theorem if103_addPtr106 (n : BitVec 64) (b : Nat) (bs136 bs137 : List UInt8)
    (ascii : List (BitVec 64)) (st0 st9 st15 prevS andv shr : BitVec 64)
    (ent : Nat) (conv prevAscii : BitVec 32) :
    (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
      prevAscii).addPtr106 = b + 64 * (n >>> 6).toNat := by
  rw [show (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent
      conv prevAscii).addPtr106
      = b + ((n &&& 0xffffffffffffffc0#64).signExtend 64).toNat from rfl]
  exact addptr106_eq n b

/-! ### The block window

`peelWindow bs shr` is the three bytes before block `shr` — the previous block's
tail, or the caller's staged zeroes at the first block — followed by the block's
sixty-four bytes from the padded document. -/

/-- The three carry bytes before the peel's block, then the block. -/
def peelWindow (bs : List UInt8) (shr : Nat) : List UInt8 :=
  (if shr = 0 then [0x00, 0x00, 0x00] else (docBlock bs (shr - 1)).drop 61)
    ++ docBlock bs shr

/-- A document block has sixty-four bytes at a live index. -/
theorem docBlock_length (bs : List UInt8) {j : Nat} (hj : j < blocksOf bs.length) :
    (docBlock bs j).length = 64 := by
  unfold docBlock
  rw [List.length_take, List.length_drop, padded_length]
  have := Nat.mul_le_mul_left 64 (Nat.le_of_lt hj)
  omega

/-- At the first block the window is the three staged zeroes and the block. -/
theorem peelWindow_zero (bs : List UInt8) :
    peelWindow bs 0 = [0x00, 0x00, 0x00] ++ docBlock bs 0 := by
  unfold peelWindow
  simp

/-- Past the first block the window is the previous block's tail and the block. -/
theorem peelWindow_succ {bs : List UInt8} {shr : Nat} (h : shr ≠ 0) :
    peelWindow bs shr = (docBlock bs (shr - 1)).drop 61 ++ docBlock bs shr := by
  unfold peelWindow
  simp [h]

/-- The window has sixty-seven bytes. -/
theorem peelWindow_length {bs : List UInt8} {shr : Nat}
    (hshr : shr < blocksOf bs.length) : (peelWindow bs shr).length = 67 := by
  by_cases h0 : shr = 0
  · subst h0
    rw [peelWindow_zero, List.length_append, List.length_cons, List.length_cons,
      List.length_cons, List.length_nil, docBlock_length bs (by omega)]
  · rw [peelWindow_succ h0, List.length_append, List.length_drop,
      docBlock_length bs (by omega), docBlock_length bs hshr]

/-- The window splits into its three carry bytes and the block. -/
theorem peelWindow_split {bs : List UInt8} {shr : Nat}
    (hshr : shr < blocksOf bs.length) :
    peelWindow bs shr = (peelWindow bs shr).take 3
      ++ ((peelWindow bs shr).drop 3).take 64 := by
  have h67 : (peelWindow bs shr).length = 67 := peelWindow_length hshr
  have hlen : ((peelWindow bs shr).drop 3).length = 64 := by
    rw [List.length_drop, h67]
  calc peelWindow bs shr
      = (peelWindow bs shr).take 3 ++ (peelWindow bs shr).drop 3 :=
        (List.take_append_drop 3 (peelWindow bs shr)).symm
    _ = (peelWindow bs shr).take 3
        ++ ((peelWindow bs shr).drop 3).take 64 := by
        rw [List.take_of_length_le (l := (peelWindow bs shr).drop 3) (i := 64)
          (by rw [hlen]; decide)]

/-! ### The prefix arithmetic

The two window shapes — the staged zeroes and a previous block's tail — reduced
to the bytes the block's loads read. -/

theorem cons_drop3 (L : List UInt8) :
    (([0x00, 0x00, 0x00] : List UInt8) ++ L).drop 3 = L := by
  simp only [List.drop_append, List.length_cons]
  rw [show (3 - ([].length + 1 + 1 + 1) : Nat) = 0 from by decide]
  rfl

theorem cons_drop2 (L : List UInt8) :
    (([0x00, 0x00, 0x00] : List UInt8) ++ L).drop 2 = [0x00] ++ L := by
  simp only [List.drop_append, List.length_cons]
  rw [show (2 - ([].length + 1 + 1 + 1) : Nat) = 0 from by decide]
  rfl

theorem cons_drop1 (L : List UInt8) :
    (([0x00, 0x00, 0x00] : List UInt8) ++ L).drop 1 = [0x00, 0x00] ++ L := by
  simp only [List.drop_append, List.length_cons]
  rw [show (1 - ([].length + 1 + 1 + 1) : Nat) = 0 from by decide]
  rfl

theorem cons_drop32 (L : List UInt8) :
    (([0x00, 0x00, 0x00] : List UInt8) ++ L).drop 32 = L.drop 29 := by
  simp only [List.drop_append, List.length_cons]
  rw [show (32 - ([].length + 1 + 1 + 1) : Nat) = 29 from by decide]
  rfl

theorem cons_take32 (L : List UInt8) :
    (([0x00, 0x00, 0x00] : List UInt8) ++ L).take 32
      = [0x00, 0x00, 0x00] ++ L.take 29 := by
  simp only [List.take_append, List.length_cons]
  rw [show (32 - ([].length + 1 + 1 + 1) : Nat) = 29 from by decide]
  rfl

theorem cons_drop2_take32 (L : List UInt8) :
    ((([0x00, 0x00, 0x00] : List UInt8) ++ L).drop 2).take 32
      = [0x00] ++ L.take 31 := by
  rw [cons_drop2]
  simp only [List.take_append, List.length_cons]
  rw [show (32 - ([].length + 1) : Nat) = 31 from by decide]
  rfl

theorem cons_drop1_take32 (L : List UInt8) :
    ((([0x00, 0x00, 0x00] : List UInt8) ++ L).drop 1).take 32
      = [0x00, 0x00] ++ L.take 30 := by
  rw [cons_drop1]
  simp only [List.take_append, List.length_cons]
  rw [show (32 - ([].length + 1 + 1) : Nat) = 30 from by decide]
  rfl

theorem cons_drop32_drop1_take32 (L : List UInt8) :
    (((([0x00, 0x00, 0x00] : List UInt8) ++ L).drop 32).drop 1).take 32
      = (L.drop 30).take 32 := by
  rw [cons_drop32, List.drop_drop, show (29 : Nat) + 1 = 30 from by decide]

theorem cons_drop32_drop2_take32 (L : List UInt8) :
    (((([0x00, 0x00, 0x00] : List UInt8) ++ L).drop 32).drop 2).take 32
      = (L.drop 31).take 32 := by
  rw [cons_drop32, List.drop_drop, show (29 : Nat) + 2 = 31 from by decide]

theorem cons_drop32_drop3_take32 (L : List UInt8) (hL : L.length = 64) :
    (((([0x00, 0x00, 0x00] : List UInt8) ++ L).drop 32).drop 3).take 32
      = L.drop 32 := by
  rw [cons_drop32, List.drop_drop, show (29 : Nat) + 3 = 32 from by decide,
    List.take_of_length_le (l := L.drop 32) (i := 32) (by
      rw [List.length_drop, hL]; decide)]

theorem carry_drop3 (P L : List UInt8) (hP : P.length = 64) :
    (P.drop 61 ++ L).drop 3 = L := by
  simp only [List.drop_append, List.length_drop, hP]
  rw [List.drop_drop, show (61 + 3 : Nat) = 64 from by decide,
    List.drop_eq_nil_of_le (by rw [hP]; decide),
    show (3 - (64 - 61) : Nat) = 0 from by decide, List.drop_zero, List.nil_append]

theorem carry_drop2 (P L : List UInt8) (hP : P.length = 64) :
    (P.drop 61 ++ L).drop 2 = P.drop 63 ++ L := by
  simp only [List.drop_append, List.length_drop, hP]
  rw [List.drop_drop, show (61 + 2 : Nat) = 63 from by decide,
    show (2 - (64 - 61) : Nat) = 0 from by decide, List.drop_zero]

theorem carry_drop1 (P L : List UInt8) (hP : P.length = 64) :
    (P.drop 61 ++ L).drop 1 = P.drop 62 ++ L := by
  simp only [List.drop_append, List.length_drop, hP]
  rw [List.drop_drop, show (61 + 1 : Nat) = 62 from by decide,
    show (1 - (64 - 61) : Nat) = 0 from by decide, List.drop_zero]

theorem carry_drop32 (P L : List UInt8) (hP : P.length = 64) :
    (P.drop 61 ++ L).drop 32 = L.drop 29 := by
  simp only [List.drop_append, List.length_drop, hP]
  rw [List.drop_drop, show (32 - (64 - 61) : Nat) = 29 from by decide,
    List.drop_eq_nil_of_le (by rw [hP]; decide), List.nil_append]

theorem carry_take32 (P L : List UInt8) (hP : P.length = 64) :
    (P.drop 61 ++ L).take 32 = P.drop 61 ++ L.take 29 := by
  simp only [List.take_append, List.length_drop, hP]
  have hlen : (P.drop 61).length = 3 := by rw [List.length_drop, hP]
  rw [show (32 - (64 - 61) : Nat) = 29 from by decide,
    List.take_of_length_le (by rw [hlen]; decide)]

theorem carry_drop2_take32 (P L : List UInt8) (hP : P.length = 64) :
    ((P.drop 61 ++ L).drop 2).take 32 = P.drop 63 ++ L.take 31 := by
  rw [carry_drop2 P L hP]
  have hlen : (P.drop 63).length = 1 := by rw [List.length_drop, hP]
  simp only [List.take_append, List.length_drop, hP]
  rw [show (32 - (64 - 63) : Nat) = 31 from by decide,
    List.take_of_length_le (by rw [hlen]; decide)]

theorem carry_drop1_take32 (P L : List UInt8) (hP : P.length = 64) :
    ((P.drop 61 ++ L).drop 1).take 32 = P.drop 62 ++ L.take 30 := by
  rw [carry_drop1 P L hP]
  have hlen : (P.drop 62).length = 2 := by rw [List.length_drop, hP]
  simp only [List.take_append, List.length_drop, hP]
  rw [show (32 - (64 - 62) : Nat) = 30 from by decide,
    List.take_of_length_le (by rw [hlen]; decide)]

theorem carry_drop32_drop1_take32 (P L : List UInt8) (hP : P.length = 64) :
    (((P.drop 61 ++ L).drop 32).drop 1).take 32 = (L.drop 30).take 32 := by
  rw [carry_drop32 P L hP, List.drop_drop, show (29 : Nat) + 1 = 30 from by decide]

theorem carry_drop32_drop2_take32 (P L : List UInt8) (hP : P.length = 64) :
    (((P.drop 61 ++ L).drop 32).drop 2).take 32 = (L.drop 31).take 32 := by
  rw [carry_drop32 P L hP, List.drop_drop, show (29 : Nat) + 2 = 31 from by decide]

theorem carry_drop32_drop3_take32 (P L : List UInt8) (hP : P.length = 64)
    (hL : L.length = 64) :
    (((P.drop 61 ++ L).drop 32).drop 3).take 32 = L.drop 32 := by
  rw [carry_drop32 P L hP, List.drop_drop, show (29 : Nat) + 3 = 32 from by decide,
    List.take_of_length_le (l := L.drop 32) (i := 32) (by
      rw [List.length_drop, hL]; decide)]

/-- The window's three carry bytes are dropped before the block. -/
theorem peelWindow_drop3 {bs : List UInt8} {shr : Nat}
    (hshr : shr < blocksOf bs.length) :
    (peelWindow bs shr).drop 3 = docBlock bs shr := by
  by_cases h0 : shr = 0
  · subst h0
    rw [peelWindow_zero, cons_drop3]
  · rw [peelWindow_succ h0, carry_drop3 _ _ (docBlock_length bs (by omega))]

/-- The window thirty-two bytes in is the block's twenty-ninth byte on. -/
theorem peelWindow_drop32 {bs : List UInt8} {shr : Nat}
    (hshr : shr < blocksOf bs.length) :
    (peelWindow bs shr).drop 32 = (docBlock bs shr).drop 29 := by
  by_cases h0 : shr = 0
  · subst h0
    rw [peelWindow_zero, cons_drop32]
  · rw [peelWindow_succ h0, carry_drop32 _ _ (docBlock_length bs (by omega))]

/-- The window's high half is the block's. -/
theorem peelWindow_block_hi {bs : List UInt8} {shr : Nat}
    (hshr : shr < blocksOf bs.length) :
    (((peelWindow bs shr).drop 32).drop 3).take 32 = (docBlock bs shr).drop 32 := by
  rw [peelWindow_drop32 hshr, List.drop_drop,
    show (29 : Nat) + 3 = 32 from by decide,
    List.take_of_length_le (l := (docBlock bs shr).drop 32) (i := 32) (by
      rw [List.length_drop, docBlock_length bs hshr]; decide)]


/-! ### The six reads, from the document

At the first block the three below windows are the staged zeroes plus the block's
head; past it they are the previous block's tail plus the block's head.  The
three above windows are interior windows of the block. -/

/-- **The six DFA windows, at the document.**  Every below window is a slice of
`peelWindow` taken below its first byte, every above window a slice taken inside
the block. -/
theorem peelWindow_reads (mem : Mem) (bs : List UInt8) (b shr : Nat)
    (hb3 : 3 ≤ b) (hshr : shr < blocksOf bs.length)
    (hzero : readBytes mem (b - 3) 3 = some [0, 0, 0])
    (hdoc : readBytes mem b (64 * blocksOf bs.length) = some (padded bs)) :
    readBytes mem (b + 64 * shr - 1) 32
        = some (((peelWindow bs shr).drop 2).take 32) ∧
      readBytes mem (b + 64 * shr - 2) 32
        = some (((peelWindow bs shr).drop 1).take 32) ∧
      readBytes mem (b + 64 * shr - 3) 32
        = some ((peelWindow bs shr).take 32) ∧
      readBytes mem (b + 64 * shr + 31) 32
        = some ((((peelWindow bs shr).drop 32).drop 2).take 32) ∧
      readBytes mem (b + 64 * shr + 30) 32
        = some ((((peelWindow bs shr).drop 32).drop 1).take 32) ∧
      readBytes mem (b + 64 * shr + 29) 32
        = some (((peelWindow bs shr).drop 32).take 32) := by
  by_cases h0 : shr = 0
  · subst h0
    simp only [Nat.mul_zero, Nat.add_zero]
    rw [peelWindow_zero]
    have hblk : readBytes mem b 64 = some (docBlock bs 0) := by
      simpa using readBytes_docBlock mem bs b hdoc (j := 0) (by omega)
    have h1 : readBytes mem (b - 1) 1 = some [0] := by
      have h := (readBytes_split mem (b - 3) 2 1 (by
        rw [show 2 + 1 = 3 from by omega]; exact hzero)).2
      rw [show b - 3 + 2 = b - 1 from by omega] at h
      simpa using h
    have h2 : readBytes mem (b - 2) 2 = some [0, 0] := by
      have h := (readBytes_split mem (b - 3) 1 2 (by
        rw [show 1 + 2 = 3 from by omega]; exact hzero)).2
      rw [show b - 3 + 1 = b - 2 from by omega] at h
      simpa using h
    have hb31 : readBytes mem b 31 = some ((docBlock bs 0).take 31) := by
      have h := readBytes_docBlock_inside (addr := b) hblk (k := 0) (n := 31) (by omega)
      simpa using h
    have hb30 : readBytes mem b 30 = some ((docBlock bs 0).take 30) := by
      have h := readBytes_docBlock_inside (addr := b) hblk (k := 0) (n := 30) (by omega)
      simpa using h
    have hb29 : readBytes mem b 29 = some ((docBlock bs 0).take 29) := by
      have h := readBytes_docBlock_inside (addr := b) hblk (k := 0) (n := 29) (by omega)
      simpa using h
    have r171 : readBytes mem (b - 1) 32
        = some ([0] ++ (docBlock bs 0).take 31) := by
      have h := readBytes_append mem 1 (b - 1) [0] 31 ((docBlock bs 0).take 31) h1 (by
        rw [show b - 1 + 1 = b from by omega]; exact hb31)
      simpa using h
    have r172 : readBytes mem (b - 2) 32
        = some ([0, 0] ++ (docBlock bs 0).take 30) := by
      have h := readBytes_append mem 2 (b - 2) [0, 0] 30 ((docBlock bs 0).take 30) h2 (by
        rw [show b - 2 + 2 = b from by omega]; exact hb30)
      simpa using h
    have r173 : readBytes mem (b - 3) 32
        = some ([0, 0, 0] ++ (docBlock bs 0).take 29) := by
      have h := readBytes_append mem 3 (b - 3) [0, 0, 0] 29 ((docBlock bs 0).take 29)
        hzero (by rw [show b - 3 + 3 = b from by omega]; exact hb29)
      simpa using h
    have r183 : readBytes mem (b + 31) 32
        = some (((docBlock bs 0).drop 31).take 32) :=
      readBytes_docBlock_inside (addr := b) hblk (k := 31) (n := 32) (by omega)
    have r184 : readBytes mem (b + 30) 32
        = some (((docBlock bs 0).drop 30).take 32) :=
      readBytes_docBlock_inside (addr := b) hblk (k := 30) (n := 32) (by omega)
    have r185 : readBytes mem (b + 29) 32
        = some (((docBlock bs 0).drop 29).take 32) :=
      readBytes_docBlock_inside (addr := b) hblk (k := 29) (n := 32) (by omega)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [cons_drop2_take32]; exact r171
    · rw [cons_drop1_take32]; exact r172
    · rw [cons_take32]; exact r173
    · rw [cons_drop32_drop2_take32]; exact r183
    · rw [cons_drop32_drop1_take32]; exact r184
    · rw [cons_drop32]; exact r185
  · have hP : (docBlock bs (shr - 1)).length = 64 :=
      docBlock_length bs (by omega)
    have hL : (docBlock bs shr).length = 64 := docBlock_length bs hshr
    rw [peelWindow_succ h0]
    have hblk : readBytes mem (b + 64 * shr) 64 = some (docBlock bs shr) :=
      readBytes_docBlock mem bs b hdoc (j := shr) hshr
    have hprev : readBytes mem (b + 64 * (shr - 1)) 64
        = some (docBlock bs (shr - 1)) :=
      readBytes_docBlock mem bs b hdoc (j := shr - 1) (by omega)
    have haddr : b + 64 * shr - 64 = b + 64 * (shr - 1) := by omega
    have r171 : readBytes mem (b + 64 * shr - 1) 32
        = some ((docBlock bs (shr - 1)).drop 63
            ++ (docBlock bs shr).take 31) :=
      readBytes_docBlock_carry (m := mem) (addr := b + 64 * shr)
        (prev := docBlock bs (shr - 1)) (blk := docBlock bs shr) (d := 1)
        (by omega) (by rw [haddr]; exact hprev) hblk (by omega) (by omega)
    have r172 : readBytes mem (b + 64 * shr - 2) 32
        = some ((docBlock bs (shr - 1)).drop 62
            ++ (docBlock bs shr).take 30) :=
      readBytes_docBlock_carry (m := mem) (addr := b + 64 * shr)
        (prev := docBlock bs (shr - 1)) (blk := docBlock bs shr) (d := 2)
        (by omega) (by rw [haddr]; exact hprev) hblk (by omega) (by omega)
    have r173 : readBytes mem (b + 64 * shr - 3) 32
        = some ((docBlock bs (shr - 1)).drop 61
            ++ (docBlock bs shr).take 29) :=
      readBytes_docBlock_carry (m := mem) (addr := b + 64 * shr)
        (prev := docBlock bs (shr - 1)) (blk := docBlock bs shr) (d := 3)
        (by omega) (by rw [haddr]; exact hprev) hblk (by omega) (by omega)
    have r183 : readBytes mem (b + 64 * shr + 31) 32
        = some (((docBlock bs shr).drop 31).take 32) :=
      readBytes_docBlock_inside (addr := b + 64 * shr) hblk (k := 31) (n := 32)
        (by omega)
    have r184 : readBytes mem (b + 64 * shr + 30) 32
        = some (((docBlock bs shr).drop 30).take 32) :=
      readBytes_docBlock_inside (addr := b + 64 * shr) hblk (k := 30) (n := 32)
        (by omega)
    have r185 : readBytes mem (b + 64 * shr + 29) 32
        = some (((docBlock bs shr).drop 29).take 32) :=
      readBytes_docBlock_inside (addr := b + 64 * shr) hblk (k := 29) (n := 32)
        (by omega)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [carry_drop2_take32 _ _ hP]; exact r171
    · rw [carry_drop1_take32 _ _ hP]; exact r172
    · rw [carry_take32 _ _ hP]; exact r173
    · rw [carry_drop32_drop2_take32 _ _ hP]; exact r183
    · rw [carry_drop32_drop1_take32 _ _ hP]; exact r184
    · rw [carry_drop32 _ _ hP]; exact r185



/-! ### The classifier's two controls

`if.then144`'s third table reads `%152` and `%161`, the two low-nibble controls
`if.then103` left.  They are the high nibbles of the block's two halves, which is
`ifThen144_orI_eq`'s `h103`/`h161` at the peel's own registers. -/

/-- `%152` is the block's low half's high nibbles. -/
theorem if103_low152_eq_hiNibbleLanes (bs136 : List UInt8) (h136 : bs136.length = 32)
    (n : BitVec 64) (b : Nat) (bs137 : List UInt8) (ascii : List (BitVec 64))
    (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat) (conv prevAscii : BitVec 32) :
    (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
      prevAscii).low152 = hiNibbleLanes (bytesToNat bs136) := by
  rw [if103_low152, if103_byte151, if103_shr148, if103_half147]
  exact byteView_highNibble' bs136 h136

/-- `%161` is the block's high half's high nibbles. -/
theorem if103_low161_eq_hiNibbleLanes (bs137 : List UInt8) (h137 : bs137.length = 32)
    (n : BitVec 64) (b : Nat) (bs136 : List UInt8) (ascii : List (BitVec 64))
    (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat) (conv prevAscii : BitVec 32) :
    (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
      prevAscii).low161 = hiNibbleLanes (bytesToNat bs137) := by
  rw [if103_low161, if103_byte160, if103_shr157, if103_half156]
  exact byteView_highNibble' bs137 h137

/-! ### The DFA word at the document's window

`ifThen144_orI_eq` reads the six windows as drops of one sixty-seven-byte list.
`peelWindow` is exactly that list, so the word identity is an instantiation; the
composition with `peelWindow_reads` then states it at the block's own reads. -/

/-- **The peel's DFA word is `klErrBlk`'s, at the window.**  The six windows are
`peelWindow`'s slices, the classifier's two halves are the window's block, and
the accumulator is the one the loop carries. -/
theorem ifThen144_orI_eq_peelWindow (bs : List UInt8) {shr : Nat}
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
          (klErrBlk ((peelWindow bs shr).take 3)
            (((peelWindow bs shr).drop 3).take 64)))) := by
  have h67 : 67 ≤ (peelWindow bs shr).length := by
    rw [peelWindow_length hshr]; decide
  have hpre3 : ((peelWindow bs shr).take 3).length = 3 := by
    rw [List.length_take]; omega
  have hblk64 : (((peelWindow bs shr).drop 3).take 64).length = 64 := by
    rw [List.length_take, List.length_drop]; omega
  exact ifThen144_orI_eq a lo103 lo161 u8k
    (((peelWindow bs shr).drop 2).take 32)
    (((peelWindow bs shr).drop 1).take 32)
    ((peelWindow bs shr).take 32)
    ((((peelWindow bs shr).drop 32).drop 2).take 32)
    ((((peelWindow bs shr).drop 32).drop 1).take 32)
    (((peelWindow bs shr).drop 32).take 32)
    bs136 bs137 acc ((peelWindow bs shr).take 3)
    (((peelWindow bs shr).drop 3).take 64) (peelWindow bs shr)
    rfl rfl rfl rfl rfl rfl h136 h137 h103 h161
    (peelWindow_split hshr) h67 hacc32 hpre3 hblk64 hu8k hacc

/-- **The peel's DFA word at the document's last block.**  From the caller's
padded window and three staged zeroes, the six window reads and the block's two
halves, the peel's `%or.i` is the accumulator or-ed with `klErrBlk` over the
block's window.  The only remaining premise is the loop's accumulator packing. -/
theorem peel_orI_eq_docBlock (mem : Mem) (bs : List UInt8) (b shr : Nat)
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
          (klErrBlk ((peelWindow bs shr).take 3)
            (((peelWindow bs shr).drop 3).take 64)))) := by
  subst a
  obtain ⟨r171, r172, r173, r183, r184, r185⟩ :=
    peelWindow_reads mem bs b shr hb3 hshr hzero hdoc
  have e171 : bs171 = (((peelWindow bs shr).drop 2).take 32) :=
    Option.some.inj (w171.symm.trans r171)
  have e172 : bs172 = (((peelWindow bs shr).drop 1).take 32) :=
    Option.some.inj (w172.symm.trans r172)
  have e173 : bs173 = ((peelWindow bs shr).take 32) :=
    Option.some.inj (w173.symm.trans r173)
  have e183 : bs183 = ((((peelWindow bs shr).drop 32).drop 2).take 32) :=
    Option.some.inj (w183.symm.trans r183)
  have e184 : bs184 = ((((peelWindow bs shr).drop 32).drop 1).take 32) :=
    Option.some.inj (w184.symm.trans r184)
  have e185 : bs185 = (((peelWindow bs shr).drop 32).take 32) :=
    Option.some.inj (w185.symm.trans r185)
  have e136 : bs136 = ((peelWindow bs shr).drop 3).take 32 := by
    rw [h136, ← peelWindow_drop3 hshr]
  have e137 : bs137 = (((peelWindow bs shr).drop 32).drop 3).take 32 := by
    rw [h137, ← peelWindow_block_hi hshr]
  rw [e171, e172, e173, e183, e184, e185]
  exact ifThen144_orI_eq_peelWindow bs hshr (b + 64 * shr) lo103 lo161 u8k
    bs136 bs137 acc e136 e137 h103 h161 hacc32 hu8k hacc


/-! ### Remaining

The accumulator's packing (`packLanes u8k = bytesToNat acc`) is the loop's
invariant, supplied as `hacc`; it is not a read.  The specification's window is
the unpadded `0x00 :: 0x00 :: 0x00 :: bs`; its `klBlk` at the last partial block
is shorter than the padded block here, and `klErrBlk`'s `klByte` zero fill is
what makes the two words agree.  That list identity, not a memory read, is the
spec-facing remainder. -/

/-! ### Axiom footprints

The reads are `readBytes_split`/`readBytes_append`/`readBytes_docBlock_carry` /
`readBytes_docBlock_inside` and list arithmetic; the word identity is
`ifThen144_orI_eq`'s.  No statement carries `sorryAx`. -/

#print axioms LeanLLVM.Refinement.JsonS1BlocksPeelWindows.addptr106_eq
#print axioms LeanLLVM.Refinement.JsonS1BlocksPeelWindows.peelWindow_split
#print axioms LeanLLVM.Refinement.JsonS1BlocksPeelWindows.peelWindow_drop3
#print axioms LeanLLVM.Refinement.JsonS1BlocksPeelWindows.peelWindow_drop32
#print axioms LeanLLVM.Refinement.JsonS1BlocksPeelWindows.peelWindow_block_hi
#print axioms LeanLLVM.Refinement.JsonS1BlocksPeelWindows.if103_low152_eq_hiNibbleLanes
#print axioms LeanLLVM.Refinement.JsonS1BlocksPeelWindows.if103_low161_eq_hiNibbleLanes
#print axioms LeanLLVM.Refinement.JsonS1BlocksPeelWindows.peelWindow_reads
#print axioms LeanLLVM.Refinement.JsonS1BlocksPeelWindows.ifThen144_orI_eq_peelWindow
#print axioms LeanLLVM.Refinement.JsonS1BlocksPeelWindows.peel_orI_eq_docBlock

end LeanLLVM.Refinement.JsonS1BlocksPeelWindows
