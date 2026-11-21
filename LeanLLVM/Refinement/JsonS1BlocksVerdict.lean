/-
The block unit's return word, read against the contract's verdict clause.

`s1BlocksPost` states three things about the word the run returns: no higher bit
is set (`r &&& 3 = r`), bit 0 is the ASCII probe (`1` exactly when every
document byte is below `0x80`), and bit 1 is the UTF-8 stage's error bit (`0`
exactly when the staged window is a valid prefix).  `JsonS1BlocksRefine` traces
the body to `if.end170`, where the two phis select the ASCII word and the error
bit and the join `%or176` is the return; `JsonUtf8Fused` states the stage at a
host loop's own word.  This module joins the two: it reads `verdictWord`'s bits,
proves the ASCII probe against the word's bytes, proves the error bit against
`utf8WinPrefix` at the block unit's window with the fused verdict's lemmas, and
states which part of the result comes from the caller's staging and which from
the emitted body's trace.

## What is proved

* `verdictWord_and_three` — the return word has no bit above the two.
* `verdictWord_and_one` / `VerdictStaging.bit0` — bit 0 is the ASCII probe, and
  it is set exactly when every byte of the word's thirty-two-byte view is below
  `0x80` (`asciiProbe_eq_one_iff_asciiBytes`).
* `verdictWord_and_two` / `VerdictStaging.bit1` — bit 1 is the error bit, and it
  is clear exactly on `utf8WinPrefix (utf8Window bs bs.length (blocksOf bs.length))`.
* `if_end170_step_verdict` — the traced return, together with the staging, gives
  the post's verdict conjuncts at the returned word.

## The split between the staging and the trace

`VerdictStaging` is the caller's and the loop's part: the ASCII word's high bits
are the document's (`ascii_bytes`), the accumulator's packed word is `klAll`
(`acc_pack`), and the phi's error bit is `%cmp155` or `%or169500`'s `¬ u8k = 0`
or the last byte's `kl_tail_byte` (`err_def`).  The emitted body's part is
`if_end170_step`'s own premises: the block's pc and predecessor (`hpc`, `hpre`)
and the two phi selections (`hinc1`/`hop1`, `hinc2`/`hop2`).  Neither side
implies the other; the record instance is what supplies the staging, and
`JsonS1BlocksRefine`'s trace is what supplies the step.

## What remains for the record instance

The staging's three fields are the loop refinement's obligation, and they are
stated at the loop's own registers rather than derived here: `ascii_bytes` from
`%ascii.1.lcssa`'s lane-wise OR of each block's two halves, `acc_pack` from the
fused accumulator invariant (`packLanes u8k = bytesToNat (klAcc bs i)`, which
`JsonUtf8Fused.fusedRun_word_eq_klAll` carries to `klAll`), and `err_def` from
`%cmp155`'s `ptestz u8k u8k` and `if.then164`'s load of `b[n-1]` and its
`%204` byte test.  `ptestzU8k_icmp_eq_zero` states the first arm's reading, and
`or169500_one_iff` the second's — the two together are `err_def` at the block's
own byte.
-/
import LeanLLVM.Refinement.JsonS1BlocksRefine
import LeanLLVM.Refinement.JsonS1BlocksSteps
import LeanLLVM.Refinement.JsonUtf8Fused

namespace LeanLLVM.Refinement.JsonS1BlocksVerdict

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.BitLanes
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonUtf8Fused
open LeanLLVM.Refinement.JsonUtf8IR (utf8Window utf8WinPrefix le_mul_div_sixtyfour)
open LeanLLVM.Refinement.JsonUtf8Spec
open LeanLLVM.Refinement.JsonUtf8Steps

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ### The word's byte view

The probe tests the packed lanes against a mask, and the post's ASCII clause is
about the document's bytes.  The bridge is the word's own byte view, which is
`natToBytes` at the packing: its `bytesToNat` is the packing back, so the byte
list is the one the vector holds rather than a second encoding. -/

/-- The thirty-two bytes a word denotes, little-endian. -/
def asciiBytes (w : List (BitVec 64)) : List UInt8 := natToBytes (packLanes w) 32

theorem asciiBytes_length (w : List (BitVec 64)) : (asciiBytes w).length = 32 :=
  natToBytes_length _ _

/-- A four-lane word's byte view packs back to the word. -/
theorem bytesToNat_asciiBytes (w : List (BitVec 64)) (hw : w.length = 4) :
    bytesToNat (asciiBytes w) = packLanes w := by
  unfold asciiBytes
  rw [natToBytes_toNat]
  have hlt := packLanes_lt w
  rw [hw, show (4 * 64) = 256 from rfl] at hlt
  exact Nat.mod_eq_of_lt hlt

/-! ### The probe's mask and its two answers -/

/-- The probe's mask lanes are the high bit of every byte. -/
theorem highMaskLanes_eq : highMaskLanes = highLanes64 := by
  have h : (0x8080808080808080#64 : BitVec 64)
      = BitVec.ofInt 64 (-9187201950435737472) := by decide
  unfold highMaskLanes highLanes64
  rw [h]

/-- The mask's packed word is `0x80` in every byte. -/
theorem packLanes_highMaskLanes :
    packLanes highMaskLanes = bytesToNat (List.replicate 32 (0x80 : UInt8)) := by
  rw [highMaskLanes_eq]
  exact packLanes_highLanes64

theorem highMaskLanes_length : highMaskLanes.length = 4 := rfl

/-- A byte is below `0x80` exactly when its high bit is clear. -/
theorem u8_and_80_eq_zero_iff (b : UInt8) : b &&& 0x80 = 0 ↔ b.toNat < 0x80 := by
  have hall : ∀ i : Fin 256,
      (UInt8.ofNat i.val &&& 0x80 = 0) ↔ (UInt8.ofNat i.val).toNat < 0x80 := by
    decide
  have h := hall ⟨b.toNat, b.toNat_lt⟩
  rwa [UInt8.ofNat_toNat] at h

/-- The lane-wise `&&&` with the high-bit byte is zero exactly at an all-ASCII
byte list. -/
theorem zipWith_and_high_all_zero_iff (l : List UInt8) :
    (∀ x ∈ List.zipWith (· &&& ·) l
        (List.replicate l.length (0x80 : UInt8)), x = 0) ↔
      ∀ b ∈ l, b.toNat < 0x80 := by
  induction l with
  | nil => simp
  | cons b bs ih =>
      rw [List.length_cons, List.replicate_succ, List.zipWith_cons_cons]
      constructor
      · intro h x hx
        simp only [List.mem_cons] at hx
        rcases hx with hxb | hx
        · rw [hxb]
          exact (u8_and_80_eq_zero_iff b).mp (h (b &&& 0x80) (by simp))
        · exact ih.mp (fun y hy => h y (by simp [hy])) x hx
      · intro h y hy
        simp only [List.mem_cons] at hy
        rcases hy with hyb | hy
        · rw [hyb]
          exact (u8_and_80_eq_zero_iff b).mpr (h b (by simp))
        · exact ih.mpr (fun z hz => h z (by simp [hz])) y hy

/-- `ptestz` answers one of the ABI's two words. -/
theorem asciiProbe_eq_zero_or_one (w : List (BitVec 64)) :
    asciiProbe w = 0 ∨ asciiProbe w = 1 := by
  by_cases h : (BitVec.ofNat 256 (packLanes w)) &&&
      (BitVec.ofNat 256 (packLanes highMaskLanes)) = 0
  · right
    unfold asciiProbe ptestz
    rw [if_pos h]
  · left
    unfold asciiProbe ptestz
    rw [if_neg h]

/-- **The probe at the word's bytes**: `1` exactly when every byte of the word's
thirty-two-byte view is below `0x80`. -/
theorem asciiProbe_eq_one_iff_asciiBytes (w : List (BitVec 64)) (hw : w.length = 4) :
    asciiProbe w = 1 ↔ ∀ b ∈ asciiBytes w, b.toNat < 0x80 := by
  have hult : packLanes w < 2 ^ 256 := by
    have h := packLanes_lt w
    rw [hw, show (4 * 64) = 256 from rfl] at h
    exact h
  have hMlt : packLanes highMaskLanes < 2 ^ 256 := by
    have h := packLanes_lt highMaskLanes
    rw [highMaskLanes_length, show (4 * 64) = 256 from rfl] at h
    exact h
  have hand : ((BitVec.ofNat 256 (packLanes w)) &&&
        (BitVec.ofNat 256 (packLanes highMaskLanes))).toNat
      = packLanes w &&& packLanes highMaskLanes := by
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hult, Nat.mod_eq_of_lt hMlt]
  have hiff : ((BitVec.ofNat 256 (packLanes w)) &&&
        (BitVec.ofNat 256 (packLanes highMaskLanes)) = 0)
      ↔ packLanes w &&& packLanes highMaskLanes = 0 := by
    constructor
    · intro hz
      have hz' := congrArg BitVec.toNat hz
      rw [hand] at hz'
      simpa using hz'
    · intro hz
      apply BitVec.eq_of_toNat_eq
      rw [hand]
      simpa using hz
  unfold asciiProbe
  rw [ptestz_eq_one_iff, hiff, packLanes_highMaskLanes,
    ← bytesToNat_asciiBytes w hw,
    ← bytesToNat_zipWith_and (asciiBytes w) (List.replicate 32 (0x80 : UInt8))
      (by rw [asciiBytes_length, List.length_replicate]),
    bytesToNat_eq_zero_iff]
  rw [← asciiBytes_length w]
  exact zipWith_and_high_all_zero_iff (asciiBytes w)

/-! ### The return word's bits

`verdictWord` is the join of the shifted error bit and the zero-extended ASCII
probe.  The two summands are `{0, 2}` and `{0, 1}`, so the join has no bit above
the two, bit 0 is the probe and bit 1 is the error bit. -/

theorem evalICmp_ne_zero_one_iff (p : BitVec 32) :
    evalICmp .ne p (0 : BitVec 32) = 1 ↔ p ≠ 0 := by
  unfold evalICmp
  exact ofBool_eq_one_iff

theorem ofNat64_icmp_ne_zero (p : BitVec 32) :
    BitVec.ofNat 64 (evalICmp .ne p (0 : BitVec 32)).toNat
      = if p = 0 then (0 : BitVec 64) else 1 := by
  by_cases hp : p = 0
  · rw [hp]
    decide
  · rw [(evalICmp_ne_zero_one_iff p).mpr hp, if_neg hp]
    decide

/-- The return word is the join of the two bits. -/
theorem verdictWord_eq_join (ascii : List (BitVec 64)) (err : BitVec 1) :
    verdictWord ascii err
      = (if err = 1 then (2 : BitVec 64) else 0) |||
        (if asciiProbe ascii = 0 then (0 : BitVec 64) else 1) := by
  unfold verdictWord
  rw [ofNat64_icmp_ne_zero]

theorem verdictWord_two_or_zero (err : BitVec 1) :
    (if err = 1 then (2 : BitVec 64) else 0) = 0 ∨
      (if err = 1 then (2 : BitVec 64) else 0) = 2 := by
  by_cases he : err = 1
  · right; rw [if_pos he]
  · left; rw [if_neg he]

theorem asciiBit_zero_or_one (w : List (BitVec 64)) :
    (if asciiProbe w = 0 then (0 : BitVec 64) else 1) = 0 ∨
      (if asciiProbe w = 0 then (0 : BitVec 64) else 1) = 1 := by
  by_cases hp : asciiProbe w = 0
  · left; rw [if_pos hp]
  · right; rw [if_neg hp]

theorem or_two_bit_and_one (a b : BitVec 64) (ha : a = 0 ∨ a = 2)
    (hb : b = 0 ∨ b = 1) : (a ||| b) &&& 1 = b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem or_two_bit_and_two (a b : BitVec 64) (ha : a = 0 ∨ a = 2)
    (hb : b = 0 ∨ b = 1) : (a ||| b) &&& 2 = a := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem or_two_bit_and_three (a b : BitVec 64) (ha : a = 0 ∨ a = 2)
    (hb : b = 0 ∨ b = 1) : (a ||| b) &&& 3 = a ||| b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

/-- **No higher bit is set**: the return word is its own value below `4`. -/
theorem verdictWord_and_three (ascii : List (BitVec 64)) (err : BitVec 1) :
    verdictWord ascii err &&& 3 = verdictWord ascii err := by
  rw [verdictWord_eq_join]
  exact or_two_bit_and_three _ _ (verdictWord_two_or_zero err)
    (asciiBit_zero_or_one ascii)

/-- Bit 0 is the ASCII probe. -/
theorem verdictWord_and_one (ascii : List (BitVec 64)) (err : BitVec 1) :
    verdictWord ascii err &&& 1 = (if asciiProbe ascii = 0 then 0 else 1) := by
  rw [verdictWord_eq_join]
  exact or_two_bit_and_one _ _ (verdictWord_two_or_zero err)
    (asciiBit_zero_or_one ascii)

/-- Bit 1 is the error bit. -/
theorem verdictWord_and_two (ascii : List (BitVec 64)) (err : BitVec 1) :
    verdictWord ascii err &&& 2 = (if err = 1 then 2 else 0) := by
  rw [verdictWord_eq_join]
  exact or_two_bit_and_two _ _ (verdictWord_two_or_zero err)
    (asciiBit_zero_or_one ascii)

theorem verdictWord_and_one_eq_one (ascii : List (BitVec 64)) (err : BitVec 1) :
    verdictWord ascii err &&& 1 = 1 ↔ asciiProbe ascii ≠ 0 := by
  rw [verdictWord_and_one]
  by_cases hp : asciiProbe ascii = 0 <;> simp [hp]

theorem verdictWord_and_two_eq_zero (ascii : List (BitVec 64)) (err : BitVec 1) :
    verdictWord ascii err &&& 2 = 0 ↔ err ≠ 1 := by
  rw [verdictWord_and_two]
  by_cases he : err = 1 <;> simp [he]

/-! ### The accumulator's zero test at the trace's own arm

`if.end153` and `if.end153.thread` both bind `%cmp155` as
`icmp eq (ptestz u8k u8k) 0`; `ptestz` answers one exactly on a cleared word, so
the bit is set exactly on a non-zero accumulator.  That is the `%cmp155` half of
the error bit; `if.then164` ors the last byte's own test into it. -/

/-- `ptestz u8k u8k` is zero exactly at a non-zero accumulator. -/
theorem ptestzU8k_zero_iff (u8k : List (BitVec 64)) (hu : u8k.length = 4) :
    ptestzU8k u8k = 0 ↔ ¬ (u8k.all (fun x => decide (x = 0x00)) = true) := by
  have hult : packLanes u8k < 2 ^ 256 := by
    have h := packLanes_lt u8k
    rw [hu, show (4 * 64) = 256 from rfl] at h
    exact h
  have hofNat : BitVec.ofNat 256 (packLanes u8k) = 0 ↔ packLanes u8k = 0 := by
    constructor
    · intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hult] at h'
      simpa using h'
    · intro h; simp [h]
  have hand : ptestzU8k u8k = 0 ↔
      ¬ (BitVec.ofNat 256 (packLanes u8k) = 0) := by
    unfold ptestzU8k
    rw [ptestz_eq_zero_iff, BitVec.and_self]
  rw [hand, hofNat, packLanes_eq_zero_iff_all]

theorem ptestzU8k_icmp_eq_zero (u8k : List (BitVec 64)) (hu : u8k.length = 4) :
    evalICmp .eq (ptestzU8k u8k) (0 : BitVec 32) = 1 ↔
      ¬ (u8k.all (fun x => decide (x = 0x00)) = true) := by
  have hbit : evalICmp .eq (ptestzU8k u8k) (0 : BitVec 32) = 1 ↔
      ptestzU8k u8k = 0 :=
    ofBool_eq_one_iff
  rw [hbit, ptestzU8k_zero_iff u8k hu]

/-- A one-bit value is zero or one. -/
theorem bit1_eq_zero_or_one (x : BitVec 1) : x = 0 ∨ x = 1 := by
  have h := x.isLt
  rcases Nat.lt_or_ge x.toNat 1 with h0 | h1
  · left
    apply BitVec.toNat_inj.mp
    rw [show (0 : BitVec 1).toNat = 0 from rfl]
    omega
  · right
    apply BitVec.toNat_inj.mp
    rw [show (1 : BitVec 1).toNat = 1 from rfl]
    omega

/-- A one-bit `or` is one exactly on one of its terms. -/
theorem bit1_or_eq_one (a b : BitVec 1) : a ||| b = 1 ↔ a = 1 ∨ b = 1 := by
  rcases bit1_eq_zero_or_one a with rfl | rfl <;>
    rcases bit1_eq_zero_or_one b with rfl | rfl <;> decide

/-- The `if.then164` arm's byte test is set exactly at a byte `kl_tail_byte`
rejects. -/
theorem utf8TailBit_one_iff (x : UInt8) :
    utf8TailBit x.toBitVec = 1 ↔ klTailByte x = true := by
  constructor
  · intro h1
    cases hb : klTailByte x with
    | false =>
        have h0 : utf8TailBit x.toBitVec = 0 := (utf8TailBit_zero_iff x).mpr hb
        rw [h1] at h0
        exact absurd h0 (by decide)
    | true => rfl
  · intro hb
    rcases bit1_eq_zero_or_one (utf8TailBit x.toBitVec) with h0 | h1
    · have hf := (utf8TailBit_zero_iff x).mp h0
      rw [hb] at hf
      exact absurd hf (by decide)
    · exact h1

/-- **The `if.then164` arm's `%or169500`**: the accumulator's zero test or the
last byte's tail test, in the staging's spelling.  This is the emitted block's
own value at its own byte `x`; the staging's `err_def` is this at
`x = klByte bs (n-1)` with the `n ≠ 0` guard the block's branch supplies. -/
theorem or169500_one_iff (u8k : List (BitVec 64)) (x : UInt8)
    (hu : u8k.length = 4) :
    (evalICmp .eq (ptestzU8k u8k) (0 : BitVec 32) ||| utf8TailBit x.toBitVec) = 1 ↔
      ¬ (u8k.all (fun y => decide (y = 0x00)) = true) ∨ klTailByte x = true := by
  rw [bit1_or_eq_one, ptestzU8k_icmp_eq_zero u8k hu, utf8TailBit_one_iff]

/-! ### The tail byte over padding

At a document that is not a whole number of blocks, the byte after the last
document byte is the zero padding.  A byte that can never begin a character
(`C0`, `C1`, `F5`..`FF`) is refused there — `klErrByte_eq_zero_iff`'s first
clause wants a continuation and its second wants `KlPair`, and neither holds —
so the accumulator is already non-zero and the body's unguarded tail test
changes nothing. -/

/-- A tail byte is never a continuation. -/
theorem not_isContByte_of_tailByte {c : UInt8} (h : klTailByte c = true) :
    ¬ IsContByte c := by
  have hge : 192 ≤ c.toNat := klTailByte_true_ge h
  intro hc
  have h1 := hc.1
  have h2 := hc.2
  rw [UInt8.le_iff_toNat_le] at h1
  rw [UInt8.le_iff_toNat_le] at h2
  have e1 : (0x80 : UInt8).toNat = 128 := by decide
  have e2 : (0xBF : UInt8).toNat = 191 := by decide
  rw [e1] at h1
  rw [e2] at h2
  omega

/-- A tail byte may not be followed by `0x00` in a locally admissible window. -/
theorem not_klPair_zero_of_tailByte {c : UInt8} (h : klTailByte c = true) :
    ¬ KlPair c 0x00 := by
  have hge : 192 ≤ c.toNat := klTailByte_true_ge h
  have hc0 : ¬ IsContByte (0x00 : UInt8) := by unfold IsContByte; decide
  have hA : ¬ ((0xA0 : UInt8) ≤ 0x00) := by decide
  have h90 : ¬ ((0x90 : UInt8) ≤ 0x00) := by decide
  have h80 : ¬ ((0x80 : UInt8) ≤ 0x00) := by decide
  have hce : ¬ IsCharEnd c := by
    unfold IsCharEnd IsContByte
    intro hc
    rcases hc with hc | ⟨h1, h2⟩
    · omega
    · rw [UInt8.le_iff_toNat_le] at h1
      rw [UInt8.le_iff_toNat_le] at h2
      have e1 : (0x80 : UInt8).toNat = 128 := by decide
      have e2 : (0xBF : UInt8).toNat = 191 := by decide
      rw [e1] at h1
      rw [e2] at h2
      omega
  intro hp
  rw [klPair_iff] at hp
  rcases hp with ⟨-, he⟩ | ⟨-, -, h0⟩ | ⟨-, h0, -⟩ | ⟨-, h0⟩ |
    ⟨-, h0, -⟩ | ⟨-, h0, -⟩ | ⟨-, -, h0⟩ | ⟨-, h0, -⟩
  · exact hce he
  · exact hc0 h0
  · exact hA h0
  · exact hc0 h0
  · exact h80 h0
  · exact h90 h0
  · exact hc0 h0
  · exact h80 h0

/-- **The unguarded tail test is redundant over padding.**  When the document
is not a whole number of blocks, the padding supplies the window after its last
byte, so the position the tables judge there is refused and the accumulator is
not clear. -/
theorem not_klErrAll_of_tail_padding (bs : List UInt8) (n nb : Nat)
    (hn : n = bs.length) (hnb : nb = (n + 63) / 64)
    (hn0 : n ≠ 0) (hmod : n % 64 ≠ 0)
    (htail : klTailByte (klByte bs (n - 1)) = true) :
    ¬ klErrAll (utf8Window bs n nb) (64 * nb) := by
  intro herr
  have hle : n ≤ 64 * nb := by
    rw [hnb]; exact JsonUtf8IR.le_mul_div_sixtyfour n
  have hne : n ≠ 64 * nb := by
    intro h
    apply hmod
    rw [h]
    exact Nat.mul_mod_right 64 nb
  have hlt : n < 64 * nb := by omega
  have hwin := herr n hlt
  have hc : klByte (utf8Window bs n nb) (n + 2) = klByte bs (n - 1) :=
    klByte_window_tail bs n nb (by omega)
  have hzero : klByte (utf8Window bs n nb) (n + 3) = 0x00 := by
    rw [klByte_window]
    have hpast : (0x00 :: 0x00 :: 0x00 :: bs)[n + 3]? = none :=
      List.getElem?_eq_none (by simp only [List.length_cons]; omega)
    simpa [klByte, List.getD_eq_getElem?_getD, hpast]
  unfold klErrWin at hwin
  rw [hc, hzero] at hwin
  rcases (klErrByte_eq_zero_iff _ _ _ _).mp hwin with ⟨_, hp1, _⟩ | ⟨_, hk⟩
  · exact not_isContByte_of_tailByte htail hp1
  · exact not_klPair_zero_of_tailByte htail hk

/-! ### The staging

The loop and the caller hand the return word three things; the emitted body's
`if.end170` hands it the phi selections, which are the trace's part. -/

/-- **The verdict's staging.**  The ASCII word's high bits are the document's
(the loop's `%ascii.1.lcssa` accumulates each block's two halves lane for lane),
the accumulator's packed word is `klAll` (the fused loop's invariant), and the
error bit is the emitted `%cmp155`/`%or169500` arm's reading: the accumulator is
not zero, or the last byte can never begin a character. -/
structure VerdictStaging (ascii u8k : List (BitVec 64)) (bs : List UInt8)
    (n nb : Nat) (gate : Bool) (err : BitVec 1) : Prop where
  ascii_len : ascii.length = 4
  acc_len : u8k.length = 4
  hn : n = bs.length
  hnb : nb = blocksOf bs.length
  ascii_bytes : (∀ b ∈ asciiBytes ascii, b.toNat < 0x80) ↔
    (∀ x ∈ bs, x.toNat < 0x80)
  acc_pack : packLanes u8k = bytesToNat (klAll gate bs)
  err_def : err = 1 ↔ ¬ (u8k.all (fun x => decide (x = 0x00)) = true) ∨
    (n ≠ 0 ∧ klTailByte (klByte bs (n - 1)) = true)

namespace VerdictStaging

variable {ascii u8k : List (BitVec 64)} {bs : List UInt8} {n nb : Nat}
  {gate : Bool} {err : BitVec 1}

/-- The staging's block count in the window's own spelling. -/
theorem hnb' (h : VerdictStaging ascii u8k bs n nb gate err) : nb = (n + 63) / 64 := by
  simpa [blocksOf, h.hn] using h.hnb

/-- **The accumulator is clear exactly when the window is error-free.** -/
theorem klErrAll_iff (h : VerdictStaging ascii u8k bs n nb gate err) :
    (u8k.all (fun x => decide (x = 0x00)) = true) ↔
      klErrAll (utf8Window bs n nb) (64 * nb) := by
  rw [← packLanes_eq_zero_iff_all u8k, h.acc_pack, bytesToNat_eq_zero_iff,
    ← all_eq_zero_iff]
  exact klAll_zero_iff_klErrAll bs n nb gate h.hn h.hnb'

/-- **The fused verdict at the accumulator is zero exactly on the unit's post.** -/
theorem fusedVerdict_zero_iff (h : VerdictStaging ascii u8k bs n nb gate err) :
    fusedVerdict (klAll gate bs) n (klByte bs (n - 1)) = 0 ↔
      utf8WinPrefix (utf8Window bs n nb) := by
  have hrun := fusedVerdict_zero_iff_unit_post bs n nb gate h.hn h.hnb'
  rwa [show (fusedRun (0x00 :: 0x00 :: 0x00 :: bs) gate nb FusedState.init).u8k
        = klAll gate bs from by
      rw [show nb = (bs.length + 63) / 64 from by simpa [blocksOf] using h.hnb]
      exact fusedRun_word_eq_klAll bs gate] at hrun

/-- The fused verdict is one exactly on an invalid prefix. -/
theorem fusedVerdict_one_iff (h : VerdictStaging ascii u8k bs n nb gate err) :
    fusedVerdict (klAll gate bs) n (klByte bs (n - 1)) = 1 ↔
      ¬ utf8WinPrefix (utf8Window bs n nb) := by
  constructor
  · intro h1 hv
    have h0 := h.fusedVerdict_zero_iff.mpr hv
    rw [h1] at h0
    exact absurd h0 (by decide)
  · intro hnv
    rcases fusedVerdict_eq_zero_or_one (klAll gate bs) n (klByte bs (n - 1)) with
      h0 | h1
    · exact absurd (h.fusedVerdict_zero_iff.mp h0) hnv
    · exact h1

/-- The window's verdict as the error predicate the tables state. -/
theorem valid_iff (h : VerdictStaging ascii u8k bs n nb gate err) :
    utf8WinPrefix (utf8Window bs n nb) ↔
      klErrAll (utf8Window bs n nb) (64 * nb) ∧
        ¬ (n ≠ 0 ∧ n % 64 = 0 ∧
          klTailByte (klByte bs (n - 1)) = true) := by
  unfold utf8WinPrefix utf8Window
  exact (klErrAll_window_iff bs n nb h.hn h.hnb').symm

/-- **The error bit is the fused verdict's bit.**  This is the trace's
`%or169500` read at the staging: the accumulator's zero test, or the last
byte's tail test.  The second disjunct needs no length guard in the body, and
it needs none here either: where the document is not a whole number of blocks,
the padding already carries the accumulator's error, which
`valid_iff`'s two sides record. -/
theorem err_iff_fusedVerdict (h : VerdictStaging ascii u8k bs n nb gate err) :
    err = 1 ↔ fusedVerdict (klAll gate bs) n (klByte bs (n - 1)) = 1 := by
  rw [h.err_def, h.fusedVerdict_one_iff, h.valid_iff]
  have hA := h.klErrAll_iff
  constructor
  · rintro (hna | ⟨hn0, htail⟩)
    · intro hc
      exact hna (hA.mpr hc.1)
    · intro hc
      rcases hc with ⟨herr, hnotM⟩
      by_cases hmod : n % 64 = 0
      · exact hnotM ⟨hn0, hmod, htail⟩
      · exact not_klErrAll_of_tail_padding bs n nb h.hn h.hnb' hn0 hmod htail herr
  · intro hnv
    by_cases hM : n ≠ 0 ∧ n % 64 = 0 ∧ klTailByte (klByte bs (n - 1)) = true
    · exact Or.inr ⟨hM.1, hM.2.2⟩
    · exact Or.inl (fun hAl => hnv ⟨hA.mp hAl, hM⟩)

end VerdictStaging

/-! ### The post's verdict clause

The three conjuncts `s1BlocksPost` states about the returned word, at the word
`if.end170` returns. -/

/-- `s1BlocksPost`'s three verdict conjuncts, at an arbitrary returned word. -/
def VerdictPost (r : BitVec 64) (bs : List UInt8) : Prop :=
  r &&& 3 = r ∧
    (r &&& 1 = 1 ↔ ∀ x ∈ bs, x.toNat < 0x80) ∧
    (r &&& 2 = 0 ↔ utf8WinPrefix (utf8Window bs bs.length (blocksOf bs.length)))

namespace VerdictStaging

variable {ascii u8k : List (BitVec 64)} {bs : List UInt8} {n nb : Nat}
  {gate : Bool} {err : BitVec 1}

/-- Bit 0 is the document's ASCII probe. -/
theorem bit0 (h : VerdictStaging ascii u8k bs n nb gate err) :
    verdictWord ascii err &&& 1 = 1 ↔ ∀ x ∈ bs, x.toNat < 0x80 := by
  rw [verdictWord_and_one_eq_one]
  constructor
  · intro hne
    have h1 : asciiProbe ascii = 1 := by
      rcases asciiProbe_eq_zero_or_one ascii with h0 | h1
      · exact absurd h0 hne
      · exact h1
    exact h.ascii_bytes.mp
      ((asciiProbe_eq_one_iff_asciiBytes ascii h.ascii_len).mp h1)
  · intro hbs hz
    have h1 : asciiProbe ascii = 1 :=
      (asciiProbe_eq_one_iff_asciiBytes ascii h.ascii_len).mpr
        (h.ascii_bytes.mpr hbs)
    rw [h1] at hz
    exact absurd hz (by decide)

/-- Bit 1 is clear exactly on the staged window's valid prefix. -/
theorem bit1 (h : VerdictStaging ascii u8k bs n nb gate err) :
    verdictWord ascii err &&& 2 = 0 ↔ utf8WinPrefix (utf8Window bs n nb) := by
  rw [verdictWord_and_two_eq_zero, ne_eq, h.err_iff_fusedVerdict]
  constructor
  · intro hne
    rcases fusedVerdict_eq_zero_or_one (klAll gate bs) n (klByte bs (n - 1)) with
      h0 | h1
    · exact h.fusedVerdict_zero_iff.mp h0
    · exact absurd h1 hne
  · intro hv h1
    have h0 := h.fusedVerdict_zero_iff.mpr hv
    rw [h1] at h0
    exact absurd h0 (by decide)

/-- **The post's verdict conjuncts, at the staging's word.** -/
theorem satisfies_post (h : VerdictStaging ascii u8k bs n nb gate err) :
    VerdictPost (verdictWord ascii err) bs := by
  refine ⟨verdictWord_and_three ascii err, h.bit0, ?_⟩
  simpa [h.hn, h.hnb] using h.bit1

end VerdictStaging

/-! ### The traced return

`if.end170`'s step is the trace's; the staging is the caller's.  The two
together give the post's verdict clause at the returned word. -/

/-- **The traced return satisfies the post's verdict clause.**  The premises are
the step's own (`hpc`, `hpre`, and the two phi selections), which are
`JsonS1BlocksRefine.if_end170_step`'s; the staging is
`VerdictStaging`'s, and no step fact implies it. -/
theorem if_end170_step_verdict
    (env : Env) (s : State) (p : String) (op1 op2 : Operand)
    (ascii u8k : List (BitVec 64)) (err : BitVec 1) (bs : List UInt8)
    (n nb : Nat) (gate : Bool)
    (hpc : s.pc = "if.end170")
    (hpre : s.pre = some p)
    (hinc1 : phiIncoming p [("if.then164", .reg "%ascii.1.lcssa"),
      ("if.end153", .reg "%ascii.1.lcssa"),
      ("if.end153.thread", .reg "%or.i279")] = some op1)
    (hop1 : evalOperand (stateAt env s) op1 = some (.vec 4 64 ascii))
    (hinc2 : phiIncoming p [("if.then164", .reg "%or169500"),
      ("if.end153", .reg "%cmp155"),
      ("if.end153.thread", .reg "%cmp155495")] = some op2)
    (hop2 : evalOperand (stateAt env s) op2 = some (.int 1 err))
    (hstage : VerdictStaging ascii u8k bs n nb gate err) :
    step s1BlocksCalls s1BlocksFunction (stateAt env s) =
        .ret (some (.int 64 (verdictWord ascii err)))
          (stateAt (ifEnd170Env env ascii err) s) ∧
      VerdictPost (verdictWord ascii err) bs :=
  ⟨if_end170_step env s p op1 op2 ascii err hpc hpre hinc1 hop1 hinc2 hop2,
    hstage.satisfies_post⟩

/-! ### The footprint

Every statement reads the emitted body's own definitions and the stage's; none
of them reaches a choice principle beyond the quotient and propositional
extensionality the library already carries. -/

#print axioms LeanLLVM.Refinement.JsonS1BlocksVerdict.asciiProbe_eq_one_iff_asciiBytes
#print axioms LeanLLVM.Refinement.JsonS1BlocksVerdict.verdictWord_and_three
#print axioms LeanLLVM.Refinement.JsonS1BlocksVerdict.verdictWord_and_one
#print axioms LeanLLVM.Refinement.JsonS1BlocksVerdict.verdictWord_and_two
#print axioms LeanLLVM.Refinement.JsonS1BlocksVerdict.ptestzU8k_zero_iff
#print axioms LeanLLVM.Refinement.JsonS1BlocksVerdict.ptestzU8k_icmp_eq_zero
#print axioms LeanLLVM.Refinement.JsonS1BlocksVerdict.utf8TailBit_one_iff
#print axioms LeanLLVM.Refinement.JsonS1BlocksVerdict.or169500_one_iff
#print axioms LeanLLVM.Refinement.JsonS1BlocksVerdict.VerdictStaging.klErrAll_iff
#print axioms LeanLLVM.Refinement.JsonS1BlocksVerdict.VerdictStaging.fusedVerdict_zero_iff
#print axioms LeanLLVM.Refinement.JsonS1BlocksVerdict.VerdictStaging.err_iff_fusedVerdict
#print axioms LeanLLVM.Refinement.JsonS1BlocksVerdict.not_klErrAll_of_tail_padding
#print axioms LeanLLVM.Refinement.JsonS1BlocksVerdict.VerdictStaging.bit0
#print axioms LeanLLVM.Refinement.JsonS1BlocksVerdict.VerdictStaging.bit1
#print axioms LeanLLVM.Refinement.JsonS1BlocksVerdict.VerdictStaging.satisfies_post
#print axioms LeanLLVM.Refinement.JsonS1BlocksVerdict.if_end170_step_verdict

end LeanLLVM.Refinement.JsonS1BlocksVerdict
