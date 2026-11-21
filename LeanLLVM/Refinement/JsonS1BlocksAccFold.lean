/-
The loop's accumulator fold, and the peel's last block.

`JsonS1BlocksWordIdentities.packLanes_or281_eq` states the DFA arm's step at the
loop's own accumulator invariant, `packLanes u8k = bytesToNat (klAcc bs i)`, and
`JsonS1BlocksLoopRun` hands that invariant to the exit as an obligation
(`loopExitFacts_at`'s `hu8k`).  This module states it as a carry beside the
loop's own, proves it preserved by the page shapes, and identifies the peel's
merged word with `klAll`.

## The invariant

`AccCarry bs c` is three facts at one loop head:

* `pack` — the carried word packs to the ungated window walk's accumulator at the
  loop's index, `packLanes u8k = bytesToNat (klAcc bs i)`;
* `len` — the word has four lanes;
* `carry` — the carried ASCII probe is either clear, or the three bytes before
  the row are all below `0x80`.  (`accCarry_init` proves it at block zero, where
  the carry bytes are the staged zeroes, whatever the preheader's probe was.)  This is the premise the merge arm needs: the
  loop drops a block's error vector there (`%u8k.2` is the body's `%u8k.1521`),
  and the drop is sound exactly because the probe says the block is ASCII and
  the carry says the block boundary is.  `klPre_succ` reads the carry at the
  next index as the block's own last three bytes, and the page's probe
  (`fb54Probe`, the verdict's `asciiProbe`) settles the block.

## The two arms' steps

* `packLanes_dfa_or281` — the DFA arm: `if.then90`'s `%or.i281` packs to
  `klErrBlk`'s word or-ed in, which is `klAcc`'s own step.  Its six windows are
  the peel window's slices, so `peelWindow_reads_of_block` reads them from the
  document and `PageDfaWindows` names them.
* `packLanes_merge_keep` — the merge arm: the block's error vector is zero
  (`utf8Skip_eq_zero`) when the probe and the carry are ASCII, so keeping the
  word is the fold's step.

`accLatch_dfa` and `accLatch_merge` are those steps at the page's own
hypotheses; `accLatch_dfa_escape`, `accLatch_dfa_skip`, `accLatch_merge_escape`
and `accLatch_merge_skip` are the four page shapes `JsonS1BlocksLoop`'s
`fused_dfa_escape_page`, `fused_dfa_skip_page`, `fused_merge_escape_page` and
`fused_merge_skip_page` reach, at their successor words and memories (the
accumulator's carry is memory-independent, so the escape and skip shapes share
it).

## The exit

The loop stops at `%shr = n >>> 6`, one block short of a partial document's
block count, and the peel at `if.then144` merges its own block's error vector
into the loop's word.  `peelWord_pack_klAll` reads the merged word as `klAll`'s:
the loop's invariant gives `acc = klAcc bs shr` (`bytesToNat`'s injectivity),
`klAll_eq_klAcc_succ` adds the last block, and `packLanes_unpackLanes` returns
the packed form.  `peelWord_eq_klAll_lanes` is the lane form `acc_pack_of_peel`
consumes, and `acc_pack_of_peelWord` is that lemma at the peel's word — the
record's `VerdictStaging.acc_pack` field on the peeled arm.  On the aligned arm
`acc_pack_of_alignedExit` is the same field from the invariant at the document's
block count, through `acc_pack_of_klAcc`.

## What remains

The thread through the run lives in `JsonS1BlocksAccRun`: `LoopInv` with
`AccCarry` beside it (`AccInv`), the model's carry and the accumulator's
advanced by one page per row (`loopRun_accCarry`), the terminal `AccTerm`, and
the exit's facts at it.  `accCarry_init` is that induction's base at the entry's
zero word and the four page shapes here are its page step; the exit's obligation
is discharged by `loopExitFacts_of_accCarry` from a terminal `AccCarry`, and the
aligned arm's `acc_pack` is `acc_pack_of_alignedExit` at the same terminal, the
peel's `acc_pack_of_peelWord`.

The run's inputs are its callers' staging facts: the page's `pre` at the call
vectors (the escape record's answer and its keeps, `JsonS1BlocksAccRun`'s
`hcallAll` and `hkeep`) and the entry's bounded prefix
(`JsonS1BlocksLoopRun.OnePrefix`'s fuel).  Neither is a fold identity.
-/
import LeanLLVM.Refinement.JsonS1BlocksSpecWindow
import LeanLLVM.Refinement.JsonS1BlocksWordIdentities
import LeanLLVM.Refinement.JsonS1BlocksLoopRun
import LeanLLVM.Refinement.JsonS1BlocksPeelStaging

namespace LeanLLVM.Refinement.JsonS1BlocksAccFold

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.BitLanes
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksExit
open LeanLLVM.Refinement.JsonS1BlocksTail
open LeanLLVM.Refinement.JsonS1BlocksStaging
open LeanLLVM.Refinement.JsonS1BlocksVerdict
open LeanLLVM.Refinement.JsonS1BlocksPeelStaging
open LeanLLVM.Refinement.JsonS1BlocksPeelWindows
open LeanLLVM.Refinement.JsonS1BlocksSpecWindow
open LeanLLVM.Refinement.JsonS1BlocksWordIdentities
open LeanLLVM.Refinement.JsonS1BlocksLoop
open LeanLLVM.Refinement.JsonS1BlocksLoopFacts
open LeanLLVM.Refinement.JsonS1BlocksRecordFrame
open LeanLLVM.Refinement.JsonS1BlocksLoopRun
open LeanLLVM.Refinement.JsonS1MasksSteps
open LeanLLVM.Refinement.JsonUtf8Steps
open LeanLLVM.Refinement.JsonUtf8Spec
open LeanLLVM.Refinement.JsonUtf8Fused
open LeanLLVM.Refinement.JsonEntrySteps

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### Lane-one facts

The page's two decisions are one-bit words; these are the readings the merge's
`select` and `v107` need. -/

/-- A one-bit conjunction is set exactly when both factors are. -/
theorem bv1_and_one_iff (a b : BitVec 1) :
    (a &&& b = (1 : BitVec 1)) ↔ a = 1 ∧ b = 1 := by
  constructor
  · intro h
    have h1 : (a &&& b).toNat = 1 := by rw [h]; rfl
    rw [BitVec.toNat_and] at h1
    have ha : a.toNat ≤ 1 := by have := a.isLt; omega
    have hb : b.toNat ≤ 1 := by have := b.isLt; omega
    have hle1 := Nat.and_le_left (n := a.toNat) (m := b.toNat)
    have hle2 := Nat.and_le_right (n := a.toNat) (m := b.toNat)
    refine ⟨BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_⟩
    · show a.toNat = 1; omega
    · show b.toNat = 1; omega
  · rintro ⟨rfl, rfl⟩
    decide

/-- The loop's gated select is set exactly at the gate and the arm's bit. -/
theorem fb54Select_eq_one {g x : BitVec 1} (h : fb54Select g x = 1) :
    g = 1 ∧ x = 1 := by
  by_cases hg : g = 1
  · rw [fb54Select, ite_eq_left hg] at h
    exact ⟨hg, h⟩
  · rw [fb54Select, ite_eq_right hg] at h
    exact absurd h (by decide)

/-! ### The block behind the page's probe

`for.body54` tests `%74 ||| %73` against the high-bit mask, and the verdict tests
the same word; `fb54Probe` is `asciiProbe` at the same mask lanes.  The word's
byte view is the block's half-OR, so the probe is the block's ASCII answer. -/

/-- The loop's fast-table probe is the verdict's. -/
theorem fb54Probe_eq_asciiProbe (a : List (BitVec 64)) :
    fb54Probe a = asciiProbe a := rfl

/-- **The page's two halves, or-ed, are the block's half-OR.**  The join's byte
view is `blockHalfOr` at the block: the half-words pack to the halves' values and
`bytesToNat` of the lane-wise OR is the byte-wise one. -/
theorem asciiBytes_fb54Or_halves {bs : List UInt8} {k : Nat} {bs73 bs74 : List UInt8}
    (hk : k < blocksOf bs.length)
    (h73 : bs73 = (docBlock bs k).take 32) (h74 : bs74 = (docBlock bs k).drop 32) :
    asciiBytes (fb54Or (unpackLanes 64 4 (bytesToNat bs74))
        (unpackLanes 64 4 (bytesToNat bs73))) = blockHalfOr bs k := by
  have hblen : (docBlock bs k).length = 64 := docBlock_length_of_lt bs hk
  have h73len : bs73.length = 32 := by
    rw [h73, List.length_take, hblen, Nat.min_eq_left (by decide)]
  have h74len : bs74.length = 32 := by
    rw [h74, List.length_drop, hblen]
  have hz : (docBlock bs k).take 32 = bs73 := h73.symm
  have hd : (docBlock bs k).drop 32 = bs74 := h74.symm
  unfold asciiBytes
  rw [show fb54Or (unpackLanes 64 4 (bytesToNat bs74))
        (unpackLanes 64 4 (bytesToNat bs73))
      = List.zipWith (· ||| ·) (unpackLanes 64 4 (bytesToNat bs74))
          (unpackLanes 64 4 (bytesToNat bs73)) from rfl,
    packLanes_peelBlock (bs136 := bs73) (bs137 := bs74) h73len h74len,
    show List.zipWith (· ||| ·) bs73 bs74 = blockHalfOr bs k from by
      rw [blockHalfOr, ← hz, ← hd],
    ← blockHalfOr_length bs hk]
  exact JsonUtf8Steps.natToBytes_bytesToNat _

/-- **The page's probe answers the block's ASCII test.** -/
theorem fb54Probe_ne_zero_iff_blockHalfOr {bs : List UInt8} {k : Nat}
    {bs73 bs74 : List UInt8}
    (hk : k < blocksOf bs.length)
    (h73 : bs73 = (docBlock bs k).take 32) (h74 : bs74 = (docBlock bs k).drop 32) :
    fb54Probe (fb54Or (unpackLanes 64 4 (bytesToNat bs74))
        (unpackLanes 64 4 (bytesToNat bs73))) ≠ 0 ↔
      ∀ x ∈ blockHalfOr bs k, x.toNat < 0x80 := by
  have hlen : (fb54Or (unpackLanes 64 4 (bytesToNat bs74))
      (unpackLanes 64 4 (bytesToNat bs73))).length = 4 := by
    unfold fb54Or
    rw [List.length_zipWith, unpackLanes_length, unpackLanes_length, Nat.min_self]
  have hbytes := asciiBytes_fb54Or_halves hk h73 h74
  rw [fb54Probe_eq_asciiProbe]
  constructor
  · intro hne
    rcases asciiProbe_eq_zero_or_one _ with h0 | h1
    · exact absurd h0 hne
    · rw [← hbytes]
      exact (asciiProbe_eq_one_iff_asciiBytes _ hlen).mp h1
  · intro hall h0
    have h1 := (asciiProbe_eq_one_iff_asciiBytes _ hlen).mpr (by rw [hbytes]; exact hall)
    rw [h0] at h1
    exact absurd h1 (by decide)

/-- **A set probe makes the block ASCII.**  The probe is the high-bit test of the
block's half-OR, and both halves are high-clear exactly when their OR is, so
every byte of the block is below `0x80`. -/
theorem docBlock_ascii_of_probe {bs : List UInt8} {k : Nat} {bs73 bs74 : List UInt8}
    (hk : k < blocksOf bs.length)
    (h73 : bs73 = (docBlock bs k).take 32) (h74 : bs74 = (docBlock bs k).drop 32)
    (hprobe : fb54Probe (fb54Or (unpackLanes 64 4 (bytesToNat bs74))
        (unpackLanes 64 4 (bytesToNat bs73))) ≠ 0) :
    ∀ x ∈ docBlock bs k, x.toNat < 0x80 := by
  have hblen : (docBlock bs k).length = 64 := docBlock_length_of_lt bs hk
  have hhalf := (fb54Probe_ne_zero_iff_blockHalfOr hk h73 h74).mp hprobe
  intro x hx
  obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hx
  have hm64 : m < 64 := by rw [hblen] at hm; exact hm
  rw [← getD_of_lt _ 0x00 hm]
  rcases Nat.lt_or_ge m 32 with hm32 | hm32
  · have hbh := blockHalfOr_getD bs hk hm32
    have hlt : ((blockHalfOr bs k).getD m 0x00).toNat < 0x80 := by
      rw [getD_of_lt _ 0x00 (by rw [blockHalfOr_length bs hk]; exact hm32)]
      exact hhalf _ (List.getElem_mem (by rw [blockHalfOr_length bs hk]; exact hm32))
    rw [hbh, u8_or_lt] at hlt
    exact hlt.1
  · have hm' : m - 32 < 32 := by omega
    have hbh := blockHalfOr_getD bs hk hm'
    have hlt : ((blockHalfOr bs k).getD (m - 32) 0x00).toNat < 0x80 := by
      rw [getD_of_lt _ 0x00 (by rw [blockHalfOr_length bs hk]; exact hm')]
      exact hhalf _ (List.getElem_mem (by rw [blockHalfOr_length bs hk]; exact hm'))
    rw [hbh, u8_or_lt] at hlt
    rw [show 32 + (m - 32) = m from by omega] at hlt
    exact hlt.2

/-! ### The window's two spellings

The peel's window is built from the padded document's blocks, while `klAll`'s
window is the unpadded `0x00 :: 0x00 :: 0x00 :: bs`.  At a block that lies
wholly inside the document the two spellings are the same bytes, and that is the
form `packLanes_or281_eq` asks for. -/

/-- The padded window is the unpadded one followed by its zero padding. -/
theorem window_padded_eq (bs : List UInt8) :
    (0x00 :: 0x00 :: 0x00 :: padded bs)
      = (0x00 :: 0x00 :: 0x00 :: bs)
        ++ List.replicate (64 * blocksOf bs.length - bs.length) (0x00 : UInt8) := rfl

/-- **The carry bytes agree.**  Block `i`'s three carry bytes are document bytes,
so the padding after the document cannot reach them. -/
theorem klPre_padded_eq (bs : List UInt8) {i : Nat} (hi : 64 * i ≤ bs.length) :
    klPre (0x00 :: 0x00 :: 0x00 :: bs) i
      = klPre (0x00 :: 0x00 :: 0x00 :: padded bs) i := by
  have hW : (0x00 :: 0x00 :: 0x00 :: bs).length = bs.length + 3 := rfl
  have hstart : 3 ≤ ((0x00 :: 0x00 :: 0x00 :: bs).drop (64 * i)).length := by
    rw [List.length_drop, hW]; omega
  unfold klPre
  rw [window_padded_eq,
    List.drop_append_of_le_length (by rw [hW]; omega), List.take_append,
    show 3 - ((0x00 :: 0x00 :: 0x00 :: bs).drop (64 * i)).length = 0 from by omega,
    List.take_zero, List.append_nil]

/-- **The blocks agree at a full block.** -/
theorem klBlk_padded_eq (bs : List UInt8) {i : Nat} (hi : 64 * (i + 1) ≤ bs.length) :
    klBlk (0x00 :: 0x00 :: 0x00 :: bs) i
      = klBlk (0x00 :: 0x00 :: 0x00 :: padded bs) i := by
  have hW : (0x00 :: 0x00 :: 0x00 :: bs).length = bs.length + 3 := rfl
  have hlen : 64 ≤ ((0x00 :: 0x00 :: 0x00 :: bs).drop (64 * i + 3)).length := by
    rw [List.length_drop, hW]; omega
  unfold klBlk
  rw [window_padded_eq,
    List.drop_append_of_le_length (by rw [hW]; omega), List.take_append,
    show 64 - ((0x00 :: 0x00 :: 0x00 :: bs).drop (64 * i + 3)).length = 0 from by omega,
    List.take_zero, List.append_nil]

/-- The padded window's block at a live index is the document's block. -/
theorem klBlk_padded_eq_docBlock (bs : List UInt8) {i : Nat}
    (hi : i < blocksOf bs.length) :
    klBlk (0x00 :: 0x00 :: 0x00 :: padded bs) i = docBlock bs i := by
  rw [← peelWindow_block bs hi, peelWindow_drop3 hi]
  exact List.take_of_length_le (by rw [docBlock_length bs hi]; omega)

/-! ### The page's six windows, at the peel's window

`packLanes_or281_eq` reads the row's six windows as slices of `peelWindow`, which
is the three carry bytes and the block.  This lemma reads them from the document
at the loop's own hypotheses: the block at the row, and the blocks below it. -/

/-- **The six DFA windows, at the document's own reads.**  `peelWindow_reads` at
the form the loop holds: the block's own sixty-four bytes and the blocks below it
rather than the whole padded window. -/
theorem peelWindow_reads_of_block (mem : Mem) (bs : List UInt8) (b shr : Nat)
    (hb3 : 3 ≤ b) (hshr : shr < blocksOf bs.length)
    (hzero : readBytes mem (b - 3) 3 = some [0, 0, 0])
    (hblk : readBytes mem (b + 64 * shr) 64 = some (docBlock bs shr))
    (hbelow : ∀ j, j < shr →
      readBytes mem (b + 64 * j) 64 = some (docBlock bs j)) :
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
    have hblk0 : readBytes mem b 64 = some (docBlock bs 0) := by simpa using hblk
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
      have h := readBytes_docBlock_inside (addr := b) hblk0 (k := 0) (n := 31) (by omega)
      simpa using h
    have hb30 : readBytes mem b 30 = some ((docBlock bs 0).take 30) := by
      have h := readBytes_docBlock_inside (addr := b) hblk0 (k := 0) (n := 30) (by omega)
      simpa using h
    have hb29 : readBytes mem b 29 = some ((docBlock bs 0).take 29) := by
      have h := readBytes_docBlock_inside (addr := b) hblk0 (k := 0) (n := 29) (by omega)
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
      readBytes_docBlock_inside (addr := b) hblk0 (k := 31) (n := 32) (by omega)
    have r184 : readBytes mem (b + 30) 32
        = some (((docBlock bs 0).drop 30).take 32) :=
      readBytes_docBlock_inside (addr := b) hblk0 (k := 30) (n := 32) (by omega)
    have r185 : readBytes mem (b + 29) 32
        = some (((docBlock bs 0).drop 29).take 32) :=
      readBytes_docBlock_inside (addr := b) hblk0 (k := 29) (n := 32) (by omega)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [cons_drop2_take32]; exact r171
    · rw [cons_drop1_take32]; exact r172
    · rw [cons_take32]; exact r173
    · rw [cons_drop32_drop2_take32]; exact r183
    · rw [cons_drop32_drop1_take32]; exact r184
    · rw [cons_drop32]; exact r185
  · have hP : (docBlock bs (shr - 1)).length = 64 :=
      docBlock_length bs (by omega)
    rw [peelWindow_succ h0]
    have hprev : readBytes mem (b + 64 * (shr - 1)) 64 = some (docBlock bs (shr - 1)) :=
      hbelow (shr - 1) (by omega)
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

/-- **The page's six windows, at the peel's window's slices.**  The bundle
`packLanes_or281_eq` reads: each of the row's six windows is the peel window's
slice at that offset. -/
structure PageDfaWindows (bs : List UInt8) (k : Nat)
    (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) : Prop where
  /-- The window one byte below the row. -/
  w41 : bs41 = ((peelWindow bs k).drop 2).take 32
  /-- The window two bytes below the row. -/
  w42 : bs42 = ((peelWindow bs k).drop 1).take 32
  /-- The window three bytes below the row. -/
  w43 : bs43 = (peelWindow bs k).take 32
  /-- The interior window thirty-one bytes into the row. -/
  w57 : bs57 = (((peelWindow bs k).drop 32).drop 2).take 32
  /-- The interior window thirty bytes into the row. -/
  w58 : bs58 = (((peelWindow bs k).drop 32).drop 1).take 32
  /-- The interior window twenty-nine bytes into the row. -/
  w59 : bs59 = ((peelWindow bs k).drop 32).take 32

/-- **The page's six windows are the peel window's slices**, from the page's own
reads.  The reads are the row's, and the slices are
`peelWindow_reads_of_block`'s, at the same addresses. -/
theorem pageDfaWindows_of_reads {mem : Mem} {bs : List UInt8} {b shr : Nat}
    {bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8}
    (hb3 : 3 ≤ b) (hshr : shr < blocksOf bs.length)
    (hzero : readBytes mem (b - 3) 3 = some [0, 0, 0])
    (hblk : readBytes mem (b + 64 * shr) 64 = some (docBlock bs shr))
    (hbelow : ∀ j, j < shr →
      readBytes mem (b + 64 * j) 64 = some (docBlock bs j))
    (w41 : readBytes mem (b + 64 * shr - 1) 32 = some bs41)
    (w42 : readBytes mem (b + 64 * shr - 2) 32 = some bs42)
    (w43 : readBytes mem (b + 64 * shr - 3) 32 = some bs43)
    (w57 : readBytes mem (b + 64 * shr + 31) 32 = some bs57)
    (w58 : readBytes mem (b + 64 * shr + 30) 32 = some bs58)
    (w59 : readBytes mem (b + 64 * shr + 29) 32 = some bs59) :
    PageDfaWindows bs shr bs41 bs42 bs43 bs57 bs58 bs59 := by
  obtain ⟨r41, r42, r43, r57, r58, r59⟩ :=
    peelWindow_reads_of_block mem bs b shr hb3 hshr hzero hblk hbelow
  exact
    { w41 := Option.some.inj (w41.symm.trans r41)
      w42 := Option.some.inj (w42.symm.trans r42)
      w43 := Option.some.inj (w43.symm.trans r43)
      w57 := Option.some.inj (w57.symm.trans r57)
      w58 := Option.some.inj (w58.symm.trans r58)
      w59 := Option.some.inj (w59.symm.trans r59) }

/-! ### The classifier's two controls

The DFA step's third table reads the block's high nibbles, which the body's own
expression is.  These are `packLanes_or281_eq`'s two control hypotheses at the
page's registers. -/

/-- The page's first control is the low half's high nibbles. -/
theorem low88_eq_hiNibbleLanes (c : FusedCarry) (bs73 bs74 : List UInt8)
    (h73 : bs73.length = 32) :
    (fusedValues c bs73 bs74).low88 = hiNibbleLanes (bytesToNat bs73) := by
  rw [fb54_low88, fb54_byte87, fb54_shr84, fb54_half83, byteView_highNibble' _ h73]

/-- The page's second control is the high half's high nibbles. -/
theorem low97_eq_hiNibbleLanes (c : FusedCarry) (bs73 bs74 : List UInt8)
    (h74 : bs74.length = 32) :
    (fusedValues c bs73 bs74).low97 = hiNibbleLanes (bytesToNat bs74) := by
  rw [fb54_low97, fb54_byte96, fb54_shr93, fb54_half92, byteView_highNibble' _ h74]

/-! ### The carry

The invariant at one loop head, and the two pieces of its step that do not depend
on the arm. -/

/-- **The loop's accumulator carry.**  The carried word packs to the window
walk's accumulator at the loop's index; it has four lanes; and the carried probe
either is clear or marks an ASCII block boundary. -/
structure AccCarry (bs : List UInt8) (c : FusedCarry) : Prop where
  /-- The word packs to the accumulator at the loop's index. -/
  pack : packLanes c.u8k = bytesToNat (klAcc bs c.i.toNat)
  /-- The word has four lanes. -/
  len : c.u8k.length = 4
  /-- The probe marks an ASCII carried-byte window, or is clear. -/
  carry : c.prevAscii = 0 ∨
    ∀ b ∈ klPre (0x00 :: 0x00 :: 0x00 :: bs) c.i.toNat, b.toNat < 0x80

/-- **The carry at the entry's zero word.**  The preheader stages the zero
accumulator, and at block zero the three carry bytes are the staged zeroes, so
the probe's meaning is settled whatever the preheader wrote. -/
theorem accCarry_init {bs : List UInt8} {c : FusedCarry}
    (hi : c.i = 0) (hu : c.u8k = List.replicate 4 (0 : BitVec 64)) :
    AccCarry bs c := by
  have hzero : klAcc bs 0 = List.replicate 32 0x00 := rfl
  refine ⟨?_, by rw [hu]; simp, Or.inr ?_⟩
  · rw [hu, hi]
    show packLanes (List.replicate 4 (0 : BitVec 64)) = bytesToNat (klAcc bs 0)
    rw [show packLanes (List.replicate 4 (0 : BitVec 64)) = 0 from rfl, hzero]
    exact (bytesToNat_eq_zero_iff (List.replicate 32 0x00)).mpr
      (by intro x hx; rw [List.eq_of_mem_replicate hx])
  · have hidx : c.i.toNat = 0 := by rw [hi]; rfl
    rw [hidx]
    intro b hb
    have hlist : klPre (0x00 :: 0x00 :: 0x00 :: bs) 0 = [0x00, 0x00, 0x00] := rfl
    rw [hlist] at hb
    simp only [List.mem_cons, List.not_mem_nil] at hb
    rcases hb with rfl | rfl | rfl | hb
    · decide
    · decide
    · decide
    · exact absurd hb (by simp)

/-- **The successor's probe marks an ASCII boundary.**  The page's probe is the
block's ASCII test, so a set successor probe means the next index's carry bytes
(the block's last three) are ASCII. -/
theorem accCarry_nextCarry {bs : List UInt8} {c : FusedCarry}
    {bs73 bs74 : List UInt8} {u8k : List (BitVec 64)} {mem : Mem}
    (hi : c.i.toNat < blocksOf bs.length)
    (hle64 : c.i.toNat + 1 < 2 ^ 64)
    (hfull : 64 * (c.i.toNat + 1) ≤ bs.length)
    (h73 : bs73 = (docBlock bs c.i.toNat).take 32)
    (h74 : bs74 = (docBlock bs c.i.toNat).drop 32) :
    (fusedNext c bs73 bs74 u8k mem).prevAscii = 0 ∨
      ∀ b ∈ klPre (0x00 :: 0x00 :: 0x00 :: bs)
        (fusedNext c bs73 bs74 u8k mem).i.toNat, b.toNat < 0x80 := by
  by_cases h0 : fb54Probe (fb54Or (unpackLanes 64 4 (bytesToNat bs74))
      (unpackLanes 64 4 (bytesToNat bs73))) = 0
  · left
    show fb54Probe (fb54Or (unpackLanes 64 4 (bytesToNat bs74))
      (unpackLanes 64 4 (bytesToNat bs73))) = 0
    exact h0
  · right
    have hhigh : ∀ x ∈ docBlock bs c.i.toNat, x.toNat < 0x80 :=
      docBlock_ascii_of_probe hi h73 h74 h0
    have hnext : (fusedNext c bs73 bs74 u8k mem).i.toNat = c.i.toNat + 1 :=
      toNat_succ_of_lt hle64
    intro b hb
    rw [hnext, klPre_succ] at hb
    rw [klBlk_padded_eq bs hfull, klBlk_padded_eq_docBlock bs hi] at hb
    exact hhigh b (List.mem_of_mem_drop hb)

/-! ### The DFA arm's step

`%or.i281` packs to `klErrBlk`'s word or-ed into the accumulator, which is
`klAcc`'s own step at the successor. -/

/-- **The page's DFA step advances the fold.**  From the carry, the row's six
windows as the peel window's slices, and the two controls, `if.then90`'s
`%or.i281` packs to `klAcc` at the successor index. -/
theorem packLanes_dfa_or281 {bs : List UInt8} {c : FusedCarry}
    {bs73 bs74 : List UInt8} {bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8}
    (hcarry : AccCarry bs c)
    (hi : c.i.toNat < blocksOf bs.length)
    (hfull : 64 * (c.i.toNat + 1) ≤ bs.length)
    (h73 : bs73 = (docBlock bs c.i.toNat).take 32)
    (h74 : bs74 = (docBlock bs c.i.toNat).drop 32)
    (hw : PageDfaWindows bs c.i.toNat bs41 bs42 bs43 bs57 bs58 bs59) :
    packLanes (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).or281
      = bytesToNat (klAcc bs (c.i.toNat + 1)) := by
  have hle : 64 * c.i.toNat ≤ bs.length := by omega
  have hblen : (docBlock bs c.i.toNat).length = 64 := docBlock_length_of_lt bs hi
  have hs : peelWindow bs c.i.toNat
      = klPre (0x00 :: 0x00 :: 0x00 :: bs) c.i.toNat
        ++ klBlk (0x00 :: 0x00 :: 0x00 :: bs) c.i.toNat := by
    rw [peelWindow_split hi, peelWindow_take3 bs hi, peelWindow_block bs hi,
      klPre_padded_eq bs hle, klBlk_padded_eq bs hfull]
  have h67 : 67 ≤ (peelWindow bs c.i.toNat).length := by
    rw [peelWindow_length hi]
    omega
  have hpre3 : (klPre (0x00 :: 0x00 :: 0x00 :: bs) c.i.toNat).length = 3 := by
    rw [klPre_padded_eq bs hle, ← peelWindow_take3 bs hi, List.length_take,
      peelWindow_length hi]
    decide
  have hblk64 : (klBlk (0x00 :: 0x00 :: 0x00 :: bs) c.i.toNat).length = 64 := by
    rw [klBlk_padded_eq bs hfull, ← peelWindow_block bs hi, List.length_take,
      List.length_drop, peelWindow_length hi]
    decide
  have h73len : bs73.length = 32 := by
    rw [h73, List.length_take, hblen, Nat.min_eq_left (by decide)]
  have h74len : bs74.length = 32 := by
    rw [h74, List.length_drop, hblen]
  have h73' : bs73 = List.take 32 (List.drop 3 (peelWindow bs c.i.toNat)) := by
    rw [peelWindow_drop3 hi, h73]
  have h74' : bs74
      = List.take 32 (List.drop 3 (List.drop 32 (peelWindow bs c.i.toNat))) := by
    rw [peelWindow_block_hi hi, h74]
  have h88 := low88_eq_hiNibbleLanes c bs73 bs74 h73len
  have h97 := low97_eq_hiNibbleLanes c bs73 bs74 h74len
  have hgoal : packLanes (ifThen90Values (fusedValues c bs73 bs74).addPtr57
      (fusedValues c bs73 bs74).low88 (fusedValues c bs73 bs74).low97 c.u8k
      bs41 bs42 bs43 bs57 bs58 bs59).or281
      = bytesToNat (klAcc bs (c.i.toNat + 1)) :=
    packLanes_or281_eq bs _ _ _ c.u8k bs41 bs42 bs43 bs57 bs58 bs59 bs73 bs74
      (peelWindow bs c.i.toNat) (klPre (0x00 :: 0x00 :: 0x00 :: bs) c.i.toNat)
      (klBlk (0x00 :: 0x00 :: 0x00 :: bs) c.i.toNat) c.i.toNat
      hw.w41 hw.w42 hw.w43 hw.w57 hw.w58 hw.w59 h73' h74' h88 h97 hs h67 hpre3
      hblk64 rfl rfl hcarry.len hcarry.pack
  exact hgoal

/-! ### The merge arm's step

The merge keeps `%u8k.2` at the body's `%u8k.1521`.  The block's error vector is
zero exactly when the probe and the carry are ASCII, so keeping the word is the
fold's step. -/

/-- **The block's error vector vanishes at an ASCII boundary.** -/
theorem klErrBlk_eq_zero_of_ascii {bs : List UInt8} {c : FusedCarry}
    {bs73 bs74 : List UInt8}
    (hcarry : AccCarry bs c)
    (hi : c.i.toNat < blocksOf bs.length)
    (hfull : 64 * (c.i.toNat + 1) ≤ bs.length)
    (hprev : c.prevAscii ≠ 0)
    (h73 : bs73 = (docBlock bs c.i.toNat).take 32)
    (h74 : bs74 = (docBlock bs c.i.toNat).drop 32)
    (hprobe : fb54Probe (fb54Or (unpackLanes 64 4 (bytesToNat bs74))
        (unpackLanes 64 4 (bytesToNat bs73))) ≠ 0) :
    klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) c.i.toNat)
      (klBlk (0x00 :: 0x00 :: 0x00 :: bs) c.i.toNat) = List.replicate 32 0x00 := by
  have hhigh : ∀ x ∈ docBlock bs c.i.toNat, x.toNat < 0x80 :=
    docBlock_ascii_of_probe hi h73 h74 hprobe
  have hblkHigh : ∀ x ∈ klBlk (0x00 :: 0x00 :: 0x00 :: bs) c.i.toNat, x.toNat < 0x80 := by
    rw [klBlk_padded_eq bs hfull, klBlk_padded_eq_docBlock bs hi]
    exact hhigh
  have hpreHigh : ∀ x ∈ klPre (0x00 :: 0x00 :: 0x00 :: bs) c.i.toNat, x.toNat < 0x80 := by
    rcases hcarry.carry with h0 | h
    · exact absurd h0 hprev
    · exact h
  exact utf8Skip_eq_zero _ _ hpreHigh hblkHigh

/-- **The merge arm keeps the fold.**  The block's contribution is zero, so the
successor's word is still the accumulator at the successor index. -/
theorem packLanes_merge_keep {bs : List UInt8} {c : FusedCarry} {gate : BitVec 1}
    {bs73 bs74 : List UInt8}
    (hcarry : AccCarry bs c)
    (hi : c.i.toNat < blocksOf bs.length)
    (hfull : 64 * (c.i.toNat + 1) ≤ bs.length)
    (h73 : bs73 = (docBlock bs c.i.toNat).take 32)
    (h74 : bs74 = (docBlock bs c.i.toNat).drop 32)
    (hdec : fb54Select gate (fusedValues c bs73 bs74).v107 = 1) :
    packLanes c.u8k = bytesToNat (klAcc bs (c.i.toNat + 1)) := by
  have hv : (fusedValues c bs73 bs74).v107 = 1 := (fb54Select_eq_one hdec).2
  have hand : (fusedValues c bs73 bs74).tobool89
      &&& (fusedValues c bs73 bs74).tobool88 = (1 : BitVec 1) := hv
  obtain ⟨h89, h88⟩ := bv1_and_one_iff _ _ |>.mp hand
  have hpv : c.prevAscii ≠ 0 := (evalICmp_ne_zero_one_iff c.prevAscii).mp h89
  have hprobe : fb54Probe (fb54Or (unpackLanes 64 4 (bytesToNat bs74))
      (unpackLanes 64 4 (bytesToNat bs73))) ≠ 0 :=
    (evalICmp_ne_zero_one_iff _).mp h88
  have hzero := klErrBlk_eq_zero_of_ascii hcarry hi hfull hpv h73 h74 hprobe
  have hstep : klAcc bs (c.i.toNat + 1) = klAcc bs c.i.toNat := by
    rw [klAcc_succ, hzero,
      zipWith_zero_right (· ||| ·) (0 : UInt8) (klAcc bs c.i.toNat)
        (fun x => UInt8.or_zero) (klAcc_length bs c.i.toNat)]
  rw [hstep]
  exact hcarry.pack

/-! ### The four page shapes -/

/-- **The DFA arm's page.**  Both of the DFA arm's branches reach the latch with
the successor's word advancing the fold, whatever the page's memory is. -/
theorem accLatch_dfa {bs : List UInt8} {c : FusedCarry}
    {bs73 bs74 : List UInt8} {bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8}
    (hcarry : AccCarry bs c)
    (hi : c.i.toNat < c.shr.toNat) (hshrLe : c.shr.toNat ≤ blocksOf bs.length)
    (hshrBlocks : 64 * c.shr.toNat ≤ bs.length) (hshr57 : c.shr.toNat < 2 ^ 57)
    (hb3 : 3 ≤ c.b) (hzero : readBytes c.mem (c.b - 3) 3 = some [0, 0, 0])
    (hdoc : ∀ j, j < c.shr.toNat →
      readBytes c.mem (c.b + 64 * j) 64 = some (docBlock bs j))
    (h73 : bs73 = (docBlock bs c.i.toNat).take 32)
    (h74 : bs74 = (docBlock bs c.i.toNat).drop 32)
    (w41 : readBytes c.mem (c.b + 64 * c.i.toNat - 1) 32 = some bs41)
    (w42 : readBytes c.mem (c.b + 64 * c.i.toNat - 2) 32 = some bs42)
    (w43 : readBytes c.mem (c.b + 64 * c.i.toNat - 3) 32 = some bs43)
    (w57 : readBytes c.mem (c.b + 64 * c.i.toNat + 31) 32 = some bs57)
    (w58 : readBytes c.mem (c.b + 64 * c.i.toNat + 30) 32 = some bs58)
    (w59 : readBytes c.mem (c.b + 64 * c.i.toNat + 29) 32 = some bs59)
    (mem : Mem) :
    AccCarry bs (fusedNext c bs73 bs74
      (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).or281 mem) := by
  have hlt : c.i.toNat < blocksOf bs.length := by omega
  have hle64 : c.i.toNat + 1 < 2 ^ 64 := by omega
  have hfull : 64 * (c.i.toNat + 1) ≤ bs.length := by
    have := Nat.mul_le_mul_left 64 (Nat.le_of_lt hi)
    omega
  have hw : PageDfaWindows bs c.i.toNat bs41 bs42 bs43 bs57 bs58 bs59 :=
    pageDfaWindows_of_reads hb3 hlt hzero (hdoc c.i.toNat hi)
      (fun j hj => hdoc j (by omega)) w41 w42 w43 w57 w58 w59
  have hpack := packLanes_dfa_or281 hcarry hlt hfull h73 h74 hw
  have hnext : (fusedNext c bs73 bs74
      (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).or281 mem).i.toNat
      = c.i.toNat + 1 :=
    toNat_succ_of_lt hle64
  have hpack' : packLanes (fusedNext c bs73 bs74
      (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).or281 mem).u8k
      = bytesToNat (klAcc bs (fusedNext c bs73 bs74
        (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).or281 mem).i.toNat) := by
    rw [hnext]
    exact hpack
  have hlen' : (fusedNext c bs73 bs74
      (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).or281 mem).u8k.length = 4 := by
    show (ifThen90Values (fusedValues c bs73 bs74).addPtr57
      (fusedValues c bs73 bs74).low88 (fusedValues c bs73 bs74).low97 c.u8k
      bs41 bs42 bs43 bs57 bs58 bs59).or281.length = 4
    exact ifThen90Values_or281_length _ _ _ _ _ _ _ _ _ _ hcarry.len
  exact ⟨hpack', hlen', accCarry_nextCarry hlt hle64 hfull h73 h74⟩

/-- **The merge arm's page.**  Both of the merge arm's branches keep the body's
word, and the fold's step is the block's zero contribution. -/
theorem accLatch_merge {bs : List UInt8} {c : FusedCarry} {gate : BitVec 1}
    {bs73 bs74 : List UInt8}
    (hcarry : AccCarry bs c)
    (hi : c.i.toNat < c.shr.toNat) (hshrLe : c.shr.toNat ≤ blocksOf bs.length)
    (hshrBlocks : 64 * c.shr.toNat ≤ bs.length) (hshr57 : c.shr.toNat < 2 ^ 57)
    (h73 : bs73 = (docBlock bs c.i.toNat).take 32)
    (h74 : bs74 = (docBlock bs c.i.toNat).drop 32)
    (hdec : fb54Select gate (fusedValues c bs73 bs74).v107 = 1)
    (mem : Mem) :
    AccCarry bs (fusedNext c bs73 bs74 c.u8k mem) := by
  have hlt : c.i.toNat < blocksOf bs.length := by omega
  have hle64 : c.i.toNat + 1 < 2 ^ 64 := by omega
  have hfull : 64 * (c.i.toNat + 1) ≤ bs.length := by
    have := Nat.mul_le_mul_left 64 (Nat.le_of_lt hi)
    omega
  have hpack := packLanes_merge_keep hcarry hlt hfull h73 h74 hdec
  have hnext : (fusedNext c bs73 bs74 c.u8k mem).i.toNat = c.i.toNat + 1 :=
    toNat_succ_of_lt hle64
  have hpack' : packLanes (fusedNext c bs73 bs74 c.u8k mem).u8k
      = bytesToNat (klAcc bs (fusedNext c bs73 bs74 c.u8k mem).i.toNat) := by
    rw [hnext]
    exact hpack
  have hlen' : (fusedNext c bs73 bs74 c.u8k mem).u8k.length = 4 := hcarry.len
  exact ⟨hpack', hlen', accCarry_nextCarry hlt hle64 hfull h73 h74⟩

/-- The two loaded halves, from a page's reads. -/
theorem halves_of_reads {mem : Mem} {addr : Nat} {blk bs73 bs74 : List UInt8}
    (hblk : readBytes mem addr 64 = some blk)
    (h73 : readBytes mem addr 32 = some bs73)
    (h74 : readBytes mem (addr + 32) 32 = some bs74) :
    bs73 = blk.take 32 ∧ bs74 = blk.drop 32 := by
  obtain ⟨h1, h2⟩ := readBytes_split mem addr 32 32
    (by rw [show 32 + 32 = 64 from rfl]; exact hblk)
  rw [h73] at h1
  rw [h74] at h2
  exact ⟨Option.some.inj h1, Option.some.inj h2⟩

/-- **The DFA-escape page's accumulator carry.**  `fused_dfa_escape_page`'s
successor word and the escape call's memory.  The state, the gate and the call's
outcome are the page's own: the accumulator's carry reads only the index's place
in the bound and the page's reads. -/
theorem accLatch_dfa_escape (sel : Calls) (env : Env) (s : State) (c : FusedCarry)
    (gate : BitVec 1) (bs73 bs74 : List UInt8)
    (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) (bs : List UInt8)
    (hinv : FusedInv env s c gate 0)
    (hcarry : AccCarry bs c)
    (hshrLe : c.shr.toNat ≤ blocksOf bs.length)
    (hshrBlocks : 64 * c.shr.toNat ≤ bs.length) (hshr57 : c.shr.toNat < 2 ^ 57)
    (hb3 : 3 ≤ c.b) (hzero : readBytes c.mem (c.b - 3) 3 = some [0, 0, 0])
    (hdoc : ∀ j, j < c.shr.toNat →
      readBytes c.mem (c.b + 64 * j) 64 = some (docBlock bs j))
    (hread73 : readBytes c.mem (c.b + 64 * c.i.toNat) 32 = some bs73)
    (hread74 : readBytes c.mem (c.b + 64 * c.i.toNat + 32) 32 = some bs74)
    (w41 : readBytes c.mem (c.b + 64 * c.i.toNat - 1) 32 = some bs41)
    (w42 : readBytes c.mem (c.b + 64 * c.i.toNat - 2) 32 = some bs42)
    (w43 : readBytes c.mem (c.b + 64 * c.i.toNat - 3) 32 = some bs43)
    (w57 : readBytes c.mem (c.b + 64 * c.i.toNat + 31) 32 = some bs57)
    (w58 : readBytes c.mem (c.b + 64 * c.i.toNat + 30) 32 = some bs58)
    (w59 : readBytes c.mem (c.b + 64 * c.i.toNat + 29) 32 = some bs59)
    (r : CallOutcome) :
    AccCarry bs (fusedNext c bs73 bs74
      (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).or281 r.mem) := by
  obtain ⟨h73, h74⟩ :=
    halves_of_reads (hdoc c.i.toNat hinv.index_lt) hread73 hread74
  exact accLatch_dfa hcarry hinv.index_lt hshrLe hshrBlocks hshr57 hb3 hzero hdoc
    h73 h74 w41 w42 w43 w57 w58 w59 r.mem

/-- **The DFA-skip page's accumulator carry.**  `fused_dfa_skip_page`'s successor
word and the page's store. -/
theorem accLatch_dfa_skip (sel : Calls) (env : Env) (s : State) (c : FusedCarry)
    (gate : BitVec 1) (bs73 bs74 : List UInt8)
    (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) (bs : List UInt8)
    (hinv : FusedInv env s c gate 1)
    (hcarry : AccCarry bs c)
    (hshrLe : c.shr.toNat ≤ blocksOf bs.length)
    (hshrBlocks : 64 * c.shr.toNat ≤ bs.length) (hshr57 : c.shr.toNat < 2 ^ 57)
    (hb3 : 3 ≤ c.b) (hzero : readBytes c.mem (c.b - 3) 3 = some [0, 0, 0])
    (hdoc : ∀ j, j < c.shr.toNat →
      readBytes c.mem (c.b + 64 * j) 64 = some (docBlock bs j))
    (hread73 : readBytes c.mem (c.b + 64 * c.i.toNat) 32 = some bs73)
    (hread74 : readBytes c.mem (c.b + 64 * c.i.toNat + 32) 32 = some bs74)
    (w41 : readBytes c.mem (c.b + 64 * c.i.toNat - 1) 32 = some bs41)
    (w42 : readBytes c.mem (c.b + 64 * c.i.toNat - 2) 32 = some bs42)
    (w43 : readBytes c.mem (c.b + 64 * c.i.toNat - 3) 32 = some bs43)
    (w57 : readBytes c.mem (c.b + 64 * c.i.toNat + 31) 32 = some bs57)
    (w58 : readBytes c.mem (c.b + 64 * c.i.toNat + 30) 32 = some bs58)
    (w59 : readBytes c.mem (c.b + 64 * c.i.toNat + 29) 32 = some bs59) :
    AccCarry bs (fusedNext c bs73 bs74
      (fusedDfa90 c bs73 bs74 bs41 bs42 bs43 bs57 bs58 bs59).or281
      (fusedStore c bs73 bs74)) := by
  obtain ⟨h73, h74⟩ :=
    halves_of_reads (hdoc c.i.toNat hinv.index_lt) hread73 hread74
  exact accLatch_dfa hcarry hinv.index_lt hshrLe hshrBlocks hshr57 hb3 hzero hdoc
    h73 h74 w41 w42 w43 w57 w58 w59 (fusedStore c bs73 bs74)

/-- **The merge-escape page's accumulator carry.**  `fused_merge_escape_page`'s
successor word and the escape call's memory. -/
theorem accLatch_merge_escape (sel : Calls) (env : Env) (s : State) (c : FusedCarry)
    (gate : BitVec 1) (bs73 bs74 : List UInt8) (bs : List UInt8)
    (hinv : FusedInv env s c gate 0)
    (hcarry : AccCarry bs c)
    (hshrLe : c.shr.toNat ≤ blocksOf bs.length)
    (hshrBlocks : 64 * c.shr.toNat ≤ bs.length) (hshr57 : c.shr.toNat < 2 ^ 57)
    (hdoc : ∀ j, j < c.shr.toNat →
      readBytes c.mem (c.b + 64 * j) 64 = some (docBlock bs j))
    (hread73 : readBytes c.mem (c.b + 64 * c.i.toNat) 32 = some bs73)
    (hread74 : readBytes c.mem (c.b + 64 * c.i.toNat + 32) 32 = some bs74)
    (hdec : fb54Select gate (fusedValues c bs73 bs74).v107 = 1)
    (r : CallOutcome) :
    AccCarry bs (fusedNext c bs73 bs74 c.u8k r.mem) := by
  obtain ⟨h73, h74⟩ :=
    halves_of_reads (hdoc c.i.toNat hinv.index_lt) hread73 hread74
  exact accLatch_merge hcarry hinv.index_lt hshrLe hshrBlocks hshr57 h73 h74 hdec r.mem

/-- **The merge-skip page's accumulator carry.**  `fused_merge_skip_page`'s
successor word and the page's store. -/
theorem accLatch_merge_skip (sel : Calls) (env : Env) (s : State) (c : FusedCarry)
    (gate : BitVec 1) (bs73 bs74 : List UInt8) (bs : List UInt8)
    (hinv : FusedInv env s c gate 1)
    (hcarry : AccCarry bs c)
    (hshrLe : c.shr.toNat ≤ blocksOf bs.length)
    (hshrBlocks : 64 * c.shr.toNat ≤ bs.length) (hshr57 : c.shr.toNat < 2 ^ 57)
    (hdoc : ∀ j, j < c.shr.toNat →
      readBytes c.mem (c.b + 64 * j) 64 = some (docBlock bs j))
    (hread73 : readBytes c.mem (c.b + 64 * c.i.toNat) 32 = some bs73)
    (hread74 : readBytes c.mem (c.b + 64 * c.i.toNat + 32) 32 = some bs74)
    (hdec : fb54Select gate (fusedValues c bs73 bs74).v107 = 1) :
    AccCarry bs (fusedNext c bs73 bs74 c.u8k (fusedStore c bs73 bs74)) := by
  obtain ⟨h73, h74⟩ :=
    halves_of_reads (hdoc c.i.toNat hinv.index_lt) hread73 hread74
  exact accLatch_merge hcarry hinv.index_lt hshrLe hshrBlocks hshr57 h73 h74 hdec
    (fusedStore c bs73 bs74)

/-! ### The exit's word

The loop's word at `%shr`, the peel's error vector at the peel's block, and
`klAll_eq_klAcc_succ`: `%or.i`'s word is `klAll`'s, and `acc_pack_of_peel` is the
record's field at it. -/

/-- **`bytesToNat` is injective at a length.** -/
theorem bytesToNat_inj {a b : List UInt8} (hlen : a.length = b.length)
    (h : bytesToNat a = bytesToNat b) : a = b := by
  calc a = natToBytes (bytesToNat a) a.length :=
        (JsonUtf8Steps.natToBytes_bytesToNat a).symm
    _ = natToBytes (bytesToNat b) b.length := by rw [h, hlen]
    _ = b := JsonUtf8Steps.natToBytes_bytesToNat b

/-- **The peel's merged word is `klAll`'s.**  The loop's invariant gives its
carried accumulator as `klAcc bs shr` (`bytesToNat`'s injectivity at thirty-two
bytes), `klAll_eq_klAcc_succ` adds the peel's own block, and the packing round
trip returns the word. -/
theorem peelWord_pack_klAll {bs : List UInt8} {gate : Bool} {shr : Nat}
    {acc : List UInt8} {u8k orI : List (BitVec 64)}
    (hsucc : shr + 1 = blocksOf bs.length)
    (hacc32 : acc.length = 32) (hlen : u8k.length = 4)
    (hpack : packLanes u8k = bytesToNat acc)
    (hloop : packLanes u8k = bytesToNat (klAcc bs shr))
    (horI : orI = unpackLanes 64 4 (bytesToNat (List.zipWith (· ||| ·) acc
      (klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) shr)
        (klBlk (0x00 :: 0x00 :: 0x00 :: bs) shr))))) :
    packLanes orI = bytesToNat (klAll gate bs) := by
  have haccEq : acc = klAcc bs shr :=
    bytesToNat_inj (by rw [hacc32, klAcc_length]) (by rw [← hpack, hloop])
  have hlen32 : (List.zipWith (· ||| ·) acc
      (klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) shr)
        (klBlk (0x00 :: 0x00 :: 0x00 :: bs) shr))).length = 32 := by
    rw [List.length_zipWith, hacc32, klErrBlk_length, Nat.min_self]
  rw [horI, packLanes_unpackLanes, show (4 * 64 : Nat) = 256 from by decide,
    Nat.mod_eq_of_lt (by
      have := bytesToNat_lt (List.zipWith (· ||| ·) acc
        (klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) shr)
          (klBlk (0x00 :: 0x00 :: 0x00 :: bs) shr)))
      rw [hlen32] at this
      simpa [show (256 : Nat) ^ 32 = 2 ^ 256 from by decide] using this),
    haccEq, ← klAll_eq_klAcc_succ bs gate hsucc]

/-- **The peel's word, at the staging's lane form.**  `acc_pack_of_peel` consumes
this: the merged word is `klAll`'s four lanes. -/
theorem peelWord_eq_klAll_lanes {bs : List UInt8} {gate : Bool} {shr : Nat}
    {acc : List UInt8} {u8k orI : List (BitVec 64)}
    (hsucc : shr + 1 = blocksOf bs.length)
    (hacc32 : acc.length = 32) (hlen : u8k.length = 4)
    (hpack : packLanes u8k = bytesToNat acc)
    (hloop : packLanes u8k = bytesToNat (klAcc bs shr))
    (horI : orI = unpackLanes 64 4 (bytesToNat (List.zipWith (· ||| ·) acc
      (klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) shr)
        (klBlk (0x00 :: 0x00 :: 0x00 :: bs) shr))))) :
    orI = unpackLanes 64 4 (bytesToNat (klAll gate bs)) := by
  have hpacked := peelWord_pack_klAll (gate := gate) hsucc hacc32 hlen hpack hloop horI
  have horilen : orI.length = 4 := by
    rw [horI]
    exact unpackLanes_length 64 4 _
  have h1 : unpackLanes 64 4 (packLanes orI) = orI := by
    rw [← horilen]
    exact unpackLanes_packLanes orI
  rw [← h1, hpacked]

/-- **The peeled arm's `acc_pack`.**  `acc_pack_of_peel` at the peel's word: the
staging's accumulator field on the peel's arm, from the loop's invariant. -/
theorem acc_pack_of_peelWord {bs : List UInt8} {gate : Bool} {shr : Nat}
    {acc : List UInt8} {u8k orI : List (BitVec 64)}
    (hsucc : shr + 1 = blocksOf bs.length)
    (hacc32 : acc.length = 32) (hlen : u8k.length = 4)
    (hpack : packLanes u8k = bytesToNat acc)
    (hloop : packLanes u8k = bytesToNat (klAcc bs shr))
    (horI : orI = unpackLanes 64 4 (bytesToNat (List.zipWith (· ||| ·) acc
      (klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) shr)
        (klBlk (0x00 :: 0x00 :: 0x00 :: bs) shr))))) :
    packLanes orI = bytesToNat (klAll gate bs) :=
  acc_pack_of_peel hsucc orI
    (peelWord_eq_klAll_lanes hsucc hacc32 hlen hpack hloop horI)

/-- **The exit's facts from the carry.**  `loopExitFacts_at` takes the
accumulator's pack and lane count as the run's obligations; the carry is both. -/
theorem loopExitFacts_of_accCarry {mem0 : Mem} {xp xn : Nat} {ps : List Nat}
    {bs : List UInt8} {env : Env} {s : State} {c : FusedCarry}
    (hexit : FusedExit env s c) (hc : LoopCarry mem0 xp xn ps bs c)
    (hacc : AccCarry bs c)
    (hframe : EntryFrame mem0 c.mem c.ent (blocksOf bs.length)) :
    LoopExitFacts mem0 bs c :=
  loopExitFacts_at hexit hc hframe hacc.pack hacc.len

/-- **The aligned arm's `acc_pack`.**  At the document's block count the
invariant is the staging's accumulator directly, through `acc_pack_of_klAcc`. -/
theorem acc_pack_of_alignedExit {bs : List UInt8} {gate : Bool} {nb : Nat}
    {c : FusedCarry} (hcarry : AccCarry bs c)
    (hnb : nb = blocksOf bs.length) (hi : c.i.toNat = nb) :
    packLanes c.u8k = bytesToNat (klAll gate bs) := by
  refine acc_pack_of_klAcc bs gate nb c.u8k hnb ?_
  rw [← hi]
  exact hcarry.pack

/-! ### Axiom footprints

The probe facts are the verdict's own (`asciiProbe_eq_*`); the window reads are
`JsonS1BlocksPeelWindows`'s at the loop's block reads; the DFA step is
`packLanes_or281_eq` and the merge's is `utf8Skip_eq_zero` with `klAcc_succ`; the
exit is `klAll_eq_klAcc_succ` and `acc_pack_of_peel`.  No statement reaches
`sorryAx`.  The four DFA page shapes carry `Classical.choice` through
`JsonS1BlocksLoop.ifThen90Values_or281_length`, the same footprint the loop's own
page lemmas (`fused_dfa_skip_page` and its siblings) report; the merge shapes and
the exit's statements carry only `propext` and `Quot.sound`. -/

#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.bv1_and_one_iff
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.fb54Select_eq_one
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.fb54Probe_eq_asciiProbe
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.asciiBytes_fb54Or_halves
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.fb54Probe_ne_zero_iff_blockHalfOr
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.docBlock_ascii_of_probe
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.window_padded_eq
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.klPre_padded_eq
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.klBlk_padded_eq
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.klBlk_padded_eq_docBlock
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.peelWindow_reads_of_block
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.PageDfaWindows
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.pageDfaWindows_of_reads
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.low88_eq_hiNibbleLanes
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.low97_eq_hiNibbleLanes
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.AccCarry
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.accCarry_init
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.accCarry_nextCarry
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.packLanes_dfa_or281
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.klErrBlk_eq_zero_of_ascii
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.packLanes_merge_keep
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.accLatch_dfa
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.accLatch_merge
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.halves_of_reads
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.accLatch_dfa_escape
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.accLatch_dfa_skip
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.accLatch_merge_escape
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.accLatch_merge_skip
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.bytesToNat_inj
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.peelWord_pack_klAll
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.peelWord_eq_klAll_lanes
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.acc_pack_of_peelWord
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.loopExitFacts_of_accCarry
#print axioms LeanLLVM.Refinement.JsonS1BlocksAccFold.acc_pack_of_alignedExit

end LeanLLVM.Refinement.JsonS1BlocksAccFold
