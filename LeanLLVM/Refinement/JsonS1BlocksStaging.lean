/-
The block unit's verdict staging, proved at the loop's own registers.

`JsonS1BlocksVerdict` states what the emitted `if.end170` needs from its caller:
the ASCII word's high bits (`ascii_bytes`), the accumulator's packed word
(`acc_pack`), and the error bit the phi selects (`err_def`).  It proves the post's
verdict clause *from* those three fields.  This module proves the fields
themselves, at the words the caller's phase and the fused loop carry.

## The three fields

**`acc_pack`.**  The loop carries `packLanes u8k = bytesToNat (klAcc bs i)`, the
ungated window walk's own step (`JsonUtf8Steps.klAcc_succ`), and stops at the
document's block count.  `fusedRun_word_eq_klAll` reads the fused loop's word at
that count as the stage's `klAll`, for either gate; `fusedRun_word_eq_klAcc` reads
the same word as the walk.  `klAcc_eq_klAll` is the two readings' equality, and
`acc_pack_of_klAcc` is the field.

**`ascii_bytes`.**  The latch ORs the block's two half-vectors lane for lane into
the carried word (`%or.i283 = %74 ||| %73`, then `%or.i282 = %or.i283 |||
%ascii.1522`), so the word is the lane-wise OR of every block the fused loop
passed.  `asciiLanes` is that fold at the four-lane carrier and `asciiAcc` is the
same fold at the byte carrier the field speaks about; `packLanes_asciiLanes` is
their agreement, and `ascii_bytes_of_carry` is the field at any word that packs
to `asciiAcc`.  Its content is `asciiAcc_high_iff`: a byte of the accumulated
word is below `0x80` exactly when every byte of the padded window is.  Each
document byte sits in exactly one lane (position `q`'s block is `q / 64`, its
half is `(q % 64) / 32` and its lane is the remainder), the zero padding
contributes no bit, and `JsonScanSpec.ascii_padded_iff` closes the window/document
step.

**`err_def`.**  The `if.end170` error phi has three incoming arms, and
`ErrArm` names them: `if.end153`'s `%cmp155` (the zero-length document),
`if.then164`'s `%or169500` (`%cmp155` or-ed with the last byte's `%204`), and
`if.end153.thread`'s `%cmp155495` (the peeled tail's accumulator-only bit).
`ErrArm.reads` is each arm's word and `ErrArm.Branch` is the condition the phi
selects it under.  `err_def_of_arm` proves the staging's equivalence at each:
the `if.end153` arm is vacuous in the tail conjunct because its length is zero,
the `if.then164` arm is `or169500_one_iff` at the document's last byte, and the
thread arm is the accumulator-only reading plus one document fact — the peel's
non-aligned length means the padding after the last byte already carries the
error (`not_klErrAll_of_tail_padding`), so a tail byte cannot sit on a clear
accumulator.

## What is here, and what is not

`staging_of_carry` assembles `VerdictStaging` from the three carries, and
`post_of_carry` reads the post's verdict conjuncts at the returned word.  The
record's remaining conjuncts — its entry array, the escape stream and count, and
the four-region `UnchangedOutside` — are the memory obligations
`JsonS1BlocksCompose` names, not the verdict's, and this module states nothing
about them.
-/
import LeanLLVM.Refinement.JsonS1BlocksVerdict
import LeanLLVM.Refinement.JsonS1BlocksRefine
import LeanLLVM.Refinement.JsonUtf8Fused

namespace LeanLLVM.Refinement.JsonS1BlocksStaging

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.BitLanes
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksVerdict
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonUtf8Fused
open LeanLLVM.Refinement.JsonUtf8IR (utf8Window)
open LeanLLVM.Refinement.JsonUtf8Spec
open LeanLLVM.Refinement.JsonUtf8Steps

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ### The accumulator's block count

The fused loop's word and the ungated window walk are two readings of one word;
at the document's block count they read the stage's own accumulator. -/

/-- **The ungated window walk at the document's block count is the stage's
accumulator**, for both gate values.  `fusedRun_word_eq_klAll` reads the fused
loop's word as `klAll`; `fusedRun_word_eq_klAcc` reads the same word as the
ungated walk. -/
theorem klAcc_eq_klAll (bs : List UInt8) (gate : Bool) :
    klAcc bs ((bs.length + 63) / 64) = klAll gate bs := by
  rw [← fusedRun_word_eq_klAll bs gate, fusedRun_word_eq_klAcc]

/-- The stage's accumulator is thirty-two bytes. -/
theorem klAll_length (bs : List UInt8) (gate : Bool) : (klAll gate bs).length = 32 := by
  cases gate with
  | false =>
      rw [klAll_false_eq_klAcc]
      exact klAcc_length bs _
  | true =>
      rw [klAll_gate_invariant, klAll_false_eq_klAcc]
      exact klAcc_length bs _

/-! ### `acc_pack`

The carried word packs to the stage's accumulator.  The loop's invariant is the
`klAcc` spelling (its own step is `klAcc_succ`); the record's field is the `klAll`
spelling.  `acc_pack_of_klAcc` is the bridge, and `stageU8k` is the word itself. -/

/-- **The carried accumulator packs to `klAll`**: the loop's invariant
`packLanes u8k = bytesToNat (klAcc bs i)` read at the document's block count. -/
theorem acc_pack_of_klAcc (bs : List UInt8) (gate : Bool) (nb : Nat)
    (u8k : List (BitVec 64)) (hnb : nb = blocksOf bs.length)
    (hcarry : packLanes u8k = bytesToNat (klAcc bs nb)) :
    packLanes u8k = bytesToNat (klAll gate bs) := by
  rw [hcarry, hnb]
  exact congrArg bytesToNat (klAcc_eq_klAll bs gate)

/-- The staging's accumulator word: the stage's own bytes as four lanes. -/
def stageU8k (bs : List UInt8) (gate : Bool) : List (BitVec 64) :=
  unpackLanes 64 4 (bytesToNat (klAll gate bs))

/-- The lane view has four lanes. -/
theorem stageU8k_length (bs : List UInt8) (gate : Bool) :
    (stageU8k bs gate).length = 4 :=
  unpackLanes_length 64 4 _

/-- **The lane view packs to the stage's accumulator.** -/
theorem stageU8k_pack (bs : List UInt8) (gate : Bool) :
    packLanes (stageU8k bs gate) = bytesToNat (klAll gate bs) := by
  have hlt : bytesToNat (klAll gate bs) < 2 ^ 256 := by
    have h := bytesToNat_lt (klAll gate bs)
    rw [klAll_length bs gate, show (256 : Nat) ^ 32 = 2 ^ 256 from by decide] at h
    exact h
  unfold stageU8k
  rw [packLanes_unpackLanes, show (4 * 64) = 256 from by decide, Nat.mod_eq_of_lt hlt]

/-! ### The ASCII word

The latch ORs the block's two halves lane for lane.  The definitions below are
the fold the loop runs: `asciiLanes` at the four-lane carrier the body keeps, and
`asciiAcc` at the byte carrier `asciiBytes` reads.  The emitted `or` writes the
second half first (`%74 ||| %73`); `|||` is commutative, so the word is the one
these folds build. -/

/-- One block's two halves, or-ed byte for byte: `%or.i283`'s byte view.
`docBlock` is the padded window's block, so a block past the document's end
reads the zero padding. -/
def blockHalfOr (bs : List UInt8) (bi : Nat) : List UInt8 :=
  List.zipWith (· ||| ·) ((docBlock bs bi).take 32) ((docBlock bs bi).drop 32)

/-- One block's two halves as the four lanes the body loads, or-ed lane for
lane: `%or.i283 = %74 ||| %73`.  The left operand is the block's low half. -/
def blockLanes (bs : List UInt8) (bi : Nat) : List (BitVec 64) :=
  List.zipWith (· ||| ·)
    (unpackLanes 64 4 (bytesToNat ((docBlock bs bi).take 32)))
    (unpackLanes 64 4 (bytesToNat ((docBlock bs bi).drop 32)))

/-- **`%ascii.1.lcssa` after `j` blocks**: the loop's own fold, from the zero word
the preheader stages.  The latch's step is `asciiLanes_succ`. -/
def asciiLanes (bs : List UInt8) (j : Nat) : List (BitVec 64) :=
  (List.range j).foldl (fun acc bi => List.zipWith (· ||| ·) acc (blockLanes bs bi))
    (List.replicate 4 0)

/-- The same fold at the byte carrier: the bytes `asciiBytes` reads. -/
def asciiAcc (bs : List UInt8) (j : Nat) : List UInt8 :=
  (List.range j).foldl (fun acc bi => List.zipWith (· ||| ·) acc (blockHalfOr bs bi))
    (List.replicate 32 0)

/-- The padded window's block is a whole sixty-four bytes inside the block count. -/
theorem docBlock_length_of_lt (bs : List UInt8) {bi : Nat}
    (hbi : bi < blocksOf bs.length) : (docBlock bs bi).length = 64 := by
  unfold docBlock
  rw [List.length_take, List.length_drop, padded_length]
  have hge : 64 ≤ 64 * blocksOf bs.length - 64 * bi := by
    have h1 : 64 * bi + 64 ≤ 64 * blocksOf bs.length := by
      have hstep : bi + 1 ≤ blocksOf bs.length := hbi
      have hmul := Nat.mul_le_mul_left 64 hstep
      rwa [Nat.mul_add, Nat.mul_one] at hmul
    omega
  rw [Nat.min_eq_left hge]

/-- A block's half-OR is thirty-two bytes. -/
theorem blockHalfOr_length (bs : List UInt8) {bi : Nat}
    (hbi : bi < blocksOf bs.length) : (blockHalfOr bs bi).length = 32 := by
  unfold blockHalfOr
  rw [List.length_zipWith, List.length_take, List.length_drop,
    docBlock_length_of_lt bs hbi]
  decide

/-- A block's lane OR has four lanes. -/
theorem blockLanes_length (bs : List UInt8) (bi : Nat) :
    (blockLanes bs bi).length = 4 := by
  unfold blockLanes
  rw [List.length_zipWith, unpackLanes_length, unpackLanes_length, Nat.min_self]

/-- The lane fold advances by one block. -/
theorem asciiLanes_succ (bs : List UInt8) (j : Nat) :
    asciiLanes bs (j + 1) =
      List.zipWith (· ||| ·) (asciiLanes bs j) (blockLanes bs j) := by
  unfold asciiLanes
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The byte fold advances by one block. -/
theorem asciiAcc_succ (bs : List UInt8) (j : Nat) :
    asciiAcc bs (j + 1) =
      List.zipWith (· ||| ·) (asciiAcc bs j) (blockHalfOr bs j) := by
  unfold asciiAcc
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The lane fold has four lanes. -/
theorem asciiLanes_length (bs : List UInt8) (j : Nat) : (asciiLanes bs j).length = 4 := by
  induction j with
  | zero =>
      unfold asciiLanes
      rw [List.range_zero, List.foldl_nil, List.length_replicate]
  | succ n ih =>
      rw [asciiLanes_succ, List.length_zipWith, ih, blockLanes_length, Nat.min_self]

/-- The byte fold is thirty-two bytes inside the block count. -/
theorem asciiAcc_length (bs : List UInt8) {j : Nat} (hj : j ≤ blocksOf bs.length) :
    (asciiAcc bs j).length = 32 := by
  revert hj
  induction j with
  | zero =>
      intro _
      unfold asciiAcc
      rw [List.range_zero, List.foldl_nil, List.length_replicate]
  | succ n ih =>
      intro hj
      rw [asciiAcc_succ, List.length_zipWith, ih (by omega),
        blockHalfOr_length bs (by omega), Nat.min_self]

/-- The lane fold's four zeros pack to the zero word. -/
theorem packLanes_replicate_zero : packLanes (List.replicate 4 (0 : BitVec 64)) = 0 := by
  decide

/-- The byte fold's thirty-two zeros are the zero word. -/
theorem bytesToNat_replicate_zero : bytesToNat (List.replicate 32 (0 : UInt8)) = 0 := by
  decide

/-- Packing a thirty-two-byte list's lanes is the list's natural. -/
theorem packLanes_unpackLanes_bytesToNat (B : List UInt8) (hB : B.length = 32) :
    packLanes (unpackLanes 64 4 (bytesToNat B)) = bytesToNat B := by
  have hlt : bytesToNat B < 2 ^ 256 := by
    have h := bytesToNat_lt B
    rw [hB, show (256 : Nat) ^ 32 = 2 ^ 256 from by decide] at h
    exact h
  rw [packLanes_unpackLanes, show (4 * 64) = 256 from by decide, Nat.mod_eq_of_lt hlt]

/-- A block's lane OR packs to its half-OR's bytes. -/
theorem packLanes_blockLanes (bs : List UInt8) {bi : Nat}
    (hbi : bi < blocksOf bs.length) :
    packLanes (blockLanes bs bi) = bytesToNat (blockHalfOr bs bi) := by
  have hlen : (docBlock bs bi).length = 64 := docBlock_length_of_lt bs hbi
  have h0 : ((docBlock bs bi).take 32).length = 32 := by
    rw [List.length_take, hlen]; decide
  have h1 : ((docBlock bs bi).drop 32).length = 32 := by
    rw [List.length_drop, hlen]
  unfold blockLanes blockHalfOr
  rw [packLanes_zipWith_or (by rw [unpackLanes_length, unpackLanes_length]),
    packLanes_unpackLanes_bytesToNat _ h0,
    packLanes_unpackLanes_bytesToNat _ h1,
    ← bytesToNat_zipWith_or _ _ (by rw [h0, h1])]

/-- **The lane fold packs to the byte fold**, block for block. -/
theorem packLanes_asciiLanes (bs : List UInt8) (j : Nat)
    (hj : j ≤ blocksOf bs.length) :
    packLanes (asciiLanes bs j) = bytesToNat (asciiAcc bs j) := by
  revert hj
  induction j with
  | zero =>
      intro _
      unfold asciiLanes asciiAcc
      rw [List.range_zero, List.foldl_nil, List.foldl_nil,
        packLanes_replicate_zero, bytesToNat_replicate_zero]
  | succ n ih =>
      intro hj
      rw [asciiLanes_succ, asciiAcc_succ,
        packLanes_zipWith_or (by rw [asciiLanes_length, blockLanes_length]),
        ih (by omega), packLanes_blockLanes bs (by omega),
        ← bytesToNat_zipWith_or _ _
          (by rw [asciiAcc_length bs (by omega), blockHalfOr_length bs (by omega)])]

/-- **The lane fold's byte view is the byte fold.** -/
theorem asciiBytes_asciiLanes (bs : List UInt8) :
    asciiBytes (asciiLanes bs (blocksOf bs.length)) =
      asciiAcc bs (blocksOf bs.length) := by
  unfold asciiBytes
  rw [packLanes_asciiLanes bs (blocksOf bs.length) (Nat.le_refl _),
    ← asciiAcc_length bs (j := blocksOf bs.length) (Nat.le_refl _),
    JsonUtf8Steps.natToBytes_bytesToNat]

/-! ### Indexing the fold

The two directions of the high-bit claim read one byte of the fold at a time, so
the fold's own byte is the fold of the blocks' bytes. -/

/-- `getD` through `take`, inside the taken span. -/
theorem getD_take_lt (l : List UInt8) {n i : Nat} (hi : i < n) :
    (l.take n).getD i 0x00 = l.getD i 0x00 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hi,
    ← List.getD_eq_getElem?_getD]

/-- `getD` through `drop`. -/
theorem getD_drop (l : List UInt8) (m i : Nat) :
    (l.drop m).getD i 0x00 = l.getD (m + i) 0x00 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD]

/-- `getD` of an `|||` of two long-enough byte lists is the `|||` of their
`getD`s. -/
theorem zipWith_getD_or {a b : List UInt8} {k : Nat}
    (ha : a.length = 32) (hb : b.length = 32) (hk : k < 32) :
    (List.zipWith (· ||| ·) a b).getD k 0x00 = a.getD k 0x00 ||| b.getD k 0x00 :=
  getD_zipWith (· ||| ·) a b 0x00 0x00 0x00 (by rw [ha]; exact hk) (by rw [hb]; exact hk)

/-- A padded block's byte is the padded window's byte at the block's offset. -/
theorem docBlock_getD (bs : List UInt8) {bi m : Nat} (hm : m < 64) :
    (docBlock bs bi).getD m 0x00 = (padded bs).getD (64 * bi + m) 0x00 := by
  exact klByte_take_drop (padded bs) (64 * bi) 64 m hm

/-- A block's half-OR byte is the OR of its two halves' bytes at that lane. -/
theorem blockHalfOr_getD (bs : List UInt8) {bi : Nat}
    (hbi : bi < blocksOf bs.length) {k : Nat} (hk : k < 32) :
    (blockHalfOr bs bi).getD k 0x00 =
      (docBlock bs bi).getD k 0x00 ||| (docBlock bs bi).getD (32 + k) 0x00 := by
  have hlen : (docBlock bs bi).length = 64 := docBlock_length_of_lt bs hbi
  unfold blockHalfOr
  rw [zipWith_getD_or (by rw [List.length_take, hlen]; decide)
      (by rw [List.length_drop, hlen]) hk,
    getD_take_lt (docBlock bs bi) (n := 32) hk, getD_drop]

/-- A fold of `|||` is high-clear exactly when its start and every element are. -/
theorem foldl_or_high_iff (l : List UInt8) (acc : UInt8) :
    (l.foldl (· ||| ·) acc).toNat < 0x80 ↔
      acc.toNat < 0x80 ∧ ∀ x ∈ l, x.toNat < 0x80 := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih, u8_or_lt, List.forall_mem_cons]
      exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

/-- A fold over the block indices is the fold over the mapped list. -/
theorem foldl_range_map (f : Nat → UInt8) (n : Nat) (init : UInt8) :
    (List.range n).foldl (fun acc i => acc ||| f i) init
      = ((List.range n).map f).foldl (· ||| ·) init := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.map_append, List.foldl_append, ih]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]

/-- The byte fold's lane `k` is the fold of the blocks' lane `k`. -/
theorem asciiAcc_getD (bs : List UInt8) {j : Nat} (hj : j ≤ blocksOf bs.length)
    {k : Nat} (hk : k < 32) :
    (asciiAcc bs j).getD k 0x00 =
      (List.range j).foldl (fun acc bi => acc ||| (blockHalfOr bs bi).getD k 0x00) 0x00 := by
  revert hj
  induction j with
  | zero =>
      intro _
      unfold asciiAcc
      rw [List.range_zero, List.foldl_nil, List.foldl_nil,
        getD_of_lt (List.replicate 32 (0x00 : UInt8)) 0x00
          (by rw [List.length_replicate]; exact hk),
        List.getElem_replicate]
  | succ n ih =>
      intro hj
      rw [asciiAcc_succ,
        zipWith_getD_or (asciiAcc_length bs (by omega))
          (blockHalfOr_length bs (by omega)) hk,
        ih (by omega), List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil]

/-- **The byte fold's lane is high-clear exactly when every block's lane is.** -/
theorem asciiAcc_getD_high_iff (bs : List UInt8) (k : Nat) (hk : k < 32) :
    ((asciiAcc bs (blocksOf bs.length)).getD k 0x00).toNat < 0x80 ↔
      ∀ bi, bi < blocksOf bs.length →
        ((blockHalfOr bs bi).getD k 0x00).toNat < 0x80 := by
  rw [asciiAcc_getD bs (Nat.le_refl _) hk, foldl_range_map]
  constructor
  · intro h bi hbi
    exact (foldl_or_high_iff _ _).mp h |>.2 _
      (List.mem_map.mpr ⟨bi, List.mem_range.mpr hbi, rfl⟩)
  · intro h
    refine (foldl_or_high_iff _ _).mpr ⟨by decide, ?_⟩
    intro y hy
    obtain ⟨bi, hbi, rfl⟩ := List.mem_map.mp hy
    exact h bi (List.mem_range.mp hbi)

/-- A padded byte is high-clear: inside the window it is a document byte, and the
padding is zero. -/
theorem padded_getD_high (bs : List UInt8)
    (hp : ∀ x ∈ padded bs, x.toNat < 0x80) (q : Nat) :
    ((padded bs).getD q 0x00).toNat < 0x80 := by
  by_cases hq : q < (padded bs).length
  · rw [getD_of_lt _ _ hq]
    exact hp _ (List.getElem_mem hq)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    decide

/-- **The ASCII word's high bits are the padded window's.**  Every byte of the
accumulated word is below `0x80` exactly when every byte of the padded window is:
the fold ORs each block's two halves byte for byte, so each window byte lands in
exactly one lane and the zero padding contributes nothing. -/
theorem asciiAcc_high_iff (bs : List UInt8) :
    (∀ b ∈ asciiAcc bs (blocksOf bs.length), b.toNat < 0x80) ↔
      ∀ x ∈ padded bs, x.toNat < 0x80 := by
  constructor
  · intro h x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_iff_getElem.mp hx
    have hqlen : q < 64 * blocksOf bs.length := by
      rw [← padded_length (bs := bs)]; exact hq
    have hdecomp : 64 * (q / 64) + q % 64 = q := Nat.div_add_mod q 64
    have ha : q / 64 < blocksOf bs.length :=
      div_lt_of_lt_mul' hqlen
    have hr : q % 64 < 64 := Nat.mod_lt _ (by decide)
    rcases Nat.lt_or_ge (q % 64) 32 with hr32 | hr32
    · have hk : q % 64 < 32 := hr32
      have hklen : q % 64 < (asciiAcc bs (blocksOf bs.length)).length := by
        rw [asciiAcc_length bs (j := blocksOf bs.length) (Nat.le_refl _)]; exact hk
      have hacc : ((asciiAcc bs (blocksOf bs.length)).getD (q % 64) 0x00).toNat < 0x80 := by
        rw [getD_of_lt _ _ hklen]
        exact h _ (List.getElem_mem hklen)
      have hbh := (asciiAcc_getD_high_iff bs (q % 64) hk).mp hacc (q / 64) ha
      rw [blockHalfOr_getD bs ha hk] at hbh
      have hfirst :
          ((docBlock bs (q / 64)).getD (q % 64) 0x00).toNat < 0x80 :=
        (u8_or_lt _ _).mp hbh |>.1
      rw [docBlock_getD bs (bi := q / 64) (m := q % 64) hr, hdecomp,
        getD_of_lt (padded bs) 0x00 hq] at hfirst
      exact hfirst
    · have hk : q % 64 - 32 < 32 := by omega
      have hklen : q % 64 - 32 < (asciiAcc bs (blocksOf bs.length)).length := by
        rw [asciiAcc_length bs (j := blocksOf bs.length) (Nat.le_refl _)]; exact hk
      have hacc :
          ((asciiAcc bs (blocksOf bs.length)).getD (q % 64 - 32) 0x00).toNat < 0x80 := by
        rw [getD_of_lt _ _ hklen]
        exact h _ (List.getElem_mem hklen)
      have hbh := (asciiAcc_getD_high_iff bs (q % 64 - 32) hk).mp hacc (q / 64) ha
      rw [blockHalfOr_getD bs ha hk] at hbh
      have hsecond :
          ((docBlock bs (q / 64)).getD (32 + (q % 64 - 32)) 0x00).toNat < 0x80 :=
        (u8_or_lt _ _).mp hbh |>.2
      rw [show 32 + (q % 64 - 32) = q % 64 from by omega,
        docBlock_getD bs (bi := q / 64) (m := q % 64) hr, hdecomp,
        getD_of_lt (padded bs) 0x00 hq] at hsecond
      exact hsecond
  · intro hp b hb
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hb
    have hk32 : k < 32 := by
      rw [asciiAcc_length bs (j := blocksOf bs.length) (Nat.le_refl _)] at hk
      exact hk
    rw [← getD_of_lt _ 0x00 hk]
    exact (asciiAcc_getD_high_iff bs k hk32).mpr (fun bi hbi => by
      rw [blockHalfOr_getD bs hbi hk32,
        docBlock_getD bs (bi := bi) (m := k) (by omega),
        docBlock_getD bs (bi := bi) (m := 32 + k) (by omega),
        u8_or_lt]
      exact ⟨padded_getD_high bs hp _, padded_getD_high bs hp _⟩)

/-- **`ascii_bytes` at any word that packs to the byte fold.** -/
theorem ascii_bytes_of_carry (bs : List UInt8) (ascii : List (BitVec 64))
    (hcarry : packLanes ascii = bytesToNat (asciiAcc bs (blocksOf bs.length))) :
    (∀ b ∈ asciiBytes ascii, b.toNat < 0x80) ↔ ∀ x ∈ bs, x.toNat < 0x80 := by
  have hbytes : asciiBytes ascii = asciiAcc bs (blocksOf bs.length) := by
    unfold asciiBytes
    rw [hcarry, ← asciiAcc_length bs (j := blocksOf bs.length) (Nat.le_refl _),
      JsonUtf8Steps.natToBytes_bytesToNat]
  rw [hbytes, asciiAcc_high_iff]
  exact (ascii_padded_iff bs).symm

/-- **`ascii_bytes` at the loop's own word.** -/
theorem ascii_bytes_lanes (bs : List UInt8) :
    (∀ b ∈ asciiBytes (asciiLanes bs (blocksOf bs.length)), b.toNat < 0x80) ↔
      ∀ x ∈ bs, x.toNat < 0x80 :=
  ascii_bytes_of_carry bs _ (packLanes_asciiLanes bs (blocksOf bs.length) (Nat.le_refl _))

/-! ### `err_def`

The `if.end170` error phi's three arms, and the staging's equivalence at each. -/

/-- The error phi's three incoming arms. -/
inductive ErrArm where
  /-- `if.end153`'s arm: the zero-length document, `%cmp155` alone. -/
  | nothing
  /-- `if.then164`'s arm: `%or169500`, the last byte's `%204` or-ed in. -/
  | tail
  /-- `if.end153.thread`'s arm: `%cmp155495`, the peeled tail's accumulator only. -/
  | thread

/-- The bit each arm hands the phi. -/
def ErrArm.reads : ErrArm → List (BitVec 64) → UInt8 → BitVec 1
  | .nothing, u8k, _ => evalICmp .eq (ptestzU8k u8k) (0 : BitVec 32)
  | .tail, u8k, last =>
      evalICmp .eq (ptestzU8k u8k) (0 : BitVec 32) ||| utf8TailBit last.toBitVec
  | .thread, u8k, _ => evalICmp .eq (ptestzU8k u8k) (0 : BitVec 32)

/-- The condition the phi selects each arm under, at the document's length. -/
def ErrArm.Branch : ErrArm → Nat → Prop
  | .nothing, n => n = 0
  | .tail, n => n ≠ 0
  | .thread, n => n % 64 ≠ 0

/-- **A clear accumulator is an error-free staged window.** -/
theorem klErrAll_of_acc (bs : List UInt8) (n nb : Nat) (gate : Bool)
    (u8k : List (BitVec 64)) (hn : n = bs.length) (hnb : nb = (n + 63) / 64)
    (hacc : packLanes u8k = bytesToNat (klAll gate bs))
    (hall : u8k.all (fun x => decide (x = 0x00)) = true) :
    klErrAll (utf8Window bs n nb) (64 * nb) := by
  have hz : packLanes u8k = 0 := (packLanes_eq_zero_iff_all u8k).mpr hall
  rw [hacc] at hz
  refine (klAll_zero_iff_klErrAll bs n nb gate hn hnb).mp ?_
  exact (all_eq_zero_iff (klAll gate bs)).mpr
    ((bytesToNat_eq_zero_iff (klAll gate bs)).mp hz)

/-- **`if.end153`'s arm**: the length is zero, so the tail conjunct is vacuous. -/
theorem err_def_nothing (bs : List UInt8) (n : Nat) (u8k : List (BitVec 64))
    (err : BitVec 1) (hn0 : n = 0) (hu : u8k.length = 4)
    (hreads : err = evalICmp .eq (ptestzU8k u8k) (0 : BitVec 32)) :
    err = 1 ↔ ¬ (u8k.all (fun x => decide (x = 0x00)) = true) ∨
      (n ≠ 0 ∧ klTailByte (klByte bs (n - 1)) = true) := by
  subst n
  rw [hreads, ptestzU8k_icmp_eq_zero u8k hu]
  constructor
  · intro h; exact Or.inl h
  · rintro (h | ⟨h0, -⟩)
    · exact h
    · exact absurd rfl h0

/-- **`if.then164`'s arm**: `%or169500` at the document's last byte. -/
theorem err_def_tail (bs : List UInt8) (n : Nat) (u8k : List (BitVec 64))
    (err : BitVec 1) (last : UInt8) (hn0 : n ≠ 0) (hu : u8k.length = 4)
    (hlast : last = klByte bs (n - 1))
    (hreads : err = evalICmp .eq (ptestzU8k u8k) (0 : BitVec 32) |||
      utf8TailBit last.toBitVec) :
    err = 1 ↔ ¬ (u8k.all (fun x => decide (x = 0x00)) = true) ∨
      (n ≠ 0 ∧ klTailByte (klByte bs (n - 1)) = true) := by
  rw [hreads, or169500_one_iff u8k last hu, hlast]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨hn0, h⟩
  · rintro (h | ⟨-, h⟩)
    · exact Or.inl h
    · exact Or.inr h

/-- **`if.end153.thread`'s arm**: the accumulator-only bit.  The arm is the peel's,
so the document is not block-aligned and the padding after its last byte already
carries a tail byte's error. -/
theorem err_def_thread (bs : List UInt8) (n nb : Nat) (gate : Bool)
    (u8k : List (BitVec 64)) (err : BitVec 1) (hmod : n % 64 ≠ 0)
    (hn : n = bs.length) (hnb : nb = blocksOf bs.length)
    (hacc : packLanes u8k = bytesToNat (klAll gate bs)) (hu : u8k.length = 4)
    (hreads : err = evalICmp .eq (ptestzU8k u8k) (0 : BitVec 32)) :
    err = 1 ↔ ¬ (u8k.all (fun x => decide (x = 0x00)) = true) ∨
      (n ≠ 0 ∧ klTailByte (klByte bs (n - 1)) = true) := by
  have hn0 : n ≠ 0 := by
    intro h
    subst h
    exact hmod (Nat.zero_mod 64)
  have hnb' : nb = (n + 63) / 64 := by simpa [blocksOf, hn] using hnb
  rw [hreads, ptestzU8k_icmp_eq_zero u8k hu]
  constructor
  · intro h; exact Or.inl h
  · rintro (h | ⟨-, htail⟩)
    · exact h
    · intro hall
      exact not_klErrAll_of_tail_padding bs n nb hn hnb' hn0 hmod htail
        (klErrAll_of_acc bs n nb gate u8k hn hnb' hacc hall)

/-- **`err_def` at the arm the phi selects**: the three arms' readings, at the
arm's own branch condition. -/
theorem err_def_of_arm (bs : List UInt8) (n nb : Nat) (gate : Bool)
    (u8k : List (BitVec 64)) (err : BitVec 1) (arm : ErrArm) (last : UInt8)
    (hn : n = bs.length) (hnb : nb = blocksOf bs.length)
    (hacc : packLanes u8k = bytesToNat (klAll gate bs)) (hu : u8k.length = 4)
    (hlast : last = klByte bs (n - 1))
    (hreads : err = arm.reads u8k last) (hbranch : arm.Branch n) :
    err = 1 ↔ ¬ (u8k.all (fun x => decide (x = 0x00)) = true) ∨
      (n ≠ 0 ∧ klTailByte (klByte bs (n - 1)) = true) := by
  cases arm with
  | nothing =>
      exact err_def_nothing bs n u8k err (by simpa only [ErrArm.Branch] using hbranch)
        hu hreads
  | tail =>
      exact err_def_tail bs n u8k err last (by simpa only [ErrArm.Branch] using hbranch)
        hu hlast hreads
  | thread =>
      exact err_def_thread bs n nb gate u8k err
        (by simpa only [ErrArm.Branch] using hbranch) hn hnb hacc hu hreads

/-! ### The record

The three fields, assembled; and the post's verdict clause at the returned word. -/

/-- **The staging's three fields, from the loop's carries.**  `hascii` is the
lane fold's carry, `hacc` the accumulator's, and `herr` the phi's selected arm. -/
theorem staging_of_carry (bs : List UInt8) (n nb : Nat) (gate : Bool)
    (ascii u8k : List (BitVec 64)) (err : BitVec 1)
    (hascii_len : ascii.length = 4) (hacc_len : u8k.length = 4)
    (hn : n = bs.length) (hnb : nb = blocksOf bs.length)
    (hascii : packLanes ascii = bytesToNat (asciiAcc bs nb))
    (hacc : packLanes u8k = bytesToNat (klAll gate bs))
    (herr : err = 1 ↔ ¬ (u8k.all (fun x => decide (x = 0x00)) = true) ∨
      (n ≠ 0 ∧ klTailByte (klByte bs (n - 1)) = true)) :
    VerdictStaging ascii u8k bs n nb gate err :=
  ⟨hascii_len, hacc_len, hn, hnb,
    ascii_bytes_of_carry bs ascii (by rw [hascii, hnb]), hacc, herr⟩

/-- **The staging from the loop's accumulator invariant**
(`packLanes u8k = bytesToNat (klAcc bs i)` at the block count). -/
theorem staging_of_loopAcc (bs : List UInt8) (n nb : Nat) (gate : Bool)
    (ascii u8k : List (BitVec 64)) (err : BitVec 1)
    (hascii_len : ascii.length = 4) (hacc_len : u8k.length = 4)
    (hn : n = bs.length) (hnb : nb = blocksOf bs.length)
    (hascii : packLanes ascii = bytesToNat (asciiAcc bs nb))
    (haccK : packLanes u8k = bytesToNat (klAcc bs nb))
    (herr : err = 1 ↔ ¬ (u8k.all (fun x => decide (x = 0x00)) = true) ∨
      (n ≠ 0 ∧ klTailByte (klByte bs (n - 1)) = true)) :
    VerdictStaging ascii u8k bs n nb gate err :=
  staging_of_carry bs n nb gate ascii u8k err hascii_len hacc_len hn hnb hascii
    (acc_pack_of_klAcc bs gate nb u8k hnb haccK) herr

/-- **The post's verdict conjuncts at the returned word**, from the staging. -/
theorem post_of_carry (bs : List UInt8) (n nb : Nat) (gate : Bool)
    (ascii u8k : List (BitVec 64)) (err : BitVec 1)
    (h : VerdictStaging ascii u8k bs n nb gate err) :
    VerdictPost (verdictWord ascii err) bs :=
  h.satisfies_post

/-- **The staging's own word**, as the record reads it: the lane fold and the
stage's accumulator at the document's block count satisfy the three fields. -/
theorem staging_lanes (bs : List UInt8) (gate : Bool) (n nb : Nat) (err : BitVec 1)
    (hn : n = bs.length) (hnb : nb = blocksOf bs.length)
    (herr : err = 1 ↔
      ¬ ((stageU8k bs gate).all (fun x => decide (x = 0x00)) = true) ∨
        (n ≠ 0 ∧ klTailByte (klByte bs (n - 1)) = true)) :
    VerdictStaging (asciiLanes bs (blocksOf bs.length)) (stageU8k bs gate)
      bs n nb gate err :=
  staging_of_carry bs n nb gate _ _ err (asciiLanes_length bs _) (stageU8k_length bs gate)
    hn hnb
    (by rw [hnb]; exact packLanes_asciiLanes bs (blocksOf bs.length) (Nat.le_refl _))
    (stageU8k_pack bs gate) herr

/-! ### The footprint

Every statement reads the emitted body's own definitions and the stage's.  The
`#print axioms` below report `propext` and `Quot.sound` for each of them, and no
statement reaches `Classical.choice` or `sorryAx`. -/

#print axioms LeanLLVM.Refinement.JsonS1BlocksStaging.klAcc_eq_klAll
#print axioms LeanLLVM.Refinement.JsonS1BlocksStaging.acc_pack_of_klAcc
#print axioms LeanLLVM.Refinement.JsonS1BlocksStaging.stageU8k_pack
#print axioms LeanLLVM.Refinement.JsonS1BlocksStaging.packLanes_asciiLanes
#print axioms LeanLLVM.Refinement.JsonS1BlocksStaging.asciiBytes_asciiLanes
#print axioms LeanLLVM.Refinement.JsonS1BlocksStaging.asciiAcc_high_iff
#print axioms LeanLLVM.Refinement.JsonS1BlocksStaging.ascii_bytes_of_carry
#print axioms LeanLLVM.Refinement.JsonS1BlocksStaging.ascii_bytes_lanes
#print axioms LeanLLVM.Refinement.JsonS1BlocksStaging.klErrAll_of_acc
#print axioms LeanLLVM.Refinement.JsonS1BlocksStaging.err_def_nothing
#print axioms LeanLLVM.Refinement.JsonS1BlocksStaging.err_def_tail
#print axioms LeanLLVM.Refinement.JsonS1BlocksStaging.err_def_thread
#print axioms LeanLLVM.Refinement.JsonS1BlocksStaging.err_def_of_arm
#print axioms LeanLLVM.Refinement.JsonS1BlocksStaging.staging_of_carry
#print axioms LeanLLVM.Refinement.JsonS1BlocksStaging.staging_of_loopAcc
#print axioms LeanLLVM.Refinement.JsonS1BlocksStaging.post_of_carry
#print axioms LeanLLVM.Refinement.JsonS1BlocksStaging.staging_lanes

end LeanLLVM.Refinement.JsonS1BlocksStaging
