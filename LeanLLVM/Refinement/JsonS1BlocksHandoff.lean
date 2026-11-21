/-
The fused loop's ASCII carry when the hand-off is later than block zero.

`JsonS1BlocksStaging` proves the staging's three fields from three carried
words, and `JsonS1BlocksLoopFacts` reads them at the loop's exit.  Both spell the
ASCII word's fold from block zero: `packLanes c.ascii = bytesToNat (asciiAcc bs
c.i.toNat)`.  The emitted body does not fold from block zero.  The leading ASCII
phase tests blocks until one has a high bit; `if.then38` joins that block's two
halves into `%or.i284`, `%ascii.0` hands the word on its edge, and `%i.1` starts
the fused loop at the block after it.  (On `%ascii.0`'s other incoming edge,
`entry`, the word is the zero splat and the hand-off's block is zero.)  The
fused loop's `%or.i282` is therefore the join of the hand-off's block with the
blocks after it — the fold from the hand-off's block, not from block zero — and
it holds no word for the blocks before that one, which the phase's own tests
already passed as ASCII.  The equality to `asciiAcc bs nb` therefore holds only
when the hand-off fires at block zero.

## What the loop's word does establish

The verdict's bit 0 asks whether the *document* has no high bit.  The probe over
the loop's thirty-two-byte word is the same census over the padded window, and
that window's prefix is the blocks the leading ASCII phase passed: those blocks
are ASCII by the phase's own test, so they contribute zero to the probe.  The loop's word therefore decides the document's claim even though it
does not equal the fold from block zero.

* `asciiAccFrom bs k n` is the fold over blocks `k`..`n-1`, whose first factor
  is the hand-off's own block; `asciiAccFrom_zero` reads `asciiAcc bs n` as its
  `k = 0` case, so nothing below weakens a block-zero statement.
* `asciiAcc_getD_split` splits one lane of the whole fold into the lane of the
  prefix fold and the lane of the hand-off's fold; `foldl_or_range_split` is the
  fold-level identity behind it.
* `asciiAcc_high_iff_le` is the prefix form of `asciiAcc_high_iff`: the first
  `j` blocks' fold is clear exactly on the first `64 * j` window bytes.
* `ascii_bytes_of_fromCarry` is the staging's `ascii_bytes` clause from the
  hand-off's carry and the phase's prefix: the loop's word is high-clear exactly
  when the document is ASCII.  `ascii_bytes_of_carry` is its `k = 0` instance,
  so the field's meaning is unchanged and the post's `∀ x < 0x80` is stated
  exactly as before.
* `packLanes_seedAscii` / `packLanes_seedAscii_entry` are the seed at the two
  hand-off edges, and `packLanes_blockAsciiFrom` / `packLanes_peelAsciiFrom` the
  page's and the peel's steps: the base and the step an induction over the
  loop's pages needs.
* `staging_of_handoff` (the three fields from the carried words),
  `staging_of_loopExit_handoff` (the aligned exit, the counterpart of
  `staging_of_loopExit`) and `staging_of_exitFacts_handoff` (at `FusedExit`, the
  counterpart of `staging_of_exitFacts`) hand `VerdictStaging` to the verdict.

`AsciiCarryAtHandoff` is the field shape the exit's ASCII carry takes once the
hand-off is not block zero: the loop's carry at its own starting block, with the
phase's prefix.  `JsonS1BlocksLoopFacts` still states `LoopExitFacts.arrAscii` at
block zero; the carry here is the fact that holds past block zero, and
`staging_of_exitFacts_handoff` reads it there.

## What is not here

The peeled arm's accumulator is `klAcc bs shr`, not `klAll gate bs`: the loop
stops one block short and the peel's block is not in the loop's word.  That is
the accumulator's lane, and the statements below take it as a hypothesis
(`hacc`), exactly as `staging_of_carry` does; nothing here claims it at a
non-aligned exit.
-/
import LeanLLVM.Refinement.JsonS1BlocksLoopFacts
import LeanLLVM.Refinement.JsonS1BlocksStaging

namespace LeanLLVM.Refinement.JsonS1BlocksHandoff

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.BitLanes
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1BlocksVerdict
open LeanLLVM.Refinement.JsonS1BlocksStaging
open LeanLLVM.Refinement.JsonS1BlocksLoop
open LeanLLVM.Refinement.JsonS1BlocksLoopFacts
open LeanLLVM.Refinement.JsonS1BlocksTail
open LeanLLVM.Refinement.JsonUtf8Fused
open LeanLLVM.Refinement.JsonUtf8IR (utf8Window)
open LeanLLVM.Refinement.JsonUtf8Spec
open LeanLLVM.Refinement.JsonUtf8Steps

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ### The join on bytes

The staging's folds are `List.zipWith (· ||| ·)` and `List.foldl (· ||| ·)` on
`UInt8`.  Splitting a fold needs the operation's laws, which the library states
at `BitVec`; these two read them back at the byte carrier. -/

theorem u8_or_assoc (a b c : UInt8) : (a ||| b) ||| c = a ||| (b ||| c) := by
  apply UInt8.toBitVec_inj.1
  simp [BitVec.or_assoc]

theorem u8_or_zero (a : UInt8) : a ||| 0 = a := by
  apply UInt8.toBitVec_inj.1
  simp

/-! ### The block fold from the hand-off's block

`%ascii.0` is seeded with the hand-off's own block, not with a running word over
every block before it, so the fused loop's latch ORs from the hand-off's block.
`asciiAccFrom` is that fold; `asciiAcc` is its `k = 0` instance. -/

/-- **The latch's byte fold from block `k`**: the hand-off's block joined with
the blocks after it.  The seed is the hand-off block's own half-OR on the
phase's edge and the zero word on the entry edge, where `k = 0`; either way the
fold's first factor is block `k`, and the pages that follow add one block each. -/
def asciiAccFrom (bs : List UInt8) (k n : Nat) : List UInt8 :=
  (List.range (n - k)).foldl
    (fun acc t => List.zipWith (· ||| ·) acc (blockHalfOr bs (k + t)))
    (List.replicate 32 0)

/-- At `k = 0` the hand-off's fold **is** the staging's own fold. -/
theorem asciiAccFrom_zero (bs : List UInt8) (n : Nat) :
    asciiAccFrom bs 0 n = asciiAcc bs n := by
  unfold asciiAccFrom asciiAcc
  simp only [Nat.sub_zero, Nat.zero_add]

/-- With no blocks left the fold is the zero word: `%ascii.0`'s entry splat. -/
theorem asciiAccFrom_self (bs : List UInt8) (k : Nat) :
    asciiAccFrom bs k k = List.replicate 32 0 := by
  unfold asciiAccFrom
  rw [Nat.sub_self, List.range_zero, List.foldl_nil]

/-- The hand-off's fold advances by one block, as `asciiAcc_succ` does. -/
theorem asciiAccFrom_succ (bs : List UInt8) {k n : Nat} (hk : k ≤ n) :
    asciiAccFrom bs k (n + 1) =
      List.zipWith (· ||| ·) (asciiAccFrom bs k n) (blockHalfOr bs n) := by
  unfold asciiAccFrom
  rw [show n + 1 - k = (n - k) + 1 from by omega,
    List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
    show k + (n - k) = n from by omega]

/-- The hand-off's fold is thirty-two bytes inside the block count. -/
theorem asciiAccFrom_length (bs : List UInt8) {k n : Nat} (hk : k ≤ n)
    (hn : n ≤ blocksOf bs.length) : (asciiAccFrom bs k n).length = 32 := by
  induction n with
  | zero =>
      have hk0 : k = 0 := by omega
      subst hk0
      unfold asciiAccFrom
      rw [Nat.sub_self, List.range_zero, List.foldl_nil, List.length_replicate]
  | succ n ih =>
      rcases Nat.lt_or_eq_of_le hk with hlt | heq
      · rw [asciiAccFrom_succ bs (by omega), List.length_zipWith,
          ih (by omega) (by omega), blockHalfOr_length bs (by omega), Nat.min_self]
      · have hk' : k = n + 1 := heq
        subst hk'
        unfold asciiAccFrom
        rw [Nat.sub_self, List.range_zero, List.foldl_nil, List.length_replicate]

/-- The hand-off's fold's lane `m` is the fold of the blocks' lane `m`. -/
theorem asciiAccFrom_getD (bs : List UInt8) {k n : Nat} (hk : k ≤ n)
    (hn : n ≤ blocksOf bs.length) {m : Nat} (hm : m < 32) :
    (asciiAccFrom bs k n).getD m 0x00 =
      (List.range (n - k)).foldl
        (fun acc t => acc ||| (blockHalfOr bs (k + t)).getD m 0x00) 0x00 := by
  induction n with
  | zero =>
      have hk0 : k = 0 := by omega
      subst hk0
      unfold asciiAccFrom
      rw [Nat.sub_self, List.range_zero, List.foldl_nil, List.foldl_nil,
        getD_of_lt (List.replicate 32 (0x00 : UInt8)) 0x00
          (by rw [List.length_replicate]; exact hm),
        List.getElem_replicate]
  | succ n ih =>
      rcases Nat.lt_or_eq_of_le hk with hlt | heq
      · rw [asciiAccFrom_succ bs (by omega),
          zipWith_getD_or (asciiAccFrom_length bs (by omega) (by omega))
            (blockHalfOr_length bs (by omega)) hm,
          ih (by omega) (by omega)]
        rw [show n + 1 - k = (n - k) + 1 from by omega, List.range_succ,
          List.foldl_append, List.foldl_cons, List.foldl_nil,
          show k + (n - k) = n from by omega]
      · have hk' : k = n + 1 := heq
        subst hk'
        unfold asciiAccFrom
        rw [Nat.sub_self, List.range_zero, List.foldl_nil, List.foldl_nil,
          getD_of_lt (List.replicate 32 (0x00 : UInt8)) 0x00
            (by rw [List.length_replicate]; exact hm),
          List.getElem_replicate]

/-! ### Splitting the fold

The whole fold is the prefix fold joined with the hand-off's fold, lane for
lane.  `foldl_or_range_split` is the identity on the index list, and
`asciiAcc_getD_split` reads it at one lane. -/

/-- **A fold over the block indices splits at `k`**: the fold over `range n` is
the fold over the first `k` indices joined with the fold over the rest, whose
values the second fold reads at the shifted index. -/
theorem foldl_or_range_split (f : Nat → UInt8) {k n : Nat} (hk : k ≤ n) :
    (List.range n).foldl (fun acc bi => acc ||| f bi) 0x00
      = ((List.range k).foldl (fun acc bi => acc ||| f bi) 0x00)
        ||| ((List.range (n - k)).foldl (fun acc t => acc ||| f (k + t)) 0x00) := by
  induction n with
  | zero =>
      have hk0 : k = 0 := by omega
      subst hk0
      simp
  | succ n ih =>
      have hexp : (List.range (n + 1)).foldl (fun acc bi => acc ||| f bi) 0x00
          = ((List.range n).foldl (fun acc bi => acc ||| f bi) 0x00) ||| f n := by
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rcases Nat.lt_or_eq_of_le hk with hlt | heq
      · rw [hexp, ih (by omega)]
        rw [show n + 1 - k = (n - k) + 1 from by omega, List.range_succ,
          List.foldl_append, List.foldl_cons, List.foldl_nil,
          show k + (n - k) = n from by omega]
        exact u8_or_assoc _ _ _
      · have hk' : k = n + 1 := heq
        subst hk'
        rw [Nat.sub_self, List.range_zero, List.foldl_nil, u8_or_zero]

/-- **One lane of the whole fold splits** into the prefix fold's lane and the
hand-off's fold's lane. -/
theorem asciiAcc_getD_split (bs : List UInt8) {k n : Nat} (hk : k ≤ n)
    (hn : n ≤ blocksOf bs.length) {m : Nat} (hm : m < 32) :
    (asciiAcc bs n).getD m 0x00
      = (asciiAcc bs k).getD m 0x00 ||| (asciiAccFrom bs k n).getD m 0x00 := by
  rw [asciiAcc_getD bs (j := n) hn (k := m) hm,
    asciiAcc_getD bs (j := k) (by omega) (k := m) hm,
    asciiAccFrom_getD bs hk hn hm]
  exact foldl_or_range_split (fun bi => (blockHalfOr bs bi).getD m 0x00) hk

/-! ### The fold's high bits at a prefix

`JsonS1BlocksStaging.asciiAcc_high_iff` reads the whole fold against the whole
window.  The hand-off needs the same reading at `j` blocks, so that the prefix
the phase passed can be turned into the prefix fold's clear lanes. -/

/-- **A list of bytes is high-clear exactly when its `getD` is**, inside its
length. -/
theorem mem_high_iff_getD (l : List UInt8) :
    (∀ b ∈ l, b.toNat < 0x80) ↔
      ∀ m, m < l.length → (l.getD m 0x00).toNat < 0x80 := by
  constructor
  · intro h m hm
    rw [getD_of_lt _ 0x00 hm]
    exact h _ (List.getElem_mem hm)
  · intro h b hb
    obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hb
    rw [← getD_of_lt _ 0x00 hm]
    exact h m hm

/-- **The prefix fold's lane is high-clear exactly when every prefix block's
lane is**, for any `j` inside the block count. -/
theorem asciiAcc_getD_high_iff_le (bs : List UInt8) {j : Nat}
    (hj : j ≤ blocksOf bs.length) (m : Nat) (hm : m < 32) :
    ((asciiAcc bs j).getD m 0x00).toNat < 0x80 ↔
      ∀ bi, bi < j → ((blockHalfOr bs bi).getD m 0x00).toNat < 0x80 := by
  rw [asciiAcc_getD bs hj hm, foldl_range_map]
  constructor
  · intro h bi hbi
    exact (foldl_or_high_iff _ _).mp h |>.2 _
      (List.mem_map.mpr ⟨bi, List.mem_range.mpr hbi, rfl⟩)
  · intro h
    refine (foldl_or_high_iff _ _).mpr ⟨by decide, ?_⟩
    intro y hy
    obtain ⟨bi, hbi, rfl⟩ := List.mem_map.mp hy
    exact h bi (List.mem_range.mp hbi)

/-- **The prefix fold's high bits are the window prefix's.**  `j` blocks' fold
is high-clear exactly when the padded window's first `64 * j` bytes are. -/
theorem asciiAcc_high_iff_le (bs : List UInt8) {j : Nat}
    (hj : j ≤ blocksOf bs.length) :
    (∀ b ∈ asciiAcc bs j, b.toNat < 0x80) ↔
      ∀ q, q < 64 * j → ((padded bs).getD q 0x00).toNat < 0x80 := by
  constructor
  · intro h q hq
    have hdecomp : 64 * (q / 64) + q % 64 = q := Nat.div_add_mod q 64
    have ha : q / 64 < j := div_lt_of_lt_mul' (by omega)
    have hr : q % 64 < 64 := Nat.mod_lt _ (by decide)
    rcases Nat.lt_or_ge (q % 64) 32 with hr32 | hr32
    · have hm : q % 64 < (asciiAcc bs j).length := by
        rw [asciiAcc_length bs hj]; exact hr32
      have hacc : ((asciiAcc bs j).getD (q % 64) 0x00).toNat < 0x80 := by
        rw [getD_of_lt _ 0x00 hm]
        exact h _ (List.getElem_mem hm)
      have hbh := (asciiAcc_getD_high_iff_le bs hj (q % 64) hr32).mp hacc (q / 64) ha
      rw [blockHalfOr_getD bs (by omega) hr32] at hbh
      have hfirst := (u8_or_lt _ _).mp hbh |>.1
      rw [docBlock_getD bs (bi := q / 64) (m := q % 64) hr, hdecomp] at hfirst
      exact hfirst
    · have hm : q % 64 - 32 < (asciiAcc bs j).length := by
        rw [asciiAcc_length bs hj]; omega
      have hacc : ((asciiAcc bs j).getD (q % 64 - 32) 0x00).toNat < 0x80 := by
        rw [getD_of_lt _ 0x00 hm]
        exact h _ (List.getElem_mem hm)
      have hbh := (asciiAcc_getD_high_iff_le bs hj (q % 64 - 32) (by omega)).mp hacc
        (q / 64) ha
      rw [blockHalfOr_getD bs (by omega) (by omega)] at hbh
      have hsecond := (u8_or_lt _ _).mp hbh |>.2
      rw [show 32 + (q % 64 - 32) = q % 64 from by omega,
        docBlock_getD bs (bi := q / 64) (m := q % 64) hr, hdecomp] at hsecond
      exact hsecond
  · intro h b hb
    obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hb
    have hm32 : m < 32 := by rw [asciiAcc_length bs hj] at hm; exact hm
    rw [← getD_of_lt _ 0x00 hm]
    refine (asciiAcc_getD_high_iff_le bs hj m hm32).mpr (fun bi hbi => ?_)
    rw [blockHalfOr_getD bs (by omega) hm32, u8_or_lt]
    constructor
    · rw [docBlock_getD bs (bi := bi) (m := m) (by omega)]
      exact h _ (by omega)
    · rw [docBlock_getD bs (bi := bi) (m := 32 + m) (by omega)]
      exact h _ (by omega)

/-! ### `ascii_bytes` at the hand-off's carry

The staging's field asks the question the verdict's bit 0 asks: is every
document byte below `0x80`?  The loop's word answers it whenever the phase's
prefix does, because the prefix blocks are ASCII and contribute no high bit. -/

/-- **`ascii_bytes` at any word that packs to the hand-off's fold**, given the
phase's prefix.  The prefix's lanes are clear, so the whole fold's lanes are the
hand-off's fold's lanes against the split, and the whole fold's high bits are the
window's, which are the document's. -/
theorem ascii_bytes_of_fromCarry (bs : List UInt8) {k nb : Nat}
    (hk : k ≤ nb) (hnb : nb = blocksOf bs.length)
    (ascii : List (BitVec 64))
    (hcarry : packLanes ascii = bytesToNat (asciiAccFrom bs k nb))
    (hprefix : ∀ q, q < 64 * k → ((padded bs).getD q 0x00).toNat < 0x80) :
    (∀ b ∈ asciiBytes ascii, b.toNat < 0x80) ↔ ∀ x ∈ bs, x.toNat < 0x80 := by
  have hlen : (asciiAccFrom bs k nb).length = 32 :=
    asciiAccFrom_length bs hk (by omega)
  have hbytes : asciiBytes ascii = asciiAccFrom bs k nb := by
    unfold asciiBytes
    rw [hcarry, ← hlen, JsonUtf8Steps.natToBytes_bytesToNat]
  have hpre : ∀ m, m < 32 → ((asciiAcc bs k).getD m 0x00).toNat < 0x80 := by
    intro m hm
    have hk32 : m < (asciiAcc bs k).length := by
      rw [asciiAcc_length bs (by omega)]; exact hm
    have hmem := (asciiAcc_high_iff_le bs (j := k) (by omega)).mpr hprefix
    rw [getD_of_lt _ 0x00 hk32]
    exact hmem _ (List.getElem_mem hk32)
  have hdoc : (∀ x ∈ bs, x.toNat < 0x80) ↔
      ∀ b ∈ asciiAcc bs nb, b.toNat < 0x80 := by
    rw [hnb]
    exact (ascii_padded_iff bs).trans (asciiAcc_high_iff bs).symm
  have hpoint : ∀ m, m < 32 →
      (((asciiAcc bs nb).getD m 0x00).toNat < 0x80 ↔
        ((asciiAccFrom bs k nb).getD m 0x00).toNat < 0x80) := by
    intro m hm
    rw [asciiAcc_getD_split bs hk (by omega) hm, u8_or_lt, and_iff_right (hpre m hm)]
  rw [hbytes, hdoc, mem_high_iff_getD, mem_high_iff_getD,
    asciiAccFrom_length bs hk (by omega), asciiAcc_length bs (by omega)]
  constructor
  · intro h m hm
    exact (hpoint m hm).mpr (h m hm)
  · intro h m hm
    exact (hpoint m hm).mp (h m hm)

/-- **The block-zero instance.**  At `k = 0` the hand-off's carry is the
staging's own fold (`asciiAccFrom_zero`) and the prefix is vacuous, so this reads
the same clause `JsonS1BlocksStaging.ascii_bytes_of_carry` states: the hand-off
form loses nothing where the hand-off is block zero. -/
theorem ascii_bytes_of_carry_zero (bs : List UInt8) (ascii : List (BitVec 64))
    (hcarry : packLanes ascii = bytesToNat (asciiAcc bs (blocksOf bs.length))) :
    (∀ b ∈ asciiBytes ascii, b.toNat < 0x80) ↔ ∀ x ∈ bs, x.toNat < 0x80 := by
  rw [← asciiAccFrom_zero bs (blocksOf bs.length)] at hcarry
  exact ascii_bytes_of_fromCarry bs (k := 0) (nb := blocksOf bs.length)
    (Nat.zero_le _) rfl ascii hcarry (by omega)

/-- **The loop's ASCII carry at its own starting block.**  `block` is the
hand-off's block, and the phase passed blocks `0`..`block-1`, each all-ASCII.
The seed is the hand-off block's own half-OR on the phase's edge, where the loop
starts at `block+1`, and the zero word on the entry edge, where `block = 0` and
the loop starts at `0`; either way the carried word is the fold from `block`, and
the pages add the blocks up to `end`.  `end` is the document's block count at the
aligned exit. -/
structure AsciiCarryAtHandoff (bs : List UInt8) (block end_ : Nat)
    (ascii : List (BitVec 64)) : Prop where
  /-- The hand-off precedes the fold's end. -/
  bound : block ≤ end_
  /-- The blocks the phase passed are ASCII: the window's first `64 * block`
  bytes are clear. -/
  prefixHigh : ∀ q, q < 64 * block → ((padded bs).getD q 0x00).toNat < 0x80
  /-- The loop's carried word is the hand-off's fold. -/
  carry : packLanes ascii = bytesToNat (asciiAccFrom bs block end_)

/-- **`ascii_bytes` from the carry bundle**, at the document's block count. -/
theorem ascii_bytes_of_handoff {bs : List UInt8} {block n : Nat}
    {ascii : List (BitVec 64)} (hn : n = blocksOf bs.length)
    (h : AsciiCarryAtHandoff bs block n ascii) :
    (∀ b ∈ asciiBytes ascii, b.toNat < 0x80) ↔ ∀ x ∈ bs, x.toNat < 0x80 :=
  ascii_bytes_of_fromCarry bs h.bound hn ascii h.carry h.prefixHigh

/-! ### The seed and the page's steps at the hand-off's carry

An induction over the fused loop's pages starts at `%ascii.0`'s word and advances
one block per page.  `packLanes_seedAscii` is the phase's edge's seed (the
hand-off block's two halves joined, which is the hand-off fold's first factor) and
`packLanes_seedAscii_entry` the entry edge's (the zero word at block zero); the
fold's own step is `asciiAccFrom_succ`, which `packLanes_blockAsciiFrom` and
`packLanes_peelAsciiFrom` read.  `packLanes_blockAscii` is the same page step at
the staging's own fold.
-/

/-- **The phase's edge seeds the fold with the hand-off block.**  `if.then38`
joins the block's two halves into `%or.i284`, so the word that enters the fused
loop is the block's half-OR: the hand-off fold's first factor. -/
theorem packLanes_seedAscii {bs : List UInt8} {k : Nat} {bs73 bs74 : List UInt8}
    (hk : k < blocksOf bs.length)
    (h73 : bs73 = (docBlock bs k).take 32)
    (h74 : bs74 = (docBlock bs k).drop 32) :
    packLanes (fb54Or (unpackLanes 64 4 (bytesToNat bs74))
        (unpackLanes 64 4 (bytesToNat bs73))) =
      bytesToNat (asciiAccFrom bs k (k + 1)) := by
  have hblen : (docBlock bs k).length = 64 := docBlock_length_of_lt bs hk
  have h73len : bs73.length = 32 := by simp [h73, hblen]
  have h74len : bs74.length = 32 := by simp [h74, hblen]
  have h73n : (unpackLanes 64 4 (bytesToNat bs73)).length = 4 := unpackLanes_length ..
  have h74n : (unpackLanes 64 4 (bytesToNat bs74)).length = 4 := unpackLanes_length ..
  have hw73 : packLanes (unpackLanes 64 4 (bytesToNat bs73)) = bytesToNat bs73 :=
    packLanes_unpackLanes_bytesToNat bs73 h73len
  have hw74 : packLanes (unpackLanes 64 4 (bytesToNat bs74)) = bytesToNat bs74 :=
    packLanes_unpackLanes_bytesToNat bs74 h74len
  unfold fb54Or
  rw [packLanes_or4 h74n h73n, hw74, hw73,
    asciiAccFrom_succ bs (Nat.le_refl k), asciiAccFrom_self]
  have hbh : blockHalfOr bs k = List.zipWith (fun x y => x ||| y) bs73 bs74 := by
    unfold blockHalfOr
    rw [h73, h74]
  rw [hbh, bytesToNat_zipWith_or (List.replicate 32 (0x00 : UInt8))
      (List.zipWith (fun x y => x ||| y) bs73 bs74)
      (by rw [List.length_replicate, List.length_zipWith, h73len, h74len,
        Nat.min_self]),
    JsonS1BlocksStaging.bytesToNat_replicate_zero, Nat.zero_or,
    bytesToNat_zipWith_or bs73 bs74 (by rw [h73len, h74len])]
  exact Nat.or_comm _ _

/-- **The entry edge's seed is the zero word.**  `%ascii.0`'s `entry` incoming is
the zero splat, and that edge's hand-off block is zero. -/
theorem packLanes_seedAscii_entry (bs : List UInt8) :
    packLanes (List.replicate 4 (0 : BitVec 64)) =
      bytesToNat (asciiAccFrom bs 0 0) := by
  rw [asciiAccFrom_self, JsonS1BlocksStaging.packLanes_replicate_zero,
    JsonS1BlocksStaging.bytesToNat_replicate_zero]

/-- **One page's ASCII step at the hand-off's carry.** -/
theorem packLanes_blockAsciiFrom {bs : List UInt8} {k i : Nat} {bs73 bs74 : List UInt8}
    {ascii : List (BitVec 64)}
    (hk : k ≤ i)
    (hi : i < blocksOf bs.length)
    (h73 : bs73 = (docBlock bs i).take 32)
    (h74 : bs74 = (docBlock bs i).drop 32)
    (hasciilen : ascii.length = 4)
    (hacc : packLanes ascii = bytesToNat (asciiAccFrom bs k i)) :
    packLanes (fb54Or (fb54Or (unpackLanes 64 4 (bytesToNat bs74))
        (unpackLanes 64 4 (bytesToNat bs73))) ascii) =
      bytesToNat (asciiAccFrom bs k (i + 1)) := by
  have hblen : (docBlock bs i).length = 64 := docBlock_length_of_lt bs hi
  have h73len : bs73.length = 32 := by simp [h73, hblen]
  have h74len : bs74.length = 32 := by simp [h74, hblen]
  have h73n : (unpackLanes 64 4 (bytesToNat bs73)).length = 4 := unpackLanes_length ..
  have h74n : (unpackLanes 64 4 (bytesToNat bs74)).length = 4 := unpackLanes_length ..
  have hw73 : packLanes (unpackLanes 64 4 (bytesToNat bs73)) = bytesToNat bs73 :=
    packLanes_unpackLanes_bytesToNat bs73 h73len
  have hw74 : packLanes (unpackLanes 64 4 (bytesToNat bs74)) = bytesToNat bs74 :=
    packLanes_unpackLanes_bytesToNat bs74 h74len
  unfold fb54Or
  rw [packLanes_or4 (by simp [List.length_zipWith, h74n, h73n]) hasciilen,
    packLanes_or4 h74n h73n, hw74, hw73, hacc]
  have hbh : blockHalfOr bs i = List.zipWith (fun x y => x ||| y) bs73 bs74 := by
    unfold blockHalfOr
    rw [h73, h74]
  rw [asciiAccFrom_succ bs hk,
    bytesToNat_zipWith_or _ _
      (by rw [asciiAccFrom_length bs hk (by omega), blockHalfOr_length bs hi]),
    hbh, bytesToNat_zipWith_or _ _ (by rw [h73len, h74len])]
  exact or3_comm _ _ _

/-- **One page's ASCII step, at the successor carry, at the hand-off's fold.** -/
theorem fusedAscii_packFrom {c : FusedCarry} {bs : List UInt8} {bs73 bs74 : List UInt8}
    {k : Nat}
    (hk : k ≤ c.i.toNat)
    (hi : c.i.toNat < blocksOf bs.length)
    (h73 : bs73 = (docBlock bs c.i.toNat).take 32)
    (h74 : bs74 = (docBlock bs c.i.toNat).drop 32)
    (hasciilen : c.ascii.length = 4)
    (hacc : packLanes c.ascii = bytesToNat (asciiAccFrom bs k c.i.toNat)) :
    packLanes (fusedAscii c bs73 bs74) =
      bytesToNat (asciiAccFrom bs k (c.i.toNat + 1)) := by
  show packLanes (fb54Or (fb54Or (unpackLanes 64 4 (bytesToNat bs74))
      (unpackLanes 64 4 (bytesToNat bs73))) c.ascii) =
    bytesToNat (asciiAccFrom bs k (c.i.toNat + 1))
  exact packLanes_blockAsciiFrom hk hi h73 h74 hasciilen hacc

/-- **The peel's ASCII word at the hand-off's carry.**  The peel's `%or.i279` is
its two windows' join OR-ed into the loop's carried word, so the word packs to
the hand-off's fold at the document's block count. -/
theorem packLanes_peelAsciiFrom {n : BitVec 64} {b : Nat} {bs136 bs137 : List UInt8}
    {ascii : List (BitVec 64)} {st0 st9 st15 prevS andv shr : BitVec 64}
    {ent : Nat} {conv prevAscii : BitVec 32} {bs : List UInt8} {k : Nat}
    (hk : k ≤ shr.toNat)
    (hsucc : shr.toNat + 1 = blocksOf bs.length)
    (h136 : bs136 = (docBlock bs shr.toNat).take 32)
    (h137 : bs137 = (docBlock bs shr.toNat).drop 32)
    (hasciilen : ascii.length = 4)
    (hacc : packLanes ascii = bytesToNat (asciiAccFrom bs k shr.toNat)) :
    packLanes (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent
        conv prevAscii).or279 =
      bytesToNat (asciiAccFrom bs k (blocksOf bs.length)) := by
  have hblen : (docBlock bs shr.toNat).length = 64 :=
    docBlock_length_of_lt bs (by omega)
  have h136len : bs136.length = 32 := by simp [h136, hblen]
  have h137len : bs137.length = 32 := by simp [h137, hblen]
  have h136n : (unpackLanes 64 4 (bytesToNat bs136)).length = 4 := unpackLanes_length ..
  have h137n : (unpackLanes 64 4 (bytesToNat bs137)).length = 4 := unpackLanes_length ..
  have hw136 : packLanes (unpackLanes 64 4 (bytesToNat bs136)) = bytesToNat bs136 :=
    packLanes_unpackLanes_bytesToNat bs136 h136len
  have hw137 : packLanes (unpackLanes 64 4 (bytesToNat bs137)) = bytesToNat bs137 :=
    packLanes_unpackLanes_bytesToNat bs137 h137len
  show packLanes (List.zipWith (fun x y => x ||| y)
      (List.zipWith (fun x y => x ||| y)
        (unpackLanes 64 4 (bytesToNat bs137))
        (unpackLanes 64 4 (bytesToNat bs136))) ascii) = _
  rw [packLanes_or4 (by simp [List.length_zipWith, h137n, h136n]) hasciilen,
    packLanes_or4 h137n h136n, hw137, hw136, hacc]
  have hbh : blockHalfOr bs shr.toNat =
      List.zipWith (fun x y => x ||| y) bs136 bs137 := by
    unfold blockHalfOr
    rw [h136, h137]
  rw [← hsucc, asciiAccFrom_succ bs hk,
    bytesToNat_zipWith_or _ _
      (by rw [asciiAccFrom_length bs hk (by omega),
        blockHalfOr_length bs (by omega)]),
    hbh, bytesToNat_zipWith_or _ _ (by rw [h136len, h137len])]
  exact or3_comm _ _ _

/-- **The peeled arm's ASCII field at the hand-off's carry.**  The peel's
`%or.i279` is the hand-off's fold at the block count, so the staging's
`ascii_bytes` clause is the document's, given the phase's prefix. -/
theorem ascii_bytes_of_peelAsciiFrom {n : BitVec 64} {b : Nat} {bs136 bs137 : List UInt8}
    {ascii : List (BitVec 64)} {st0 st9 st15 prevS andv shr : BitVec 64}
    {ent : Nat} {conv prevAscii : BitVec 32} {bs : List UInt8} {k : Nat}
    (hk : k ≤ shr.toNat)
    (hsucc : shr.toNat + 1 = blocksOf bs.length)
    (h136 : bs136 = (docBlock bs shr.toNat).take 32)
    (h137 : bs137 = (docBlock bs shr.toNat).drop 32)
    (hasciilen : ascii.length = 4)
    (hacc : packLanes ascii = bytesToNat (asciiAccFrom bs k shr.toNat))
    (hprefix : ∀ q, q < 64 * k → ((padded bs).getD q 0x00).toNat < 0x80) :
    (∀ b' ∈ asciiBytes (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv
        shr ent conv prevAscii).or279, b'.toNat < 0x80) ↔
      ∀ x ∈ bs, x.toNat < 0x80 := by
  have hpack := packLanes_peelAsciiFrom (n := n) (b := b)
    (bs136 := bs136) (bs137 := bs137) (ascii := ascii)
    (st0 := st0) (st9 := st9) (st15 := st15) (prevS := prevS) (andv := andv)
    (shr := shr) (ent := ent) (conv := conv) (prevAscii := prevAscii) (bs := bs)
    (k := k) hk hsucc h136 h137 hasciilen hacc
  exact ascii_bytes_of_fromCarry bs (by omega) rfl
    (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent
      conv prevAscii).or279 hpack hprefix

/-! ### The staging at the hand-off

The record's three fields, assembled from the carried words at the hand-off's
fold.  The remaining conjuncts — the entry array, the escape stream and count,
and the `UnchangedOutside` frame — are `JsonS1BlocksCompose`'s memory
obligations, not the verdict's. -/

/-- **The staging's three fields, from the carried words at the hand-off.**  The
ASCII field is `ascii_bytes_of_handoff`; the accumulator and the error bit are
the staging's own readings, which the hand-off does not reach. -/
theorem staging_of_handoff (bs : List UInt8) (n nb : Nat) (gate : Bool)
    (ascii u8k : List (BitVec 64)) (err : BitVec 1) {k : Nat}
    (hascii_len : ascii.length = 4) (hacc_len : u8k.length = 4)
    (hn : n = bs.length) (hnb : nb = blocksOf bs.length)
    (hcarry : AsciiCarryAtHandoff bs k nb ascii)
    (hacc : packLanes u8k = bytesToNat (klAll gate bs))
    (herr : err = 1 ↔ ¬ (u8k.all (fun x => decide (x = 0x00)) = true) ∨
      (n ≠ 0 ∧ klTailByte (klByte bs (n - 1)) = true)) :
    VerdictStaging ascii u8k bs n nb gate err :=
  ⟨hascii_len, hacc_len, hn, hnb, ascii_bytes_of_handoff hnb hcarry, hacc, herr⟩

/-- **The aligned exit's staging at the hand-off's fold**, the counterpart of
`staging_of_loopExit`: at the loop's bound equal to the document's block count,
the carried words are the record's three fields, with the ASCII word read at the
hand-off's block rather than at block zero. -/
theorem staging_of_loopExit_handoff {bs : List UInt8} {n nb : Nat} {gate : Bool}
    {ascii u8k : List (BitVec 64)} {err : BitVec 1} {i k : Nat}
    (hn : n = bs.length) (hnb : nb = blocksOf bs.length) (hi : i = nb)
    (hk : k ≤ i)
    (hasciilen : ascii.length = 4) (hu8klen : u8k.length = 4)
    (hprefix : ∀ q, q < 64 * k → ((padded bs).getD q 0x00).toNat < 0x80)
    (hascii : packLanes ascii = bytesToNat (asciiAccFrom bs k i))
    (haccK : packLanes u8k = bytesToNat (klAcc bs i))
    (herr : err = 1 ↔ ¬ (u8k.all (fun x => decide (x = 0x00)) = true) ∨
      (n ≠ 0 ∧ klTailByte (klByte bs (n - 1)) = true)) :
    VerdictStaging ascii u8k bs n nb gate err := by
  refine staging_of_handoff bs n nb gate ascii u8k err hasciilen hu8klen hn hnb
    ⟨by omega, hprefix, ?_⟩ ?_ herr
  · rw [← hi]
    exact hascii
  · exact acc_pack_of_klAcc bs gate nb u8k hnb (by rw [← hi]; exact haccK)

/-- **The staging at the loop's exit with the hand-off's ASCII carry**, the
counterpart of `staging_of_exitFacts`: the carried words are read at the exit's
own index (`c.i`, which `FusedExit.bound_reached` pins to the loop's bound), and
`LoopExitFacts.arrAscii` states the ASCII field at block zero, where this takes
the hand-off's carry instead. -/
theorem staging_of_exitFacts_handoff {bs : List UInt8} {c : FusedCarry}
    {n nb : Nat} {gate : Bool} {err : BitVec 1} {k : Nat}
    (hn : n = bs.length) (hnb : nb = blocksOf bs.length)
    (hic : c.i.toNat = nb) (hk : k ≤ c.i.toNat)
    (hasciilen : c.ascii.length = 4) (hu8klen : c.u8k.length = 4)
    (hprefix : ∀ q, q < 64 * k → ((padded bs).getD q 0x00).toNat < 0x80)
    (hascii : packLanes c.ascii = bytesToNat (asciiAccFrom bs k c.i.toNat))
    (hacc : packLanes c.u8k = bytesToNat (klAll gate bs))
    (herr : err = 1 ↔ ¬ (c.u8k.all (fun x => decide (x = 0x00)) = true) ∨
      (n ≠ 0 ∧ klTailByte (klByte bs (n - 1)) = true)) :
    VerdictStaging c.ascii c.u8k bs n nb gate err :=
  staging_of_handoff bs n nb gate c.ascii c.u8k err hasciilen hu8klen hn hnb
    ⟨by omega, hprefix, by rw [← hic]; exact hascii⟩ hacc herr

/-! ### Axiom footprints

Every statement reads the emitted body's definitions, the staging's fold and the
window's.  The reports below name each carrier; none reaches `sorryAx` or a
choice principle beyond the quotient and propositional extensionality the
library already carries. -/

#print axioms LeanLLVM.Refinement.JsonS1BlocksHandoff.u8_or_assoc
#print axioms LeanLLVM.Refinement.JsonS1BlocksHandoff.asciiAccFrom_zero
#print axioms LeanLLVM.Refinement.JsonS1BlocksHandoff.asciiAccFrom_succ
#print axioms LeanLLVM.Refinement.JsonS1BlocksHandoff.asciiAccFrom_length
#print axioms LeanLLVM.Refinement.JsonS1BlocksHandoff.asciiAccFrom_getD
#print axioms LeanLLVM.Refinement.JsonS1BlocksHandoff.foldl_or_range_split
#print axioms LeanLLVM.Refinement.JsonS1BlocksHandoff.asciiAcc_getD_split
#print axioms LeanLLVM.Refinement.JsonS1BlocksHandoff.mem_high_iff_getD
#print axioms LeanLLVM.Refinement.JsonS1BlocksHandoff.asciiAcc_getD_high_iff_le
#print axioms LeanLLVM.Refinement.JsonS1BlocksHandoff.asciiAcc_high_iff_le
#print axioms LeanLLVM.Refinement.JsonS1BlocksHandoff.ascii_bytes_of_fromCarry
#print axioms LeanLLVM.Refinement.JsonS1BlocksHandoff.ascii_bytes_of_carry_zero
#print axioms LeanLLVM.Refinement.JsonS1BlocksHandoff.AsciiCarryAtHandoff
#print axioms LeanLLVM.Refinement.JsonS1BlocksHandoff.ascii_bytes_of_handoff
#print axioms LeanLLVM.Refinement.JsonS1BlocksHandoff.packLanes_seedAscii
#print axioms LeanLLVM.Refinement.JsonS1BlocksHandoff.packLanes_seedAscii_entry
#print axioms LeanLLVM.Refinement.JsonS1BlocksHandoff.packLanes_blockAsciiFrom
#print axioms LeanLLVM.Refinement.JsonS1BlocksHandoff.fusedAscii_packFrom
#print axioms LeanLLVM.Refinement.JsonS1BlocksHandoff.packLanes_peelAsciiFrom
#print axioms LeanLLVM.Refinement.JsonS1BlocksHandoff.ascii_bytes_of_peelAsciiFrom
#print axioms LeanLLVM.Refinement.JsonS1BlocksHandoff.staging_of_handoff
#print axioms LeanLLVM.Refinement.JsonS1BlocksHandoff.staging_of_loopExit_handoff
#print axioms LeanLLVM.Refinement.JsonS1BlocksHandoff.staging_of_exitFacts_handoff

end LeanLLVM.Refinement.JsonS1BlocksHandoff
