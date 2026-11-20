/-
The entry stream's specification: the scalar word, its run starts, the entry word,
the `lim` tail and the table row the two position emitters read.

`JsonScanSpec` holds the six masks the stage-1 classifier computes over one
sixty-four-lane block, each proved equal to the extracted unit's registers by
`s1_masks_refines`.  The entry word consumes four of them and nothing else:

* `specScalar64` is the complement of the unescaped-quote, delimiter,
  in-string and whitespace masks — a derived instance of that vocabulary, not a
  fifth mask and not a byte predicate of its own.  It depends on the carry
  through `specInString64`, which is why it cannot be the carry-free
  `maskOfListWith` fold: the fold takes the classifier's state, and the string
  interior is what makes a run start impossible inside a string.
* `scalarStarts64` is the run-start word of a lane mask, `S & ~((S << 1) | S₆₃)`
  with the previous block's top lane supplied as a `Bool` — the carry the loop
  keeps in memory, which the harness reads as `S >> 63` and which no extracted
  unit takes as a parameter.
* `entryMask64` joins the unescaped quotes, the delimiters outside strings and
  the scalar starts.  `structuralOnly64` is the `S1F_GRAIN=1` granularity and is
  specified, not claimed as measured behaviour, because the measured build does
  not select it.

The `lim` tail is the block's last window: `limMask` keeps the lanes below the
document's end and `positionsOf` reads any mask as the block-base-relative
positions it names.  `pos8Row` is one row of the eight-entry table the POS8
emitter indexes by mask byte, which is the specification of the loop
`xl_pos8_init` fills.

The entry word's two emitters are `kernel/json/entry.c`'s `s1f_k_pos8` and
`s1f_k_b8`.  `LeanLLVM.Refinement.JsonEntrySteps.entry_pos8_refines` and
`LeanLLVM.Refinement.JsonB8Steps.entry_b8_refines` state them against the
definitions here, over the fixtures `JsonEntryIR` pins, and `entry_mask_eq` below
is the lane-level identification the word rests on — so the masks here are the
meaning of that emission and of no other.  The pipeline that assembles the
stream and the selector that consumes it are outside this tree.

`stage1Words` below is the whole-document composition: the block loop's own
entry words, one per sixty-four-byte block, with the classifier carry and the
scalar run start carried from block to block exactly as the contracted block
unit carries them in registers.
-/
import LeanLLVM.Refinement.JsonScanSpec

namespace LeanLLVM.Refinement.JsonScanSpec

open LeanLLVM
open LeanLLVM.JSON

/-! ### The scalar word and its run starts -/

/-- The block's scalar word: the complement of the four terms the kernel writes,
stated in the specification's own masks rather than in a byte predicate of its
own.  Each term is load-bearing and none is redundant: `im` covers the string
interior *and* the opening-quote lane, `sm` is the six delimiters
(`s1f_structural`, `s1fuse.h:370-377` — not the eight-byte structural set), `qm`
is *unescaped* quotes, and a backslash is not a term at all, so a backslash
outside a string and an escaped quote outside a string are scalar under the
measured rule.  Reading `im` is why this word depends on the carry and is not a
carry-free `maskOfListWith`. -/
def specScalar64 (lo hi : Block32) (st : ClassState) : BitVec 64 :=
  ~~~ (specQuote64 lo hi st ||| specDelimiter64 lo hi st |||
        specInString64 lo hi st ||| specSpace64 lo hi st)

/-- The run-start word: `S & ~((S << 1) | prevS)`, `prevS` the previous block's
top lane, which the kernel keeps in `S1F.prevS`.  No run start can lie inside a
string, because no lane of `im` is in `S`. -/
def scalarStarts64 (s : BitVec 64) (prevS : Bool) : BitVec 64 :=
  s &&& ~~~ ((s <<< 1) ||| (if prevS then 1 else 0))

/-! ### The entry word -/

/-- The `S1F_GRAIN=1` granularity: the unescaped quotes and the delimiters
outside strings, with no scalar-run starts.  Specified for the entry word's
decomposition; not claimed as measured behaviour, because the measured build
does not set the granularity. -/
def structuralOnly64 (lo hi : Block32) (st : ClassState) : BitVec 64 :=
  specQuote64 lo hi st ||| (specDelimiter64 lo hi st &&& ~~~ specInString64 lo hi st)

/-- The entry word: unescaped quotes, delimiters outside strings, and every
scalar start. -/
def entryMask64 (lo hi : Block32) (st : ClassState) (prevS : Bool) : BitVec 64 :=
  structuralOnly64 lo hi st ||| scalarStarts64 (specScalar64 lo hi st) prevS

/-- **The entry word, lane by lane.**  For every lane `k < 64`, bit `k` of
`entryMask64 lo hi st prevS` is set exactly when lane `k` is an unescaped quote
(`specQuote64`), a delimiter outside a string (`specDelimiter64` cleared at
`specInString64`), or the first lane of a scalar run: a lane of `specScalar64`
whose predecessor — lane `k - 1`, or the previous block's top lane `prevS` at
`k = 0` — is not scalar.  That reading of `scalarStarts64` is the whole
content of the run-start word, and the complement's four terms are the ones
`specScalar64` names, so no lane outside them can start a run. -/
theorem entry_mask_eq (lo hi : Block32) (st : ClassState) (prevS : Bool) (k : Nat)
    (hk : k < 64) :
    (entryMask64 lo hi st prevS).getLsbD k =
      ((specQuote64 lo hi st).getLsbD k ||
        ((specDelimiter64 lo hi st).getLsbD k && !(specInString64 lo hi st).getLsbD k) ||
        ((specScalar64 lo hi st).getLsbD k &&
          !(if k = 0 then prevS else (specScalar64 lo hi st).getLsbD (k - 1)))) := by
  simp only [entryMask64, structuralOnly64, scalarStarts64, BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitLanes.getLsbD_not_of_lt _ hk, BitVec.getLsbD_shiftLeft]
  rw [show decide (k < 64) = true from decide_eq_true hk, Bool.true_and]
  by_cases hk0 : k = 0
  · subst hk0
    by_cases hp : prevS <;> simp [hp]
  · have hk1 : ¬ k < 1 := by omega
    rw [show decide (k < 1) = false from decide_eq_false hk1, Bool.not_false, Bool.true_and]
    have hcarry : (if prevS then (1 : BitVec 64) else 0).getLsbD k = false := by
      by_cases hp : prevS
      · rw [ite_eq_left hp, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
          BitVec.getLsbD_ofNat]
        rw [show (1 : Nat).testBit k = false from
          Nat.testBit_lt_two_pow (by
            have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
            omega)]
        simp
      · rw [ite_eq_right hp]
        exact BitVec.getLsbD_zero
    rw [hcarry]
    simp [hk0]

/-! ### The tail, the positions and the table -/

/-- The tail mask: `if lim < 64 then (1 <<< lim) - 1 else all-ones`. -/
def limMask (lim : Nat) : BitVec 64 :=
  if lim < 64 then (1 <<< lim) - 1 else BitVec.ofInt 64 (-1)

/-- A mask's positions, from a block base: `setLanes` mapped to `base + lane`. -/
def positionsOf (m : BitVec 64) (base : Nat) : List Nat :=
  (BitLanes.setLanes m).map (fun k => base + k)

/-- One row of the kernel's table: the set lanes of the mask byte, then zeros to
eight entries.  `xl_pos8_init` fills exactly this rule; the route compares the
object's exported table against it row by row. -/
def pos8Row (m : Nat) : List (BitVec 32) :=
  ((BitLanes.setLanes (BitVec.ofNat 8 m)).map (fun k => BitVec.ofNat 32 k)) ++
    List.replicate (8 - (BitLanes.setLanes (BitVec.ofNat 8 m)).length) 0

/-! ### The document's block grid -/

/-- The number of sixty-four-byte blocks a document of length `n` occupies.  It is
the block unit's trip count, `(n + 63) >> 6`, and the entry stream's word count. -/
def blocksOf (n : Nat) : Nat := (n + 63) / 64

/-- The document padded with zeroes to a whole number of blocks: the window the
block unit reads.  The classifier reads all sixty-four bytes of the last block
unconditionally, so the caller stages this window rather than the document. -/
def padded (bs : List UInt8) : List UInt8 :=
  bs ++ List.replicate (64 * blocksOf bs.length - bs.length) 0

theorem blocksOf_le (n : Nat) : n ≤ 64 * blocksOf n := by
  unfold blocksOf
  have hq := Nat.div_add_mod (n + 63) 64
  have hr := Nat.mod_lt (n + 63) (by decide : 0 < 64)
  omega

theorem blocksOf_lt (n : Nat) : 64 * blocksOf n < n + 64 := by
  unfold blocksOf
  have hq := Nat.div_add_mod (n + 63) 64
  have hr := Nat.mod_lt (n + 63) (by decide : 0 < 64)
  omega

theorem padded_length (bs : List UInt8) :
    (padded bs).length = 64 * blocksOf bs.length := by
  unfold padded
  rw [List.length_append, List.length_replicate]
  have h := blocksOf_le bs.length
  omega

/-- Every block of the padded window reads at its own offset. -/
theorem padded_drop (bs : List UInt8) (i : Nat) :
    (padded bs).drop (64 * i) =
      (bs ++ List.replicate (64 * blocksOf bs.length - bs.length) 0).drop
        (64 * i) := rfl

theorem padded_drop_length (bs : List UInt8) {i : Nat} (hi : i < blocksOf bs.length) :
    ((padded bs).drop (64 * i)).length = 64 * (blocksOf bs.length - i) := by
  rw [List.length_drop, padded_length]
  have := Nat.mul_le_mul_left 64 (Nat.le_of_lt hi)
  omega

/-- The block at `i`, as the two halves the classifier reads.  A block past the
end reads as zeroes, which the tail clamp already hides; the definitions are total
so that `blocksOf` alone decides the loop's extent. -/
def blockLo (p : List UInt8) (i : Nat) : Block32 :=
  fun j => (p.drop (64 * i)).getD j.1 0

/-- The high half of the block at `i`. -/
def blockHi (p : List UInt8) (i : Nat) : Block32 :=
  fun j => (p.drop (64 * i + 32)).getD j.1 0

theorem blockHi_bound (bs : List UInt8) {i k : Nat} (hi : i < blocksOf bs.length)
    (hk : k < 64) (hk32 : 32 ≤ k) :
    k - 32 < ((padded bs).drop (64 * i + 32)).length := by
  rw [List.length_drop, padded_length]
  have hb : 64 * i + 64 ≤ 64 * blocksOf bs.length := by
    have h := Nat.mul_le_mul_left 64 (show i + 1 ≤ blocksOf bs.length from by omega)
    rwa [Nat.mul_add, Nat.mul_one] at h
  have hge : 32 ≤ 64 * blocksOf bs.length - (64 * i + 32) := by
    rw [Nat.le_sub_iff_add_le (by omega : 64 * i + 32 ≤ 64 * blocksOf bs.length)]
    omega
  have hsub : k - 32 < 32 := by omega
  exact Nat.lt_of_lt_of_le hsub hge

/-- A thirty-two-byte prefix read back as the block half it is. -/
theorem take32_ofFn (p : List UInt8) (h : 32 ≤ p.length) :
    p.take 32 = List.ofFn (fun j : Fin 32 => p.getD j.1 0) := by
  apply List.ext_getElem
  · rw [List.length_take, Nat.min_eq_left h]; simp
  · intro k h1 h2
    simp only [List.getElem_ofFn, List.getElem_take]
    have hk : k < p.length := by
      rw [List.length_take] at h1
      omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]

/-- The low half of block `i`, as the bytes the window read returns. -/
theorem take32_blockLo (bs : List UInt8) {i : Nat} (hi : i < blocksOf bs.length) :
    ((padded bs).drop (64 * i)).take 32 = List.ofFn (blockLo (padded bs) i) :=
  take32_ofFn _ (by
    rw [padded_drop_length bs hi]
    have : 1 ≤ blocksOf bs.length - i := by omega
    omega)

/-- The high half of block `i`, as the bytes the window read returns. -/
theorem take32_blockHi (bs : List UInt8) {i : Nat} (hi : i < blocksOf bs.length) :
    ((padded bs).drop (64 * i + 32)).take 32 = List.ofFn (blockHi (padded bs) i) :=
  take32_ofFn _ (by
    rw [List.length_drop, padded_length]
    have hb : 64 * i + 64 ≤ 64 * blocksOf bs.length := by
      have h := Nat.mul_le_mul_left 64 (show i + 1 ≤ blocksOf bs.length from by omega)
      rwa [Nat.mul_add, Nat.mul_one] at h
    omega)

/-! ### The document's entry words -/

/-- The run start the block at `i` is entered with: zero for the first block,
otherwise the previous block's top scalar lane. -/
def stage1PrevS (bs : List UInt8) (i : Nat) : Bool :=
  if i = 0 then false
  else
    (specScalar64 (blockLo (padded bs) (i - 1)) (blockHi (padded bs) (i - 1))
      (classCarryAt (padded bs) ⟨false, false⟩ (64 * (i - 1)))).getLsbD 63

/-- The entry word the block at `i` emits: the block's composition at the carry
the document's prefix leaves, clamped past the document's end. -/
def stage1Word (bs : List UInt8) (i : Nat) : BitVec 64 :=
  entryMask64 (blockLo (padded bs) i) (blockHi (padded bs) i)
      (classCarryAt (padded bs) ⟨false, false⟩ (64 * i)) (stage1PrevS bs i) &&&
    limMask (bs.length - 64 * i)

/-- The document's entry words, one per block, in block order. -/
def stage1Words (bs : List UInt8) : List (BitVec 64) :=
  (List.range (blocksOf bs.length)).map (stage1Word bs)

theorem stage1Words_length (bs : List UInt8) :
    (stage1Words bs).length = blocksOf bs.length := by
  simp [stage1Words]

/-- The first `i` entry words are the words of the first `i` blocks. -/
theorem stage1Words_take (bs : List UInt8) (i : Nat) :
    (stage1Words bs).take i =
      (List.range (min i (blocksOf bs.length))).map (stage1Word bs) := by
  unfold stage1Words
  rw [← List.map_take, List.take_range]

/-- The word at block `i`, read out of the list. -/
theorem stage1Words_getElem (bs : List UInt8) {i : Nat} (hi : i < blocksOf bs.length) :
    (stage1Words bs)[i]'((stage1Words_length bs).symm ▸ hi) = stage1Word bs i := by
  unfold stage1Words
  rw [List.getElem_map, List.getElem_range]

/-! ### The tail clamp, in the body's own shape -/

/-- The clamp the emitted body computes: `%sub16` on the `%cmp14` arm, and `-1`
otherwise.  The `if` is the body's `select`. -/
def clampWord (lim : Nat) : BitVec 64 :=
  if lim < 64 then ~~~ (BitVec.ofInt 64 (-1) <<< lim) else BitVec.ofInt 64 (-1)

theorem shiftLeft_allOnes_getLsbD {lim k : Nat} (hk : k < 64) :
    (BitVec.ofInt 64 (-1) <<< lim).getLsbD k = decide (lim ≤ k) := by
  rw [BitVec.getLsbD_shiftLeft, decide_eq_true hk, Bool.true_and,
    show BitVec.ofInt 64 (-1) = BitVec.allOnes 64 from rfl]
  by_cases h : lim ≤ k
  · have hfalse : ¬ (k < lim) := by omega
    have hlt64 : k - lim < 64 := Nat.lt_of_le_of_lt (Nat.sub_le k lim) hk
    rw [decide_eq_false hfalse]
    simp only [Bool.not_false, Bool.true_and, decide_eq_true h]
    exact LeanLLVM.Refinement.BitLanes.allOnes_getLsbD_of_lt hlt64
  · have htrue : k < lim := by omega
    rw [decide_eq_true htrue]
    simp only [Bool.not_true, Bool.false_and, decide_eq_false h]

/-- Below the width, `limMask`'s lanes are exactly those below `lim`. -/
theorem limMask_getLsbD (lim k : Nat) (hlim : lim ≤ 64) (hk : k < 64) :
    (limMask lim).getLsbD k = decide (k < lim) := by
  by_cases h : lim < 64
  · have hpow : 2 ^ lim < 2 ^ 64 := by
      have hle : 2 ^ lim ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
      have h63 : 2 ^ 63 < 2 ^ 64 := by decide
      omega
    have hpos : 0 < 2 ^ lim := Nat.two_pow_pos lim
    have htoNat : (((1 : BitVec 64) <<< lim) - 1).toNat = 2 ^ lim - 1 := by
      rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft]
      rw [show (1 : BitVec 64).toNat = 1 from rfl, Nat.shiftLeft_eq, Nat.one_mul]
      rw [Nat.mod_eq_of_lt hpow]
      rw [show 2 ^ 64 - 1 + 2 ^ lim = (2 ^ lim - 1) + 2 ^ 64 from by omega]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [limMask, if_pos h]
    show (((1 : BitVec 64) <<< lim) - 1).getLsbD k = _
    rw [BitVec.getLsbD, htoNat]
    exact BitLanes.testBit_two_pow_sub_one lim k
  · have h64 : lim = 64 := by omega
    subst h64
    rw [limMask, if_neg h]
    have hall : BitVec.ofInt 64 (-1) = BitVec.allOnes 64 := by decide
    rw [hall, BitLanes.allOnes_getLsbD_of_lt hk]
    exact (decide_eq_true hk).symm

/-- **The body's clamp is `limMask`.**  Below the block width the complement of
the all-ones shift keeps exactly the low `lim` lanes; at or above it the select
keeps the all-ones word. -/
theorem clampWord_eq_limMask (lim : Nat) (h : lim < 2 ^ 64) : clampWord lim = limMask lim := by
  by_cases hlt : lim < 64
  · rw [clampWord, if_pos hlt]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [BitLanes.getLsbD_not_of_lt _ hk, shiftLeft_allOnes_getLsbD hk,
      limMask_getLsbD lim k (by omega) hk]
    by_cases hkl : lim ≤ k
    · rw [decide_eq_true hkl, decide_eq_false (by omega)]
      rfl
    · rw [decide_eq_false hkl, decide_eq_true (by omega)]
      rfl
  · rw [clampWord, if_neg hlt, limMask, if_neg hlt]

theorem limMask_eq_allOnes {lim : Nat} (h : 64 ≤ lim) :
    limMask lim = BitVec.ofInt 64 (-1) := by
  rw [limMask, if_neg (by omega)]

end LeanLLVM.Refinement.JsonScanSpec
