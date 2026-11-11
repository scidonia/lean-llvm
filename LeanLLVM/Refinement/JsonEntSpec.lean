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

end LeanLLVM.Refinement.JsonScanSpec
