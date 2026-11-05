/-
The JSON classifier's specification, in the model's own vocabulary.

`LeanLLVM/JSON/ScanBlock.lean` states what the scalar transition decides on one
block (`maskOfList`, `maskOf`, `scanBlock_correct`), and `LeanLLVM/JSON/ScanWindow.lean`
states what the stateful scanner's window fold reports (`windowOf`: the structural,
quote, backslash, content and delimiter masks, the first stop, and the carry).
What neither states is the **classifier's** interface: the candidate mask and the
in-string mask the index kernel forms from the quote, backslash and delimiter
lanes of a sixty-four-byte block, with the escape-run state carried across the
block boundary.  That interface exists only as the arithmetic of the emitted
kernel, so this module writes it down here — in the vocabulary the model already
uses.  The bridges to the block layer's fold, to its predicates and to the byte
rule's `inside` field are proved below.  The identification with
`ScanWindow.lean`'s `windowOf`/`carryAt`, and with the emitted kernel's own
registers, is **not** proved here; both are recorded as owed under "What is not
proved" below, and this module does not claim them.

## The specification decision: which quotes count

The kernel computes

    cand = (q & ~esc) | (s & ~m)

with `q` the raw quote lane mask, `esc` the escaped-quote lane mask, `s` the six
RFC 8259 structural characters, and `m` the in-string mask.  The specification's
quote component — the `q` of the candidate mask below, `quoteMask` — is

    q & ~esc,

that is, **unescaped quotes only**.  This is the decision, and it is the one place
where the other choice silently changes what the proof means:

* `m` must flip exactly on the quotes that open and close a string, because it is
  the string-state carry the next block inherits.  A `\"` inside a string is a
  quote byte that does not flip the state, so it is not in `q & ~esc`.
* The walking stage consumes candidate lanes as token starts.  If the candidate's
  quote component were the raw quote mask, `\"` would be emitted as a token start
  while `m` says the lane is inside a string: the two masks would disagree about
  the same byte, and the index stream would split a string.
* Reading `q` as "all quote bytes" and `m` as the prefix XOR of all quote bytes
  agrees with the emitted kernel on no string containing an escaped quote.  It is
  therefore not detectable by a span check on quoted JSON; only the arithmetic
  notices.

So the two readings are not interchangeable: the escaped quotes are lanes the
kernel records in `escapedQuoteMask` and deliberately keeps out of `quoteMask`,
and both masks are part of the specification.

## What the masks are

For a window of at most thirty-two bytes and an incoming `ClassState` (`inside`,
the string state; `oddRun`, the parity of the backslash run ending immediately
before the window).

The kernel's loop carries three values across a block: `%carry` (the string
state, `%carryn = ashr %m, 63`), `%open` (the run-open bit,
`%open = %bsc2 >> 63`, true when the block's last lane is a backslash) and `%ppar`
(the trailing-run parity).  `ClassState` is the pair `(%carry, %ppar)`.  `%open`
is omitted because it is redundant: the parity plus the contiguous bytes on both
sides of the boundary re-derive whether a run continues, and `classStep` toggles
on every backslash, which is exactly the run continuing across the boundary.

* `quoteMask` — lanes holding an **unescaped** quote;
* `escapedQuoteMask` — lanes holding a quote preceded by an odd backslash run;
* `delimiterMask` — lanes holding one of `, : { } [ ]`.  This is the kernel's `s`
  mask.  `ScanWindow.lean`'s `Window.delim` names a **different** mask — the lane
  where the byte rule closes a body, i.e. the closing quote — and the two must not
  be read as one;
* `backslashMask` — lanes holding `\`;
* `inStringMask` (`im`) — the **inclusive** prefix XOR of `quoteMask`, seeded with
  `inside`: bit `k` is set exactly when the scanner is inside a string after
  reading byte `k`.  The opening quote's own lane is inside; the closing quote's
  own lane is not.  This is the kernel's `m = px ^ carry`, where `px` is the
  carry-free prefix XOR of the unescaped quotes and `carry` is the all-ones or
  zero sign of the previous block's top `im` bit;
* `candidateMask` (`cand`) — lanes that are a candidate token start: an
  unescaped quote, or a delimiter that is not inside a string.

The escape rule is the kernel's: a quote is escaped exactly when the number of
backslashes immediately before it is odd, with the run continuing across the
window boundary through `oddRun`.  The rule does not consult the string state,
which is what the kernel's `esc` arithmetic does too.  `ScanBody.bodyStep` tracks
the run in its `oddRun` field, but outside a string it writes `false` for a
backslash rather than toggling, so the two carries can diverge only when a
backslash occurs outside a string — which no valid JSON text contains.  The
specification follows the kernel, because the kernel is what the emitted body
computes.

The divergence is **not** a monotone widening.  Where `bodyStep` leaves `oddRun`
false, this specification sets it true, so on such a window `escapedQuoteMask`
gains lanes, `inStringMask` loses a flip, and `candidateMask` loses the quote
that would have opened the string and gains the later delimiters the opened
string would have suppressed — three masks move in three directions.  Valid JSON
never reaches it, because a backslash is legal only inside a string; the
divergence lies outside the domain the classifier is used on, which is a domain
statement, not a safety property of the divergence.

`bodyStep_inside` states the part the masks read: on a common carry, the byte
rule's `inside` field is `inStringAfter` on every path that continues or closes,
with no hypothesis.

## The bridges

* The component predicates are the model's: `IsQuoteB` and `IsBackslashB` are
  `ScanBlock.lean`'s, and `IsDelimB` is proved to be the missing third of
  `IsStructuralB`/`IsStructOrSpaceB` (`isStructuralB_eq`, `isStructOrSpaceB_eq`).
* `pack32` is `maskOfListWith` at the block's thirty-two lanes, so the packed word
  is the block layer's fold and not a second packing; `pack32_getLsbD` reads a
  lane, and `pack32_eq_maskOf` is the instance at the scalar transition.
* `mask64` is the kernel's `zext`/`shl`/`or` join of two packed words, and
  `specMask64` applies a predicate over a two-half block.
* `maskOfList_decompose` states the scalar transition's mask as the union of the
  classifier's components and whitespace: the model's `maskOf` is the classifier's
  lane vocabulary, not a parallel one.
* `candidateMask_eq` states `cand = q | (s & ~im)` at one window, and
  `candidateMask64_eq` states it at the kernel's sixty-four-lane interface.
  Every component of both statements is a definition in this module.

## What is not proved (owed)

* **No bridge to `windowOf` or `carryAt`.**  `classWindow`, `classLane`,
  `classCarryAt` and `classStep` are a fold in `windowOf`'s shape, but they are a
  parallel fold: no theorem relates `classWindow`'s masks to the corresponding
  `windowOf` fields, and no theorem relates `classCarryAt` to `carryAt`.
  `bodyStep_inside` is the only connection to the model's byte rule, and it is a
  per-byte statement about `inside` on a common carry.  The identification is
  owed — `windowOf` carries the stop, the refusal and the clamped carry, which the
  classifier's total fold deliberately does not — and until it is proved, this
  module is the classifier's vocabulary, not yet the scanner model's classifier.
* **The sixty-four-lane masks are a transcription, not a proved bridge.**
  `specQuote64`, `specDelimiter64`, `specInString64` and `specCandidate64` are the
  two-half block the kernel computes, but nothing here relates them to the
  kernel's registers `%qmc2`, `%ssc2`, `%m` and `%cand`, and the outgoing carry
  (`%carryn`, `%pparn`, `%openn`) is neither defined nor related to
  `(classWindow ...).carry`.  Proving the kernel body against these definitions is
  the next obligation; this module only states the target.
-/

import LeanLLVM.JSON.ScanBlock
import LeanLLVM.JSON.ScanBody
import LeanLLVM.Semantics

namespace LeanLLVM.Vellum.JsonScanSpec

open LeanLLVM
open LeanLLVM.JSON

/-! ### The byte predicates

`IsQuoteB` and `IsBackslashB` are `ScanBlock.lean`'s, and the shared parser proves
through them; they are used here rather than restated.  `IsDelimB` is the missing
third of the classifier's vocabulary: the six RFC 8259 §2 structural characters,
without the quote and the backslash, which the kernel masks separately. -/

/-- The six RFC 8259 §2 structural characters the classifier masks as `s`:
`,` `:` `{` `}` `[` `]`.  The quote and the backslash are not here; the kernel
masks them in their own lanes and filters the quote by the escape mask.  This is
not `ScanWindow.Window.delim`, which is the lane where the byte rule closes a
body — the closing quote, a different mask. -/
def IsDelimB (b : UInt8) : Bool :=
  decide (b = 0x2C) || decide (b = 0x3A) || decide (b = 0x7B) ||
  decide (b = 0x7D) || decide (b = 0x5B) || decide (b = 0x5D)

/-- The model's structural set is the classifier's three components: the six
delimiters, the quote and the backslash. -/
theorem isStructuralB_eq (b : UInt8) :
    IsStructuralB b = (IsDelimB b || IsQuoteB b || IsBackslashB b) := by
  simp only [IsStructuralB, IsDelimB, IsQuoteB, IsBackslashB]
  simp only [Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

/-- The scalar transition's set is the classifier's three components plus the
four RFC 8259 §2 whitespace bytes. -/
theorem isStructOrSpaceB_eq (b : UInt8) :
    IsStructOrSpaceB b = (IsDelimB b || IsQuoteB b || IsBackslashB b || IsSpaceB b) := by
  simp only [IsStructOrSpaceB, IsStructuralB, IsDelimB, IsQuoteB, IsBackslashB, IsSpaceB]
  simp only [Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

/-! ### Packing the lanes

`pack32` is the block layer's fold at the block's own lanes, so the packed word is
`maskOfListWith` and not a second packing.  `mask64` is the kernel's join of two
packed words. -/

/-- One packed word at a per-byte decision: bit `k` is the decision on `blk k`.
This is `maskOfListWith` at the block's lanes, so the fold is `ScanBlock.lean`'s,
and `maskOf` is its instance at `IsStructOrSpaceB`. -/
def pack32 (f : UInt8 → Bool) (blk : Block32) : BitVec 32 :=
  maskOfListWith f (List.ofFn blk)

/-- The kernel's `zext`/`shl`/`or` join: the low word in bits 0..31 and the high
word in bits 32..63. -/
def mask64 (lo hi : BitVec 32) : BitVec 64 :=
  lo.setWidth 64 ||| (hi.setWidth 64 <<< 32)

/-- The specification's sixty-four-lane mask: the predicate's packed words over a
two-half block, joined.  The kernel's `%qrawc2`, `%ssc2` and `%bsc2` are the
instances at `IsQuoteB`, `IsDelimB` and `IsBackslashB`. -/
def specMask64 (f : UInt8 → Bool) (lo hi : Block32) : BitVec 64 :=
  mask64 (pack32 f lo) (pack32 f hi)

/-- The packed word is the block layer's fold, definitionally. -/
theorem pack32_eq_maskOfListWith (f : UInt8 → Bool) (blk : Block32) :
    pack32 f blk = maskOfListWith f (List.ofFn blk) := rfl

/-- The scalar transition's mask is the packing at `IsStructOrSpaceB`: the block
layer's `maskOf` is a `pack32`. -/
theorem pack32_eq_maskOf (blk : Block32) :
    pack32 IsStructOrSpaceB blk = maskOf blk := rfl

/-- Bit `k` of a packed word is the decision on lane `k`. -/
theorem pack32_getLsbD (f : UInt8 → Bool) (blk : Block32) (k : Fin 32) :
    (pack32 f blk).getLsbD k.val = f (blk k) := by
  unfold pack32
  have hlookup : (List.ofFn blk)[k.val]? = some (blk k) := by
    rw [List.getElem?_ofFn]
    simp [k.isLt]
  exact maskOfListWith_getLsbD k.isLt hlookup

/-- A bit past the word's width is clear. -/
private theorem getLsbD_false_of_ge {w : Nat} (x : BitVec w) {i : Nat} (h : w ≤ i) :
    x.getLsbD i = false := by
  rw [show x.getLsbD i = x.toNat.testBit i from rfl]
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) h))

/-- The packing is the bitcast of the lane vector: `lanesToNat` of the thirty-two
lane bits at width thirty-two, which is what the semantics' `bitcastMask` leaves
for `bitcast <32 x i1> to i32`. -/
theorem pack32_eq_bitcast (f : UInt8 → Bool) (blk : Block32) :
    pack32 f blk =
      BitVec.ofNat 32
        (lanesToNat (List.ofFn (fun k : Fin 32 => BitVec.ofBool (f (blk k))))) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [pack32_getLsbD f blk ⟨k, hk⟩]
  rw [BitVec.getLsbD_ofNat]
  rw [show decide (k < 32) = true from decide_eq_true hk, Bool.true_and]
  apply Bool.eq_iff_iff.mpr
  rw [lanesToNat_testBit]
  rw [List.getElem?_ofFn, dite_eq_left hk]
  cases hf : f (blk ⟨k, hk⟩) <;> simp [BitVec.ofBool]

/-- Bit `k` of the low word of the join is bit `k` of `lo`. -/
theorem mask64_getLsbD_lo (lo hi : BitVec 32) {k : Nat} (hk : k < 32) :
    (mask64 lo hi).getLsbD k = lo.getLsbD k := by
  unfold mask64
  rw [BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth]
  rw [show decide (k < 64) = true from decide_eq_true (by omega),
    show decide (k < 32) = true from decide_eq_true hk]
  simp

/-- Bit `32 + k` of the join is bit `k` of `hi`. -/
theorem mask64_getLsbD_hi (lo hi : BitVec 32) {k : Nat} (hk : k < 32) :
    (mask64 lo hi).getLsbD (k + 32) = hi.getLsbD k := by
  unfold mask64
  rw [BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth]
  rw [show decide (k + 32 < 64) = true from decide_eq_true (by omega),
    show decide (k + 32 < 32) = false from decide_eq_false (by omega),
    show k + 32 - 32 = k from by omega,
    show decide (k < 64) = true from decide_eq_true (by omega)]
  have hfalse : lo.getLsbD (k + 32) = false := getLsbD_false_of_ge lo (by omega)
  rw [hfalse]
  simp

/-- Bit `k` of the sixty-four-lane mask below the halfway point. -/
theorem specMask64_getLsbD_lo (f : UInt8 → Bool) (lo hi : Block32) {k : Nat}
    (hk : k < 32) :
    (specMask64 f lo hi).getLsbD k = f (lo ⟨k, hk⟩) := by
  unfold specMask64
  rw [mask64_getLsbD_lo _ _ hk]
  exact pack32_getLsbD f lo ⟨k, hk⟩

/-- Bit `32 + k` of the sixty-four-lane mask. -/
theorem specMask64_getLsbD_hi (f : UInt8 → Bool) (lo hi : Block32) {k : Nat}
    (hk : k < 32) :
    (specMask64 f lo hi).getLsbD (k + 32) = f (hi ⟨k, hk⟩) := by
  unfold specMask64
  rw [mask64_getLsbD_hi _ _ hk]
  exact pack32_getLsbD f hi ⟨k, hk⟩


/-! ### The classifier's carry

The kernel's loop carries three values across a block boundary: `%carry` (the
string state, `ashr %m, 63`), `%open` (the run-open bit, `%bsc2 >> 63`) and `%ppar`
(the trailing-run parity).  `ClassState` is the pair `(%carry, %ppar)`; `%open` is
redundant, because the parity plus the contiguous bytes on both sides of the
boundary re-derive whether a run continues.  `ScanBody.BodyState` carries the
string state and the run parity plus the pending UTF-8 requirement;
`ClassState.toBody` is the embedding, and `bodyStep_inside` below is the bridge for
the field the masks read.
-/

/-- The classifier's carry: inside a string, and the parity of the backslash run
ending immediately before the window.  This is the kernel's `(%carry, %ppar)`
pair — `%carry` the string state and `%ppar` the trailing-run parity — not the
kernel's `%open`, which is the run-open bit (the block's last lane is a
backslash) and is re-derived here from `oddRun` and the bytes. -/
structure ClassState where
  inside : Bool
  oddRun : Bool
deriving DecidableEq, Repr

/-- The scanner's state at the same two fields, with no UTF-8 requirement
outstanding.  The classifier never reads the requirement, so this is the embedding
the byte-rule bridge is stated at. -/
def ClassState.toBody (st : ClassState) : BodyState :=
  ⟨st.inside, st.oddRun, Utf8Need.none⟩

/-- An **unescaped** quote: a quote lane whose immediately preceding backslashes
number evenly.  This is the candidate mask's quote component. -/
def isUnescapedQuote (st : ClassState) (b : UInt8) : Bool :=
  IsQuoteB b && !st.oddRun

/-- An escaped quote: a quote lane preceded by an odd backslash run.  It is a quote
byte but not a string boundary. -/
def isEscapedQuote (st : ClassState) (b : UInt8) : Bool :=
  IsQuoteB b && st.oddRun

/-- The string state after the byte: an unescaped quote flips it. -/
def inStringAfter (st : ClassState) (b : UInt8) : Bool :=
  Bool.xor st.inside (isUnescapedQuote st b)

/-- The candidate decision at a lane: an unescaped quote, or a delimiter that is not
inside a string. -/
def isCandidateLane (st : ClassState) (b : UInt8) : Bool :=
  isUnescapedQuote st b || (IsDelimB b && !inStringAfter st b)

/-- One byte of the classifier's carry: the string state flips on an unescaped
quote, and the backslash-run parity toggles on a backslash and resets otherwise.
The run parity is the kernel's `esc` arithmetic, which does not consult the string
state. -/
def classStep (st : ClassState) (b : UInt8) : ClassState :=
  { inside := inStringAfter st b,
    oddRun := if IsBackslashB b then !st.oddRun else false }

/-- The carry on entry to lane `k`: the unclamped fold of `classStep` over the
window's first `k` bytes. -/
def classCarryAt (bs : List UInt8) (st : ClassState) (k : Nat) : ClassState :=
  (bs.take k).foldl classStep st

theorem classCarryAt_succ (bs : List UInt8) (st : ClassState) (k : Nat) :
    classCarryAt bs st (k + 1) =
      (match bs[k]? with
       | some b => classStep (classCarryAt bs st k) b
       | none => classCarryAt bs st k) := by
  unfold classCarryAt
  rw [List.take_add_one, List.foldl_append]
  cases h : bs[k]? with
  | none => simp
  | some b => simp

/-! ### The window fold

One pass over a window's lanes, in `windowOf`'s shape: a per-lane function that
records each mask's decision at the lane's own bit and advances the one carry.
-/

/-- What one window reports, and the carry it leaves. -/
structure ClassWindow where
  quote : BitVec 32
  escaped : BitVec 32
  delim : BitVec 32
  backslash : BitVec 32
  inString : BitVec 32
  candidate : BitVec 32
  carry : ClassState
deriving DecidableEq, Repr

/-- The window a fold starts from. -/
private def classInit (st : ClassState) : ClassWindow :=
  { quote := 0, escaped := 0, delim := 0, backslash := 0, inString := 0,
    candidate := 0, carry := st }

/-- One lane of the fold: each mask records its decision at the lane's index and
the carry advances.  Every lane is asked; nothing stops the classifier's fold. -/
private def classLane (w : ClassWindow) (p : UInt8 × Nat) : ClassWindow :=
  match p with
  | (b, k) =>
      { quote := if isUnescapedQuote w.carry b then w.quote ||| ((1 : BitVec 32) <<< k) else w.quote
        escaped := if isEscapedQuote w.carry b then w.escaped ||| ((1 : BitVec 32) <<< k) else w.escaped
        delim := if IsDelimB b then w.delim ||| ((1 : BitVec 32) <<< k) else w.delim
        backslash := if IsBackslashB b then w.backslash ||| ((1 : BitVec 32) <<< k) else w.backslash
        inString := if inStringAfter w.carry b then w.inString ||| ((1 : BitVec 32) <<< k) else w.inString
        candidate := if isCandidateLane w.carry b then w.candidate ||| ((1 : BitVec 32) <<< k) else w.candidate
        carry := classStep w.carry b }

/-- The classifier's window: the fold over the first thirty-two lanes. -/
def classWindow (bs : List UInt8) (st : ClassState) : ClassWindow :=
  (bs.zipIdx.take 32).foldl classLane (classInit st)

/-- The window's unescaped-quote mask. -/
def quoteMask (bs : List UInt8) (st : ClassState) : BitVec 32 :=
  (classWindow bs st).quote

/-- The window's escaped-quote mask. -/
def escapedQuoteMask (bs : List UInt8) (st : ClassState) : BitVec 32 :=
  (classWindow bs st).escaped

/-- The window's delimiter mask: the six RFC 8259 structural characters, the
kernel's `s` lane.  `ScanWindow.Window.delim` is the closing-quote lane, a
different mask. -/
def delimiterMask (bs : List UInt8) (st : ClassState) : BitVec 32 :=
  (classWindow bs st).delim

/-- The window's backslash mask. -/
def backslashMask (bs : List UInt8) (st : ClassState) : BitVec 32 :=
  (classWindow bs st).backslash

/-- The window's in-string mask (`im`). -/
def inStringMask (bs : List UInt8) (st : ClassState) : BitVec 32 :=
  (classWindow bs st).inString

/-- The window's candidate mask (`cand`). -/
def candidateMask (bs : List UInt8) (st : ClassState) : BitVec 32 :=
  (classWindow bs st).candidate

/-! ### Reading one lane

The fold writes each mask at the lane's own index, so a mask's bit `k` is decided by
lane `k` alone.  The helpers below are copies of `ScanWindow.lean`'s private ones.
The copies exist because the originals are private — a reason, not a virtue:
making them public there would remove this duplication — and they are facts about
the fold's list and the packed lane, not about the classifier.
-/

/-- Bit `k` of a packed lane is unaffected by a lane that is not `k`. -/
private theorem getLsbD_or_shift_of_ne {x : BitVec 32} {j k : Nat} (hjk : j ≠ k) :
    (x ||| ((1 : BitVec 32) <<< j)).getLsbD k = x.getLsbD k := by
  rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft (1 : BitVec 32) j]
  by_cases hk : k < 32
  · by_cases h : k < j
    · simp [hk, h]
    · have h0 : k - j ≠ 0 := by omega
      simp [hk, h, h0]
  · simp [hk]

/-- Bit `j` of a lane written under a condition is the lane's own bit or-ed with the
condition. -/
private theorem getLsbD_ite_or {x : BitVec 32} {c : Bool} {j : Nat} (hj : j < 32) :
    (if c = true then x ||| ((1 : BitVec 32) <<< j) else x).getLsbD j = (x.getLsbD j || c) := by
  by_cases hc : c = true
  · rw [ite_eq_left hc, hc]
    rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft (1 : BitVec 32) j]
    have h0 : j - j = 0 := by omega
    have hnn : ¬ j < j := by omega
    simp [hj, h0, hnn]
  · rw [ite_eq_right hc]
    simp [hc]

/-- Bit `k` of a lane written under a condition is untouched when the lane is not
`k`. -/
private theorem getLsbD_ite_or_ne {x : BitVec 32} {c : Bool} {j k : Nat} (hjk : j ≠ k) :
    (if c = true then x ||| ((1 : BitVec 32) <<< j) else x).getLsbD k = x.getLsbD k := by
  by_cases hc : c = true
  · rw [ite_eq_left hc]
    rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft (1 : BitVec 32) j]
    by_cases hk : k < 32
    · by_cases h : k < j
      · simp [hk, h]
      · have h0 : k - j ≠ 0 := by omega
        simp [hk, h, h0]
    · simp [hk]
  · rw [ite_eq_right hc]

/-- Lane `k` of the fold's list is the byte at `k`, while the list reaches it. -/
private theorem zipIdx_take_getElem? (bs : List UInt8) {k : Nat} (hk : k < 32) :
    (bs.zipIdx.take 32)[k]? = (bs[k]?).map (fun b => (b, k)) := by
  rw [List.getElem?_take, ite_eq_left hk, List.getElem?_zipIdx]
  simp

/-- Lane `k` of the fold's list, when the carrier has a byte there. -/
private theorem zipIdx_take_getElem?_some {bs : List UInt8} {k : Nat} {b : UInt8}
    (hk : k < 32) (hb : bs[k]? = some b) :
    (bs.zipIdx.take 32)[k]? = some (b, k) := by
  rw [zipIdx_take_getElem? bs hk, hb]
  rfl

/-- The lanes before `k` do not include `k`. -/
private theorem snd_ne_of_mem_take {bs : List UInt8} {k : Nat} (hk : k < 32)
    {p : UInt8 × Nat} (h : p ∈ (bs.zipIdx.take 32).take k) : p.2 ≠ k := by
  rw [List.mem_iff_getElem?] at h
  obtain ⟨j, hj⟩ := h
  rw [List.getElem?_take] at hj
  by_cases hjk : j < k
  · rw [ite_eq_left hjk, zipIdx_take_getElem? bs (by omega)] at hj
    cases hb : bs[j]? with
    | none => rw [hb] at hj; simp at hj
    | some c =>
        rw [hb] at hj
        simp only [Option.map_some, Option.some.injEq] at hj
        rw [← hj]
        omega
  · rw [ite_eq_right hjk] at hj
    simp at hj

/-- The lanes after `k` do not include `k`. -/
private theorem snd_ne_of_mem_drop {bs : List UInt8} {k : Nat} {p : UInt8 × Nat}
    (h : p ∈ (bs.zipIdx.take 32).drop (k + 1)) : p.2 ≠ k := by
  rw [List.mem_iff_getElem?] at h
  obtain ⟨i, hi⟩ := h
  rw [List.getElem?_drop] at hi
  by_cases h32 : k + 1 + i < 32
  · rw [zipIdx_take_getElem? bs h32] at hi
    cases hb : bs[k + 1 + i]? with
    | none => rw [hb] at hi; simp at hi
    | some c =>
        rw [hb] at hi
        simp only [Option.map_some, Option.some.injEq] at hi
        rw [← hi]
        omega
  · rw [List.getElem?_take, ite_eq_right h32] at hi
    simp at hi

/-- The fold's carry is the unclamped fold of `classStep` over the lanes' bytes. -/
private theorem fold_carry (l : List (UInt8 × Nat)) (w : ClassWindow) :
    (l.foldl classLane w).carry =
      l.foldl (fun (st : ClassState) (p : UInt8 × Nat) => classStep st p.1) w.carry := by
  induction l generalizing w with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨b, k⟩ := p
    rw [List.foldl_cons, List.foldl_cons, ih]
    rfl

/-- The fold over the first `k` lanes' steps is `classCarryAt` at `k`. -/
private theorem fold_take_carry (bs : List UInt8) (st : ClassState) :
    ∀ k ≤ 32,
      ((bs.zipIdx.take 32).take k).foldl
          (fun (st : ClassState) (p : UInt8 × Nat) => classStep st p.1) st
        = classCarryAt bs st k := by
  intro k
  induction k with
  | zero => intro _; simp [classCarryAt]
  | succ k ih =>
    intro hk
    have hk32 : k < 32 := by omega
    rw [List.take_add_one, List.foldl_append, ih (by omega)]
    cases hb : bs[k]? with
    | none =>
        rw [zipIdx_take_getElem? bs hk32, hb, classCarryAt_succ bs st k, hb]
        simp [Option.toList_none]
    | some b =>
        rw [zipIdx_take_getElem? bs hk32, hb, classCarryAt_succ bs st k, hb]
        simp [Option.toList_some]

/-- Lane `k` is the only lane that writes bit `k`, and it writes it with the
decision at the lane's carry. -/
private theorem classLane_self (w : ClassWindow) (b : UInt8) (k : Nat) (hk : k < 32) :
    (classLane w (b, k)).quote.getLsbD k =
        (w.quote.getLsbD k || isUnescapedQuote w.carry b) ∧
    (classLane w (b, k)).escaped.getLsbD k =
        (w.escaped.getLsbD k || isEscapedQuote w.carry b) ∧
    (classLane w (b, k)).delim.getLsbD k =
        (w.delim.getLsbD k || IsDelimB b) ∧
    (classLane w (b, k)).backslash.getLsbD k =
        (w.backslash.getLsbD k || IsBackslashB b) ∧
    (classLane w (b, k)).inString.getLsbD k =
        (w.inString.getLsbD k || inStringAfter w.carry b) ∧
    (classLane w (b, k)).candidate.getLsbD k =
        (w.candidate.getLsbD k || isCandidateLane w.carry b) := by
  dsimp only [classLane]
  exact ⟨getLsbD_ite_or hk, getLsbD_ite_or hk, getLsbD_ite_or hk, getLsbD_ite_or hk,
    getLsbD_ite_or hk, getLsbD_ite_or hk⟩

/-- A lane that is not `k` leaves bit `k` of every mask alone. -/
private theorem classLane_other (w : ClassWindow) (b : UInt8) (j : Nat) {k : Nat}
    (hjk : j ≠ k) :
    (classLane w (b, j)).quote.getLsbD k = w.quote.getLsbD k ∧
    (classLane w (b, j)).escaped.getLsbD k = w.escaped.getLsbD k ∧
    (classLane w (b, j)).delim.getLsbD k = w.delim.getLsbD k ∧
    (classLane w (b, j)).backslash.getLsbD k = w.backslash.getLsbD k ∧
    (classLane w (b, j)).inString.getLsbD k = w.inString.getLsbD k ∧
    (classLane w (b, j)).candidate.getLsbD k = w.candidate.getLsbD k := by
  dsimp only [classLane]
  exact ⟨getLsbD_ite_or_ne hjk, getLsbD_ite_or_ne hjk, getLsbD_ite_or_ne hjk,
    getLsbD_ite_or_ne hjk, getLsbD_ite_or_ne hjk, getLsbD_ite_or_ne hjk⟩

/-- Lanes that are not `k` leave bit `k` of every mask alone. -/
private theorem fold_no_hit (l : List (UInt8 × Nat)) (w : ClassWindow) (k : Nat)
    (hne : ∀ p ∈ l, p.2 ≠ k) :
    (l.foldl classLane w).quote.getLsbD k = w.quote.getLsbD k ∧
    (l.foldl classLane w).escaped.getLsbD k = w.escaped.getLsbD k ∧
    (l.foldl classLane w).delim.getLsbD k = w.delim.getLsbD k ∧
    (l.foldl classLane w).backslash.getLsbD k = w.backslash.getLsbD k ∧
    (l.foldl classLane w).inString.getLsbD k = w.inString.getLsbD k ∧
    (l.foldl classLane w).candidate.getLsbD k = w.candidate.getLsbD k := by
  induction l generalizing w with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons p l ih =>
    obtain ⟨b, j⟩ := p
    have hjk : j ≠ k := hne (b, j) (by simp)
    have htl : ∀ q ∈ l, q.2 ≠ k := fun q hq => hne q (List.mem_cons_of_mem _ hq)
    rw [List.foldl_cons]
    have hrec := ih (classLane w (b, j)) htl
    have hstep := classLane_other w b j hjk
    exact ⟨hrec.1.trans hstep.1, hrec.2.1.trans hstep.2.1,
      hrec.2.2.1.trans hstep.2.2.1, hrec.2.2.2.1.trans hstep.2.2.2.1,
      hrec.2.2.2.2.1.trans hstep.2.2.2.2.1, hrec.2.2.2.2.2.trans hstep.2.2.2.2.2⟩

/-- The fold split at a lane: the lanes after it fold the window the lanes up to it
leave, and the lane itself is applied last to that window. -/
private theorem foldl_lane_split (l : List (UInt8 × Nat)) (w : ClassWindow) (k : Nat)
    (p : UInt8 × Nat) (h : l[k]? = some p) :
    l.foldl classLane w =
      (l.drop (k + 1)).foldl classLane (classLane ((l.take k).foldl classLane w) p) := by
  conv => lhs; rw [← List.take_append_drop (k + 1) l]
  rw [List.foldl_append, List.take_add_one, h]
  simp

/-- The fold split at lane `k` of a window over a byte list. -/
private theorem fold_take_split (bs : List UInt8) (st : ClassState) {k : Nat} {b : UInt8}
    (hk : k < 32) (hb : bs[k]? = some b) :
    (bs.zipIdx.take 32).foldl classLane (classInit st) =
      ((bs.zipIdx.take 32).drop (k + 1)).foldl classLane
        (classLane (((bs.zipIdx.take 32).take k).foldl classLane (classInit st))
          (b, k)) :=
  foldl_lane_split _ _ k (b, k) (zipIdx_take_getElem?_some hk hb)

/-- Every mask at lane `k` is its decision at the carry the lane was entered with. -/
private theorem classWindow_lane {bs : List UInt8} {st : ClassState} {k : Nat} {b : UInt8}
    (hk : k < 32) (hb : bs[k]? = some b) :
    (classWindow bs st).quote.getLsbD k = isUnescapedQuote (classCarryAt bs st k) b ∧
    (classWindow bs st).escaped.getLsbD k = isEscapedQuote (classCarryAt bs st k) b ∧
    (classWindow bs st).delim.getLsbD k = IsDelimB b ∧
    (classWindow bs st).backslash.getLsbD k = IsBackslashB b ∧
    (classWindow bs st).inString.getLsbD k = inStringAfter (classCarryAt bs st k) b ∧
    (classWindow bs st).candidate.getLsbD k =
      isCandidateLane (classCarryAt bs st k) b := by
  have hnd : ∀ p ∈ (bs.zipIdx.take 32).drop (k + 1), p.2 ≠ k :=
    fun p hp => snd_ne_of_mem_drop hp
  have hnt : ∀ p ∈ (bs.zipIdx.take 32).take k, p.2 ≠ k :=
    fun p hp => snd_ne_of_mem_take hk hp
  have hcarry : (((bs.zipIdx.take 32).take k).foldl classLane (classInit st)).carry
      = classCarryAt bs st k := by
    rw [fold_carry, show (classInit st).carry = st from rfl]
    exact fold_take_carry bs st k (by omega)
  have hsplit := fold_take_split bs st hk hb
  have htail := fold_no_hit ((bs.zipIdx.take 32).drop (k + 1))
    (classLane (((bs.zipIdx.take 32).take k).foldl classLane (classInit st)) (b, k)) k hnd
  have hhead := fold_no_hit ((bs.zipIdx.take 32).take k) (classInit st) k hnt
  have hstep := classLane_self
    (((bs.zipIdx.take 32).take k).foldl classLane (classInit st)) b k hk
  unfold classWindow
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsplit, htail.1, hstep.1, hhead.1, hcarry]; simp [classInit]
  · rw [hsplit, htail.2.1, hstep.2.1, hhead.2.1, hcarry]; simp [classInit]
  · rw [hsplit, htail.2.2.1, hstep.2.2.1, hhead.2.2.1]; simp [classInit]
  · rw [hsplit, htail.2.2.2.1, hstep.2.2.2.1, hhead.2.2.2.1]; simp [classInit]
  · rw [hsplit, htail.2.2.2.2.1, hstep.2.2.2.2.1, hhead.2.2.2.2.1, hcarry]; simp [classInit]
  · rw [hsplit, htail.2.2.2.2.2, hstep.2.2.2.2.2, hhead.2.2.2.2.2, hcarry]; simp [classInit]

/-- Bit `k` of the unescaped-quote mask. -/
theorem quoteMask_getLsbD {bs : List UInt8} {st : ClassState} {k : Nat} {b : UInt8}
    (hk : k < 32) (hb : bs[k]? = some b) :
    (quoteMask bs st).getLsbD k = isUnescapedQuote (classCarryAt bs st k) b :=
  (classWindow_lane hk hb).1

/-- Bit `k` of the escaped-quote mask. -/
theorem escapedQuoteMask_getLsbD {bs : List UInt8} {st : ClassState} {k : Nat} {b : UInt8}
    (hk : k < 32) (hb : bs[k]? = some b) :
    (escapedQuoteMask bs st).getLsbD k = isEscapedQuote (classCarryAt bs st k) b :=
  (classWindow_lane hk hb).2.1

/-- Bit `k` of the delimiter mask. -/
theorem delimiterMask_getLsbD {bs : List UInt8} {st : ClassState} {k : Nat} {b : UInt8}
    (hk : k < 32) (hb : bs[k]? = some b) :
    (delimiterMask bs st).getLsbD k = IsDelimB b :=
  (classWindow_lane hk hb).2.2.1

/-- Bit `k` of the backslash mask. -/
theorem backslashMask_getLsbD {bs : List UInt8} {st : ClassState} {k : Nat} {b : UInt8}
    (hk : k < 32) (hb : bs[k]? = some b) :
    (backslashMask bs st).getLsbD k = IsBackslashB b :=
  (classWindow_lane hk hb).2.2.2.1

/-- Bit `k` of the in-string mask: the string state after byte `k`. -/
theorem inStringMask_getLsbD {bs : List UInt8} {st : ClassState} {k : Nat} {b : UInt8}
    (hk : k < 32) (hb : bs[k]? = some b) :
    (inStringMask bs st).getLsbD k = inStringAfter (classCarryAt bs st k) b :=
  (classWindow_lane hk hb).2.2.2.2.1

/-- Bit `k` of the candidate mask. -/
theorem candidateMask_getLsbD {bs : List UInt8} {st : ClassState} {k : Nat} {b : UInt8}
    (hk : k < 32) (hb : bs[k]? = some b) :
    (candidateMask bs st).getLsbD k = isCandidateLane (classCarryAt bs st k) b :=
  (classWindow_lane hk hb).2.2.2.2.2

/-- The fold leaves the carry the window's bytes leave. -/
theorem classWindow_carry (bs : List UInt8) (st : ClassState) :
    (classWindow bs st).carry = classCarryAt bs st 32 := by
  rw [classWindow, fold_carry, show (classInit st).carry = st from rfl]
  have h := fold_take_carry bs st 32 (by omega)
  rw [List.take_take, Nat.min_self] at h
  exact h


/-! ### The predicate algebra

Two facts turn the classifier's three components back into the model's predicates.
`quote_or_escaped` is the escaped-quote decision's complement: every quote lane is
exactly one of unescaped and escaped. -/

/-- Every quote lane is either unescaped or escaped, and the two are disjoint. -/
theorem quote_or_escaped (st : ClassState) (b : UInt8) :
    (isUnescapedQuote st b || isEscapedQuote st b) = IsQuoteB b := by
  unfold isUnescapedQuote isEscapedQuote
  cases h : IsQuoteB b <;> cases ho : st.oddRun <;> rfl

/-! ### The byte rule's inside field

`ScanBody.bodyStep` is the model's byte rule.  Its `inside` component is the
classifier's in-string decision; the two agree on every path that continues or
closes, with no hypothesis: a continued byte keeps the state unless it is an
unescaped quote, and a closing quote leaves the state outside.  The classifier's
own fold additionally runs past lanes the rule refuses, because the masks are
total over the block; the bridge states the rule's own paths, not the fold's. -/

/-- The byte rule's `inside` field is `inStringAfter`: continuing keeps the state
except on an unescaped quote, and closing leaves it outside. -/
theorem bodyStep_inside (st : ClassState) (b : UInt8) :
    (∀ st', bodyStep (ClassState.toBody st) b = .cont st' →
        st'.inside = inStringAfter st b) ∧
    (bodyStep (ClassState.toBody st) b = .closed → inStringAfter st b = false) := by
  by_cases ho : st.oddRun
  · constructor
    · intro st' h
      simp [bodyStep, ClassState.toBody, ho] at h
      subst h
      simp [inStringAfter, isUnescapedQuote, ho]
    · intro h
      simp [bodyStep, ClassState.toBody, ho] at h
  · by_cases hq : IsQuoteB b = true
    · by_cases hin : st.inside
      · constructor
        · intro st' h
          simp [bodyStep, ClassState.toBody, ho, hq, hin] at h
        · intro _
          simp [inStringAfter, isUnescapedQuote, ho, hq, hin]
      · constructor
        · intro st' h
          simp [bodyStep, ClassState.toBody, ho, hq, hin] at h
          subst h
          simp [inStringAfter, isUnescapedQuote, ho, hq, hin]
        · intro h
          simp [bodyStep, ClassState.toBody, ho, hq, hin] at h
    · by_cases hb : IsBackslashB b = true
      · constructor
        · intro st' h
          simp [bodyStep, ClassState.toBody, ho, hq, hb] at h
          subst h
          simp [inStringAfter, isUnescapedQuote, ho, hq]
        · intro h
          simp [bodyStep, ClassState.toBody, ho, hq, hb] at h
      · by_cases hin : st.inside
        · by_cases hctl : decide (b < 0x20) = true
          · constructor
            · intro st' h
              simp [bodyStep, ClassState.toBody, ho, hq, hb, hin, hctl] at h
            · intro h
              simp [bodyStep, ClassState.toBody, ho, hq, hb, hin, hctl] at h
          · constructor
            · intro st' h
              simp only [bodyStep, ClassState.toBody, ho, hq, hb, hin, hctl] at h
              cases hs : Utf8Need.step .none b with
              | none => simp [hs] at h
              | some u =>
                  simp [hs] at h
                  subst h
                  simp [inStringAfter, isUnescapedQuote, ho, hq, hin]
            · intro h
              simp only [bodyStep, ClassState.toBody, ho, hq, hb, hin, hctl] at h
              cases hs : Utf8Need.step .none b <;> simp [hs] at h
        · constructor
          · intro st' h
            simp [bodyStep, ClassState.toBody, ho, hq, hb, hin] at h
            subst h
            simp [inStringAfter, isUnescapedQuote, ho, hq, hin]
          · intro h
            simp [bodyStep, ClassState.toBody, ho, hq, hb, hin] at h

/-! ### The masks as the block layer's fold -/

/-- The byte at lane `k` of a window that reaches it, as a lookup. -/
private theorem getElem?_of_lt {bs : List UInt8} {k : Nat} (hk : k < bs.length) :
    bs[k]? = some (bs[k]'hk) :=
  List.getElem?_eq_getElem hk

/-- The delimiter mask is the block layer's fold at `IsDelimB`. -/
theorem delimiterMask_eq_maskOfListWith (bs : List UInt8) (st : ClassState)
    (hlen : 32 ≤ bs.length) :
    delimiterMask bs st = maskOfListWith IsDelimB bs := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hklen : k < bs.length := by omega
  rw [delimiterMask_getLsbD hk (getElem?_of_lt hklen),
    maskOfListWith_getLsbD hk (getElem?_of_lt hklen)]

/-- The backslash mask is the block layer's fold at `IsBackslashB`. -/
theorem backslashMask_eq_maskOfListWith (bs : List UInt8) (st : ClassState)
    (hlen : 32 ≤ bs.length) :
    backslashMask bs st = maskOfListWith IsBackslashB bs := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hklen : k < bs.length := by omega
  rw [backslashMask_getLsbD hk (getElem?_of_lt hklen),
    maskOfListWith_getLsbD hk (getElem?_of_lt hklen)]

/-- The two quote masks together are the block layer's raw quote mask: the
classifier splits the quote lane by the escape state and loses no lane. -/
theorem quoteMask_or_escaped_eq (bs : List UInt8) (st : ClassState)
    (hlen : 32 ≤ bs.length) :
    quoteMask bs st ||| escapedQuoteMask bs st = maskOfListWith IsQuoteB bs := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hklen : k < bs.length := by omega
  rw [BitVec.getLsbD_or, quoteMask_getLsbD hk (getElem?_of_lt hklen),
    escapedQuoteMask_getLsbD hk (getElem?_of_lt hklen),
    maskOfListWith_getLsbD hk (getElem?_of_lt hklen), quote_or_escaped]

/-- Inserting a split atom into an or-chain: replacing `q` by the two atoms `u` and
`e` whose disjunction is `q` leaves the truth value alone. -/
private theorem or_insert (d q b s u e : Bool) (h : (u || e) = q) :
    (d || q || b || s) = (d || u || e || b || s) := by
  rw [← h]
  simp only [Bool.or_left_comm, Bool.or_comm]

/-- **The scalar transition's mask is the classifier's components.**  `maskOfList`'s
decision is the union of the delimiter, quote, escaped-quote and backslash lanes with
whitespace; the classifier and the block layer are one vocabulary, not two. -/
theorem maskOfList_decompose (bs : List UInt8) (st : ClassState)
    (hlen : 32 ≤ bs.length) :
    maskOfList bs =
      delimiterMask bs st ||| quoteMask bs st ||| escapedQuoteMask bs st |||
        backslashMask bs st ||| maskOfListWith IsSpaceB bs := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hklen : k < bs.length := by omega
  rw [maskOfList_getLsbD hk (getElem?_of_lt hklen), BitVec.getLsbD_or,
    BitVec.getLsbD_or, BitVec.getLsbD_or, BitVec.getLsbD_or,
    delimiterMask_getLsbD hk (getElem?_of_lt hklen),
    quoteMask_getLsbD hk (getElem?_of_lt hklen),
    escapedQuoteMask_getLsbD hk (getElem?_of_lt hklen),
    backslashMask_getLsbD hk (getElem?_of_lt hklen),
    maskOfListWith_getLsbD hk (getElem?_of_lt hklen)]
  rw [isStructOrSpaceB_eq]
  exact or_insert (IsDelimB (bs[k]'hklen)) (IsQuoteB (bs[k]'hklen))
    (IsBackslashB (bs[k]'hklen)) (IsSpaceB (bs[k]'hklen))
    (isUnescapedQuote (classCarryAt bs st k) (bs[k]'hklen))
    (isEscapedQuote (classCarryAt bs st k) (bs[k]'hklen))
    (quote_or_escaped _ _)

/-- **The candidate mask is `q | (s & ~im)`.**  `q` is the unescaped-quote mask,
`s` the delimiter mask and `im` the in-string mask, each a definition above; this is
the kernel's `%cand = %qm | (%ss & ~%m)` at one window. -/
theorem candidateMask_eq (bs : List UInt8) (st : ClassState) (hlen : 32 ≤ bs.length) :
    candidateMask bs st =
      quoteMask bs st ||| (delimiterMask bs st &&& ~~~inStringMask bs st) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hklen : k < bs.length := by omega
  rw [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    show decide (k < 32) = true from decide_eq_true hk, Bool.true_and,
    candidateMask_getLsbD hk (getElem?_of_lt hklen),
    quoteMask_getLsbD hk (getElem?_of_lt hklen),
    delimiterMask_getLsbD hk (getElem?_of_lt hklen),
    inStringMask_getLsbD hk (getElem?_of_lt hklen)]
  rfl

/-! ### The kernel's sixty-four lanes

The kernel reads one sixty-four-byte block as two thirty-two-byte halves and joins
their masks.  The low half leaves the carry the high half is entered with, and the
escape-run parity crosses the halfway point the same way. -/

/-- A mask over the kernel's sixty-four-lane block: the halves' folded masks joined,
the high half entered with the carry the low half left. -/
def classMask64 (f : List UInt8 → ClassState → BitVec 32) (lo hi : Block32)
    (st : ClassState) : BitVec 64 :=
  mask64 (f (List.ofFn lo) st)
    (f (List.ofFn hi) ((classWindow (List.ofFn lo) st).carry))

/-- The kernel's in-string mask over one sixty-four-byte block. -/
def specInString64 (lo hi : Block32) (st : ClassState) : BitVec 64 :=
  classMask64 inStringMask lo hi st

/-- The kernel's candidate mask over one sixty-four-byte block. -/
def specCandidate64 (lo hi : Block32) (st : ClassState) : BitVec 64 :=
  classMask64 candidateMask lo hi st

/-- The kernel's unescaped-quote mask over one sixty-four-byte block. -/
def specQuote64 (lo hi : Block32) (st : ClassState) : BitVec 64 :=
  classMask64 quoteMask lo hi st

/-- The kernel's delimiter mask over one sixty-four-byte block. -/
def specDelimiter64 (lo hi : Block32) (st : ClassState) : BitVec 64 :=
  classMask64 delimiterMask lo hi st

/-- Bit `k` below the halfway point of the joined mask. -/
theorem classMask64_getLsbD_lo (f : List UInt8 → ClassState → BitVec 32)
    (lo hi : Block32) (st : ClassState) {k : Nat} (hk : k < 32) :
    (classMask64 f lo hi st).getLsbD k = (f (List.ofFn lo) st).getLsbD k := by
  unfold classMask64
  rw [mask64_getLsbD_lo _ _ hk]

/-- Bit `32 + k` of the joined mask. -/
theorem classMask64_getLsbD_hi (f : List UInt8 → ClassState → BitVec 32)
    (lo hi : Block32) (st : ClassState) {k : Nat} (hk : k < 32) :
    (classMask64 f lo hi st).getLsbD (k + 32) =
      (f (List.ofFn hi) ((classWindow (List.ofFn lo) st).carry)).getLsbD k := by
  unfold classMask64
  rw [mask64_getLsbD_hi _ _ hk]

/-- The join commutes with disjunction. -/
theorem mask64_or (a b c d : BitVec 32) :
    mask64 a b ||| mask64 c d = mask64 (a ||| c) (b ||| d) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  by_cases hk32 : k < 32
  · rw [BitVec.getLsbD_or, mask64_getLsbD_lo _ _ hk32, mask64_getLsbD_lo _ _ hk32,
      mask64_getLsbD_lo _ _ hk32, BitVec.getLsbD_or]
  · rw [show k = (k - 32) + 32 from by omega]
    rw [BitVec.getLsbD_or, mask64_getLsbD_hi _ _ (by omega),
      mask64_getLsbD_hi _ _ (by omega), mask64_getLsbD_hi _ _ (by omega),
      BitVec.getLsbD_or]

/-- The join commutes with conjunction. -/
theorem mask64_and (a b c d : BitVec 32) :
    mask64 a b &&& mask64 c d = mask64 (a &&& c) (b &&& d) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  by_cases hk32 : k < 32
  · rw [BitVec.getLsbD_and, mask64_getLsbD_lo _ _ hk32, mask64_getLsbD_lo _ _ hk32,
      mask64_getLsbD_lo _ _ hk32, BitVec.getLsbD_and]
  · rw [show k = (k - 32) + 32 from by omega]
    rw [BitVec.getLsbD_and, mask64_getLsbD_hi _ _ (by omega),
      mask64_getLsbD_hi _ _ (by omega), mask64_getLsbD_hi _ _ (by omega),
      BitVec.getLsbD_and]

/-- The join commutes with complement. -/
theorem mask64_not (a b : BitVec 32) :
    ~~~(mask64 a b) = mask64 (~~~a) (~~~b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  by_cases hk32 : k < 32
  · rw [BitVec.getLsbD_not, mask64_getLsbD_lo _ _ hk32, mask64_getLsbD_lo _ _ hk32,
      BitVec.getLsbD_not]
    rw [show decide (k < 64) = true from decide_eq_true (by omega), Bool.true_and,
      show decide (k < 32) = true from decide_eq_true hk32, Bool.true_and]
  · rw [show k = (k - 32) + 32 from by omega]
    rw [BitVec.getLsbD_not, mask64_getLsbD_hi _ _ (by omega),
      mask64_getLsbD_hi _ _ (by omega), BitVec.getLsbD_not]
    rw [show decide ((k - 32) + 32 < 64) = true from decide_eq_true (by omega),
      Bool.true_and,
      show decide (k - 32 < 32) = true from decide_eq_true (by omega), Bool.true_and]

/-- **The kernel's candidate mask is `q | (s & ~im)` at sixty-four lanes.**  The
high half's components are its own window's, entered with the carry the low half
left, so the identity holds on the whole block and not only per half. -/
theorem candidateMask64_eq (lo hi : Block32) (st : ClassState) :
    specCandidate64 lo hi st =
      specQuote64 lo hi st |||
        (specDelimiter64 lo hi st &&& ~~~specInString64 lo hi st) := by
  unfold specCandidate64 specQuote64 specDelimiter64 specInString64 classMask64
  rw [mask64_not, mask64_and, mask64_or]
  rw [candidateMask_eq (List.ofFn lo) st (by simp),
    candidateMask_eq (List.ofFn hi) ((classWindow (List.ofFn lo) st).carry) (by simp)]


/-! ### The decision, executed

The decision above is not only prose: on `"\""` (four bytes) the lanes show it.
Lane 0 opens the string, lane 2 is the escaped quote, lane 3 closes the string.
Lane 2 is a quote byte and an escape record, and it is deliberately absent from
the candidate mask; the raw quote mask has it, and that is the reading the
specification does not take. -/

/-- `"\""` from outside a string: the candidate mask is `0b1001` (lanes 0 and 3),
the escaped quote is lane 2 alone, the in-string mask is `0b0111`, and the raw
quote mask — unescaped and escaped together — is `0b1101`.  The escaped quote at
lane 2 is the difference the specification decision makes; lane 3 is in both
masks. -/
theorem escaped_quote_witness :
    candidateMask [0x22, 0x5C, 0x22, 0x22] ⟨false, false⟩ = 0b1001 ∧
    quoteMask [0x22, 0x5C, 0x22, 0x22] ⟨false, false⟩ = 0b1001 ∧
    escapedQuoteMask [0x22, 0x5C, 0x22, 0x22] ⟨false, false⟩ = 0b100 ∧
    inStringMask [0x22, 0x5C, 0x22, 0x22] ⟨false, false⟩ = 0b0111 ∧
    (quoteMask [0x22, 0x5C, 0x22, 0x22] ⟨false, false⟩ |||
      escapedQuoteMask [0x22, 0x5C, 0x22, 0x22] ⟨false, false⟩) = 0b1101 := by
  decide

end LeanLLVM.Vellum.JsonScanSpec
