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
uses.  The bridges to the block layer's fold, to its predicates, to the byte
rule's `inside` field and to `ScanWindow.lean`'s own window fold are proved
below: on a full window with no stop, `classWindow`'s quote, backslash and
structural masks are `windowOf`'s, its closing lane is empty on both sides, and
`classCarryAt` is `carryAt` read at the two fields both states have — the carry
takes the two named conditions, and the closing-lane identification at a stop's
own lane takes `NoBackslashOutside` on top of the continuation the stop's readback
supplies — and each condition is shown necessary by a counterexample rather than
assumed.
The identification with the emitted kernel's own registers is **not** proved
here; it is recorded as owed under "What is not proved" below.

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
* **The window fold is the model's.**  On a full window with no stop,
  `windowOf_quote_eq` and `windowOf_backslash_eq` identify the model's quote and
  backslash fields with the classifier's masks, and `windowOf_structural_eq` puts
  the structural field in the classifier's component vocabulary; those three need
  only the no-stop hypothesis.  `Window.delim` — the closing-quote lane, which is
  not `delimiterMask` — is a different case, because the fold records it only on
  the branch that also records a stop: `windowOf_delim_eq_zero_of_stop_none`
  states that a no-stop window has both it and `quoteMask &&& ~~~inStringMask`
  empty, and `windowOf_delim_eq_of_close_stop` identifies the two bits at a
  closing stop's own lane, under `NoBackslashOutside` (`delim_eq_fails_outside`)
  and the stop's own continuation (`delim_eq_fails_past_stop`).
* **The carry is the model's.**  `classPart_classStep_of_cont` is one byte of
  agreement between `classStep` and `bodyStep`, at the projection
  `BodyState.classPart := ⟨inside, oddRun⟩`; `classCarryAt_eq_classPart` is the
  fold, under `ContinuesBefore bs st.toBody k` (no stop before the lane) and
  `NoBackslashOutside bs st.toBody k` (no backslash read outside a body).
  `classCarryAt_eq_classPart_of_inside` discharges the second condition for a
  window read from inside a body.  Neither condition is decorative:
  `no_stop_does_not_identify_carries` is a window that stops nowhere and reads a
  backslash outside a body, where the carries differ, and
  `close_stop_carry_diverges` is a window with a closing stop, where they differ.
  The UTF-8 field is not a hypothesis: `carryAt_oddRun_utf8` proves a run parity
  and an outstanding requirement never coincide on the fold's states, and
  `carryAt_aboveAscii` that such a requirement only wants continuation bytes.
* **Past a stop the two are different objects.**  `classCarryAt_succ_of_stop`
  states the divergence: at a lane the rule does not continue past, `carryAt`
  keeps the state on entry while `classStep` takes the step the rule refused;
  `classCarryAt_succ_closed` reads it at a closing stop, where the classifier's
  string flag is the complement of the model's.  It is a divergence, not a
  widening: the classifier neither over- nor under-approximates the scanner after
  a stop, it describes a different state.

## What is not proved (owed)

* **The bridge stops at the stop.**  The carry identifications are stated on a
  window that stops nowhere — the window shape the scanner's readback hands over —
  and the carry's also needs no backslash outside a body.  The masks are identified
  on a no-stop window, except the closing lane, which is empty there and is
  identified only at a closing stop's own lane (`windowOf_delim_eq_of_close_stop`).
  Past a stop the classifier's fold continues where `windowOf`'s holds, so no
  theorem here compares the two carries there: `classCarryAt_succ_of_stop` and
  `classCarryAt_succ_closed` are the divergence, and a refinement that reads the
  classifier's masks on a stopped window is resting on lanes the parser re-reads
  from the model, not on the identification.  A refinement stated over the
  classifier's whole window therefore owes either a no-stop hypothesis or a
  statement that its lanes past the stop are unused.
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
import LeanLLVM.JSON.ScanWindow
import LeanLLVM.Semantics
import LeanLLVM.Vellum.BitLanes

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
  rw [BitVec.getLsbD_or, BitVec.getLsbD_and,
    LeanLLVM.Vellum.BitLanes.getLsbD_not_of_lt _ hk,
    candidateMask_getLsbD hk (getElem?_of_lt hklen),
    quoteMask_getLsbD hk (getElem?_of_lt hklen),
    delimiterMask_getLsbD hk (getElem?_of_lt hklen),
    inStringMask_getLsbD hk (getElem?_of_lt hklen)]
  rfl

/-! ### The bridge to the window fold

`ScanWindow.lean`'s `windowOf` folds the byte rule and reports the masks the scanner
consumes; `classWindow` folds the classifier's arithmetic.  They are not the same fold:
`windowOf` records a stop and a refusal and holds its carry at them, while `classWindow`
asks every lane and always steps.  So the identifications below are stated where the two
folds can agree — on a full window with **no stop**, the window shape the scanner's own
readback hands over — and the places where the classifier is defined and the model is
not are named, with what they cost.

Two conditions are named, and each is proved necessary by a counterexample rather than
asserted:

* `ContinuesBefore bs st.toBody k` — the fold stops nowhere before lane `k`.
  `close_stop_carry_diverges` is a window where it fails and the carries differ.
* `NoBackslashOutside bs st.toBody k` — every backslash before lane `k` is read inside
  a body.  `no_stop_does_not_identify_carries` is a no-stop window where it fails and
  the carries differ.

Nothing else is assumed.  In particular the UTF-8 field of the model's state is not a
hypothesis: `carryAt_oddRun_utf8` proves that a run parity and an outstanding sequence
never coincide on a state the fold reaches from `ClassState.toBody`, and
`carryAt_aboveAscii` proves that such a requirement only ever wants continuation
bytes — so the classifier's silence about UTF-8 costs nothing on the fold's reachable
states.
-/

/-- The classifier's view of the model's carry: the two fields `ClassState` has.  The
UTF-8 requirement is dropped, which is why the comparison is stated here and not at
`BodyState` itself. -/
def BodyState.classPart (st : BodyState) : ClassState where
  inside := st.inside
  oddRun := st.oddRun

/-- The embedding's projection is the identity. -/
theorem ClassState.classPart_toBody (st : ClassState) : BodyState.classPart st.toBody = st := rfl

/-- A requirement that only continuation bytes satisfy: its range starts at or above
`0x80`.  `Utf8Need.step` produces one from `.none`, and a continuation leaves one, so
every state the byte rule reaches from `ClassState.toBody` has this shape.  It is what
the classifier's silence about UTF-8 needs: a byte such a requirement accepts is
neither a quote nor a backslash. -/
def Utf8Need.AboveAscii : Utf8Need → Prop
  | .none => True
  | .more _ lo _ => 0x80 ≤ lo

/-- A byte at or above `0x80` is not a quote. -/
private theorem isQuoteB_false_of_ge {b : UInt8} (h : 0x80 ≤ b) : IsQuoteB b = false := by
  unfold IsQuoteB
  rw [decide_eq_false_iff_not]
  intro hb
  subst hb
  exact absurd h (by decide)

/-- A byte at or above `0x80` is not a backslash. -/
private theorem isBackslashB_false_of_ge {b : UInt8} (h : 0x80 ≤ b) :
    IsBackslashB b = false := by
  unfold IsBackslashB
  rw [decide_eq_false_iff_not]
  intro hb
  subst hb
  exact absurd h (by decide)

/-- A quote byte is not a backslash. -/
private theorem isBackslash_false_of_quote {b : UInt8} (h : IsQuoteB b = true) :
    IsBackslashB b = false := by
  unfold IsQuoteB at h
  obtain rfl : b = 0x22 := of_decide_eq_true h
  unfold IsBackslashB
  exact decide_eq_false (by decide)

/-- A requirement produced from `.none` wants continuation bytes only. -/
private theorem step_none_aboveAscii {b : UInt8} {u : Utf8Need}
    (h : Utf8Need.step .none b = some u) : Utf8Need.AboveAscii u := by
  by_cases h1 : b < 0x80
  · have hs : Utf8Need.step .none b = some Utf8Need.none := by
      simp only [Utf8Need.step]
      rw [ite_eq_left h1]
    rw [hs] at h
    cases h
    simp [Utf8Need.AboveAscii]
  · by_cases h2 : 0xC2 ≤ b ∧ b ≤ 0xDF
    · have hs : Utf8Need.step .none b = some (Utf8Need.more 1 0x80 0xBF) := by
        simp only [Utf8Need.step]
        rw [ite_eq_right h1, ite_eq_left h2]
      rw [hs] at h
      cases h
      unfold Utf8Need.AboveAscii
      decide
    · by_cases h3 : b = 0xE0
      · have hs : Utf8Need.step .none b = some (Utf8Need.more 2 0xA0 0xBF) := by
          simp only [Utf8Need.step]
          rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]
        rw [hs] at h
        cases h
        unfold Utf8Need.AboveAscii
        decide
      · by_cases h4 : 0xE1 ≤ b ∧ b ≤ 0xEC
        · have hs : Utf8Need.step .none b = some (Utf8Need.more 2 0x80 0xBF) := by
            simp only [Utf8Need.step]
            rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_left h4]
          rw [hs] at h
          cases h
          unfold Utf8Need.AboveAscii
          decide
        · by_cases h5 : b = 0xED
          · have hs : Utf8Need.step .none b = some (Utf8Need.more 2 0x80 0x9F) := by
              simp only [Utf8Need.step]
              rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
                ite_eq_left h5]
            rw [hs] at h
            cases h
            unfold Utf8Need.AboveAscii
            decide
          · by_cases h6 : 0xEE ≤ b ∧ b ≤ 0xEF
            · have hs : Utf8Need.step .none b = some (Utf8Need.more 2 0x80 0xBF) := by
                simp only [Utf8Need.step]
                rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
                  ite_eq_right h5, ite_eq_left h6]
              rw [hs] at h
              cases h
              unfold Utf8Need.AboveAscii
              decide
            · by_cases h7 : b = 0xF0
              · have hs : Utf8Need.step .none b = some (Utf8Need.more 3 0x90 0xBF) := by
                  simp only [Utf8Need.step]
                  rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
                    ite_eq_right h5, ite_eq_right h6, ite_eq_left h7]
                rw [hs] at h
                cases h
                unfold Utf8Need.AboveAscii
                decide
              · by_cases h8 : 0xF1 ≤ b ∧ b ≤ 0xF3
                · have hs : Utf8Need.step .none b = some (Utf8Need.more 3 0x80 0xBF) := by
                    simp only [Utf8Need.step]
                    rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
                      ite_eq_right h5, ite_eq_right h6, ite_eq_right h7, ite_eq_left h8]
                  rw [hs] at h
                  cases h
                  unfold Utf8Need.AboveAscii
                  decide
                · by_cases h9 : b = 0xF4
                  · have hs : Utf8Need.step .none b = some (Utf8Need.more 3 0x80 0x8F) := by
                      simp only [Utf8Need.step]
                      rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
                        ite_eq_right h4, ite_eq_right h5, ite_eq_right h6,
                        ite_eq_right h7, ite_eq_right h8, ite_eq_left h9]
                    rw [hs] at h
                    cases h
                    unfold Utf8Need.AboveAscii
                    decide
                  · have hs : Utf8Need.step .none b = Option.none := by
                      simp only [Utf8Need.step]
                      rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
                        ite_eq_right h4, ite_eq_right h5, ite_eq_right h6,
                        ite_eq_right h7, ite_eq_right h8, ite_eq_right h9]
                    rw [hs] at h
                    cases h

/-- A requirement keeps its range above `0x80` across a byte it accepts. -/
private theorem step_aboveAscii {u : Utf8Need} (hu : Utf8Need.AboveAscii u) {b : UInt8}
    {u' : Utf8Need} (h : Utf8Need.step u b = some u') : Utf8Need.AboveAscii u' := by
  cases u with
  | none => exact step_none_aboveAscii h
  | more n lo hi =>
      unfold Utf8Need.AboveAscii at hu
      by_cases hmem : lo ≤ b ∧ b ≤ hi
      · have hstep : Utf8Need.step (.more n lo hi) b =
            some (if n ≤ 1 then Utf8Need.none else Utf8Need.more (n - 1) 0x80 0xBF) := by
          simp only [Utf8Need.step]
          rw [ite_eq_left hmem]
        rw [hstep] at h
        by_cases hn : n ≤ 1
        · rw [ite_eq_left hn] at h
          cases h
          simp [Utf8Need.AboveAscii]
        · rw [ite_eq_right hn] at h
          cases h
          show (0x80 : UInt8) ≤ 0x80
          decide
      · have hstep : Utf8Need.step (.more n lo hi) b = none := by
          simp only [Utf8Need.step]
          rw [ite_eq_right hmem]
        rw [hstep] at h
        exact absurd h (by simp)

/-- A byte an above-`0x80` requirement accepts is itself at or above `0x80`. -/
private theorem step_accepted_ge {u : Utf8Need} (hu : Utf8Need.AboveAscii u) (hn : u ≠ .none)
    {b : UInt8} {u' : Utf8Need} (h : Utf8Need.step u b = some u') : 0x80 ≤ b := by
  cases u with
  | none => exact absurd rfl hn
  | more n lo hi =>
      unfold Utf8Need.AboveAscii at hu
      by_cases hmem : lo ≤ b ∧ b ≤ hi
      · have h1 : (0x80 : UInt8).toNat ≤ lo.toNat := UInt8.le_iff_toNat_le.mp hu
        have h2 : lo.toNat ≤ b.toNat := UInt8.le_iff_toNat_le.mp hmem.1
        exact UInt8.le_iff_toNat_le.mpr (Nat.le_trans h1 h2)
      · have hstep : Utf8Need.step (.more n lo hi) b = none := by
          simp only [Utf8Need.step]
          rw [ite_eq_right hmem]
        rw [hstep] at h
        exact absurd h (by simp)

/-- **One byte, both rules.**  Where the byte rule continues, the two fields the
classifier has are `classStep`'s: the same string flag, the same run parity.  The
hypotheses are the per-lane form of the two named conditions — an odd run never
overlaps an outstanding requirement, the requirement only wants continuation bytes, and
a backslash is read inside a body — and each is used by one branch of the rule.  At the
fold the first two are **derived**, not assumed (`carryAt_oddRun_utf8`,
`carryAt_aboveAscii`), and the third is the named condition `NoBackslashOutside`.  The
other conjunct of `BodyState.WellFormed`, a run implies the string flag, is **unused by
this proof and not established here**. -/
theorem classPart_classStep_of_cont (st : BodyState) (b : UInt8) {st' : BodyState}
    (hstep : bodyStep st b = .cont st')
    (hodd : st.oddRun = true → st.utf8 = Utf8Need.none)
    (habove : Utf8Need.AboveAscii st.utf8)
    (hins : IsBackslashB b = true → st.inside = true) :
    BodyState.classPart st' = classStep (BodyState.classPart st) b := by
  have hkey : st'.inside = inStringAfter (BodyState.classPart st) b ∧
      st'.oddRun = (if IsBackslashB b then !st.oddRun else false) ∧
      Utf8Need.AboveAscii st'.utf8 := by
    by_cases h8 : st.utf8 = Utf8Need.none
    · by_cases ho : st.oddRun = true
      · simp [bodyStep, h8, ho] at hstep
        subst hstep
        refine ⟨?_, ?_, ?_⟩
        · simp [BodyState.classPart, inStringAfter, isUnescapedQuote, ho]
        · simp [ho]
        · simp [Utf8Need.AboveAscii]
      · by_cases hq : IsQuoteB b = true
        · by_cases hin : st.inside = true
          · simp [bodyStep, h8, ho, hq, hin] at hstep
          · simp [bodyStep, h8, ho, hq, hin] at hstep
            subst hstep
            have hof : st.oddRun = false := by
              cases h : st.oddRun with
              | false => rfl
              | true => exact absurd h ho
            have hinf : st.inside = false := by
              cases h : st.inside with
              | false => rfl
              | true => exact absurd h hin
            refine ⟨?_, ?_, ?_⟩
            · simp [BodyState.classPart, inStringAfter, isUnescapedQuote, hq, hof, hinf]
            · simp [isBackslash_false_of_quote hq]
            · simp [Utf8Need.AboveAscii]
        · by_cases hbs : IsBackslashB b = true
          · simp [bodyStep, h8, ho, hq, hbs] at hstep
            subst hstep
            have hin := hins hbs
            have hof : st.oddRun = false := by
              cases h : st.oddRun with
              | false => rfl
              | true => exact absurd h ho
            refine ⟨?_, ?_, ?_⟩
            · simp [BodyState.classPart, inStringAfter, isUnescapedQuote, hq]
            · simp [hbs, hin, hof]
            · simp [Utf8Need.AboveAscii]
          · by_cases hin : st.inside = true
            · by_cases hctl : decide (b < 0x20) = true
              · simp [bodyStep, h8, ho, hq, hbs, hin, hctl] at hstep
              · cases hs : Utf8Need.step .none b with
                | none => simp [bodyStep, h8, ho, hq, hbs, hin, hctl, hs] at hstep
                | some u =>
                    simp [bodyStep, h8, ho, hq, hbs, hin, hctl, hs] at hstep
                    subst hstep
                    have hof : st.oddRun = false := by
                      cases h : st.oddRun with
                      | false => rfl
                      | true => exact absurd h ho
                    refine ⟨?_, ?_, ?_⟩
                    · simp [BodyState.classPart, inStringAfter, isUnescapedQuote, hq, hin]
                    · simp [hbs]
                    · exact step_none_aboveAscii hs
            · simp [bodyStep, h8, ho, hq, hbs, hin] at hstep
              subst hstep
              have hof : st.oddRun = false := by
                cases h : st.oddRun with
                | false => rfl
                | true => exact absurd h ho
              have hinf : st.inside = false := by
                cases h : st.inside with
                | false => rfl
                | true => exact absurd h hin
              refine ⟨?_, ?_, ?_⟩
              · simp [BodyState.classPart, inStringAfter, isUnescapedQuote, hq, hinf]
              · simp [hbs, hof]
              · simp [Utf8Need.AboveAscii, h8]
    · cases hs : st.utf8.step b with
      | none => simp [bodyStep, h8, hs] at hstep
      | some u =>
          simp [bodyStep, h8, hs] at hstep
          subst hstep
          have hge : 0x80 ≤ b := step_accepted_ge habove h8 hs
          have hq : IsQuoteB b = false := isQuoteB_false_of_ge hge
          have hbk : IsBackslashB b = false := isBackslashB_false_of_ge hge
          have hof : st.oddRun = false := by
            cases h : st.oddRun with
            | false => rfl
            | true => exact absurd (hodd h) h8
          refine ⟨?_, ?_, ?_⟩
          · simp [BodyState.classPart, inStringAfter, isUnescapedQuote, hq, hof]
          · simp [hbk, hof]
          · exact step_aboveAscii habove hs
  obtain ⟨h1, h2, _⟩ := hkey
  simp [BodyState.classPart, classStep, h1, h2]

/-- **The byte rule's `.closed` is an unescaped quote inside a body.**  Every other
branch of the rule answers `.cont` or `.refused`, so the closing decision carries its
own premises. -/
theorem bodyStep_closed_facts {st : BodyState} {b : UInt8}
    (h : bodyStep st b = .closed) :
    st.inside = true ∧ st.oddRun = false ∧ IsQuoteB b = true := by
  by_cases h8 : st.utf8 = Utf8Need.none
  · by_cases ho : st.oddRun = true
    · simp [bodyStep, h8, ho] at h
    · by_cases hq : IsQuoteB b = true
      · by_cases hin : st.inside = true
        · have hof : st.oddRun = false := by
            cases h : st.oddRun with
            | false => rfl
            | true => exact absurd h ho
          exact ⟨hin, hof, hq⟩
        · simp [bodyStep, h8, ho, hq, hin] at h
      · by_cases hbs : IsBackslashB b = true
        · simp [bodyStep, h8, ho, hq, hbs] at h
        · by_cases hin : st.inside = true
          · by_cases hctl : decide (b < 0x20) = true
            · simp [bodyStep, h8, ho, hq, hbs, hin, hctl] at h
            · cases hs : Utf8Need.step .none b with
              | none => simp [bodyStep, h8, ho, hq, hbs, hin, hctl, hs] at h
              | some u => simp [bodyStep, h8, ho, hq, hbs, hin, hctl, hs] at h
          · simp [bodyStep, h8, ho, hq, hbs, hin] at h
  · cases hs : st.utf8.step b with
    | none => simp [bodyStep, h8, hs] at h
    | some u => simp [bodyStep, h8, hs] at h

/-! ### The two named conditions, and their counterexamples

`ContinuesBefore` is `ScanWindow.lean`'s; `NoBackslashOutside` is the classifier's
domain, and it is the condition the run parity needs.
-/

/-- Before lane `k`, the byte rule reads no backslash outside a body: every backslash
lane is reached with the string flag set.  `classStep` toggles the run parity on every
backslash, while `bodyStep` starts a run only inside a body (`oddRun := st.inside`), so
this is exactly where the two folds can agree on the parity.  It is not free:
`no_stop_does_not_identify_carries` fails it on a window that stops nowhere. -/
def NoBackslashOutside (bs : List UInt8) (st : BodyState) (k : Nat) : Prop :=
  ∀ j, j < k → ∀ {b : UInt8}, bs[j]? = some b → IsBackslashB b = true →
    (carryAt bs st j).inside = true

/-- `ScanWindow.lean`'s `carryAt` advances one lane at a time.  The original is private
there, so this is a restatement rather than an import — the same reason the lane
helpers above are restated. -/
private theorem carryAt_succ (bs : List UInt8) (st : BodyState) (k : Nat) :
    carryAt bs st (k + 1) =
      (match bs[k]? with
       | some b => (match bodyStep (carryAt bs st k) b with
                    | .cont st' => st'
                    | _ => carryAt bs st k)
       | none => carryAt bs st k) := by
  unfold carryAt
  rw [List.take_add_one, List.foldl_append]
  cases h : bs[k]? with
  | none => simp
  | some b => rfl

/-- The lane's own step, when the carrier has a byte there. -/
private theorem carryAt_succ_some (bs : List UInt8) (st : BodyState) (k : Nat) {b : UInt8}
    (hb : bs[k]? = some b) :
    carryAt bs st (k + 1) =
      (match bodyStep (carryAt bs st k) b with
       | .cont st' => st'
       | _ => carryAt bs st k) := by
  rw [carryAt_succ, hb]

/-- A lane past the carrier's length does not move the carry. -/
private theorem carryAt_succ_none (bs : List UInt8) (st : BodyState) (k : Nat)
    (hb : bs[k]? = none) : carryAt bs st (k + 1) = carryAt bs st k := by
  rw [carryAt_succ, hb]

/-- A continuing lane leaves the state its step reports. -/
private theorem carryAt_succ_cont (bs : List UInt8) (st : BodyState) (k : Nat) {b : UInt8}
    {st' : BodyState} (hb : bs[k]? = some b)
    (hstep : bodyStep (carryAt bs st k) b = .cont st') :
    carryAt bs st (k + 1) = st' := by
  rw [carryAt_succ_some bs st k hb]
  simp [hstep]

/-- The classifier's carry advances one lane, when the carrier has a byte there. -/
private theorem classCarryAt_succ_some (bs : List UInt8) (st : ClassState) (k : Nat)
    {b : UInt8} (hb : bs[k]? = some b) :
    classCarryAt bs st (k + 1) = classStep (classCarryAt bs st k) b := by
  rw [classCarryAt_succ, hb]

/-- A lane past the carrier's length does not move the classifier's carry. -/
private theorem classCarryAt_succ_none (bs : List UInt8) (st : ClassState) (k : Nat)
    (hb : bs[k]? = none) : classCarryAt bs st (k + 1) = classCarryAt bs st k := by
  rw [classCarryAt_succ, hb]

/-- The rule never leaves an odd run and an outstanding sequence in one state: the run
is started only past the requirement's guard, and a requirement is entered only past
the run's. -/
private theorem bodyStep_oddRun_utf8 {st st' : BodyState} {b : UInt8}
    (h : bodyStep st b = .cont st')
    (hodd : st.oddRun = true → st.utf8 = Utf8Need.none) :
    st'.oddRun = true → st'.utf8 = Utf8Need.none := by
  by_cases h8 : st.utf8 = Utf8Need.none
  · by_cases ho : st.oddRun = true
    · simp [bodyStep, h8, ho] at h
      subst h
      intro hc
      simp at hc
    · by_cases hq : IsQuoteB b = true
      · by_cases hin : st.inside = true
        · simp [bodyStep, h8, ho, hq, hin] at h
        · simp [bodyStep, h8, ho, hq, hin] at h
          subst h
          intro hc
          simp at hc
      · by_cases hbs : IsBackslashB b = true
        · simp [bodyStep, h8, ho, hq, hbs] at h
          subst h
          intro _
          simp
        · by_cases hin : st.inside = true
          · by_cases hctl : decide (b < 0x20) = true
            · simp [bodyStep, h8, ho, hq, hbs, hin, hctl] at h
            · cases hs : Utf8Need.step .none b with
              | none => simp [bodyStep, h8, ho, hq, hbs, hin, hctl, hs] at h
              | some u =>
                  simp [bodyStep, h8, ho, hq, hbs, hin, hctl, hs] at h
                  subst h
                  intro hc
                  simp at hc
          · simp [bodyStep, h8, ho, hq, hbs, hin] at h
            subst h
            intro hc
            exact absurd hc ho
  · cases hs : st.utf8.step b with
    | none => simp [bodyStep, h8, hs] at h
    | some u =>
        simp [bodyStep, h8, hs] at h
        subst h
        intro hc
        exact absurd (hodd hc) h8

/-- The fold from `ClassState.toBody` never holds an odd run and a requirement at once:
the invariant is the initial state's (`utf8 = none`) and `bodyStep` keeps it. -/
private theorem carryAt_oddRun_utf8 (bs : List UInt8) (st : ClassState) (k : Nat) :
    (carryAt bs st.toBody k).oddRun = true → (carryAt bs st.toBody k).utf8 = Utf8Need.none := by
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      cases hb : bs[k]? with
      | none => rw [carryAt_succ_none bs st.toBody k hb]; exact ih
      | some b =>
          cases hstep : bodyStep (carryAt bs st.toBody k) b with
          | cont st' =>
              rw [carryAt_succ_some bs st.toBody k hb]
              simpa [hstep] using bodyStep_oddRun_utf8 hstep ih
          | closed =>
              rw [carryAt_succ_some bs st.toBody k hb]
              simpa [hstep] using ih
          | refused s =>
              rw [carryAt_succ_some bs st.toBody k hb]
              simpa [hstep] using ih

/-- A continuation keeps an above-`0x80` requirement above `0x80`. -/
private theorem bodyStep_cont_aboveAscii {st st' : BodyState} {b : UInt8}
    (h : bodyStep st b = .cont st') (hu : Utf8Need.AboveAscii st.utf8) :
    Utf8Need.AboveAscii st'.utf8 := by
  by_cases h8 : st.utf8 = Utf8Need.none
  · by_cases ho : st.oddRun = true
    · simp [bodyStep, h8, ho] at h
      subst h
      simp [Utf8Need.AboveAscii]
    · by_cases hq : IsQuoteB b = true
      · by_cases hin : st.inside = true
        · simp [bodyStep, h8, ho, hq, hin] at h
        · simp [bodyStep, h8, ho, hq, hin] at h
          subst h
          simp [Utf8Need.AboveAscii]
      · by_cases hbs : IsBackslashB b = true
        · simp [bodyStep, h8, ho, hq, hbs] at h
          subst h
          simp [Utf8Need.AboveAscii]
        · by_cases hin : st.inside = true
          · by_cases hctl : decide (b < 0x20) = true
            · simp [bodyStep, h8, ho, hq, hbs, hin, hctl] at h
            · cases hs : Utf8Need.step .none b with
              | none => simp [bodyStep, h8, ho, hq, hbs, hin, hctl, hs] at h
              | some u =>
                  simp [bodyStep, h8, ho, hq, hbs, hin, hctl, hs] at h
                  subst h
                  exact step_none_aboveAscii hs
          · simp [bodyStep, h8, ho, hq, hbs, hin] at h
            subst h
            simp [Utf8Need.AboveAscii, h8]
  · cases hs : st.utf8.step b with
    | none => simp [bodyStep, h8, hs] at h
    | some u =>
        simp [bodyStep, h8, hs] at h
        subst h
        exact step_aboveAscii hu hs

/-- The fold from `ClassState.toBody` keeps the requirement's range above `0x80`. -/
private theorem carryAt_aboveAscii (bs : List UInt8) (st : ClassState) (k : Nat) :
    Utf8Need.AboveAscii (carryAt bs st.toBody k).utf8 := by
  induction k with
  | zero => simp [carryAt, ClassState.toBody, Utf8Need.AboveAscii]
  | succ k ih =>
      cases hb : bs[k]? with
      | none => rw [carryAt_succ_none bs st.toBody k hb]; exact ih
      | some b =>
          cases hstep : bodyStep (carryAt bs st.toBody k) b with
          | cont st' =>
              rw [carryAt_succ_some bs st.toBody k hb]
              simpa [hstep] using bodyStep_cont_aboveAscii hstep ih
          | closed =>
              rw [carryAt_succ_some bs st.toBody k hb]
              simpa [hstep] using ih
          | refused s =>
              rw [carryAt_succ_some bs st.toBody k hb]
              simpa [hstep] using ih

/-! ### The carry bridge

On a window where the model stops nowhere and reads no backslash outside a body, the
two carries are one state read at the two states' shared fields.
-/

/-- **The carries agree where the model is defined.**  Before lane `k`, if the byte
rule has continued at every lane and has read no backslash outside a body, then the
classifier's carry on entry to lane `k` is the model's carry there, read at the two
fields both states have.  Both hypotheses are named conditions of this module, and both
have a counterexample below.

`BodyState.WellFormed` is **not** assumed, and the omission is per conjunct rather than
global.  Two of its conjuncts are **unused by this proof and are not established here**:
a run implies the string flag (`oddRun → inside`), which a later proof needing it must
prove for itself, and the requirement's count bound.  The third — a run excludes an
outstanding requirement (`oddRun → utf8 = none`) — is **derived at the fold** by
`carryAt_oddRun_utf8`, exactly as `carryAt_aboveAscii` derives the continuation-only
range that `classPart_classStep_of_cont` takes per lane. -/
theorem classCarryAt_eq_classPart (bs : List UInt8) (st : ClassState) {k : Nat}
    (hcont : ContinuesBefore bs st.toBody k)
    (hdom : NoBackslashOutside bs st.toBody k) :
    classCarryAt bs st k = BodyState.classPart (carryAt bs st.toBody k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hcont' : ContinuesBefore bs st.toBody k := fun j hj b hb => hcont j (by omega) hb
      have hdom' : NoBackslashOutside bs st.toBody k :=
        fun j hj b hb hbs => hdom j (by omega) hb hbs
      cases hb : bs[k]? with
      | none =>
          rw [classCarryAt_succ_none bs st k hb, carryAt_succ_none bs st.toBody k hb]
          exact ih hcont' hdom'
      | some b =>
          obtain ⟨st', hst'⟩ := hcont k (Nat.lt_succ_self k) hb
          have hins : IsBackslashB b = true → (carryAt bs st.toBody k).inside = true :=
            fun hbs => hdom k (Nat.lt_succ_self k) hb hbs
          rw [classCarryAt_succ_some bs st k hb, carryAt_succ_cont bs st.toBody k hb hst']
          rw [ih hcont' hdom']
          exact (classPart_classStep_of_cont (carryAt bs st.toBody k) b hst'
            (carryAt_oddRun_utf8 bs st k) (carryAt_aboveAscii bs st k) hins).symm

/-- A continuing byte keeps the string flag set: every `.cont` branch either leaves the
flag alone or sets it. -/
private theorem bodyStep_cont_inside {st st' : BodyState} {b : UInt8}
    (h : bodyStep st b = .cont st') (hin : st.inside = true) : st'.inside = true := by
  by_cases h8 : st.utf8 = Utf8Need.none
  · by_cases ho : st.oddRun = true
    · simp [bodyStep, h8, ho] at h
      subst h
      simp [hin]
    · by_cases hq : IsQuoteB b = true
      · simp [bodyStep, h8, ho, hq, hin] at h
      · by_cases hbs : IsBackslashB b = true
        · simp [bodyStep, h8, ho, hq, hbs] at h
          subst h
          simp [hin]
        · by_cases hctl : decide (b < 0x20) = true
          · simp [bodyStep, h8, ho, hq, hbs, hin, hctl] at h
          · cases hs : Utf8Need.step .none b with
            | none => simp [bodyStep, h8, ho, hq, hbs, hin, hctl, hs] at h
            | some u =>
                simp [bodyStep, h8, ho, hq, hbs, hin, hctl, hs] at h
                subst h
                simp
  · cases hs : st.utf8.step b with
    | none => simp [bodyStep, h8, hs] at h
    | some u =>
        simp [bodyStep, h8, hs] at h
        subst h
        simp [hin]

/-- The fold from a state inside a body keeps the flag set, while the rule continues. -/
private theorem carryAt_inside_of_continues (bs : List UInt8) (st : BodyState) {k : Nat}
    (hin : st.inside = true) (hcont : ContinuesBefore bs st k) :
    ∀ j, j < k → (carryAt bs st j).inside = true := by
  intro j
  induction j with
  | zero => intro _; simp [carryAt, hin]
  | succ j ih =>
      intro hj
      have hj' : j < k := by omega
      cases hb : bs[j]? with
      | none => rw [carryAt_succ_none bs st j hb]; exact ih hj'
      | some b =>
          obtain ⟨st', hst'⟩ := hcont j hj' hb
          rw [carryAt_succ_cont bs st j hb hst']
          exact bodyStep_cont_inside hst' (ih hj')

/-- A window read from inside a body that stops nowhere stays inside it: the flag can
only leave through a closing quote, which is a stop.  So `NoBackslashOutside` follows
from the start state, and the bridge needs no condition on the window's bytes there. -/
theorem classCarryAt_eq_classPart_of_inside (bs : List UInt8) (st : ClassState)
    (hin : st.inside = true) {k : Nat} (hcont : ContinuesBefore bs st.toBody k) :
    classCarryAt bs st k = BodyState.classPart (carryAt bs st.toBody k) := by
  apply classCarryAt_eq_classPart bs st hcont
  intro j hj b hb _
  exact carryAt_inside_of_continues bs st.toBody hin hcont j hj

/-- **The no-stop hypothesis alone does not identify the carries.**  Outside a body a
backslash continues the byte rule without starting a run, while `classStep` toggles the
parity.  The window stops nowhere, so `ContinuesBefore` holds; `NoBackslashOutside` is
the condition that fails, and the carries differ. -/
theorem no_stop_does_not_identify_carries :
    (windowOf [0x5C] (⟨false, false⟩ : ClassState).toBody).stop = none ∧
      ¬ NoBackslashOutside [0x5C] (⟨false, false⟩ : ClassState).toBody 1 ∧
      classCarryAt [0x5C] (⟨false, false⟩ : ClassState) 1 ≠
        BodyState.classPart (carryAt [0x5C] (⟨false, false⟩ : ClassState).toBody 1) := by
  refine ⟨by decide, ?_, by decide⟩
  intro h
  have hin := h 0 (by omega) (b := 0x5C) rfl (by decide)
  exact absurd hin (by decide)

/-- **The no-stop hypothesis is necessary.**  A closing quote at lane 0 stops the model,
which holds its state, while the classifier steps past it: `ContinuesBefore` fails at
lane 0 and the two carries differ at lane 1. -/
theorem close_stop_carry_diverges :
    (windowOf [0x22] (⟨true, false⟩ : ClassState).toBody).stop = some (.close 0) ∧
      ¬ ContinuesBefore [0x22] (⟨true, false⟩ : ClassState).toBody 1 ∧
      classCarryAt [0x22] (⟨true, false⟩ : ClassState) 1 = ⟨false, false⟩ ∧
      carryAt [0x22] (⟨true, false⟩ : ClassState).toBody 1 = BodyState.body := by
  refine ⟨by decide, ?_, by decide, by decide⟩
  intro h
  obtain ⟨st', hst'⟩ := h 0 (by omega) (b := 0x22) rfl
  have hclosed : bodyStep (carryAt [0x22] (⟨true, false⟩ : ClassState).toBody 0) 0x22 = .closed :=
    rfl
  rw [hclosed] at hst'
  cases hst'

/-! ### The model's masks are the classifier's

The three statements below are stated on a full window with no stop and need no
condition on the bytes: the quote statement splits the model's quote lane into the
classifier's unescaped and escaped quotes, the backslash statement reads the same
predicate, and the structural statement is the block layer's fold in the classifier's
component vocabulary.

The closing lane is a different matter, because `windowOf` records it only where the
rule answers `.closed`, and that answer records a stop too.  `windowOf_delim_eq_zero_of_stop_none`
states the consequence: on a no-stop window both `Window.delim` and the classifier's
closing-lane mask are empty, so nothing there identifies them on a lane where `delim`
means anything.  `windowOf_delim_eq_of_close_stop` states the identification at a
closing stop's own lane, which reads the carry and therefore needs
`NoBackslashOutside` on top of the continuation the stop's readback supplies.  Each
condition is necessary for that statement and has a witness where it fails and the
lane disagrees: `delim_eq_fails_outside` and `delim_eq_fails_past_stop`.
-/

/-- A window with no stop continues at every lane, so no lane refuses either. -/
private theorem continuesBefore_of_stop_none {bs : List UInt8} {st : BodyState}
    (h : (windowOf bs st).stop = none) : ContinuesBefore bs st 32 := by
  have hs := windowOf_stop_spec (bs := bs) (st := st)
  rw [h] at hs
  exact hs

/-- At a lane before the window's length, a no-stop window does not refuse. -/
private theorem not_refused_of_continues {bs : List UInt8} {st : BodyState} {k : Nat}
    (hcont : ContinuesBefore bs st k) {j : Nat} (hj : j < k) {b : UInt8}
    (hb : bs[j]? = some b) : ∀ s, bodyStep (carryAt bs st j) b ≠ .refused s := by
  obtain ⟨st', hst'⟩ := hcont j hj hb
  intro s h
  rw [hst'] at h
  cases h

/-- **The model's quote mask is the classifier's two quote masks.**  `windowOf`'s
`quote` field records the byte rule's quote lane, and the classifier splits that lane
into the unescaped quotes — the string boundaries — and the escaped ones.  On a full
window with no stop the split loses no lane, and no parity condition is needed. -/
theorem windowOf_quote_eq (bs : List UInt8) (st : ClassState) (hlen : 32 ≤ bs.length)
    (hstop : (windowOf bs st.toBody).stop = none) :
    (windowOf bs st.toBody).quote = quoteMask bs st ||| escapedQuoteMask bs st := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hklen : k < bs.length := by omega
  have hb : bs[k]? = some (bs[k]'hklen) := getElem?_of_lt hklen
  have hcont := continuesBefore_of_stop_none hstop
  rw [BitVec.getLsbD_or,
    windowOf_quote (bs := bs) (st := st.toBody) (k := k) (b := bs[k]'hklen) hk hb
      (not_refused_of_continues hcont hk hb),
    quoteMask_getLsbD hk hb, escapedQuoteMask_getLsbD hk hb, quote_or_escaped]

/-- **The model's backslash mask is the classifier's.** -/
theorem windowOf_backslash_eq (bs : List UInt8) (st : ClassState) (hlen : 32 ≤ bs.length)
    (hstop : (windowOf bs st.toBody).stop = none) :
    (windowOf bs st.toBody).backslash = backslashMask bs st := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hklen : k < bs.length := by omega
  have hb : bs[k]? = some (bs[k]'hklen) := getElem?_of_lt hklen
  have hcont := continuesBefore_of_stop_none hstop
  rw [windowOf_backslash (bs := bs) (st := st.toBody) (k := k) (b := bs[k]'hklen) hk hb
      (not_refused_of_continues hcont hk hb),
    backslashMask_getLsbD hk hb]

/-- **The model's structural mask is the classifier's components.**  This one is the
block layer's `maskOfList` read through the split, so it holds on every full window,
stopped or not: the scalar transition's decision does not read the carry. -/
theorem windowOf_structural_eq (bs : List UInt8) (st : ClassState) (hlen : 32 ≤ bs.length) :
    (windowOf bs st.toBody).structural =
      delimiterMask bs st ||| quoteMask bs st ||| escapedQuoteMask bs st |||
        backslashMask bs st ||| maskOfListWith IsSpaceB bs := by
  rw [windowOf_structural, maskOfList_decompose bs st hlen]

/-- At a lane where the rule refuses nothing, its closing decision is the classifier's
closing lane: an unescaped quote lane read inside a body, which is `quoteMask` without
`inStringMask` at that bit.  The refusal hypothesis is not decoration — a quote arriving
while a requirement is outstanding is a `badUtf8` refusal, and on that lane the
classifier's bit would say "closing" while the rule refuses. -/
private theorem closed_iff_classifier (st : BodyState) (b : UInt8)
    (hodd : st.oddRun = true → st.utf8 = Utf8Need.none)
    (habove : Utf8Need.AboveAscii st.utf8)
    (hnr : ∀ s, bodyStep st b ≠ .refused s) :
    (match bodyStep st b with | .closed => true | _ => false) =
      (isUnescapedQuote (BodyState.classPart st) b &&
        !inStringAfter (BodyState.classPart st) b) := by
  by_cases h8 : st.utf8 = Utf8Need.none
  · by_cases ho : st.oddRun = true
    · simp [bodyStep, h8, ho, BodyState.classPart, isUnescapedQuote, inStringAfter]
    · by_cases hq : IsQuoteB b = true
      · by_cases hin : st.inside = true
        · simp [bodyStep, h8, ho, hq, hin, BodyState.classPart, isUnescapedQuote,
            inStringAfter]
        · simp [bodyStep, h8, ho, hq, hin, BodyState.classPart, isUnescapedQuote,
            inStringAfter]
      · by_cases hbs : IsBackslashB b = true
        · simp [bodyStep, h8, ho, hq, hbs, BodyState.classPart, isUnescapedQuote,
            inStringAfter]
        · by_cases hin : st.inside = true
          · by_cases hctl : decide (b < 0x20) = true
            · exact absurd (by simp [bodyStep, h8, ho, hq, hbs, hin, hctl]) (hnr .control)
            · cases hs : Utf8Need.step .none b with
              | none =>
                  exact absurd (by simp [bodyStep, h8, ho, hq, hbs, hin, hctl, hs])
                    (hnr .badUtf8)
              | some u =>
                  simp [bodyStep, h8, ho, hq, hbs, hin, hctl, hs, BodyState.classPart,
                    isUnescapedQuote, inStringAfter]
          · simp [bodyStep, h8, ho, hq, hbs, hin, BodyState.classPart, isUnescapedQuote,
              inStringAfter]
  · cases hs : st.utf8.step b with
    | none => exact absurd (by simp [bodyStep, h8, hs]) (hnr .badUtf8)
    | some u =>
        have hge : 0x80 ≤ b := step_accepted_ge habove h8 hs
        have hq : IsQuoteB b = false := isQuoteB_false_of_ge hge
        have hof : st.oddRun = false := by
          cases h : st.oddRun with
          | false => rfl
          | true => exact absurd (hodd h) h8
        simp [bodyStep, h8, hs, BodyState.classPart, isUnescapedQuote, inStringAfter,
          hq, hof]

/-- A continuing lane that leaves the byte rule outside a body leaves it with the run
parity clear and the requirement empty.  The one branch that could carry a requirement
while outside a body is the requirement's own, and it is never entered from outside:
the initial state has no requirement, and every branch that produces one is inside. -/
private theorem bodyStep_cont_outside_facts {st st' : BodyState} {b : UInt8}
    (hstep : bodyStep st b = .cont st') (hin : st'.inside = false)
    (hutf : st.utf8 ≠ Utf8Need.none → st.inside = true) :
    st'.oddRun = false ∧ st'.utf8 = Utf8Need.none := by
  by_cases h8 : st.utf8 = Utf8Need.none
  · by_cases ho : st.oddRun = true
    · simp [bodyStep, h8, ho] at hstep
      subst hstep
      exact ⟨rfl, by simp⟩
    · have hof : st.oddRun = false := by
        cases h : st.oddRun with
        | false => rfl
        | true => exact absurd h ho
      by_cases hq : IsQuoteB b = true
      · by_cases hi : st.inside = true
        · simp [bodyStep, h8, hof, hq, hi] at hstep
        · simp [bodyStep, h8, hof, hq, hi] at hstep
          subst hstep
          simp at hin
      · by_cases hbs : IsBackslashB b = true
        · simp [bodyStep, h8, hof, hq, hbs] at hstep
          subst hstep
          exact ⟨by simpa using hin, by simp⟩
        · by_cases hi : st.inside = true
          · by_cases hctl : decide (b < 0x20) = true
            · simp [bodyStep, h8, hof, hq, hbs, hi, hctl] at hstep
            · cases hu : Utf8Need.step .none b with
              | none => simp [bodyStep, h8, hof, hq, hbs, hi, hctl, hu] at hstep
              | some u =>
                  simp [bodyStep, h8, hof, hq, hbs, hi, hctl, hu] at hstep
                  subst hstep
                  simp at hin
          · simp [bodyStep, h8, hof, hq, hbs, hi] at hstep
            subst hstep
            exact ⟨hof, h8⟩
  · have hsi : st.inside = true := hutf h8
    cases hu : st.utf8.step b with
    | none => simp [bodyStep, h8, hu] at hstep
    | some u =>
        simp [bodyStep, h8, hu] at hstep
        subst hstep
        simp [hsi] at hin

/-- The requirement's own fold never leaves the string flag behind: a requirement is
produced only inside a body, and every branch reached with one keeps the flag set. -/
private theorem carryAt_utf8_inside (bs : List UInt8) (st : ClassState) :
    ∀ k, (carryAt bs st.toBody k).utf8 ≠ Utf8Need.none →
      (carryAt bs st.toBody k).inside = true := by
  intro k
  induction k with
  | zero => intro h; exact absurd rfl h
  | succ k ih =>
      intro h
      cases hb : bs[k]? with
      | none =>
          rw [carryAt_succ_none bs st.toBody k hb] at h ⊢
          exact ih h
      | some b =>
          cases hs : bodyStep (carryAt bs st.toBody k) b with
          | cont st' =>
              rw [carryAt_succ_some bs st.toBody k hb] at h ⊢
              rw [hs] at h ⊢
              by_cases h8 : (carryAt bs st.toBody k).utf8 = Utf8Need.none
              · by_cases ho : (carryAt bs st.toBody k).oddRun = true
                · simp [bodyStep, h8, ho] at hs
                  subst hs
                  exfalso
                  exact h (by simp)
                · by_cases hq : IsQuoteB b = true
                  · by_cases hi : (carryAt bs st.toBody k).inside = true
                    · simp [bodyStep, h8, ho, hq, hi] at hs
                    · simp [bodyStep, h8, ho, hq, hi] at hs
                      subst hs
                      simp
                  · by_cases hbs : IsBackslashB b = true
                    · simp [bodyStep, h8, ho, hq, hbs] at hs
                      subst hs
                      exfalso
                      exact h (by simp)
                    · by_cases hi : (carryAt bs st.toBody k).inside = true
                      · by_cases hctl : decide (b < 0x20) = true
                        · simp [bodyStep, h8, ho, hq, hbs, hi, hctl] at hs
                        · cases hu : Utf8Need.step .none b with
                          | none =>
                              simp [bodyStep, h8, ho, hq, hbs, hi, hctl, hu] at hs
                          | some u =>
                              simp [bodyStep, h8, ho, hq, hbs, hi, hctl, hu] at hs
                              subst hs
                              simp
                      · simp [bodyStep, h8, ho, hq, hbs, hi] at hs
                        subst hs
                        simp [h8] at h
              · have hsi : (carryAt bs st.toBody k).inside = true := ih h8
                cases hu : (carryAt bs st.toBody k).utf8.step b with
                | none => simp [bodyStep, h8, hu] at hs
                | some u =>
                    simp [bodyStep, h8, hu] at hs
                    subst hs
                    simpa using hsi
          | closed =>
              rw [carryAt_succ_some bs st.toBody k hb] at h ⊢
              rw [hs] at h ⊢
              exact ih h
          | refused s =>
              rw [carryAt_succ_some bs st.toBody k hb] at h ⊢
              rw [hs] at h ⊢
              exact ih h

/-- One continuing lane more: a lane the rule continues from outside a body leaves the
next carry outside it with the run parity clear and no requirement outstanding. -/
private theorem carryAt_succ_outside_of_cont (bs : List UInt8) (st : ClassState)
    {j : Nat} {b : UInt8} (hb : bs[j]? = some b)
    (hcont : ContinuesBefore bs st.toBody (j + 1))
    (hin : (carryAt bs st.toBody (j + 1)).inside = false) :
    (carryAt bs st.toBody (j + 1)).oddRun = false ∧
      (carryAt bs st.toBody (j + 1)).utf8 = Utf8Need.none := by
  obtain ⟨st', hstep⟩ := hcont j (Nat.lt_succ_self j) hb
  rw [carryAt_succ_cont bs st.toBody j hb hstep] at hin ⊢
  exact bodyStep_cont_outside_facts hstep hin (carryAt_utf8_inside bs st j)

/-- A continuing quote lane the classifier reads as unescaped leaves the byte rule
inside a body with the run parity clear.  Arriving outside, the rule opens the body;
arriving inside with the parity clear, the lane would close or refuse, so it cannot
continue at all. -/
private theorem cont_quote_outside_class {st : BodyState} {b : UInt8} {st' : BodyState}
    (hstep : bodyStep st b = .cont st') (hq : IsQuoteB b = true)
    (habove : Utf8Need.AboveAscii st.utf8)
    (hout : st.inside = false → st.oddRun = false ∧ st.utf8 = Utf8Need.none) :
    st'.inside = true ∧ st'.oddRun = false := by
  by_cases h8 : st.utf8 = Utf8Need.none
  · by_cases ho : st.oddRun = true
    · simp [bodyStep, h8, ho] at hstep
      subst hstep
      have hsi : st.inside = true := by
        cases hi : st.inside with
        | true => rfl
        | false => exact absurd ho (by rw [(hout hi).1]; simp)
      exact ⟨by simp [hsi], by simp⟩
    · have hof : st.oddRun = false := by
        cases h : st.oddRun with
        | false => rfl
        | true => exact absurd h ho
      by_cases hi : st.inside = true
      · simp [bodyStep, h8, hof, hq, hi] at hstep
      · simp [bodyStep, h8, hof, hq, hi] at hstep
        subst hstep
        exact ⟨by simp, by simp⟩
  · have hge : 0x80 ≤ b := by
      cases hu : st.utf8.step b with
      | none => simp [bodyStep, h8, hu] at hstep
      | some u => exact step_accepted_ge habove h8 hu
    have hbq : b = 0x22 := of_decide_eq_true hq
    subst hbq
    exact absurd hge (by decide)

/-- **Inside a body, the classifier's carry is the rule's**, on a window that continues
at every lane before the one being read.  The two can only part where the rule reads a
backslash outside a body — the classifier toggles the run parity there and the rule does
not — and such a lane leaves the classifier outside the body it opened, which the rule
does not.  So whenever the classifier is inside, the rule is inside with the same
parity, and a classifier lane marked as closing is a lane where the rule does not
continue. -/
private theorem classInside_of_continues (bs : List UInt8) (st : ClassState)
    (hlen : 32 ≤ bs.length) :
    ∀ k, k < 32 → ContinuesBefore bs st.toBody (k + 1) →
      (classCarryAt bs st k).inside = true →
        (carryAt bs st.toBody k).inside = true ∧
          (classCarryAt bs st k).oddRun = (carryAt bs st.toBody k).oddRun := by
  intro k
  induction k with
  | zero =>
      intro _ _ hin
      refine ⟨?_, rfl⟩
      simpa [classCarryAt, carryAt, ClassState.toBody] using hin
  | succ k ih =>
      intro hk32 hcont hin
      have hk : k < 32 := by omega
      have hcont' : ContinuesBefore bs st.toBody (k + 1) :=
        fun j hj b hb => hcont j (by omega) hb
      cases hb : bs[k]? with
      | none =>
          rw [classCarryAt_succ_none bs st k hb] at hin ⊢
          rw [carryAt_succ_none bs st.toBody k hb] at ⊢
          exact ih hk hcont' hin
      | some b =>
          obtain ⟨st', hstep⟩ := hcont k (by omega) hb
          rw [classCarryAt_succ_some bs st k hb] at hin ⊢
          rw [carryAt_succ_cont bs st.toBody k hb hstep] at ⊢
          by_cases hci : (classCarryAt bs st k).inside = true
          · obtain ⟨hmcin, hodd⟩ := ih hk hcont' hci
            have hpart : BodyState.classPart (carryAt bs st.toBody k) =
                classCarryAt bs st k := by
              cases hcc : classCarryAt bs st k
              cases hmc : carryAt bs st.toBody k
              simp_all [BodyState.classPart]
            have hstep' := classPart_classStep_of_cont (carryAt bs st.toBody k) b hstep
              (carryAt_oddRun_utf8 bs st k) (carryAt_aboveAscii bs st k)
              (fun _ => hmcin)
            rw [hpart] at hstep'
            refine ⟨?_, ?_⟩
            · have h := congrArg ClassState.inside hstep'
              simpa [BodyState.classPart, hin] using h
            · have h := congrArg ClassState.oddRun hstep'
              simpa [BodyState.classPart] using h.symm
          · have hci' : (classCarryAt bs st k).inside = false := by
              cases h : (classCarryAt bs st k).inside <;> simp_all
            have hin0 : isUnescapedQuote (classCarryAt bs st k) b = true := by
              have h : inStringAfter (classCarryAt bs st k) b = true := hin
              rw [inStringAfter, hci'] at h
              simpa using h
            have hq : IsQuoteB b = true := by
              have h := hin0
              unfold isUnescapedQuote at h
              exact ((Bool.and_eq_true ..).mp h).1
            have hccodd : (classCarryAt bs st k).oddRun = false := by
              have h := hin0
              unfold isUnescapedQuote at h
              have h2 := ((Bool.and_eq_true ..).mp h).2
              simpa using h2
            have hout : (carryAt bs st.toBody k).inside = false →
                (carryAt bs st.toBody k).oddRun = false ∧
                  (carryAt bs st.toBody k).utf8 = Utf8Need.none := by
              intro hmi
              rcases Nat.eq_zero_or_pos k with hk0 | hkpos
              · subst hk0
                refine ⟨?_, by simp [carryAt, ClassState.toBody]⟩
                simpa [classCarryAt, carryAt, ClassState.toBody] using hccodd
              · have hbprev : bs[k - 1]? = some (bs[k - 1]'(by omega)) :=
                  getElem?_of_lt (by omega)
                have hcontk : ContinuesBefore bs st.toBody ((k - 1) + 1) :=
                  fun j hj b' hb' => hcont j (by omega) hb'
                have hprev := carryAt_succ_outside_of_cont bs st hbprev hcontk
                  (by simpa [Nat.sub_add_cancel hkpos] using hmi)
                simpa [Nat.sub_add_cancel hkpos] using hprev
            obtain ⟨hstin, hstodd⟩ := cont_quote_outside_class hstep hq
              (carryAt_aboveAscii bs st k) hout
            refine ⟨hstin, ?_⟩
            rw [hstodd]
            simp [classStep, isBackslash_false_of_quote hq]

/-- A lane the classifier marks as closing is a lane where the byte rule does not
continue: an unescaped quote read inside a body closes it, or — with a requirement
outstanding — is refused, since a quote is not a continuation byte. -/
private theorem bodyStep_cont_quote_impossible {st : BodyState} {b : UInt8}
    (hin : st.inside = true) (hoff : st.oddRun = false) (hq : IsQuoteB b = true)
    (habove : Utf8Need.AboveAscii st.utf8) :
    ∀ st', bodyStep st b ≠ .cont st' := by
  intro st' h
  by_cases h8 : st.utf8 = Utf8Need.none
  · simp [bodyStep, h8, hoff, hq, hin] at h
  · have hge : 0x80 ≤ b := by
      cases hu : st.utf8.step b with
      | none => simp [bodyStep, h8, hu] at h
      | some u => exact step_accepted_ge habove h8 hu
    have hbq : b = 0x22 := of_decide_eq_true hq
    subst hbq
    exact absurd hge (by decide)

/-- **With no stop, the closing lane is empty on both sides.**  `windowLane` writes
`Window.delim` only on the branch that answers `.closed`, and that branch records the
stop, so a window that stops nowhere has `delim = 0`.  On the classifier's side the
same emptiness holds with no condition on the bytes: its closing-lane mask marks an
unescaped quote read inside a body, and such a lane is one the rule cannot continue
past — it closes the body or refuses the byte.  No identification is claimed here,
because neither mask has a set lane to identify. -/
theorem windowOf_delim_eq_zero_of_stop_none (bs : List UInt8) (st : ClassState)
    (hlen : 32 ≤ bs.length) (hstop : (windowOf bs st.toBody).stop = none) :
    (windowOf bs st.toBody).delim = 0 ∧
      quoteMask bs st &&& ~~~inStringMask bs st = 0 := by
  refine ⟨?_, ?_⟩
  · apply BitVec.eq_of_getLsbD_eq
    intro k hk
    have hklen : k < bs.length := by omega
    have hb : bs[k]? = some (bs[k]'hklen) := getElem?_of_lt hklen
    obtain ⟨st', hst'⟩ := continuesBefore_of_stop_none hstop k hk hb
    rw [windowOf_delim hk hb, hst']
    exact BitVec.getLsbD_zero.symm
  · apply BitVec.eq_of_getLsbD_eq
    intro k hk
    have hklen : k < bs.length := by omega
    have hcont := continuesBefore_of_stop_none hstop
    have hcontk : ContinuesBefore bs st.toBody (k + 1) :=
      fun j hj b hb' => hcont j (by omega) hb'
    obtain ⟨b, hb⟩ : ∃ b, bs[k]? = some b := ⟨_, getElem?_of_lt hklen⟩
    rw [BitVec.getLsbD_and, LeanLLVM.Vellum.BitLanes.getLsbD_not_of_lt _ hk,
      quoteMask_getLsbD hk hb, inStringMask_getLsbD hk hb]
    cases hmask : (isUnescapedQuote (classCarryAt bs st k) b &&
        !inStringAfter (classCarryAt bs st k) b) with
    | false =>
        exact BitVec.getLsbD_zero.symm
    | true =>
        exfalso
        have h1 : isUnescapedQuote (classCarryAt bs st k) b = true :=
          ((Bool.and_eq_true ..).mp hmask).1
        have h2 : (!inStringAfter (classCarryAt bs st k) b) = true :=
          ((Bool.and_eq_true ..).mp hmask).2
        have hq : IsQuoteB b = true := by
          have h := h1
          unfold isUnescapedQuote at h
          exact ((Bool.and_eq_true ..).mp h).1
        have hccodd : (classCarryAt bs st k).oddRun = false := by
          have h := h1
          unfold isUnescapedQuote at h
          simpa using ((Bool.and_eq_true ..).mp h).2
        have hcin : (classCarryAt bs st k).inside = true := by
          have h3 : inStringAfter (classCarryAt bs st k) b = false := by simpa using h2
          rw [inStringAfter, h1] at h3
          simpa using h3
        obtain ⟨hmcin, hmcodd⟩ := classInside_of_continues bs st hlen k hk hcontk hcin
        have hoff : (carryAt bs st.toBody k).oddRun = false := by
          rw [← hmcodd]; exact hccodd
        obtain ⟨st', hst'⟩ := hcont k hk hb
        exact bodyStep_cont_quote_impossible hmcin hoff hq
          (carryAt_aboveAscii bs st k) st' hst'

/-- **At a closing stop's lane the two closing lanes are the same bit.**  `Window.delim`
is the lane where the rule closes the body; in the classifier's vocabulary that is an
unescaped quote read inside a body, which is `quoteMask` without `inStringMask` — the
same two masks the candidate identity is built from.  The comparison reads the carry at
the stop's own lane, so it takes both named conditions: the stop's readback supplies
`ContinuesBefore`, and `NoBackslashOutside` is the second, necessary because the
counterexamples below each fail it or the continuation and disagree at the stop. -/
theorem windowOf_delim_eq_of_close_stop (bs : List UInt8) (st : ClassState) {k : Nat}
    (hstop : (windowOf bs st.toBody).stop = some (.close k))
    (hdom : NoBackslashOutside bs st.toBody k) :
    (windowOf bs st.toBody).delim.getLsbD k =
      (quoteMask bs st &&& ~~~inStringMask bs st).getLsbD k := by
  obtain ⟨hk, ⟨b, hb⟩, hcont, hclosedAll⟩ := by
    have hs := windowOf_stop_spec (bs := bs) (st := st.toBody)
    rw [hstop] at hs
    exact hs
  have hclosed : bodyStep (carryAt bs st.toBody k) b = .closed := hclosedAll hb
  have hcarry := classCarryAt_eq_classPart bs st hcont hdom
  have hleft : (windowOf bs st.toBody).delim.getLsbD k = true := windowOf_stop_close hstop
  have hclass : (isUnescapedQuote (classCarryAt bs st k) b &&
      !inStringAfter (classCarryAt bs st k) b) = true := by
    rw [hcarry]
    have h := closed_iff_classifier (carryAt bs st.toBody k) b
      (carryAt_oddRun_utf8 bs st k) (carryAt_aboveAscii bs st k)
      (fun s hs => by rw [hclosed] at hs; cases hs)
    rw [hclosed] at h
    exact h.symm
  rw [hleft, BitVec.getLsbD_and, LeanLLVM.Vellum.BitLanes.getLsbD_not_of_lt _ hk,
    quoteMask_getLsbD hk hb, inStringMask_getLsbD hk hb]
  exact hclass.symm

/-- **`NoBackslashOutside` is necessary for the stop-lane identification.**  Read from
outside a body, a backslash starts the classifier's run but not the rule's, so the
classifier calls the following quote escaped and the rule does not.  The rule closes at
lane 2, where `Window.delim` is set, while the classifier's closing lane there is
empty; the lanes before it all continue, so the failing hypothesis is the backslash
condition. -/
theorem delim_eq_fails_outside :
    (windowOf [0x5C, 0x22, 0x22] (⟨false, false⟩ : ClassState).toBody).stop =
        some (.close 2) ∧
      (windowOf [0x5C, 0x22, 0x22] (⟨false, false⟩ : ClassState).toBody).delim.getLsbD 2 =
        true ∧
      (quoteMask [0x5C, 0x22, 0x22] ⟨false, false⟩ &&&
        ~~~inStringMask [0x5C, 0x22, 0x22] ⟨false, false⟩).getLsbD 2 = false ∧
      ContinuesBefore [0x5C, 0x22, 0x22] (⟨false, false⟩ : ClassState).toBody 2 ∧
      ¬ NoBackslashOutside [0x5C, 0x22, 0x22] (⟨false, false⟩ : ClassState).toBody 2 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · intro j hj b hb
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · simp at hb
      subst hb
      exact ⟨⟨false, false, Utf8Need.none⟩, rfl⟩
    · simp at hb
      subst hb
      exact ⟨⟨true, false, Utf8Need.none⟩, rfl⟩
  · intro h
    have hin := h 0 (by omega) (b := 0x5C) rfl (by decide)
    exact absurd hin (by decide)

/-- **`ContinuesBefore` is necessary for the stop-lane identification.**  The window
starts inside a body and the first lane closes it; the fold still asks the second lane,
which closes the same body again, so `Window.delim` has lane 1 set.  The classifier
steps past the first close and its closing lane at 1 is empty.  No backslash occurs, so
`NoBackslashOutside` holds and the failing hypothesis is the continuation. -/
theorem delim_eq_fails_past_stop :
    (windowOf [0x22, 0x22] (⟨true, false⟩ : ClassState).toBody).stop = some (.close 0) ∧
      (windowOf [0x22, 0x22] (⟨true, false⟩ : ClassState).toBody).delim.getLsbD 1 = true ∧
      (quoteMask [0x22, 0x22] ⟨true, false⟩ &&&
        ~~~inStringMask [0x22, 0x22] ⟨true, false⟩).getLsbD 1 = false ∧
      NoBackslashOutside [0x22, 0x22] (⟨true, false⟩ : ClassState).toBody 1 ∧
      ¬ ContinuesBefore [0x22, 0x22] (⟨true, false⟩ : ClassState).toBody 1 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · intro j hj b hb hbs
    have hj0 : j = 0 := by omega
    subst hj0
    simp at hb
    subst hb
    exact absurd hbs (by decide)
  · intro h
    obtain ⟨st', hst'⟩ := h 0 (by omega) (b := 0x22) rfl
    have hclosed : bodyStep (carryAt [0x22, 0x22] (⟨true, false⟩ : ClassState).toBody 0) 0x22
        = .closed := rfl
    rw [hclosed] at hst'
    cases hst'

/-! ### What happens after a stop

The classifier is total where the model stops or refuses, so its values past a stop
describe no run of the byte rule.  The two theorems below are the divergence itself, not
a caveat: at the stop's lane the model holds the state on entry, and the classifier
takes the step the rule refused.  Everything the parser reads after a stop comes from
the model again, so the classifier's post-stop lanes are defined but not meaningful.
-/

/-- **Past a stop the classifier steps and the model holds.**  At a lane the byte rule
does not continue past, `carryAt` keeps the state on entry to the lane while `classStep`
takes the step the rule refused; from the next lane the two folds read the same bytes
from different states. -/
theorem classCarryAt_succ_of_stop (bs : List UInt8) (st : ClassState) {s : Nat} {b : UInt8}
    (hb : bs[s]? = some b)
    (hcarry : classCarryAt bs st s = BodyState.classPart (carryAt bs st.toBody s))
    (hstop : ∀ st', bodyStep (carryAt bs st.toBody s) b ≠ .cont st') :
    carryAt bs st.toBody (s + 1) = carryAt bs st.toBody s ∧
      classCarryAt bs st (s + 1) = classStep (BodyState.classPart (carryAt bs st.toBody s)) b := by
  constructor
  · rw [carryAt_succ, hb]
    cases hstep : bodyStep (carryAt bs st.toBody s) b with
    | cont st' => exact absurd hstep (hstop st')
    | closed => simp [hstep]
    | refused s' => simp [hstep]
  · rw [classCarryAt_succ, hb, hcarry]

/-- **At a closing stop the classifier's string state is the complement of the model's.**
The rule's `.closed` is an unescaped quote inside a body, so `classStep` flips the flag
exactly where the model holds it: the classifier lands outside the string and the model
stays inside.  This is a divergence, not a widening — the classifier neither
over-approximates nor under-approximates the scanner after a stop, it describes a
different state, and every lane past the stop is one the parser re-reads from the
model. -/
theorem classCarryAt_succ_closed (bs : List UInt8) (st : ClassState) {s : Nat} {b : UInt8}
    (hb : bs[s]? = some b)
    (hcont : ContinuesBefore bs st.toBody s)
    (hdom : NoBackslashOutside bs st.toBody s)
    (hclosed : bodyStep (carryAt bs st.toBody s) b = .closed) :
    classCarryAt bs st (s + 1) = ⟨false, false⟩ ∧
      carryAt bs st.toBody (s + 1) = carryAt bs st.toBody s ∧
      (carryAt bs st.toBody s).inside = true := by
  have hcarry : classCarryAt bs st s = BodyState.classPart (carryAt bs st.toBody s) :=
    classCarryAt_eq_classPart bs st hcont hdom
  have hstep := classCarryAt_succ_of_stop bs st hb hcarry
    (fun st' h => by rw [hclosed] at h; cases h)
  obtain ⟨hhold, hfold⟩ := hstep
  obtain ⟨hin, hof, hq⟩ := bodyStep_closed_facts hclosed
  have hbs : IsBackslashB b = false := isBackslash_false_of_quote hq
  have hclass : classStep (BodyState.classPart (carryAt bs st.toBody s)) b = ⟨false, false⟩ := by
    simp [BodyState.classPart, classStep, inStringAfter, isUnescapedQuote, hq, hin, hof, hbs]
  exact ⟨by rw [hfold, hclass], hhold, hin⟩

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

/-- The join commutes with complement.  The lane lemmas it needs are
`BitLanes.getLsbD_not_of_lt`, proved without the `Classical.choice` that
`BitVec.getLsbD_not`'s proof term carries; this is a specification lemma, so the
narrower footprint belongs here. -/
theorem mask64_not (a b : BitVec 32) :
    ~~~(mask64 a b) = mask64 (~~~a) (~~~b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [LeanLLVM.Vellum.BitLanes.getLsbD_not_of_lt _ hk]
  by_cases hk32 : k < 32
  · rw [mask64_getLsbD_lo _ _ hk32, mask64_getLsbD_lo _ _ hk32,
      LeanLLVM.Vellum.BitLanes.getLsbD_not_of_lt _ hk32]
  · rw [show k = (k - 32) + 32 from by omega, mask64_getLsbD_hi _ _ (by omega),
      mask64_getLsbD_hi _ _ (by omega),
      LeanLLVM.Vellum.BitLanes.getLsbD_not_of_lt _ (by omega)]

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
