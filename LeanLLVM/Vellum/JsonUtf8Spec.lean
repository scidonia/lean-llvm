/-
The UTF-8 validity stage's specification, in the model's own vocabulary.

The stage is `u8kl.h`'s Keiser–Lemire table DFA as `kernel/json/measured/`'s
header states it, read at the three published 32-byte tables.  A position's error
byte is

    err = sc ^ must
    sc   = T1[lo p1] & T2[hi p1] & T3[hi c]
    must = 0x80 & ((p2 -s 0x60) | (p3 -s 0x70))

where `c` is the byte at the position, `p1`/`p2`/`p3` the three before it, and
`-s` is `llvm.usub.sat.v32i8`'s lane (`BitLanes.subsSat`).  `sc` carries the
continuation-structure bit `0x80` plus seven error classes, and `must` carries the
single bit that says the position *must* be a continuation.

The tables reach the shuffles as literal `<32 x i8>` operands (`JsonUtf8IR.lean`'s
header records that the compiler folds them), so they are constants of this
specification and `klSc` takes no table parameter; `tests/json-utf8/check.sh` is
what ties those constants to the header's bytes.

## The eight-class vocabulary

`sc`'s bits are the header's, and the specification reads each of them:

|bit|name|meaning|
|---|---|---|
|`0x01`|`tooShort`|a lead is not followed by a continuation|
|`0x02`|`tooLong`|a continuation follows an ASCII byte|
|`0x04`|`overlong3`|`E0`'s first continuation is below `A0`|
|`0x08`|`tooLarge`|`F4`'s first continuation is above `8F`|
|`0x10`|`surrogate`|`ED`'s first continuation is above `9F`|
|`0x20`|`overlong2`|`C0`/`C1` never begin a character|
|`0x40`|`tooLarge1000`|`F0`'s first continuation is below `90`; the same bit is the header's `OVERLONG_4`, because the two cannot hold at one position|
|`0x80`|`twoConts`|the pair (`p1`, `c`) is two continuations, and `must` disagrees|

## The window, and what the verdict is a verdict on

`klStage` is the stage at the ABI's arguments: a document of `n` bytes staged at
`b`, whose three preceding bytes are zero and whose bytes from `n` to the 64-byte
boundary are zero.  It evaluates `nb = (n + 63) / 64` blocks of 64 positions each
into one accumulated error vector, then adds the tail byte's own test.

The verdict is zero exactly when the **staged window** — the three prefix bytes,
the document, and the zero padding to the boundary — is a valid prefix in
`LeanLLVM.JSON.ValidPrefix`'s sense.  It is not "the document is valid UTF-8":

* at `n % 64 ≠ 0` the padding supplies the position after the document's last
  byte, so a truncated final character is *seen* and rejected, and the verdict is
  zero exactly for a concatenation of complete characters;
* at `n % 64 = 0` the position after the last byte is never looked at, so a
  truncated final character is accepted, and only a byte that can never begin one
  (`C0`, `C1`, `F5`..`FF`) is restored by `klTailByte`.

That asymmetry is the caller's rule, not the stage's, and it is stated here
because the two cases are different predicates over the same bytes.  The
block-boundary case is the reason the verdict is a statement about a *prefix*:
the stage's own contract is the window, and the window's relation to a document
is what the caller supplies.

## Applying the lead classes

The reconstruction splits the lead byte by class, and each class's `Utf8Char`
constructor fixes part of the byte list it concludes.  Three consequences hold
for proofs in this file:

* A class whose constructor fixes the lead — `0xE0` in `three₀`, `0xED` in
  `three₂`, `0xF0` in `four₀`, `0xF4` in `four₂` — cannot be applied while the
  goal's head is `klByte s i`.  The class is known from `hcE0 : c = 0xE0`, a
  propositional equality, not by reduction, so the head is rewritten to the
  literal first.  The classes that take the lead as a parameter (`three₁`,
  `three₃`, `four₁`) need no such step.
* Write the byte list in cons form and give the codepoint in the constructor's
  own expression.  A list written `([a, b] ++ [c])` leaves the codepoint
  placeholder unsynthesised although the two forms are definitionally equal, and
  a codepoint in reduced form — `(c.toNat - 0xF0) * 0x40000` for `four₁` rather
  than the constructor's sum of four terms — exhausts the elaborator's recursion
  budget when it is unified against the constructor's.
* A branch whose `omega` counterexample is satisfiable is a missing case in the
  lead-class tree, not an arithmetic problem.  `klPair_iff`'s clauses are the
  ranges to check the branch against: a counterexample set narrower than one
  clause's range is a missing split, and only an empty set is arithmetic.

## What is proved here

`klErrByte_eq_zero_iff` is C59, and what it states is **local** admissibility
given the continuation requirement the byte one back imposes: if a lead two or
three bytes back still owns this position (`NeedsCont p2 p3`) then both `p1` and
`c` are `UTF8-tail`s, and otherwise `c` may follow `p1` in the sense of `KlPair`
(RFC 3629 §4's productions, clause for clause).  It is deliberately not a claim
about the four bytes around the position being admissible *each in turn*: a
position can be locally fine while the sequence is broken one or two places
earlier.

The witness is the window `(0xF0, 0x41, 0x80, 0x80)` read at its last byte:
`klErrByte 0xF0 0x41 0x80 0x80 = 0`, and none of that zero is a claim about the
pair (`0x41`, `0x80`).  `NeedsCont` is **true** here — `0xF0` is a four-byte lead
three bytes back — so the requirement the tables read is that `p1` and `c` be
continuations, and both are `0x80`s.  On its own the pair is refused:
`KlPair 0x41 0x80` is false and `klErrByte 0x00 0x00 0x41 0x80` is the
`tooLong` class this file already names.  The error is at the neighbours, and at
both of them: one position earlier, the *first* `0x80`, is
`klErrByte 0x00 0xF0 0x41 0x80 = 0x82` — `twoConts | tooLong`, because `NeedsCont`
demands a continuation at `p1 = 0x41` and an ASCII byte is not one — and two
positions earlier the `0x41` is `klErrByte 0x00 0x00 0xF0 0x41 = 0x01`,
`tooShort`, a lead with no continuation after it.  Those two evaluations are
`klErrByte_window_witness_earlier` and `klErrByte_window_witness_earliest` in
`JsonUtf8Steps`.  The decomposition the proof uses is
`err = sc ^ must`, then `must`'s single bit and `sc`'s table word; `sc` is decided
over `lo(p1) × hi(p1) × hi(c)`, which is 16 × 16 × 16 = 4096 table cases, once per
value of `NeedsCont`, so 2 × 4096 = 8192 decided cases.

The eight refused witnesses below are one per class the tables distinguish, and
the count is the table above's: eight.

The tables are the vendored header's bytes.  `tests/json-utf8/check.sh` compares
this module's three tables with `kl_t1`/`kl_t2`/`kl_t3` read out of
`kernel/json/measured/u8kl.h` by a compiled translation unit, so the values are
checked against the header rather than transcribed from it here.

Nothing here is about the emitted body.  `utf8Calls` (`JsonUtf8IR.lean`) binds
the three intrinsics and `JsonUtf8IR` pins the fixture; `JsonUtf8Steps` holds the
body's execution and the refinement of the pinned body against `klStage`.  The
specification is this module's, the statement is that module's, and neither
restates the other's definitions.
-/
import LeanLLVM.JSON.Utf8
import LeanLLVM.Vellum.BitLanes

namespace LeanLLVM.Vellum.JsonUtf8Spec

open LeanLLVM
open LeanLLVM.JSON

/-! ### The three published tables

`Vector UInt8 32`, at the header's values.  `klTables_bytes` is the 96-byte count
the route row compares: three vectors of thirty-two lanes, and each lane one byte.
-/

/-- `kl_t1`, at the header's bytes: indexed by `lo(p1)`. -/
def klT1 : Vector UInt8 32 :=
  ⟨#[0xe7, 0xa3, 0x83, 0x83, 0x8b, 0xcb, 0xcb, 0xcb,
     0xcb, 0xcb, 0xcb, 0xcb, 0xcb, 0xdb, 0xcb, 0xcb,
     0xe7, 0xa3, 0x83, 0x83, 0x8b, 0xcb, 0xcb, 0xcb,
     0xcb, 0xcb, 0xcb, 0xcb, 0xcb, 0xdb, 0xcb, 0xcb], by decide⟩

/-- `kl_t2`, at the header's bytes: indexed by `hi(p1)`. -/
def klT2 : Vector UInt8 32 :=
  ⟨#[0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02,
     0x80, 0x80, 0x80, 0x80, 0x21, 0x01, 0x15, 0x49,
     0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02,
     0x80, 0x80, 0x80, 0x80, 0x21, 0x01, 0x15, 0x49], by decide⟩

/-- `kl_t3`, at the header's bytes: indexed by `hi(c)`. -/
def klT3 : Vector UInt8 32 :=
  ⟨#[0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
     0xe6, 0xae, 0xba, 0xba, 0x01, 0x01, 0x01, 0x01,
     0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
     0xe6, 0xae, 0xba, 0xba, 0x01, 0x01, 0x01, 0x01], by decide⟩

/-- The three tables are 96 bytes: three vectors of thirty-two lanes, one byte
per lane.  The route row's own arithmetic is this lemma's. -/
theorem klTables_bytes :
    klT1.toList.length + klT2.toList.length + klT3.toList.length = 96 := by
  decide

/-- **The eight-class vocabulary**, defined once and read by both the table
mathematics below and `klErrByte_eq_zero_iff`'s statement.  Named for the
header's own constants. -/
def tooShort : UInt8 := 0x01
def tooLong : UInt8 := 0x02
def overlong3 : UInt8 := 0x04
def tooLarge : UInt8 := 0x08
def surrogate : UInt8 := 0x10
def overlong2 : UInt8 := 0x20
def tooLarge1000 : UInt8 := 0x40
def twoConts : UInt8 := 0x80

/-! ### The per-position words -/

/-- A table lane at a nibble: `T[n]`, and `0` past the end, which the fixed
sixteen-lane tables never reach. -/
def klAt (t : Vector UInt8 32) (n : Nat) : UInt8 := t.toList.getD n 0x00

/-- `sc` at one position: `T1[lo p1] & T2[hi p1] & T3[hi c]`.  This is the word
the three `llvm.x86.avx2.pshuf.b` calls and the two `and`s form. -/
def klSc (p1 c : UInt8) : UInt8 :=
  klAt klT1 (p1.toNat % 16) &&& klAt klT2 (p1.toNat / 16) &&& klAt klT3 (c.toNat / 16)

/-- `must` at one position.  The emission's word is
`0x80 & ((p2 -s 0x60) | (p3 -s 0x70))`, and only bit 7 of it survives the `and`:
`subsSat_high_bit` below says bit 7 of `x -s c` is set exactly when
`c + 0x80 ≤ x`, so the word is `0x80` exactly when `p2 ≥ 0xE0` or `p3 ≥ 0xF0`.
The definition is that surviving bit, because the eight-class vocabulary reads it
as one. -/
def klMust (p2 p3 : UInt8) : UInt8 := if 0xE0 ≤ p2 ∨ 0xF0 ≤ p3 then 0x80 else 0x00

/-- Bit 7 of `llvm.usub.sat.v32i8`'s lane is set exactly when the subtrahend is a
whole `0x80` below the minuend: the fact `klMust`'s definition is the surviving
bit of. -/
theorem subsSat_high_bit (x c : UInt8) :
    (0x80 ≤ (BitLanes.subsSat x.toBitVec c.toBitVec).toNat) ↔
      c.toNat + 0x80 ≤ x.toNat := by
  have hval : (BitLanes.subsSat x.toBitVec c.toBitVec).toNat =
      if c.toNat ≤ x.toNat then x.toNat - c.toNat else 0 := by
    unfold BitLanes.subsSat
    by_cases h : c.toBitVec.toNat ≤ x.toBitVec.toNat
    · have h' : c.toNat ≤ x.toNat := by simpa using h
      rw [ite_eq_left h, ite_eq_left h',
        BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact h)]
      rfl
    · have h' : ¬ c.toNat ≤ x.toNat := by
        intro hh
        exact h (by simpa using hh)
      rw [ite_eq_right h, ite_eq_right h']
      rfl
  rw [hval]
  by_cases h : c.toNat ≤ x.toNat
  · rw [ite_eq_left h]
    constructor
    · intro hh; omega
    · intro hh; omega
  · rw [ite_eq_right h]
    constructor
    · intro hh; omega
    · intro hh; omega

/-- The error byte at one position: `sc ^ must`.  Zero exactly when the eight
classes' bits and the continuation bit all agree, which is
`klErrByte_eq_zero_iff`'s statement. -/
def klErrByte (p3 p2 p1 c : UInt8) : UInt8 := klSc p1 c ^^^ klMust p2 p3

/-! ### The vector, the block and the accumulate

The stream these read is the staged window: `s[0..2]` the three bytes before the
block, `s[3..]` the block itself.  A read past the stream is `0x00`, which is what
the caller's padding holds, so the definitions are the machine's at every position
the loop reads. -/

/-- Byte `k` of a stream, `0x00` past its end. -/
def klByte (s : List UInt8) (k : Nat) : UInt8 := s.getD k 0x00

/-- One 32-byte vector's error bytes, the vector's three carry bytes first: lane
`k`'s window is `(p3, p2, p1, c) = (s[k], s[k+1], s[k+2], s[k+3])`. -/
def klErrVec (s : List UInt8) : List UInt8 :=
  (List.range 32).map fun k =>
    klErrByte (klByte s k) (klByte s (k + 1)) (klByte s (k + 2)) (klByte s (k + 3))

/-- One 32-byte vector's error bytes, from the 3-byte carry and the vector:
this is one `kl_err32_ld` call. -/
def klErr32 (pre blk : List UInt8) : List UInt8 := klErrVec (pre ++ blk)

/-- One block's error vector: the two halves' error bytes or-ed lane for lane,
which is `kl_err_vec_ld`'s two calls and its `or`.  The upper half's carry is the
lower half's last three bytes, which is the same three bytes the second
`kl_err32_ld` loads at `p + 32 - 3`. -/
def klErrBlk (pre blk : List UInt8) : List UInt8 :=
  List.zipWith (· ||| ·) (klErr32 pre (blk.take 32))
    (klErr32 ((pre ++ blk.take 32).drop 32) (blk.drop 32))

/-- A block's 64 bytes are all below `0x80`: `testz(v0 | v1, 0x80)`, which is the
gate's `ascii`, and `ascii && prev_ascii` is the skip condition.  The equality is
`decide` rather than `BEq`: `UInt8`'s `==` is the classical one, and a
specification that reached `Classical.choice` would carry it into every theorem
about the stage. -/
def klAsciiBlk (blk : List UInt8) : Bool :=
  decide ((blk.foldl (· ||| ·) 0x00 &&& 0x80) = 0x00)

/-- The document's accumulator: each block's error vector or-ed in, the
`ascii`/`prev_ascii` pair carried, and the gated path skipping a block whose 64
bytes and predecessor are both ASCII.  `bs` is the document; the three prefix
bytes are zero, as the ABI requires, and the padding is `klByte`'s zero.

`gate = true` is the measured path (`S1F_KL_DOC=1` with the gate selected) and
`gate = false` the ungated one; the measured verdict does not depend on which,
which is the statement the gate lemma carries. -/
def klAll (gate : Bool) (bs : List UInt8) : List UInt8 :=
  let win : List UInt8 := 0x00 :: 0x00 :: 0x00 :: bs
  let nb := (bs.length + 63) / 64
  ((List.range nb).foldl
    (fun (st : List UInt8 × Bool) bi =>
      let pre := (win.drop (64 * bi)).take 3
      let blk := (win.drop (64 * bi + 3)).take 64
      let ascii := klAsciiBlk blk
      let skipped := gate && ascii && st.2
      let acc := if skipped then st.1 else List.zipWith (· ||| ·) st.1 (klErrBlk pre blk)
      (acc, ascii))
    (List.replicate 32 0x00, true)).1

/-- `kl_tail_byte`: a byte that can never begin a character — `C0`/`C1` (the
`0xFE` mask) or `F5`..`FF`. -/
def klTailByte (c : UInt8) : Bool := decide ((c &&& 0xFE) = 0xC0) || decide (0xF5 ≤ c)

/-- The stage's verdict, at the ABI's arguments: the accumulator's non-emptiness,
then the tail byte's own test at a document whose length is a whole number of
blocks. -/
def klStage (bs : List UInt8) (n : Nat) (gate : Bool) : Nat :=
  let acc := klAll gate bs
  let err := if acc.all (fun x => decide (x = 0x00)) then 0 else 1
  if decide (n ≠ 0) && decide (n % 64 = 0) && klTailByte (klByte bs (n - 1)) then 1 else err

/-! ### RFC 3629 §4's local condition

The statement's vocabulary, in RFC terms and not in the tables' bits. -/

/-- `UTF8-tail`: `%x80-BF`. -/
def IsContByte (b : UInt8) : Prop := 0x80 ≤ b ∧ b ≤ 0xBF

/-- The position must be a continuation: a lead two bytes back (`p2 ≥ 0xE0`, a
three- or four-byte character) or three bytes back (`p3 ≥ 0xF0`, a four-byte one)
is still inside its character. -/
def NeedsCont (p2 p3 : UInt8) : Prop := 0xE0 ≤ p2 ∨ 0xF0 ≤ p3

/-- The three predicates below are `def`s of RFC arithmetic, so their
`Decidable` instances are stated: `decide` and `by_cases` are what the
characterization is proved and used with, and instance search does not unfold a
`def` on its own. -/
instance decidableIsContByte (b : UInt8) : Decidable (IsContByte b) := by
  unfold IsContByte
  infer_instance

instance decidableNeedsCont (p2 p3 : UInt8) : Decidable (NeedsCont p2 p3) := by
  unfold NeedsCont
  infer_instance

/-- `KlPair p1 c`: `c` may follow `p1` at a position that need not be a
continuation.  The clauses are RFC 3629 §4's productions, read at `p1`'s role and
`c`'s first byte:

* `UTF8-1`: `c` is not a `UTF8-tail` and `p1` is ASCII or a `UTF8-tail`, i.e. the
  character ended at `p1`;
* `UTF8-2 = %xC2-DF UTF8-tail`;
* `UTF8-3 = %xE0 %xA0-BF UTF8-tail`, `%xE1-EC 2( UTF8-tail )`, `%xED %x80-9F
  UTF8-tail` and `%xEE-EF 2( UTF8-tail )`, the four branches the restricted
  first continuation splits into;
* `UTF8-4 = %xF0 %x90-BF 2( UTF8-tail )`, `%xF1-F3 3( UTF8-tail )` and `%xF4
  %x80-8F 2( UTF8-tail )`.

`0xC0`, `0xC1` and `0xF5..0xFF` appear in no clause: they can never begin a
character, and the tail test is what restores the last of them at a document's
end. -/
def KlPair (p1 c : UInt8) : Prop :=
  (¬ IsContByte c ∧ (p1 < 0x80 ∨ IsContByte p1)) ∨
  (0xC2 ≤ p1 ∧ p1 ≤ 0xDF ∧ IsContByte c) ∨
  (p1 = 0xE0 ∧ 0xA0 ≤ c ∧ c ≤ 0xBF) ∨
  ((0xE1 ≤ p1 ∧ p1 ≤ 0xEC) ∨ (0xEE ≤ p1 ∧ p1 ≤ 0xEF)) ∧ IsContByte c ∨
  (p1 = 0xED ∧ 0x80 ≤ c ∧ c ≤ 0x9F) ∨
  (p1 = 0xF0 ∧ 0x90 ≤ c ∧ c ≤ 0xBF) ∨
  (0xF1 ≤ p1 ∧ p1 ≤ 0xF3 ∧ IsContByte c) ∨
  (p1 = 0xF4 ∧ 0x80 ≤ c ∧ c ≤ 0x8F)

instance decidableKlPair (p1 c : UInt8) : Decidable (KlPair p1 c) := by
  unfold KlPair
  infer_instance

/-! ### The nibble reduction

Both sides of the characterization depend on `p1` through its two nibbles and on
`c` through its high nibble, so the 65536 pairs are 4096 table cases.  The lemmas
below are that reduction, stated separately from the decision that follows. -/

/-- The byte `16·hi + lo`. -/
def nib (hi lo : Nat) : UInt8 := UInt8.ofNat (16 * hi + lo)

theorem nib_toNat (hi lo : Nat) (hhi : hi < 16) (hlo : lo < 16) :
    (nib hi lo).toNat = 16 * hi + lo := by
  unfold nib
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

theorem nib_div (hi lo : Nat) (hhi : hi < 16) (hlo : lo < 16) :
    (nib hi lo).toNat / 16 = hi := by
  rw [nib_toNat hi lo hhi hlo]
  omega

theorem nib_mod (hi lo : Nat) (hhi : hi < 16) (hlo : lo < 16) :
    (nib hi lo).toNat % 16 = lo := by
  rw [nib_toNat hi lo hhi hlo]
  omega

/-- The table words agree at a `p1`'s own nibbles. -/
theorem klSc_p1_nib (p1 c : UInt8) :
    klSc p1 c = klSc (nib (p1.toNat / 16) (p1.toNat % 16)) c := by
  have h1 : p1.toNat / 16 < 16 := by have := p1.toNat_lt; omega
  have h2 : p1.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  unfold klSc klAt
  rw [nib_div (p1.toNat / 16) (p1.toNat % 16) h1 h2,
    nib_mod (p1.toNat / 16) (p1.toNat % 16) h1 h2]

/-- The table words read `c`'s high nibble only. -/
theorem klSc_c_nib (p1 c : UInt8) :
    klSc p1 c = klSc p1 (nib (c.toNat / 16) 0) := by
  have h3 : c.toNat / 16 < 16 := by have := c.toNat_lt; omega
  unfold klSc klAt
  rw [nib_div (c.toNat / 16) 0 h3 (by decide)]

/-- The table word is a function of `p1`'s nibbles and `c`'s high nibble. -/
theorem klSc_nib (p1 c : UInt8) :
    klSc p1 c = klSc (nib (p1.toNat / 16) (p1.toNat % 16)) (nib (c.toNat / 16) 0) := by
  rw [klSc_p1_nib, klSc_c_nib]

/-- `16·(n / 16) + n % 16 = n`: the split every endpoint below is read at. -/
theorem sixteen_split (n : Nat) : 16 * (n / 16) + n % 16 = n := Nat.div_add_mod n 16

/-- The canonical `c`'s value: the high nibble times sixteen. -/
theorem nib_high (c : UInt8) : (nib (c.toNat / 16) 0).toNat = 16 * (c.toNat / 16) := by
  rw [nib_toNat (c.toNat / 16) 0 (by have := c.toNat_lt; omega) (by decide)]
  omega

/-- The canonical `p1`'s value: `p1` itself. -/
theorem nib_self (p1 : UInt8) :
    (nib (p1.toNat / 16) (p1.toNat % 16)).toNat = p1.toNat := by
  rw [nib_toNat (p1.toNat / 16) (p1.toNat % 16) (by have := p1.toNat_lt; omega)
    (Nat.mod_lt _ (by decide)), sixteen_split]

/-- The pair condition is a function of the same nibbles: every clause's `c`
interval has an endpoint at a multiple of sixteen or one less, so the low nibble
of `c` cannot move it.  Each of the five clauses is its own interval fact, which is
why the conjunction is stated rather than one arm of it. -/
theorem klPair_c_nib (p1 c : UInt8) :
    KlPair p1 c ↔ KlPair p1 (nib (c.toNat / 16) 0) := by
  have hval := nib_high c
  have hsplit := sixteen_split c.toNat
  have hmod : c.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  have hc : IsContByte c ↔ IsContByte (nib (c.toNat / 16) 0) := by
    unfold IsContByte
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat, hval]
    constructor
    · rintro ⟨g1, g2⟩; exact ⟨by omega, by omega⟩
    · rintro ⟨g1, g2⟩; exact ⟨by omega, by omega⟩
  have h1 : (0xA0 ≤ c ∧ c ≤ 0xBF) ↔
      (0xA0 ≤ nib (c.toNat / 16) 0 ∧ nib (c.toNat / 16) 0 ≤ 0xBF) := by
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat, hval]
    constructor
    · rintro ⟨g1, g2⟩; exact ⟨by omega, by omega⟩
    · rintro ⟨g1, g2⟩; exact ⟨by omega, by omega⟩
  have h2 : (0x80 ≤ c ∧ c ≤ 0x9F) ↔
      (0x80 ≤ nib (c.toNat / 16) 0 ∧ nib (c.toNat / 16) 0 ≤ 0x9F) := by
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat, hval]
    constructor
    · rintro ⟨g1, g2⟩; exact ⟨by omega, by omega⟩
    · rintro ⟨g1, g2⟩; exact ⟨by omega, by omega⟩
  have h3 : (0x90 ≤ c ∧ c ≤ 0xBF) ↔
      (0x90 ≤ nib (c.toNat / 16) 0 ∧ nib (c.toNat / 16) 0 ≤ 0xBF) := by
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat, hval]
    constructor
    · rintro ⟨g1, g2⟩; exact ⟨by omega, by omega⟩
    · rintro ⟨g1, g2⟩; exact ⟨by omega, by omega⟩
  have h4 : (0x80 ≤ c ∧ c ≤ 0x8F) ↔
      (0x80 ≤ nib (c.toNat / 16) 0 ∧ nib (c.toNat / 16) 0 ≤ 0x8F) := by
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat, hval]
    constructor
    · rintro ⟨g1, g2⟩; exact ⟨by omega, by omega⟩
    · rintro ⟨g1, g2⟩; exact ⟨by omega, by omega⟩
  unfold KlPair
  rw [hc, h1, h2, h3, h4]

/-- The pair condition is a function of `p1`'s nibbles: every `p1` clause names a
range whose endpoints are the RFC's own byte values. -/
theorem klPair_p1_nib (p1 c : UInt8) :
    KlPair p1 c ↔ KlPair (nib (p1.toNat / 16) (p1.toNat % 16)) c := by
  have hval := nib_self p1
  unfold KlPair IsContByte
  simp only [UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat, hval,
    ← UInt8.toNat_inj]

/-! ### The 4096 table cases, decided

`lo(p1) × hi(p1) × hi(c)` is 16 × 16 × 16 = 4096 cases, and both characterizations
of the table word are decided at each — 2 × 4096 decided cases. -/

private theorem klSc_nibble_facts (lo hi hic : Fin 16) :
    ((klSc (nib hi.val lo.val) (nib hic.val 0) = 0) ↔
        KlPair (nib hi.val lo.val) (nib hic.val 0)) ∧
      ((klSc (nib hi.val lo.val) (nib hic.val 0) = 0x80) ↔
        (IsContByte (nib hi.val lo.val) ∧ IsContByte (nib hic.val 0))) := by
  revert lo hi hic
  decide

/-- A cleared table word is the local pair condition: `sc`'s seven class bits are
all clear exactly when `KlPair` holds. -/
theorem klSc_zero_iff (p1 c : UInt8) : klSc p1 c = 0 ↔ KlPair p1 c := by
  have h1 : p1.toNat / 16 < 16 := by have := p1.toNat_lt; omega
  have h2 : p1.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  have h3 : c.toNat / 16 < 16 := by have := c.toNat_lt; omega
  rw [klSc_nib p1 c, klPair_c_nib p1 c, klPair_p1_nib p1 (nib (c.toNat / 16) 0)]
  exact (klSc_nibble_facts ⟨p1.toNat % 16, h2⟩ ⟨p1.toNat / 16, h1⟩
    ⟨c.toNat / 16, h3⟩).1

/-- `UTF8-tail` at `p1`'s own nibbles. -/
theorem isCont_p1_nib (p1 : UInt8) :
    IsContByte (nib (p1.toNat / 16) (p1.toNat % 16)) ↔ IsContByte p1 := by
  have hval := nib_self p1
  unfold IsContByte
  simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat, hval]

/-- `UTF8-tail` at `c`'s high nibble. -/
theorem isCont_c_nib (c : UInt8) :
    IsContByte (nib (c.toNat / 16) 0) ↔ IsContByte c := by
  have hval := nib_high c
  have hsplit := sixteen_split c.toNat
  have hmod : c.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  unfold IsContByte
  simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat, hval]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩

/-- The table word is `twoConts` exactly when the pair is two continuations. -/
theorem klSc_twoConts (p1 c : UInt8) :
    klSc p1 c = 0x80 ↔ (IsContByte p1 ∧ IsContByte c) := by
  have h1 : p1.toNat / 16 < 16 := by have := p1.toNat_lt; omega
  have h2 : p1.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  have h3 : c.toNat / 16 < 16 := by have := c.toNat_lt; omega
  rw [klSc_nib p1 c,
    (klSc_nibble_facts ⟨p1.toNat % 16, h2⟩ ⟨p1.toNat / 16, h1⟩
      ⟨c.toNat / 16, h3⟩).2,
    isCont_p1_nib, isCont_c_nib]

/-- **C59, the per-position characterization.**  A position's error byte is zero
exactly when the position is locally admissible given the continuation
requirement the byte one back imposes: if a lead two or three bytes back still
owns the position (`NeedsCont`) then both it and this byte are `UTF8-tail`s, and
otherwise the two-byte structure `KlPair` holds.

"Locally" is load-bearing and is not a hedge.  The statement does not say the
bytes before it are themselves admissible, so a window can be zero here while the
sequence is broken one or two places earlier: at `klErrByte 0xF0 0x41 0x80 0x80 =
0` the position one place earlier is `0x82` (`twoConts | tooLong`, from the `0x41`
that follows the `0xF0` lead) and the one two places earlier is `0x01`
(`tooShort`).  A reader who took this for a statement about the four bytes around
the position would have a claim the tables refute, twice over — and would also be
reading the pair (`0x41`, `0x80`) as admitted, which `KlPair 0x41 0x80 = false`
denies.

The decomposition is `err = sc ^ must`: `must` is the bit `subsSat_high_bit` reads,
`sc` is the table word `klSc_zero_iff` and `klSc_twoConts` characterize, and the
case count is the 2 × 4096 the decided table facts cover. -/
theorem klErrByte_eq_zero_iff (p3 p2 p1 c : UInt8) :
    klErrByte p3 p2 p1 c = 0 ↔
      (NeedsCont p2 p3 ∧ IsContByte p1 ∧ IsContByte c) ∨
        (¬ NeedsCont p2 p3 ∧ KlPair p1 c) := by
  have hm : klMust p2 p3 = if NeedsCont p2 p3 then 0x80 else 0x00 := rfl
  unfold klErrByte
  rw [hm, UInt8.xor_eq_zero_iff]
  by_cases h : NeedsCont p2 p3
  · rw [ite_eq_left h]
    constructor
    · intro he
      exact Or.inl ⟨h, (klSc_twoConts p1 c).mp he⟩
    · rintro (⟨-, h1, h2⟩ | ⟨hn, -⟩)
      · exact (klSc_twoConts p1 c).mpr ⟨h1, h2⟩
      · exact absurd h hn
  · rw [ite_eq_right h]
    constructor
    · intro he
      exact Or.inr ⟨h, (klSc_zero_iff p1 c).mp he⟩
    · rintro (⟨hn, -⟩ | ⟨-, hp⟩)
      · exact absurd hn h
      · exact (klSc_zero_iff p1 c).mpr hp

theorem klErrByte_eq_klSc_xor_klMust (p3 p2 p1 c : UInt8) :
    klErrByte p3 p2 p1 c = klSc p1 c ^^^ klMust p2 p3 := rfl

/-! ### The eight refused witnesses

One window per class the tables distinguish, and the count is the vocabulary's
eight.  Each is a position's own error byte, so a reader sees which clause of
`KlPair` (or which half of `NeedsCont`'s obligation) the window violates. -/

/-- `tooShort`: a lead at the end of the scanned window, with no continuation
after it. -/
theorem refused_tooShort : klErrByte 0x00 0x00 0xC2 0x41 = tooShort := by decide

/-- `tooLong`: a continuation after an ASCII byte. -/
theorem refused_tooLong : klErrByte 0x00 0x00 0x41 0x80 = tooLong := by decide

/-- `overlong3`: `E0`'s first continuation below `A0`. -/
theorem refused_overlong3 : klErrByte 0x00 0x00 0xE0 0x80 = overlong3 := by decide

/-- `tooLarge`: `F4`'s first continuation above `8F`. -/
theorem refused_tooLarge : klErrByte 0x00 0x00 0xF4 0x90 = tooLarge := by decide

/-- `surrogate`: `ED`'s first continuation above `9F`. -/
theorem refused_surrogate : klErrByte 0x00 0x00 0xED 0xA0 = surrogate := by decide

/-- `overlong2`: `C0` never begins a character. -/
theorem refused_overlong2 : klErrByte 0x00 0x00 0xC0 0x80 = overlong2 := by decide

/-- `tooLarge1000`: `F0`'s first continuation below `90`, the header's
`OVERLONG_4` bit. -/
theorem refused_tooLarge1000 : klErrByte 0x00 0x00 0xF0 0x80 = tooLarge1000 := by decide

/-- `twoConts`: two continuations at a position no lead demands one at. -/
theorem refused_twoConts : klErrByte 0x00 0x00 0x80 0x80 = twoConts := by decide

/-- The eight witnesses are exactly the eight classes: no two of the eight values
are equal, and every one of them is a class the vocabulary names. -/
theorem refused_witnesses_distinct :
    [tooShort, tooLong, overlong3, tooLarge, surrogate, overlong2, tooLarge1000,
      twoConts].length = 8 ∧
    [tooShort, tooLong, overlong3, tooLarge, surrogate, overlong2, tooLarge1000,
      twoConts].foldl (· ||| ·) 0x00 = 0xFF := by
  decide

/-! ### The accepted witnesses

The other direction, at the windows whose classes are all clear. -/

/-- ASCII positions: the character before this one ended, and this byte starts
another. -/
theorem accepted_ascii : klErrByte 0x41 0x41 0x41 0x41 = 0 := by decide

/-- `UTF8-2`'s tail. -/
theorem accepted_two : klErrByte 0x00 0x00 0xC2 0xA9 = 0 := by decide

/-- `UTF8-3`'s restricted first continuation, `%xE0 %xA0-BF`. -/
theorem accepted_three_E0 : klErrByte 0x00 0x00 0xE0 0xA0 = 0 := by decide

/-- `UTF8-3`'s surrogate branch's upper continuation, `%xED %x80-9F`. -/
theorem accepted_three_ED : klErrByte 0x00 0x00 0xED 0x9F = 0 := by decide

/-- `UTF8-4`'s restricted first continuation, `%xF0 %x90-BF`. -/
theorem accepted_four_F0 : klErrByte 0x00 0x00 0xF0 0x90 = 0 := by decide

/-- `UTF8-4`'s too-large branch's upper continuation, `%xF4 %x80-8F`. -/
theorem accepted_four_F4 : klErrByte 0x00 0x00 0xF4 0x8F = 0 := by decide

/-- The middle of a four-byte character: a lead three bytes back demands a
continuation here, and this byte is one. -/
theorem accepted_four_middle : klErrByte 0xF0 0x90 0x80 0x80 = 0 := by decide


/-! ### The local condition across a window

`klErrByte` is one position's error byte; the verdict is zero exactly when every
position of the staged window reads zero.  The three definitions below name that
reading: the window starting at byte `t` (`s[t]`, `s[t+1]`, `s[t+2]` precede
`s[t+3]`), the conjunction over the first `L` windows, and the byte predicate
"ASCII or a continuation" — a byte that may end a character. -/

/-- The window starting at byte `t`: the three carry bytes and the byte they
precede. -/
def klErrWin (s : List UInt8) (t : Nat) : Prop :=
  klErrByte (klByte s t) (klByte s (t + 1)) (klByte s (t + 2)) (klByte s (t + 3)) = 0

/-- Every window of the first `L` reads zero.  `L` is the block count's byte
count, so the windows are the positions the loop stages. -/
def klErrAll (s : List UInt8) (L : Nat) : Prop := ∀ t, t < L → klErrWin s t

/-- A byte that may end a character: ASCII or a continuation. -/
def IsCharEnd (b : UInt8) : Prop := b.toNat < 0x80 ∨ IsContByte b

theorem needsCont_nat (p2 p3 : UInt8) :
    NeedsCont p2 p3 ↔ (224 ≤ p2.toNat ∨ 240 ≤ p3.toNat) := by
  unfold NeedsCont
  simp only [UInt8.le_iff_toNat_le]
  exact Iff.rfl

theorem needsCont_false_iff (p2 p3 : UInt8) :
    ¬ NeedsCont p2 p3 ↔ (p2.toNat < 224 ∧ p3.toNat < 240) := by
  rw [needsCont_nat]
  constructor
  · intro h
    exact ⟨Nat.not_le.mp fun h1 => h (Or.inl h1),
      Nat.not_le.mp fun h2 => h (Or.inr h2)⟩
  · rintro ⟨h1, h2⟩ (h | h)
    · exact (Nat.not_le.mpr h1) h
    · exact (Nat.not_le.mpr h2) h

theorem isCharEnd_nat (b : UInt8) :
    IsCharEnd b ↔ (b.toNat < 128 ∨ (128 ≤ b.toNat ∧ b.toNat ≤ 191)) := by
  unfold IsCharEnd IsContByte
  simp only [UInt8.le_iff_toNat_le]
  exact Iff.rfl

theorem isCharEnd_lt (b : UInt8) (h : IsCharEnd b) : b.toNat < 192 := by
  rw [isCharEnd_nat] at h; omega

theorem not_cont_of_lt (b : UInt8) (h : b.toNat < 128) : ¬ IsContByte b := by
  rintro ⟨h1, -⟩
  rw [UInt8.le_iff_toNat_le] at h1
  have h80 : (0x80 : UInt8).toNat = 128 := rfl
  omega

theorem not_needsCont_of_lt {p2 p3 : UInt8} (h2 : p2.toNat < 224) (h3 : p3.toNat < 240) :
    ¬ NeedsCont p2 p3 := by
  rw [needsCont_nat]
  rintro (h | h)
  · exact (Nat.not_le.mpr h2) h
  · exact (Nat.not_le.mpr h3) h

theorem cont_of_bounds {b : UInt8} (h1 : 128 ≤ b.toNat) (h2 : b.toNat ≤ 191) :
    IsContByte b := by
  unfold IsContByte
  constructor
  · rw [UInt8.le_iff_toNat_le]; simpa using h1
  · rw [UInt8.le_iff_toNat_le]; simpa using h2

/-! ### The `KlPair` clauses, in the form a character supplies them -/

theorem klPair_iff (p1 c : UInt8) :
    KlPair p1 c ↔
      (¬ IsContByte c ∧ IsCharEnd p1) ∨
      (0xC2 ≤ p1 ∧ p1 ≤ 0xDF ∧ IsContByte c) ∨
      (p1 = 0xE0 ∧ 0xA0 ≤ c ∧ c ≤ 0xBF) ∨
      ((0xE1 ≤ p1 ∧ p1 ≤ 0xEC) ∨ (0xEE ≤ p1 ∧ p1 ≤ 0xEF)) ∧ IsContByte c ∨
      (p1 = 0xED ∧ 0x80 ≤ c ∧ c ≤ 0x9F) ∨
      (p1 = 0xF0 ∧ 0x90 ≤ c ∧ c ≤ 0xBF) ∨
      (0xF1 ≤ p1 ∧ p1 ≤ 0xF3 ∧ IsContByte c) ∨
      (p1 = 0xF4 ∧ 0x80 ≤ c ∧ c ≤ 0x8F) := by
  unfold KlPair IsCharEnd
  simp only [UInt8.lt_iff_toNat_lt]
  exact Iff.rfl

theorem ok_right (a b c d : UInt8) (hn : ¬ NeedsCont b a) (hp : KlPair c d) :
    klErrByte a b c d = 0 :=
  (klErrByte_eq_zero_iff a b c d).mpr (Or.inr ⟨hn, hp⟩)

theorem ok_left (a b c d : UInt8) (hn : NeedsCont b a) (hc : IsContByte c)
    (hd : IsContByte d) : klErrByte a b c d = 0 :=
  (klErrByte_eq_zero_iff a b c d).mpr (Or.inl ⟨hn, hc, hd⟩)

/-! ### Reading a character's bytes off the stream -/

theorem klByte_drop (s : List UInt8) (i m : Nat) :
    klByte s (i + m) = klByte (s.drop i) m := by
  unfold klByte
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem klByte_of_drop_eq {s : List UInt8} {i : Nat} {cs rs : List UInt8}
    (h : s.drop i = cs ++ rs) {m : Nat} (hm : m < cs.length) : klByte s (i + m) = cs[m] := by
  rw [klByte_drop]
  unfold klByte
  rw [h, List.getD_eq_getElem?_getD, List.getElem?_append_left hm,
    List.getElem?_eq_getElem hm]
  rfl

theorem win_shift (s : List UInt8) (j : Nat) :
    klErrWin s j = (klErrByte (klByte s j) (klByte s (j + 1)) (klByte s (j + 2))
      (klByte s (j + 3)) = 0) := rfl

theorem win_m0 {s : List UInt8} {i : Nat} (hi : 3 ≤ i) :
    klErrWin s (i - 3) = (klErrByte (klByte s (i - 3)) (klByte s (i - 2)) (klByte s (i - 1))
      (klByte s i) = 0) := by
  rw [win_shift]
  rw [show i - 3 + 1 = i - 2 from by omega, show i - 3 + 2 = i - 1 from by omega,
    show i - 3 + 3 = i from by omega]

theorem win_m1 {s : List UInt8} {i : Nat} (hi : 3 ≤ i) :
    klErrWin s (i - 2) = (klErrByte (klByte s (i - 2)) (klByte s (i - 1)) (klByte s i)
      (klByte s (i + 1)) = 0) := by
  rw [win_shift]
  rw [show i - 2 + 1 = i - 1 from by omega, show i - 2 + 2 = i from by omega,
    show i - 2 + 3 = i + 1 from by omega]

theorem win_m2 {s : List UInt8} {i : Nat} (hi : 3 ≤ i) :
    klErrWin s (i - 1) = (klErrByte (klByte s (i - 1)) (klByte s i) (klByte s (i + 1))
      (klByte s (i + 2)) = 0) := by
  rw [win_shift]
  rw [show i - 1 + 1 = i from by omega, show i - 1 + 2 = i + 1 from by omega,
    show i - 1 + 3 = i + 2 from by omega]

theorem win_m3 (s : List UInt8) (i : Nat) :
    klErrWin s i = (klErrByte (klByte s i) (klByte s (i + 1)) (klByte s (i + 2))
      (klByte s (i + 3)) = 0) := rfl


theorem klByte_drop_any (s : List UInt8) (i m : Nat) :
    klByte s (i + m) = (s.drop i)[m]?.getD 0x00 := by
  rw [klByte_drop]
  unfold klByte
  rw [List.getD_eq_getElem?_getD]

theorem klByte_prefix {s : List UInt8} {i : Nat} {cs rs : List UInt8} (h : s.drop i = cs ++ rs)
    {m : Nat} (hm : m < cs.length) : klByte s (i + m) = (cs[m]?).getD 0x00 := by
  rw [klByte_drop]
  unfold klByte
  rw [h, List.getD_eq_getElem?_getD, List.getElem?_append, ite_eq_left hm]

/-! ### One character's windows

The four helpers below are the character step at each byte length: given the
carry facts at the character's first byte and the pair/clause facts its
constructor supplies, the windows the character's bytes occupy read zero and the
carry at the position after it is the one the next character needs. -/

theorem not_cont_of_lead {b : UInt8} (h : 192 ≤ b.toNat) : ¬ IsContByte b := by
  rintro ⟨h1, h2⟩
  rw [UInt8.le_iff_toNat_le] at h2
  have hbf : (0xBF : UInt8).toNat = 191 := rfl
  omega

theorem needsCont_of_lead {p2 p3 : UInt8} (h : 224 ≤ p2.toNat) : NeedsCont p2 p3 := by
  rw [needsCont_nat]; omega

theorem needsCont_of_lead3 {p2 p3 : UInt8} (h : 240 ≤ p3.toNat) : NeedsCont p2 p3 := by
  rw [needsCont_nat]; omega

theorem cont_le {b : UInt8} (h : IsContByte b) : b.toNat ≤ 191 := by
  have := h.2
  rw [UInt8.le_iff_toNat_le] at this
  have hbf : (0xBF : UInt8).toNat = 191 := rfl
  omega

theorem char1 (s : List UInt8) (i : Nat) (hi : 3 ≤ i)
    (hn : ¬ NeedsCont (klByte s (i - 2)) (klByte s (i - 3)))
    (he : IsCharEnd (klByte s (i - 1)))
    (hc : ¬ IsContByte (klByte s i)) (hce : IsCharEnd (klByte s i)) :
    klErrWin s (i - 3) ∧ ¬ NeedsCont (klByte s (i - 1)) (klByte s (i - 2)) ∧
      IsCharEnd (klByte s i) := by
  refine ⟨?_, ?_, hce⟩
  · rw [win_m0 hi]
    exact ok_right _ _ _ _ hn (klPair_iff _ _ |>.mpr (Or.inl ⟨hc, he⟩))
  · refine not_needsCont_of_lt ?_ ?_
    · have := isCharEnd_lt _ he; omega
    · have := (needsCont_false_iff _ _).mp hn; omega

theorem char2 (s : List UInt8) (i : Nat) (hi : 3 ≤ i)
    (hn : ¬ NeedsCont (klByte s (i - 2)) (klByte s (i - 3)))
    (he : IsCharEnd (klByte s (i - 1)))
    (hc : ¬ IsContByte (klByte s i)) (hi224 : (klByte s i).toNat < 224)
    (hpair : KlPair (klByte s i) (klByte s (i + 1)))
    (hcont : IsContByte (klByte s (i + 1))) :
    klErrWin s (i - 3) ∧ klErrWin s (i - 2) ∧
      ¬ NeedsCont (klByte s i) (klByte s (i - 1)) ∧ IsCharEnd (klByte s (i + 1)) := by
  have hnc : ¬ NeedsCont (klByte s (i - 1)) (klByte s (i - 2)) := by
    refine not_needsCont_of_lt ?_ ?_
    · have := isCharEnd_lt _ he; omega
    · have := (needsCont_false_iff _ _).mp hn; omega
  refine ⟨?_, ?_, ?_, Or.inr hcont⟩
  · rw [win_m0 hi]
    exact ok_right _ _ _ _ hn (klPair_iff _ _ |>.mpr (Or.inl ⟨hc, he⟩))
  · rw [win_m1 hi]
    exact ok_right _ _ _ _ hnc hpair
  · refine not_needsCont_of_lt hi224 ?_
    have := isCharEnd_lt _ he; omega

theorem char3 (s : List UInt8) (i : Nat) (hi : 3 ≤ i)
    (hn : ¬ NeedsCont (klByte s (i - 2)) (klByte s (i - 3)))
    (he : IsCharEnd (klByte s (i - 1)))
    (hc : ¬ IsContByte (klByte s i)) (hpos : 224 ≤ (klByte s i).toNat)
    (hi240 : (klByte s i).toNat < 240)
    (hpair : KlPair (klByte s i) (klByte s (i + 1)))
    (hc1 : IsContByte (klByte s (i + 1))) (hc2 : IsContByte (klByte s (i + 2))) :
    klErrWin s (i - 3) ∧ klErrWin s (i - 2) ∧ klErrWin s (i - 1) ∧
      ¬ NeedsCont (klByte s (i + 1)) (klByte s i) ∧ IsCharEnd (klByte s (i + 2)) := by
  have hnc : ¬ NeedsCont (klByte s (i - 1)) (klByte s (i - 2)) := by
    refine not_needsCont_of_lt ?_ ?_
    · have := isCharEnd_lt _ he; omega
    · have := (needsCont_false_iff _ _).mp hn; omega
  refine ⟨?_, ?_, ?_, ?_, Or.inr hc2⟩
  · rw [win_m0 hi]
    exact ok_right _ _ _ _ hn (klPair_iff _ _ |>.mpr (Or.inl ⟨hc, he⟩))
  · rw [win_m1 hi]
    exact ok_right _ _ _ _ hnc hpair
  · rw [win_m2 hi]
    exact ok_left _ _ _ _ (needsCont_of_lead hpos) hc1 hc2
  · refine not_needsCont_of_lt ?_ hi240
    have := cont_le hc1; omega

theorem char4 (s : List UInt8) (i : Nat) (hi : 3 ≤ i)
    (hn : ¬ NeedsCont (klByte s (i - 2)) (klByte s (i - 3)))
    (he : IsCharEnd (klByte s (i - 1)))
    (hc : ¬ IsContByte (klByte s i)) (hpos : 240 ≤ (klByte s i).toNat)
    (hpair : KlPair (klByte s i) (klByte s (i + 1)))
    (hc1 : IsContByte (klByte s (i + 1))) (hc2 : IsContByte (klByte s (i + 2)))
    (hc3 : IsContByte (klByte s (i + 3))) :
    klErrWin s (i - 3) ∧ klErrWin s (i - 2) ∧ klErrWin s (i - 1) ∧ klErrWin s i ∧
      ¬ NeedsCont (klByte s (i + 2)) (klByte s (i + 1)) ∧
      IsCharEnd (klByte s (i + 3)) := by
  have hnc : ¬ NeedsCont (klByte s (i - 1)) (klByte s (i - 2)) := by
    refine not_needsCont_of_lt ?_ ?_
    · have := isCharEnd_lt _ he; omega
    · have := (needsCont_false_iff _ _).mp hn; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, Or.inr hc3⟩
  · rw [win_m0 hi]
    exact ok_right _ _ _ _ hn (klPair_iff _ _ |>.mpr (Or.inl ⟨hc, he⟩))
  · rw [win_m1 hi]
    exact ok_right _ _ _ _ hnc hpair
  · rw [win_m2 hi]
    exact ok_left _ _ _ _ (needsCont_of_lead (by omega)) hc1 hc2
  · rw [win_m3]
    exact ok_left _ _ _ _ (needsCont_of_lead3 hpos) hc2 hc3
  · refine not_needsCont_of_lt ?_ ?_
    · have := cont_le hc2; omega
    · have := cont_le hc1; omega


theorem not_cont_of_ge {b : UInt8} (h : 0xC2 ≤ b) : ¬ IsContByte b := by
  apply not_cont_of_lead
  rw [UInt8.le_iff_toNat_le] at h
  have hc2 : (0xC2 : UInt8).toNat = 194 := rfl
  omega

theorem drop_of_literal {s : List UInt8} {i : Nat} {v : Bytes}
    (hl : ByteString.literal (s.drop i) = v) : s.drop i = v.data.toList := by
  have := congrArg (fun x : Bytes => x.data.toList) hl
  simpa [ByteString.data_toList_literal] using this

theorem char_ok {b : Bytes} {c : Nat} {rest : Bytes} (h : Utf8Char b c rest) :
    ∀ (s : List UInt8) (i : Nat), ByteString.literal (s.drop i) = b → 3 ≤ i →
    ¬ NeedsCont (klByte s (i - 2)) (klByte s (i - 3)) →
    IsCharEnd (klByte s (i - 1)) →
    (∀ m, m < b.length - rest.length → klErrWin s (i - 3 + m)) ∧
    ¬ NeedsCont (klByte s (i - 3 + (b.length - rest.length) + 1))
        (klByte s (i - 3 + (b.length - rest.length))) ∧
    IsCharEnd (klByte s (i - 3 + (b.length - rest.length) + 2)) := by
  induction h with
  | one hb =>
      intro s i hl hi hn he
      have hdrop := drop_of_literal hl
      simp only [ByteString.data_toList_cons] at hdrop
      have hb0 : klByte s i = (s.drop i)[0]?.getD 0x00 := by
        simpa using klByte_drop_any s i 0
      rw [hdrop] at hb0
      simp only [List.getElem?_cons_zero, Option.getD_some] at hb0
      have hlt : (klByte s i).toNat < 128 := by
        rw [hb0]
        rw [UInt8.lt_iff_toNat_lt] at hb
        simpa using hb
      have hcn : ¬ IsContByte (klByte s i) := not_cont_of_lt _ hlt
      have hce : IsCharEnd (klByte s i) := Or.inl hlt
      obtain ⟨h0, h1, h2⟩ := char1 s i hi hn he hcn hce
      simp only [ByteString.length_cons]
      rw [show ∀ a : Nat, (a + 1) - a = 1 from fun a => by omega]
      refine ⟨?_, ?_, ?_⟩
      · intro m hm
        have hm0 : m = 0 := by omega
        subst hm0
        simpa using h0
      · rw [show i - 3 + 1 + 1 = i - 1 from by omega,
            show i - 3 + 1 = i - 2 from by omega]
        exact h1
      · simpa [show i - 3 + 1 + 2 = i from by omega] using h2
  | two h0 h0' h1 h1' =>
      intro s i hl hi hn he
      have hdrop := drop_of_literal hl
      simp only [ByteString.data_toList_cons] at hdrop
      have hb0 : klByte s i = (s.drop i)[0]?.getD 0x00 := by
        simpa using klByte_drop_any s i 0
      rw [hdrop] at hb0
      simp only [List.getElem?_cons_zero, Option.getD_some] at hb0
      have hb1 := klByte_drop_any s i 1
      rw [hdrop] at hb1
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hb1
      have h0i : 0xC2 ≤ klByte s i := by rw [hb0]; exact h0
      have h0i' : klByte s i ≤ 0xDF := by rw [hb0]; exact h0'
      have hcn : ¬ IsContByte (klByte s i) := not_cont_of_ge h0i
      have hcont : IsContByte (klByte s (i + 1)) := by rw [hb1]; exact ⟨h1, h1'⟩
      have hpair : KlPair (klByte s i) (klByte s (i + 1)) := by
        rw [hb0, hb1]
        exact (klPair_iff _ _).mpr (Or.inr (Or.inl ⟨h0, h0', h1, h1'⟩))
      have hi224 : (klByte s i).toNat < 224 := by
        rw [UInt8.le_iff_toNat_le] at h0i'
        have hdf : (0xDF : UInt8).toNat = 223 := rfl
        omega
      obtain ⟨hc0, hc1, hc2, hc3⟩ := char2 s i hi hn he hcn hi224 hpair hcont
      simp only [ByteString.length_cons]
      rw [show ∀ a : Nat, ((a + 1) + 1) - a = 2 from fun a => by omega]
      refine ⟨?_, ?_, ?_⟩
      · intro m hm
        have hm' : m = 0 ∨ m = 1 := by omega
        rcases hm' with rfl | rfl
        · simpa using hc0
        · simpa [show i - 3 + 1 = i - 2 from by omega] using hc1
      · rw [show i - 3 + 2 + 1 = i from by omega,
            show i - 3 + 2 = i - 1 from by omega]
        exact hc2
      · simpa [show i - 3 + 2 + 2 = i + 1 from by omega] using hc3
  | three₀ h1 h1' h2 h2' =>
      intro s i hl hi hn he
      have hdrop := drop_of_literal hl
      simp only [ByteString.data_toList_cons] at hdrop
      have hb0 : klByte s i = (s.drop i)[0]?.getD 0x00 := by
        simpa using klByte_drop_any s i 0
      rw [hdrop] at hb0
      simp only [List.getElem?_cons_zero, Option.getD_some] at hb0
      have hb1 := klByte_drop_any s i 1
      rw [hdrop] at hb1
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hb1
      have hb2 := klByte_drop_any s i 2
      rw [hdrop] at hb2
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hb2
      have hcn : ¬ IsContByte (klByte s i) := by
        rw [hb0]; exact not_cont_of_ge (by decide)
      have hpos : 224 ≤ (klByte s i).toNat := by rw [hb0]; decide
      have hi240 : (klByte s i).toNat < 240 := by rw [hb0]; decide
      have hcont1 : IsContByte (klByte s (i + 1)) := by
        rw [hb1]
        exact ⟨UInt8.le_trans (by decide) h1, UInt8.le_trans h1' (by decide)⟩
      have hcont2 : IsContByte (klByte s (i + 2)) := by rw [hb2]; exact ⟨h2, h2'⟩
      have hpair : KlPair (klByte s i) (klByte s (i + 1)) := by
        rw [hb0, hb1]
        exact (klPair_iff _ _).mpr (Or.inr (Or.inr (Or.inl ⟨rfl, h1, h1'⟩)))
      obtain ⟨hc0, hc1, hc2, hc3, hc4⟩ :=
        char3 s i hi hn he hcn hpos hi240 hpair hcont1 hcont2
      simp only [ByteString.length_cons]
      rw [show ∀ a : Nat, (((a + 1) + 1) + 1) - a = 3 from fun a => by omega]
      refine ⟨?_, ?_, ?_⟩
      · intro m hm
        have hm' : m = 0 ∨ m = 1 ∨ m = 2 := by omega
        rcases hm' with rfl | rfl | rfl
        · simpa using hc0
        · simpa [show i - 3 + 1 = i - 2 from by omega] using hc1
        · simpa [show i - 3 + 2 = i - 1 from by omega] using hc2
      · rw [show i - 3 + 3 + 1 = i + 1 from by omega,
            show i - 3 + 3 = i from by omega]
        exact hc3
      · simpa [show i - 3 + 3 + 2 = i + 2 from by omega] using hc4
  | three₁ h0 h0' h1 h1' h2 h2' =>
      intro s i hl hi hn he
      have hdrop := drop_of_literal hl
      simp only [ByteString.data_toList_cons] at hdrop
      have hb0 : klByte s i = (s.drop i)[0]?.getD 0x00 := by
        simpa using klByte_drop_any s i 0
      rw [hdrop] at hb0
      simp only [List.getElem?_cons_zero, Option.getD_some] at hb0
      have hb1 := klByte_drop_any s i 1
      rw [hdrop] at hb1
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hb1
      have hb2 := klByte_drop_any s i 2
      rw [hdrop] at hb2
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hb2
      have h0i : 0xE1 ≤ klByte s i := by rw [hb0]; exact h0
      have hcn : ¬ IsContByte (klByte s i) :=
        not_cont_of_ge (UInt8.le_trans (by decide) h0i)
      have hpos : 224 ≤ (klByte s i).toNat := by
        have hn : (0xE1 : UInt8).toNat ≤ (klByte s i).toNat := by
          rw [hb0]; exact (UInt8.le_iff_toNat_le).mp h0
        have hv : (0xE1 : UInt8).toNat = 225 := by decide
        omega
      have hi240 : (klByte s i).toNat < 240 := by
        have hn : (klByte s i).toNat ≤ (0xEC : UInt8).toNat := by
          rw [hb0]; exact (UInt8.le_iff_toNat_le).mp h0'
        have hv : (0xEC : UInt8).toNat = 236 := by decide
        omega
      have hcont1 : IsContByte (klByte s (i + 1)) := by
        rw [hb1]
        exact ⟨UInt8.le_trans (by decide) h1, UInt8.le_trans h1' (by decide)⟩
      have hcont2 : IsContByte (klByte s (i + 2)) := by rw [hb2]; exact ⟨h2, h2'⟩
      have hpair : KlPair (klByte s i) (klByte s (i + 1)) := by
        rw [hb0, hb1]
        exact (klPair_iff _ _).mpr
          (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl ⟨h0, h0'⟩, h1, h1'⟩))))
      obtain ⟨hc0, hc1, hc2, hc3, hc4⟩ :=
        char3 s i hi hn he hcn hpos hi240 hpair hcont1 hcont2
      simp only [ByteString.length_cons]
      rw [show ∀ a : Nat, (((a + 1) + 1) + 1) - a = 3 from fun a => by omega]
      refine ⟨?_, ?_, ?_⟩
      · intro m hm
        have hm' : m = 0 ∨ m = 1 ∨ m = 2 := by omega
        rcases hm' with rfl | rfl | rfl
        · simpa using hc0
        · simpa [show i - 3 + 1 = i - 2 from by omega] using hc1
        · simpa [show i - 3 + 2 = i - 1 from by omega] using hc2
      · rw [show i - 3 + 3 + 1 = i + 1 from by omega,
            show i - 3 + 3 = i from by omega]
        exact hc3
      · simpa [show i - 3 + 3 + 2 = i + 2 from by omega] using hc4
  | three₂ h1 h1' h2 h2' =>
      intro s i hl hi hn he
      have hdrop := drop_of_literal hl
      simp only [ByteString.data_toList_cons] at hdrop
      have hb0 : klByte s i = (s.drop i)[0]?.getD 0x00 := by
        simpa using klByte_drop_any s i 0
      rw [hdrop] at hb0
      simp only [List.getElem?_cons_zero, Option.getD_some] at hb0
      have hb1 := klByte_drop_any s i 1
      rw [hdrop] at hb1
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hb1
      have hb2 := klByte_drop_any s i 2
      rw [hdrop] at hb2
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hb2
      have hcn : ¬ IsContByte (klByte s i) := by
        rw [hb0]; exact not_cont_of_ge (by decide)
      have hpos : 224 ≤ (klByte s i).toNat := by rw [hb0]; decide
      have hi240 : (klByte s i).toNat < 240 := by rw [hb0]; decide
      have hcont1 : IsContByte (klByte s (i + 1)) := by
        rw [hb1]
        exact ⟨UInt8.le_trans (by decide) h1, UInt8.le_trans h1' (by decide)⟩
      have hcont2 : IsContByte (klByte s (i + 2)) := by rw [hb2]; exact ⟨h2, h2'⟩
      have hpair : KlPair (klByte s i) (klByte s (i + 1)) := by
        rw [hb0, hb1]
        exact (klPair_iff _ _).mpr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨rfl, h1, h1'⟩)))))
      obtain ⟨hc0, hc1, hc2, hc3, hc4⟩ :=
        char3 s i hi hn he hcn hpos hi240 hpair hcont1 hcont2
      simp only [ByteString.length_cons]
      rw [show ∀ a : Nat, (((a + 1) + 1) + 1) - a = 3 from fun a => by omega]
      refine ⟨?_, ?_, ?_⟩
      · intro m hm
        have hm' : m = 0 ∨ m = 1 ∨ m = 2 := by omega
        rcases hm' with rfl | rfl | rfl
        · simpa using hc0
        · simpa [show i - 3 + 1 = i - 2 from by omega] using hc1
        · simpa [show i - 3 + 2 = i - 1 from by omega] using hc2
      · rw [show i - 3 + 3 + 1 = i + 1 from by omega,
            show i - 3 + 3 = i from by omega]
        exact hc3
      · simpa [show i - 3 + 3 + 2 = i + 2 from by omega] using hc4
  | three₃ h0 h0' h1 h1' h2 h2' =>
      intro s i hl hi hn he
      have hdrop := drop_of_literal hl
      simp only [ByteString.data_toList_cons] at hdrop
      have hb0 : klByte s i = (s.drop i)[0]?.getD 0x00 := by
        simpa using klByte_drop_any s i 0
      rw [hdrop] at hb0
      simp only [List.getElem?_cons_zero, Option.getD_some] at hb0
      have hb1 := klByte_drop_any s i 1
      rw [hdrop] at hb1
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hb1
      have hb2 := klByte_drop_any s i 2
      rw [hdrop] at hb2
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hb2
      have h0i : 0xEE ≤ klByte s i := by rw [hb0]; exact h0
      have hcn : ¬ IsContByte (klByte s i) :=
        not_cont_of_ge (UInt8.le_trans (by decide) h0i)
      have hpos : 224 ≤ (klByte s i).toNat := by
        have hn : (0xEE : UInt8).toNat ≤ (klByte s i).toNat := by
          rw [hb0]; exact (UInt8.le_iff_toNat_le).mp h0
        have hv : (0xEE : UInt8).toNat = 238 := by decide
        omega
      have hi240 : (klByte s i).toNat < 240 := by
        rw [hb0]; rw [UInt8.le_iff_toNat_le] at h0'
        have hef : (0xEF : UInt8).toNat = 239 := rfl
        omega
      have hcont1 : IsContByte (klByte s (i + 1)) := by
        rw [hb1]
        exact ⟨UInt8.le_trans (by decide) h1, UInt8.le_trans h1' (by decide)⟩
      have hcont2 : IsContByte (klByte s (i + 2)) := by rw [hb2]; exact ⟨h2, h2'⟩
      have hpair : KlPair (klByte s i) (klByte s (i + 1)) := by
        rw [hb0, hb1]
        exact (klPair_iff _ _).mpr
          (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr ⟨h0, h0'⟩, h1, h1'⟩))))
      obtain ⟨hc0, hc1, hc2, hc3, hc4⟩ :=
        char3 s i hi hn he hcn hpos hi240 hpair hcont1 hcont2
      simp only [ByteString.length_cons]
      rw [show ∀ a : Nat, (((a + 1) + 1) + 1) - a = 3 from fun a => by omega]
      refine ⟨?_, ?_, ?_⟩
      · intro m hm
        have hm' : m = 0 ∨ m = 1 ∨ m = 2 := by omega
        rcases hm' with rfl | rfl | rfl
        · simpa using hc0
        · simpa [show i - 3 + 1 = i - 2 from by omega] using hc1
        · simpa [show i - 3 + 2 = i - 1 from by omega] using hc2
      · rw [show i - 3 + 3 + 1 = i + 1 from by omega,
            show i - 3 + 3 = i from by omega]
        exact hc3
      · simpa [show i - 3 + 3 + 2 = i + 2 from by omega] using hc4
  | four₀ h1 h1' h2 h2' h3 h3' =>
      intro s i hl hi hn he
      have hdrop := drop_of_literal hl
      simp only [ByteString.data_toList_cons] at hdrop
      have hb0 : klByte s i = (s.drop i)[0]?.getD 0x00 := by
        simpa using klByte_drop_any s i 0
      rw [hdrop] at hb0
      simp only [List.getElem?_cons_zero, Option.getD_some] at hb0
      have hb1 := klByte_drop_any s i 1
      rw [hdrop] at hb1
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hb1
      have hb2 := klByte_drop_any s i 2
      rw [hdrop] at hb2
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hb2
      have hb3 := klByte_drop_any s i 3
      rw [hdrop] at hb3
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hb3
      have hcn : ¬ IsContByte (klByte s i) := by
        rw [hb0]; exact not_cont_of_ge (by decide)
      have hpos : 240 ≤ (klByte s i).toNat := by rw [hb0]; decide
      have hcont1 : IsContByte (klByte s (i + 1)) := by
        rw [hb1]
        exact ⟨UInt8.le_trans (by decide) h1, UInt8.le_trans h1' (by decide)⟩
      have hcont2 : IsContByte (klByte s (i + 2)) := by rw [hb2]; exact ⟨h2, h2'⟩
      have hcont3 : IsContByte (klByte s (i + 3)) := by rw [hb3]; exact ⟨h3, h3'⟩
      have hpair : KlPair (klByte s i) (klByte s (i + 1)) := by
        rw [hb0, hb1]
        exact (klPair_iff _ _).mpr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h1, h1'⟩))))))
      obtain ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩ :=
        char4 s i hi hn he hcn hpos hpair hcont1 hcont2 hcont3
      simp only [ByteString.length_cons]
      rw [show ∀ a : Nat, ((((a + 1) + 1) + 1) + 1) - a = 4 from fun a => by omega]
      refine ⟨?_, ?_, ?_⟩
      · intro m hm
        have hm' : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
        rcases hm' with rfl | rfl | rfl | rfl
        · simpa using hc0
        · simpa [show i - 3 + 1 = i - 2 from by omega] using hc1
        · simpa [show i - 3 + 2 = i - 1 from by omega] using hc2
        · simpa [show i - 3 + 3 = i from by omega] using hc3
      · rw [show i - 3 + 4 + 1 = i + 2 from by omega,
            show i - 3 + 4 = i + 1 from by omega]
        exact hc4
      · simpa [show i - 3 + 4 + 2 = i + 3 from by omega] using hc5
  | four₁ h0 h0' h1 h1' h2 h2' h3 h3' =>
      intro s i hl hi hn he
      have hdrop := drop_of_literal hl
      simp only [ByteString.data_toList_cons] at hdrop
      have hb0 : klByte s i = (s.drop i)[0]?.getD 0x00 := by
        simpa using klByte_drop_any s i 0
      rw [hdrop] at hb0
      simp only [List.getElem?_cons_zero, Option.getD_some] at hb0
      have hb1 := klByte_drop_any s i 1
      rw [hdrop] at hb1
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hb1
      have hb2 := klByte_drop_any s i 2
      rw [hdrop] at hb2
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hb2
      have hb3 := klByte_drop_any s i 3
      rw [hdrop] at hb3
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hb3
      have h0i : 0xF1 ≤ klByte s i := by rw [hb0]; exact h0
      have hcn : ¬ IsContByte (klByte s i) :=
        not_cont_of_ge (UInt8.le_trans (by decide) h0i)
      have hpos : 240 ≤ (klByte s i).toNat := by
        have hn : (0xF1 : UInt8).toNat ≤ (klByte s i).toNat := by
          rw [hb0]; exact (UInt8.le_iff_toNat_le).mp h0
        have hv : (0xF1 : UInt8).toNat = 241 := by decide
        omega
      have hcont1 : IsContByte (klByte s (i + 1)) := by
        rw [hb1]
        exact ⟨UInt8.le_trans (by decide) h1, UInt8.le_trans h1' (by decide)⟩
      have hcont2 : IsContByte (klByte s (i + 2)) := by rw [hb2]; exact ⟨h2, h2'⟩
      have hcont3 : IsContByte (klByte s (i + 3)) := by rw [hb3]; exact ⟨h3, h3'⟩
      have hpair : KlPair (klByte s i) (klByte s (i + 1)) := by
        rw [hb0, hb1]
        exact (klPair_iff _ _).mpr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl ⟨h0, h0', h1, h1'⟩)))))))
      obtain ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩ :=
        char4 s i hi hn he hcn hpos hpair hcont1 hcont2 hcont3
      simp only [ByteString.length_cons]
      rw [show ∀ a : Nat, ((((a + 1) + 1) + 1) + 1) - a = 4 from fun a => by omega]
      refine ⟨?_, ?_, ?_⟩
      · intro m hm
        have hm' : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
        rcases hm' with rfl | rfl | rfl | rfl
        · simpa using hc0
        · simpa [show i - 3 + 1 = i - 2 from by omega] using hc1
        · simpa [show i - 3 + 2 = i - 1 from by omega] using hc2
        · simpa [show i - 3 + 3 = i from by omega] using hc3
      · rw [show i - 3 + 4 + 1 = i + 2 from by omega,
            show i - 3 + 4 = i + 1 from by omega]
        exact hc4
      · simpa [show i - 3 + 4 + 2 = i + 3 from by omega] using hc5
  | four₂ h1 h1' h2 h2' h3 h3' =>
      intro s i hl hi hn he
      have hdrop := drop_of_literal hl
      simp only [ByteString.data_toList_cons] at hdrop
      have hb0 : klByte s i = (s.drop i)[0]?.getD 0x00 := by
        simpa using klByte_drop_any s i 0
      rw [hdrop] at hb0
      simp only [List.getElem?_cons_zero, Option.getD_some] at hb0
      have hb1 := klByte_drop_any s i 1
      rw [hdrop] at hb1
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hb1
      have hb2 := klByte_drop_any s i 2
      rw [hdrop] at hb2
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hb2
      have hb3 := klByte_drop_any s i 3
      rw [hdrop] at hb3
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hb3
      have hcn : ¬ IsContByte (klByte s i) := by
        rw [hb0]; exact not_cont_of_ge (by decide)
      have hpos : 240 ≤ (klByte s i).toNat := by rw [hb0]; decide
      have hcont1 : IsContByte (klByte s (i + 1)) := by
        rw [hb1]
        exact ⟨UInt8.le_trans (by decide) h1, UInt8.le_trans h1' (by decide)⟩
      have hcont2 : IsContByte (klByte s (i + 2)) := by rw [hb2]; exact ⟨h2, h2'⟩
      have hcont3 : IsContByte (klByte s (i + 3)) := by rw [hb3]; exact ⟨h3, h3'⟩
      have hpair : KlPair (klByte s i) (klByte s (i + 1)) := by
        rw [hb0, hb1]
        exact (klPair_iff _ _).mpr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr ⟨rfl, h1, h1'⟩)))))))
      obtain ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩ :=
        char4 s i hi hn he hcn hpos hpair hcont1 hcont2 hcont3
      simp only [ByteString.length_cons]
      rw [show ∀ a : Nat, ((((a + 1) + 1) + 1) + 1) - a = 4 from fun a => by omega]
      refine ⟨?_, ?_, ?_⟩
      · intro m hm
        have hm' : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
        rcases hm' with rfl | rfl | rfl | rfl
        · simpa using hc0
        · simpa [show i - 3 + 1 = i - 2 from by omega] using hc1
        · simpa [show i - 3 + 2 = i - 1 from by omega] using hc2
        · simpa [show i - 3 + 3 = i from by omega] using hc3
      · rw [show i - 3 + 4 + 1 = i + 2 from by omega,
            show i - 3 + 4 = i + 1 from by omega]
        exact hc4
      · simpa [show i - 3 + 4 + 2 = i + 3 from by omega] using hc5


theorem klByte_getElem {s : List UInt8} {j : Nat} (h : j < s.length) :
    klByte s j = s[j] := by
  unfold klByte
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem literal_drop_cons {s : List UInt8} {i : Nat} (hi : i < s.length) :
    ByteString.literal (s.drop i) = klByte s i +: ByteString.literal (s.drop (i + 1)) := by
  have hb : klByte s i = s[i] := klByte_getElem hi
  rw [hb, List.drop_eq_getElem_cons hi, ByteString.literal_cons]

theorem utf8Char_length_le {b : Bytes} {c : Nat} {rest : Bytes} (h : Utf8Char b c rest) :
    rest.length ≤ b.length := by
  cases h <;> (simp only [ByteString.length_eq_size, ByteString.size_cons]; omega)

theorem utf8Spans_length_le {b rest : Bytes} (h : Utf8Spans b rest) :
    rest.length ≤ b.length := by
  induction h with
  | nil t => exact Nat.le_refl _
  | char hc hr ih => exact Nat.le_trans ih (utf8Char_length_le hc)

theorem utf8Char_drop {b : Bytes} {c : Nat} {rest : Bytes} (h : Utf8Char b c rest) :
    b.data.toList.drop (b.length - rest.length) = rest.data.toList := by
  cases h with
  | one _ =>
      simp only [ByteString.length_eq_size, ByteString.size_cons]
      rw [show ByteArray.size rest + 1 - ByteArray.size rest = 1 from by omega]
      rfl
  | two _ _ _ _ =>
      simp only [ByteString.length_eq_size, ByteString.size_cons]
      rw [show ByteArray.size rest + 1 + 1 - ByteArray.size rest = 2 from by omega]
      rfl
  | three₀ _ _ _ _ =>
      simp only [ByteString.length_eq_size, ByteString.size_cons]
      rw [show ByteArray.size rest + 1 + 1 + 1 - ByteArray.size rest = 3 from by omega]
      rfl
  | three₁ _ _ _ _ _ _ =>
      simp only [ByteString.length_eq_size, ByteString.size_cons]
      rw [show ByteArray.size rest + 1 + 1 + 1 - ByteArray.size rest = 3 from by omega]
      rfl
  | three₂ _ _ _ _ =>
      simp only [ByteString.length_eq_size, ByteString.size_cons]
      rw [show ByteArray.size rest + 1 + 1 + 1 - ByteArray.size rest = 3 from by omega]
      rfl
  | three₃ _ _ _ _ _ _ =>
      simp only [ByteString.length_eq_size, ByteString.size_cons]
      rw [show ByteArray.size rest + 1 + 1 + 1 - ByteArray.size rest = 3 from by omega]
      rfl
  | four₀ _ _ _ _ _ _ =>
      simp only [ByteString.length_eq_size, ByteString.size_cons]
      rw [show ByteArray.size rest + 1 + 1 + 1 + 1 - ByteArray.size rest = 4 from by omega]
      rfl
  | four₁ _ _ _ _ _ _ _ _ =>
      simp only [ByteString.length_eq_size, ByteString.size_cons]
      rw [show ByteArray.size rest + 1 + 1 + 1 + 1 - ByteArray.size rest = 4 from by omega]
      rfl
  | four₂ _ _ _ _ _ _ =>
      simp only [ByteString.length_eq_size, ByteString.size_cons]
      rw [show ByteArray.size rest + 1 + 1 + 1 + 1 - ByteArray.size rest = 4 from by omega]
      rfl

theorem drop_three_cons (l : List UInt8) (k : Nat) :
    (0x00 :: 0x00 :: 0x00 :: l).drop (3 + k) = l.drop k := by
  rw [← List.drop_drop]
  rfl

theorem literal_drop_list (l : List UInt8) (k : Nat) :
    ByteString.literal (l.drop k) = ByteString.drop (ByteString.literal l) k := by
  apply ByteString.eq_of_toList_eq
  rw [ByteString.toList_literal, ByteString.toList_drop, ByteString.toList_literal]

theorem klByte_append_left {s t : List UInt8} {j : Nat} (hj : j < s.length) :
    klByte (s ++ t) j = klByte s j := by
  unfold klByte
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem klErrWin_append_left {s t : List UInt8} {j : Nat} (hj : j + 3 < s.length) :
    klErrWin (s ++ t) j = klErrWin s j := by
  unfold klErrWin
  rw [klByte_append_left (s := s) (t := t) (by omega),
    klByte_append_left (s := s) (t := t) (by omega),
    klByte_append_left (s := s) (t := t) (by omega),
    klByte_append_left (s := s) (t := t) (by omega)]

theorem spans_ok {b rest : Bytes} (h : Utf8Spans b rest) :
    ∀ (s : List UInt8) (i : Nat), ByteString.literal (s.drop i) = b → 3 ≤ i →
    ¬ NeedsCont (klByte s (i - 2)) (klByte s (i - 3)) →
    IsCharEnd (klByte s (i - 1)) →
    (∀ m, m < b.length - rest.length → klErrWin s (i - 3 + m)) ∧
    ¬ NeedsCont (klByte s (i - 3 + (b.length - rest.length) + 1))
        (klByte s (i - 3 + (b.length - rest.length))) ∧
    IsCharEnd (klByte s (i - 3 + (b.length - rest.length) + 2)) := by
  induction h with
  | nil t =>
      intro s i _ hi hn he
      refine ⟨?_, ?_, ?_⟩
      · intro m hm
        omega
      · have h1 : i - 3 + (t.length - t.length) + 1 = i - 2 := by omega
        have h2 : i - 3 + (t.length - t.length) = i - 3 := by omega
        rw [h1, h2]
        exact hn
      · have h1 : i - 3 + (t.length - t.length) + 2 = i - 1 := by omega
        rw [h1]
        exact he
  | char hc hr ih =>
      rename_i bb bp rr cc
      intro s i hl hi hn he
      obtain ⟨hw1, hc1, he1⟩ := char_ok hc s i hl hi hn he
      have hcle := utf8Char_length_le hc
      have hltl := utf8Spans_length_le hr
      have hsub : (bb.length - bp.length) + (bp.length - rr.length)
          = bb.length - rr.length := by omega
      have hi' : 3 ≤ i + (bb.length - bp.length) := by omega
      have hl' : ByteString.literal (s.drop (i + (bb.length - bp.length))) = bp := by
        rw [← List.drop_drop, drop_of_literal hl, utf8Char_drop hc,
          ByteString.literal_data_toList]
      have hnc : ¬ NeedsCont (klByte s (i + (bb.length - bp.length) - 2))
          (klByte s (i + (bb.length - bp.length) - 3)) := by
        have h := hc1
        rwa [show i - 3 + (bb.length - bp.length) + 1
              = i + (bb.length - bp.length) - 2 from by omega,
            show i - 3 + (bb.length - bp.length)
              = i + (bb.length - bp.length) - 3 from by omega] at h
      have hec : IsCharEnd (klByte s (i + (bb.length - bp.length) - 1)) := by
        have h := he1
        rwa [show i - 3 + (bb.length - bp.length) + 2
              = i + (bb.length - bp.length) - 1 from by omega] at h
      obtain ⟨hw2, hc2, he2⟩ := ih s (i + (bb.length - bp.length)) hl' hi' hnc hec
      refine ⟨?_, ?_, ?_⟩
      · intro m hm
        by_cases hmk : m < bb.length - bp.length
        · exact hw1 m hmk
        · have hm' : m - (bb.length - bp.length) < bp.length - rr.length := by omega
          have h := hw2 (m - (bb.length - bp.length)) hm'
          rwa [show i + (bb.length - bp.length) - 3 + (m - (bb.length - bp.length))
                = i - 3 + m from by omega] at h
      · have h := hc2
        rwa [show i + (bb.length - bp.length) - 3 + (bp.length - rr.length) + 1
              = i - 3 + (bb.length - rr.length) + 1 from by omega,
            show i + (bb.length - bp.length) - 3 + (bp.length - rr.length)
              = i - 3 + (bb.length - rr.length) from by omega] at h
      · have h := he2
        rwa [show i + (bb.length - bp.length) - 3 + (bp.length - rr.length) + 2
              = i - 3 + (bb.length - rr.length) + 2 from by omega] at h

theorem char_prefix_ok {b : Bytes} {c : Nat} {rest : Bytes} (h : Utf8Char b c rest)
    (k : Nat) (hk1 : 1 ≤ k) (hkl : k < b.length - rest.length) :
    ∀ (s : List UInt8) (i : Nat), ByteString.literal (s.drop i) = (b.take k) → 3 ≤ i →
    ¬ NeedsCont (klByte s (i - 2)) (klByte s (i - 3)) →
    IsCharEnd (klByte s (i - 1)) →
    ∀ m, m < k → klErrWin s (i - 3 + m) := by
  intro s i hl hi hn he m hm
  have hk_le : k ≤ b.length := by
    have := utf8Char_length_le h
    omega
  have hdrop : (s.drop i).length = k := by
    have hh := congrArg (fun x : Bytes => x.length) hl
    rw [ByteString.length_take] at hh
    rw [ByteString.length_eq_size, ByteString.size_literal] at hh
    rw [hh, Nat.min_eq_left hk_le]
  have hsi : s.length = i + k := by
    have h1 : (s.drop i).length = s.length - i := List.length_drop
    omega
  have hsplit : (b.take k).data.toList ++ (b.drop k).data.toList = b.data.toList := by
    have hh := congrArg (fun x : Bytes => x.toList) (ByteString.take_append_drop b k)
    rw [ByteString.toList_append, ByteString.toList_eq_data_toList,
      ByteString.toList_eq_data_toList, ByteString.toList_eq_data_toList] at hh
    exact hh
  have hd : s.drop i = (b.take k).data.toList := drop_of_literal hl
  have hs' : ByteString.literal ((s ++ (b.drop k).data.toList).drop i) = b := by
    have hdropi : (s ++ (b.drop k).data.toList).drop i
        = s.drop i ++ (b.drop k).data.toList := by
      rw [List.drop_append, Nat.sub_eq_zero_of_le (by omega), List.drop_zero]
    rw [hdropi, hd, hsplit, ByteString.literal_data_toList]
  have hn' : ¬ NeedsCont (klByte (s ++ (b.drop k).data.toList) (i - 2))
      (klByte (s ++ (b.drop k).data.toList) (i - 3)) := by
    rw [klByte_append_left (s := s) (t := (b.drop k).data.toList) (by omega),
      klByte_append_left (s := s) (t := (b.drop k).data.toList) (by omega)]
    exact hn
  have he' : IsCharEnd (klByte (s ++ (b.drop k).data.toList) (i - 1)) := by
    rw [klByte_append_left (s := s) (t := (b.drop k).data.toList) (by omega)]
    exact he
  obtain ⟨hw, -, -⟩ := char_ok h (s ++ (b.drop k).data.toList) i hs' hi hn' he'
  have hm' : m < b.length - rest.length := by omega
  have hwin := hw m hm'
  rwa [klErrWin_append_left (s := s) (t := (b.drop k).data.toList)
        (j := i - 3 + m) (by omega)] at hwin

theorem u8_le_of_toNat {a b : UInt8} (h : a.toNat ≤ b.toNat) : a ≤ b :=
  (UInt8.le_iff_toNat_le).mpr h

theorem u8_lt_of_toNat {a b : UInt8} (h : a.toNat < b.toNat) : a < b :=
  (UInt8.lt_iff_toNat_lt).mpr h

theorem klErrWin_at_succ {s : List UInt8} {i : Nat} (hi : 3 ≤ i) (h : klErrWin s (i + 1 - 3)) :
    klErrByte (klByte s (i - 2)) (klByte s (i - 1)) (klByte s i) (klByte s (i + 1)) = 0 := by
  unfold klErrWin at h
  simpa [show i + 1 - 3 = i - 2 from by omega, show i - 2 + 1 = i - 1 from by omega,
    show i - 2 + 2 = i from by omega, show i - 2 + 3 = i + 1 from by omega] using h

theorem klErrWin_at_succ2 {s : List UInt8} {i : Nat} (hi : 3 ≤ i) (h : klErrWin s (i + 2 - 3)) :
    klErrByte (klByte s (i - 1)) (klByte s i) (klByte s (i + 1)) (klByte s (i + 2)) = 0 := by
  unfold klErrWin at h
  simpa [show i + 2 - 3 = i - 1 from by omega, show i - 1 + 1 = i from by omega,
    show i - 1 + 2 = i + 1 from by omega, show i - 1 + 3 = i + 2 from by omega] using h

theorem klErrWin_at_succ3 {s : List UInt8} {i : Nat} (hi : 3 ≤ i) (h : klErrWin s (i + 3 - 3)) :
    klErrByte (klByte s i) (klByte s (i + 1)) (klByte s (i + 2)) (klByte s (i + 3)) = 0 := by
  unfold klErrWin at h
  simpa [show i + 3 - 3 = i from by omega, show i + 1 = i + 1 from by omega,
    show i + 2 = i + 2 from by omega, show i + 3 = i + 3 from by omega] using h

theorem not_charEnd_of_ge {p : UInt8} (h : 0xC2 ≤ p) : ¬ IsCharEnd p := by
  intro hp
  have hlt := isCharEnd_lt p hp
  rw [UInt8.le_iff_toNat_le] at h
  have hc2 : (0xC2 : UInt8).toNat = 194 := rfl
  omega

theorem not_cont_of_pair {p1 c : UInt8} (hp : IsCharEnd p1) (hk : KlPair p1 c) :
    ¬ IsContByte c := by
  rw [klPair_iff] at hk
  rcases hk with ⟨h1, -⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact h1
  · exfalso; exact not_charEnd_of_ge (UInt8.le_trans (by decide) h1) hp
  · exfalso; exact not_charEnd_of_ge (h1 ▸ (by decide)) hp
  · exfalso
    rcases h1 with ⟨a, -⟩ | ⟨a, -⟩
    · exact not_charEnd_of_ge (UInt8.le_trans (by decide) a) hp
    · exact not_charEnd_of_ge (UInt8.le_trans (by decide) a) hp
  · exfalso; exact not_charEnd_of_ge (h1 ▸ (by decide)) hp
  · exfalso; exact not_charEnd_of_ge (h1 ▸ (by decide)) hp
  · exfalso; exact not_charEnd_of_ge (UInt8.le_trans (by decide) h1) hp
  · exfalso; exact not_charEnd_of_ge (h1 ▸ (by decide)) hp

theorem not_klPair_of_dead {c d : UInt8} (hc : ¬ IsCharEnd c)
    (hl : ¬ IsUtf8LeadByte c) : ¬ KlPair c d := by
  intro hk
  rw [klPair_iff] at hk
  rcases hk with ⟨-, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact hc h2
  · exact hl (Or.inr ⟨h1, UInt8.le_trans h2 (by decide)⟩)
  · exact hl (Or.inr (h1.symm ▸ (by decide)))
  · rcases h1 with ⟨a, b⟩ | ⟨a, b⟩
    · exact hl (Or.inr ⟨UInt8.le_trans (by decide) a, UInt8.le_trans b (by decide)⟩)
    · exact hl (Or.inr ⟨UInt8.le_trans (by decide) a, UInt8.le_trans b (by decide)⟩)
  · exact hl (Or.inr (h1.symm ▸ (by decide)))
  · exact hl (Or.inr (h1.symm ▸ (by decide)))
  · exact hl (Or.inr ⟨UInt8.le_trans (by decide) h1, UInt8.le_trans h2 (by decide)⟩)
  · exact hl (Or.inr (h1.symm ▸ (by decide)))

theorem not_needsCont_of_charEnd {p1 p2 p3 : UInt8} (hp : IsCharEnd p1)
    (hn : ¬ NeedsCont p2 p3) : ¬ NeedsCont p1 p2 := by
  refine not_needsCont_of_lt ?_ ?_
  · have := isCharEnd_lt p1 hp; omega
  · have := (needsCont_false_iff p2 p3).mp hn; omega

theorem pair_two_cont {p1 d : UInt8} (h0 : 0xC2 ≤ p1) (h0' : p1 ≤ 0xDF)
    (hk : KlPair p1 d) : IsContByte d := by
  rw [klPair_iff] at hk
  rcases hk with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exfalso; exact not_charEnd_of_ge h0 h2
  · exact h3
  · subst h1; exfalso
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0' ⊢; omega
  · rcases h1 with ⟨a, b⟩ | ⟨a, b⟩
    · exfalso; simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at a h0' ⊢; omega
    · exfalso; simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at a h0' ⊢; omega
  · subst h1; exfalso
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0' ⊢; omega
  · subst h1; exfalso
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0' ⊢; omega
  · exfalso
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h1 h0' ⊢; omega
  · subst h1; exfalso
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0' ⊢; omega

theorem pair_three0_cont {d : UInt8} (hk : KlPair 0xE0 d) :
    0xA0 ≤ d ∧ d ≤ 0xBF := by
  rw [klPair_iff] at hk
  rcases hk with ⟨-, h2⟩ | ⟨h1, h2, h3⟩ | ⟨-, h2, h3⟩ | ⟨h1, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact absurd h2 (not_charEnd_of_ge (by decide))
  · exact absurd h2 (by decide)
  · exact ⟨h2, h3⟩
  · rcases h1 with ⟨a, -⟩ | ⟨a, -⟩ <;> exact absurd a (by decide)
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)

theorem pair_three1_cont {p1 d : UInt8} (h0 : 0xE1 ≤ p1) (h0' : p1 ≤ 0xEC)
    (hk : KlPair p1 d) : IsContByte d := by
  rw [klPair_iff] at hk
  rcases hk with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exfalso; exact not_charEnd_of_ge (UInt8.le_trans (by decide) h0) h2
  · exfalso
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0 h2 ⊢; omega
  · subst h1; exfalso
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0 ⊢; omega
  · rcases h1 with ⟨a, b⟩ | ⟨a, b⟩
    · exact h3
    · exfalso
      simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at a h0' ⊢; omega
  · subst h1; exfalso
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0' ⊢; omega
  · subst h1; exfalso
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0' ⊢; omega
  · exfalso
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h1 h0' ⊢; omega
  · subst h1; exfalso
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0' ⊢; omega

theorem pair_three2_cont {d : UInt8} (hk : KlPair 0xED d) :
    0x80 ≤ d ∧ d ≤ 0x9F := by
  rw [klPair_iff] at hk
  rcases hk with ⟨-, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h3⟩ | ⟨-, h2, h3⟩ |
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact absurd h2 (not_charEnd_of_ge (by decide))
  · exact absurd h2 (by decide)
  · exact absurd h1 (by decide)
  · rcases h1 with ⟨a, b⟩ | ⟨a, b⟩
    · exact absurd b (by decide)
    · exact absurd a (by decide)
  · exact ⟨h2, h3⟩
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)

theorem pair_three3_cont {p1 d : UInt8} (h0 : 0xEE ≤ p1) (h0' : p1 ≤ 0xEF)
    (hk : KlPair p1 d) : IsContByte d := by
  rw [klPair_iff] at hk
  rcases hk with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exfalso; exact not_charEnd_of_ge (UInt8.le_trans (by decide) h0) h2
  · exfalso
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0 h2 ⊢; omega
  · subst h1; exfalso
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0 ⊢; omega
  · rcases h1 with ⟨a, b⟩ | ⟨a, b⟩
    · exfalso
      simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0 b ⊢; omega
    · exact h3
  · subst h1; exfalso
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0 ⊢; omega
  · subst h1; exfalso
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0' ⊢; omega
  · exfalso
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h1 h0' ⊢; omega
  · subst h1; exfalso
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0' ⊢; omega

theorem pair_four0_cont {d : UInt8} (hk : KlPair 0xF0 d) :
    0x90 ≤ d ∧ d ≤ 0xBF := by
  rw [klPair_iff] at hk
  rcases hk with ⟨-, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨-, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact absurd h2 (not_charEnd_of_ge (by decide))
  · exact absurd h2 (by decide)
  · exact absurd h1 (by decide)
  · rcases h1 with ⟨a, b⟩ | ⟨a, b⟩
    · exact absurd b (by decide)
    · exact absurd b (by decide)
  · exact absurd h1 (by decide)
  · exact ⟨h2, h3⟩
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)

theorem pair_four1_cont {p1 d : UInt8} (h0 : 0xF1 ≤ p1) (h0' : p1 ≤ 0xF3)
    (hk : KlPair p1 d) : IsContByte d := by
  rw [klPair_iff] at hk
  rcases hk with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exfalso; exact not_charEnd_of_ge (UInt8.le_trans (by decide) h0) h2
  · exfalso
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0 h2 ⊢; omega
  · subst h1; exfalso
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0 ⊢; omega
  · rcases h1 with ⟨a, b⟩ | ⟨a, b⟩
    · exfalso
      simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0 b ⊢; omega
    · exfalso
      simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0 b ⊢; omega
  · subst h1; exfalso
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0 ⊢; omega
  · subst h1; exfalso
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0 ⊢; omega
  · exact h3
  · subst h1; exfalso
    simp only [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at h0' ⊢; omega

theorem pair_four2_cont {d : UInt8} (hk : KlPair 0xF4 d) :
    0x80 ≤ d ∧ d ≤ 0x8F := by
  rw [klPair_iff] at hk
  rcases hk with ⟨-, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h3⟩ | ⟨h1, h2, h3⟩ |
    ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨-, h2, h3⟩
  · exact absurd h2 (not_charEnd_of_ge (by decide))
  · exact absurd h2 (by decide)
  · exact absurd h1 (by decide)
  · rcases h1 with ⟨a, b⟩ | ⟨a, b⟩
    · exact absurd b (by decide)
    · exact absurd b (by decide)
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)
  · exact absurd h2 (by decide)
  · exact ⟨h2, h3⟩

theorem klTailByte_true_ge {c : UInt8} (h : klTailByte c = true) : 192 ≤ c.toNat := by
  unfold klTailByte at h
  rw [Bool.or_eq_true] at h
  rcases h with h1 | h2
  · rw [decide_eq_true_eq] at h1
    have he : (c &&& 0xFE).toNat = 192 := by rw [h1]; rfl
    have hle : (c &&& 0xFE).toNat ≤ c.toNat := by
      rw [UInt8.toNat_and]
      exact Nat.and_le_left
    omega
  · rw [decide_eq_true_eq] at h2
    have hge := (UInt8.le_iff_toNat_le).mp h2
    have hf5 : (0xF5 : UInt8).toNat = 245 := rfl
    omega

theorem klTailByte_false_of_lead {c : UInt8} (h1 : 0xC2 ≤ c) (h2 : c ≤ 0xF4) :
    klTailByte c = false := by
  have h1' : 194 ≤ c.toNat := (UInt8.le_iff_toNat_le).mp h1
  have h2' : c.toNat ≤ 244 := (UInt8.le_iff_toNat_le).mp h2
  have hc : c = UInt8.ofNat (194 + (c.toNat - 194)) := by
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    omega
  rw [hc]
  exact (by decide : ∀ i : Fin 51, klTailByte (UInt8.ofNat (194 + i.val)) = false)
    ⟨c.toNat - 194, by omega⟩

theorem klTailByte_false_of_cont {c : UInt8} (h1 : 0x80 ≤ c) (h2 : c ≤ 0xBF) :
    klTailByte c = false := by
  have h1' : 128 ≤ c.toNat := (UInt8.le_iff_toNat_le).mp h1
  have h2' : c.toNat ≤ 191 := (UInt8.le_iff_toNat_le).mp h2
  have hc : c = UInt8.ofNat (128 + (c.toNat - 128)) := by
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    omega
  rw [hc]
  exact (by decide : ∀ i : Fin 64, klTailByte (UInt8.ofNat (128 + i.val)) = false)
    ⟨c.toNat - 128, by omega⟩

theorem klTailByte_false_of_charEnd {c : UInt8} (h : IsCharEnd c) : klTailByte c = false := by
  rcases h with h | h
  · cases hb : klTailByte c with
    | false => rfl
    | true =>
        have hge := klTailByte_true_ge hb
        exact absurd hge (by omega)
  · exact klTailByte_false_of_cont h.1 h.2

theorem utf8PrefixOf_of_literal_take {l : List UInt8} {b : Bytes} {c : Nat} {r : Bytes}
    (hc : Utf8Char b c r) (hne : l ≠ [])
    (hlt : l.length < b.length - r.length)
    (ht : b.take l.length = ByteString.literal l) :
    Utf8PrefixOf (ByteString.literal l) := by
  refine ⟨?_, b, c, r, hc, ?_, ?_⟩
  · cases l with
    | nil => exact absurd rfl hne
    | cons _ _ => rw [ByteString.literal_cons]; exact ByteString.cons_ne_empty _ _
  · rw [ByteString.length_eq_size, ByteString.size_literal]; exact hlt
  · unfold HasPrefix
    rw [ByteString.drop_zero, ByteString.length_eq_size, ByteString.size_literal]
    exact ht

theorem utf8Spans_tail_drop {b : Bytes} {t : Bytes} (h : Utf8Spans b t) :
    ∃ k, t = ByteString.literal (b.data.toList.drop k) := by
  induction h with
  | nil t => exact ⟨0, by rw [List.drop_zero, ByteString.literal_data_toList]⟩
  | char hc hr ih =>
      rename_i bb bp rr cc
      obtain ⟨k, hk⟩ := ih
      refine ⟨(bb.length - bp.length) + k, ?_⟩
      rw [hk]
      have hd := utf8Char_drop hc
      rw [← hd, List.drop_drop]

theorem utf8Spans_literal_tail {l : List UInt8} {t : Bytes}
    (h : Utf8Spans (ByteString.literal l) t) :
    ∃ k, t = ByteString.literal (l.drop k) := by
  obtain ⟨k, hk⟩ := utf8Spans_tail_drop h
  exact ⟨k, by rwa [ByteString.data_toList_literal] at hk⟩

theorem help_drop1 {s : List UInt8} {i : Nat} (hi : i < s.length) (h : i + 1 = s.length) :
    s.drop i = [klByte s i] := by
  rw [List.drop_eq_getElem_cons hi]
  have hnil : s.drop (i + 1) = [] := List.drop_eq_nil_of_le (by omega)
  rw [hnil, klByte_getElem hi]

theorem help_drop2 {s : List UInt8} {i : Nat} (hi : i < s.length) (hi1 : i + 1 < s.length)
    (h : i + 2 = s.length) : s.drop i = [klByte s i, klByte s (i + 1)] := by
  rw [List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hi1]
  have hnil : s.drop (i + 2) = [] := List.drop_eq_nil_of_le (by omega)
  rw [hnil, klByte_getElem hi, klByte_getElem hi1]

theorem help_drop3 {s : List UInt8} {i : Nat} (hi : i < s.length) (hi1 : i + 1 < s.length)
    (hi2 : i + 2 < s.length) (h : i + 3 = s.length) :
    s.drop i = [klByte s i, klByte s (i + 1), klByte s (i + 2)] := by
  rw [List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hi1,
    List.drop_eq_getElem_cons hi2]
  have hnil : s.drop (i + 3) = [] := List.drop_eq_nil_of_le (by omega)
  rw [hnil, klByte_getElem hi, klByte_getElem hi1, klByte_getElem hi2]

theorem literal_take_append (l d : List UInt8) :
    (ByteString.literal (l ++ d)).take l.length = ByteString.literal l := by
  apply ByteString.eq_of_toList_eq
  simp [ByteString.toList_take]

theorem literal_length_lt_append {l d : List UInt8} (hd : d ≠ []) :
    l.length < (ByteString.literal (l ++ d)).length - (ByteString.literal []).length := by
  have h0 : (ByteString.literal [] : Bytes).length = 0 := rfl
  rw [h0, ByteString.length_eq_size, ByteString.size_literal]
  simp only [List.length_append, Nat.sub_zero]
  have hdlen : 0 < d.length := by
    cases d with
    | nil => exact absurd rfl hd
    | cons _ _ => simp
  omega

theorem klTailByte_true_of_C0_C1 {c : UInt8} (h1 : 0xC0 ≤ c) (h2 : c ≤ 0xC1) :
    klTailByte c = true := by
  have h1' : 192 ≤ c.toNat := (UInt8.le_iff_toNat_le).mp h1
  have h2' : c.toNat ≤ 193 := (UInt8.le_iff_toNat_le).mp h2
  have hc : c = UInt8.ofNat (0xC0 + (c.toNat - 0xC0)) := by
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    omega
  rw [hc]
  exact (by decide : ∀ i : Fin 2, klTailByte (UInt8.ofNat (0xC0 + i.val)) = true)
    ⟨c.toNat - 0xC0, by omega⟩

theorem klTailByte_true_of_F5 {c : UInt8} (h1 : 0xF5 ≤ c) (h2 : c.toNat ≤ 255) :
    klTailByte c = true := by
  have h1' : 245 ≤ c.toNat := (UInt8.le_iff_toNat_le).mp h1
  have hc : c = UInt8.ofNat (0xF5 + (c.toNat - 0xF5)) := by
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    omega
  rw [hc]
  exact (by decide : ∀ i : Fin 11, klTailByte (UInt8.ofNat (0xF5 + i.val)) = true)
    ⟨c.toNat - 0xF5, by omega⟩

theorem validPrefix_of_klErrAll {s : List UInt8} {i : Nat} (hi : 3 ≤ i)
    (hstate : ¬ NeedsCont (klByte s (i - 2)) (klByte s (i - 3)) ∧
      IsCharEnd (klByte s (i - 1)))
    (hwin : ∀ q, i ≤ q → q < s.length → klErrWin s (q - 3))
    (hlast : ¬ klTailByte (klByte s (s.length - 1)) = true) :
    ValidPrefix (ByteString.literal (s.drop i)) := by
  suffices h : ∀ k, ∀ (s : List UInt8) (i : Nat), s.length - i = k → 3 ≤ i →
      (¬ NeedsCont (klByte s (i - 2)) (klByte s (i - 3)) ∧
        IsCharEnd (klByte s (i - 1))) →
      (∀ q, i ≤ q → q < s.length → klErrWin s (q - 3)) →
      (¬ klTailByte (klByte s (s.length - 1)) = true) →
      ValidPrefix (ByteString.literal (s.drop i)) from
    h (s.length - i) s i rfl hi hstate hwin hlast
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro s i hk hi hstate hwin hlast
    by_cases hlen : i < s.length
    · let c := klByte s i
      have hc : c = klByte s i := rfl
      have hwin_i : klErrWin s (i - 3) := hwin i (Nat.le_refl i) hlen
      have hwin_i' : klErrByte (klByte s (i - 3)) (klByte s (i - 2)) (klByte s (i - 1))
          (klByte s i) = 0 := by
        have hh := hwin_i
        unfold klErrWin at hh
        simpa [show i - 3 + 1 = i - 2 from by omega, show i - 3 + 2 = i - 1 from by omega,
          show i - 3 + 3 = i from by omega] using hh
      have hpair : KlPair (klByte s (i - 1)) c := by
        rcases (klErrByte_eq_zero_iff _ _ _ _).mp hwin_i' with ⟨hn, -⟩ | ⟨-, hp⟩
        · exact absurd hn hstate.1
        · rw [← hc] at hp
          exact hp
      have hnc : ¬ IsContByte c := not_cont_of_pair hstate.2 hpair
      have hne_l : s.drop i ≠ [] := by
        intro h0
        have hpos : 0 < (s.drop i).length := by rw [List.length_drop]; omega
        rw [h0] at hpos; simp at hpos
      have step : ∀ (l : Nat) (c' : Nat) (b' : Bytes),
          Utf8Char (ByteString.literal (s.drop i)) c' b' →
          b' = ByteString.literal (s.drop (i + l)) → 1 ≤ l →
          (¬ NeedsCont (klByte s (i + l - 2)) (klByte s (i + l - 3)) ∧
            IsCharEnd (klByte s (i + l - 1))) →
          ValidPrefix (ByteString.literal (s.drop i)) := by
        intro l c' b' hch hb' hl hstate'
        have hi' : 3 ≤ i + l := by omega
        obtain ⟨t, hspans, htail⟩ :=
          ih (s.length - (i + l)) (by omega) s (i + l) rfl hi' hstate'
            (fun q hq hqs => hwin q (by omega) hqs) hlast
        rw [← hb'] at hspans
        exact ⟨t, Utf8Spans.char hch hspans, htail⟩
      have lift : ∀ (l : Nat) (L : List UInt8) (d : List UInt8) (c' : Nat),
          s.drop i = L → d ≠ [] →
          Utf8Char (ByteString.literal (L ++ d)) c' (ByteString.literal []) →
          ValidPrefix (ByteString.literal (s.drop i)) := by
        intro l L d c' hd hdn hchar
        rw [hd]
        exact ⟨ByteString.literal L, Utf8Spans.nil _,
          Or.inr (utf8PrefixOf_of_literal_take (l := L) hchar
            (by cases L with | nil => exact absurd hd.symm (by simpa using hne_l) | cons _ _ => simp)
            (literal_length_lt_append hdn) (literal_take_append L d))⟩
      by_cases hascii : c.toNat < 0x80
      · have hlt80 : c < 0x80 := by rw [UInt8.lt_iff_toNat_lt]; exact hascii
        have hch : Utf8Char (ByteString.literal (s.drop i)) c.toNat
            (ByteString.literal (s.drop (i + 1))) := by
          rw [literal_drop_cons hlen]
          exact Utf8Char.one hlt80
        refine step 1 c.toNat _ hch rfl (by omega) ⟨?_, ?_⟩
        · have h := not_needsCont_of_charEnd hstate.2 hstate.1
          simpa [show i + 1 - 2 = i - 1 from by omega, show i + 1 - 3 = i - 2 from by omega] using h
        · rw [show i + 1 - 1 = i from by omega]
          exact Or.inl hascii
      · have hge : 0x80 ≤ c.toNat := by omega
        by_cases hcont : c.toNat ≤ 0xBF
        · exact absurd (cont_of_bounds hge hcont) hnc
        · have hgeC0 : 0xC0 ≤ c.toNat := by omega
          by_cases hc01 : c.toNat < 0xC2
          · have h1 : 0xC0 ≤ c := u8_le_of_toNat hgeC0
            have h2 : c ≤ 0xC1 :=
              u8_le_of_toNat (by simp only [UInt8.toNat_ofNat] at hc01 ⊢; omega)
            have hctrue : klTailByte c = true := klTailByte_true_of_C0_C1 h1 h2
            by_cases hnext : i + 1 < s.length
            · exfalso
              have hneed1 : ¬ NeedsCont (klByte s (i - 1)) (klByte s (i - 2)) :=
                not_needsCont_of_charEnd hstate.2 hstate.1
              have hpair1 : KlPair c (klByte s (i + 1)) := by
                have hw := klErrWin_at_succ (s := s) (hi := hi) (hwin (i + 1) (by omega) hnext)
                rcases (klErrByte_eq_zero_iff _ _ _ _).mp hw with ⟨hn, -⟩ | ⟨-, hp⟩
                · exact absurd hn hneed1
                · rw [← hc] at hp
                  exact hp
              have hnc' : ¬ IsCharEnd c := by
                rw [isCharEnd_nat]; omega
              have hnl : ¬ IsUtf8LeadByte c := by
                intro hl
                unfold IsUtf8LeadByte at hl
                simp only [UInt8.lt_iff_toNat_lt, UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at hl
                omega
              exact not_klPair_of_dead hnc' hnl hpair1
            · exfalso
              have hi_eq : i = s.length - 1 := by omega
              rw [hc] at hctrue
              exact hlast (by rw [← hi_eq]; exact hctrue)
          · have h0 : 0xC2 ≤ c := by
              rw [UInt8.le_iff_toNat_le]
              simp only [UInt8.toNat_ofNat] at hc01 ⊢
              omega
            by_cases hdf : c.toNat ≤ 0xDF
            · have h0' : c ≤ 0xDF := by rw [UInt8.le_iff_toNat_le]; exact hdf
              by_cases hnext : i + 1 < s.length
              · have hneed1 : ¬ NeedsCont (klByte s (i - 1)) (klByte s (i - 2)) :=
                  not_needsCont_of_charEnd hstate.2 hstate.1
                have hpair1 : KlPair c (klByte s (i + 1)) := by
                  have hw := klErrWin_at_succ (s := s) (hi := hi) (hwin (i + 1) (by omega) hnext)
                  rcases (klErrByte_eq_zero_iff _ _ _ _).mp hw with ⟨hn, -⟩ | ⟨-, hp⟩
                  · exact absurd hn hneed1
                  · exact hp
                have hcont1 : IsContByte (klByte s (i + 1)) := pair_two_cont h0 h0' hpair1
                have hch : Utf8Char (ByteString.literal (s.drop i))
                    (((klByte s i).toNat - 0xC0) * 0x40 + ((klByte s (i + 1)).toNat - 0x80))
                    (ByteString.literal (s.drop (i + 2))) := by
                  rw [literal_drop_cons hlen, literal_drop_cons hnext]
                  exact Utf8Char.two h0 h0' hcont1.1 hcont1.2
                refine step 2 _ _ hch rfl (by omega) ⟨?_, ?_⟩
                · refine not_needsCont_of_lt ?_ ?_
                  · rw [show i + 2 - 2 = i from by omega, ← hc]
                    omega
                  · rw [show i + 2 - 3 = i - 1 from by omega]
                    have hlt := isCharEnd_lt _ hstate.2
                    omega
                · rw [show i + 2 - 1 = i + 1 from by omega]; exact Or.inr hcont1
              · have hcord : i + 1 = s.length := by omega
                have hd : s.drop i = [c] := by rw [help_drop1 hlen hcord, hc]
                have hchar := Utf8Char.two (b0 := c) (b1 := 0x80) (rest := ByteString.literal [])
                  h0 h0' (by decide) (by decide)
                exact lift 1 [c] [0x80] _ hd (by simp) hchar
            · have hE0 : 0xE0 ≤ c.toNat := by omega
              by_cases hef : c.toNat ≤ 0xEF
              · have h0E : 0xE0 ≤ c := by rw [UInt8.le_iff_toNat_le]; exact hE0
                by_cases he0 : c.toNat = 0xE0
                · have hcE0 : c = 0xE0 := UInt8.toNat_inj.mp (by simpa using he0)
                  by_cases hnext : i + 1 < s.length
                  · have hneed1 : ¬ NeedsCont (klByte s (i - 1)) (klByte s (i - 2)) :=
                      not_needsCont_of_charEnd hstate.2 hstate.1
                    have hpair1 : KlPair c (klByte s (i + 1)) := by
                      have hw := klErrWin_at_succ (s := s) (hi := hi) (hwin (i + 1) (by omega) hnext)
                      rcases (klErrByte_eq_zero_iff _ _ _ _).mp hw with ⟨hn, -⟩ | ⟨-, hp⟩
                      · exact absurd hn hneed1
                      · exact hp
                    have hp1 : 0xA0 ≤ klByte s (i + 1) ∧ klByte s (i + 1) ≤ 0xBF := by
                      rw [hcE0] at hpair1
                      exact pair_three0_cont hpair1
                    by_cases hnext2 : i + 2 < s.length
                    · have hcont2 : IsContByte (klByte s (i + 1)) ∧ IsContByte (klByte s (i + 2)) := by
                        have hw := klErrWin_at_succ2 (s := s) (hi := hi) (hwin (i + 2) (by omega) hnext2)
                        rcases (klErrByte_eq_zero_iff _ _ _ _).mp hw with ⟨hne, h1, h2⟩ | ⟨hnn, hp⟩
                        · exact ⟨h1, h2⟩
                        · exact absurd (needsCont_of_lead hE0) hnn
                      have hch : Utf8Char (ByteString.literal (s.drop i))
                          (((klByte s (i + 1)).toNat - 0x80) * 0x40 + ((klByte s (i + 2)).toNat - 0x80))
                          (ByteString.literal (s.drop (i + 3))) := by
                        rw [literal_drop_cons hlen, literal_drop_cons hnext, literal_drop_cons hnext2]
                        rw [show klByte s i = 0xE0 from hcE0]
                        exact Utf8Char.three₀ hp1.1 hp1.2 hcont2.2.1 hcont2.2.2
                      refine step 3 _ _ hch rfl (by omega) ⟨?_, ?_⟩
                      · refine not_needsCont_of_lt ?_ ?_
                        · rw [show i + 3 - 2 = i + 1 from by omega]; have h := cont_le hcont2.1; omega
                        · rw [show i + 3 - 3 = i from by omega]; rw [← hc]; omega
                      · rw [show i + 3 - 1 = i + 2 from by omega]; exact Or.inr hcont2.2
                    · have hcord : i + 2 = s.length := by omega
                      have hd : s.drop i = [c, klByte s (i + 1)] := by
                        rw [help_drop2 hlen hnext hcord, hc]
                      have hchar : Utf8Char (ByteString.literal (c :: klByte s (i + 1) :: 0x80 :: []))
                          (((klByte s (i + 1)).toNat - 0x80) * 0x40 + ((0x80 : UInt8).toNat - 0x80))
                          (ByteString.literal []) := by
                        rw [ByteString.literal_cons, ByteString.literal_cons, ByteString.literal_cons]
                        rw [show c = 0xE0 from hcE0]
                        exact Utf8Char.three₀ hp1.1 hp1.2 (by decide) (by decide)
                      exact lift 2 [c, klByte s (i + 1)] [0x80] _ hd (by simp) hchar
                  · have hcord : i + 1 = s.length := by omega
                    have hd : s.drop i = [c] := by rw [help_drop1 hlen hcord, hc]
                    have hchar : Utf8Char (ByteString.literal (c :: 0xA0 :: 0x80 :: []))
                        (((0xA0 : UInt8).toNat - 0x80) * 0x40 + ((0x80 : UInt8).toNat - 0x80))
                        (ByteString.literal []) := by
                      rw [ByteString.literal_cons, ByteString.literal_cons, ByteString.literal_cons]
                      rw [show c = 0xE0 from hcE0]
                      exact Utf8Char.three₀ (by decide) (by decide) (by decide) (by decide)
                    exact lift 1 [c] [0xA0, 0x80] _ hd (by simp) hchar
                · by_cases hed : c.toNat = 0xED
                  · have hcED : c = 0xED := UInt8.toNat_inj.mp (by simpa using hed)
                    by_cases hnext : i + 1 < s.length
                    · have hneed1 : ¬ NeedsCont (klByte s (i - 1)) (klByte s (i - 2)) :=
                        not_needsCont_of_charEnd hstate.2 hstate.1
                      have hpair1 : KlPair c (klByte s (i + 1)) := by
                        have hw := klErrWin_at_succ (s := s) (hi := hi) (hwin (i + 1) (by omega) hnext)
                        rcases (klErrByte_eq_zero_iff _ _ _ _).mp hw with ⟨hn, -⟩ | ⟨-, hp⟩
                        · exact absurd hn hneed1
                        · exact hp
                      have hp1 : 0x80 ≤ klByte s (i + 1) ∧ klByte s (i + 1) ≤ 0x9F := by
                        rw [hcED] at hpair1
                        exact pair_three2_cont hpair1
                      by_cases hnext2 : i + 2 < s.length
                      · have hcont2 : IsContByte (klByte s (i + 1)) ∧ IsContByte (klByte s (i + 2)) := by
                          have hw := klErrWin_at_succ2 (s := s) (hi := hi) (hwin (i + 2) (by omega) hnext2)
                          rcases (klErrByte_eq_zero_iff _ _ _ _).mp hw with ⟨hne, h1, h2⟩ | ⟨hnn, hp⟩
                          · exact ⟨h1, h2⟩
                          · exact absurd (needsCont_of_lead hE0) hnn
                        have hch : Utf8Char (ByteString.literal (s.drop i))
                            (0xD000 + ((klByte s (i + 1)).toNat - 0x80) * 0x40 + ((klByte s (i + 2)).toNat - 0x80))
                            (ByteString.literal (s.drop (i + 3))) := by
                          rw [literal_drop_cons hlen, literal_drop_cons hnext, literal_drop_cons hnext2]
                          rw [show klByte s i = 0xED from hcED]
                          exact Utf8Char.three₂ hp1.1 hp1.2 hcont2.2.1 hcont2.2.2
                        refine step 3 _ _ hch rfl (by omega) ⟨?_, ?_⟩
                        · refine not_needsCont_of_lt ?_ ?_
                          · rw [show i + 3 - 2 = i + 1 from by omega]; have h := cont_le hcont2.1; omega
                          · rw [show i + 3 - 3 = i from by omega]; rw [← hc]; omega
                        · rw [show i + 3 - 1 = i + 2 from by omega]; exact Or.inr hcont2.2
                      · have hcord : i + 2 = s.length := by omega
                        have hd : s.drop i = [c, klByte s (i + 1)] := by
                          rw [help_drop2 hlen hnext hcord, hc]
                        have hchar : Utf8Char (ByteString.literal (c :: klByte s (i + 1) :: 0x80 :: []))
                            (0xD000 + ((klByte s (i + 1)).toNat - 0x80) * 0x40
                              + ((0x80 : UInt8).toNat - 0x80))
                            (ByteString.literal []) := by
                          rw [ByteString.literal_cons, ByteString.literal_cons, ByteString.literal_cons]
                          rw [show c = 0xED from hcED]
                          exact Utf8Char.three₂ hp1.1 hp1.2 (by decide) (by decide)
                        exact lift 2 [c, klByte s (i + 1)] [0x80] _ hd (by simp) hchar
                    · have hcord : i + 1 = s.length := by omega
                      have hd : s.drop i = [c] := by rw [help_drop1 hlen hcord, hc]
                      have hchar : Utf8Char (ByteString.literal (c :: 0x80 :: 0x80 :: [])) 0xD000
                          (ByteString.literal []) := by
                        rw [ByteString.literal_cons, ByteString.literal_cons, ByteString.literal_cons]
                        rw [show c = 0xED from hcED]
                        exact Utf8Char.three₂ (by decide) (by decide) (by decide) (by decide)
                      exact lift 1 [c] [0x80, 0x80] _ hd (by simp) hchar
                  · have hECsplit : c.toNat ≤ 0xEC ∨ 0xEE ≤ c.toNat := by omega
                    have hpE : (0xE1 ≤ c ∧ c ≤ 0xEC) ∨ (0xEE ≤ c ∧ c ≤ 0xEF) := by
                      have hE1 : 0xE1 ≤ c := by
                        rw [UInt8.le_iff_toNat_le]
                        simp only [UInt8.toNat_ofNat]
                        omega
                      rcases hECsplit with hle | hge
                      · left
                        exact ⟨hE1, by rw [UInt8.le_iff_toNat_le]; exact hle⟩
                      · right
                        exact ⟨by rw [UInt8.le_iff_toNat_le]; simpa only [UInt8.toNat_ofNat] using hge,
                          by rw [UInt8.le_iff_toNat_le]; exact hef⟩
                    by_cases hnext : i + 1 < s.length
                    · have hneed1 : ¬ NeedsCont (klByte s (i - 1)) (klByte s (i - 2)) :=
                        not_needsCont_of_charEnd hstate.2 hstate.1
                      have hpair1 : KlPair c (klByte s (i + 1)) := by
                        have hw := klErrWin_at_succ (s := s) (hi := hi) (hwin (i + 1) (by omega) hnext)
                        rcases (klErrByte_eq_zero_iff _ _ _ _).mp hw with ⟨hn, -⟩ | ⟨-, hp⟩
                        · exact absurd hn hneed1
                        · exact hp
                      have hcont1 : IsContByte (klByte s (i + 1)) := by
                        rcases hpE with ⟨a, b⟩ | ⟨a, b⟩
                        · exact pair_three1_cont a b hpair1
                        · exact pair_three3_cont a b hpair1
                      by_cases hnext2 : i + 2 < s.length
                      · have hcont2 : IsContByte (klByte s (i + 1)) ∧ IsContByte (klByte s (i + 2)) := by
                          have hw := klErrWin_at_succ2 (s := s) (hi := hi) (hwin (i + 2) (by omega) hnext2)
                          rcases (klErrByte_eq_zero_iff _ _ _ _).mp hw with ⟨hne, h1, h2⟩ | ⟨hnn, hp⟩
                          · exact ⟨h1, h2⟩
                          · exact absurd (needsCont_of_lead hE0) hnn
                        have hch : Utf8Char (ByteString.literal (s.drop i))
                            (((klByte s i).toNat - 0xE0) * 0x1000 + ((klByte s (i + 1)).toNat - 0x80) * 0x40
                              + ((klByte s (i + 2)).toNat - 0x80))
                            (ByteString.literal (s.drop (i + 3))) := by
                          rw [literal_drop_cons hlen, literal_drop_cons hnext, literal_drop_cons hnext2]
                          exact Or.elim hpE
                            (fun h => Utf8Char.three₁ h.1 h.2 hcont1.1 hcont1.2 hcont2.2.1 hcont2.2.2)
                            (fun h => Utf8Char.three₃ h.1 h.2 hcont1.1 hcont1.2 hcont2.2.1 hcont2.2.2)
                        refine step 3 _ _ hch rfl (by omega) ⟨?_, ?_⟩
                        · refine not_needsCont_of_lt ?_ ?_
                          · rw [show i + 3 - 2 = i + 1 from by omega]; have h := cont_le hcont2.1; omega
                          · rw [show i + 3 - 3 = i from by omega, ← hc]; omega
                        · rw [show i + 3 - 1 = i + 2 from by omega]; exact Or.inr hcont2.2
                      · have hcord : i + 2 = s.length := by omega
                        have hd : s.drop i = [c, klByte s (i + 1)] := by
                          rw [help_drop2 hlen hnext hcord, hc]
                        have hchar : Utf8Char (ByteString.literal (c :: klByte s (i + 1) :: 0x80 :: []))
                            ((c.toNat - 0xE0) * 0x1000 + ((klByte s (i + 1)).toNat - 0x80) * 0x40
                              + ((0x80 : UInt8).toNat - 0x80))
                            (ByteString.literal []) := by
                          rw [ByteString.literal_cons, ByteString.literal_cons, ByteString.literal_cons]
                          exact Or.elim hpE
                            (fun h => Utf8Char.three₁ h.1 h.2 hcont1.1 hcont1.2 (by decide) (by decide))
                            (fun h => Utf8Char.three₃ h.1 h.2 hcont1.1 hcont1.2 (by decide) (by decide))
                        exact lift 2 [c, klByte s (i + 1)] [0x80] _ hd (by simp) hchar
                    · have hcord : i + 1 = s.length := by omega
                      have hd : s.drop i = [c] := by rw [help_drop1 hlen hcord, hc]
                      have hchar : Utf8Char (ByteString.literal (c :: 0x80 :: 0x80 :: []))
                          ((c.toNat - 0xE0) * 0x1000 + ((0x80 : UInt8).toNat - 0x80) * 0x40
                            + ((0x80 : UInt8).toNat - 0x80))
                          (ByteString.literal []) := by
                        rw [ByteString.literal_cons, ByteString.literal_cons, ByteString.literal_cons]
                        exact Or.elim hpE
                          (fun h => Utf8Char.three₁ h.1 h.2 (by decide) (by decide) (by decide) (by decide))
                          (fun h => Utf8Char.three₃ h.1 h.2 (by decide) (by decide) (by decide) (by decide))
                      exact lift 1 [c] [0x80, 0x80] _ hd (by simp) hchar
              · have hF0 : 0xF0 ≤ c.toNat := by omega
                have h0F : 0xF0 ≤ c := by rw [UInt8.le_iff_toNat_le]; exact hF0
                by_cases hf0 : c.toNat = 0xF0
                · have hcF0 : c = 0xF0 := UInt8.toNat_inj.mp (by simpa using hf0)
                  by_cases hnext : i + 1 < s.length
                  · have hneed1 : ¬ NeedsCont (klByte s (i - 1)) (klByte s (i - 2)) :=
                      not_needsCont_of_charEnd hstate.2 hstate.1
                    have hpair1 : KlPair c (klByte s (i + 1)) := by
                      have hw := klErrWin_at_succ (s := s) (hi := hi) (hwin (i + 1) (by omega) hnext)
                      rcases (klErrByte_eq_zero_iff _ _ _ _).mp hw with ⟨hn, -⟩ | ⟨-, hp⟩
                      · exact absurd hn hneed1
                      · exact hp
                    have hp1 : 0x90 ≤ klByte s (i + 1) ∧ klByte s (i + 1) ≤ 0xBF := by
                      rw [hcF0] at hpair1
                      exact pair_four0_cont hpair1
                    by_cases hnext2 : i + 2 < s.length
                    · have hcont2 : IsContByte (klByte s (i + 1)) ∧ IsContByte (klByte s (i + 2)) := by
                        have hw := klErrWin_at_succ2 (s := s) (hi := hi) (hwin (i + 2) (by omega) hnext2)
                        rcases (klErrByte_eq_zero_iff _ _ _ _).mp hw with ⟨hne, h1, h2⟩ | ⟨hnn, hp⟩
                        · exact ⟨h1, h2⟩
                        · exact absurd (needsCont_of_lead hE0) hnn
                      by_cases hnext3 : i + 3 < s.length
                      · have hcont3 : IsContByte (klByte s (i + 2)) ∧ IsContByte (klByte s (i + 3)) := by
                          have hw := klErrWin_at_succ3 (s := s) (hi := hi) (hwin (i + 3) (by omega) hnext3)
                          rcases (klErrByte_eq_zero_iff _ _ _ _).mp hw with ⟨hne, h1, h2⟩ | ⟨hnn, hp⟩
                          · exact ⟨h1, h2⟩
                          · exact absurd (needsCont_of_lead3 hF0) hnn
                        have hch : Utf8Char (ByteString.literal (s.drop i))
                            (((klByte s (i + 1)).toNat - 0x80) * 0x1000
                              + ((klByte s (i + 2)).toNat - 0x80) * 0x40 + ((klByte s (i + 3)).toNat - 0x80))
                            (ByteString.literal (s.drop (i + 4))) := by
                          rw [literal_drop_cons hlen, literal_drop_cons hnext, literal_drop_cons hnext2,
                            literal_drop_cons hnext3]
                          rw [show klByte s i = 0xF0 from hcF0]
                          exact Utf8Char.four₀ hp1.1 hp1.2 hcont2.2.1 hcont2.2.2 hcont3.2.1 hcont3.2.2
                        refine step 4 _ _ hch rfl (by omega) ⟨?_, ?_⟩
                        · refine not_needsCont_of_lt ?_ ?_
                          · rw [show i + 4 - 2 = i + 2 from by omega]; have h := cont_le hcont2.2; omega
                          · rw [show i + 4 - 3 = i + 1 from by omega]; have h := cont_le hcont2.1; omega
                        · rw [show i + 4 - 1 = i + 3 from by omega]; exact Or.inr hcont3.2
                      · have hcord : i + 3 = s.length := by omega
                        have hd : s.drop i = [c, klByte s (i + 1), klByte s (i + 2)] := by
                          rw [help_drop3 hlen hnext hnext2 hcord, hc]
                        have hchar : Utf8Char
                            (ByteString.literal (c :: klByte s (i + 1) :: klByte s (i + 2) :: 0x80 :: []))
                            (((klByte s (i + 1)).toNat - 0x80) * 0x1000
                              + ((klByte s (i + 2)).toNat - 0x80) * 0x40 + ((0x80 : UInt8).toNat - 0x80))
                            (ByteString.literal []) := by
                          rw [ByteString.literal_cons, ByteString.literal_cons, ByteString.literal_cons,
                            ByteString.literal_cons]
                          rw [show c = 0xF0 from hcF0]
                          exact Utf8Char.four₀ hp1.1 hp1.2 hcont2.2.1 hcont2.2.2 (by decide) (by decide)
                        exact lift 3 [c, klByte s (i + 1), klByte s (i + 2)] [0x80] _ hd (by simp) hchar
                    · have hcord : i + 2 = s.length := by omega
                      have hd : s.drop i = [c, klByte s (i + 1)] := by
                        rw [help_drop2 hlen hnext hcord, hc]
                      have hchar : Utf8Char (ByteString.literal (c :: klByte s (i + 1) :: 0x80 :: 0x80 :: []))
                          (((klByte s (i + 1)).toNat - 0x80) * 0x1000
                            + ((0x80 : UInt8).toNat - 0x80) * 0x40 + ((0x80 : UInt8).toNat - 0x80))
                          (ByteString.literal []) := by
                        rw [ByteString.literal_cons, ByteString.literal_cons, ByteString.literal_cons,
                          ByteString.literal_cons]
                        rw [show c = 0xF0 from hcF0]
                        exact Utf8Char.four₀ hp1.1 hp1.2 (by decide) (by decide) (by decide) (by decide)
                      exact lift 2 [c, klByte s (i + 1)] [0x80, 0x80] _ hd (by simp) hchar
                  · have hcord : i + 1 = s.length := by omega
                    have hd : s.drop i = [c] := by rw [help_drop1 hlen hcord, hc]
                    have hchar : Utf8Char (ByteString.literal (c :: 0x90 :: 0x80 :: 0x80 :: [])) 0x10000
                        (ByteString.literal []) := by
                      rw [ByteString.literal_cons, ByteString.literal_cons, ByteString.literal_cons,
                        ByteString.literal_cons]
                      rw [show c = 0xF0 from hcF0]
                      exact Utf8Char.four₀ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                    exact lift 1 [c] [0x90, 0x80, 0x80] _ hd (by simp) hchar
                · by_cases hf4 : c.toNat = 0xF4
                  · have hcF4 : c = 0xF4 := UInt8.toNat_inj.mp (by simpa using hf4)
                    by_cases hnext : i + 1 < s.length
                    · have hneed1 : ¬ NeedsCont (klByte s (i - 1)) (klByte s (i - 2)) :=
                        not_needsCont_of_charEnd hstate.2 hstate.1
                      have hpair1 : KlPair c (klByte s (i + 1)) := by
                        have hw := klErrWin_at_succ (s := s) (hi := hi) (hwin (i + 1) (by omega) hnext)
                        rcases (klErrByte_eq_zero_iff _ _ _ _).mp hw with ⟨hn, -⟩ | ⟨-, hp⟩
                        · exact absurd hn hneed1
                        · exact hp
                      have hp1 : 0x80 ≤ klByte s (i + 1) ∧ klByte s (i + 1) ≤ 0x8F := by
                        rw [hcF4] at hpair1
                        exact pair_four2_cont hpair1
                      by_cases hnext2 : i + 2 < s.length
                      · have hcont2 : IsContByte (klByte s (i + 1)) ∧ IsContByte (klByte s (i + 2)) := by
                          have hw := klErrWin_at_succ2 (s := s) (hi := hi) (hwin (i + 2) (by omega) hnext2)
                          rcases (klErrByte_eq_zero_iff _ _ _ _).mp hw with ⟨hne, h1, h2⟩ | ⟨hnn, hp⟩
                          · exact ⟨h1, h2⟩
                          · exact absurd (needsCont_of_lead hE0) hnn
                        by_cases hnext3 : i + 3 < s.length
                        · have hcont3 : IsContByte (klByte s (i + 2)) ∧ IsContByte (klByte s (i + 3)) := by
                            have hw := klErrWin_at_succ3 (s := s) (hi := hi) (hwin (i + 3) (by omega) hnext3)
                            rcases (klErrByte_eq_zero_iff _ _ _ _).mp hw with ⟨hne, h1, h2⟩ | ⟨hnn, hp⟩
                            · exact ⟨h1, h2⟩
                            · exact absurd (needsCont_of_lead3 hF0) hnn
                          have hch : Utf8Char (ByteString.literal (s.drop i))
                              (0x100000 + ((klByte s (i + 1)).toNat - 0x80) * 0x1000
                                + ((klByte s (i + 2)).toNat - 0x80) * 0x40 + ((klByte s (i + 3)).toNat - 0x80))
                              (ByteString.literal (s.drop (i + 4))) := by
                            rw [literal_drop_cons hlen, literal_drop_cons hnext, literal_drop_cons hnext2,
                              literal_drop_cons hnext3]
                            rw [show klByte s i = 0xF4 from hcF4]
                            exact Utf8Char.four₂ hp1.1 hp1.2 hcont2.2.1 hcont2.2.2 hcont3.2.1 hcont3.2.2
                          refine step 4 _ _ hch rfl (by omega) ⟨?_, ?_⟩
                          · refine not_needsCont_of_lt ?_ ?_
                            · rw [show i + 4 - 2 = i + 2 from by omega]; have h := cont_le hcont2.2; omega
                            · rw [show i + 4 - 3 = i + 1 from by omega]; have h := cont_le hcont2.1; omega
                          · rw [show i + 4 - 1 = i + 3 from by omega]; exact Or.inr hcont3.2
                        · have hcord : i + 3 = s.length := by omega
                          have hd : s.drop i = [c, klByte s (i + 1), klByte s (i + 2)] := by
                            rw [help_drop3 hlen hnext hnext2 hcord, hc]
                          have hchar : Utf8Char
                              (ByteString.literal (c :: klByte s (i + 1) :: klByte s (i + 2) :: 0x80 :: []))
                              (0x100000 + ((klByte s (i + 1)).toNat - 0x80) * 0x1000
                                + ((klByte s (i + 2)).toNat - 0x80) * 0x40 + ((0x80 : UInt8).toNat - 0x80))
                              (ByteString.literal []) := by
                            rw [ByteString.literal_cons, ByteString.literal_cons, ByteString.literal_cons,
                              ByteString.literal_cons]
                            rw [show c = 0xF4 from hcF4]
                            exact Utf8Char.four₂ hp1.1 hp1.2 hcont2.2.1 hcont2.2.2 (by decide) (by decide)
                          exact lift 3 [c, klByte s (i + 1), klByte s (i + 2)] [0x80] _ hd (by simp) hchar
                      · have hcord : i + 2 = s.length := by omega
                        have hd : s.drop i = [c, klByte s (i + 1)] := by
                          rw [help_drop2 hlen hnext hcord, hc]
                        have hchar : Utf8Char (ByteString.literal (c :: klByte s (i + 1) :: 0x80 :: 0x80 :: []))
                            (0x100000 + ((klByte s (i + 1)).toNat - 0x80) * 0x1000
                              + ((0x80 : UInt8).toNat - 0x80) * 0x40 + ((0x80 : UInt8).toNat - 0x80))
                            (ByteString.literal []) := by
                          rw [ByteString.literal_cons, ByteString.literal_cons, ByteString.literal_cons,
                            ByteString.literal_cons]
                          rw [show c = 0xF4 from hcF4]
                          exact Utf8Char.four₂ hp1.1 hp1.2 (by decide) (by decide) (by decide) (by decide)
                        exact lift 2 [c, klByte s (i + 1)] [0x80, 0x80] _ hd (by simp) hchar
                    · have hcord : i + 1 = s.length := by omega
                      have hd : s.drop i = [c] := by rw [help_drop1 hlen hcord, hc]
                      have hchar : Utf8Char (ByteString.literal (c :: 0x80 :: 0x80 :: 0x80 :: [])) 0x100000
                          (ByteString.literal []) := by
                        rw [ByteString.literal_cons, ByteString.literal_cons, ByteString.literal_cons,
                          ByteString.literal_cons]
                        rw [show c = 0xF4 from hcF4]
                        exact Utf8Char.four₂ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                      exact lift 1 [c] [0x80, 0x80, 0x80] _ hd (by simp) hchar
                  · by_cases hf13 : c.toNat ≤ 0xF3
                    · have h0F1 : 0xF1 ≤ c := by
                        rw [UInt8.le_iff_toNat_le]
                        simp only [UInt8.toNat_ofNat]
                        omega
                      have h0F3 : c ≤ 0xF3 := by rw [UInt8.le_iff_toNat_le]; exact hf13
                      by_cases hnext : i + 1 < s.length
                      · have hneed1 : ¬ NeedsCont (klByte s (i - 1)) (klByte s (i - 2)) :=
                          not_needsCont_of_charEnd hstate.2 hstate.1
                        have hpair1 : KlPair c (klByte s (i + 1)) := by
                          have hw := klErrWin_at_succ (s := s) (hi := hi) (hwin (i + 1) (by omega) hnext)
                          rcases (klErrByte_eq_zero_iff _ _ _ _).mp hw with ⟨hn, -⟩ | ⟨-, hp⟩
                          · exact absurd hn hneed1
                          · exact hp
                        have hcont1 : IsContByte (klByte s (i + 1)) := pair_four1_cont h0F1 h0F3 hpair1
                        by_cases hnext2 : i + 2 < s.length
                        · have hcont2 : IsContByte (klByte s (i + 1)) ∧ IsContByte (klByte s (i + 2)) := by
                            have hw := klErrWin_at_succ2 (s := s) (hi := hi) (hwin (i + 2) (by omega) hnext2)
                            rcases (klErrByte_eq_zero_iff _ _ _ _).mp hw with ⟨hne, h1, h2⟩ | ⟨hnn, hp⟩
                            · exact ⟨h1, h2⟩
                            · exact absurd (needsCont_of_lead hE0) hnn
                          by_cases hnext3 : i + 3 < s.length
                          · have hcont3 : IsContByte (klByte s (i + 2)) ∧ IsContByte (klByte s (i + 3)) := by
                              have hw := klErrWin_at_succ3 (s := s) (hi := hi) (hwin (i + 3) (by omega) hnext3)
                              rcases (klErrByte_eq_zero_iff _ _ _ _).mp hw with ⟨hne, h1, h2⟩ | ⟨hnn, hp⟩
                              · exact ⟨h1, h2⟩
                              · exact absurd (needsCont_of_lead3 hF0) hnn
                            have hch : Utf8Char (ByteString.literal (s.drop i))
                                (((klByte s i).toNat - 0xF0) * 0x40000
                                  + ((klByte s (i + 1)).toNat - 0x80) * 0x1000
                                  + ((klByte s (i + 2)).toNat - 0x80) * 0x40 + ((klByte s (i + 3)).toNat - 0x80))
                                (ByteString.literal (s.drop (i + 4))) := by
                              rw [literal_drop_cons hlen, literal_drop_cons hnext, literal_drop_cons hnext2,
                                literal_drop_cons hnext3]
                              exact Utf8Char.four₁ h0F1 h0F3 hcont1.1 hcont1.2 hcont2.2.1 hcont2.2.2
                                hcont3.2.1 hcont3.2.2
                            refine step 4 _ _ hch rfl (by omega) ⟨?_, ?_⟩
                            · refine not_needsCont_of_lt ?_ ?_
                              · rw [show i + 4 - 2 = i + 2 from by omega]; have h := cont_le hcont2.2; omega
                              · rw [show i + 4 - 3 = i + 1 from by omega]; have h := cont_le hcont2.1; omega
                            · rw [show i + 4 - 1 = i + 3 from by omega]; exact Or.inr hcont3.2
                          · have hcord : i + 3 = s.length := by omega
                            have hd : s.drop i = [c, klByte s (i + 1), klByte s (i + 2)] := by
                              rw [help_drop3 hlen hnext hnext2 hcord, hc]
                            have hchar : Utf8Char
                                (ByteString.literal (c :: klByte s (i + 1) :: klByte s (i + 2) :: 0x80 :: []))
                                ((c.toNat - 0xF0) * 0x40000 + ((klByte s (i + 1)).toNat - 0x80) * 0x1000
                                  + ((klByte s (i + 2)).toNat - 0x80) * 0x40 + ((0x80 : UInt8).toNat - 0x80))
                                (ByteString.literal []) := by
                              rw [ByteString.literal_cons, ByteString.literal_cons, ByteString.literal_cons,
                                ByteString.literal_cons]
                              exact Utf8Char.four₁ h0F1 h0F3 hcont1.1 hcont1.2 hcont2.2.1 hcont2.2.2
                                (by decide) (by decide)
                            exact lift 3 [c, klByte s (i + 1), klByte s (i + 2)] [0x80] _ hd (by simp) hchar
                        · have hcord : i + 2 = s.length := by omega
                          have hd : s.drop i = [c, klByte s (i + 1)] := by
                            rw [help_drop2 hlen hnext hcord, hc]
                          have hchar : Utf8Char (ByteString.literal (c :: klByte s (i + 1) :: 0x80 :: 0x80 :: []))
                              ((c.toNat - 0xF0) * 0x40000 + ((klByte s (i + 1)).toNat - 0x80) * 0x1000
                                + ((0x80 : UInt8).toNat - 0x80) * 0x40 + ((0x80 : UInt8).toNat - 0x80))
                              (ByteString.literal []) := by
                            rw [ByteString.literal_cons, ByteString.literal_cons, ByteString.literal_cons,
                              ByteString.literal_cons]
                            exact Utf8Char.four₁ h0F1 h0F3 hcont1.1 hcont1.2 (by decide) (by decide)
                              (by decide) (by decide)
                          exact lift 2 [c, klByte s (i + 1)] [0x80, 0x80] _ hd (by simp) hchar
                      · have hcord : i + 1 = s.length := by omega
                        have hd : s.drop i = [c] := by rw [help_drop1 hlen hcord, hc]
                        have hchar : Utf8Char (ByteString.literal (c :: 0x80 :: 0x80 :: 0x80 :: []))
                            ((c.toNat - 0xF0) * 0x40000 + ((0x80 : UInt8).toNat - 0x80) * 0x1000
                              + ((0x80 : UInt8).toNat - 0x80) * 0x40 + ((0x80 : UInt8).toNat - 0x80))
                            (ByteString.literal []) := by
                          rw [ByteString.literal_cons, ByteString.literal_cons, ByteString.literal_cons,
                            ByteString.literal_cons]
                          exact Utf8Char.four₁ (b1 := 0x80) (b2 := 0x80) (b3 := 0x80)
                            h0F1 h0F3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                        exact lift 1 [c] [0x80, 0x80, 0x80] _ hd (by simp) hchar
                    · have h1 : 0xF5 ≤ c :=
                        u8_le_of_toNat (by simp only [UInt8.toNat_ofNat] at hf13 hf4 ⊢; omega)
                      have hctrue : klTailByte c = true :=
                        klTailByte_true_of_F5 h1 (by have := c.toNat_lt; omega)
                      by_cases hnext : i + 1 < s.length
                      · exfalso
                        have hneed1 : ¬ NeedsCont (klByte s (i - 1)) (klByte s (i - 2)) :=
                          not_needsCont_of_charEnd hstate.2 hstate.1
                        have hpair1 : KlPair c (klByte s (i + 1)) := by
                          have hw := klErrWin_at_succ (s := s) (hi := hi) (hwin (i + 1) (by omega) hnext)
                          rcases (klErrByte_eq_zero_iff _ _ _ _).mp hw with ⟨hn, -⟩ | ⟨-, hp⟩
                          · exact absurd hn hneed1
                          · rw [← hc] at hp
                            exact hp
                        have hnc' : ¬ IsCharEnd c := by
                          rw [isCharEnd_nat]; omega
                        have hnl : ¬ IsUtf8LeadByte c := by
                          intro hl
                          unfold IsUtf8LeadByte at hl
                          simp only [UInt8.lt_iff_toNat_lt, UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at hl
                          omega
                        exact not_klPair_of_dead hnc' hnl hpair1
                      · exfalso
                        have hi_eq : i = s.length - 1 := by omega
                        rw [hc] at hctrue
                        exact hlast (by rw [← hi_eq]; exact hctrue)
    · have hdrop : s.drop i = [] := List.drop_eq_nil_of_le (by omega)
      rw [hdrop]
      exact ⟨ByteString.literal [], Utf8Spans.nil _, Or.inl rfl⟩

theorem not_klTailByte_of_char_prefix {b : Bytes} {c : Nat} {r : Bytes}
    (hc : Utf8Char b c r) {k : Nat} (hk1 : 1 ≤ k) (hkl : k < b.length - r.length) :
    ¬ klTailByte ((b.data.toList).getD (k - 1) 0x00) = true := by
  cases hc with
  | one h =>
      simp only [ByteString.length_eq_size, ByteString.size_cons] at hkl
      omega
  | two h0 h0' h1 h1' =>
      simp only [ByteString.length_eq_size, ByteString.size_cons] at hkl
      have hk : k = 1 := by omega
      rename_i b0 b1
      rw [hk]
      show ¬ klTailByte b0 = true
      rw [klTailByte_false_of_lead h0 (UInt8.le_trans h0' (by decide))]; simp
  | three₀ h1 h1' h2 h2' =>
      simp only [ByteString.length_eq_size, ByteString.size_cons] at hkl
      have hk : k = 1 ∨ k = 2 := by omega
      rename_i b1 b2
      rcases hk with rfl | rfl
      · show ¬ klTailByte (0xE0 : UInt8) = true
        rw [klTailByte_false_of_lead (by decide : (0xC2 : UInt8) ≤ 0xE0) (by decide)]; simp
      · show ¬ klTailByte b1 = true
        rw [klTailByte_false_of_cont (UInt8.le_trans (by decide) h1) h1']; simp
  | three₁ h0 h0' h1 h1' h2 h2' =>
      simp only [ByteString.length_eq_size, ByteString.size_cons] at hkl
      have hk : k = 1 ∨ k = 2 := by omega
      rename_i b0 b1 b2
      rcases hk with rfl | rfl
      · show ¬ klTailByte b0 = true
        rw [klTailByte_false_of_lead (UInt8.le_trans (by decide) h0)
          (UInt8.le_trans h0' (by decide))]; simp
      · show ¬ klTailByte b1 = true
        rw [klTailByte_false_of_cont h1 h1']; simp
  | three₂ h1 h1' h2 h2' =>
      simp only [ByteString.length_eq_size, ByteString.size_cons] at hkl
      have hk : k = 1 ∨ k = 2 := by omega
      rename_i b1 b2
      rcases hk with rfl | rfl
      · show ¬ klTailByte (0xED : UInt8) = true
        rw [klTailByte_false_of_lead (by decide : (0xC2 : UInt8) ≤ 0xED) (by decide)]; simp
      · show ¬ klTailByte b1 = true
        rw [klTailByte_false_of_cont h1 (UInt8.le_trans h1' (by decide))]; simp
  | three₃ h0 h0' h1 h1' h2 h2' =>
      simp only [ByteString.length_eq_size, ByteString.size_cons] at hkl
      have hk : k = 1 ∨ k = 2 := by omega
      rename_i b0 b1 b2
      rcases hk with rfl | rfl
      · show ¬ klTailByte b0 = true
        rw [klTailByte_false_of_lead (UInt8.le_trans (by decide) h0)
          (UInt8.le_trans h0' (by decide))]; simp
      · show ¬ klTailByte b1 = true
        rw [klTailByte_false_of_cont h1 h1']; simp
  | four₀ h1 h1' h2 h2' h3 h3' =>
      simp only [ByteString.length_eq_size, ByteString.size_cons] at hkl
      have hk : k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rename_i b1 b2 b3
      rcases hk with rfl | rfl | rfl
      · show ¬ klTailByte (0xF0 : UInt8) = true
        rw [klTailByte_false_of_lead (by decide : (0xC2 : UInt8) ≤ 0xF0) (by decide)]; simp
      · show ¬ klTailByte b1 = true
        rw [klTailByte_false_of_cont (UInt8.le_trans (by decide) h1) h1']; simp
      · show ¬ klTailByte b2 = true
        rw [klTailByte_false_of_cont h2 h2']; simp
  | four₁ h0 h0' h1 h1' h2 h2' h3 h3' =>
      simp only [ByteString.length_eq_size, ByteString.size_cons] at hkl
      have hk : k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rename_i b0 b1 b2 b3
      rcases hk with rfl | rfl | rfl
      · show ¬ klTailByte b0 = true
        rw [klTailByte_false_of_lead (UInt8.le_trans (by decide) h0)
          (UInt8.le_trans h0' (by decide))]; simp
      · show ¬ klTailByte b1 = true
        rw [klTailByte_false_of_cont h1 h1']; simp
      · show ¬ klTailByte b2 = true
        rw [klTailByte_false_of_cont h2 h2']; simp
  | four₂ h1 h1' h2 h2' h3 h3' =>
      simp only [ByteString.length_eq_size, ByteString.size_cons] at hkl
      have hk : k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rename_i b1 b2 b3
      rcases hk with rfl | rfl | rfl
      · show ¬ klTailByte (0xF4 : UInt8) = true
        rw [klTailByte_false_of_lead (by decide : (0xC2 : UInt8) ≤ 0xF4) (by decide)]; simp
      · show ¬ klTailByte b1 = true
        rw [klTailByte_false_of_cont h1 (UInt8.le_trans h1' (by decide))]; simp
      · show ¬ klTailByte b2 = true
        rw [klTailByte_false_of_cont h2 h2']; simp

theorem le_mul_div_sixtyfour (n : Nat) : n ≤ 64 * ((n + 63) / 64) := by
  have h := Nat.div_add_mod (n + 63) 64
  have hmod : (n + 63) % 64 < 64 := Nat.mod_lt _ (by decide)
  omega

theorem klByte_append_right (a b : List UInt8) (j : Nat) :
    klByte (a ++ b) (a.length + j) = klByte b j := by
  unfold klByte
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (Nat.le_add_right a.length j),
    show a.length + j - a.length = j from by omega]

theorem klByte_replicate_zero (p j : Nat) :
    klByte (List.replicate p (0x00 : UInt8)) j = 0x00 := by
  unfold klByte
  rw [List.getD_eq_getElem?_getD]
  cases h : (List.replicate p (0x00 : UInt8))[j]? with
  | none => rfl
  | some v =>
      have hv : v = 0x00 := by
        obtain ⟨hj, hval⟩ := List.getElem?_eq_some_iff.mp h
        rw [List.getElem_replicate hj] at hval
        exact hval.symm
      rw [hv]
      rfl

theorem klByte_win_pad_last (bs : List UInt8) (n nb : Nat)
    (hpad : 0 < 64 * nb - n) :
    klByte (List.replicate 3 0x00 ++ bs ++ List.replicate (64 * nb - n) 0x00)
      ((List.replicate 3 0x00 ++ bs ++ List.replicate (64 * nb - n) 0x00).length - 1)
      = 0x00 := by
  have hj : (List.replicate 3 0x00 ++ bs ++ List.replicate (64 * nb - n) 0x00).length - 1
      = (List.replicate 3 0x00 ++ bs).length + (64 * nb - n - 1) := by
    simp only [List.length_append, List.length_replicate]
    omega
  rw [hj, klByte_append_right, klByte_replicate_zero]

theorem klByte_win_doc_last (bs : List UInt8) (n nb : Nat) (hn : n = bs.length)
    (hpad : 64 * nb - n = 0) (hn0 : 0 < n) :
    klByte (List.replicate 3 0x00 ++ bs ++ List.replicate (64 * nb - n) 0x00)
      ((List.replicate 3 0x00 ++ bs ++ List.replicate (64 * nb - n) 0x00).length - 1)
      = klByte bs (n - 1) := by
  have hj : (List.replicate 3 0x00 ++ bs ++ List.replicate (64 * nb - n) 0x00).length - 1
      = (List.replicate 3 0x00).length + (n - 1) := by
    simp only [List.length_append, List.length_replicate, hn]
    omega
  have hpad' : List.replicate (64 * nb - n) (0x00 : UInt8) = [] := by rw [hpad]; rfl
  rw [hj]
  rw [hpad', List.append_nil]
  exact klByte_append_right (List.replicate 3 (0x00 : UInt8)) bs (n - 1)

theorem validPrefix_zero_cons {l : List UInt8}
    (h : ValidPrefix (ByteString.literal (0x00 :: l))) : ValidPrefix (ByteString.literal l) := by
  rcases h with ⟨t, hspans, htail⟩
  rcases utf8Spans_zero hspans with hw | hs
  · rcases htail with ht | hp
    · rw [hw] at ht
      exact absurd ht (literal_cons_ne_empty 0x00 l)
    · rw [hw] at hp
      exact absurd hp (not_utf8PrefixOf_zero l)
  · exact ⟨t, hs, htail⟩

theorem validPrefix_zero_cons_back {l : List UInt8}
    (h : ValidPrefix (ByteString.literal l)) : ValidPrefix (ByteString.literal (0x00 :: l)) := by
  rcases h with ⟨t, hspans, htail⟩
  refine ⟨t, ?_, htail⟩
  rw [ByteString.literal_cons]
  exact Utf8Spans.char (Utf8Char.one (b := 0x00) (rest := ByteString.literal l) (by decide)) hspans

theorem validPrefix_three_cons {l : List UInt8}
    (h : ValidPrefix (ByteString.literal (0x00 :: 0x00 :: 0x00 :: l))) :
    ValidPrefix (ByteString.literal l) :=
  validPrefix_zero_cons (validPrefix_zero_cons (validPrefix_zero_cons h))

theorem validPrefix_three_cons_back {l : List UInt8}
    (h : ValidPrefix (ByteString.literal l)) :
    ValidPrefix (ByteString.literal (0x00 :: 0x00 :: 0x00 :: l)) :=
  validPrefix_zero_cons_back (validPrefix_zero_cons_back (validPrefix_zero_cons_back h))

theorem klByte_take_len {l : List UInt8} {n j : Nat} (hj : j < n) :
    klByte (l.take n) j = klByte l j := by
  unfold klByte
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hj]

theorem pad_eq_zero_of_mod {n nb : Nat} (hnb : nb = (n + 63) / 64) (h : n % 64 = 0) :
    64 * nb - n = 0 := by
  subst hnb
  have h1 : n = 64 * (n / 64) := by
    have := Nat.div_add_mod n 64
    omega
  have h2 : (n + 63) / 64 = n / 64 := by
    have hd : n + 63 = 64 * (n / 64) + 63 := by omega
    rw [hd, Nat.mul_add_div (by decide : 0 < 64)]
    simp
  rw [h2, ← h1]
  exact Nat.sub_self _

theorem not_klTailByte_last_of_validPrefix {l : List UInt8} (hl : l ≠ []) :
    ValidPrefix (ByteString.literal l) →
    ¬ klTailByte (klByte l (l.length - 1)) = true := by
  intro hvp
  rcases hvp with ⟨t, hspans, ht | hp⟩
  · rw [ht] at hspans
    have hz0 : klByte (0x00 :: 0x00 :: 0x00 :: l) 0 = 0x00 := rfl
    have hz1 : klByte (0x00 :: 0x00 :: 0x00 :: l) 1 = 0x00 := rfl
    have hz2 : klByte (0x00 :: 0x00 :: 0x00 :: l) 2 = 0x00 := rfl
    have hstate : ¬ NeedsCont (klByte (0x00 :: 0x00 :: 0x00 :: l) 1)
        (klByte (0x00 :: 0x00 :: 0x00 :: l) 0) ∧
        IsCharEnd (klByte (0x00 :: 0x00 :: 0x00 :: l) 2) := by
      rw [hz1, hz0, hz2]
      exact ⟨by decide, Or.inl (by decide)⟩
    obtain ⟨-, -, he1⟩ := spans_ok hspans (0x00 :: 0x00 :: 0x00 :: l) 3 rfl (by omega)
      hstate.1 hstate.2
    have hblen : (ByteString.literal l).length = l.length := by
      rw [ByteString.length_eq_size, ByteString.size_literal]
    have hzlen : ByteString.empty.length = 0 := rfl
    have hlpos : 0 < l.length := by
      cases l with
      | nil => exact absurd rfl hl
      | cons _ _ => simp
    have heq : klByte (0x00 :: 0x00 :: 0x00 :: l)
          (3 - 3 + ((ByteString.literal l).length - ByteString.empty.length) + 2)
        = klByte l (l.length - 1) := by
      rw [hblen, hzlen]
      rw [show (0x00 :: 0x00 :: 0x00 :: l) = List.replicate 3 (0x00 : UInt8) ++ l from rfl]
      rw [show 3 - 3 + (l.length - 0) + 2 = (List.replicate 3 (0x00 : UInt8)).length + (l.length - 1) from by
        simp only [List.length_replicate]; omega]
      exact klByte_append_right (List.replicate 3 (0x00 : UInt8)) l (l.length - 1)
    rw [heq] at he1
    intro hb
    rw [klTailByte_false_of_charEnd he1] at hb
    simp at hb
  · rcases hp with ⟨htne, b, c, r, hc, hlt, hp'⟩
    obtain ⟨k, hk⟩ := utf8Spans_literal_tail hspans
    have hklt : k < l.length := by
      by_cases h : k < l.length
      · exact h
      · exfalso
        have hnil : l.drop k = [] := List.drop_eq_nil_of_le (by omega)
        rw [hk, hnil] at htne
        exact htne rfl
    have htlen : t.length = (l.length - k) := by
      rw [hk, ByteString.length_eq_size, ByteString.size_literal, List.length_drop]
    have htlen' : (l.drop k).length = l.length - k := List.length_drop
    have ht_take : t = b.take t.length := by
      unfold HasPrefix at hp'
      rw [ByteString.drop_zero] at hp'
      exact hp'.symm
    have hprefix : ¬ klTailByte ((b.data.toList).getD (t.length - 1) 0x00) = true :=
      not_klTailByte_of_char_prefix hc (by omega) hlt
    have hklast : klByte l (l.length - 1) = klByte (b.data.toList) (t.length - 1) := by
      have h1 : klByte l (l.length - 1) = klByte (l.drop k) ((l.drop k).length - 1) := by
        rw [← klByte_drop]
        congr 1
        omega
      have h2 : klByte (l.drop k) ((l.drop k).length - 1)
          = klByte (t.data.toList) (t.length - 1) := by
        rw [hk, ByteString.length_eq_size, ByteString.size_literal]
        rfl
      have htlist : t.data.toList = (b.data.toList).take t.length := by
        conv =>
          lhs
          rw [ht_take]
        rw [ByteString.data_toList_take]
      have h3 : klByte (t.data.toList) (t.length - 1)
          = klByte ((b.data.toList).take t.length) (t.length - 1) := by rw [htlist]
      have h4 : klByte ((b.data.toList).take t.length) (t.length - 1)
          = klByte (b.data.toList) (t.length - 1) :=
        klByte_take_len (l := b.data.toList) (n := t.length) (j := t.length - 1) (by omega)
      rw [h1, h2, h3, h4]
    intro hb
    rw [hklast] at hb
    exact hprefix hb

theorem klErrAll_window_iff (bs : List UInt8) (n nb : Nat)
    (hn : n = bs.length) (hnb : nb = (n + 63) / 64) :
    (klErrAll (List.replicate 3 0x00 ++ bs ++ List.replicate (64 * nb - n) 0x00) (64 * nb) ∧
      ¬ (n ≠ 0 ∧ n % 64 = 0 ∧ klTailByte (klByte bs (n - 1)) = true)) ↔
    ValidPrefix (ByteString.literal
      (List.replicate 3 0x00 ++ bs ++ List.replicate (64 * nb - n) 0x00)) := by
  have hle : n ≤ 64 * nb := by rw [hnb]; exact le_mul_div_sixtyfour n
  have hLlen : (bs ++ List.replicate (64 * nb - n) 0x00).length = 64 * nb := by
    simp only [List.length_append, List.length_replicate, hn]; omega
  have hlitlen : (ByteString.literal (bs ++ List.replicate (64 * nb - n) 0x00)).length
      = (bs ++ List.replicate (64 * nb - n) 0x00).length := by
    rw [ByteString.length_eq_size, ByteString.size_literal]
  have hzlen : ByteString.empty.length = 0 := rfl
  have hwinlen : (List.replicate 3 (0x00 : UInt8) ++ bs ++ List.replicate (64 * nb - n) 0x00).length
      = 3 + (bs ++ List.replicate (64 * nb - n) 0x00).length := by
    simp only [List.length_append, List.length_replicate]
    omega
  have hsplit : (List.replicate 3 (0x00 : UInt8) ++ bs ++ List.replicate (64 * nb - n) 0x00)
      = 0x00 :: 0x00 :: 0x00 :: (bs ++ List.replicate (64 * nb - n) 0x00) := rfl
  have hdrop3 : (List.replicate 3 (0x00 : UInt8) ++ bs ++ List.replicate (64 * nb - n) 0x00).drop 3
      = bs ++ List.replicate (64 * nb - n) 0x00 := by rw [hsplit]; rfl
  have hw0 : klByte (List.replicate 3 (0x00 : UInt8) ++ bs ++ List.replicate (64 * nb - n) 0x00)
      0 = 0x00 := by rw [hsplit]; rfl
  have hw1 : klByte (List.replicate 3 (0x00 : UInt8) ++ bs ++ List.replicate (64 * nb - n) 0x00)
      1 = 0x00 := by rw [hsplit]; rfl
  have hw2 : klByte (List.replicate 3 (0x00 : UInt8) ++ bs ++ List.replicate (64 * nb - n) 0x00)
      2 = 0x00 := by rw [hsplit]; rfl
  have hstate : ¬ NeedsCont
      (klByte (List.replicate 3 (0x00 : UInt8) ++ bs ++ List.replicate (64 * nb - n) 0x00) (3 - 2))
      (klByte (List.replicate 3 (0x00 : UInt8) ++ bs ++ List.replicate (64 * nb - n) 0x00) (3 - 3)) ∧
      IsCharEnd (klByte (List.replicate 3 (0x00 : UInt8) ++ bs ++ List.replicate (64 * nb - n) 0x00)
        (3 - 1)) := by
    refine ⟨?_, ?_⟩
    · rw [show 3 - 2 = 1 from rfl, show 3 - 3 = 0 from rfl, hw1, hw0]
      exact (by decide : ¬ NeedsCont (0x00 : UInt8) (0x00 : UInt8))
    · rw [show 3 - 1 = 2 from rfl, hw2]
      exact Or.inl (by decide)
  constructor
  · rintro ⟨hwinall, htail⟩
    have hlast : ¬ klTailByte (klByte
        (List.replicate 3 (0x00 : UInt8) ++ bs ++ List.replicate (64 * nb - n) 0x00)
        ((List.replicate 3 (0x00 : UInt8) ++ bs ++ List.replicate (64 * nb - n) 0x00).length - 1))
        = true := by
      intro hb
      by_cases hpad : 64 * nb - n = 0
      · by_cases hn0 : n = 0
        · subst hn0
          have hnb0 : nb = 0 := by omega
          subst hnb0
          have hbs0 : bs = [] := List.eq_nil_of_length_eq_zero hn.symm
          subst hbs0
          exact absurd hb (by decide)
        · have hmod : n % 64 = 0 := by
            have h1 : n = 64 * nb := by omega
            rw [h1]; omega
          have hbl := klByte_win_doc_last bs n nb hn hpad (by omega)
          exact htail ⟨hn0, hmod, by rw [← hbl]; exact hb⟩
      · have hb0 := klByte_win_pad_last bs n nb (by omega)
        rw [hb0] at hb
        exact absurd hb (by decide)
    have hwin' : ∀ q, 3 ≤ q →
        q < (List.replicate 3 (0x00 : UInt8) ++ bs ++ List.replicate (64 * nb - n) 0x00).length →
        klErrWin (List.replicate 3 (0x00 : UInt8) ++ bs ++ List.replicate (64 * nb - n) 0x00) (q - 3) := by
      intro q hq hqw
      rw [hwinlen] at hqw
      have hlt : q - 3 < 64 * nb := by omega
      exact hwinall (q - 3) hlt
    have hvpl := validPrefix_of_klErrAll (s := List.replicate 3 (0x00 : UInt8) ++ bs ++ List.replicate (64 * nb - n) 0x00) (i := 3)
      (by omega) hstate hwin' hlast
    rw [hdrop3] at hvpl
    rw [hsplit]
    exact validPrefix_three_cons_back hvpl
  · intro hvp
    have hL : ValidPrefix (ByteString.literal (bs ++ List.replicate (64 * nb - n) 0x00)) := by
      have h := hvp
      rw [hsplit] at h
      exact validPrefix_three_cons h
    constructor
    · intro m hm
      obtain ⟨t, hspans, htail⟩ := hL
      rcases htail with ht | hp
      · rw [ht] at hspans
        obtain ⟨hws, -, -⟩ := spans_ok hspans
          (List.replicate 3 (0x00 : UInt8) ++ bs ++ List.replicate (64 * nb - n) 0x00) 3
          (by rw [hdrop3]) (by omega) hstate.1 hstate.2
        have hm' : m < (ByteString.literal (bs ++ List.replicate (64 * nb - n) 0x00)).length
            - ByteString.empty.length := by
          rw [hlitlen, hzlen, hLlen]
          simpa using hm
        have := hws m hm'
        rwa [show 3 - 3 + m = m from by omega] at this
      · rcases hp with ⟨htne, b, c, r, hc, hltc, hp'⟩
        obtain ⟨k, hk⟩ := utf8Spans_literal_tail hspans
        have hklt : k < (bs ++ List.replicate (64 * nb - n) 0x00).length := by
          by_cases h : k < (bs ++ List.replicate (64 * nb - n) 0x00).length
          · exact h
          · exfalso
            have hnil : (bs ++ List.replicate (64 * nb - n) 0x00).drop k = [] :=
              List.drop_eq_nil_of_le (by omega)
            rw [hk, hnil] at htne
            exact htne rfl
        have htlen : t.length = (bs ++ List.replicate (64 * nb - n) 0x00).length - k := by
          rw [hk, ByteString.length_eq_size, ByteString.size_literal, List.length_drop]
        obtain ⟨hws, hc1, he1⟩ := spans_ok hspans
          (List.replicate 3 (0x00 : UInt8) ++ bs ++ List.replicate (64 * nb - n) 0x00) 3
          (by rw [hdrop3]) (by omega) hstate.1 hstate.2
        have hlk : (bs ++ List.replicate (64 * nb - n) 0x00).length - t.length = k := by
          rw [htlen]; omega
        by_cases hmk : m < k
        · have := hws m (by rw [hlitlen, hlk]; exact hmk)
          rwa [show 3 - 3 + m = m from by omega] at this
        · have ht_take : t = b.take t.length := by
            unfold HasPrefix at hp'
            rw [ByteString.drop_zero] at hp'
            exact hp'.symm
          have hk1 : 1 ≤ t.length := by
            rw [htlen]; omega
          have H1 : ByteString.literal
              ((List.replicate 3 (0x00 : UInt8) ++ bs ++ List.replicate (64 * nb - n) 0x00).drop (3 + k))
              = b.take t.length := by
            rw [hsplit, drop_three_cons, ← hk, ← ht_take]
          have hidx2 : 3 - 3 + ((bs ++ List.replicate (64 * nb - n) 0x00).length - t.length) + 1
              = 3 + k - 2 := by omega
          have hidx3 : 3 - 3 + ((bs ++ List.replicate (64 * nb - n) 0x00).length - t.length)
              = 3 + k - 3 := by omega
          have hidx4 : 3 - 3 + ((bs ++ List.replicate (64 * nb - n) 0x00).length - t.length) + 2
              = 3 + k - 1 := by omega
          have H2 : ¬ NeedsCont
              (klByte (List.replicate 3 (0x00 : UInt8) ++ bs ++ List.replicate (64 * nb - n) 0x00)
                (3 + k - 2))
              (klByte (List.replicate 3 (0x00 : UInt8) ++ bs ++ List.replicate (64 * nb - n) 0x00)
                (3 + k - 3)) := by
            have := hc1
            rw [hlitlen, hidx2, hidx3] at this
            exact this
          have H3 : IsCharEnd
              (klByte (List.replicate 3 (0x00 : UInt8) ++ bs ++ List.replicate (64 * nb - n) 0x00)
                (3 + k - 1)) := by
            have := he1
            rw [hlitlen, hidx4] at this
            exact this
          have hm' : m - k < t.length := by
            have hmlen : m < (bs ++ List.replicate (64 * nb - n) 0x00).length := by rw [hLlen]; exact hm
            rw [htlen]; omega
          have hcp := char_prefix_ok hc t.length hk1 hltc
            (List.replicate 3 (0x00 : UInt8) ++ bs ++ List.replicate (64 * nb - n) 0x00) (3 + k)
            H1 (by omega) H2 H3 (m - k) hm'
          rwa [show 3 + k - 3 + (m - k) = m from by omega] at hcp
    · rintro ⟨hn0, hmod, hb⟩
      have hpad : 64 * nb - n = 0 := pad_eq_zero_of_mod hnb hmod
      have hl_eq : (bs ++ List.replicate (64 * nb - n) 0x00) = bs := by rw [hpad]; simp
      have hlne : (bs ++ List.replicate (64 * nb - n) 0x00) ≠ [] := by
        intro h0
        apply hn0
        have hlen0 : (bs ++ List.replicate (64 * nb - n) 0x00).length = 0 := by rw [h0]; rfl
        rw [hLlen] at hlen0
        omega
      have hlast := not_klTailByte_last_of_validPrefix hlne hL
      rw [hl_eq] at hlast
      rw [hn] at hb
      exact hlast hb

theorem witness_C0_nonmultiple :
    (¬ klErrAll (List.replicate 3 0x00 ++ [0xC0] ++ List.replicate 63 0x00) 64) ∧
    (¬ ValidPrefix (ByteString.literal
      (List.replicate 3 0x00 ++ [0xC0] ++ List.replicate 63 0x00))) := by
  have hno : ¬ klErrAll (List.replicate 3 0x00 ++ [0xC0] ++ List.replicate 63 0x00) 64 := by
    intro h
    have hw := h 1 (by decide)
    unfold klErrWin at hw
    have he : klErrByte
        (klByte (List.replicate 3 0x00 ++ [0xC0] ++ List.replicate 63 0x00) 1)
        (klByte (List.replicate 3 0x00 ++ [0xC0] ++ List.replicate 63 0x00) 2)
        (klByte (List.replicate 3 0x00 ++ [0xC0] ++ List.replicate 63 0x00) 3)
        (klByte (List.replicate 3 0x00 ++ [0xC0] ++ List.replicate 63 0x00) 4) = 0x01 := by
      decide
    rw [he] at hw
    exact (by decide : (0x01 : UInt8) = 0 → False) hw
  refine ⟨hno, ?_⟩
  intro hvp
  exact hno ((klErrAll_window_iff [0xC0] 1 1 (by decide) (by decide)).mpr hvp).1

theorem witness_C0_block :
    (klErrAll (List.replicate 3 0x00 ++ (List.replicate 63 0x00 ++ [0xC0])) 64) ∧
    (klTailByte 0xC0 = true) ∧
    (¬ ValidPrefix (ByteString.literal
      (List.replicate 3 0x00 ++ (List.replicate 63 0x00 ++ [0xC0])))) := by
  have hwin : List.replicate 3 (0x00 : UInt8) ++ (List.replicate 63 0x00 ++ [0xC0])
      = List.replicate 66 0x00 ++ [0xC0] := by
    rw [← List.append_assoc]
    congr 1
  have hall : klErrAll (List.replicate 3 0x00 ++ (List.replicate 63 0x00 ++ [0xC0])) 64 := by
    intro t ht
    rw [hwin]
    unfold klErrWin
    by_cases h63 : t < 63
    · have hz : ∀ j, j < 66 → klByte (List.replicate 66 (0x00 : UInt8) ++ [0xC0]) j = 0x00 := by
        intro j hj
        rw [klByte_append_left (s := List.replicate 66 (0x00 : UInt8)) (t := [0xC0])
          (by simpa using hj)]
        exact klByte_replicate_zero 66 j
      rw [hz t (by omega), hz (t + 1) (by omega), hz (t + 2) (by omega), hz (t + 3) (by omega)]
      exact (by decide : klErrByte (0x00 : UInt8) 0x00 0x00 0x00 = 0x00)
    · have ht63 : t = 63 := by omega
      subst ht63
      have h63z : klByte (List.replicate 66 (0x00 : UInt8) ++ [0xC0]) 63 = 0x00 := by
        rw [klByte_append_left (s := List.replicate 66 (0x00 : UInt8)) (t := [0xC0]) (by decide)]
        exact klByte_replicate_zero 66 63
      have h64z : klByte (List.replicate 66 (0x00 : UInt8) ++ [0xC0]) 64 = 0x00 := by
        rw [klByte_append_left (s := List.replicate 66 (0x00 : UInt8)) (t := [0xC0]) (by decide)]
        exact klByte_replicate_zero 66 64
      have h65z : klByte (List.replicate 66 (0x00 : UInt8) ++ [0xC0]) 65 = 0x00 := by
        rw [klByte_append_left (s := List.replicate 66 (0x00 : UInt8)) (t := [0xC0]) (by decide)]
        exact klByte_replicate_zero 66 65
      have h66 : klByte (List.replicate 66 (0x00 : UInt8) ++ [0xC0]) 66 = 0xC0 := by
        rw [show (66 : Nat) = (List.replicate 66 (0x00 : UInt8)).length + 0 from by simp]
        exact klByte_append_right (List.replicate 66 (0x00 : UInt8)) [0xC0] 0
      rw [h63z, h64z, h65z, h66]
      decide
  refine ⟨hall, by decide, ?_⟩
  intro hvp
  have hL := (klErrAll_window_iff (List.replicate 63 0x00 ++ [0xC0]) 64 1 (by decide) (by decide)).mpr hvp
  exact hL.2 ⟨by decide, by decide, by decide⟩

end LeanLLVM.Vellum.JsonUtf8Spec
