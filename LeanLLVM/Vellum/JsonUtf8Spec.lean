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

## What is proved here

`klErrByte_eq_zero_iff` is C59: a position's error byte is zero exactly when the
four bytes around it are admissible in RFC 3629 §4's terms — `NeedsCont` (a lead
two or three bytes back still inside its character) and `KlPair` (the local
two-byte structure, clause for clause).  The decomposition the proof uses is
`err = sc ^ must`, then `must`'s single bit and `sc`'s table word; `sc` is decided
over `lo(p1) × hi(p1) × hi(c)`, which is 16 × 16 × 16 = 4096 table cases, once per
value of `NeedsCont`, so 2 × 4096 = 8192 decided cases.

The eight refused witnesses below are one per class the tables distinguish, and
the count is the table above's: eight.

The tables are the vendored header's bytes.  `tests/json-utf8/check.sh` compares
this module's three tables with `kl_t1`/`kl_t2`/`kl_t3` read out of
`kernel/json/measured/u8kl.h` by a compiled translation unit, so the values are
checked against the header rather than transcribed from it here.

Nothing here is about the emitted body: `utf8Calls` (`JsonUtf8IR.lean`) binds the
three intrinsics, and the refinement of the pinned body against `klStage` is
stated in `JsonUtf8IR.lean` and `JsonUtf8Steps.lean`, not here.
-/
import LeanLLVM.JSON.Utf8
import LeanLLVM.Vellum.BitLanes

namespace LeanLLVM.Vellum.JsonUtf8Spec

open LeanLLVM

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
exactly when the four bytes around it are admissible in RFC 3629 §4's terms: if a
lead two or three bytes back still owns the position (`NeedsCont`) then both it
and this byte are `UTF8-tail`s, and otherwise the two-byte structure `KlPair`
holds.

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

end LeanLLVM.Vellum.JsonUtf8Spec
