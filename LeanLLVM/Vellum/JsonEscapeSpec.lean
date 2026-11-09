/-
The escape unit's specification: the positions its list carries, and the decode
that consumes them.

Two predicates, both stated in the JSON model's own vocabulary rather than in
the emission's:

* `escapePositions` is the rule a position is a position by.  A byte inside a
  string contributes a position when it is a control byte or the first backslash
  of a run; the string state and the run parity come from `JsonScanSpec`'s
  `classStep` fold, and the same decision read at a lane is the classifier's
  backslash, control and in-string masks (`isEscapeLane_eq_masks`).  Nothing here
  names `xl_lanes`, its start arithmetic, or the batch that emits the positions,
  so a list built by that arithmetic can be judged against this rule without the
  rule restating it.

* `escapeDecode` is the body a position list decodes to: the bytes before each
  position copied verbatim, the escape at it replaced by what it stands for, or a
  refusal at the body-relative offset where the decoder stopped.  It is stated
  from RFC 8259 §7's escape productions and the code-unit arithmetic, not from
  `us_dec_x`'s control flow; the cursor the measured signature carries (`*xj`)
  and the refusal offset it writes (`*err`) are both outcomes here rather than
  prose.

`escapeCodePoints` is the bridge the model needs and the reason this module
exists.  The measured decoder writes **UTF-8 bytes**; `JSON.Value.string` stores
**code points**.  The two are related by `utf8Encode`, and the relation is a
theorem rather than a convention: `escapeCodePoints_encode` reads a code point
list back off its encoding, so the bytes a decode wrote can be compared with
`Value.string`'s payload instead of with a rendered form of it.

**One thing about that bridge is stated and one is owed.**  Stated: an unpaired
surrogate has no RFC 3629 encoding, and `utf8Encode_surrogate` says why — its
three-byte form's lead byte is `ED` and its second byte is at least `A0`, while
RFC 3629's only construction for a lead of `ED` admits at most `9F` there.  A JSON
text can give a lone surrogate a place only through a `\u` escape (RFC 8259 §8.2's
unpaired surrogate), which is exactly the case that makes the code-point bridge
this module's own relation rather than `Utf8Spans`.  Owed: that every *scalar* code
point's encoding is an RFC 3629 character in `Utf8Char`'s sense.  The reading
direction is what the records consume, and the case analysis that would place the
scalar encodings inside `Utf8Char` is not stated here.

What is not stated here either: the emitted body, its intrinsic environment, and
the records read at them.  This module states what the unit's answers must be, so
it is readable without the unit.
-/
import LeanLLVM.Vellum.JsonScanSpec
import LeanLLVM.JSON.Spec

namespace LeanLLVM.Vellum

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Vellum.JsonScanSpec

/-! ### The position rule

A position is a byte **inside a string** that is a control byte or the first
backslash of a run.  Both clauses are `JsonScanSpec`'s: the string state is
`inStringAfter` — the decision the in-string mask records at the lane — and the
run's parity is the carry's `oddRun`, so "first backslash of a run" is a
backslash whose run parity on entry is even. -/

/-- The lane at which a byte inside a string is an escape: a control byte, or the
first backslash of a run.  On a control byte and on a backslash the string state
does not change, so the `inStringAfter` read is the same as reading the state on
entry; both are the in-string mask's bit at the lane. -/
def IsEscapeLane (st : ClassState) (b : UInt8) : Bool :=
  inStringAfter st b && (IsControlB b || (IsBackslashB b && !st.oddRun))

/-- The escape positions of a run of bytes entered with a carry: the indices at
which `IsEscapeLane` holds, in increasing order. -/
def escapePositionsFrom (bs : List UInt8) (st : ClassState) : List Nat :=
  (List.range bs.length).filter fun k =>
    match bs[k]? with
    | some b => IsEscapeLane (classCarryAt bs st k) b
    | none => false

/-- A document's escape positions: the walk enters at the document's first byte,
outside a string and with an even backslash run. -/
def escapePositions (bs : List UInt8) : List Nat :=
  escapePositionsFrom bs ⟨false, false⟩

/-- A little-endian array of positions, one `w`-byte entry each: the bytes a
position stream occupies. -/
def positionsBytes (w : Nat) (ps : List Nat) : List UInt8 :=
  (ps.map fun p => natToBytes p w).flatten

/-- An unsigned word as the bytes a slot holds. -/
def wordBytes (w : Nat) (v : Nat) : List UInt8 := natToBytes v w

/-- The document offset of a block's first byte: the position base the list entry
point is given, `blk0 << 6`. -/
def blockAddr (blk0 : BitVec 64) : Nat := blk0.toNat * 64

/-- A landed lookup indexes the list. -/
theorem lt_length_of_getElem?_eq_some {bs : List UInt8} {k : Nat} {b : UInt8}
    (h : bs[k]? = some b) : k < bs.length := by
  rcases Nat.lt_or_ge k bs.length with hk | hk
  · exact hk
  · have hnone : bs[k]? = none := List.getElem?_eq_none hk
    rw [hnone] at h
    exact absurd h (by simp)

/-- A position is a byte inside a string that is a control byte or the first
backslash of a run. -/
theorem escapePositionsFrom_mem {bs : List UInt8} {st : ClassState} {k : Nat} :
    k ∈ escapePositionsFrom bs st ↔
      ∃ b, bs[k]? = some b ∧ IsEscapeLane (classCarryAt bs st k) b = true := by
  unfold escapePositionsFrom
  rw [List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hlt, hp⟩
    refine ⟨bs[k], List.getElem?_eq_getElem hlt, ?_⟩
    rw [List.getElem?_eq_getElem hlt] at hp
    exact hp
  · rintro ⟨b, hb, hp⟩
    refine ⟨lt_length_of_getElem?_eq_some hb, ?_⟩
    rw [hb]
    exact hp

/-- Every position is an index of the run it was read off. -/
theorem escapePositionsFrom_lt {bs : List UInt8} {st : ClassState} {k : Nat}
    (h : k ∈ escapePositionsFrom bs st) : k < bs.length := by
  obtain ⟨b, hb, _⟩ := escapePositionsFrom_mem.mp h
  exact lt_length_of_getElem?_eq_some hb

/-- A list is empty exactly when nothing is a member. -/
theorem eq_nil_iff_forall_not_mem {l : List Nat} : l = [] ↔ ∀ x, x ∉ l := by
  constructor
  · intro h x hx
    rw [h] at hx
    exact absurd hx (by simp)
  · intro h
    cases l with
    | nil => rfl
    | cons a as => exact absurd (h a (by simp)) (by simp)

/-- A run with no escape has no positions.  This is the direction that leaves the
suppressed arm's clause sayable without asserting anything about the document's
bytes: the suppressed arm claims the count is zero, never that this holds. -/
theorem escapePositionsFrom_eq_nil_iff {bs : List UInt8} {st : ClassState} :
    escapePositionsFrom bs st = [] ↔
      ∀ (k : Nat) (b : UInt8), bs[k]? = some b →
        IsEscapeLane (classCarryAt bs st k) b = false := by
  rw [eq_nil_iff_forall_not_mem]
  constructor
  · intro h k b hb
    cases hv : IsEscapeLane (classCarryAt bs st k) b with
    | false => rfl
    | true => exact absurd (escapePositionsFrom_mem.mpr ⟨b, hb, hv⟩) (h k)
  · intro h k hk
    obtain ⟨b, hb, hv⟩ := escapePositionsFrom_mem.mp hk
    rw [h k b hb] at hv
    exact absurd hv (by simp)

/-- **The position rule read at a lane of the classifier's masks.**  The
in-string mask restricts the lanes, the control mask supplies the control lanes,
and the backslash mask supplies the run starts; the carries are the same fold
`classCarryAt` in every term.  This is what makes the rule a statement about the
document rather than about a list the emission happened to build: the three words
are `JsonScanSpec`'s, and the position is decided by them. -/
theorem isEscapeLane_eq_masks {bs : List UInt8} {st : ClassState} {k : Nat} {b : UInt8}
    (hk : k < 32) (hb : bs[k]? = some b) :
    IsEscapeLane (classCarryAt bs st k) b =
      ((inStringMask bs st).getLsbD k &&
        ((controlMask bs st).getLsbD k ||
          ((backslashMask bs st).getLsbD k && !(classCarryAt bs st k).oddRun))) := by
  unfold IsEscapeLane
  rw [backslashMask_getLsbD hk hb, inStringMask_getLsbD hk hb, controlMask,
    maskOfListWith_getLsbD hk hb]

/-- The escape word the emission's arithmetic forms — the control and run-start
lanes, restricted to the in-string lanes — decides the same lane.  `xl_lanes`
returns `(ctl | e) & im` with `e` the run starts; the two readings agree at every
lane of a block. -/
theorem isEscapeLane_eq_escapeWord {bs : List UInt8} {st : ClassState} {k : Nat} {b : UInt8}
    (hk : k < 32) (hb : bs[k]? = some b) :
    (((controlMask bs st).getLsbD k ||
        ((backslashMask bs st).getLsbD k && !(classCarryAt bs st k).oddRun)) &&
      (inStringMask bs st).getLsbD k) =
      IsEscapeLane (classCarryAt bs st k) b := by
  rw [isEscapeLane_eq_masks hk hb]
  simp [Bool.and_comm]

/-! ### The escape productions

RFC 8259 §7's escape is a backslash and one byte, or `\u` and four hexadecimal
digits, with the surrogate pair the §7 note describes.  A two-character escape's
meaning is the table below; a `\u` escape's meaning is a code unit, encoded to
UTF-8 by `utf8Encode`. -/

/-- The byte a two-character escape stands for: the eight of RFC 8259 §7. -/
def simpleEscape (c : UInt8) : Option UInt8 :=
  if c = 0x22 then some 0x22      -- \"
  else if c = 0x5C then some 0x5C -- \\
  else if c = 0x2F then some 0x2F -- \/
  else if c = 0x62 then some 0x08 -- \b
  else if c = 0x66 then some 0x0C -- \f
  else if c = 0x6E then some 0x0A -- \n
  else if c = 0x72 then some 0x0D -- \r
  else if c = 0x74 then some 0x09 -- \t
  else none

/-- One hexadecimal digit's value, in either case. -/
def hexDigit (c : UInt8) : Option Nat :=
  if 0x30 ≤ c ∧ c ≤ 0x39 then some (c.toNat - 0x30)
  else if 0x41 ≤ c ∧ c ≤ 0x46 then some (c.toNat - 0x37)
  else if 0x61 ≤ c ∧ c ≤ 0x66 then some (c.toNat - 0x57)
  else none

/-- The code unit four hexadecimal digits spell: the digits at `k` through
`k+3`, most significant first.  A digit that is absent or not hexadecimal is a
refusal, which is the same answer the measured test gives and a shorter read. -/
def hex4 (bs : List UInt8) (k : Nat) : Option Nat :=
  match bs[k]?, bs[k + 1]?, bs[k + 2]?, bs[k + 3]? with
  | some d0, some d1, some d2, some d3 =>
      match hexDigit d0, hexDigit d1, hexDigit d2, hexDigit d3 with
      | some v0, some v1, some v2, some v3 =>
          some (v0 * 0x1000 + v1 * 0x100 + v2 * 0x10 + v3)
      | _, _, _, _ => none
  | _, _, _, _ => none

/-- A trailing byte of a UTF-8 sequence: `10xxxxxx`. -/
def IsUtf8Tail (b : UInt8) : Bool := decide (0x80 ≤ b) && decide (b ≤ 0xBF)

/-- The UTF-8 encoding of a code point, surrogates included.

A scalar code point's encoding is RFC 3629 §3's.  An unpaired surrogate's is the
three-byte form the measured encoder writes — the only encoding a JSON text can
give it, and not one RFC 3629 admits — which is why the bridge below is not
`Utf8Spans`. -/
def utf8Encode (cp : Nat) : List UInt8 :=
  if cp < 0x80 then
    [UInt8.ofNat cp]
  else if cp < 0x800 then
    [UInt8.ofNat (0xC0 + cp / 0x40), UInt8.ofNat (0x80 + cp % 0x40)]
  else if cp < 0x10000 then
    [UInt8.ofNat (0xE0 + cp / 0x1000), UInt8.ofNat (0x80 + (cp / 0x40) % 0x40),
     UInt8.ofNat (0x80 + cp % 0x40)]
  else
    [UInt8.ofNat (0xF0 + cp / 0x40000), UInt8.ofNat (0x80 + (cp / 0x1000) % 0x40),
     UInt8.ofNat (0x80 + (cp / 0x40) % 0x40), UInt8.ofNat (0x80 + cp % 0x40)]

/-- The pair rule of RFC 8259 §7's note and RFC 2781 §2.2: a high surrogate
(`D800`–`DBFF`) directly followed by a `\u` escape for a low surrogate
(`DC00`–`DFFF`) is one code point, `10000 + (hi - D800) * 400 + (lo - DC00)`, and it
consumes both escapes' twelve bytes.  Every other reading of a high surrogate is the
six-byte form of the first half on its own.

The answer is returned whole — the code point the pair spells and the twelve bytes —
and the six-byte fallback is `escapeAt`'s, which is why a pair whose second half is
absent or out of range needs no separate case here. -/
def surrogateTail (bs : List UInt8) (k cp : Nat) : Option (Nat × Nat) :=
  if 0xD800 ≤ cp ∧ cp ≤ 0xDBFF ∧ k + 12 ≤ bs.length ∧ bs[k + 6]? = some 0x5C ∧
      bs[k + 7]? = some 0x75 then
    match hex4 bs (k + 8) with
    | some lo =>
        if 0xDC00 ≤ lo ∧ lo ≤ 0xDFFF then
          some (0x10000 + (cp - 0xD800) * 0x400 + (lo - 0xDC00), 12)
        else none
    | none => none
  else none

/-- The escape at `k`: the bytes it stands for and the number of body bytes it
consumes.  `none` is a refusal at `k`, which the record reports at the offset
where it happened.

`k` is taken as a position, so `bs[k]` is the backslash; the rule does not test
it, because it is not this rule's to test — a position that is not a backslash is
a list that is not this body's positions, and the requirement that it is is one of
the decode's premisses rather than a clause here. -/
def escapeAt (bs : List UInt8) (k : Nat) : Option (List UInt8 × Nat) :=
  match bs[k + 1]? with
  | none => none
  | some c1 =>
      match simpleEscape c1 with
      | some b => some ([b], 2)
      | none =>
          if c1 = 0x75 then
            match hex4 bs (k + 2) with
            | none => none
            | some cp =>
                match surrogateTail bs k cp with
                | some (cp', adv) => some (utf8Encode cp', adv)
                | none => some (utf8Encode cp, 6)
          else none

/-! ### The decode

The body is walked once, with a byte cursor and a position cursor, and the
outcome carries both: the measured signature's `*xj` is the position cursor in and
out, and its return is the decoded length or the refusal marker.  A refusal is an
*outcome with an offset*, not an absence: `refused offset consumed` says where the
body stopped and how many positions the walk had taken, which is what `*err` and
`*xj` are written with. -/

/-- What a decode produces: the decoded bytes and the number of positions the walk
consumed, or a refusal at the body-relative offset where it stopped, with the
same cursor. -/
inductive EscapeOutcome where
  | decoded (bytes : List UInt8) (consumed : Nat) : EscapeOutcome
  | refused (offset : Nat) (consumed : Nat) : EscapeOutcome
deriving DecidableEq, Repr

/-- The walk: `i` is the next byte to copy, `k` the positions already consumed,
and `out` the decoded bytes so far.

A position at or past the body's end stops the walk; a control byte inside a
string is a refusal at its own offset (RFC 8259 §7 forbids it); an escape is
replaced by what it stands for and the byte cursor moves past it; and a surrogate
pair consumes one more position than it started with, because the second `\u` of
the pair is a position of its own.  Past the last position the rest of the body is
copied.

Nothing here requires the positions to be this body's escape positions, and the walk
is not claimed to mean anything for any other list: a list that is not is outside
every statement made at this specification, which is what the first clause of the
expander's record names. -/
def escapeDecodeGo (bs : List UInt8) (i k : Nat) : List Nat → List UInt8 → EscapeOutcome
  | [], out => .decoded (out ++ bs.drop i) k
  | q :: qs, out =>
      if bs.length ≤ q then .decoded (out ++ bs.drop i) k
      else
        match bs[q]? with
        | none => .decoded (out ++ bs.drop i) k
        | some b =>
            let out := out ++ (bs.drop i).take (q - i)
            if IsControlB b then .refused q (k + 1)
            else
              match escapeAt bs q with
              | none => .refused q (k + 1)
              | some (bytes, adv) =>
                  if adv = 12 then
                    match qs with
                    | [] => escapeDecodeGo bs (q + adv) (k + 2) [] (out ++ bytes)
                    | _ :: qs' => escapeDecodeGo bs (q + adv) (k + 2) qs' (out ++ bytes)
                  else escapeDecodeGo bs (q + adv) (k + 1) qs (out ++ bytes)

/-- A body decoded against its escape positions. -/
def escapeDecode (bs : List UInt8) (ps : List Nat) : EscapeOutcome :=
  escapeDecodeGo bs 0 0 ps []

/-! ### Reading a code point list off its encoding

The measured decoder writes UTF-8 bytes and the model stores code points, so the
two have to be related by a rule and not by a rendering.  `utf8Encode` is that
rule's writing direction and `decodeHead`/`escapeCodePoints` its reading
direction; `escapeCodePoints_encode` says the reading returns the list the writing
produced, which is what lets a decode's bytes be compared with the payload of
`JSON.Value.string`.
-/

/-- The value of a byte literal below `256`. -/
theorem toNat_ofNat_of_lt {n : Nat} (h : n < 256) : (UInt8.ofNat n).toNat = n := by
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt]
  omega

/-- A trailing byte of a UTF-8 sequence is `10xxxxxx`. -/
theorem isUtf8Tail_iff (b : UInt8) :
    IsUtf8Tail b = true ↔ (0x80 : Nat) ≤ b.toNat ∧ b.toNat ≤ 0xBF := by
  unfold IsUtf8Tail
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, UInt8.le_iff_toNat_le,
    UInt8.le_iff_toNat_le]
  have h80 : ((0x80 : UInt8)).toNat = 0x80 := by decide
  have hbf : ((0xBF : UInt8)).toNat = 0xBF := by decide
  rw [h80, hbf]

/-- The code point at the front of a byte string, and the bytes after its
encoding.  `none` when the bytes do not begin with an encoded code point. -/
def decodeHead (bs : List UInt8) : Option (Nat × List UInt8) :=
  match bs[0]? with
  | none => none
  | some b0 =>
      if b0 < 0x80 then some (b0.toNat, bs.drop 1)
      else if b0 < 0xC2 then none
      else if b0 < 0xE0 then
        match bs[1]? with
        | some b1 =>
            if IsUtf8Tail b1 then
              some ((b0.toNat - 0xC0) * 0x40 + (b1.toNat - 0x80), bs.drop 2)
            else none
        | none => none
      else if b0 < 0xF0 then
        match bs[1]?, bs[2]? with
        | some b1, some b2 =>
            if IsUtf8Tail b1 && IsUtf8Tail b2 then
              some ((b0.toNat - 0xE0) * 0x1000 + (b1.toNat - 0x80) * 0x40 +
                (b2.toNat - 0x80), bs.drop 3)
            else none
        | _, _ => none
      else if b0 < 0xF5 then
        match bs[1]?, bs[2]?, bs[3]? with
        | some b1, some b2, some b3 =>
            if IsUtf8Tail b1 && IsUtf8Tail b2 && IsUtf8Tail b3 then
              some ((b0.toNat - 0xF0) * 0x40000 + (b1.toNat - 0x80) * 0x1000 +
                (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80), bs.drop 4)
            else none
        | _, _, _ => none
      else none

/-- A byte from a value below `256` compares as the value does, against a
written-out literal. -/
theorem ofNat_lt_lit {n m : Nat} (hn : n < 256) (hm : m < 256) :
    (UInt8.ofNat n < (OfNat.ofNat m : UInt8)) ↔ n < m := by
  rw [UInt8.lt_iff_toNat_lt, toNat_ofNat_of_lt hn, UInt8.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]

/-- The same, non-strictly. -/
theorem ofNat_le_lit {n m : Nat} (hn : n < 256) (hm : m < 256) :
    (UInt8.ofNat n ≤ (OfNat.ofNat m : UInt8)) ↔ n ≤ m := by
  rw [UInt8.le_iff_toNat_le, toNat_ofNat_of_lt hn, UInt8.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]

/-- A written-out literal against a byte built from a value below `256`. -/
theorem lit_le_ofNat {n m : Nat} (hn : n < 256) (hm : m < 256) :
    ((OfNat.ofNat n : UInt8) ≤ UInt8.ofNat m) ↔ n ≤ m := by
  rw [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat, Nat.mod_eq_of_lt hn,
    UInt8.toNat_ofNat', Nat.mod_eq_of_lt hm]

/-- The encodings, at every range of a code point, in the form each is written. -/
theorem utf8Encode_eq_one {c : Nat} (h : c < 0x80) :
    utf8Encode c = [UInt8.ofNat c] := by
  unfold utf8Encode
  rw [if_pos h]

theorem utf8Encode_eq_two {c : Nat} (h0 : ¬ c < 0x80) (h1 : c < 0x800) :
    utf8Encode c = [UInt8.ofNat (0xC0 + c / 0x40), UInt8.ofNat (0x80 + c % 0x40)] := by
  unfold utf8Encode
  rw [if_neg h0, if_pos h1]

theorem utf8Encode_eq_three {c : Nat} (h0 : ¬ c < 0x80) (h1 : ¬ c < 0x800)
    (h2 : c < 0x10000) :
    utf8Encode c =
      [UInt8.ofNat (0xE0 + c / 0x1000), UInt8.ofNat (0x80 + (c / 0x40) % 0x40),
       UInt8.ofNat (0x80 + c % 0x40)] := by
  unfold utf8Encode
  rw [if_neg h0, if_neg h1, if_pos h2]

theorem utf8Encode_eq_four {c : Nat} (h0 : ¬ c < 0x80) (h1 : ¬ c < 0x800)
    (h2 : ¬ c < 0x10000) :
    utf8Encode c =
      [UInt8.ofNat (0xF0 + c / 0x40000), UInt8.ofNat (0x80 + (c / 0x1000) % 0x40),
       UInt8.ofNat (0x80 + (c / 0x40) % 0x40), UInt8.ofNat (0x80 + c % 0x40)] := by
  unfold utf8Encode
  rw [if_neg h0, if_neg h1, if_neg h2]

/-- An encoding is never empty. -/
theorem utf8Encode_length_pos (c : Nat) : 0 < (utf8Encode c).length := by
  by_cases h1 : c < 0x80
  · rw [utf8Encode_eq_one h1]; simp
  · by_cases h2 : c < 0x800
    · rw [utf8Encode_eq_two h1 h2]; simp
    · by_cases h3 : c < 0x10000
      · rw [utf8Encode_eq_three h1 h2 h3]; simp
      · rw [utf8Encode_eq_four h1 h2 h3]; simp

/-- A little-endian word read back from its bytes starts with them: the first
`bs.length` bytes of `natToBytes (bytesToNat bs) n` are `bs` when they fit. -/
theorem natToBytes_bytesToNat (bs : List UInt8) (n : Nat) (h : bs.length ≤ n) :
    (natToBytes (bytesToNat bs) n).take bs.length = bs := by
  induction bs generalizing n with
  | nil => simp
  | cons b bs ih =>
      cases n with
      | zero => simp at h
      | succ m =>
          have hb : b.toNat < 256 := b.toNat_lt
          have hdiv : (256 * bytesToNat bs + b.toNat) / 256 = bytesToNat bs := by
            rw [Nat.mul_add_div (by decide : 0 < 256), Nat.div_eq_of_lt hb, Nat.add_zero]
          have hmod : (256 * bytesToNat bs + b.toNat) % 256 = b.toNat := by
            rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hb]
          simp only [bytesToNat, natToBytes, hmod, hdiv, List.length_cons, Nat.add_comm]
          have hle : bs.length ≤ m := by simpa using h
          rw [List.take_succ_cons, ih m hle]
          simp

/-- An encoding is at most four bytes. -/
theorem utf8Encode_length_le_four (c : Nat) : (utf8Encode c).length ≤ 4 := by
  by_cases h1 : c < 0x80
  · rw [utf8Encode_eq_one h1]; simp
  · by_cases h2 : c < 0x800
    · rw [utf8Encode_eq_two h1 h2]; simp
    · by_cases h3 : c < 0x10000
      · rw [utf8Encode_eq_three h1 h2 h3]; simp
      · rw [utf8Encode_eq_four h1 h2 h3]; simp

/-- **The encoding, read out of a four-byte word.**  The little-endian word of an
encoding's bytes has that encoding as its first `(utf8Encode c).length` bytes.
This is the specification's side of the encoder's word; it names no emission
term. -/
theorem utf8Word_bytes (c : Nat) (h : c < 0x110000) :
    (natToBytes (bytesToNat (utf8Encode c)) 4).take (utf8Encode c).length =
      utf8Encode c :=
  natToBytes_bytesToNat (utf8Encode c) 4 (utf8Encode_length_le_four c)

/-- info: 'LeanLLVM.Vellum.natToBytes_bytesToNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms natToBytes_bytesToNat

/-- info: 'LeanLLVM.Vellum.utf8Encode_length_le_four' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms utf8Encode_length_le_four

/-- info: 'LeanLLVM.Vellum.utf8Word_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms utf8Word_bytes

/-- A list of code points is no longer than their encodings. -/
theorem flatten_length_ge (cps : List Nat) :
    cps.length ≤ (cps.map utf8Encode).flatten.length := by
  induction cps with
  | nil => simp
  | cons c cs ih =>
      simp only [List.map_cons, List.flatten_cons, List.length_cons, List.length_append]
      have := utf8Encode_length_pos c
      omega

/-- **The reading returns the list the writing produced.**  Every code point at or
below U+10FFFF, surrogates included, is read back off its encoding, and the rest
of the bytes follow it. -/
theorem decodeHead_encode (c : Nat) (hc : c ≤ 0x10FFFF) (rest : List UInt8) :
    decodeHead (utf8Encode c ++ rest) = some (c, rest) := by
  by_cases h1 : c < 0x80
  · rw [utf8Encode_eq_one h1]
    have hlt : UInt8.ofNat c < (0x80 : UInt8) := by
      rw [ofNat_lt_lit (by omega) (by decide)]; exact h1
    have hnat : (UInt8.ofNat c).toNat = c := toNat_ofNat_of_lt (by omega)
    simp only [List.cons_append, List.nil_append, decodeHead, List.getElem?_cons_zero,
      if_pos hlt, hnat]
    simp
  · by_cases h2 : c < 0x800
    · rw [utf8Encode_eq_two h1 h2]
      have hq : c / 0x40 < 0x20 := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]; omega
      have hq0 : 2 ≤ c / 0x40 := by
        rw [Nat.le_div_iff_mul_le (by decide)]; omega
      have htop : 0xC0 + c / 0x40 < 256 :=
        Nat.lt_trans (Nat.add_lt_add_left hq 0xC0) (by decide)
      have hlt0 : ¬ UInt8.ofNat (0xC0 + c / 0x40) < (0x80 : UInt8) := by
        rw [ofNat_lt_lit htop (by decide)]
        exact Nat.not_lt.mpr
          (Nat.le_trans (by decide : (0x80 : Nat) ≤ 0xC0) (Nat.le_add_right 0xC0 _))
      have hlt1 : ¬ UInt8.ofNat (0xC0 + c / 0x40) < (0xC2 : UInt8) := by
        rw [ofNat_lt_lit htop (by decide)]
        exact Nat.not_lt.mpr
          (Nat.le_trans (by decide : (0xC2 : Nat) ≤ 0xC0 + 2) (Nat.add_le_add_left hq0 0xC0))
      have hlt2 : UInt8.ofNat (0xC0 + c / 0x40) < (0xE0 : UInt8) := by
        rw [ofNat_lt_lit htop (by decide)]
        exact Nat.lt_of_lt_of_eq (Nat.add_lt_add_left hq 0xC0) (by decide)
      have htail : IsUtf8Tail (UInt8.ofNat (0x80 + c % 0x40)) = true := by
        rw [isUtf8Tail_iff, toNat_ofNat_of_lt (by omega)]
        have := Nat.mod_lt c (show 0 < 0x40 by decide)
        constructor <;> omega
      have hx : (UInt8.ofNat (0xC0 + c / 0x40)).toNat = 0xC0 + c / 0x40 :=
        toNat_ofNat_of_lt htop
      have hy : (UInt8.ofNat (0x80 + c % 0x40)).toNat = 0x80 + c % 0x40 :=
        toNat_ofNat_of_lt (by omega)
      have hcp : ((UInt8.ofNat (0xC0 + c / 0x40)).toNat - 0xC0) * 0x40 +
          ((UInt8.ofNat (0x80 + c % 0x40)).toNat - 0x80) = c := by
        rw [hx, hy, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left,
          Nat.mul_comm (c / 0x40) 0x40]
        exact Nat.div_add_mod c 0x40
      simp only [List.cons_append, List.nil_append, decodeHead, List.getElem?_cons_zero,
        List.getElem?_cons_succ, if_neg hlt0, if_neg hlt1, if_pos hlt2, if_pos htail, hcp]
      simp
    · by_cases h3 : c < 0x10000
      · rw [utf8Encode_eq_three h1 h2 h3]
        have hq : c / 0x1000 < 0x10 := by
          rw [Nat.div_lt_iff_lt_mul (by decide)]; omega
        have htop : 0xE0 + c / 0x1000 < 256 :=
          Nat.lt_trans (Nat.add_lt_add_left hq 0xE0) (by decide)
        have hlt0 : ¬ UInt8.ofNat (0xE0 + c / 0x1000) < (0x80 : UInt8) := by
          rw [ofNat_lt_lit htop (by decide)]
          exact Nat.not_lt.mpr
            (Nat.le_trans (by decide : (0x80 : Nat) ≤ 0xE0) (Nat.le_add_right 0xE0 _))
        have hlt1 : ¬ UInt8.ofNat (0xE0 + c / 0x1000) < (0xC2 : UInt8) := by
          rw [ofNat_lt_lit htop (by decide)]
          exact Nat.not_lt.mpr
            (Nat.le_trans (by decide : (0xC2 : Nat) ≤ 0xE0) (Nat.le_add_right 0xE0 _))
        have hlt2 : ¬ UInt8.ofNat (0xE0 + c / 0x1000) < (0xE0 : UInt8) := by
          rw [ofNat_lt_lit htop (by decide)]
          exact Nat.not_lt.mpr (Nat.le_add_right 0xE0 _)
        have hlt3 : UInt8.ofNat (0xE0 + c / 0x1000) < (0xF0 : UInt8) := by
          rw [ofNat_lt_lit htop (by decide)]
          exact Nat.lt_of_lt_of_eq (Nat.add_lt_add_left hq 0xE0) (by decide)
        have ht1 : IsUtf8Tail (UInt8.ofNat (0x80 + (c / 0x40) % 0x40)) = true := by
          rw [isUtf8Tail_iff, toNat_ofNat_of_lt (by omega)]
          have := Nat.mod_lt (c / 0x40) (show 0 < 0x40 by decide)
          constructor <;> omega
        have ht2 : IsUtf8Tail (UInt8.ofNat (0x80 + c % 0x40)) = true := by
          rw [isUtf8Tail_iff, toNat_ofNat_of_lt (by omega)]
          have := Nat.mod_lt c (show 0 < 0x40 by decide)
          constructor <;> omega
        have htail : (IsUtf8Tail (UInt8.ofNat (0x80 + (c / 0x40) % 0x40)) &&
            IsUtf8Tail (UInt8.ofNat (0x80 + c % 0x40))) = true := by
          rw [Bool.and_eq_true]; exact ⟨ht1, ht2⟩
        have hx : (UInt8.ofNat (0xE0 + c / 0x1000)).toNat = 0xE0 + c / 0x1000 :=
          toNat_ofNat_of_lt htop
        have hy : (UInt8.ofNat (0x80 + (c / 0x40) % 0x40)).toNat =
            0x80 + (c / 0x40) % 0x40 := toNat_ofNat_of_lt (by omega)
        have hz : (UInt8.ofNat (0x80 + c % 0x40)).toNat = 0x80 + c % 0x40 :=
          toNat_ofNat_of_lt (by omega)
        have hcp : ((UInt8.ofNat (0xE0 + c / 0x1000)).toNat - 0xE0) * 0x1000 +
            ((UInt8.ofNat (0x80 + (c / 0x40) % 0x40)).toNat - 0x80) * 0x40 +
            ((UInt8.ofNat (0x80 + c % 0x40)).toNat - 0x80) = c := by
          rw [hx, hy, hz, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left,
            Nat.add_sub_cancel_left]
          have e3 : c / 0x1000 = (c / 0x40) / 0x40 := by
            rw [Nat.div_div_eq_div_mul, show (0x40 : Nat) * 0x40 = 0x1000 from by decide]
          rw [e3]
          have e1 := Nat.div_add_mod c 0x40
          have e2 := Nat.div_add_mod (c / 0x40) 0x40
          omega
        simp only [List.cons_append, List.nil_append, decodeHead, List.getElem?_cons_zero,
          List.getElem?_cons_succ, if_neg hlt0, if_neg hlt1, if_neg hlt2, if_pos hlt3,
          if_pos htail, hcp]
        simp
      · rw [utf8Encode_eq_four h1 h2 h3]
        have hq : c / 0x40000 < 5 := by
          rw [Nat.div_lt_iff_lt_mul (by decide)]; omega
        have htop : 0xF0 + c / 0x40000 < 256 :=
          Nat.lt_trans (Nat.add_lt_add_left hq 0xF0) (by decide)
        have hlt0 : ¬ UInt8.ofNat (0xF0 + c / 0x40000) < (0x80 : UInt8) := by
          rw [ofNat_lt_lit htop (by decide)]
          exact Nat.not_lt.mpr
            (Nat.le_trans (by decide : (0x80 : Nat) ≤ 0xF0) (Nat.le_add_right 0xF0 _))
        have hlt1 : ¬ UInt8.ofNat (0xF0 + c / 0x40000) < (0xC2 : UInt8) := by
          rw [ofNat_lt_lit htop (by decide)]
          exact Nat.not_lt.mpr
            (Nat.le_trans (by decide : (0xC2 : Nat) ≤ 0xF0) (Nat.le_add_right 0xF0 _))
        have hlt2 : ¬ UInt8.ofNat (0xF0 + c / 0x40000) < (0xE0 : UInt8) := by
          rw [ofNat_lt_lit htop (by decide)]
          exact Nat.not_lt.mpr
            (Nat.le_trans (by decide : (0xE0 : Nat) ≤ 0xF0) (Nat.le_add_right 0xF0 _))
        have hlt3 : ¬ UInt8.ofNat (0xF0 + c / 0x40000) < (0xF0 : UInt8) := by
          rw [ofNat_lt_lit htop (by decide)]
          exact Nat.not_lt.mpr (Nat.le_add_right 0xF0 _)
        have hlt4 : UInt8.ofNat (0xF0 + c / 0x40000) < (0xF5 : UInt8) := by
          rw [ofNat_lt_lit htop (by decide)]
          exact Nat.lt_of_lt_of_eq (Nat.add_lt_add_left hq 0xF0) (by decide)
        have ht1 : IsUtf8Tail (UInt8.ofNat (0x80 + (c / 0x1000) % 0x40)) = true := by
          rw [isUtf8Tail_iff, toNat_ofNat_of_lt (by omega)]
          have := Nat.mod_lt (c / 0x1000) (show 0 < 0x40 by decide)
          constructor <;> omega
        have ht2 : IsUtf8Tail (UInt8.ofNat (0x80 + (c / 0x40) % 0x40)) = true := by
          rw [isUtf8Tail_iff, toNat_ofNat_of_lt (by omega)]
          have := Nat.mod_lt (c / 0x40) (show 0 < 0x40 by decide)
          constructor <;> omega
        have ht3 : IsUtf8Tail (UInt8.ofNat (0x80 + c % 0x40)) = true := by
          rw [isUtf8Tail_iff, toNat_ofNat_of_lt (by omega)]
          have := Nat.mod_lt c (show 0 < 0x40 by decide)
          constructor <;> omega
        have htail : (IsUtf8Tail (UInt8.ofNat (0x80 + (c / 0x1000) % 0x40)) &&
            IsUtf8Tail (UInt8.ofNat (0x80 + (c / 0x40) % 0x40)) &&
            IsUtf8Tail (UInt8.ofNat (0x80 + c % 0x40))) = true := by
          rw [Bool.and_eq_true, Bool.and_eq_true]; exact ⟨⟨ht1, ht2⟩, ht3⟩
        have hx : (UInt8.ofNat (0xF0 + c / 0x40000)).toNat = 0xF0 + c / 0x40000 :=
          toNat_ofNat_of_lt htop
        have hw : (UInt8.ofNat (0x80 + (c / 0x1000) % 0x40)).toNat =
            0x80 + (c / 0x1000) % 0x40 := toNat_ofNat_of_lt (by omega)
        have hy : (UInt8.ofNat (0x80 + (c / 0x40) % 0x40)).toNat =
            0x80 + (c / 0x40) % 0x40 := toNat_ofNat_of_lt (by omega)
        have hz : (UInt8.ofNat (0x80 + c % 0x40)).toNat = 0x80 + c % 0x40 :=
          toNat_ofNat_of_lt (by omega)
        have hcp : ((UInt8.ofNat (0xF0 + c / 0x40000)).toNat - 0xF0) * 0x40000 +
            ((UInt8.ofNat (0x80 + (c / 0x1000) % 0x40)).toNat - 0x80) * 0x1000 +
            ((UInt8.ofNat (0x80 + (c / 0x40) % 0x40)).toNat - 0x80) * 0x40 +
            ((UInt8.ofNat (0x80 + c % 0x40)).toNat - 0x80) = c := by
          rw [hx, hw, hy, hz, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left,
            Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
          have e4 : c / 0x40000 = (c / 0x1000) / 0x40 := by
            rw [Nat.div_div_eq_div_mul, show (0x1000 : Nat) * 0x40 = 0x40000 from by decide]
          have e5 : c / 0x1000 = (c / 0x40) / 0x40 := by
            rw [Nat.div_div_eq_div_mul, show (0x40 : Nat) * 0x40 = 0x1000 from by decide]
          rw [e4, e5]
          have e1 := Nat.div_add_mod c 0x40
          have e2 := Nat.div_add_mod (c / 0x40) 0x40
          have e3 := Nat.div_add_mod (c / 0x40 / 0x40) 0x40
          omega
        simp only [List.cons_append, List.nil_append, decodeHead, List.getElem?_cons_zero,
          List.getElem?_cons_succ, if_neg hlt0, if_neg hlt1, if_neg hlt2, if_neg hlt3,
          if_pos hlt4, if_pos htail, hcp]
        simp

/-- **A surrogate's bytes are not an RFC 3629 character.**  The encoding's lead
byte is `ED` and its second byte is at least `A0`; RFC 3629's only construction for
a lead of `ED` (`Utf8Char.three₂`) admits at most `9F` there.  The model admits the
surrogate reading — RFC 8259 §8.2's unpaired escape — which is why the code-point
bridge above is `utf8Encode`'s relation and not `Utf8Spans`. -/
theorem utf8Encode_surrogate {c : Nat} (hlo : 0xD800 ≤ c) (hhi : c ≤ 0xDFFF) :
    utf8Encode c =
        [UInt8.ofNat (0xE0 + c / 0x1000), UInt8.ofNat (0x80 + (c / 0x40) % 0x40),
         UInt8.ofNat (0x80 + c % 0x40)] ∧
      (UInt8.ofNat (0xE0 + c / 0x1000)).toNat = 0xED ∧
      (0xA0 : Nat) ≤ (UInt8.ofNat (0x80 + (c / 0x40) % 0x40)).toNat := by
  refine ⟨utf8Encode_eq_three (by omega) (by omega) (by omega), ?_, ?_⟩
  · rw [toNat_ofNat_of_lt (by omega)]
    have h1 : 0xD ≤ c / 0x1000 := by rw [Nat.le_div_iff_mul_le (by decide)]; omega
    have h2 : c / 0x1000 < 0xE := by rw [Nat.div_lt_iff_lt_mul (by decide)]; omega
    omega
  · rw [toNat_ofNat_of_lt (by omega)]
    have hq : 0x360 ≤ c / 0x40 := by rw [Nat.le_div_iff_mul_le (by decide)]; omega
    have hq' : c / 0x40 < 0x380 := by rw [Nat.div_lt_iff_lt_mul (by decide)]; omega
    have := Nat.mod_lt (c / 0x40) (by decide : 0 < 0x40)
    omega

/-- The reading, with the fuel the bytes themselves provide.  A code point's
encoding is at least one byte, so one byte per step of fuel is enough for every
code point of every list. -/
def escapeCodePointsGo : Nat → List UInt8 → List Nat → Option (List Nat)
  | 0, _, _ => none
  | _ + 1, [], acc => some acc.reverse
  | n + 1, bs, acc =>
      match decodeHead bs with
      | none => none
      | some (c, rest) => escapeCodePointsGo n rest (c :: acc)

/-- The code points a decoded body reads as. -/
def escapeCodePoints (bytes : List UInt8) : Option (List Nat) :=
  escapeCodePointsGo (bytes.length + 1) bytes []

/-- One step of the walk, at a byte string that has a head. -/
theorem escapeCodePointsGo_cons (n : Nat) (b : UInt8) (bs : List UInt8) (acc : List Nat) :
    escapeCodePointsGo (n + 1) (b :: bs) acc =
      match decodeHead (b :: bs) with
      | none => none
      | some (c, rest) => escapeCodePointsGo n rest (c :: acc) := rfl

/-- The reading of an encoding is the list that was encoded.  The fuel is more
than the list's length, which is what leaves the walk its last step on the empty
bytes. -/
theorem escapeCodePointsGo_encode (cps : List Nat)
    (h : ∀ c ∈ cps, c ≤ 0x10FFFF) :
    ∀ (acc : List Nat) (n : Nat), cps.length < n →
      escapeCodePointsGo n ((cps.map utf8Encode).flatten) acc =
        some (acc.reverse ++ cps) := by
  induction cps with
  | nil =>
      intro acc n hn
      match n with
      | 0 => simp at hn
      | k + 1 => simp [escapeCodePointsGo]
  | cons c cs ih =>
      intro acc n hn
      match n with
      | 0 => simp at hn
      | k + 1 =>
          have hc : c ≤ 0x10FFFF := h c (by simp)
          have hcs : ∀ c' ∈ cs, c' ≤ 0x10FFFF := fun c' hc' => h c' (by simp [hc'])
          rw [List.map_cons, List.flatten_cons]
          have hne : utf8Encode c ++ (cs.map utf8Encode).flatten ≠ [] := by
            intro hnil
            have hpos := utf8Encode_length_pos c
            have hlen : (utf8Encode c ++ (cs.map utf8Encode).flatten).length = 0 := by
              rw [hnil]; rfl
            rw [List.length_append] at hlen
            omega
          obtain ⟨b, bs', hbs⟩ := List.exists_cons_of_ne_nil hne
          have henc := decodeHead_encode c hc (cs.map utf8Encode).flatten
          rw [hbs] at henc ⊢
          rw [escapeCodePointsGo_cons, henc]
          dsimp only
          rw [ih hcs (c :: acc) k (by simp at hn ⊢; omega)]
          simp

/-- **The code-point bridge.**  A body carrying the encodings of a code point list
reads back as that list, which is what lets the bytes the decoder wrote be
compared with `JSON.Value.string`'s payload instead of with a rendered form of
it. -/
theorem escapeCodePoints_encode (cps : List Nat) (h : ∀ c ∈ cps, c ≤ 0x10FFFF) :
    escapeCodePoints ((cps.map utf8Encode).flatten) = some cps := by
  unfold escapeCodePoints
  have hlt : cps.length < ((cps.map utf8Encode).flatten).length + 1 := by
    have := flatten_length_ge cps; omega
  rw [escapeCodePointsGo_encode cps h [] (((cps.map utf8Encode).flatten).length + 1) hlt]
  simp

/-! ### The decode's length

Every form the decode writes is at most as long as the bytes its escape consumes, and
a body's escape positions are far enough apart that the copies do not overlap, so a
decode never writes more bytes than the body holds.  The second half is a hypothesis
here: `Spaced` names the spacing the bound uses — the cursor behind each position,
and the next position at least as far along as the bytes the escape consumed.  A
list that is this body's escape positions has it; a list that is not may not, and the
bound is false for such a list — `[0, 0, 0]` on `\n` writes three bytes over a
two-byte body — which is why the spacing is stated and not assumed. -/

/-- The spacing the length bound uses, one constructor per shape the walk takes at a
position: the cursor is behind the position, an escape's output fits in the bytes it
consumes and those bytes are inside the body, and the walk continues on the list it
really continues on, one entry dropped after a surrogate pair. -/
inductive Spaced (bs : List UInt8) : Nat → List Nat → Prop where
  /-- No positions left. -/
  | nil (i : Nat) : Spaced bs i []
  /-- A control byte: the walk refuses there, so it writes nothing further. -/
  | control (i q : Nat) (qs : List Nat) (b : UInt8) :
      i ≤ q → bs[q]? = some b → IsControlB b = true → Spaced bs i (q :: qs)
  /-- An escape that is not one: the walk refuses there too. -/
  | refuse (i q : Nat) (qs : List Nat) :
      i ≤ q → q < bs.length → escapeAt bs q = none → Spaced bs i (q :: qs)
  /-- A decoded escape: its output is no longer than the bytes it consumes, those
  bytes are inside the body, and the walk continues past them. -/
  | step (i q : Nat) (qs : List Nat) (adv : Nat) (bytes : List UInt8) (b : UInt8) :
      i ≤ q → bs[q]? = some b → IsControlB b = false → escapeAt bs q = some (bytes, adv) →
      bytes.length ≤ adv → q + adv ≤ bs.length →
      Spaced bs (q + adv) (if adv = 12 then qs.drop 1 else qs) → Spaced bs i (q :: qs)

/-- **A decode never writes more than the body holds.**  The quantity carried is
`written + (body length - cursor)`: a raw copy moves bytes from the second summand to
the first, and a decoded escape adds at most the bytes it consumes to the first while
removing exactly those from the second. -/
theorem escapeDecodeGo_length_le (bs : List UInt8) :
    ∀ {i : Nat} {ps : List Nat}, Spaced bs i ps →
      ∀ (pos : Nat) (out out' : List UInt8) (ks : Nat),
        escapeDecodeGo bs i pos ps out = .decoded out' ks →
        out'.length ≤ out.length + (bs.length - i) := by
  intro i ps hsp
  induction hsp with
  | nil i =>
      intro pos out out' ks hrun
      simp only [escapeDecodeGo] at hrun
      cases hrun
      simp only [List.length_append, List.length_drop]
      omega
  | control i q qs b hi hb hctl =>
      intro pos out out' ks hrun
      have hlt : q < bs.length := lt_length_of_getElem?_eq_some hb
      simp only [escapeDecodeGo, if_neg (show ¬ (bs.length ≤ q) from by omega), hb, hctl]
        at hrun
      exact absurd hrun (by simp)
  | refuse i q qs hi hlt href =>
      intro pos out out' ks hrun
      have hbq : bs[q]? = some bs[q] := List.getElem?_eq_getElem hlt
      simp only [escapeDecodeGo, if_neg (show ¬ (bs.length ≤ q) from by omega), hbq, href]
        at hrun
      split at hrun <;> simp_all
  | step i q qs adv bytes b hi hb hctl hesc hlen hadv ihsp ih =>
      intro pos out out' ks hrun
      have hlt : q < bs.length := lt_length_of_getElem?_eq_some hb
      have hcopy : ((bs.drop i).take (q - i)).length = q - i := by
        rw [List.length_take, List.length_drop]
        omega
      simp only [escapeDecodeGo, if_neg (show ¬ (bs.length ≤ q) from by omega), hb,
        if_neg (show ¬ (IsControlB b = true) from by rw [hctl]; simp), hesc] at hrun
      by_cases h12 : adv = 12
      · rw [if_pos h12] at hrun ih
        cases qs with
        | nil =>
            simp only [List.drop] at ih
            have hstep := ih (pos + 2) (out ++ (bs.drop i).take (q - i) ++ bytes) out' ks hrun
            simp only [List.length_append, hcopy] at hstep ⊢
            omega
        | cons q' qs' =>
            simp only [List.drop_succ_cons, List.drop_zero] at ih
            have hstep := ih (pos + 2) (out ++ (bs.drop i).take (q - i) ++ bytes) out' ks hrun
            simp only [List.length_append, hcopy] at hstep ⊢
            omega
      · rw [if_neg h12] at hrun ih
        have hstep := ih (pos + 1) (out ++ (bs.drop i).take (q - i) ++ bytes) out' ks hrun
        simp only [List.length_append, hcopy] at hstep ⊢
        omega

/-- A body decoded against its positions writes no more than the body holds, when the
positions are spaced as the body's own are. -/
theorem escapeDecode_length_le {bs : List UInt8} {ps : List Nat} (hsp : Spaced bs 0 ps)
    {out : List UInt8} {k : Nat} (h : escapeDecode bs ps = .decoded out k) :
    out.length ≤ bs.length := by
  have := escapeDecodeGo_length_le bs hsp 0 [] out k h
  simpa using this

/-! ### Fixtures for the rule -/

-- The backslash of a `\n` inside a string is a position; the quotes around it
-- are not.
#guard escapePositions [0x22, 0x5C, 0x6E, 0x22] = [1]

-- A raw control byte inside a string is a position.
#guard escapePositions [0x22, 0x01, 0x22] = [1]

-- The same byte outside a string is not.
#guard escapePositions [0x01] = []

-- The second backslash of a run is not a position: only a run's first is.
#guard escapePositions [0x22, 0x5C, 0x5C, 0x22] = [1]

/-! ### Fixtures for the reading -/

-- A four-byte code point reads back.
#guard escapeCodePoints [0xF0, 0x9F, 0x98, 0x80] = some [0x1F600]

-- A scalar reads back.
#guard escapeCodePoints [0x41] = some [0x41]

-- The empty body reads as no code points.
#guard escapeCodePoints [] = some []

-- A lone surrogate's three-byte form reads back as the surrogate code unit.
#guard escapeCodePoints [0xED, 0xA0, 0x80] = some [0xD800]

-- A continuation byte with no lead is not a code point.
#guard escapeCodePoints [0x80] = none

-- A truncated four-byte form is not a code point.
#guard escapeCodePoints [0xF0, 0x9F] = none

-- The surrogate's encoding, byte for byte.
#guard utf8Encode 0xD800 = [0xED, 0xA0, 0x80]

-- A scalar's encoding, byte for byte.
#guard utf8Encode 0x1F600 = [0xF0, 0x9F, 0x98, 0x80]

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Vellum.escapePositionsFrom_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapePositionsFrom_mem

/-- info: 'LeanLLVM.Vellum.isEscapeLane_eq_masks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms isEscapeLane_eq_masks

/-- info: 'LeanLLVM.Vellum.escapePositionsFrom_eq_nil_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapePositionsFrom_eq_nil_iff

/-- info: 'LeanLLVM.Vellum.decodeHead_encode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms decodeHead_encode

/-- info: 'LeanLLVM.Vellum.escapeCodePoints_encode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapeCodePoints_encode

/-- info: 'LeanLLVM.Vellum.utf8Encode_surrogate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms utf8Encode_surrogate

/-- info: 'LeanLLVM.Vellum.escapeDecodeGo_length_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapeDecodeGo_length_le

/-- info: 'LeanLLVM.Vellum.escapeDecode_length_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapeDecode_length_le

end LeanLLVM.Vellum
