/-
The semantics: RFC 8259's grammar as an inductive relation over bytes, and our
character restriction as a separate predicate.

Nothing in this module mentions a parser, a scanner, a token, a span, a tape or
a limit.  That is what makes the accepted language a definition rather than a
description of whatever the parser happens to do: the parser is proved against
this relation in `LeanLLVM/JSON/Correct.lean`, and only there.
-/
import LeanLLVM.JSON.Bytes
import LeanLLVM.JSON.Utf8

namespace LeanLLVM.JSON

open ByteString

/-- The logical JSON value.  Strings are lists of Unicode code points rather than
Lean `String`s: the policy is about code points, and rendering to `String` is a
separate, unproved view.  `RfcText` accepts a reading whose list can contain a
surrogate code unit (§8.2's unpaired escape); every reading that satisfies
`Policy` is scalar-only, and every accepted document is therefore scalar-only.
Numbers keep their exact source lexeme.  Object members are ordered and may
repeat a key. -/
inductive Value where
  | null : Value
  | bool (b : Bool) : Value
  | string (codePoints : List Nat) : Value
  | number (lexeme : Bytes) : Value
  | array (elems : List Value) : Value
  | object (members : List (List Nat × Value)) : Value
deriving Repr

/-! ### Decidable equality

`deriving DecidableEq` does not support nested inductive types in this Lean
version, so equality is written out.  The comparison is a structural recursion
that returns the decision itself — no Boolean specification to prove — so the
instance is computable and the `#guard` fixtures can evaluate it.
-/

mutual
/-- Structural equality on values and their lists. -/
def Value.decEq : (a b : Value) → Decidable (a = b)
  | .null, .null => isTrue rfl
  | .bool a, .bool b =>
      if h : a = b then isTrue (by rw [h])
      else isFalse (by intro h2; injection h2 with h3; exact h h3)
  | .string a, .string b =>
      if h : a = b then isTrue (by rw [h])
      else isFalse (by intro h2; injection h2 with h3; exact h h3)
  | .number a, .number b =>
      if h : a = b then isTrue (by rw [h])
      else isFalse (by intro h2; injection h2 with h3; exact h h3)
  | .array a, .array b =>
      match elemsDecEq a b with
      | isTrue h => isTrue (by rw [h])
      | isFalse h => isFalse (by intro h2; injection h2 with h3; exact h h3)
  | .object a, .object b =>
      match membersDecEq a b with
      | isTrue h => isTrue (by rw [h])
      | isFalse h => isFalse (by intro h2; injection h2 with h3; exact h h3)
  | .null, .bool _ => isFalse (by intro h; cases h)
  | .null, .string _ => isFalse (by intro h; cases h)
  | .null, .number _ => isFalse (by intro h; cases h)
  | .null, .array _ => isFalse (by intro h; cases h)
  | .null, .object _ => isFalse (by intro h; cases h)
  | .bool _, .null => isFalse (by intro h; cases h)
  | .bool _, .string _ => isFalse (by intro h; cases h)
  | .bool _, .number _ => isFalse (by intro h; cases h)
  | .bool _, .array _ => isFalse (by intro h; cases h)
  | .bool _, .object _ => isFalse (by intro h; cases h)
  | .string _, .null => isFalse (by intro h; cases h)
  | .string _, .bool _ => isFalse (by intro h; cases h)
  | .string _, .number _ => isFalse (by intro h; cases h)
  | .string _, .array _ => isFalse (by intro h; cases h)
  | .string _, .object _ => isFalse (by intro h; cases h)
  | .number _, .null => isFalse (by intro h; cases h)
  | .number _, .bool _ => isFalse (by intro h; cases h)
  | .number _, .string _ => isFalse (by intro h; cases h)
  | .number _, .array _ => isFalse (by intro h; cases h)
  | .number _, .object _ => isFalse (by intro h; cases h)
  | .array _, .null => isFalse (by intro h; cases h)
  | .array _, .bool _ => isFalse (by intro h; cases h)
  | .array _, .string _ => isFalse (by intro h; cases h)
  | .array _, .number _ => isFalse (by intro h; cases h)
  | .array _, .object _ => isFalse (by intro h; cases h)
  | .object _, .null => isFalse (by intro h; cases h)
  | .object _, .bool _ => isFalse (by intro h; cases h)
  | .object _, .string _ => isFalse (by intro h; cases h)
  | .object _, .number _ => isFalse (by intro h; cases h)
  | .object _, .array _ => isFalse (by intro h; cases h)

def elemsDecEq : (as bs : List Value) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
  | a :: as, b :: bs =>
      match Value.decEq a b with
      | isTrue h1 =>
          match elemsDecEq as bs with
          | isTrue h2 => isTrue (by rw [h1, h2])
          | isFalse h2 => isFalse (by intro h; injection h with h3 h4; exact h2 h4)
      | isFalse h1 =>
          isFalse (by intro h; injection h with h3 h4; exact h1 h3)

def membersDecEq : (as bs : List (List Nat × Value)) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
  | (ka, va) :: as, (kb, vb) :: bs =>
      match decEq ka kb with
      | isTrue hk =>
          match Value.decEq va vb with
          | isTrue hv =>
              match membersDecEq as bs with
              | isTrue hs => isTrue (by rw [hk, hv, hs])
              | isFalse hs =>
                  isFalse (by intro h; injection h with h1 h2; exact hs h2)
          | isFalse hv =>
              isFalse (by
                intro h; injection h with h1 h2
                injection h1 with h3 h4; exact hv h4)
      | isFalse hk =>
          isFalse (by
            intro h; injection h with h1 h2
            injection h1 with h3 h4; exact hk h3)
end

instance : DecidableEq Value := Value.decEq

/-! ### The two measures the limits are stated against

Both are structural recursions over the value and its lists; neither is a
theorem, and `parseRef_complete`'s hypotheses are their only consumers. -/

mutual
/-- Container nesting depth: a scalar is `0`, a container is one more than its
deepest child, so `[]` is `1` and `[[[1]]]` is `3`.  This is the quantity
`parseValue`'s `depth` counter is compared with: entering a container requires
`depth ≠ 0` and passes `depth - 1` to its children. -/
def Value.depth : Value → Nat
  | .null => 0
  | .bool _ => 0
  | .string _ => 0
  | .number _ => 0
  | .array es => 1 + elemsDepth es
  | .object ms => 1 + membersDepth ms

def elemsDepth : List Value → Nat
  | [] => 0
  | e :: es => max (Value.depth e) (elemsDepth es)

def membersDepth : List (List Nat × Value) → Nat
  | [] => 0
  | m :: ms => max (Value.depth m.2) (membersDepth ms)
end

mutual
/-- The number of tape tokens a document for this value produces.  It depends on
the value's shape only — spans and lexemes do not change it — so the capacity
limit is a bound on the value.  `[1,2]` is five tokens; `{"a":1}` is five;
`[[1]]` is five. -/
def Value.tokenCount : Value → Nat
  | .null => 1
  | .bool _ => 1
  | .string _ => 1
  | .number _ => 1
  | .array [] => 2
  | .array (e :: es) => 2 + Value.tokenCount e + elemsCount es
  | .object [] => 2
  | .object ((_, v) :: ms) => 2 + (Value.tokenCount v + 2) + membersCount ms

def elemsCount : List Value → Nat
  | [] => 0
  | e :: es => Value.tokenCount e + 1 + elemsCount es

def membersCount : List (List Nat × Value) → Nat
  | [] => 0
  | (_, v) :: ms => Value.tokenCount v + 3 + membersCount ms
end

mutual
/-- Every code point of every member name and string value is allowed by RFC 7493
§2.1.  This is the character half of that profile, and it is the whole of
`Policy`. -/
def Value.charPolicy : Value → Prop
  | .null => True
  | .bool _ => True
  | .number _ => True
  | .string cs => ∀ c ∈ cs, CharAllowed c
  | .array es => ∀ e ∈ es, e.charPolicy
  | .object ms => membersPolicy ms

/-- The member lists' half of `Value.charPolicy`.  It is a separate function
because the member branch reads a pair projection, which the structural
recursion cannot see through inline. -/
def membersPolicy : List (List Nat × Value) → Prop
  | [] => True
  | (k, v) :: ms => (∀ c ∈ k, CharAllowed c) ∧ v.charPolicy ∧ membersPolicy ms
end

/-- `membersPolicy` is the `∀ m ∈ ms` reading of the object branch: the same
proposition, stated in the form the clause map cites. -/
theorem membersPolicy_iff (ms : List (List Nat × Value)) :
    membersPolicy ms ↔
      ∀ m ∈ ms, (∀ c ∈ m.1, CharAllowed c) ∧ m.2.charPolicy := by
  induction ms with
  | nil => simp [membersPolicy]
  | cons m ms ih =>
      obtain ⟨k, v⟩ := m
      simp only [membersPolicy, List.mem_cons, forall_eq_or_imp, ih]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, h2, h3⟩

/-! `Value.charPolicy` and `membersPolicy` are compiled from one mutual recursion
and are `@[irreducible]`, so the equation a branch needs is not available by
reduction.  The six lemmas below state those equations in the direction a proof
consumes them. -/

/-- A null is allowed: `charPolicy` has nothing to check. -/
theorem charPolicy_null : (Value.null).charPolicy := by simp [Value.charPolicy]

/-- A boolean is allowed: `charPolicy` has nothing to check. -/
theorem charPolicy_bool (b : Bool) : (Value.bool b).charPolicy := by
  simp [Value.charPolicy]

/-- A number is allowed: its lexeme is not a code-point list, so the policy has
nothing to check. -/
theorem charPolicy_number (lex : Bytes) : (Value.number lex).charPolicy := by
  simp [Value.charPolicy]

/-- The string branch, in the form the code points are consumed with. -/
theorem charPolicy_string (cs : List Nat) :
    (Value.string cs).charPolicy ↔ ∀ c ∈ cs, CharAllowed c := by
  simp [Value.charPolicy]

/-- The array branch, in the form the elements are consumed with. -/
theorem charPolicy_array (vs : List Value) :
    (Value.array vs).charPolicy ↔ ∀ v ∈ vs, v.charPolicy := by
  simp [Value.charPolicy]

/-- The object branch: the policy descends to `membersPolicy`, which
`membersPolicy_iff` reads as a `∀ m ∈ ms`. -/
theorem charPolicy_object (ms : List (List Nat × Value)) :
    (Value.object ms).charPolicy ↔ membersPolicy ms := by
  simp [Value.charPolicy]

/-! ### Number productions

RFC 8259 §6, with the ABNF's own production names as clause docstrings. -/

/-- `1*DIGIT` -/
inductive Digits : Bytes → Prop where
  | one {b : UInt8} (h : IsDigitB b = true) : Digits (b +: empty)
  | more {b : UInt8} {bs : Bytes} (h : IsDigitB b = true) (hr : Digits bs) :
      Digits (b +: bs)

/-- `*DIGIT`: the zero-or-more digit tail RFC 8259 §6's `int` production carries
(`digit1-9 *DIGIT`).  Distinct from `Digits` so the `1*DIGIT` uses above stay
`1*DIGIT`. -/
inductive Digits0 : Bytes → Prop where
  | nil : Digits0 empty
  | more {b : UInt8} {bs : Bytes} (h : IsDigitB b = true) (hr : Digits0 bs) :
      Digits0 (b +: bs)

/-- `int = zero / ( digit1-9 *DIGIT )`.  The tail is `*DIGIT`, so a one-digit
`int` such as `1` has a derivation. -/
inductive IntPart : Bytes → Prop where
  | zero : IntPart (0x30 +: empty)
  | lead {b : UInt8} {bs : Bytes} (h1 : 0x31 ≤ b) (h2 : b ≤ 0x39)
      (hr : Digits0 bs) : IntPart (b +: bs)

/-- `exp = e [ minus / plus ] 1*DIGIT`, with `e = %x65 / %x45` -/
inductive ExpPart : Bytes → Prop where
  | mk {e : UInt8} {sign ds : Bytes} (he : e = 0x65 ∨ e = 0x45)
      (hs : sign = empty ∨ sign = (0x2B +: empty) ∨ sign = (0x2D +: empty))
      (hd : Digits ds) :
      ExpPart (e +: (sign ++ ds))

/-- `[ frac ] [ exp ]` applied to an `int`: the four shapes of §6's `number`
without its optional `minus`. -/
inductive NumBody : Bytes → Prop where
  | plain {ip : Bytes} (h : IntPart ip) : NumBody ip
  | frac {ip fs : Bytes} (hi : IntPart ip) (hf : Digits fs) :
      NumBody (ip ++ (0x2E +: fs))
  | exp {ip es : Bytes} (hi : IntPart ip) (he : ExpPart es) : NumBody (ip ++ es)
  | fracExp {ip fs es : Bytes} (hi : IntPart ip) (hf : Digits fs)
      (he : ExpPart es) : NumBody (ip ++ (0x2E +: fs) ++ es)

/-- `number = [ minus ] int [ frac ] [ exp ]` -/
inductive RfcNumber : Bytes → Prop where
  | pos {b : Bytes} (h : NumBody b) : RfcNumber b
  | neg {b : Bytes} (h : NumBody b) : RfcNumber (0x2D +: b)

/-- `bs[i…j)` is a JSON number lexeme.  The `i ≤ j` conjunct is what keeps the
empty range out, and the lexeme is a function of the range. -/
def NumberAt (bs : Bytes) (i j : Nat) : Prop :=
  i ≤ j ∧ RfcNumber ((bs.drop i).take (j - i))

/-! ### String productions

RFC 8259 §7; RFC 3629 for the encoding; RFC 7493 §2.1 for the mode. -/

/-- The two-character escapes of §7 and the code point each denotes. -/
def EscVal (b : UInt8) : Option Nat :=
  match b with
  | 0x22 => some 0x22   -- \"
  | 0x5C => some 0x5C   -- reverse solidus
  | 0x2F => some 0x2F   -- \/
  | 0x62 => some 0x08   -- \b
  | 0x66 => some 0x0C   -- \f
  | 0x6E => some 0x0A   -- \n
  | 0x72 => some 0x0D   -- \r
  | 0x74 => some 0x09   -- \t
  | _ => none

/-- The character policy a reading is held to.  `rfc` imposes none — RFC 8259's
grammar has no character restriction beyond §7's `unescaped` ranges.  `strict` is
RFC 7493 §2.1, which `Policy` selects. -/
inductive Strictness where
  | rfc
  | strict
deriving DecidableEq, Repr

def ModeAllows : Strictness → Nat → Prop
  | .rfc, _ => True
  | .strict, c => CharAllowed c

instance (m : Strictness) (n : Nat) : Decidable (ModeAllows m n) := by
  unfold ModeAllows
  cases m <;> infer_instance

/-- One string character, per RFC 8259 §7.  Raw characters are `unescaped`:
a `UTF8-char` whose code point is in `%x20-21 / %x23-5B / %x5D-10FFFF`, i.e. not
`"`, not the reverse solidus, and not a control character.  A high-surrogate
escape followed by a low-surrogate escape is one code point (§7's 12-character
sequence); an unpaired surrogate escape is its code unit, which §8.2 says the
ABNF admits and which only the `rfc` mode derives.
The mode hypothesis sits on the character, not on the production, so `rfc` and
`strict` differ in exactly one place per clause. -/
inductive StrChar (m : Strictness) : Bytes → Nat → Bytes → Prop where
  /-- `unescaped = %x20-21 / %x23-5B / %x5D-10FFFF`, transported as UTF-8 -/
  | unescaped {b : Bytes} {c : Nat} {rest : Bytes} (h : Utf8Char b c rest)
      (hctrl : 0x20 ≤ c) (hq : c ≠ 0x22) (hb : c ≠ 0x5C) (hm : ModeAllows m c) :
      StrChar m b c rest
  /-- `escape ( %x22 / %x5C / %x2F / %x62 / %x66 / %x6E / %x72 / %x74 )` -/
  | short {e : UInt8} {c : Nat} {rest : Bytes} (h : EscVal e = some c) :
      StrChar m (0x5C +: e +: rest) c rest
  /-- `%x75 4HEXDIG` whose digits denote a scalar -/
  | escU {h0 h1 h2 h3 : UInt8} {c : Nat} {rest : Bytes}
      (hx : Hex4 h0 h1 h2 h3 = some c) (hs : IsScalar c)
      (hm : ModeAllows m c) :
      StrChar m (0x5C +: 0x75 +: h0 +: h1 +: h2 +: h3 +: rest) c rest
  /-- §7's surrogate-pair rule: a high and a low escape denote one code point -/
  | escPair {h0 h1 h2 h3 l0 l1 l2 l3 : UInt8} {hi lo c : Nat} {rest : Bytes}
      (hhi : Hex4 h0 h1 h2 h3 = some hi) (hlo : Hex4 l0 l1 l2 l3 = some lo)
      (hh : IsHighSurrogate hi) (hl : IsLowSurrogate lo)
      (hc : c = 0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00))
      (hm : ModeAllows m c) :
      StrChar m (0x5C +: 0x75 +: h0 +: h1 +: h2 +: h3 +: 0x5C +: 0x75 +:
        l0 +: l1 +: l2 +: l3 +: rest) c rest
  /-- §8.2's case: an unpaired `\u` escape denotes its code unit, and only the
  RFC grammar derives it -/
  | escLone {h0 h1 h2 h3 : UInt8} {c : Nat} {rest : Bytes}
      (hm : m = .rfc) (hx : Hex4 h0 h1 h2 h3 = some c) (hs : ¬ IsScalar c) :
      StrChar m (0x5C +: 0x75 +: h0 +: h1 +: h2 +: h3 +: rest) c rest

/-- `string = quotation-mark *char quotation-mark`.  The base case matches the
closing quote, so the remainder is what follows the literal and a body cannot
contain a raw quote. -/
inductive StrChars (m : Strictness) : Bytes → List Nat → Bytes → Prop where
  | nil {rest : Bytes} : StrChars m (0x22 +: rest) [] rest
  | cons {b : Bytes} {c : Nat} {mid rest : Bytes} {cs : List Nat}
      (h : StrChar m b c mid) (hr : StrChars m mid cs rest) :
      StrChars m b (c :: cs) rest

/-- `bs[i…j)` is one JSON string literal whose body reads as `cs`. -/
def StringAt (m : Strictness) (bs : Bytes) (i j : Nat) (cs : List Nat) : Prop :=
  bs[i]? = some 0x22 ∧
    ∃ rest : Bytes, StrChars m (bs.drop (i + 1)) cs rest ∧ bs.drop j = rest

/-! ### Container productions

The six structural characters are §2's production names with `ws` on both sides;
each clause below cites one.  `ValueAt` is parameterised by the mode because its
string clause is. -/

mutual

/-- RFC 8259 §2's grammar on a byte list and two indices: `ValueAt m bs i v j`
holds when `bs[i…j)` spells the value `v` in mode `m`.  Nothing here mentions a
parser, a tape or a limit. -/
inductive ValueAt (m : Strictness) (bs : Bytes) : Nat → Value → Nat → Prop where
  /-- §3 `null = %x6e.75.6c.6c` -/
  | null {i : Nat} (h : HasPrefix bs i (literal [0x6E, 0x75, 0x6C, 0x6C])) :
      ValueAt m bs i .null (i + 4)
  /-- §3 `true = %x74.72.75.65` -/
  | true {i : Nat} (h : HasPrefix bs i (literal [0x74, 0x72, 0x75, 0x65])) :
      ValueAt m bs i (.bool true) (i + 4)
  /-- §3 `false = %x66.61.6c.73.65` -/
  | false {i : Nat} (h : HasPrefix bs i (literal [0x66, 0x61, 0x6C, 0x73, 0x65])) :
      ValueAt m bs i (.bool false) (i + 5)
  /-- §6 `number` -/
  | number {i j : Nat} (h : NumberAt bs i j) :
      ValueAt m bs i (.number ((bs.drop i).take (j - i))) j
  /-- §7 `string` -/
  | string {i j : Nat} {cs : List Nat} (h : StringAt m bs i j cs) :
      ValueAt m bs i (.string cs) j
  /-- §2 `begin-array = ws %x5B ws` … `end-array = ws %x5D ws` -/
  | array {i k : Nat} {vs : List Value} (hl : bs[i]? = some 0x5B)
      (hb : ArrBody m bs (skipFrom bs (i + 1)) vs k) (hr : bs[k]? = some 0x5D) :
      ValueAt m bs i (.array vs) (k + 1)
  /-- §2 `begin-object = ws %x7B ws` … `end-object = ws %x7D ws` -/
  | object {i k : Nat} {ms : List (List Nat × Value)} (hl : bs[i]? = some 0x7B)
      (hb : ObjBody m bs (skipFrom bs (i + 1)) ms k) (hr : bs[k]? = some 0x7D) :
      ValueAt m bs i (.object ms) (k + 1)

/-- §5 `array = begin-array [ value *( value-separator value ) ] end-array` -/
inductive ArrBody (m : Strictness) (bs : Bytes) : Nat → List Value → Nat → Prop where
  | empty {i : Nat} (h : bs[i]? = some 0x5D) : ArrBody m bs i [] i
  | elems {i k : Nat} {vs : List Value} (he : Elems m bs i vs k)
      (h : bs[k]? = some 0x5D) : ArrBody m bs i vs k

/-- The elements, ending at the whitespace before the closing bracket.  A
trailing `value-separator` has no derivation. -/
inductive Elems (m : Strictness) (bs : Bytes) : Nat → List Value → Nat → Prop where
  | last {i j k : Nat} {v : Value} (hv : ValueAt m bs i v j) (hw : SpaceAt bs j k) :
      Elems m bs i [v] k
  | cons {i j1 j2 j3 j4 : Nat} {v : Value} {vs : List Value}
      (hv : ValueAt m bs i v j1) (hw1 : SpaceAt bs j1 j2) (hc : bs[j2]? = some 0x2C)
      (hw2 : SpaceAt bs (j2 + 1) j3) (hr : Elems m bs j3 vs j4) :
      Elems m bs i (v :: vs) j4

/-- §4 `member = string name-separator value` -/
inductive Member (m : Strictness) (bs : Bytes) : Nat → (List Nat × Value) → Nat → Prop where
  | mk {i j1 j2 j3 j4 : Nat} {cs : List Nat} {v : Value}
      (hk : StringAt m bs i j1 cs) (hw1 : SpaceAt bs j1 j2)
      (hc : bs[j2]? = some 0x3A) (hw2 : SpaceAt bs (j2 + 1) j3)
      (hv : ValueAt m bs j3 v j4) : Member m bs i (cs, v) j4

/-- The members, in source order.  Nothing compares names: `SHOULD` uniqueness is
the RFC's, and RFC 7493 §2.3's `MUST NOT` is not adopted. -/
inductive Members (m : Strictness) (bs : Bytes) : Nat → List (List Nat × Value) → Nat → Prop where
  | last {i j k : Nat} {mem : List Nat × Value} (hm : Member m bs i mem j)
      (hw : SpaceAt bs j k) : Members m bs i [mem] k
  | cons {i j1 j2 j3 j4 : Nat} {mem : List Nat × Value}
      {ms : List (List Nat × Value)} (hm : Member m bs i mem j1)
      (hw1 : SpaceAt bs j1 j2) (hc : bs[j2]? = some 0x2C)
      (hw2 : SpaceAt bs (j2 + 1) j3) (hr : Members m bs j3 ms j4) :
      Members m bs i (mem :: ms) j4

/-- §4 `object = begin-object [ member *( value-separator member ) ] end-object` -/
inductive ObjBody (m : Strictness) (bs : Bytes) : Nat → List (List Nat × Value) → Nat → Prop where
  | empty {i : Nat} (h : bs[i]? = some 0x7D) : ObjBody m bs i [] i
  | members {i k : Nat} {ms : List (List Nat × Value)}
      (hm : Members m bs i ms k) (h : bs[k]? = some 0x7D) : ObjBody m bs i ms k

end

/-- §2 `JSON-text = ws value ws`.  A second top-level value, and any trailing
non-whitespace byte, have no derivation; a byte-order mark is not in `ws`, so it
has none either. -/
def TextAt (m : Strictness) (bs : Bytes) (v : Value) : Prop :=
  ∃ i j : Nat, skipFrom bs 0 = i ∧ ValueAt m bs i v j ∧ skipFrom bs j = bs.length

/-- RFC 8259 as written, with the §8.1 UTF-8 encoding: unpaired surrogate escapes
included, duplicates included, any nesting depth. -/
def RfcText (bs : Bytes) (v : Value) : Prop := TextAt .rfc bs v

/-- RFC 8259 restricted by RFC 7493 §2.1's character constraint.  This is the
language the parser is proved to accept, and the one the reflection lemmas
characterise. -/
def StrictText (bs : Bytes) (v : Value) : Prop := TextAt .strict bs v

/-- Our restrictions on the text's interpretation: RFC 7493 §2.1's character
constraint, on member names and string values alike, escaped or raw.  There is no
byte-order-mark clause because the grammar has no BOM to narrow, and no UTF-8
clause because RFC 8259 §8.1 already makes RFC 3629 normative (§3.3). -/
def Policy (v : Value) : Prop := v.charPolicy

/-- The accepted language, before limits: the RFC 8259 grammar restricted by
`Policy`.  The adherence theorems of §7.5 are stated against these three names. -/
def ValidDocument (bs : Bytes) (v : Value) : Prop := RfcText bs v ∧ Policy v

/-- No number constituent immediately follows: what the enclosing production
guarantees after a value, and what makes the number scan's maximal run equal the
semantic lexeme. -/
def NumberStop (bs : Bytes) (j : Nat) : Prop :=
  ∀ (c : UInt8) (rest : Bytes), bs.drop j = c +: rest → NumConstituent c = false

end LeanLLVM.JSON
