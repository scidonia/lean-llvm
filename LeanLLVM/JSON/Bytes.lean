/-
Byte-level primitives shared by the JSON semantics, the scanners and the
parser.  Nothing here mentions a value, a token, a tape or a limit.

RFC 8259 §2 fixes the whitespace set; RFC 8259 §6 and §7 fix the digit and hex
sets; RFC 7493 §2.1 fixes the character restriction, which is a predicate on
code points and therefore lives here too.

The carrier is one move, not a translation: every definition in the JSON chain
is written over `Bytes`, so the statements are the same sentences over the
carrier that holds the bytes.  No transport theorem from the former
`List UInt8` development to this one is stated or proved, and propositional
identity with it is not claimed — only that the definitions moved together and
that the claims their statements make are the ones they made before.
-/
import LeanLLVM.JSON.ByteString

namespace LeanLLVM.JSON

open ByteString

/-- The proof layer's byte string: the contiguous carrier of `ByteString`, so
`bs[i]?`, `bs.size`, `bs.drop n` and `bs ++ bs'` are the vector's operations and
no statement in this subtree is about a linked list. -/
abbrev Bytes := ByteString

/-- The four JSON whitespace bytes of RFC 8259 §2's `ws` production. -/
def IsSpaceB (b : UInt8) : Bool :=
  decide (b = 0x20) || decide (b = 0x09) || decide (b = 0x0A) || decide (b = 0x0D)

def IsDigitB (b : UInt8) : Bool := decide (0x30 ≤ b) && decide (b ≤ 0x39)

def HexVal (b : UInt8) : Option Nat :=
  if IsDigitB b then some (b.toNat - 0x30)
  else if decide (0x41 ≤ b) && decide (b ≤ 0x46) then some (b.toNat - 0x37)
  else if decide (0x61 ≤ b) && decide (b ≤ 0x66) then some (b.toNat - 0x57)
  else none

def Hex4 (a b c d : UInt8) : Option Nat :=
  match HexVal a, HexVal b, HexVal c, HexVal d with
  | some x, some y, some z, some w => some (x * 0x1000 + y * 0x100 + z * 0x10 + w)
  | _, _, _, _ => none

/-- The bytes `bs[i…j)` are all JSON whitespace.  The empty range is admitted. -/
def SpaceAt (bs : Bytes) (i j : Nat) : Prop :=
  i ≤ j ∧ ∀ (k : Nat) (b : UInt8), i ≤ k → k < j → bs[k]? = some b → IsSpaceB b = true

/-- A lookup that found nothing is past the end. -/
private theorem ge_of_getElem?_eq_none {bs : Bytes} {i : Nat} (h : bs[i]? = none) :
    bs.size ≤ i := by
  by_cases hi : i < bs.size
  · have hi' : i < bs.length := by rwa [ByteString.length_eq_size]
    have hsome : bs[i]? = some bs[i] := ByteString.getElem?_eq_getElem hi'
    rw [hsome] at h
    exact absurd h (by simp)
  · omega

/-- The list view of a drop splits off the byte at the index: the shape an
index scan recurses on. -/
private theorem data_toList_drop_eq_cons {bs : Bytes} {i : Nat} {a : UInt8}
    (h : bs[i]? = some a) :
    bs.data.toList.drop i = a :: bs.data.toList.drop (i + 1) := by
  have hlist : bs.data.toList[i]? = some a := by
    rw [Array.getElem?_toList, ← ByteString.getElem?_eq_data]
    exact h
  obtain ⟨hlen, hval⟩ := List.getElem?_eq_some_iff.mp hlist
  rw [List.drop_eq_getElem_cons hlen, hval]

/-- A drop at or past the end is empty: the other shape an index scan recurses
on. -/
private theorem data_toList_drop_eq_nil {bs : Bytes} {i : Nat} (h : bs.size ≤ i) :
    bs.data.toList.drop i = [] :=
  List.drop_eq_nil_of_le (by simpa [Array.length_toList] using h)

/-- The whitespace run over the carrier's list view: the reference form the cons
equations and the run lemmas are stated against. -/
private def spaceRunL : List UInt8 → Nat
  | [] => 0
  | b :: rest => if IsSpaceB b then spaceRunL rest + 1 else 0

/-- The whitespace run from index `i`, read by index: the scan costs the run and
materialises no suffix.  `fuel` bounds the number of steps, so the recursion is
structural and a scan on concrete bytes computes definitionally. -/
private def spaceRunAt (bs : Bytes) (fuel i : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | fuel + 1 =>
      match bs[i]? with
      | none => 0
      | some b => if IsSpaceB b then spaceRunAt bs fuel (i + 1) + 1 else 0

/-- The length of the whitespace run at the head of the argument. -/
def spaceRun (bs : Bytes) : Nat := spaceRunAt bs bs.size 0

/-- The index scan is the list view's scan at every offset: the agreement the
cons equations and the run lemmas are proved through. -/
private theorem spaceRunAt_eq_list (fuel : Nat) :
    ∀ (bs : Bytes) (i : Nat), bs.size ≤ i + fuel →
      spaceRunAt bs fuel i = spaceRunL (bs.data.toList.drop i) := by
  induction fuel with
  | zero =>
      intro bs i h
      have hge : bs.size ≤ i := by omega
      simp only [spaceRunAt, spaceRunL, data_toList_drop_eq_nil hge]
  | succ fuel ih =>
      intro bs i h
      cases hk : bs[i]? with
      | none =>
          have hge := ge_of_getElem?_eq_none hk
          simp only [spaceRunAt, spaceRunL, hk, data_toList_drop_eq_nil hge]
      | some a =>
          have hi : i < bs.size := (ByteString.getElem?_eq_some_iff.mp hk).1
          simp only [spaceRunAt, hk, data_toList_drop_eq_cons hk, spaceRunL]
          rw [ih bs (i + 1) (by omega)]

/-- The head of the argument under the list view: the form the cons equations
are proved through. -/
private theorem spaceRun_eq_list (bs : Bytes) : spaceRun bs = spaceRunL bs.data.toList := by
  rw [spaceRun, spaceRunAt_eq_list bs.size bs 0 (by omega), List.drop_zero]

/-! ### The run equations

`spaceRun` and `numRun` read the carrier at an index and copy nothing at their
own boundary, so their equations are proved from the index scan's agreement with
the list view (`spaceRunAt_eq_list`, `numRunAt_eq_list`) rather than being
definitional: `rfl` does not reduce across `cons` or `drop`, which rebuild the
carrier.  The proofs' footprint is `[propext, Quot.sound]`.

A caller that hands a scan a dropped suffix still pays that copy: the parser's
number and string paths and `HasPrefix` call these functions on `bs.drop i`, and
they keep doing so until the parser threads offsets instead of dropping. -/

theorem spaceRun_cons (b : UInt8) (bs : Bytes) :
    spaceRun (cons b bs) = if IsSpaceB b then spaceRun bs + 1 else 0 := by
  rw [spaceRun_eq_list, spaceRun_eq_list, ByteString.data_toList_cons]
  simp only [spaceRunL]

theorem spaceRun_empty : spaceRun (empty : Bytes) = 0 := by
  rw [spaceRun_eq_list, ByteString.data_toList_empty]
  rfl

/-- The first index at or after `i` that is not whitespace; `bs.length` when the
rest of the input is whitespace. -/
def skipFrom (bs : Bytes) (i : Nat) : Nat := i + spaceRunAt bs (bs.size - i) i

/-- The arithmetic form of `skipFrom`: the index scan from `i` is the run at the
head of the dropped suffix, so the skip is that sum.  The lemma is the name the
parser's proofs rewrite with, and the equality is proved rather than definitional
because the scan reads the carrier at an index. -/
theorem skipFrom_def (bs : Bytes) (i : Nat) :
    skipFrom bs i = i + spaceRun (bs.drop i) := by
  rw [skipFrom, spaceRun,
    spaceRunAt_eq_list (bs.size - i) bs i (by omega),
    spaceRunAt_eq_list (bs.drop i).size (bs.drop i) 0 (by omega),
    List.drop_zero, ByteString.data_toList_drop]

/-- `bs[i…]` starts with exactly `p`. -/
def HasPrefix (bs : Bytes) (i : Nat) (p : Bytes) : Prop := (bs.drop i).take p.length = p

def HasPrefixB (bs : Bytes) (i : Nat) (p : Bytes) : Bool :=
  decide ((bs.drop i).take p.length = p)

/-- A byte that could continue a JSON number.  The number scan takes the maximal
run of these and then validates it with the grammar. -/
def NumConstituent (b : UInt8) : Bool :=
  IsDigitB b || decide (b = 0x2E) || decide (b = 0x65) || decide (b = 0x45) ||
    decide (b = 0x2B) || decide (b = 0x2D)

/-- The longest prefix of the argument consisting of number constituents, over
the carrier's list view: the reference form the cons equations and `numRun_spec`
are stated against. -/
private def numRunL : List UInt8 → List UInt8
  | [] => []
  | b :: rest => if NumConstituent b then b :: numRunL rest else []

/-- The number constituents from index `i`, collected by index: the run's bytes
are built once and no suffix is materialised, and the lexeme is a `literal` of
that list rather than a slice of a dropped carrier.  `fuel` bounds the number of
steps, so a scan on concrete bytes computes definitionally. -/
private def numRunAt (bs : Bytes) (fuel i : Nat) : List UInt8 :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
      match bs[i]? with
      | none => []
      | some b => if NumConstituent b then b :: numRunAt bs fuel (i + 1) else []

/-- The longest prefix of the argument consisting of number constituents. -/
def numRun (bs : Bytes) : Bytes := literal (numRunAt bs bs.size 0)

/-- The index scan is the list view's scan at every offset: the agreement the
cons equations and the spec lemmas are proved through. -/
private theorem numRunAt_eq_list (fuel : Nat) :
    ∀ (bs : Bytes) (i : Nat), bs.size ≤ i + fuel →
      numRunAt bs fuel i = numRunL (bs.data.toList.drop i) := by
  induction fuel with
  | zero =>
      intro bs i h
      have hge : bs.size ≤ i := by omega
      simp only [numRunAt, numRunL, data_toList_drop_eq_nil hge]
  | succ fuel ih =>
      intro bs i h
      cases hk : bs[i]? with
      | none =>
          have hge := ge_of_getElem?_eq_none hk
          simp only [numRunAt, numRunL, hk, data_toList_drop_eq_nil hge]
      | some a =>
          have hi : i < bs.size := (ByteString.getElem?_eq_some_iff.mp hk).1
          simp only [numRunAt, hk, data_toList_drop_eq_cons hk, numRunL]
          rw [ih bs (i + 1) (by omega)]

/-- The head of the argument under the list view: the form the cons equations
are proved through. -/
private theorem numRun_eq_list (bs : Bytes) :
    numRun bs = literal (numRunL bs.data.toList) := by
  rw [numRun, numRunAt_eq_list bs.size bs 0 (by omega), List.drop_zero]

theorem numRun_empty : numRun (empty : Bytes) = empty := by
  rw [numRun_eq_list, ByteString.data_toList_empty]
  rfl

theorem numRun_cons (b : UInt8) (bs : Bytes) :
    numRun (cons b bs) = if NumConstituent b then cons b (numRun bs) else empty := by
  rw [numRun_eq_list, numRun_eq_list, ByteString.data_toList_cons]
  by_cases h : NumConstituent b = true
  · simp [numRunL, h, ByteString.literal_cons]
  · simp [numRunL, h, ByteString.empty]

/-- A Unicode scalar value: a code point that is not a surrogate.  The
`≤ 0x10FFFF` bound is already imposed by `Utf8Char`, and is restated because this
predicate is also used where no encoding has been checked. -/
def IsScalar (n : Nat) : Prop := n ≤ 0x10FFFF ∧ ¬ (0xD800 ≤ n ∧ n ≤ 0xDFFF)

/-- Unicode noncharacters: U+FDD0..U+FDEF and every U+nFFFE / U+nFFFF. -/
def IsNoncharacter (n : Nat) : Bool :=
  (decide (0xFDD0 ≤ n) && decide (n ≤ 0xFDEF)) ||
    decide (n % 0x10000 = 0xFFFE) || decide (n % 0x10000 = 0xFFFF)

/-- The character a string may contain under RFC 7493 §2.1. -/
def CharAllowed (n : Nat) : Prop := IsScalar n ∧ IsNoncharacter n = false

/-- `IsScalar` is decided by ordinary arithmetic, so clients can `decide` a
concrete instance without unfolding the definition by hand. -/
instance (n : Nat) : Decidable (IsScalar n) := by
  unfold IsScalar
  infer_instance

instance (n : Nat) : Decidable (CharAllowed n) := by
  unfold CharAllowed
  infer_instance


def IsHighSurrogate (n : Nat) : Prop := 0xD800 ≤ n ∧ n ≤ 0xDBFF
def IsLowSurrogate (n : Nat) : Prop := 0xDC00 ≤ n ∧ n ≤ 0xDFFF

instance (n : Nat) : Decidable (IsHighSurrogate n) := by
  unfold IsHighSurrogate
  infer_instance

instance (n : Nat) : Decidable (IsLowSurrogate n) := by
  unfold IsLowSurrogate
  infer_instance

end LeanLLVM.JSON
