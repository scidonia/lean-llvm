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

/-- The whitespace run, over the carrier's list view.  This is the one definition
of the scan; `spaceRun` applies it to the view. -/
private def spaceRunL : List UInt8 → Nat
  | [] => 0
  | b :: rest => if IsSpaceB b then spaceRunL rest + 1 else 0

/-- The length of the whitespace run at the head of the argument. -/
def spaceRun (bs : Bytes) : Nat := spaceRunL bs.data.toList

theorem spaceRun_cons (b : UInt8) (bs : Bytes) :
    spaceRun (cons b bs) = if IsSpaceB b then spaceRun bs + 1 else 0 := rfl

theorem spaceRun_empty : spaceRun (empty : Bytes) = 0 := rfl

/-- The first index at or after `i` that is not whitespace; `bs.length` when the
rest of the input is whitespace. -/
def skipFrom (bs : Bytes) (i : Nat) : Nat := i + spaceRun (bs.drop i)

/-- The arithmetic form of `skipFrom`, by `rfl`: the definition already is that
form, and the lemma is the name proofs rewrite with. -/
theorem skipFrom_def (bs : Bytes) (i : Nat) :
    skipFrom bs i = i + spaceRun (bs.drop i) := rfl

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
the carrier's list view. -/
private def numRunL : List UInt8 → List UInt8
  | [] => []
  | b :: rest => if NumConstituent b then b :: numRunL rest else []

/-- The longest prefix of the argument consisting of number constituents. -/
def numRun (bs : Bytes) : Bytes := literal (numRunL bs.data.toList)

theorem numRun_empty : numRun (empty : Bytes) = empty := rfl

theorem numRun_cons (b : UInt8) (bs : Bytes) :
    numRun (cons b bs) = if NumConstituent b then cons b (numRun bs) else empty := by
  by_cases h : NumConstituent b = true
  · rw [if_pos h]
    apply ByteString.eq_of_toList_eq
    simp [numRun, numRunL, ByteString.data_toList_cons, ByteString.toList_cons, h]
  · rw [if_neg h]
    apply ByteString.eq_of_toList_eq
    simp [numRun, numRunL, ByteString.data_toList_cons, ByteString.toList_empty, h]

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
