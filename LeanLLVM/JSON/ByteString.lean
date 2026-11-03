/-
The byte vector the JSON proof layer is written against: `ByteString` is
`ByteArray`, with the list-shaped operations and lemmas the semantics, the
scanners and the parser use.

`ByteArray` is the carrier because it packs one byte per slot and because its
terms already have the shape the proofs take; what it lacks is lemmas.  So this
module supplies exactly those:

* the three bridges to the underlying array, which is where `Array`'s and
  `List`'s libraries discharge byte-directed goals: `toList_eq_data_toList` (one
  loop induction, because `ByteArray.toList` is an irreducible loop),
  `getElem?_eq_data` and `size_eq_data` (both `rfl`);
* the list-shaped shims `ByteArray` does not have — a byte literal, `cons`,
  `head?`, `take`, `drop`, `takeWhile`, `dropWhile`, `length` and `get?` — each
  with its `toList` bridge, plus the two cons laws an induction over a non-empty
  string splits on, and `toList_append`;
* the `Membership` instance and its cons lemma, so `b ∈ bs` means the list
  membership it means over a list;
* `Digits0` over `ByteString`, its transfer to and from the list-shaped relation
  in `Spec`, and the four `takeWhile`/`dropWhile` facts `Scan` proves, restated
  through the bridges.

`size`, `toList`, `empty` and `++` are `ByteArray`'s own operations and are not
restated; only the lemmas they lack are.

`Bytes` is still `List UInt8`, so no statement in the subtree is written over
this type yet.  The module states the interface in advance, which is what makes
moving `Bytes` to it a rewrite of statements and proof moves rather than a
search for missing lemmas; it sits above `Scan` because the four scanner facts
it restates are proved there today over the list carrier, and they move down
with `Bytes`.

`take` and `drop` are defined through `.toList`, which is the cheap direction to
bridge and the expensive one to run: each copies into a list and back, since
`ByteArray` has neither.  A `.data`-defined variant (`Array.take`/`Array.drop`)
keeps the same `toList_take`/`toList_drop` statements and so leaves every proof
below unchanged; it needs `Array.take_eq_extract`, `Array.toList_extract` and
`List.extract_eq_take_drop` to bridge.
-/
import LeanLLVM.JSON.Scan

namespace LeanLLVM.JSON

/-- The byte vector this module's interface is stated over.  It is `ByteArray`
itself, so `bs[i]?`, `bs.size`, `bs.toList` and `bs ++ bs'` are the native
operations, with no wrapper between them and the statements. -/
abbrev ByteString := ByteArray

namespace ByteString

/-! ### The three bridges to the underlying array -/

/-- The loop invariant of `ByteArray.toList`: from index `i` the accumulator
holds the bytes after `i`, in reverse. -/
private theorem toList_loop_eq (bs : ByteString) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  refine ByteArray.toList.loop.induct bs
    (motive := fun i r => ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i)
    ?_ ?_ i r
  · intro i r hi ih
    rw [ByteArray.toList.loop.eq_def]
    simp only [hi, ite_true]
    rw [ih]
    have hlen : i < bs.data.toList.length := by
      rw [Array.length_toList, ByteArray.size_data]; exact hi
    have hget : bs.data.toList[i]? = some (bs.get! i) := by
      rw [Array.getElem?_toList]
      have hsz : i < bs.data.size := by simpa only [← ByteArray.size_data] using hi
      rw [Array.getElem?_eq_getElem hsz]
      show some bs.data[i] = some (bs.get! i)
      rw [ByteArray.get!, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem hsz]
      rfl
    have hval : bs.data.toList[i] = bs.get! i :=
      (List.getElem?_eq_some_iff.mp hget).2
    have hdrop : bs.data.toList.drop i = bs.get! i :: bs.data.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons hlen, hval]
    rw [hdrop, List.reverse_cons, List.append_assoc]
    rfl
  · intro i r hi
    rw [ByteArray.toList.loop.eq_def]
    simp only [hi, ite_false]
    have hle : bs.data.toList.length ≤ i := by
      rw [Array.length_toList, ByteArray.size_data]
      omega
    rw [List.drop_eq_nil_of_le hle]
    simp

/-- `bs.toList` is the underlying array's list.  Not `rfl`: `ByteArray.toList` is
an irreducible loop over the array, so this is the family's one loop induction. -/
theorem toList_eq_data_toList (bs : ByteString) : bs.toList = bs.data.toList := by
  rw [ByteArray.toList.eq_def]
  simpa using toList_loop_eq bs 0 []

/-- `rfl`: both sides are the same `ite` over the same size and the same
instance. -/
theorem getElem?_eq_data (bs : ByteString) (i : Nat) : bs[i]? = bs.data[i]? := rfl

/-- `rfl`: `ByteArray.size` is the underlying array's size. -/
theorem size_eq_data (bs : ByteString) : bs.size = bs.data.size := rfl

/-- The per-index form of `toList_eq_data_toList`, the direction the cons laws
rewrite a hypothesis with. -/
theorem toList_getElem?_eq_getElem? (bs : ByteString) (i : Nat) :
    bs.toList[i]? = bs[i]? := by
  rw [toList_eq_data_toList, getElem?_eq_data, ← Array.getElem?_toList]

/-! ### Length, lookup, literals, and extensionality -/

/-- List-compatible spelling of `bs.size`. -/
def length (bs : ByteString) : Nat := bs.size

theorem length_eq_size (bs : ByteString) : bs.length = bs.size := rfl

/-- `bs.toList.length = bs.size`, the form the `List` length lemmas expect. -/
theorem toList_length (bs : ByteString) : bs.toList.length = bs.size := by
  rw [toList_eq_data_toList, Array.length_toList, ByteArray.size_data]

/-- Positional lookup under the method spelling: `bs.get? i` is `bs[i]?`. -/
def get? (bs : ByteString) (i : Nat) : Option UInt8 := bs[i]?

theorem get?_eq_getElem? (bs : ByteString) (i : Nat) : bs.get? i = bs[i]? := rfl

/-- A byte string from a list, the spelling the grammar's literals take once the
statements are written over `ByteString`. -/
def literal (l : List UInt8) : ByteString := l.toByteArray

theorem toList_literal (l : List UInt8) : (literal l).toList = l := by
  rw [literal, toList_eq_data_toList]
  exact List.toList_data_toByteArray

/-- The literal of a byte string's list is that byte string: the round-trip
`ByteArray` does not ship (`ByteArray.toList_toByteArray` does not exist). -/
theorem literal_toList (bs : ByteString) : literal bs.toList = bs := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  show bs.toList.toByteArray.data.toList = bs.data.toList
  rw [List.toList_data_toByteArray, toList_eq_data_toList]

theorem literal_nil : literal ([] : List UInt8) = ByteArray.empty := rfl

/-- Two byte strings with the same list are equal. -/
theorem eq_of_toList_eq {a b : ByteString} (h : a.toList = b.toList) : a = b := by
  rw [← literal_toList a, ← literal_toList b, h]

/-! ### `cons` and `head?` -/

/-- Prepend a byte.  There is no array cons, so this goes through the list and
reallocates. -/
def cons (b : UInt8) (bs : ByteString) : ByteString := literal (b :: bs.toList)

theorem toList_cons (b : UInt8) (bs : ByteString) :
    (cons b bs).toList = b :: bs.toList := by
  rw [cons, toList_literal]

theorem size_cons (b : UInt8) (bs : ByteString) : (cons b bs).size = bs.size + 1 := by
  rw [← toList_length, toList_cons, List.length_cons, toList_length]

/-- The first byte, read straight off the underlying array: no loop, no copy. -/
def head? (bs : ByteString) : Option UInt8 := bs.data[0]?

theorem head?_cons (b : UInt8) (bs : ByteString) : head? (cons b bs) = some b := by
  rw [head?, cons, literal, ← Array.getElem?_toList, List.toList_data_toByteArray]
  rfl

/-- `List.head?`-shaped: the first byte is the list's head. -/
theorem head?_toList (bs : ByteString) : head? bs = bs.toList.head? := by
  rw [head?, List.head?_eq_getElem?, toList_eq_data_toList, Array.getElem?_toList]

/-! ### `take` and `drop` -/

/-- The first `n` bytes. -/
def take (bs : ByteString) (n : Nat) : ByteString := literal (bs.toList.take n)

theorem toList_take (bs : ByteString) (n : Nat) :
    (take bs n).toList = bs.toList.take n := by
  rw [take, toList_literal]

/-- The bytes from `n` on. -/
def drop (bs : ByteString) (n : Nat) : ByteString := literal (bs.toList.drop n)

theorem toList_drop (bs : ByteString) (n : Nat) :
    (drop bs n).toList = bs.toList.drop n := by
  rw [drop, toList_literal]

/-- `List.take_succ_cons`-shaped: taking `i + 1` from a cons is the cons of
taking `i` from its tail. -/
theorem take_succ_cons (a : UInt8) (bs : ByteString) (i : Nat) :
    take (cons a bs) (i + 1) = cons a (take bs i) := by
  apply eq_of_toList_eq
  rw [toList_take, toList_cons, toList_cons, toList_take, List.take_succ_cons]

/-- `List.drop_eq_getElem_cons`-shaped: dropping at an indexed byte splits that
byte off. -/
theorem drop_eq_getElem_cons {bs : ByteString} {i : Nat} {a : UInt8}
    (h : bs[i]? = some a) : drop bs i = cons a (drop bs (i + 1)) := by
  apply eq_of_toList_eq
  rw [toList_drop, toList_cons, toList_drop]
  have h' : bs.toList[i]? = some a := by
    rw [toList_getElem?_eq_getElem?]
    exact h
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp h'
  rw [List.drop_eq_getElem_cons hlt, hget]

/-- `List.getElem?_take`-shaped. -/
theorem getElem?_take (bs : ByteString) (n i : Nat) :
    (take bs n)[i]? = if i < n then bs[i]? else none := by
  rw [← toList_getElem?_eq_getElem? (take bs n) i, toList_take, List.getElem?_take]
  by_cases h : i < n <;> simp [h, toList_getElem?_eq_getElem?]

/-! ### `append`

`++` is `ByteArray.append`; what it lacks is the list bridge. -/

/-- The list of an appended pair is the appended lists.  `ByteArray.append`
builds its array from the concatenated lists, so once the bridge and the two
list rewrites are done the goal is definitional. -/
theorem toList_append (a b : ByteString) : (a ++ b).toList = a.toList ++ b.toList := by
  rw [toList_eq_data_toList]
  have ha := toList_eq_data_toList a
  have hb := toList_eq_data_toList b
  rw [ha, hb]
  rfl

/-! ### `takeWhile` and `dropWhile` -/

/-- The longest prefix whose bytes satisfy `p`. -/
def takeWhile (bs : ByteString) (p : UInt8 → Bool) : ByteString :=
  literal (bs.toList.takeWhile p)

theorem toList_takeWhile (bs : ByteString) (p : UInt8 → Bool) :
    (takeWhile bs p).toList = bs.toList.takeWhile p := by
  rw [takeWhile, toList_literal]

/-- The rest after the longest prefix whose bytes satisfy `p`. -/
def dropWhile (bs : ByteString) (p : UInt8 → Bool) : ByteString :=
  literal (bs.toList.dropWhile p)

theorem toList_dropWhile (bs : ByteString) (p : UInt8 → Bool) :
    (dropWhile bs p).toList = bs.toList.dropWhile p := by
  rw [dropWhile, toList_literal]

/-- `List.takeWhile_cons`-shaped. -/
theorem takeWhile_cons (p : UInt8 → Bool) (a : UInt8) (bs : ByteString) :
    takeWhile (cons a bs) p = if p a then cons a (takeWhile bs p) else ByteArray.empty := by
  apply eq_of_toList_eq
  rw [toList_takeWhile, toList_cons, List.takeWhile_cons]
  by_cases hp : p a = true
  · simp [hp, toList_cons, toList_takeWhile]
  · simp [hp, ByteArray.toList_empty]

/-- `List.dropWhile_cons`-shaped. -/
theorem dropWhile_cons (p : UInt8 → Bool) (a : UInt8) (bs : ByteString) :
    dropWhile (cons a bs) p = if p a then dropWhile bs p else cons a bs := by
  apply eq_of_toList_eq
  rw [toList_dropWhile, toList_cons, List.dropWhile_cons]
  by_cases hp : p a = true
  · simp [hp, toList_dropWhile]
  · simp [hp, toList_cons]

/-! ### Membership -/

/-- A byte is a member when it occurs in the list. -/
instance instMembershipByteString : Membership UInt8 ByteString where
  mem := fun (bs : ByteString) (b : UInt8) => b ∈ bs.toList

/-- Membership is list membership, which is the instance's definition. -/
theorem mem_def (b : UInt8) (bs : ByteString) : b ∈ bs ↔ b ∈ bs.toList := Iff.rfl

/-- `List.mem_cons`-shaped. -/
theorem mem_cons (a b : UInt8) (bs : ByteString) :
    b ∈ cons a bs ↔ b = a ∨ b ∈ bs := by
  simp only [mem_def, toList_cons, List.mem_cons]

/-! ### `Digits0`, and its transfer to the list-shaped relation

`Spec.Digits0` is the relation the grammar states over `Bytes` while `Bytes` is a
list.  This is that shape over `ByteString`, with both transfers, so the relation
survives the carrier unchanged. -/

/-- `*DIGIT`: the shape `Spec.Digits0` takes over `ByteString`. -/
inductive Digits0 : ByteString → Prop where
  | nil : Digits0 ByteArray.empty
  | more {b : UInt8} {bs : ByteString} (h : IsDigitB b = true) (hr : Digits0 bs) :
      Digits0 (cons b bs)

/-- The literal of a cons is the cons of the literals. -/
theorem literal_cons (b : UInt8) (l : List UInt8) :
    literal (b :: l) = cons b (literal l) := by
  apply eq_of_toList_eq
  rw [toList_literal, toList_cons, toList_literal]

/-- A derivation over `ByteString` is a derivation over its list. -/
theorem digits0_toList {bs : ByteString} (h : Digits0 bs) : LeanLLVM.JSON.Digits0 bs.toList := by
  induction h with
  | nil => rw [ByteArray.toList_empty]; exact .nil
  | more hb _ ih => rw [toList_cons]; exact .more hb ih

/-- A derivation over a list is a derivation over its literal. -/
theorem digits0_of_toList {l : List UInt8} (h : LeanLLVM.JSON.Digits0 l) :
    Digits0 (literal l) := by
  induction h with
  | nil => exact .nil
  | more hb _ ih => rw [literal_cons]; exact .more hb ih

theorem digits0_all {bs : ByteString} (h : Digits0 bs) : ∀ b ∈ bs, IsDigitB b = true := by
  intro b hb
  exact LeanLLVM.JSON.digits0_all (digits0_toList h) b hb

/-! ### The four `takeWhile`/`dropWhile` facts of `Scan`, over `ByteString` -/

/-- The maximal digit run is all digits. -/
theorem digits0_takeWhile (bs : ByteString) : Digits0 (takeWhile bs IsDigitB) := by
  rw [← literal_toList (takeWhile bs IsDigitB)]
  apply digits0_of_toList
  rw [toList_takeWhile]
  exact LeanLLVM.JSON.digits0_takeWhile bs.toList

/-- An all-digit string has nothing left after its digit run. -/
theorem dropWhile_digits {bs : ByteString} (h : Digits0 bs) :
    dropWhile bs IsDigitB = ByteArray.empty := by
  apply eq_of_toList_eq
  rw [toList_dropWhile, ByteArray.toList_empty]
  exact LeanLLVM.JSON.dropWhile_digits (digits0_toList h)

/-- An all-digit string is its own digit run. -/
theorem takeWhile_digits {bs : ByteString} (h : Digits0 bs) : takeWhile bs IsDigitB = bs := by
  apply eq_of_toList_eq
  rw [toList_takeWhile]
  exact LeanLLVM.JSON.takeWhile_digits (digits0_toList h)

/-- A string with nothing left after its digit run is that run. -/
theorem eq_takeWhile_of_dropWhile_eq_nil {bs : ByteString}
    (h : dropWhile bs IsDigitB = ByteArray.empty) : bs = takeWhile bs IsDigitB := by
  apply eq_of_toList_eq
  rw [toList_takeWhile]
  exact LeanLLVM.JSON.eq_takeWhile_of_dropWhile_eq_nil (by
    have := congrArg ByteArray.toList h
    rwa [toList_dropWhile, ByteArray.toList_empty] at this)

end ByteString

end LeanLLVM.JSON
