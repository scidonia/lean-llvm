/-
The byte vector the JSON proof layer is written against: `ByteString` is
`ByteArray`, with the list-shaped operations and lemmas the semantics, the
scanners and the parser use.

`ByteArray` is the carrier because it packs one byte per slot and because the
block layer's window is a vector, not a cons cell.  What it lacks is the
interface: there is no `cons`, no `take`/`drop`, no `takeWhile`/`dropWhile`, no
`Membership` instance, and its `toList` is an irreducible loop rather than a
projection.  This module supplies that interface once, so that a statement
written over bytes reads the same as it did over the list.

The design is the `.data` view.  `ByteArray`'s only field is an `Array`, whose
`toList` is a structure projection and therefore transparent to the kernel, so
every operation below is defined on `bs.data.toList` and rebuilt with
`Array.mk`.  That gives two properties the proofs lean on:

* `(literal l).data.toList = l`, `(cons b bs).data.toList = b :: bs.data.toList`,
  `(drop bs n).data.toList = (bs.data.toList).drop n`, and the same for `take`,
  `takeWhile`, `dropWhile` are `rfl`, so a definition that matches on
  `bs.data.toList` reduces on the constructors the proofs produce;
* `bs.toList` is not definitional, but `toList_eq_data_toList` (one loop
  induction) rewrites it to `bs.data.toList` in one step, which is how a proof
  that reasons in list vocabulary enters this world.

The operations are the *interface*, not the fast path: `drop`, `take`, `cons`,
`takeWhile` and `dropWhile` rebuild the array, so each costs a copy, and a
definition that recurses through them is quadratic.  The definitions in `Scan`
therefore match on `bs.data.toList` once and consume the list tail directly.
Taking a window, a `Vector UInt8 32`, and a cursor over the array are the same
abstraction at the array level and are not part of this module.
-/
namespace LeanLLVM.JSON

/-- The byte vector this subtree's statements are written over.  It is
`ByteArray` itself, so `bs[i]?`, `bs.size`, `bs.toList` and `bs ++ bs'` are the
native operations, with no wrapper between them and the statements. -/
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

@[simp] theorem length_eq_size (bs : ByteString) : bs.length = bs.size := rfl

/-- `bs.toList.length = bs.size`, the form the `List` length lemmas expect. -/
@[simp] theorem toList_length (bs : ByteString) : bs.toList.length = bs.size := by
  rw [toList_eq_data_toList, Array.length_toList, ByteArray.size_data]

/-- Positional lookup under the method spelling: `bs.get? i` is `bs[i]?`. -/
def get? (bs : ByteString) (i : Nat) : Option UInt8 := bs[i]?

theorem get?_eq_getElem? (bs : ByteString) (i : Nat) : bs.get? i = bs[i]? := rfl

/-- A byte string from a list.  `Array.mk` is the array's constructor, so
`.data.toList` of the result is the argument by `rfl`. -/
def literal (l : List UInt8) : ByteString := ⟨Array.mk l⟩

theorem data_toList_literal (l : List UInt8) : (literal l).data.toList = l := rfl

@[simp] theorem toList_literal (l : List UInt8) : (literal l).toList = l := by
  rw [toList_eq_data_toList, data_toList_literal]

/-- A literal's size is its list's.  `Array.size` does not reduce on a
constructed array, so this is the form the span arithmetic and `decide` sites
need; the `.length` spelling follows from it. -/
@[simp] theorem size_literal (l : List UInt8) : (literal l).size = l.length := by
  rw [size_eq_data, ← Array.length_toList, data_toList_literal]

/-- The literal of a byte string's list is that byte string: the round-trip
`ByteArray` does not ship. -/
theorem literal_toList (bs : ByteString) : literal bs.toList = bs := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  show bs.toList = bs.data.toList
  rw [toList_eq_data_toList]

/-- The empty byte string, spelled through `Array.mk` so that its `.data.toList`
is `[]` by `rfl`. -/
def empty : ByteString := literal []

theorem data_toList_empty : (empty : ByteString).data.toList = [] := rfl

@[simp] theorem toList_empty : (empty : ByteString).toList = [] := by
  rw [toList_eq_data_toList, data_toList_empty]

theorem length_empty : (empty : ByteString).length = 0 := rfl

/-- `ByteArray` ships no `Repr` in this toolchain.  The carrier prints as the
list it holds, which is how a byte string printed before it was a vector. -/
instance instReprByteString : Repr ByteString where
  reprPrec bs prec := Repr.reprPrec bs.toList prec

/-- Two byte strings with the same list are equal. -/
theorem eq_of_toList_eq {a b : ByteString} (h : a.toList = b.toList) : a = b := by
  rw [← literal_toList a, ← literal_toList b, h]

/-- Two byte strings with the same underlying list are equal. -/
theorem eq_of_data_toList_eq {a b : ByteString} (h : a.data.toList = b.data.toList) :
    a = b := by
  apply ByteArray.ext
  exact Array.toList_inj.mp h

/-- The literal of a byte string's underlying list is that byte string. -/
theorem literal_data_toList (bs : ByteString) : literal bs.data.toList = bs := by
  apply eq_of_data_toList_eq
  rw [data_toList_literal]

/-- `List.getElem?_eq_getElem`-shaped: an in-bounds lookup is the byte at that
index.  The proof layer's statements read a byte positionally, so the list
lemma's proof steps have this spelling over the carrier. -/
theorem getElem?_eq_getElem {bs : ByteString} {i : Nat} (h : i < bs.length) :
    bs[i]? = some bs[i] := by
  rw [getElem?_eq_data]
  exact Array.getElem?_eq_getElem (xs := bs.data) h

/-- `List.getElem?_eq_some_iff`-shaped: a successful lookup is an in-bounds
index and the byte there. -/
theorem getElem?_eq_some_iff {bs : ByteString} {i : Nat} {b : UInt8} :
    bs[i]? = some b ↔ ∃ _ : i < bs.length, bs[i] = b := by
  rw [getElem?_eq_data]
  exact (Array.getElem?_eq_some_iff :
    bs.data[i]? = some b ↔ ∃ _ : i < bs.data.size, bs.data[i] = b)

/-! ### `cons` and `head?` -/

/-- Prepend a byte.  There is no array cons, so this rebuilds the array. -/
def cons (b : UInt8) (bs : ByteString) : ByteString := literal (b :: bs.data.toList)

theorem data_toList_cons (b : UInt8) (bs : ByteString) :
    (cons b bs).data.toList = b :: bs.data.toList := rfl

@[simp] theorem toList_cons (b : UInt8) (bs : ByteString) :
    (cons b bs).toList = b :: bs.toList := by
  rw [toList_eq_data_toList, data_toList_cons, toList_eq_data_toList]

@[simp] theorem length_cons (b : UInt8) (bs : ByteString) :
    (cons b bs).length = bs.length + 1 := by
  rw [length_eq_size, ← toList_length, toList_cons, List.length_cons, toList_length]
  rw [length_eq_size]

theorem size_cons (b : UInt8) (bs : ByteString) : (cons b bs).size = bs.size + 1 := by
  rw [← length_eq_size, length_cons, length_eq_size]

/-! ### Notation

`List`'s `::` is `List.cons` and cannot be retargeted, so the carrier's cons
gets its own infix at the list's precedence: a cons chain over bytes is written
`b +: rest`, which is `cons b rest`. -/

/-- The carrier's cons, at the list's precedence. -/
infixr:67 " +: " => cons

/-- The first byte, read straight off the underlying array: no loop, no copy. -/
def head? (bs : ByteString) : Option UInt8 := bs.data[0]?

theorem head?_cons (b : UInt8) (bs : ByteString) : head? (cons b bs) = some b := by
  rw [head?, cons, literal]
  rfl

/-- `List.head?_eq_getElem?`-shaped: the first byte is the list's head. -/
theorem head?_toList (bs : ByteString) : head? bs = bs.toList.head? := by
  rw [head?, List.head?_eq_getElem?, toList_eq_data_toList, Array.getElem?_toList]

/-- A byte string is empty or a cons.  The elimination form the proofs use where
they used to `cases` the carrier. -/
theorem eq_empty_or_cons (bs : ByteString) :
    bs = empty ∨ ∃ b rest, bs = cons b rest := by
  match h : bs.data.toList with
  | [] => left; apply eq_of_data_toList_eq; rw [data_toList_empty]; exact h
  | b :: rest =>
      right
      refine ⟨b, literal rest, ?_⟩
      apply eq_of_data_toList_eq
      rw [data_toList_cons, data_toList_literal]
      exact h

/-- A byte string whose underlying list is empty is the empty byte string. -/
theorem eq_empty_of_data_toList {bs : ByteString} (h : bs.data.toList = []) : bs = empty := by
  rw [← literal_data_toList bs, h]
  rfl

/-- A byte string whose underlying list is a cons is that cons. -/
theorem eq_cons_of_data_toList {bs : ByteString} {b : UInt8} {rest : List UInt8}
    (h : bs.data.toList = b :: rest) : bs = cons b (literal rest) := by
  rw [← literal_data_toList bs, h]
  rfl

/-- Induction on a byte string, by its two shapes: the elimination form the
proofs use where they used to `induction` the carrier. -/
noncomputable def induction_on {C : ByteString → Sort u} (bs : ByteString)
    (h0 : C empty) (hs : ∀ (b : UInt8) (rest : ByteString), C rest → C (cons b rest)) :
    C bs := by
  have key : ∀ (l : List UInt8), C (literal l) := by
    intro l
    induction l with
    | nil => exact h0
    | cons b rest ih => exact hs b (literal rest) ih
  rw [← literal_data_toList bs]
  exact key bs.data.toList

/-! ### `take` and `drop` -/

/-- The first `n` bytes. -/
def take (bs : ByteString) (n : Nat) : ByteString := literal (bs.data.toList.take n)

theorem data_toList_take (bs : ByteString) (n : Nat) :
    (take bs n).data.toList = bs.data.toList.take n := rfl

@[simp] theorem toList_take (bs : ByteString) (n : Nat) :
    (take bs n).toList = bs.toList.take n := by
  rw [toList_eq_data_toList, data_toList_take, toList_eq_data_toList]

/-- The bytes from `n` on. -/
def drop (bs : ByteString) (n : Nat) : ByteString := literal (bs.data.toList.drop n)

theorem data_toList_drop (bs : ByteString) (n : Nat) :
    (drop bs n).data.toList = bs.data.toList.drop n := rfl

@[simp] theorem toList_drop (bs : ByteString) (n : Nat) :
    (drop bs n).toList = bs.toList.drop n := by
  rw [toList_eq_data_toList, data_toList_drop, toList_eq_data_toList]

theorem length_drop (bs : ByteString) (n : Nat) : (drop bs n).length = bs.length - n := by
  rw [length_eq_size, ← toList_length, toList_drop, List.length_drop, toList_length,
    length_eq_size]

theorem length_take (bs : ByteString) (n : Nat) : (take bs n).length = min n bs.length := by
  rw [length_eq_size, ← toList_length, toList_take, List.length_take, toList_length,
    length_eq_size]

theorem drop_zero (bs : ByteString) : drop bs 0 = bs := by
  apply eq_of_toList_eq
  rw [toList_drop, List.drop_zero]

theorem take_zero (bs : ByteString) : take bs 0 = empty := by
  apply eq_of_toList_eq
  rw [toList_take, List.take_zero, toList_empty]

theorem drop_length (bs : ByteString) : drop bs bs.length = empty := by
  apply eq_of_toList_eq
  rw [toList_drop, toList_empty, length_eq_size, ← toList_length, List.drop_length]

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

/-- `List.getElem?_drop`-shaped. -/
theorem getElem?_drop (bs : ByteString) (n i : Nat) :
    (drop bs n)[i]? = bs[n + i]? := by
  rw [← toList_getElem?_eq_getElem? (drop bs n) i, toList_drop, List.getElem?_drop,
    toList_getElem?_eq_getElem?]

/-- Dropping `n` and taking `m` is the window `[n, n + m)`. -/
theorem take_drop (bs : ByteString) (n m : Nat) :
    take (drop bs n) m = drop (take bs (n + m)) n := by
  apply eq_of_toList_eq
  rw [toList_take, toList_drop, toList_drop, toList_take, List.take_drop]

/-! ### `append`

`++` is `ByteArray.append`; what it lacks is the list bridge. -/

/-- The list of an appended pair is the appended lists. -/
@[simp] theorem toList_append (a b : ByteString) : (a ++ b).toList = a.toList ++ b.toList := by
  rw [toList_eq_data_toList]
  have ha := toList_eq_data_toList a
  have hb := toList_eq_data_toList b
  rw [ha, hb]
  rfl

theorem length_append (a b : ByteString) :
    (a ++ b).length = a.length + b.length := by
  simp only [length_eq_size]
  rw [← toList_length (a ++ b), toList_append, List.length_append, toList_length,
    toList_length]

theorem getElem?_append (a b : ByteString) (i : Nat) :
    (a ++ b)[i]? = if i < a.size then a[i]? else b[i - a.size]? := by
  rw [← toList_getElem?_eq_getElem? (a ++ b) i, toList_append, List.getElem?_append,
    ← toList_length a]
  by_cases h : i < a.toList.length
  · rw [if_pos h, if_pos (by exact h)]; exact toList_getElem?_eq_getElem? a i
  · rw [if_neg h, if_neg (by exact h)]; exact toList_getElem?_eq_getElem? b (i - a.toList.length)

theorem empty_append (bs : ByteString) : empty ++ bs = bs := by
  apply eq_of_toList_eq
  rw [toList_append, toList_empty, List.nil_append]

theorem append_empty (bs : ByteString) : bs ++ empty = bs := by
  apply eq_of_toList_eq
  rw [toList_append, toList_empty, List.append_nil]

/-- A literal's lookups are its list's: `Array.getElem?` does not reduce on a
constructed array, so this is how a literal byte is read positionally. -/
@[simp] theorem getElem?_literal (l : List UInt8) (i : Nat) : (literal l)[i]? = l[i]? := by
  rw [getElem?_eq_data, ← Array.getElem?_toList, data_toList_literal]

/-- `List.drop_drop`-shaped. -/
theorem drop_drop (bs : ByteString) {i j : Nat} :
    drop (drop bs j) i = drop bs (j + i) := by
  apply eq_of_toList_eq
  rw [toList_drop, toList_drop, toList_drop, List.drop_drop]

/-- A byte string is its take followed by its drop. -/
theorem take_append_drop (bs : ByteString) (n : Nat) :
    take bs n ++ drop bs n = bs := by
  apply eq_of_toList_eq
  rw [toList_append, toList_take, toList_drop]
  exact List.take_append_drop n bs.toList

/-! ### `extract`

`Array.extract` is the array's slice: a `min`-clamped length and a loop that
pushes the bytes it walks into a fresh array.  Its list view is what a proof
that reads a slice positionally needs, and the core characterisations of it
(`Array.toList_extract`, `Array.getElem_extract`, `Array.extract_append`) carry
`Classical.choice`.  The loop invariant below is the same correspondence without
that route: the loop's own recursion is the whole argument, so the slice facts
here rest on `propext` and `Quot.sound` alone. -/

/-- The loop invariant of `Array.extract`: from `start`, with `k` bytes left to
take, the accumulator's list view is the slice in front of it. -/
theorem extract_loop_toList (xs : Array UInt8) :
    ∀ (k start : Nat) (ys : Array UInt8), start + k ≤ xs.size →
      (Array.extract.loop xs k start ys).toList
        = ys.toList ++ (xs.toList.drop start).take k := by
  intro k
  induction k with
  | zero =>
      intro start ys _
      rw [Array.extract_loop_zero]
      simp
  | succ k ih =>
      intro start ys h
      have hlt : start < xs.size := by omega
      rw [Array.extract_loop_succ (h := hlt)]
      rw [ih (start + 1) (ys.push xs[start]) (by omega)]
      rw [Array.toList_push]
      have hlen : start < xs.toList.length := by simpa using hlt
      have hdrop : xs.toList.drop start
          = xs[start] :: xs.toList.drop (start + 1) := by
        rw [List.drop_eq_getElem_cons hlen]
        simp only [Array.getElem_toList]
      rw [hdrop, List.take_succ_cons]
      simp only [List.append_assoc, List.singleton_append]

/-- A slice to the end of the array is the list view dropped at the same index. -/
theorem extract_suffix_toList (xs : Array UInt8) (j : Nat) :
    (xs.extract j xs.size).toList = xs.toList.drop j := by
  rw [Array.extract]
  simp only [Nat.min_self]
  rw [Array.emptyWithCapacity_eq]
  by_cases hj : j ≤ xs.size
  · rw [extract_loop_toList]
    · simp only [List.nil_append]
      refine List.take_of_length_le ?_
      simp [List.length_drop]
    · exact Nat.le_of_eq (Nat.add_sub_of_le hj)
  · rw [Array.extract_loop_of_ge (h := by omega)]
    rw [List.drop_eq_nil_of_le (by simpa [Array.length_toList] using Nat.le_of_not_le hj)]

/-- The same correspondence on the carrier: the data view of the suffix. -/
theorem extract_suffix_data_toList (bs : ByteString) (j : Nat) :
    (bs.extract j bs.size).data.toList = bs.data.toList.drop j := by
  rw [ByteArray.data_extract]
  exact extract_suffix_toList bs.data j

/-- The suffix of a byte string is its `drop`: the equality a scanner needs to
hand a native slice to a specification stated over the carrier's `drop`. -/
theorem extract_suffix_eq_drop (bs : ByteString) (j : Nat) :
    bs.extract j bs.size = drop bs j := by
  apply eq_of_data_toList_eq
  rw [extract_suffix_data_toList, data_toList_drop]

/-- The list view of an arbitrary slice, the choice-free replacement for
`Array.toList_extract`.  The length is spelled `Nat.sub` so that it matches the
form `Array.extract`'s body produces on unfolding; `-` elaborates to `HSub.hSub`
and does not. -/
theorem extract_toList (xs : Array UInt8) (i j : Nat) :
    (xs.extract i j).toList = (xs.toList.drop i).take (Nat.sub j i) := by
  by_cases hji : j ≤ i
  · rw [Array.extract_empty_of_stop_le_start hji]
    have h0 : Nat.sub j i = 0 := Nat.sub_eq_zero_of_le hji
    rw [h0]
    rfl
  · rw [Array.extract, Array.emptyWithCapacity_eq]
    by_cases hj : j ≤ xs.size
    · rw [Nat.min_eq_left hj]
      rw [extract_loop_toList]
      · simp only [List.nil_append]
      · exact Nat.le_trans (Nat.le_of_eq (Nat.add_sub_of_le (by omega))) hj
    · rw [Nat.min_eq_right (by omega)]
      by_cases his : i ≤ xs.size
      · rw [extract_loop_toList]
        · simp only [List.nil_append]
          rw [List.take_of_length_le (by simp [List.length_drop]), List.take_of_length_le]
          rw [List.length_drop, Array.length_toList]
          exact Nat.sub_le_sub_right (Nat.le_of_not_le hj) i
        · exact Nat.le_trans (Nat.le_of_eq (Nat.add_sub_of_le his)) (Nat.le_refl _)
      · rw [Array.extract_loop_of_ge (h := Nat.le_of_not_le his)]
        rw [List.drop_eq_nil_of_le
          (by simpa [Array.length_toList] using Nat.le_of_not_le his)]
        simp

/-! ### `takeWhile` and `dropWhile` -/

/-- The longest prefix whose bytes satisfy `p`. -/
def takeWhile (bs : ByteString) (p : UInt8 → Bool) : ByteString :=
  literal (bs.data.toList.takeWhile p)

theorem data_toList_takeWhile (bs : ByteString) (p : UInt8 → Bool) :
    (takeWhile bs p).data.toList = bs.data.toList.takeWhile p := rfl

@[simp] theorem toList_takeWhile (bs : ByteString) (p : UInt8 → Bool) :
    (takeWhile bs p).toList = bs.toList.takeWhile p := by
  rw [toList_eq_data_toList, data_toList_takeWhile, toList_eq_data_toList]

/-- The rest after the longest prefix whose bytes satisfy `p`. -/
def dropWhile (bs : ByteString) (p : UInt8 → Bool) : ByteString :=
  literal (bs.data.toList.dropWhile p)

theorem data_toList_dropWhile (bs : ByteString) (p : UInt8 → Bool) :
    (dropWhile bs p).data.toList = bs.data.toList.dropWhile p := rfl

@[simp] theorem toList_dropWhile (bs : ByteString) (p : UInt8 → Bool) :
    (dropWhile bs p).toList = bs.toList.dropWhile p := by
  rw [toList_eq_data_toList, data_toList_dropWhile, toList_eq_data_toList]

/-- `List.takeWhile_cons`-shaped. -/
theorem takeWhile_cons (p : UInt8 → Bool) (a : UInt8) (bs : ByteString) :
    takeWhile (cons a bs) p = if p a then cons a (takeWhile bs p) else empty := by
  apply eq_of_toList_eq
  rw [toList_takeWhile, toList_cons, List.takeWhile_cons]
  by_cases hp : p a = true
  · simp [hp, toList_cons, toList_takeWhile]
  · simp [hp, toList_empty]

/-- `List.dropWhile_cons`-shaped. -/
theorem dropWhile_cons (p : UInt8 → Bool) (a : UInt8) (bs : ByteString) :
    dropWhile (cons a bs) p = if p a then dropWhile bs p else cons a bs := by
  apply eq_of_toList_eq
  rw [toList_dropWhile, toList_cons, List.dropWhile_cons]
  by_cases hp : p a = true
  · simp [hp, toList_dropWhile]
  · simp [hp, toList_cons]

theorem takeWhile_empty (p : UInt8 → Bool) : takeWhile empty p = empty := by
  apply eq_of_toList_eq
  rw [toList_takeWhile, toList_empty, List.takeWhile_nil]

theorem dropWhile_empty (p : UInt8 → Bool) : dropWhile empty p = empty := by
  apply eq_of_toList_eq
  rw [toList_dropWhile, toList_empty, List.dropWhile_nil]

/-! ### Membership -/

/-- A byte is a member when it occurs in the list. -/
instance instMembershipByteString : Membership UInt8 ByteString where
  mem := fun (bs : ByteString) (b : UInt8) => b ∈ bs.toList

/-- Membership is list membership, which is the instance's definition. -/
@[simp] theorem mem_def (b : UInt8) (bs : ByteString) : b ∈ bs ↔ b ∈ bs.toList := Iff.rfl

/-- `List.mem_cons`-shaped. -/
theorem mem_cons (a b : UInt8) (bs : ByteString) :
    b ∈ cons a bs ↔ b = a ∨ b ∈ bs := by
  simp only [mem_def, toList_cons, List.mem_cons]

theorem not_mem_empty (b : UInt8) : b ∉ (empty : ByteString) := by
  simp [mem_def, toList_empty]

theorem mem_append {a : UInt8} {x y : ByteString} :
    a ∈ x ++ y ↔ a ∈ x ∨ a ∈ y := by
  simp only [mem_def, toList_append, List.mem_append]

/-! ### The literal of a cons -/

theorem cons_ne_empty (b : UInt8) (bs : ByteString) : (cons b bs) ≠ empty := by
  intro h
  have h' := congrArg ByteArray.toList h
  rw [toList_cons, toList_empty] at h'
  exact List.cons_ne_nil b bs.toList h'

theorem cons_inj {a c : UInt8} {b d : ByteString} :
    (cons a b = cons c d) ↔ (a = c ∧ b = d) := by
  constructor
  · intro h
    have h' := congrArg ByteArray.toList h
    rw [toList_cons, toList_cons, List.cons.injEq] at h'
    exact ⟨h'.1, eq_of_toList_eq h'.2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem cons_append (b : UInt8) (a c : ByteString) :
    (cons b a) ++ c = cons b (a ++ c) := by
  apply eq_of_toList_eq
  rw [toList_append, toList_cons, toList_cons, toList_append]
  rfl

theorem literal_cons (b : UInt8) (l : List UInt8) :
    literal (b :: l) = cons b (literal l) := by
  apply eq_of_toList_eq
  rw [toList_literal, toList_cons, toList_literal]


/-! ### Further `List`-shaped facts the proofs rewrite with -/

theorem append_assoc (a b c : ByteString) : (a ++ b) ++ c = a ++ (b ++ c) := by
  apply eq_of_toList_eq
  rw [toList_append, toList_append, toList_append, toList_append, List.append_assoc]

theorem takeWhile_append_dropWhile (bs : ByteString) (p : UInt8 → Bool) :
    takeWhile bs p ++ dropWhile bs p = bs := by
  apply eq_of_toList_eq
  rw [toList_append, toList_takeWhile, toList_dropWhile]
  exact List.takeWhile_append_dropWhile

theorem takeWhile_append_of_pos {bs : ByteString} {p : UInt8 → Bool}
    (h : ∀ b ∈ bs, p b = true) (rest : ByteString) :
    takeWhile (bs ++ rest) p = bs ++ takeWhile rest p := by
  apply eq_of_toList_eq
  rw [toList_takeWhile, toList_append, toList_append, toList_takeWhile]
  exact List.takeWhile_append_of_pos (fun b hb => h b (by rw [mem_def]; exact hb))

theorem dropWhile_append_of_pos {bs : ByteString} {p : UInt8 → Bool}
    (h : ∀ b ∈ bs, p b = true) (rest : ByteString) :
    dropWhile (bs ++ rest) p = dropWhile rest p := by
  apply eq_of_toList_eq
  rw [toList_dropWhile, toList_append, toList_dropWhile]
  exact List.dropWhile_append_of_pos (fun b hb => h b (by rw [mem_def]; exact hb))

theorem mem_cons_self (a : UInt8) (bs : ByteString) : a ∈ (a +: bs) := by
  rw [mem_def, toList_cons]; exact List.mem_cons_self

theorem mem_cons_of_mem {a b : UInt8} {bs : ByteString} (h : a ∈ bs) : a ∈ (b +: bs) := by
  rw [mem_def, toList_cons]; rw [mem_def] at h; exact List.mem_cons_of_mem b h

theorem mem_singleton_self (a : UInt8) : a ∈ (a +: empty) := mem_cons_self a empty

theorem mem_singleton {a b : UInt8} : a ∈ (b +: empty) ↔ a = b := by
  rw [mem_def, toList_cons, toList_empty, List.mem_singleton]

theorem getElem?_cons_zero (b : UInt8) (bs : ByteString) : (b +: bs)[0]? = some b := by
  rw [← toList_getElem?_eq_getElem? (b +: bs) 0, toList_cons]; rfl

theorem getElem?_cons_succ (b : UInt8) (bs : ByteString) (i : Nat) :
    (b +: bs)[i + 1]? = bs[i]? := by
  rw [← toList_getElem?_eq_getElem? (b +: bs) (i + 1), toList_cons, List.getElem?_cons_succ,
    toList_getElem?_eq_getElem?]

theorem drop_succ_cons (b : UInt8) (bs : ByteString) (i : Nat) :
    (b +: bs).drop (i + 1) = bs.drop i := by
  apply eq_of_toList_eq
  rw [toList_drop, toList_cons, toList_drop, List.drop_succ_cons]

theorem drop_left (a b : ByteString) : (a ++ b).drop a.length = b := by
  apply eq_of_toList_eq
  rw [toList_drop, toList_append]
  rw [length_eq_size, ← toList_length]
  exact List.drop_left

/-- `List.head?_take`-shaped. -/
theorem head?_take (bs : ByteString) (n : Nat) :
    head? (take bs n) = if n = 0 then none else head? bs := by
  rw [head?_toList, toList_take, List.head?_take]
  by_cases h : n = 0
  · simp [h]
  · simp only [h, if_false, head?_toList]

/-- `List.head?_drop`-shaped. -/
theorem head?_drop (bs : ByteString) (n : Nat) : head? (drop bs n) = bs[n]? := by
  rw [head?_toList, toList_drop, List.head?_drop, toList_getElem?_eq_getElem?]
/-- `List.getElem?_cons_zero`'s empty counterpart: no index is in the empty byte
string. -/
@[simp] theorem getElem?_empty (i : Nat) : (empty : ByteString)[i]? = none := by
  rw [getElem?_eq_data, ← Array.getElem?_toList, data_toList_empty]
  simp

/-- `List.getElem_mem`-shaped: an in-bounds byte is a member. -/
theorem getElem_mem {bs : ByteString} {n : Nat} (h : n < bs.length) : bs[n] ∈ bs := by
  rw [mem_def]
  have hlen : n < bs.toList.length := by rwa [toList_length]
  have hmem : bs.toList[n] ∈ bs.toList := List.getElem_mem hlen
  have heq : bs.toList[n] = bs[n] := by
    have h1 : bs.toList[n]? = some (bs.toList[n]) := List.getElem?_eq_getElem hlen
    have h2 : bs[n]? = some (bs[n]) := getElem?_eq_getElem h
    have h3 : bs.toList[n]? = bs[n]? := toList_getElem?_eq_getElem? bs n
    rw [h1, h2] at h3
    exact Option.some.inj h3
  rwa [← heq]

end ByteString

end LeanLLVM.JSON
