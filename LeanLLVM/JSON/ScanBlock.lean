/-
The block layer of the classifier: the mask the emitted body computes, and the
block operation that consumes it.

`maskOfList` is the scalar transition over a byte list — bit `k` is the decision
on byte `k` — and the lemmas below read that mask at a lane.  The module imports
`LeanLLVM.JSON.Bytes` alone, so the parser's proof chain never sees the block
layer.
-/
import LeanLLVM.JSON.Bytes

namespace LeanLLVM.JSON

/-- The classifier's mask set: the six structural characters of RFC 8259 §2
(`{`, `}`, `[`, `]`, `:`, `,`), plus the quote that delimits a string and the
backslash that begins its escapes.  The quote and the backslash are the
classifier's business, not RFC structural characters, and saying so is the point:
the mask exists to find string boundaries as well as structure. -/
def IsStructuralB (b : UInt8) : Bool :=
  decide (b = 0x22) || decide (b = 0x5C) || decide (b = 0x3A) || decide (b = 0x2C) ||
  decide (b = 0x7B) || decide (b = 0x7D) || decide (b = 0x5B) || decide (b = 0x5D)

/-- The scalar transition's per-byte decision: structural or RFC 8259 §2 `ws`. -/
def IsStructOrSpaceB (b : UInt8) : Bool := IsStructuralB b || IsSpaceB b

/-- The scalar transition, over a byte list: bit `k` is set iff byte `k` is
structural or whitespace.  Bytes past the end contribute nothing, so a list
shorter than 32 leaves the high bits zero and the fold is total. -/
def maskOfList (bs : List UInt8) : BitVec 32 :=
  BitVec.ofNat 32 <|
    (bs.zipIdx.take 32).foldl
      (fun acc (b, k) => if IsStructOrSpaceB b then acc ||| (1 <<< k) else acc) 0

/-- A 32-byte block: every byte addressable, length in the type.  Named `Block32`
rather than `Block`: this module sits in `namespace LeanLLVM.JSON` and
`LeanLLVM.Block` already exists (`Syntax.lean`), so a bare `Block` would be
shadowed or ambiguous in any file that opens both. -/
abbrev Block32 := Fin 32 → UInt8

/-- The scalar transition on a block. -/
def maskOf (block : Block32) : BitVec 32 := maskOfList (List.ofFn block)

/-- What crosses a block boundary.  `pos` is the index of the next unread byte;
nothing else crosses in this operation.  The in-string flag, the escape-run carry
and the pending-UTF-8 state are added with the scanner that consumes these masks,
and are not carried here as unused fields. -/
structure ScanState where
  pos : Nat
deriving DecidableEq, Repr

/-- The block operation's status.  `ok` means the block was classified in full;
`short` means the block was **not a full 32-byte block**, and no information was
produced.  `scanBlock` is total, so a `valid` outside `[0, 32]` takes this branch
as well; `scanBlock_correct`'s `valid ≤ 32` is what confines the theorem, not the
function.  Block availability, not validation: classification rejects nothing,
and the validation statuses the contract names belong to the scanner above this
operation. -/
inductive BlockStatus where
  | ok
  | short
deriving DecidableEq, Repr

/-- The information a block produces: one bit per byte position. -/
abbrev BlockInfo := BitVec 32

/-- The block operation. -/
def scanBlock (st : ScanState) (block : Block32) (valid : Nat) :
    ScanState × BlockInfo × BlockStatus :=
  if valid = 32 then ({ pos := st.pos + 32 }, maskOf block, .ok)
  else (st, 0, .short)

/-! ### Supporting lemmas -/

/-- Bit `k` of a single packed lane. -/
private theorem testBit_one_shiftLeft (i k : Nat) :
    (1 <<< i).testBit k = decide (i = k) := by
  rw [Nat.testBit_shiftLeft]
  by_cases h : i ≤ k
  · have hge : decide (k ≥ i) = true := decide_eq_true h
    rw [hge, Bool.true_and]
    rw [show (1 : Nat) = 2 ^ 0 from rfl, Nat.testBit_two_pow]
    by_cases hik : i = k
    · subst hik
      simp
    · rw [decide_eq_false (by omega : ¬ (0 = k - i)), decide_eq_false hik]
  · have hge : decide (k ≥ i) = false := decide_eq_false (by omega)
    rw [hge, Bool.false_and]
    exact (decide_eq_false (by omega : ¬ (i = k))).symm

/-- The accumulator's bit `k` after one packed lane is or-ed in. -/
private theorem testBit_or_one_shiftLeft (acc i k : Nat) :
    (acc ||| (1 <<< i)).testBit k = (acc.testBit k || decide (i = k)) := by
  rw [Nat.testBit_or, testBit_one_shiftLeft]

/-- One fold step, read at bit `k`. -/
private theorem step_testBit (acc : Nat) (b : UInt8) (i k : Nat) :
    ((if IsStructOrSpaceB b then acc ||| (1 <<< i) else acc)).testBit k =
      (acc.testBit k || (decide (i = k) && IsStructOrSpaceB b)) := by
  split
  · rename_i hc
    rw [testBit_or_one_shiftLeft, hc, Bool.and_true]
  · rename_i hc
    have hf : IsStructOrSpaceB b = false := by
      cases h : IsStructOrSpaceB b <;> simp_all
    rw [hf, Bool.and_false, Bool.or_false]

/-- The fold's bit `k` is the accumulator's bit `k`, or-ed with the decision on
each pair whose index is `k`. -/
private theorem fold_testBit (xs : List (UInt8 × Nat)) (acc k : Nat) :
    (xs.foldl
        (fun acc (b, k) => if IsStructOrSpaceB b then acc ||| (1 <<< k) else acc)
        acc).testBit k =
      (acc.testBit k ||
        xs.any (fun p => decide (p.2 = k) && IsStructOrSpaceB p.1)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons p xs ih =>
    obtain ⟨b, i⟩ := p
    rw [List.foldl_cons, List.any_cons, ih, step_testBit, Bool.or_assoc]

/-- A pair of the taken block addresses the byte it names and no other. -/
private theorem mem_zipIdx_take_iff {bs : List UInt8} {p : UInt8 × Nat} :
    p ∈ bs.zipIdx.take 32 ↔ p.2 < 32 ∧ bs[p.2]? = some p.1 := by
  rw [List.mem_iff_getElem?]
  constructor
  · rintro ⟨j, hj⟩
    simp only [List.getElem?_take] at hj
    split at hj
    · rename_i h32
      rw [List.getElem?_zipIdx] at hj
      cases hj' : bs[j]? with
      | none => rw [hj'] at hj; simp at hj
      | some x =>
        rw [hj'] at hj
        simp only [Option.map_some, Option.some.injEq] at hj
        subst hj
        refine ⟨by omega, ?_⟩
        simpa using hj'
    · simp at hj
  · rintro ⟨h32, hb⟩
    refine ⟨p.2, ?_⟩
    simp only [List.getElem?_take]
    split
    · rw [List.getElem?_zipIdx, hb]
      simp
    · omega

/-- Taking bytes before indexing is taking pairs after it. -/
private theorem zipIdx_take (l : List UInt8) (n : Nat) :
    (l.take n).zipIdx = l.zipIdx.take n := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_zipIdx, List.getElem?_take, List.getElem?_take, List.getElem?_zipIdx]
  by_cases hj : j < n <;> simp [hj]

/-- At index `k`, the block mask's `any` is the byte's own decision. -/
private theorem any_zipIdx_take {bs : List UInt8} {k : Nat} {b : UInt8}
    (hk : k < 32) (hb : bs[k]? = some b) :
    (bs.zipIdx.take 32).any (fun p => decide (p.2 = k) && IsStructOrSpaceB p.1) =
      IsStructOrSpaceB b := by
  by_cases hb' : IsStructOrSpaceB b = true
  · rw [hb', List.any_eq_true]
    exact ⟨(b, k), mem_zipIdx_take_iff.mpr ⟨hk, hb⟩, by simp [hb']⟩
  · have hbf : IsStructOrSpaceB b = false := by
      cases h : IsStructOrSpaceB b <;> simp_all
    rw [hbf, List.any_eq_false]
    intro p hp hpt
    rw [Bool.and_eq_true] at hpt
    obtain ⟨h1, h2⟩ := hpt
    obtain ⟨hpk, hpb⟩ := mem_zipIdx_take_iff.mp hp
    have hpk' : p.2 = k := of_decide_eq_true h1
    rw [hpk'] at hpb
    rw [hb] at hpb
    have hpb' : p.1 = b := by
      have := hpb
      simp at this
      exact this.symm
    rw [hpb', hbf] at h2
    exact absurd h2 (by decide)

/-! ### The theorems -/

/-- Bit `k` of the mask is the scalar decision on byte `k`. -/
theorem maskOfList_getLsbD {bs : List UInt8} {k : Nat} {b : UInt8}
    (hk : k < 32) (hb : bs[k]? = some b) :
    (maskOfList bs).getLsbD k = IsStructOrSpaceB b := by
  unfold maskOfList
  rw [BitVec.getLsbD_ofNat]
  have hdec : decide (k < 32) = true := decide_eq_true hk
  rw [hdec, Bool.true_and, fold_testBit, Nat.zero_testBit, Bool.false_or]
  exact any_zipIdx_take hk hb

/-- The block instance is the list instance at `List.ofFn`. -/
theorem maskOf_eq_maskOfList (block : Block32) :
    maskOf block = maskOfList (List.ofFn block) := rfl

/-- Bytes past the thirty-second do not affect the mask. -/
theorem maskOfList_take (bs : List UInt8) : maskOfList (bs.take 32) = maskOfList bs := by
  unfold maskOfList
  rw [zipIdx_take, List.take_take]
  simp

/-- A 32-byte list is the `List.ofFn` of its own indexing.  This is the bridge
`envForMask` needs: it reads an arbitrary `bs` of length 32, while the body
theorem is stated at `List.ofFn block`. -/
theorem ofFn_of_length {bs : List UInt8} (h : bs.length = 32) :
    List.ofFn (fun i : Fin 32 => bs[i.val]'(by omega)) = bs := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_ofFn]
  split
  · rename_i hj
    rw [List.getElem?_eq_getElem (by omega)]
  · rw [List.getElem?_eq_none_iff.mpr (by omega)]

/-- The per-byte identity the emitted range test stands for: `(b + (-9)) < 2`
(unsigned) is exactly "b is a tab or a newline". -/
theorem tab_newline_range (b : BitVec 8) :
    ((b + BitVec.ofInt 8 (-9)) < BitVec.ofNat 8 2) = (b = 9 ∨ b = 10) := by
  revert b
  decide

/-- `scanBlock_correct`.  A full block is classified in full and advances the
cursor by 32; a short block produces no information and leaves the state alone.
The second conjunct excludes an implementation that reports success on a partial
block: `ok` is reachable only at `valid = 32`, and every lane of the reported
mask is the scalar decision on that lane's byte. -/
theorem scanBlock_correct (st : ScanState) (block : Block32) (valid : Nat)
    (hvalid : valid ≤ 32) :
    (valid = 32 →
        scanBlock st block valid = ({ pos := st.pos + 32 }, maskOf block, .ok) ∧
        ∀ k : Fin 32, (maskOf block).getLsbD k.val = IsStructOrSpaceB (block k)) ∧
    (valid < 32 →
        scanBlock st block valid = (st, (0 : BlockInfo), .short)) := by
  constructor
  · intro h32
    subst h32
    constructor
    · simp [scanBlock]
    · intro k
      have hk : (List.ofFn block)[k.val]? = some (block k) := by
        rw [List.getElem?_eq_getElem (by simp : k.val < (List.ofFn block).length)]
        rw [List.getElem_ofFn]
      unfold maskOf
      exact maskOfList_getLsbD k.isLt hk
  · intro hlt
    simp [scanBlock, Nat.ne_of_lt hlt]

end LeanLLVM.JSON
