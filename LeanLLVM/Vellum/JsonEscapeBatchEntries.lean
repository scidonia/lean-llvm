/-
The escape batch's entries, as the list record reads them back.

`@xl_batch` writes eight four-byte entries at `%o`, each `%base | cttz(%c)` with `%c`
the escape word with the previous slots' set lanes cleared; the record the list body
claims is about the entries **inside the population count**, because the eight-entry
reserve past the true count is written but not claimed.  Three facts about
`batchMem` state that boundary, and nothing wider:

* **the entry formula** (`batchMem_entry_value`): for `i < min (ctpop esc) 8`, the
  four bytes at `o + 4 * i` are `base + (setLanes esc)[i]`, i.e. the `i`-th position
  the escape word names, in increasing lane order;
* **the write is exactly eight entries at `o`** (`batchMem_read`): thirty-two bytes
  read back as the eight entries in the order the body stores them;
* **the frame** (`batchMem_unchanged`): every byte outside `o … o + 31` is the byte
  it was, which is what lets the reserve be unspecified.

The clearing chain is `%c = and (%c + -1) %c` and the sentinel `%esc | 2^63` keeps
`llvm.cttz` total; the two laws that turn the chain into a lane list
(`setLanes_clearLow`, `cttz_clearLow`) are B8's, imported rather than restated,
because both bodies run the same chain.
-/
import LeanLLVM.Vellum.JsonEscapeBatch
import LeanLLVM.Vellum.JsonB8Steps
import LeanLLVM.Vellum.BitLanes

namespace LeanLLVM.Vellum

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Vellum.BitLanes
open LeanLLVM.Vellum.JsonB8Steps

/-! ### The eight writes as a fold

`batchMem` is the body's eight `store i32` instructions as a nesting of
`writeBytes`.  The fold below is the same nesting read from the inside out, so the
entry at offset `4 * i` is the `i`-th `writeBytes` and the peeling induction has an
index to follow. -/

/-- The first `n` entries, in the order the body writes them. -/
def batchEntries (base : BitVec 32) (esc : BitVec 64) : Nat → List UInt8
  | 0 => []
  | n + 1 => batchEntries base esc n ++ batchBytes base esc n

/-- The batch's writes in increasing offset: `n` entries at `o, o + 4, …, o + 4 * (n-1)`. -/
def batchWrites (base : BitVec 32) (esc : BitVec 64) (o : Nat) : Nat → Mem → Mem
  | 0, mem => mem
  | n + 1, mem =>
      writeBytes (batchWrites base esc o n mem) (o + 4 * n) (batchBytes base esc n)

/-- One entry is four bytes. -/
theorem batchBytes_length (base : BitVec 32) (esc : BitVec 64) (i : Nat) :
    (batchBytes base esc i).length = 4 := rfl

/-- The fold at eight entries is `batchMem`: the same eight writes, entered from the
inside rather than the outside. -/
theorem batchWrites_eq_batchMem (base : BitVec 32) (esc : BitVec 64) (o : Nat)
    (mem : Mem) : batchWrites base esc o 8 mem = batchMem base esc o mem := rfl

/-- Entry `i` reads back as the bytes the body stored there: the writes after it are
above the read and the writes before it are below it. -/
theorem batchWrites_readBytes_entry (base : BitVec 32) (esc : BitVec 64) (o : Nat) :
    ∀ n i, i < n → ∀ mem : Mem,
      readBytes (batchWrites base esc o n mem) (o + 4 * i) 4 = some (batchBytes base esc i) := by
  intro n
  induction n with
  | zero =>
      intro i hi
      omega
  | succ n ih =>
      intro i hi mem
      rw [batchWrites]
      rcases Nat.lt_or_ge i n with hlt | hge
      · rw [readBytes_writeBytes_below (batchWrites base esc o n mem) (batchBytes base esc n)
          4 (o + 4 * i) (o + 4 * n) (by omega)]
        exact ih i hlt mem
      · have hie : i = n := by omega
        rw [hie]
        simpa [batchBytes_length] using readBytes_writeBytes_same
          (batchWrites base esc o n mem) (batchBytes base esc n)

/-- A byte outside the fold's writes is the byte it was. -/
theorem batchWrites_frame (base : BitVec 32) (esc : BitVec 64) (o : Nat) :
    ∀ n a, (a < o ∨ o + 4 * n ≤ a) → ∀ mem : Mem,
      readByte (batchWrites base esc o n mem) a = readByte mem a := by
  intro n
  induction n with
  | zero =>
      intro a _ mem
      rfl
  | succ n ih =>
      intro a h mem
      rw [batchWrites]
      rw [readByte_writeBytes_outside (batchWrites base esc o n mem) (batchBytes base esc n) (by
        rw [batchBytes_length]
        rcases h with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega))]
      exact ih a (by
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)) mem

/-- The fold's thirty-two bytes, in the order the body stores them. -/
theorem batchWrites_read (base : BitVec 32) (esc : BitVec 64) (o : Nat) :
    ∀ (n : Nat) (mem : Mem),
      readBytes (batchWrites base esc o n mem) o (4 * n) = some (batchEntries base esc n) := by
  intro n
  induction n with
  | zero =>
      intro mem
      rfl
  | succ n ih =>
      intro mem
      have h1 : readBytes (batchWrites base esc o (n + 1) mem) o (4 * n) =
          some (batchEntries base esc n) := by
        rw [batchWrites]
        rw [readBytes_writeBytes_below (batchWrites base esc o n mem) (batchBytes base esc n)
          (4 * n) o (o + 4 * n) (by omega)]
        exact ih mem
      have h2 : readBytes (batchWrites base esc o (n + 1) mem) (o + 4 * n) 4 =
          some (batchBytes base esc n) := by
        rw [batchWrites]
        simpa [batchBytes_length] using readBytes_writeBytes_same
          (batchWrites base esc o n mem) (batchBytes base esc n)
      rw [show 4 * (n + 1) = 4 * n + 4 from by omega, batchEntries]
      exact LeanLLVM.Vellum.JsonEntrySteps.readBytes_append _
        (4 * n) o _ 4 _ h1 h2

/-! ### The three laws at `batchMem` -/

/-- **Entry readback**: the four bytes at `o + 4 * i` are the `i`-th entry's. -/
theorem batchMem_entry (base : BitVec 32) (esc : BitVec 64) (o : Nat) (mem : Mem)
    {i : Nat} (hi : i < 8) :
    readBytes (batchMem base esc o mem) (o + 4 * i) 4 = some (batchBytes base esc i) := by
  rw [← batchWrites_eq_batchMem]
  exact batchWrites_readBytes_entry base esc o 8 i hi mem

/-- **Exactly eight entries at `o`**: thirty-two bytes, in the body's order. -/
theorem batchMem_read (base : BitVec 32) (esc : BitVec 64) (o : Nat) (mem : Mem) :
    readBytes (batchMem base esc o mem) o 32 = some (batchEntries base esc 8) := by
  rw [← batchWrites_eq_batchMem]
  simpa using batchWrites_read base esc o 8 mem

/-- **The frame**: a byte outside `o … o + 31` is the byte it was, so the reserve
the body touches is not part of any claim about its contents. -/
theorem batchMem_unchanged (base : BitVec 32) (esc : BitVec 64) (o : Nat) (mem : Mem)
    {a : Nat} (h : a < o ∨ o + 32 ≤ a) :
    readByte (batchMem base esc o mem) a = readByte mem a := by
  rw [← batchWrites_eq_batchMem]
  exact batchWrites_frame base esc o 8 a (by
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)) mem

/-! ### The entry's value

The sentinel `%esc | 2^63` makes `llvm.cttz` total at the zero word without moving
the least set lane below lane sixty-three, and the clearing chain's `i`-th word has
the `i`-th set lane least, so entry `i` is `%base` plus that lane. -/

/-- The sentinel's only lane is sixty-three. -/
theorem topBit_getLsbD (i : Nat) :
    (BitVec.ofInt 64 (-9223372036854775808) : BitVec 64).getLsbD i = decide (i = 63) := by
  rw [show (BitVec.ofInt 64 (-9223372036854775808) : BitVec 64) =
    BitVec.ofNat 64 (2 ^ 63) from by decide]
  rw [BitVec.getLsbD_ofNat]
  by_cases hi : i < 64
  · rw [decide_eq_true hi, Bool.true_and, Nat.testBit_two_pow]
    simp [eq_comm]
  · have hfalse : decide (i = 63) = false := decide_eq_false (by omega)
    rw [decide_eq_false hi, Bool.false_and, hfalse]

/-- The sentinel read at a lane. -/
theorem or_top_getLsbD (x : BitVec 64) (i : Nat) :
    (x ||| BitVec.ofInt 64 (-9223372036854775808)).getLsbD i
      = (x.getLsbD i || decide (i = 63)) := by
  rw [BitVec.getLsbD_or, topBit_getLsbD]

/-- `List.range 64` with lane sixty-three split off, as a list equation so the
rewrite does not reach the word's width. -/
theorem range_64 : List.range 64 = List.range 63 ++ [63] := by decide

/-- A word's set lanes below sixty-three, with lane sixty-three's own contribution
split off. -/
theorem setLanes_eq_base (x : BitVec 64) :
    setLanes x = (List.range 63).filter (fun i => x.getLsbD i) ++
      (if x.getLsbD 63 = true then [63] else []) := by
  unfold setLanes
  rw [range_64, List.filter_append]
  congr 1
  by_cases h : x.getLsbD 63 = true
  · rw [if_pos h]
    simp only [List.filter_cons, List.filter_nil, h]
    rfl
  · rw [if_neg h]
    have hf : x.getLsbD 63 = false := by simpa using h
    simp only [List.filter_cons, List.filter_nil, hf]
    rfl

/-- The sentinel adds lane sixty-three to the set lanes when the word does not have
it, and nothing otherwise. -/
theorem setLanes_or_top (esc : BitVec 64) :
    setLanes (esc ||| BitVec.ofInt 64 (-9223372036854775808)) =
      setLanes esc ++ (if esc.getLsbD 63 = true then [] else [63]) := by
  have hf : (List.range 63).filter (fun i => (esc ||| BitVec.ofInt 64 (-9223372036854775808)).getLsbD i)
      = (List.range 63).filter (fun i => esc.getLsbD i) := by
    apply List.filter_congr
    intro i hi
    rw [or_top_getLsbD]
    have hne : decide (i = 63) = false :=
      decide_eq_false (by have := List.mem_range.mp hi; omega)
    rw [hne, Bool.or_false]
  have htop : (esc ||| BitVec.ofInt 64 (-9223372036854775808)).getLsbD 63 = true := by
    rw [or_top_getLsbD]
    simp
  rw [setLanes_eq_base (esc ||| BitVec.ofInt 64 (-9223372036854775808)), setLanes_eq_base esc,
    hf, htop]
  by_cases h : esc.getLsbD 63 = true
  · rw [if_pos h, if_pos h]
    simp
  · rw [if_neg h, if_neg h]
    simp

/-- The sentinel does not move a set lane below it. -/
theorem setLanes_or_top_getD (esc : BitVec 64) {i : Nat} (hi : i < ctpop esc) :
    (setLanes (esc ||| BitVec.ofInt 64 (-9223372036854775808))).getD i 0 =
      (setLanes esc).getD i 0 := by
  rw [setLanes_or_top]
  have hlen : i < (setLanes esc).length := by rwa [ctpop_eq_setLanes_length] at hi
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hlen]

/-- The sentinel cannot lower the population count. -/
theorem ctpop_le_or_top (esc : BitVec 64) :
    ctpop esc ≤ ctpop (esc ||| BitVec.ofInt 64 (-9223372036854775808)) := by
  rw [ctpop_eq_setLanes_length, ctpop_eq_setLanes_length, setLanes_or_top,
    List.length_append]
  split <;> simp

/-- `-1` as the body writes it is the word arithmetic's `-1`. -/
theorem ofInt_neg_one : (BitVec.ofInt 64 (-1) : BitVec 64) = -1 := by decide

/-- The batch's chain is B8's clearing chain on the sentinel-augmented word. -/
theorem batchChain_eq_clearLow (esc : BitVec 64) (i : Nat) :
    batchChain esc i =
      clearLow (esc ||| BitVec.ofInt 64 (-9223372036854775808)) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [batchChain, clearLow, clearStep, ih, ofInt_neg_one]

/-- The chain's least set lane at step `i` is the escape word's `i`-th set lane. -/
theorem cttz_batchChain (esc : BitVec 64) {i : Nat} (hi : i < ctpop esc) :
    cttz (batchChain esc i) = (setLanes esc).getD i 0 := by
  have htop : i < ctpop (esc ||| BitVec.ofInt 64 (-9223372036854775808)) := by
    have := ctpop_le_or_top esc
    omega
  rw [batchChain_eq_clearLow,
    cttz_clearLow (w := esc ||| BitVec.ofInt 64 (-9223372036854775808)) htop,
    setLanes_or_top_getD esc hi]

/-- **The eight clearing steps drop exactly the eight lanes the entries used**: the
word the next batch starts from has the escape word's set lanes from the eighth on,
with the sentinel's own lane kept, which is what makes the emitted batch and the
residual word agree about the same set lanes. -/
theorem setLanes_batchChain_eight (esc : BitVec 64) :
    setLanes (batchChain esc 8) =
      (setLanes (esc ||| BitVec.ofInt 64 (-9223372036854775808))).drop 8 := by
  rw [batchChain_eq_clearLow, setLanes_clearLow]

/-- The trailing count at step `i`, read back as a number. -/
theorem batchCast_toNat (esc : BitVec 64) (i : Nat) :
    (batchCast esc i).toNat = cttz (batchChain esc i) := by
  have hle := cttz64_le (batchChain esc i)
  unfold batchCast
  rw [BitVec.toNat_ofNat]                    -- the store's `% 2 ^ 32`
  rw [BitVec.toNat_ofNat]                    -- the truncation's `% 2 ^ 64`
  have h64 : cttz (batchChain esc i) % 2 ^ 64 = cttz (batchChain esc i) :=
    Nat.mod_eq_of_lt (by omega)
  have h32 : cttz (batchChain esc i) % 2 ^ 32 = cttz (batchChain esc i) :=
    Nat.mod_eq_of_lt (by omega)
  rw [h64, Nat.mod_mod, h32]

/-- A set lane lies below the word's width. -/
theorem setLanes_getD_lt (esc : BitVec 64) (i : Nat) : (setLanes esc).getD i 0 < 64 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : (setLanes esc)[i]? with
  | none => simp
  | some k =>
      have hk : k ∈ setLanes esc := List.mem_of_getElem? h
      exact (mem_setLanes.mp hk).1

/-- **The entry formula**: inside the population count and the batch's eight slots,
entry `i` is the block base plus the `i`-th set lane.  `%base + lane` is below
`2^32` because the caller's stream base plus the block's sixty-four lanes is. -/
theorem batchBytes_eq (base : BitVec 32) (esc : BitVec 64) {i : Nat}
    (hi : i < min (ctpop esc) 8) (hcap : base.toNat + 64 ≤ 2 ^ 32) :
    batchBytes base esc i = natToBytes (base.toNat + (setLanes esc).getD i 0) 4 := by
  have hi' : i < ctpop esc := (Nat.lt_min.mp hi).1
  have hX : (setLanes esc).getD i 0 < 64 := setLanes_getD_lt esc i
  have hval : (base.toNat + (setLanes esc).getD i 0) % 2 ^ 32 =
      base.toNat + (setLanes esc).getD i 0 := Nat.mod_eq_of_lt (by omega)
  unfold batchBytes
  rw [batchCast_toNat, cttz_batchChain esc hi', BitVec.toNat_ofNat, Nat.mod_mod]
  simp only [hval]

/-- The two laws together, in the form the loop step consumes: the four bytes at
`o + 4 * i` are the position `%base + (setLanes esc)[i]`, in the stream's own
little-endian four-byte encoding. -/
theorem batchMem_entry_value (base : BitVec 32) (esc : BitVec 64) (o : Nat) (mem : Mem)
    {i : Nat} (hi : i < min (ctpop esc) 8) (hcap : base.toNat + 64 ≤ 2 ^ 32) :
    readBytes (batchMem base esc o mem) (o + 4 * i) 4 =
      some (natToBytes (base.toNat + (setLanes esc).getD i 0) 4) := by
  rw [batchMem_entry base esc o mem ((Nat.lt_min.mp hi).2), batchBytes_eq base esc hi hcap]

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Vellum.batchMem_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms batchMem_entry

/-- info: 'LeanLLVM.Vellum.batchMem_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms batchMem_read

/-- info: 'LeanLLVM.Vellum.batchMem_unchanged' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms batchMem_unchanged

/-- info: 'LeanLLVM.Vellum.batchMem_entry_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms batchMem_entry_value

/-- info: 'LeanLLVM.Vellum.setLanes_batchChain_eight' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms setLanes_batchChain_eight

end LeanLLVM.Vellum
