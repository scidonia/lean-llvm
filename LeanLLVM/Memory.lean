/-
Memory facts the loop proofs need.

The memory is an association list of addressed bytes.  A write replaces the
first cell at an address (or appends one); a read takes the first cell at an
address.  This module proves the facts a loop invariant rests on:

* a byte written at an address is read back there, every offset of a written
  sequence reads back its own byte, and writes at or above an address do not
  disturb addresses below it;
* a range that reads back reads back byte by byte, so a range the body asked for
  supplies the per-lane byte a byte-walking body reads at each offset;
* a little-endian round trip through `natToBytes` and `bytesToNat` recovers the
  value, so a 64-bit store followed by a 64-bit load at the same address
  returns the stored value.

Nothing here assumes alignment, and nothing here is about aliasing: only the
same-address and below-range cases are proved.  Overlapping stores are
deliberately left unspecified.
-/
import LeanLLVM.Semantics

namespace LeanLLVM

/-! ### Single-byte access -/

/-- A write at an address is read back at that address. -/
theorem readByte_writeByte_same (m : Mem) (addr : Nat) (b : UInt8) :
    readByte (writeByte m addr b) addr = some b := by
  induction m with
  | nil => simp [writeByte, readByte]
  | cons cell rest ih =>
      obtain ⟨a, b'⟩ := cell
      simp only [writeByte]
      split
      · rename_i h
        simp [readByte, h]
      · rename_i h
        simp only [readByte]
        rw [ite_eq_right h]
        exact ih

/-- A write at one address does not change another address. -/
theorem readByte_writeByte_other (m : Mem) {addr other : Nat} (b : UInt8)
    (h : addr ≠ other) : readByte (writeByte m addr b) other = readByte m other := by
  induction m with
  | nil => simp [writeByte, readByte, h]
  | cons cell rest ih =>
      obtain ⟨a, b'⟩ := cell
      simp only [writeByte]
      split
      · rename_i ha
        subst ha
        simp [readByte, h]
      · rename_i ha
        by_cases hao : a = other
        · subst hao
          simp [readByte]
        · simp [readByte, hao, ih]

/-- Writes at or above `start` do not disturb an address below `start`. -/
theorem readByte_writeBytes_below (m : Mem) :
    ∀ (bs : List UInt8) {start addr : Nat}, addr < start →
      readByte (writeBytes m start bs) addr = readByte m addr
  | [], _, _, _ => by simp only [writeBytes]
  | b :: bs, start, addr, h => by
      simp only [writeBytes]
      rw [readByte_writeBytes_below (writeByte m start b) bs (by omega)]
      exact readByte_writeByte_other m b (by omega)

/-- A sequence read entirely below `start` is unaffected by writes at `start`. -/
theorem readBytes_writeBytes_below (m : Mem) :
    ∀ (bs : List UInt8) (n addr start : Nat), addr + n ≤ start →
      readBytes (writeBytes m start bs) addr n = readBytes m addr n
  | bs, 0, _, _, _ => by simp only [readBytes]
  | bs, n + 1, addr, start, h => by
      simp only [readBytes]
      rw [readByte_writeBytes_below m bs (by omega)]
      cases hr : readByte m addr with
      | none => rfl
      | some b =>
          rw [readBytes_writeBytes_below m bs n (addr + 1) start (by omega)]

/-- A typed load of a range entirely below `start` is unaffected by writes at
`start`. -/
theorem loadValue_writeBytes_below (m : Mem) (bs : List UInt8) (w : Nat)
    (addr start : Nat) (h : addr + (w + 7) / 8 ≤ start) :
    loadValue (writeBytes m start bs) (.int w) addr = loadValue m (.int w) addr := by
  simp only [loadValue]
  split
  · rfl
  · rw [readBytes_writeBytes_below m bs ((w + 7) / 8) addr start h]

/-- Writes entirely below an address do not change it (the mirror of
`readByte_writeBytes_below`). -/
theorem readByte_writeBytes_above (m : Mem) :
    ∀ (bs : List UInt8) {start addr : Nat}, start + bs.length ≤ addr →
      readByte (writeBytes m start bs) addr = readByte m addr
  | [], _, _, _ => by simp only [writeBytes]
  | b :: bs, start, addr, h => by
      simp only [List.length_cons] at h
      rw [show writeBytes m start (b :: bs) =
        writeBytes (writeByte m start b) (start + 1) bs from rfl]
      rw [readByte_writeBytes_above (writeByte m start b) bs (by omega)]
      exact readByte_writeByte_other m b (by omega)

/-- A write sequence does not disturb an address outside its range, on either
side of it. -/
theorem readByte_writeBytes_outside (m : Mem) (bs : List UInt8) {start addr : Nat}
    (h : addr < start ∨ start + bs.length ≤ addr) :
    readByte (writeBytes m start bs) addr = readByte m addr := by
  rcases h with h | h
  · exact readByte_writeBytes_below m bs h
  · exact readByte_writeBytes_above m bs h

/-- A written byte is read back at the offset it was written at, independently
of the memory underneath.  This is the per-offset form of
`readBytes_writeBytes_same` for a single address, and it is what lets a write of
the same bytes at the same address on two different memories be compared byte by
byte. -/
theorem readByte_writeBytes_at (m : Mem) (bs : List UInt8) (start k : Nat)
    (hk : k < bs.length) :
    readByte (writeBytes m start bs) (start + k) = some (bs.getD k 0) := by
  induction bs generalizing start k m with
  | nil => exact absurd hk (Nat.not_lt_zero k)
  | cons b bs ih =>
      cases k with
      | zero =>
          show readByte (writeBytes (writeByte m start b) (start + 1) bs) start = some b
          rw [readByte_writeBytes_below (writeByte m start b) bs (by omega),
            readByte_writeByte_same]
      | succ k =>
          have hk' : k < bs.length := by simpa using hk
          show readByte (writeBytes (writeByte m start b) (start + 1) bs)
            (start + (k + 1)) = some (bs.getD k 0)
          rw [show start + (k + 1) = (start + 1) + k from by omega]
          exact ih (writeByte m start b) (start + 1) k hk'

/-! ### Byte sequences -/

/-- The bytes written at `addr` are read back at `addr`. -/
theorem readBytes_writeBytes_same (m : Mem) :
    ∀ (bs : List UInt8) {addr : Nat},
      readBytes (writeBytes m addr bs) addr bs.length = some bs
  | [], _ => by simp only [List.length_nil, writeBytes, readBytes]
  | b :: bs, addr => by
      have ih := readBytes_writeBytes_same (writeByte m addr b) bs (addr := addr + 1)
      simp only [List.length_cons, writeBytes]
      rw [show bs.length + 1 = Nat.succ bs.length from rfl]
      simp only [readBytes]
      rw [readByte_writeBytes_below (writeByte m addr b) bs (by omega)]
      rw [readByte_writeByte_same]
      simp only [ih]

/-- A range that reads back reads back byte by byte: the byte at offset `k` of a
range `readBytes` returned is the returned list's byte at `k`.  This is what
turns `readBytes mem p 32 = some block` into the per-lane read a byte-walking
body performs at `p + k`. -/
theorem readByte_of_readBytes {m : Mem} {addr n : Nat} {bs : List UInt8}
    (h : readBytes m addr n = some bs) {k : Nat} (hk : k < n) :
    readByte m (addr + k) = some (bs.getD k 0) := by
  induction n generalizing addr bs k with
  | zero => exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
      simp only [readBytes] at h
      split at h
      · cases h
      · rename_i b hb
        split at h
        · cases h
        · rename_i bs' hbs
          cases h
          cases k with
          | zero => simpa using hb
          | succ j =>
              rw [show addr + (j + 1) = addr + 1 + j from by omega]
              rw [ih hbs (by omega)]
              simp

/-- `UInt8.ofNat` at byte width. -/
theorem uint8_toNat_ofNat_mod (v : Nat) :
    (UInt8.ofNat (v % 256)).toNat = v % 256 := by
  rw [UInt8.toNat_ofNat']
  exact Nat.mod_eq_of_lt (Nat.mod_lt v (by decide))

/-- The low-byte decomposition used by `natToBytes`. -/
theorem mod_add_mul_pow (r B M : Nat) (hr : r < 256) (hM : 0 < M) :
    (r + 256 * B) % (256 * M) = r + 256 * (B % M) := by
  have hBM : B % M < M := Nat.mod_lt B hM
  have hbound : r + 256 * (B % M) < 256 * M := by
    have h2 : 256 + 256 * (B % M) = 256 * (B % M + 1) := by
      rw [Nat.mul_succ]
      exact Nat.add_comm 256 (256 * (B % M))
    have h4 : 256 * (B % M + 1) ≤ 256 * M :=
      Nat.mul_le_mul_left 256 (Nat.succ_le_of_lt hBM)
    omega
  have hsplit : r + 256 * B = (B / M) * (256 * M) + (r + 256 * (B % M)) := by
    conv =>
      lhs
      rw [← Nat.div_add_mod B M]
    rw [Nat.mul_add]
    have hprod : 256 * (M * (B / M)) = (B / M) * (256 * M) := by
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    rw [hprod]
    omega
  calc
    (r + 256 * B) % (256 * M)
        = ((B / M) * (256 * M) + (r + 256 * (B % M))) % (256 * M) := by rw [hsplit]
    _ = r + 256 * (B % M) := Nat.mul_add_mod_of_lt hbound

/-- The low-byte decomposition, right way round. -/
theorem mod_pow256_succ (v n : Nat) :
    v % 256 ^ (n + 1) = v % 256 + 256 * (v / 256 % 256 ^ n) := by
  rw [Nat.pow_succ']
  conv =>
    lhs
    rw [← Nat.div_add_mod v 256]
  rw [Nat.add_comm]
  exact mod_add_mul_pow (v % 256) (v / 256) (256 ^ n)
    (Nat.mod_lt v (by decide)) (Nat.pow_pos (by decide))

theorem natToBytes_length (v : Nat) (n : Nat) : (natToBytes v n).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp only [natToBytes, List.length_cons, ih]

/-- A little-endian round trip recovers the value. -/
theorem natToBytes_toNat (v : Nat) (n : Nat) :
    bytesToNat (natToBytes v n) = v % 256 ^ n := by
  induction n generalizing v with
  | zero => simp [natToBytes, bytesToNat, Nat.mod_one]
  | succ n ih =>
      simp only [natToBytes, bytesToNat, ih]
      rw [uint8_toNat_ofNat_mod]
      exact (mod_pow256_succ v n).symm

/-! ### Typed access -/

/-- A successful 64-bit load means the first of its eight bytes is present. -/
theorem readByte_ne_none_of_loadValue_64 {m : Mem} {addr : Nat} {v : Value}
    (h : loadValue m (.int 64) addr = some v) : readByte m addr ≠ none := by
  intro hb
  have hread : readBytes m addr 8 = none := by
    simpa only [show (8 : Nat) = 7 + 1 from rfl, readBytes, hb]
  have h8 : (64 + 7) / 8 = 8 := by decide
  simp only [loadValue, h8, if_neg (by decide : ¬ (64 = 0)), hread] at h
  cases h

/-- A 64-bit store followed by a 64-bit load at the same address returns the
stored value. -/
theorem loadValue_storeValue_64 (s : State) (x : BitVec 64) (addr : Nat) :
    storeValue s (.int 64) (.int 64 x) addr =
        some { s with mem := writeBytes s.mem addr (natToBytes x.toNat 8) } ∧
      loadValue (writeBytes s.mem addr (natToBytes x.toNat 8)) (.int 64) addr =
        some (.int 64 x) := by
  constructor
  · simp [storeValue]
  · have hb : bytesToNat (natToBytes x.toNat 8) = x.toNat := by
      rw [natToBytes_toNat]
      rw [show (256 : Nat) ^ 8 = 2 ^ 64 from by decide]
      exact Nat.mod_eq_of_lt x.isLt
    have h8 : (64 + 7) / 8 = 8 := by decide
    simp only [loadValue, h8, show (64 = 0) = False from by decide, ite_false]
    rw [show readBytes (writeBytes s.mem addr (natToBytes x.toNat 8)) addr 8 =
        some (natToBytes x.toNat 8) from by
      rw [← natToBytes_length x.toNat 8]
      exact readBytes_writeBytes_same s.mem (natToBytes x.toNat 8)]
    simp only [Option.some.injEq]
    rw [hb]
    congr 1
    apply BitVec.toNat_inj.mp
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

/-! ### Integer-lane vector access

`storeValue`'s vector arm writes `n * w / 8` bytes as `packLanes` of the lanes, and
`loadValue`'s integer-lane arm reads the same bytes back as `unpackLanes`.  The
facts below are that layout's own: the packing stays inside the bits its lanes
occupy, a lane read back at its own offset is that lane, the two are inverse on a
full lane list, and a store followed by a load at the same vector type returns what
was stored.  The last is the one that binds the two arms to each other — a load
layout that disagreed with the store's would leave every memory-crossing proof
wrong while each arm looked right on its own. -/

/-- The lane packing stays below the width its lanes occupy. -/
theorem packLanes_lt {w : Nat} (lanes : List (BitVec w)) :
    packLanes lanes < 2 ^ (lanes.length * w) := by
  induction lanes with
  | nil => simp [packLanes]
  | cons x xs ih =>
      have hx : x.toNat < 2 ^ w := x.isLt
      show x.toNat + 2 ^ w * packLanes xs < 2 ^ ((xs.length + 1) * w)
      rw [Nat.succ_mul, Nat.pow_add, Nat.mul_comm (2 ^ (xs.length * w)) (2 ^ w)]
      have h1 : x.toNat + 2 ^ w * packLanes xs < 2 ^ w + 2 ^ w * packLanes xs := by omega
      have h2 : 2 ^ w + 2 ^ w * packLanes xs ≤ 2 ^ w * 2 ^ (xs.length * w) := by
        rw [Nat.add_comm, ← Nat.mul_succ]
        exact Nat.mul_le_mul_left _ (by omega)
      omega

/-- Lane `k` of the packing, read back as a division.  No bound is needed: past the
end both sides are zero. -/
theorem packLanes_div {w : Nat} (lanes : List (BitVec w)) (k : Nat) :
    packLanes lanes / 2 ^ (k * w) =
      ((lanes[k]?).map BitVec.toNat).getD 0 + 2 ^ w * packLanes (lanes.drop (k + 1)) := by
  induction lanes generalizing k with
  | nil => simp [packLanes]
  | cons x xs ih =>
      cases k with
      | zero => simp [packLanes]
      | succ j =>
          have hxw : x.toNat < 2 ^ w := x.isLt
          show (x.toNat + 2 ^ w * packLanes xs) / 2 ^ ((j + 1) * w) =
            ((xs[j]?).map BitVec.toNat).getD 0 + 2 ^ w * packLanes (xs.drop (j + 1))
          rw [Nat.succ_mul, Nat.pow_add, Nat.mul_comm (2 ^ (j * w)) (2 ^ w),
            ← Nat.div_div_eq_div_mul]
          rw [Nat.mul_comm (2 ^ w) (packLanes xs),
            Nat.add_mul_div_right _ _ (Nat.two_pow_pos w)]
          rw [Nat.div_eq_of_lt hxw, Nat.zero_add]
          exact ih j

/-- A lane read back from a packed word at its own offset is that lane. -/
theorem bv_ofNat_add_mul_pow {w : Nat} (x : BitVec w) (R : Nat) :
    BitVec.ofNat w (x.toNat + 2 ^ w * R) = x := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_ofNat, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt x.isLt]

/-- `unpackLanes` inverts `packLanes` at the lane count the list has. -/
theorem unpackLanes_packLanes {w : Nat} (lanes : List (BitVec w)) :
    unpackLanes w lanes.length (packLanes lanes) = lanes := by
  unfold unpackLanes
  apply List.ext_getElem
  · simp
  · intro k h1 _
    rw [List.getElem_map, List.getElem_range]
    have hk : k < lanes.length := by simpa using h1
    rw [packLanes_div lanes k, List.getElem?_eq_getElem hk]
    simp only [Option.map_some, Option.getD_some]
    exact bv_ofNat_add_mul_pow (lanes[k]) _

/-- The `i1` packing is the mask packing: `storeValue` writes a lane vector with
`packLanes` where `bitcastMask` reads one with `lanesToNat`, and at one-bit lanes
the two folds are the same word. -/
theorem packLanes_eq_lanesToNat (l : List (BitVec 1)) : packLanes l = lanesToNat l := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
      show b.toNat + 2 ^ 1 * packLanes bs = (if b = 1 then 1 else 0) + 2 * lanesToNat bs
      rw [ih]
      have hb1 : b.toNat = (if b = 1 then 1 else 0) := by
        revert b
        decide
      rw [hb1]

/-- Packing a lane list and appending one lane: the appended lane sits at its own
offset. -/
theorem packLanes_append_singleton {w : Nat} (l : List (BitVec w)) (x : BitVec w) :
    packLanes (l ++ [x]) = packLanes l + 2 ^ (l.length * w) * x.toNat := by
  induction l with
  | nil => simp [packLanes]
  | cons y ys ih =>
      have hinner : 2 ^ w * (2 ^ (ys.length * w) * x.toNat)
          = 2 ^ (ys.length * w) * 2 ^ w * x.toNat := by
        rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ w) (2 ^ (ys.length * w))]
      show y.toNat + 2 ^ w * packLanes (ys ++ [x]) =
        (y.toNat + 2 ^ w * packLanes ys) + 2 ^ ((ys.length + 1) * w) * x.toNat
      rw [ih, Nat.succ_mul, Nat.pow_add, Nat.mul_add, Nat.add_assoc, hinner]

/-- Swapping the first two factors of a product. -/
theorem mul_swap_factors (A Q X : Nat) : A * (Q * X) = Q * (A * X) := by
  rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm A Q]

/-- Packing a concatenation: the suffix is scaled by the prefix's bit width. -/
theorem packLanes_append {w : Nat} (a b : List (BitVec w)) :
    packLanes (a ++ b) = packLanes a + 2 ^ (a.length * w) * packLanes b := by
  induction a with
  | nil => simp [packLanes]
  | cons x xs ih =>
      show x.toNat + 2 ^ w * packLanes (xs ++ b) =
        (x.toNat + 2 ^ w * packLanes xs) + 2 ^ ((xs.length + 1) * w) * packLanes b
      rw [ih, Nat.succ_mul, Nat.pow_add, Nat.mul_add,
        mul_swap_factors (2 ^ w) (2 ^ (xs.length * w)) (packLanes b),
        ← Nat.mul_assoc (2 ^ (xs.length * w)) (2 ^ w) (packLanes b), Nat.add_assoc]

/-- The lane packing of a concatenation: the suffix's lanes start above the
prefix's. -/
theorem lanesToNat_append (a b : List (BitVec 1)) :
    lanesToNat (a ++ b) = lanesToNat a + 2 ^ a.length * lanesToNat b := by
  induction a with
  | nil => simp [lanesToNat]
  | cons x xs ih =>
      show (if x = 1 then 1 else 0) + 2 * lanesToNat (xs ++ b) =
        ((if x = 1 then 1 else 0) + 2 * lanesToNat xs) + 2 ^ (xs.length + 1) * lanesToNat b
      rw [ih, Nat.mul_add, Nat.pow_succ,
        mul_swap_factors 2 (2 ^ xs.length) (lanesToNat b), Nat.mul_assoc, Nat.add_assoc]

/-- A word splits into its low `A` bits and the next `B` bits above them: the
division and remainder decomposition the packing inversion reads. -/
theorem mod_pow_mul (v A B : Nat) (hA : 0 < A) (hB : 0 < B) :
    v % A + A * (v / A % B) = v % (A * B) := by
  have hsplit : A * (v / A) + v % A = v := Nat.div_add_mod v A
  have hA' : v % A < A := Nat.mod_lt _ hA
  have hB' : v / A % B < B := Nat.mod_lt _ hB
  have hq : B * (v / A / B) + v / A % B = v / A := Nat.div_add_mod (v / A) B
  have hkey : A * (v / A) = A * B * (v / A / B) + A * (v / A % B) := by
    conv =>
      lhs
      rw [← hq]
    rw [Nat.mul_add, Nat.mul_assoc]
  have hr : A * (v / A % B) + v % A < A * B := by
    have h1 : A * (v / A % B) + v % A < A * (v / A % B) + A :=
      Nat.add_lt_add_left hA' _
    have h2 : A * (v / A % B) + A = A * (v / A % B + 1) := (Nat.mul_succ _ _).symm
    have h3 : A * (v / A % B + 1) ≤ A * B :=
      Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hB')
    omega
  have hv : v = A * B * (v / A / B) + (A * (v / A % B) + v % A) := by
    conv =>
      lhs
      rw [← hsplit]
    rw [hkey, Nat.add_assoc]
  conv =>
    rhs
    rw [hv]
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr, Nat.add_comm]

/-- `unpackLanes` produces exactly the lane count it is asked for. -/
theorem unpackLanes_length (w n v : Nat) : (unpackLanes w n v).length = n := by
  simp [unpackLanes]

/-- `packLanes` inverts `unpackLanes`: reading `n` lanes out of a word and packing
them back is the word's low `n * w` bits. -/
theorem packLanes_unpackLanes {w : Nat} (n v : Nat) :
    packLanes (unpackLanes w n v) = v % 2 ^ (n * w) := by
  induction n with
  | zero => simp [unpackLanes, packLanes, Nat.mod_one]
  | succ n ih =>
      have hstep : unpackLanes w (n + 1) v =
          unpackLanes w n v ++ [BitVec.ofNat w (v / 2 ^ (n * w))] := by
        show (List.range (n + 1)).map (fun k => BitVec.ofNat w (v / 2 ^ (k * w))) =
          (List.range n).map (fun k => BitVec.ofNat w (v / 2 ^ (k * w))) ++
            [BitVec.ofNat w (v / 2 ^ (n * w))]
        rw [List.range_succ, List.map_append]
        simp
      rw [hstep, packLanes_append_singleton, ih, unpackLanes_length]
      show v % 2 ^ (n * w) + 2 ^ (n * w) * (BitVec.ofNat w (v / 2 ^ (n * w))).toNat =
        v % 2 ^ ((n + 1) * w)
      rw [BitVec.toNat_ofNat, Nat.succ_mul, Nat.pow_add]
      exact mod_pow_mul v (2 ^ (n * w)) (2 ^ w) (Nat.two_pow_pos (n * w))
        (Nat.two_pow_pos w)

/-! ### The integer-lane vector load

The load's integer-lane arm: the accepting case, the refusal for a total width that
is not a whole number of bytes, the undefined case for absent bytes, and the store
round trip that binds it to the write side. -/

/-- The accepting case of the integer-lane vector load: the destination lanes are
the `n * w / 8` bytes read, split at the lane width.  The `<n x i8>` shape is the
arm above this one, which is why the lane width is not `8` here. -/
theorem loadValue_vec_int {m : Mem} {n w addr : Nat} (hw : w ≠ 8) (hb : n * w % 8 = 0)
    {bs : List UInt8} (hr : readBytes m addr (n * w / 8) = some bs) :
    loadValue m (.vec n (.int w)) addr = some (.vec n w (unpackLanes w n (bytesToNat bs))) := by
  simp only [loadValue]
  split
  · rw [hr]
  · rename_i h
    exact absurd hb h

/-- The refusal: a total bit width that is not a whole number of bytes has no byte
layout, the same rule `storeValue` applies on the write side. -/
theorem loadValue_vec_int_none {m : Mem} {n w addr : Nat} (hw : w ≠ 8)
    (hb : n * w % 8 ≠ 0) :
    loadValue m (.vec n (.int w)) addr = none := by
  simp only [loadValue]
  split
  · rename_i h
    exact absurd h hb
  · rfl

/-- Bytes the memory does not hold make the load undefined. -/
theorem loadValue_vec_int_of_readBytes_none {m : Mem} {n w addr : Nat} (hw : w ≠ 8)
    (hb : n * w % 8 = 0) (hr : readBytes m addr (n * w / 8) = none) :
    loadValue m (.vec n (.int w)) addr = none := by
  simp only [loadValue]
  split
  · rw [hr]
  · rename_i h
    exact absurd hb h

/-- A vector store followed by a vector load of the same type and address returns
what was stored — the two arms' layouts are one layout. -/
theorem loadValue_storeValue_vec (s : State) (n w : Nat) (lanes : List (BitVec w))
    (addr : Nat) (hw : w ≠ 8) (hlen : lanes.length = n) (hb : n * w % 8 = 0) :
    storeValue s (.vec n (.int w)) (.vec n w lanes) addr =
        some { s with
               mem := writeBytes s.mem addr (natToBytes (packLanes lanes) (n * w / 8)) } ∧
      loadValue (writeBytes s.mem addr (natToBytes (packLanes lanes) (n * w / 8)))
          (.vec n (.int w)) addr = some (.vec n w lanes) := by
  constructor
  · simp [storeValue, hlen, hb]
  · have hrb : readBytes (writeBytes s.mem addr (natToBytes (packLanes lanes) (n * w / 8)))
        addr (n * w / 8) = some (natToBytes (packLanes lanes) (n * w / 8)) := by
      have h := readBytes_writeBytes_same s.mem
        (natToBytes (packLanes lanes) (n * w / 8)) (addr := addr)
      rw [natToBytes_length] at h
      exact h
    rw [loadValue_vec_int hw hb hrb]
    congr 1
    have hbytes : bytesToNat (natToBytes (packLanes lanes) (n * w / 8)) = packLanes lanes := by
      rw [natToBytes_toNat]
      have h8 : 256 ^ (n * w / 8) = 2 ^ (n * w) := by
        rw [show (256 : Nat) = 2 ^ 8 from by decide, ← Nat.pow_mul,
          show (8 * (n * w / 8)) = n * w from by
            rw [Nat.mul_comm 8 (n * w / 8),
              Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hb)]]
      rw [h8]
      exact Nat.mod_eq_of_lt (by
        have := packLanes_lt lanes
        rw [hlen] at this
        exact this)
    rw [hbytes, ← hlen, unpackLanes_packLanes]

/-- A read splits into the part before an offset and the part from it: a range that
reads back reads back from any interior offset too. -/
theorem readBytes_split (m : Mem) (addr : Nat) :
    ∀ (n k : Nat) {bs : List UInt8}, readBytes m addr (n + k) = some bs →
      readBytes m addr n = some (bs.take n) ∧ readBytes m (addr + n) k = some (bs.drop n)
  | 0, k, bs, h => by
      refine ⟨rfl, ?_⟩
      simpa using h
  | n + 1, k, bs, h => by
      have hk : (n + 1) + k = (n + k) + 1 := by omega
      rw [hk] at h
      simp only [readBytes] at h ⊢
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i rest hrest
          cases h
          obtain ⟨h1, h2⟩ := readBytes_split m (addr + 1) n k hrest
          refine ⟨?_, ?_⟩
          · rw [h1]
            simp
          · rw [show addr + (n + 1) = (addr + 1) + n from by omega, List.drop_succ_cons]
            exact h2

/-! ### Byte sequences as lanes

`loadValue`'s `<n x i8>` arm builds its lanes with `BitVec.ofNat 8 b.toNat`;
`byteLanes` names that list, so the integer-lane arm and the byte arm can be stated
to agree on the same bytes rather than compared by inspection. -/

/-- A byte list as the lane vector an `<n x i8>` load binds. -/
def byteLanes (bs : List UInt8) : List (BitVec 8) := bs.map fun b => BitVec.ofNat 8 b.toNat

theorem byteLanes_length (bs : List UInt8) : (byteLanes bs).length = bs.length := by
  simp [byteLanes]

theorem byteLanes_append (a b : List UInt8) :
    byteLanes (a ++ b) = byteLanes a ++ byteLanes b := by
  simp [byteLanes]

/-- The byte arm's lanes, as a statement about `loadValue`. -/
theorem loadValue_vec_i8 {m : Mem} {n addr : Nat} {bs : List UInt8}
    (hr : readBytes m addr n = some bs) :
    loadValue m (.vec n (.int 8)) addr = some (.vec n 8 (byteLanes bs)) := by
  simp only [loadValue, hr, byteLanes]

/-- `bytesToNat` of a concatenation: the suffix is scaled by the prefix's byte
width. -/
theorem bytesToNat_append (a b : List UInt8) :
    bytesToNat (a ++ b) = bytesToNat a + 256 ^ a.length * bytesToNat b := by
  induction a with
  | nil => simp [bytesToNat]
  | cons x xs ih =>
      show x.toNat + 256 * bytesToNat (xs ++ b) =
        (x.toNat + 256 * bytesToNat xs) + 256 ^ (xs.length + 1) * bytesToNat b
      rw [ih, Nat.pow_succ]
      rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm (256 ^ xs.length) 256]
      rw [Nat.mul_assoc, Nat.add_assoc]

/-- A byte list's value stays below the width its bytes occupy. -/
theorem bytesToNat_lt (bs : List UInt8) : bytesToNat bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [bytesToNat]
  | cons x xs ih =>
      have hx : x.toNat < 256 := x.toNat_lt
      show x.toNat + 256 * bytesToNat xs < 256 ^ (xs.length + 1)
      rw [Nat.pow_succ', Nat.mul_comm 256 (256 ^ xs.length)]
      have h1 : x.toNat + 256 * bytesToNat xs < 256 + 256 * bytesToNat xs := by omega
      have h2 : 256 + 256 * bytesToNat xs ≤ 256 * 256 ^ xs.length := by
        rw [Nat.add_comm, ← Nat.mul_succ]
        exact Nat.mul_le_mul_left _ (by omega)
      omega

/-- Byte `k` of a byte list, read out of the value by division. -/
theorem bytesToNat_div_pow (bs : List UInt8) (k : Nat) :
    bytesToNat bs / 256 ^ k % 256 = ((bs[k]?).map UInt8.toNat).getD 0 := by
  induction bs generalizing k with
  | nil => simp [bytesToNat]
  | cons x xs ih =>
      cases k with
      | zero =>
          rw [Nat.pow_zero, Nat.div_one, List.getElem?_cons_zero]
          simp only [Option.map_some, Option.getD_some]
          show (x.toNat + 256 * bytesToNat xs) % 256 = x.toNat
          rw [Nat.add_mul_mod_self_left]
          exact Nat.mod_eq_of_lt x.toNat_lt
      | succ j =>
          show (x.toNat + 256 * bytesToNat xs) / 256 ^ (j + 1) % 256 =
            ((xs[j]?).map UInt8.toNat).getD 0
          rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul,
            Nat.mul_comm 256 (bytesToNat xs), Nat.add_mul_div_right _ _ (by decide : 0 < 256),
            Nat.div_eq_of_lt x.toNat_lt, Nat.zero_add]
          exact ih j

/-- The integer-lane reading of a byte list's value at lane width eight is the byte
lanes themselves: the two load arms agree on the same bytes. -/
theorem byteLanes_eq_unpackLanes {bs : List UInt8} {n : Nat} (hlen : bs.length = n) :
    unpackLanes 8 n (bytesToNat bs) = byteLanes bs := by
  apply List.ext_getElem
  · rw [unpackLanes_length, byteLanes_length, hlen]
  · intro k h1 _
    have hk : k < bs.length := by
      rw [unpackLanes_length, ← hlen] at h1
      exact h1
    simp only [unpackLanes, byteLanes, List.getElem_map, List.getElem_range]
    show BitVec.ofNat 8 (bytesToNat bs / 2 ^ (k * 8)) = BitVec.ofNat 8 (bs[k]).toNat
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (2 : Nat) ^ 8 = 256 from by decide,
      show 2 ^ (k * 8) = 256 ^ k from by
        rw [show (256 : Nat) = 2 ^ 8 from by decide, ← Nat.pow_mul, Nat.mul_comm],
      bytesToNat_div_pow bs k, List.getElem?_eq_getElem hk]
    simp only [Option.map_some, Option.getD_some]
    exact (Nat.mod_eq_of_lt (bs[k]).toNat_lt).symm

end LeanLLVM
