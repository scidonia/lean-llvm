/-
Memory facts the loop proofs need.

The memory is an association list of addressed bytes.  A write replaces the
first cell at an address (or appends one); a read takes the first cell at an
address.  This module proves the facts a loop invariant rests on:

* a byte written at an address is read back there, and writes at or above an
  address do not disturb addresses below it;
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

end LeanLLVM
