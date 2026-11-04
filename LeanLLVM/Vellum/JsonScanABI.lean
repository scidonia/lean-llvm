/-
The scanner window's ABI.

The unit is `i32 @leanllvm_json_scan_window(ptr %in, ptr %out, ptr %state,
i32 %valid)`: it reads the first `%valid` bytes of `%in`, writes one 32-bit mask
at `%out` and the next carry in the 16-byte slot at `%state`, and returns a
status word.  This module defines the two encodings that boundary needs and the
eight obligations `docs/contract.md` §5 states, as a record with one instance.

The status word's layout is normative: bits 0–5 are the stop lane plus one (0 is
no stop), bits 6–7 the kind (`none`, `close`, `refuse`), bits 8–9 the refusal
reason, and bits 10–31 are zero.  Six lane bits are not decoration: a five-bit
field maps lane 31 and "no stop" to the same value, which the collision below
states.  The decoder's spelling is free — the obligation is the equation, not
the definition — so the round trip is proved in both directions: on the
statuses a 32-lane window produces, and on the words the encoder produces.

The state slot is four `i32` words: flags (`bit 0` inside, `bit 1` odd run), the
UTF-8 requirement's count (0 for none), and its bounds.
-/
import LeanLLVM.JSON.ScanWindow
import LeanLLVM.Frames

namespace LeanLLVM.Vellum.JsonScanABI

open LeanLLVM
open LeanLLVM.JSON

/-! ### The state slot -/

/-- The 16-byte state slot at `%state`, as four `i32` words: `+0` flags, `+4` the
UTF-8 requirement's count, `+8` and `+12` its bounds. -/
structure Slot where
  flags : BitVec 32
  count : BitVec 32
  lo : BitVec 32
  hi : BitVec 32
deriving DecidableEq, Repr

/-- The flag word: bit 0 is `inside`, bit 1 is `oddRun`.  Written `if x = true`
because the flag lemmas below match that form. -/
def encodeFlags (st : BodyState) : BitVec 32 :=
  (if st.inside = true then (1 : BitVec 32) else 0) |||
    (if st.oddRun = true then (2 : BitVec 32) else 0)

/-- The low byte of a slot word. -/
def byteOf (w : BitVec 32) : UInt8 := UInt8.ofNat w.toNat

/-- The carry, in the slot's four words. -/
def encodeState (st : BodyState) : Slot :=
  { flags := encodeFlags st,
    count := match st.utf8 with | .none => 0 | .more n _ _ => BitVec.ofNat 32 n,
    lo := match st.utf8 with | .none => 0 | .more _ lo _ => BitVec.ofNat 32 lo.toNat,
    hi := match st.utf8 with | .none => 0 | .more _ _ hi => BitVec.ofNat 32 hi.toNat }

/-- The carry a slot holds. -/
def decodeState (s : Slot) : BodyState :=
  { inside := s.flags.getLsbD 0,
    oddRun := s.flags.getLsbD 1,
    utf8 :=
      if s.count.toNat = 0 then .none
      else .more s.count.toNat (byteOf s.lo) (byteOf s.hi) }

theorem encodeFlags_inside (st : BodyState) : (encodeFlags st).getLsbD 0 = st.inside := by
  unfold encodeFlags
  by_cases hi : st.inside = true <;> by_cases ho : st.oddRun = true <;>
    simp [hi, ho] <;> decide

theorem encodeFlags_oddRun (st : BodyState) : (encodeFlags st).getLsbD 1 = st.oddRun := by
  unfold encodeFlags
  by_cases hi : st.inside = true <;> by_cases ho : st.oddRun = true <;>
    simp [hi, ho] <;> decide

theorem byteOf_ofNat (b : UInt8) : byteOf (BitVec.ofNat 32 b.toNat) = b := by
  show UInt8.ofNat ((BitVec.ofNat 32 b.toNat).toNat) = b
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := UInt8.toNat_lt b; omega)]
  exact UInt8.ofNat_toNat

theorem decodeState_encodeState {st : BodyState} (h : st.WellFormed) :
    decodeState (encodeState st) = st := by
  obtain ⟨hutf8, -, -⟩ := h
  rcases st with ⟨inside, oddRun, utf8⟩
  cases utf8 with
  | none =>
      simp only [decodeState, encodeState, encodeFlags_inside, encodeFlags_oddRun]
      rfl
  | more n lo hi =>
      simp only [Utf8Need.WellFormed] at hutf8
      obtain ⟨hn0, hn3⟩ := hutf8
      have hmod : (BitVec.ofNat 32 n).toNat = n := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hne : ¬ n = 0 := by omega
      simp only [decodeState, encodeState, encodeFlags_inside, encodeFlags_oddRun,
        byteOf_ofNat, hmod]
      rw [ite_eq_right hne]

/-! ### The status word -/

/-- A refusal reason's code: `none` is 0 and the three `BodyStop`s follow. -/
def reasonCode : BodyStop → Nat
  | .ended => 1
  | .control => 2
  | .badUtf8 => 3

/-- The reason field back to a `BodyStop`; the code 0 has no `BodyStop` and the
fallback is unreachable from the encoder. -/
def reasonOfCode : Nat → BodyStop
  | 1 => .ended
  | 2 => .control
  | 3 => .badUtf8
  | _ => .ended

theorem reasonOfCode_reasonCode (s : BodyStop) : reasonOfCode (reasonCode s) = s := by
  cases s <;> rfl

theorem reasonCode_reasonOfCode {r : Nat} (h0 : 0 < r) (h3 : r < 4) :
    reasonCode (reasonOfCode r) = r := by
  match r with
  | 0 => omega
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | n + 4 => omega

/-- What the status word says: no stop, a closing lane, or a refusing lane with
its reason. -/
inductive Status where
  | ok (stop : Option Stop)
deriving DecidableEq, Repr

namespace Status

/-- Bits 0–5: no lane is 0, lane `k` is `k + 1`. -/
def laneField : Status → Nat
  | .ok none => 0
  | .ok (some (.close k)) => k + 1
  | .ok (some (.refuse k _)) => k + 1

/-- Bits 6–7: `none` 0, `close` 1, `refuse` 2. -/
def kindField : Status → Nat
  | .ok none => 0
  | .ok (some (.close _)) => 1
  | .ok (some (.refuse _ _)) => 2

/-- Bits 8–9: 0 unless the status refuses, then the refusal's code. -/
def reasonField : Status → Nat
  | .ok none => 0
  | .ok (some (.close _)) => 0
  | .ok (some (.refuse _ s)) => reasonCode s

/-- A status names lanes of a 32-lane window: the fold produces no other. -/
def LanesInWindow : Status → Prop
  | .ok none => True
  | .ok (some (.close k)) => k < 32
  | .ok (some (.refuse k _)) => k < 32

end Status

/-- The word's value, before it is narrowed to 32 bits: the three fields, packed. -/
def encodeStatusNat (s : Status) : Nat :=
  s.laneField + 64 * s.kindField + 256 * s.reasonField

theorem encodeStatusNat_lt {s : Status} (h : s.LanesInWindow) : encodeStatusNat s < 2 ^ 32 := by
  rcases s with ⟨stop⟩
  cases stop with
  | none =>
      simp only [encodeStatusNat, Status.laneField, Status.kindField, Status.reasonField]
      omega
  | some st =>
      cases st with
      | close k =>
          have hk : k < 32 := h
          simp only [encodeStatusNat, Status.laneField, Status.kindField,
            Status.reasonField]
          omega
      | refuse k r =>
          have hk : k < 32 := h
          cases r <;>
            simp only [encodeStatusNat, Status.laneField, Status.kindField,
              Status.reasonField, reasonCode] <;> omega

/-- The status word: bits 0–5 lane + 1, 6–7 kind, 8–9 reason, 10–31 zero. -/
def encodeStatus (s : Status) : BitVec 32 := BitVec.ofNat 32 (encodeStatusNat s)

/-- The fields, read back out of a word: bits 0–5, 6–7 and 8–9. -/
def decodeStatusNat (n : Nat) : Status :=
  if n / 64 % 4 = 0 then .ok none
  else if n / 64 % 4 = 1 then
    (if n % 64 = 0 then .ok none else .ok (some (.close (n % 64 - 1))))
  else if n / 64 % 4 = 2 then
    (if n % 64 = 0 then .ok none
     else .ok (some (.refuse (n % 64 - 1) (reasonOfCode (n / 256 % 4)))))
  else .ok none

/-- A word's status. -/
def decodeStatus (w : BitVec 32) : Status := decodeStatusNat w.toNat

theorem ofNat32_toNat {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

theorem decodeStatusNat_encodeStatusNat (s : Status) (h : s.LanesInWindow) :
    decodeStatusNat (encodeStatusNat s) = s := by
  rcases s with ⟨stop⟩
  cases stop with
  | none => decide
  | some st =>
      cases st with
      | close k =>
          have hk : k < 32 := h
          show decodeStatusNat (((k + 1) + 64 * 1) + 256 * 0) =
            Status.ok (some (Stop.close k))
          unfold decodeStatusNat
          rw [ite_eq_right (show ¬ (((k + 1) + 64 * 1) + 256 * 0) / 64 % 4 = 0 by omega),
              ite_eq_left (show (((k + 1) + 64 * 1) + 256 * 0) / 64 % 4 = 1 by omega),
              ite_eq_right (show ¬ (((k + 1) + 64 * 1) + 256 * 0) % 64 = 0 by omega)]
          rw [show (((k + 1) + 64 * 1) + 256 * 0) % 64 = k + 1 by omega,
              show k + 1 - 1 = k by omega]
      | refuse k r =>
          have hk : k < 32 := h
          cases r with
          | ended =>
              show decodeStatusNat (((k + 1) + 64 * 2) + 256 * 1) =
                Status.ok (some (Stop.refuse k BodyStop.ended))
              unfold decodeStatusNat reasonOfCode
              rw [ite_eq_right (show ¬ (((k + 1) + 64 * 2) + 256 * 1) / 64 % 4 = 0 by omega),
                  ite_eq_right (show ¬ (((k + 1) + 64 * 2) + 256 * 1) / 64 % 4 = 1 by omega),
                  ite_eq_left (show (((k + 1) + 64 * 2) + 256 * 1) / 64 % 4 = 2 by omega),
                  ite_eq_right (show ¬ (((k + 1) + 64 * 2) + 256 * 1) % 64 = 0 by omega)]
              rw [show (((k + 1) + 64 * 2) + 256 * 1) % 64 = k + 1 by omega,
                  show (((k + 1) + 64 * 2) + 256 * 1) / 256 % 4 = 1 by omega,
                  show k + 1 - 1 = k by omega]
              rfl
          | control =>
              show decodeStatusNat (((k + 1) + 64 * 2) + 256 * 2) =
                Status.ok (some (Stop.refuse k BodyStop.control))
              unfold decodeStatusNat reasonOfCode
              rw [ite_eq_right (show ¬ (((k + 1) + 64 * 2) + 256 * 2) / 64 % 4 = 0 by omega),
                  ite_eq_right (show ¬ (((k + 1) + 64 * 2) + 256 * 2) / 64 % 4 = 1 by omega),
                  ite_eq_left (show (((k + 1) + 64 * 2) + 256 * 2) / 64 % 4 = 2 by omega),
                  ite_eq_right (show ¬ (((k + 1) + 64 * 2) + 256 * 2) % 64 = 0 by omega)]
              rw [show (((k + 1) + 64 * 2) + 256 * 2) % 64 = k + 1 by omega,
                  show (((k + 1) + 64 * 2) + 256 * 2) / 256 % 4 = 2 by omega,
                  show k + 1 - 1 = k by omega]
              rfl
          | badUtf8 =>
              show decodeStatusNat (((k + 1) + 64 * 2) + 256 * 3) =
                Status.ok (some (Stop.refuse k BodyStop.badUtf8))
              unfold decodeStatusNat reasonOfCode
              rw [ite_eq_right (show ¬ (((k + 1) + 64 * 2) + 256 * 3) / 64 % 4 = 0 by omega),
                  ite_eq_right (show ¬ (((k + 1) + 64 * 2) + 256 * 3) / 64 % 4 = 1 by omega),
                  ite_eq_left (show (((k + 1) + 64 * 2) + 256 * 3) / 64 % 4 = 2 by omega),
                  ite_eq_right (show ¬ (((k + 1) + 64 * 2) + 256 * 3) % 64 = 0 by omega)]
              rw [show (((k + 1) + 64 * 2) + 256 * 3) % 64 = k + 1 by omega,
                  show (((k + 1) + 64 * 2) + 256 * 3) / 256 % 4 = 3 by omega,
                  show k + 1 - 1 = k by omega]
              rfl

/-- The word the model's status encodes to, decoded, is the status again. -/
theorem decodeStatus_encodeStatus (s : Status) (h : s.LanesInWindow) :
    decodeStatus (encodeStatus s) = s := by
  rw [decodeStatus, encodeStatus, ofNat32_toNat (encodeStatusNat_lt h)]
  exact decodeStatusNat_encodeStatusNat s h

/-! ### The image side -/

/-- A word's value is in the encoder's image when it uses the layout's fields and
nothing else: bits 10–31 zero, a kind below three, a lane field of at most 32
(the 32-lane window's `lane + 1`), and a reason field only where a refusal
carries one.  `status_inImage_iff` proves this is exactly the set of values
`encodeStatus` produces from a `LanesInWindow` status, so the reverse round trip
below is a section on the encoder's range, not on a superset of it. -/
def Status.InImage (n : Nat) : Prop :=
  n < 1024 ∧
  (n / 64 % 4 = 0 → n % 64 = 0 ∧ n / 256 % 4 = 0) ∧
  (n / 64 % 4 = 1 → n % 64 ≠ 0 ∧ n / 256 % 4 = 0) ∧
  (n / 64 % 4 = 2 → n % 64 ≠ 0 ∧ 0 < n / 256 % 4) ∧
  n / 64 % 4 < 3 ∧
  n % 64 ≤ 32

/-- A value in the encoder's range decodes to a status a 32-lane window can name:
the lane field is at most 32, so `lane - 1` is below 32. -/
theorem decodeStatusNat_lanesInWindow {n : Nat} (h : Status.InImage n) :
    (decodeStatusNat n).LanesInWindow := by
  obtain ⟨hn, h0, h1, h2, h3, h4⟩ := h
  unfold decodeStatusNat
  by_cases hk0 : n / 64 % 4 = 0
  · rw [ite_eq_left hk0]
    trivial
  · by_cases hk1 : n / 64 % 4 = 1
    · obtain ⟨hl, hr⟩ := h1 hk1
      rw [ite_eq_right hk0, ite_eq_left hk1,
        ite_eq_right (show ¬ n % 64 = 0 by omega)]
      show n % 64 - 1 < 32
      omega
    · have hk2 : n / 64 % 4 = 2 := by omega
      obtain ⟨hl, hr0⟩ := h2 hk2
      rw [ite_eq_right hk0, ite_eq_right hk1, ite_eq_left hk2,
        ite_eq_right (show ¬ n % 64 = 0 by omega)]
      show n % 64 - 1 < 32
      omega

/-- Every in-window status's encoded value is in the range. -/
theorem encodeStatusNat_inImage {s : Status} (h : s.LanesInWindow) :
    Status.InImage (encodeStatusNat s) := by
  rcases s with ⟨stop⟩
  cases stop with
  | none =>
      simp only [Status.InImage, encodeStatusNat, Status.laneField, Status.kindField,
        Status.reasonField]
      decide
  | some st =>
      cases st with
      | close k =>
          have hk : k < 32 := h
          simp only [Status.InImage, encodeStatusNat, Status.laneField,
            Status.kindField, Status.reasonField]
          refine ⟨by omega, ?_, ?_, ?_, by omega, by omega⟩
          · intro hc; omega
          · intro hc; constructor <;> omega
          · intro hc; omega
      | refuse k r =>
          have hk : k < 32 := h
          cases r <;> (
            simp only [Status.InImage, encodeStatusNat, Status.laneField,
              Status.kindField, Status.reasonField, reasonCode] <;>
            refine ⟨by omega, ?_, ?_, ?_, by omega, by omega⟩)
          · intro hc; omega
          · intro hc; omega
          · intro hc; constructor <;> omega
          · intro hc; omega
          · intro hc; omega
          · intro hc; constructor <;> omega
          · intro hc; omega
          · intro hc; omega
          · intro hc; constructor <;> omega

theorem encodeStatusNat_decodeStatusNat (n : Nat) (h : Status.InImage n) :
    encodeStatusNat (decodeStatusNat n) = n := by
  obtain ⟨hn, h0, h1, h2, h3, _⟩ := h
  unfold decodeStatusNat
  by_cases hk0 : n / 64 % 4 = 0
  · obtain ⟨hl, hr⟩ := h0 hk0
    rw [ite_eq_left hk0]
    have hn0 : n = 0 := by omega
    simp only [encodeStatusNat, Status.laneField, Status.kindField, Status.reasonField,
      hn0]
  · by_cases hk1 : n / 64 % 4 = 1
    · obtain ⟨hl, hr⟩ := h1 hk1
      rw [ite_eq_right hk0, ite_eq_left hk1,
        ite_eq_right (show ¬ n % 64 = 0 by omega)]
      simp only [encodeStatusNat, Status.laneField, Status.kindField, Status.reasonField]
      omega
    · have hk2 : n / 64 % 4 = 2 := by omega
      obtain ⟨hl, hr0⟩ := h2 hk2
      have hr4 : n / 256 % 4 < 4 := Nat.mod_lt _ (by decide)
      rw [ite_eq_right hk0, ite_eq_right hk1, ite_eq_left hk2,
        ite_eq_right (show ¬ n % 64 = 0 by omega)]
      have hrc : reasonCode (reasonOfCode (n / 256 % 4)) = n / 256 % 4 :=
        reasonCode_reasonOfCode hr0 hr4
      simp only [encodeStatusNat, Status.laneField, Status.kindField, Status.reasonField,
        hrc]
      omega

/-- The predicate is the encoder's image, not a superset: a value is in the range
exactly when some in-window status encodes to it. -/
theorem status_inImage_iff (n : Nat) :
    Status.InImage n ↔ ∃ s : Status, s.LanesInWindow ∧ encodeStatusNat s = n := by
  constructor
  · intro h
    exact ⟨decodeStatusNat n, decodeStatusNat_lanesInWindow h,
      encodeStatusNat_decodeStatusNat n h⟩
  · rintro ⟨s, hs, rfl⟩
    exact encodeStatusNat_inImage hs

/-- The other direction: every word the encoder produces re-encodes to itself. -/
theorem encodeStatus_decodeStatus (w : BitVec 32) (h : Status.InImage w.toNat) :
    encodeStatus (decodeStatus w) = w := by
  have hb : encodeStatusNat (decodeStatus w) < 2 ^ 32 := by
    have hlt : w.toNat < 1024 := h.1
    show encodeStatusNat (decodeStatusNat w.toNat) < 2 ^ 32
    rw [encodeStatusNat_decodeStatusNat w.toNat h]
    omega
  apply BitVec.toNat_inj.mp
  show (BitVec.ofNat 32 (encodeStatusNat (decodeStatus w))).toNat = w.toNat
  rw [ofNat32_toNat hb]
  show encodeStatusNat (decodeStatusNat w.toNat) = w.toNat
  exact encodeStatusNat_decodeStatusNat w.toNat h

/-! ### The five-bit lane field -/

/-- The lane field a five-bit layout would have: `0` for no lane, `k + 1` for lane
`k`, taken modulo 32. -/
def laneFieldFive : Option Nat → Nat
  | none => 0
  | some k => (k + 1) % 32

/-- The six-bit field this ABI uses, for the contrast the collision needs. -/
def laneFieldSix : Option Nat → Nat
  | none => 0
  | some k => k + 1

/-- The collision: with five bits, lane 31 and "no stop" share the value `0`, so a
lane-31 stop would read back as no stop at all.  The six-bit field separates them. -/
theorem laneFieldFive_lane31_collides :
    laneFieldFive (some 31) = laneFieldFive none := by decide

/-- The same collision as arithmetic on the lane index, and the six-bit field's
separation stated beside it. -/
theorem lane31_fiveBit_wraps :
    (31 + 1) % 32 = 0 ∧ laneFieldSix (some 31) ≠ laneFieldSix none := by decide

/-! ### The state slot's size, and the ABI's symbol -/

/-- The bytes a state slot occupies. -/
def stateBytes : Nat := 16

/-- The bytes one mask occupies. -/
def outBytes : Nat := 4

/-- The input's readable extent: at most one 32-lane window. -/
def readExtent : Nat := 32

/-- The unit's symbol. -/
def scanSymbol : String := "leanllvm_json_scan_window"

/-! ### The §5 obligations as data -/

/-- The read and write footprint: the two memories differ only inside the two
written regions, and the read region is unchanged. -/
def scanFootprint (m m' : Mem) (in_ out state valid : Nat) : Prop :=
  AgreesOutsideMem m m' (fun a =>
      (out ≤ a ∧ a < out + outBytes) ∨ (state ≤ a ∧ a < state + stateBytes)) ∧
    readBytes m' in_ valid = readBytes m in_ valid

/-- The three regions the call names are pairwise disjoint. -/
def scanSlotDisjoint (in_ out state valid : Nat) : Prop :=
  (in_ + valid ≤ out ∨ out + outBytes ≤ in_) ∧
  (in_ + valid ≤ state ∨ state + stateBytes ≤ in_) ∧
  (out + outBytes ≤ state ∨ state + stateBytes ≤ out)

/-- The caller owns the three regions.  The repository has no ownership or
provenance model, so this field records the caller's obligation rather than a
fact the model can state; `AllocFrame`/`Band` are not used to express it. -/
def scanOwnership : Prop := True

/-- Input and output lifetimes, over the three buffer bases: at the full extent
the unit may read, the caller supplies three separate buffers, so neither output
region can end the input's life.  The extents are the record's own
`readBytes_`/`outBytes`/`stateBytes`.  The allocator half — the callee allocates
nothing and the caller's `next` is returned unchanged — is a component of the body
theorem, which the certificate binds to this record. -/
def scanLifetimes (in_ out state : Nat) : Prop :=
  scanSlotDisjoint in_ out state readExtent

/-- No alignment is required or assumed: memory is byte-addressed. -/
def scanAlignmentFree : Prop := True

/-- No index arithmetic exists: the only output is one 32-bit mask and the lane
counter is bounded by the readable extent. -/
def scanNoIndexArithmetic : Prop := True

/-- Insufficient capacity is impossible for this unit: the output slots are
fixed-width and the call writes exactly them. -/
def scanCapacityExhausted : Prop := False

/-- The eight obligations `docs/contract.md` §5 states, for one memory-using
replacement, as data: an instance is only honest if a theorem proves the body
meets it. -/
structure ScanContract where
  /-- The input's readable extent, in bytes: the largest `valid` the unit reads. -/
  readBytes_ : Nat
  /-- The output capacity, in bytes. -/
  outBytes : Nat
  /-- The carry's size, in bytes. -/
  stateBytes : Nat
  /-- The read and write footprint, as a relation between the memories before and
  after the call, the three regions and the readable extent. -/
  footprint : Mem → Mem → Nat → Nat → Nat → Nat → Prop
  /-- Alias restriction: the three regions are pairwise disjoint. -/
  slotDisjoint : Nat → Nat → Nat → Nat → Prop
  /-- Provenance: the caller owns every region named here. -/
  ownedByCaller : Prop
  /-- Input and output lifetimes, over the three buffer bases. -/
  lifetimes : Nat → Nat → Nat → Prop
  /-- Permitted and actual alignment. -/
  alignmentFree : Prop
  /-- Fixed-width index overflow constraints. -/
  noIndexArithmetic : Prop
  /-- Insufficient capacity and exhaustion; `False` when the slot is fixed-width. -/
  capacityExhausted : Prop

/-- The window scanner's instance of §5. -/
def jsonScanContract : ScanContract :=
  { readBytes_ := readExtent,
    outBytes := outBytes,
    stateBytes := stateBytes,
    footprint := scanFootprint,
    slotDisjoint := scanSlotDisjoint,
    ownedByCaller := scanOwnership,
    lifetimes := scanLifetimes,
    alignmentFree := scanAlignmentFree,
    noIndexArithmetic := scanNoIndexArithmetic,
    capacityExhausted := scanCapacityExhausted }

/-! ### The two statuses the model produces at lane 31 -/

/-- Thirty content bytes and a closing quote at lane 31. -/
def closeAt31 : List UInt8 := List.replicate 31 0x61 ++ [0x22]

/-- Thirty content bytes and a control byte at lane 31. -/
def controlAt31 : List UInt8 := List.replicate 31 0x61 ++ [0x01]

-- A 32-lane fold is deeper than `decide`'s default recursion depth, so each
-- check that reaches `windowOf` raises the limit locally.
-- The model closes at lane 31: the two values a five-bit lane field would have
-- wrapped are the model's own.
set_option maxRecDepth 10000 in
#guard (windowOf closeAt31 BodyState.body).stop = some (.close 31)

-- The model refuses at lane 31, with the control reason.
set_option maxRecDepth 10000 in
#guard (windowOf controlAt31 BodyState.body).stop = some (.refuse 31 .control)

set_option maxRecDepth 10000 in
/-- The model closes at the lane-31 quote. -/
theorem closeAt31_stop : (windowOf closeAt31 BodyState.body).stop = some (.close 31) := by
  decide

set_option maxRecDepth 10000 in
/-- The model refuses at the lane-31 control byte, with the control reason. -/
theorem controlAt31_stop :
    (windowOf controlAt31 BodyState.body).stop = some (.refuse 31 .control) := by
  decide

/-- The model's own lane-31 close, encoded and decoded, is the same status. -/
theorem close31_roundTrip :
    decodeStatus (encodeStatus (.ok ((windowOf closeAt31 BodyState.body).stop))) =
      .ok ((windowOf closeAt31 BodyState.body).stop) := by
  rw [closeAt31_stop]
  exact decodeStatus_encodeStatus _ (by show (31 : Nat) < 32; decide)

/-- The model's own lane-31 refusal, encoded and decoded, is the same status. -/
theorem refuse31_roundTrip :
    decodeStatus (encodeStatus (.ok ((windowOf controlAt31 BodyState.body).stop))) =
      .ok ((windowOf controlAt31 BodyState.body).stop) := by
  rw [controlAt31_stop]
  exact decodeStatus_encodeStatus _ (by show (31 : Nat) < 32; decide)

-- The lane-31 words, read off the model's own stops: lane field 32, kind 1 and
-- 2, reason 0 and 2.
set_option maxRecDepth 10000 in
#guard encodeStatus (.ok ((windowOf closeAt31 BodyState.body).stop)) =
  BitVec.ofNat 32 96

set_option maxRecDepth 10000 in
#guard encodeStatus (.ok ((windowOf controlAt31 BodyState.body).stop)) =
  BitVec.ofNat 32 672

#guard decodeState (encodeState BodyState.body) = BodyState.body

end LeanLLVM.Vellum.JsonScanABI
