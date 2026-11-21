/-
The peel's staging family, proved at the peel's own values.

`JsonS1BlocksRefines` states the unit's exit compositions at the peel:
`s1BlocksFusedExit_run` and `s1BlocksAsciiExit_run` each take four facts about
what the peel hands the return — the merge bit `%or.cond191` (`hsilent`), the
staging the loop carried (`hstage`), the peel's own ASCII word as a staging
(`hstagePeel`), and the tail-byte arm's error bit as a staging (`hstageByte`) —
and `JsonS1BlocksShort` takes the first and the third at its own join.  This
module proves them at the peel's values, so the compositions' hypotheses are
discharged by the peel rather than assumed.

## The branch bit

`if.then103`'s terminator tests `%or.cond191`, the second of the block's two
select words: `%or.cond190` is `%tobool139`'s select of `%tobool141` and zero,
and `%or.cond191` is that word's select of `%tobool143` and zero.  So the bit is
set exactly when the gate word `%conv` is zero, the peel's own high-bit probe is
set, and the carried byte is non-zero
(`ifThen103Values_cond191_eq_one_iff`).  The probe is the peel's `%138`,
`ptestz` of the two windows' join against the high-bit mask, which is the
ASCII probe of the peel's `%or.i280`
(`ifThen103Values_ptz138_eq_asciiProbe`), so its being set is the block's
being all ASCII (`ifThen103Values_ptz138_ne_zero_iff`), and at the document's
own block that is `ifThen103Values_cond191_of_block`.  The three premises are
genuine trace facts about the loop's `%conv` and carried byte and about the
document's last block; `hsilent_fusedExit`, `hsilent_asciiExit` and
`hsilent_shortPeel` are the composition's own shapes at them.  The gate word is
the entry's `%conv`, the arm's bit 2 (`entryGate`), while the merge's own branch
at `if.end147` reads the arm's bit 1; the two are independent bits of the arm,
so a caller supplies each.  No module states `%conv`'s ride-through the phase
and the fused loop, so it is a premise here rather than a consequence.

## The staging the peel's ASCII word carries

`%or.i279` is the peel's join of its two windows into the carried ASCII word
(`%or.i280 = %137 ||| %136`, then `%or.i279 = %or.i280 ||| %ascii`).  Two things
follow, and `staging_of_peel` assembles them:

* the word has four lanes (`staging_of_peel`'s `ascii_len`);
* its bytes are high-clear exactly when the carried word's are and the peel's
  block's are (`asciiBytes_zipWith_or`, `zipWith_or_all_high_iff`), so the
  staging's `ascii_bytes` clause is the one the caller carried, at the block the
  peel adds (`blockHalfOr_high`).

The other three fields are the caller's, unchanged.
`ifThen103Values_or279_staging` is that statement at the peel's own twelve
segments, and `hstagePeel_fusedExit`, `hstagePeel_asciiExit` and
`hstagePeel_shortPeel` are the composition's shapes.

## The tail byte's error bit

`if.then164`'s `%or169500` is `%cmp155` or-ed with the last byte's table bit;
`staging_of_byte` is the same staging at that error word, from the caller's
`err_def` and the document's last byte (`err_def_tail`).
`lastByte_eq_klByte` reads that byte off the padded window at the arm's own
address, which is the one premise the byte arm still needs beyond the staging.

## The latch edge's zero staging

`AsciiTerm.exit` reaches `for.end101` from the phase's latch, where the ASCII
word and the accumulator are the `for.end101` phis' zero lanes.  Those lanes
stage the caller's document exactly when it is ASCII:
`staging_zero_of_ascii` — the ASCII word's bytes are the zero word's, the
accumulator's packed word is `klAll = 0` because the padded window is a valid
prefix (`skip_sound`, `klAll_zero_iff_klErrAll`), and the error bit is clear
because every ASCII byte is below the table's lead range.  The fused edge's
staging is not restated here: it is `JsonS1BlocksEntry.fused_end_staging`'s
three carries (`packLanes %ascii`, `packLanes %u8k`, and the error bit), the
loop's register-to-model identities, not the peel's.

## What this module does not supply

`hstageByte` in `JsonS1BlocksRefines` is stated for every readable byte
(`∀ last p, readBytes s.mem p 1 = some [last] → …`).  The peel can only supply
it at the arm's own address, `b + n - 1`: it reads that byte and nothing else,
and a byte of any other value sitting elsewhere in the caller's memory (the
emit region above the document, the staged stream) would demand the same
staging at that byte's value.  The statement here is therefore the one the arm
can prove, `hstageByte_fusedExit`/`hstageByte_asciiExit`, with the byte's
identity as the premise the call site has; narrowing the composition's
hypothesis to the arm's read is a shape change in that file, which this module
does not edit.
-/
import LeanLLVM.Refinement.JsonS1BlocksRefines
import LeanLLVM.Refinement.JsonS1BlocksStaging
import LeanLLVM.Refinement.JsonS1BlocksVerdict
import LeanLLVM.Refinement.JsonAsciiSkip

namespace LeanLLVM.Refinement.JsonS1BlocksPeelStaging

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.BitLanes
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1BlocksLoop
open LeanLLVM.Refinement.JsonS1BlocksExit
open LeanLLVM.Refinement.JsonS1BlocksTail
open LeanLLVM.Refinement.JsonS1BlocksCompose
open LeanLLVM.Refinement.JsonS1BlocksStaging
open LeanLLVM.Refinement.JsonS1BlocksVerdict
open LeanLLVM.Refinement.JsonS1BlocksRefines
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonUtf8Spec
open LeanLLVM.Refinement.JsonUtf8Steps
open LeanLLVM.Refinement.JsonUtf8IR (utf8Window utf8WinPrefix)

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### The peel's two select words

`if.then103`'s terminator tests a select of a select.  `ite_ite_bit_one_iff` and
`ite_bit_one_iff` are the BitVec shapes, and the two value lemmas instantiate
them at the bits the block computes: `%or.cond190` is
`%conv = 0 ∧ %138 ≠ 0`, and `%or.cond191` is that conjunction with
`%prev_ascii ≠ 0`. -/

/-- The nested selects at one-bit words. -/
theorem ite_ite_bit_one_iff (a b c : BitVec 1) :
    (if (if a = 1 then b else 0) = 1 then c else 0) = 1 ↔ (a = 1 ∧ b = 1 ∧ c = 1) := by
  rcases bit1_eq_zero_or_one a with ha | ha <;>
    rcases bit1_eq_zero_or_one b with hb | hb <;>
    rcases bit1_eq_zero_or_one c with hc | hc <;>
    subst ha <;> subst hb <;> subst hc <;> decide

/-- One select at one-bit words. -/
theorem ite_bit_one_iff (a b : BitVec 1) :
    (if a = 1 then b else 0) = 1 ↔ (a = 1 ∧ b = 1) := by
  rcases bit1_eq_zero_or_one a with ha | ha <;>
    rcases bit1_eq_zero_or_one b with hb | hb <;>
    subst ha <;> subst hb <;> decide

/-- The peel's `%or.i280` is the model's join of its two window words. -/
theorem ifThen103Values_or280_eq (n : BitVec 64) (b : Nat) (bs136 bs137 : List UInt8)
    (ascii : List (BitVec 64)) (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat)
    (conv prevAscii : BitVec 32) :
    (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
        prevAscii).or280 =
      List.zipWith (· ||| ·) (unpackLanes 64 4 (bytesToNat bs137))
        (unpackLanes 64 4 (bytesToNat bs136)) := rfl

/-- **The peel's inner select, `%or.cond190`.**  It is the gate's select of the
block's high-bit probe: `%conv = 0 ∧ %138 ≠ 0`. -/
theorem ifThen103Values_cond190_eq_one_iff (n : BitVec 64) (b : Nat)
    (bs136 bs137 : List UInt8) (ascii : List (BitVec 64))
    (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat)
    (conv prevAscii : BitVec 32) :
    (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
        prevAscii).cond190 = 1 ↔
      (conv = 0 ∧
        (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
          prevAscii).ptz138 ≠ 0) := by
  have h : (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent
      conv prevAscii).cond190 =
      (if evalICmp .eq conv 0 = 1 then
          evalICmp .ne (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv
            shr ent conv prevAscii).ptz138 0 else 0) := rfl
  rw [h, ite_bit_one_iff]
  simp only [evalICmp]
  rw [ofBool_eq_one_iff (p := conv = 0),
    ofBool_eq_one_iff (p := (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS
      andv shr ent conv prevAscii).ptz138 ≠ 0)]

/-- **The peel's first verdict bit, at the block's three bits.**  `%or.cond191`
is `(%conv = 0 ∧ %138 ≠ 0) ∧ %prev_ascii ≠ 0`. -/
theorem ifThen103Values_cond191_eq_one_iff (n : BitVec 64) (b : Nat)
    (bs136 bs137 : List UInt8) (ascii : List (BitVec 64))
    (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat)
    (conv prevAscii : BitVec 32) :
    (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
        prevAscii).cond191 = 1 ↔
      (conv = 0 ∧
        (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
          prevAscii).ptz138 ≠ 0 ∧
        prevAscii ≠ 0) := by
  have h : (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent
      conv prevAscii).cond191 =
      (if (if evalICmp .eq conv 0 = 1 then
          evalICmp .ne (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv
            shr ent conv prevAscii).ptz138 0 else 0) = 1
        then evalICmp .ne prevAscii 0 else 0) := rfl
  rw [h, ite_ite_bit_one_iff]
  simp only [evalICmp]
  rw [ofBool_eq_one_iff (p := conv = 0),
    ofBool_eq_one_iff (p := (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS
      andv shr ent conv prevAscii).ptz138 ≠ 0),
    ofBool_eq_one_iff (p := prevAscii ≠ 0)]

/-- `%or.cond191` reads as the value the block bound. -/
theorem lookupName_ifThen103Out_cond191 (env : Env) (v : IfThen103Values) :
    lookupName (ifThen103Out env v) "%or.cond191" = some (.int 1 v.cond191) := by
  tail_lk

/-! ### The block's own all-ASCII bit

The probe is the high-bit test of the peel's join, and the join packs to the
block's half-OR.  `blockHalfOr_high` is the other direction: a high-clear block
comes from a high-clear window. -/

/-- `%138` is the ASCII probe of the peel's join. -/
theorem ifThen103Values_ptz138_eq_asciiProbe (n : BitVec 64) (b : Nat)
    (bs136 bs137 : List UInt8) (ascii : List (BitVec 64))
    (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat)
    (conv prevAscii : BitVec 32) :
    (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
        prevAscii).ptz138 =
      asciiProbe (List.zipWith (· ||| ·) (unpackLanes 64 4 (bytesToNat bs137))
        (unpackLanes 64 4 (bytesToNat bs136))) := rfl

/-- **The peel's high-bit probe is set exactly on a non-ASCII join.** -/
theorem ifThen103Values_ptz138_ne_zero_iff (n : BitVec 64) (b : Nat)
    (bs136 bs137 : List UInt8) (ascii : List (BitVec 64))
    (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat)
    (conv prevAscii : BitVec 32) :
    (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
        prevAscii).ptz138 ≠ 0 ↔
      ∀ b' ∈ asciiBytes (List.zipWith (· ||| ·)
          (unpackLanes 64 4 (bytesToNat bs137))
          (unpackLanes 64 4 (bytesToNat bs136))), b'.toNat < 0x80 := by
  have hlen : (List.zipWith (· ||| ·) (unpackLanes 64 4 (bytesToNat bs137))
      (unpackLanes 64 4 (bytesToNat bs136))).length = 4 := by
    simp [List.length_zipWith, unpackLanes_length]
  rw [ifThen103Values_ptz138_eq_asciiProbe]
  constructor
  · intro hne
    rcases asciiProbe_eq_zero_or_one _ with h0 | h1
    · exact absurd h0 hne
    · exact (asciiProbe_eq_one_iff_asciiBytes _ hlen).mp h1
  · intro hall h0
    have h1 := (asciiProbe_eq_one_iff_asciiBytes _ hlen).mpr hall
    rw [h0] at h1
    exact absurd h1 (by decide)

/-- The peel's join packs to its block's half-OR, from the two window words. -/
theorem packLanes_peelBlock {bs136 bs137 : List UInt8}
    (h136 : bs136.length = 32) (h137 : bs137.length = 32) :
    packLanes (List.zipWith (· ||| ·) (unpackLanes 64 4 (bytesToNat bs137))
        (unpackLanes 64 4 (bytesToNat bs136))) =
      bytesToNat (List.zipWith (· ||| ·) bs136 bs137) := by
  rw [packLanes_zipWith_or (by rw [unpackLanes_length, unpackLanes_length]),
    packLanes_unpackLanes_bytesToNat bs137 h137,
    packLanes_unpackLanes_bytesToNat bs136 h136,
    bytesToNat_zipWith_or bs136 bs137 (by rw [h136, h137]), Nat.or_comm]

/-- A document block's half-OR is the two halves' byte join. -/
theorem blockHalfOr_eq_halves {bs : List UInt8} {k : Nat} {bs136 bs137 : List UInt8}
    (h136 : bs136 = (docBlock bs k).take 32)
    (h137 : bs137 = (docBlock bs k).drop 32) :
    blockHalfOr bs k = List.zipWith (· ||| ·) bs136 bs137 := by
  unfold blockHalfOr
  rw [h136, h137]

/-- **A high-clear window makes the block's half-OR high-clear.** -/
theorem blockHalfOr_high {bs : List UInt8} {k : Nat} (hk : k < blocksOf bs.length)
    (hp : ∀ x ∈ padded bs, x.toNat < 0x80) :
    ∀ x ∈ blockHalfOr bs k, x.toNat < 0x80 := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
  have hj32 : j < 32 := by
    rw [blockHalfOr_length bs hk] at hj
    exact hj
  rw [← getD_of_lt _ 0x00 (by rw [blockHalfOr_length bs hk]; exact hj32),
    blockHalfOr_getD bs hk hj32]
  refine (u8_or_lt _ _).mpr ⟨?_, ?_⟩
  · rw [docBlock_getD bs (bi := k) (m := j) (by omega)]
    exact padded_getD_high bs hp _
  · rw [docBlock_getD bs (bi := k) (m := 32 + j) (by omega)]
    exact padded_getD_high bs hp _

/-- The peel's probe at the block's bytes: `%138 ≠ 0` exactly when the block's
half-OR is all ASCII. -/
theorem ifThen103Values_ptz138_ne_zero_iff_block {bs : List UInt8} {k : Nat}
    {bs136 bs137 : List UInt8} (hk : k < blocksOf bs.length)
    (h136 : bs136 = (docBlock bs k).take 32)
    (h137 : bs137 = (docBlock bs k).drop 32)
    (n : BitVec 64) (b : Nat) (ascii : List (BitVec 64))
    (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat)
    (conv prevAscii : BitVec 32) :
    (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
        prevAscii).ptz138 ≠ 0 ↔
      ∀ x ∈ blockHalfOr bs k, x.toNat < 0x80 := by
  have hblen : (docBlock bs k).length = 64 := docBlock_length_of_lt bs hk
  have h136len : bs136.length = 32 := by rw [h136, List.length_take, hblen]; decide
  have h137len : bs137.length = 32 := by rw [h137, List.length_drop, hblen]
  have hpack := packLanes_peelBlock (bs136 := bs136) (bs137 := bs137) h136len h137len
  have hbytes : asciiBytes (List.zipWith (· ||| ·)
      (unpackLanes 64 4 (bytesToNat bs137))
      (unpackLanes 64 4 (bytesToNat bs136))) =
      List.zipWith (· ||| ·) bs136 bs137 := by
    unfold asciiBytes
    rw [hpack, ← show (List.zipWith (· ||| ·) bs136 bs137).length = 32 from by
      rw [List.length_zipWith, h136len, h137len, Nat.min_self],
      JsonUtf8Steps.natToBytes_bytesToNat]
  rw [ifThen103Values_ptz138_ne_zero_iff, hbytes, blockHalfOr_eq_halves h136 h137]

/-- **The peel's first verdict bit at its block's bytes.**  The three premises are
the block's: the gate word, the last block's being all ASCII, and the
carried byte. -/
theorem ifThen103Values_cond191_of_block {bs : List UInt8} {k : Nat}
    {bs136 bs137 : List UInt8} (hk : k < blocksOf bs.length)
    (h136 : bs136 = (docBlock bs k).take 32)
    (h137 : bs137 = (docBlock bs k).drop 32)
    (n : BitVec 64) (b : Nat) (ascii : List (BitVec 64))
    (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat)
    (conv prevAscii : BitVec 32)
    (hconv : conv = 0) (hprobe : ∀ x ∈ blockHalfOr bs k, x.toNat < 0x80)
    (hprev : prevAscii ≠ 0) :
    (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
        prevAscii).cond191 = 1 :=
  (ifThen103Values_cond191_eq_one_iff n b bs136 bs137 ascii st0 st9 st15 prevS andv
    shr ent conv prevAscii).mpr
    ⟨hconv, (ifThen103Values_ptz138_ne_zero_iff_block hk h136 h137 _ _ _ _ _ _ _ _
      _ _ _ _).mpr hprobe, hprev⟩

/-! ### The peel's ASCII word as a staging

`%or.i279` is `%or.i280 ||| %ascii`; the bytes of an `|||` are the `|||` of the
bytes (`natToBytes_or`, `asciiBytes_zipWith_or`), and a byte list is all-ASCII
exactly when both factors are (`zipWith_or_all_high_iff`).  So the peel's word
stages the document exactly when the carried word did, for a block of the
document's padded window. -/

/-- The little-endian encoding of an `|||` is the byte join. -/
theorem natToBytes_or (x y : Nat) :
    ∀ n : Nat, natToBytes (x ||| y) n =
      List.zipWith (· ||| ·) (natToBytes x n) (natToBytes y n)
  | 0 => rfl
  | n + 1 => by
      have h256 : (256 : Nat) = 2 ^ 8 := by decide
      show UInt8.ofNat ((x ||| y) % 256) ::
          natToBytes ((x ||| y) / 256) n =
        (UInt8.ofNat (x % 256) ||| UInt8.ofNat (y % 256)) ::
          List.zipWith (· ||| ·) (natToBytes (x / 256) n) (natToBytes (y / 256) n)
      rw [h256, Nat.or_mod_two_pow, UInt8.ofNat_or]
      congr 1
      rw [Nat.or_div_two_pow]
      exact natToBytes_or (x / 256) (y / 256) n

/-- **A word's byte view of an `|||` is the byte join.** -/
theorem asciiBytes_zipWith_or {a b : List (BitVec 64)} (h : a.length = b.length) :
    asciiBytes (List.zipWith (· ||| ·) a b) =
      List.zipWith (· ||| ·) (asciiBytes a) (asciiBytes b) := by
  unfold asciiBytes
  rw [packLanes_zipWith_or h, natToBytes_or]

/-- **A byte join is all-ASCII exactly when both factors are.** -/
theorem zipWith_or_all_high_iff (a b : List UInt8) (h : a.length = b.length) :
    (∀ x ∈ List.zipWith (· ||| ·) a b, x.toNat < 0x80) ↔
      (∀ x ∈ a, x.toNat < 0x80) ∧ (∀ x ∈ b, x.toNat < 0x80) := by
  induction a generalizing b with
  | nil =>
      cases b with
      | nil => simp
      | cons y ys => simp at h
  | cons x xs ih =>
      cases b with
      | nil => simp at h
      | cons y ys =>
          have h' : xs.length = ys.length := by simpa using h
          rw [List.zipWith_cons_cons, List.forall_mem_cons, List.forall_mem_cons,
            List.forall_mem_cons, ih ys h', u8_or_lt]
          exact ⟨fun h => ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩,
            fun h => ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩⟩

/-- **The peel's ASCII word stages the caller's document.**  The fields other
than `ascii_bytes` are the caller's; the word's bytes are the block's join with
the carried word's, so `ascii_bytes` is the caller's clause at the block. -/
theorem staging_of_peel {bs : List UInt8} {n nb k : Nat} {gate : Bool}
    {ascii u8k : List (BitVec 64)} {err : BitVec 1} {or280 : List (BitVec 64)}
    (h : VerdictStaging ascii u8k bs n nb gate err)
    (hk : k < blocksOf bs.length)
    (h280len : or280.length = 4)
    (h280 : packLanes or280 = bytesToNat (blockHalfOr bs k)) :
    VerdictStaging (List.zipWith (· ||| ·) or280 ascii) u8k bs n nb gate err := by
  have hlen : (List.zipWith (· ||| ·) or280 ascii).length = ascii.length := by
    rw [List.length_zipWith, h280len, h.ascii_len, Nat.min_self]
  have hbytes280 : asciiBytes or280 = blockHalfOr bs k := by
    unfold asciiBytes
    rw [h280, ← blockHalfOr_length bs hk, JsonUtf8Steps.natToBytes_bytesToNat]
  have hsplit := asciiBytes_zipWith_or (a := or280) (b := ascii)
    (by rw [h280len, h.ascii_len])
  refine ⟨by rw [hlen, h.ascii_len], h.acc_len, h.hn, h.hnb, ?_, h.acc_pack,
    h.err_def⟩
  rw [hsplit, hbytes280,
    zipWith_or_all_high_iff _ _ (by rw [blockHalfOr_length bs hk, asciiBytes_length])]
  constructor
  · rintro ⟨-, hascii⟩
    exact h.ascii_bytes.mp hascii
  · intro hdoc
    exact ⟨blockHalfOr_high hk ((ascii_padded_iff bs).mp hdoc),
      h.ascii_bytes.mpr hdoc⟩

/-- **The peel's own twelve segments' ASCII word as a staging.**  The block is the
document's `k`-th, whose halves are the two windows the peel reads, and `%or.i279`
is the peel's join of those windows into the carried word. -/
theorem ifThen103Values_or279_staging {bs : List UInt8} {n nb k : Nat} {gate : Bool}
    {ascii u8k : List (BitVec 64)} {err : BitVec 1} {bs136 bs137 : List UInt8}
    (hstage : VerdictStaging ascii u8k bs n nb gate err)
    (hsucc : k + 1 = blocksOf bs.length)
    (h136 : bs136 = (docBlock bs k).take 32)
    (h137 : bs137 = (docBlock bs k).drop 32)
    (nv : BitVec 64) (b : Nat) (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat)
    (conv prevAscii : BitVec 32) (hshr : shr.toNat = k) :
    VerdictStaging
      (ifThen103Values nv b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
        prevAscii).or279 u8k bs n nb gate err := by
  have hk : k < blocksOf bs.length := by omega
  have hblen : (docBlock bs k).length = 64 := docBlock_length_of_lt bs hk
  have h136len : bs136.length = 32 := by rw [h136, List.length_take, hblen]; decide
  have h137len : bs137.length = 32 := by rw [h137, List.length_drop, hblen]
  have h280 : packLanes (List.zipWith (· ||| ·) (unpackLanes 64 4 (bytesToNat bs137))
      (unpackLanes 64 4 (bytesToNat bs136))) = bytesToNat (blockHalfOr bs k) := by
    rw [packLanes_peelBlock h136len h137len, blockHalfOr_eq_halves h136 h137]
  have hor279 : (ifThen103Values nv b bs136 bs137 ascii st0 st9 st15 prevS andv shr
      ent conv prevAscii).or279 =
      List.zipWith (· ||| ·)
        (List.zipWith (· ||| ·) (unpackLanes 64 4 (bytesToNat bs137))
          (unpackLanes 64 4 (bytesToNat bs136))) ascii := rfl
  rw [hor279]
  exact staging_of_peel hstage hk (by simp [unpackLanes_length]) h280

/-! ### The tail byte's error bit

The byte arm's error word is `%cmp155 ||| lastByteBits`, and `err_def_tail`
already states that bit's reading at the document's last byte. -/

/-- `lastByteBits` at the arm's byte is the stage's `utf8TailBit`. -/
theorem lastByteBits_ofNat_toBitVec (last : UInt8) :
    lastByteBits (BitVec.ofNat 8 last.toNat) = utf8TailBit last.toBitVec := by
  have hb : BitVec.ofNat 8 last.toNat = last.toBitVec := by
    show BitVec.ofNat 8 last.toBitVec.toNat = last.toBitVec
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [lastByteBits_eq_utf8TailBit, hb]

/-- **The staging at the tail byte's error word.**  The caller's `err_def` and the
document's last byte give the or-ed arm's. -/
theorem staging_of_byte {bs : List UInt8} {n nb : Nat} {gate : Bool}
    {ascii u8k : List (BitVec 64)} {err : BitVec 1}
    (h : VerdictStaging ascii u8k bs n nb gate err)
    (last : UInt8) (hn0 : n ≠ 0) (hlast : last = klByte bs (n - 1)) :
    VerdictStaging ascii u8k bs n nb gate
      (evalICmp .eq (ptestzU8k u8k) 0 ||| lastByteBits (BitVec.ofNat 8 last.toNat)) := by
  refine ⟨h.ascii_len, h.acc_len, h.hn, h.hnb, h.ascii_bytes, h.acc_pack, ?_⟩
  rw [lastByteBits_ofNat_toBitVec]
  exact err_def_tail bs n u8k _ last hn0 h.acc_len hlast rfl

/-- **The window's byte at an offset**: the padded window read at `b` answers the
one-byte read at `b + q`. -/
theorem readBytes_padded_byte (mem : Mem) (bs : List UInt8) (b q : Nat)
    (h : readBytes mem b (64 * blocksOf bs.length) = some (padded bs))
    (hq : q < 64 * blocksOf bs.length) :
    readBytes mem (b + q) 1 = some [(padded bs).getD q 0x00] := by
  have hlen : (padded bs).length = 64 * blocksOf bs.length := padded_length bs
  have hq1 : readBytes mem b (q + 1) = some ((padded bs).take (q + 1)) :=
    (readBytes_split mem b (q + 1) (64 * blocksOf bs.length - (q + 1)) (by
      rw [Nat.add_sub_cancel' (by omega)]
      exact h)).1
  obtain ⟨-, hbyte⟩ := readBytes_split mem b q 1 hq1
  rw [hbyte]
  congr 1
  rw [List.drop_take, show (q + 1 - q : Nat) = 1 from by omega,
    List.drop_eq_getElem_cons (by rw [hlen]; exact hq), List.take_one]
  simp only [List.head?_cons, Option.toList_some, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [hlen]; exact hq), Option.getD_some]

/-- **The tail byte's identity.**  The byte arm reads `b + n - 1`; at the caller's
padded window that byte is the document's last. -/
theorem lastByte_eq_klByte (mem : Mem) (bs : List UInt8) (b : Nat) (n : BitVec 64)
    (last : UInt8)
    (hwin : readBytes mem b (64 * blocksOf bs.length) = some (padded bs))
    (hbs : n.toNat = bs.length) (hn0 : n ≠ 0)
    (hread : readBytes mem (b + (n.signExtend 64).toNat - 1) 1 = some [last]) :
    last = klByte bs (bs.length - 1) := by
  have hpos : 0 < n.toNat := by
    rcases Nat.eq_zero_or_pos n.toNat with h0 | h0
    · exfalso
      apply hn0
      apply BitVec.eq_of_toNat_eq
      rw [h0]
      rfl
    · exact h0
  have hse : (n.signExtend 64).toNat = n.toNat := signExtend_self_toNat n
  have hq : n.toNat - 1 < 64 * blocksOf bs.length := by
    have hle : n.toNat ≤ 64 * blocksOf bs.length := by
      rw [hbs]; exact blocksOf_le bs.length
    omega
  have haddr : b + (n.signExtend 64).toNat - 1 = b + (n.toNat - 1) := by
    rw [hse, Nat.add_sub_assoc (by omega)]
  have hbyte := readBytes_padded_byte mem bs b (n.toNat - 1) hwin hq
  have hread' : readBytes mem (b + (n.toNat - 1)) 1 = some [last] := by
    rw [← haddr]
    exact hread
  rw [hread'] at hbyte
  have hval : last = (padded bs).getD (n.toNat - 1) 0x00 := by
    simpa using hbyte
  have hlt : bs.length - 1 < bs.length := by omega
  have hget : (padded bs).getD (n.toNat - 1) 0x00 = bs.getD (bs.length - 1) 0x00 := by
    rw [show n.toNat - 1 = bs.length - 1 from by omega]
    unfold padded
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append, if_pos hlt,
      List.getElem?_eq_getElem hlt, Option.getD_some]
  rw [hval, hget]
  rfl

/-! ### The compositions' shapes

Each edge states the four facts `JsonS1BlocksRefines` and `JsonS1BlocksShort`
take: the peel's bit, the staging the peel's word carries, and the tail byte's
error bit.  The fused edge is also where `hstageByte`'s address is the arm's own
read; the latch edge's `hstage` is `staging_zero_of_ascii` below. -/

/-- **`hsilent` at the fused loop's exit.** -/
theorem hsilent_fusedExit (env : Env) (c : FusedCarry) (n andv : BitVec 64)
    (bs136 bs137 : List UInt8) (conv : BitVec 32) {bs : List UInt8} {k : Nat}
    (hk : k < blocksOf bs.length) (hshr : c.shr.toNat = k)
    (h136 : bs136 = (docBlock bs k).take 32)
    (h137 : bs137 = (docBlock bs k).drop 32)
    (hconv : conv = 0) (hprobe : ∀ x ∈ blockHalfOr bs k, x.toNat < 0x80)
    (hprev : c.prevAscii ≠ 0) :
    ∀ (v : IfThen103Values), v = fusedPeelValues env c n andv bs136 bs137 conv →
      lookupName (ifThen103Out (forEnd101OutOf env c.prevS c.ascii c.u8k c.prevAscii
        c.st0 c.st9 c.st15 andv) v) "%or.cond191" = some (.int 1 1) := by
  intro v hv
  have hb := ifThen103Values_cond191_of_block hk h136 h137 n c.b c.ascii
    c.st0 c.st9 c.st15 c.prevS andv c.shr c.ent conv c.prevAscii hconv hprobe hprev
  rw [hv, lookupName_ifThen103Out_cond191, hb]

/-- **`hsilent` at the ASCII phase's exit.**  The latch's edge carries the set
byte and the zero words; the bit is the gate's and the block's. -/
theorem hsilent_asciiExit (env : Env) (c : AsciiCarry) (n andv : BitVec 64)
    (bs136 bs137 : List UInt8) (conv : BitVec 32) {bs : List UInt8} {k : Nat}
    (hk : k < blocksOf bs.length) (hshr : c.shr.toNat = k)
    (h136 : bs136 = (docBlock bs k).take 32)
    (h137 : bs137 = (docBlock bs k).drop 32)
    (hconv : conv = 0) (hprobe : ∀ x ∈ blockHalfOr bs k, x.toNat < 0x80) :
    ∀ (v : IfThen103Values), v = ifThen103Values n c.b bs136 bs137
        (List.replicate 4 0) c.st0 c.st9 c.st15 c.prevS andv c.shr c.ent conv 1 →
      lookupName (ifThen103Out (peelEntryEnv env c andv) v) "%or.cond191"
        = some (.int 1 1) := by
  intro v hv
  have hb := ifThen103Values_cond191_of_block hk h136 h137 n c.b
    (List.replicate 4 (0 : BitVec 64)) c.st0 c.st9 c.st15 c.prevS andv c.shr c.ent
    conv (1 : BitVec 32) hconv hprobe (by decide)
  rw [hv, lookupName_ifThen103Out_cond191, hb]

/-- **`hsilent` at the short document's join.** -/
theorem hsilent_shortPeel (env : Env) (n arm : BitVec 64) (b ent : Nat)
    (bs136 bs137 : List UInt8) {bs : List UInt8} {k : Nat}
    (hk : k < blocksOf bs.length) (hshr : (n >>> 6).toNat = k)
    (h136 : bs136 = (docBlock bs k).take 32)
    (h137 : bs137 = (docBlock bs k).drop 32)
    (hconv : entryGate arm = 0)
    (hprobe : ∀ x ∈ blockHalfOr bs k, x.toNat < 0x80) :
    ∀ (v : IfThen103Values), v = ifThen103Values n b bs136 bs137
        (List.replicate 4 0) 0 0 0 0 (n &&& 63) (n >>> 6) ent (entryGate arm) 1 →
      lookupName (ifThen103Out env v) "%or.cond191" = some (.int 1 1) := by
  intro v hv
  have hb := ifThen103Values_cond191_of_block hk h136 h137 n b
    (List.replicate 4 (0 : BitVec 64)) 0 0 0 0 (n &&& 63) (n >>> 6) ent
    (entryGate arm) (1 : BitVec 32) hconv hprobe (by decide)
  rw [hv, lookupName_ifThen103Out_cond191, hb]

/-- **`hstagePeel` at the fused loop's exit.** -/
theorem hstagePeel_fusedExit (env : Env) (c : FusedCarry) (n andv : BitVec 64)
    (bs136 bs137 : List UInt8) (conv : BitVec 32) {bs : List UInt8} {nb k : Nat}
    {gate : Bool}
    (hstage : VerdictStaging c.ascii c.u8k bs bs.length nb gate
      (evalICmp .eq (ptestzU8k c.u8k) 0))
    (hsucc : k + 1 = blocksOf bs.length) (hshr : c.shr.toNat = k)
    (h136 : bs136 = (docBlock bs k).take 32)
    (h137 : bs137 = (docBlock bs k).drop 32) :
    ∀ (v : IfThen103Values), v = fusedPeelValues env c n andv bs136 bs137 conv →
      VerdictStaging v.or279 c.u8k bs bs.length nb gate
        (evalICmp .eq (ptestzU8k c.u8k) 0) := by
  intro v hv
  have hs := ifThen103Values_or279_staging (n := bs.length) (nb := nb)
    (k := k) (gate := gate) (ascii := c.ascii) (u8k := c.u8k)
    (err := evalICmp .eq (ptestzU8k c.u8k) 0) hstage hsucc h136 h137 n c.b
    c.st0 c.st9 c.st15 c.prevS andv c.shr c.ent conv c.prevAscii (by rw [hshr])
  rwa [hv]

/-- **`hstagePeel` at the ASCII phase's exit.** -/
theorem hstagePeel_asciiExit (env : Env) (c : AsciiCarry) (n andv : BitVec 64)
    (conv : BitVec 32) {bs : List UInt8} {nb k : Nat} {gate : Bool}
    (hstage : VerdictStaging (List.replicate 4 0) (List.replicate 4 0) bs bs.length
      nb gate (evalICmp .eq (ptestzU8k (List.replicate 4 0)) 0))
    (hsucc : k + 1 = blocksOf bs.length) (hshr : c.shr.toNat = k) :
    ∀ (v : IfThen103Values), v = ifThen103Values n c.b
        ((docBlock bs k).take 32) ((docBlock bs k).drop 32) (List.replicate 4 0)
        c.st0 c.st9 c.st15 c.prevS andv c.shr c.ent conv 1 →
      VerdictStaging v.or279 (List.replicate 4 0) bs bs.length nb gate
        (evalICmp .eq (ptestzU8k (List.replicate 4 0)) 0) := by
  intro v hv
  have hs := ifThen103Values_or279_staging (n := bs.length) (nb := nb) (k := k)
    (gate := gate) (ascii := List.replicate 4 (0 : BitVec 64))
    (u8k := List.replicate 4 (0 : BitVec 64))
    (err := evalICmp .eq (ptestzU8k (List.replicate 4 0)) 0) hstage hsucc rfl rfl
    n c.b c.st0 c.st9 c.st15 c.prevS andv c.shr c.ent conv (1 : BitVec 32)
    (by rw [hshr])
  rwa [hv]

/-- **`hstagePeel` at the short document's join.** -/
theorem hstagePeel_shortPeel (env : Env) (n arm : BitVec 64) (b ent : Nat)
    (bs136 bs137 : List UInt8) {bs : List UInt8} {nb k : Nat} {gate : Bool}
    (hstage : VerdictStaging (List.replicate 4 0) (List.replicate 4 0) bs bs.length
      nb gate (evalICmp .eq (ptestzU8k (List.replicate 4 0)) 0))
    (hsucc : k + 1 = blocksOf bs.length) (hshr : (n >>> 6).toNat = k)
    (h136 : bs136 = (docBlock bs k).take 32)
    (h137 : bs137 = (docBlock bs k).drop 32) :
    ∀ (v : IfThen103Values), v = ifThen103Values n b bs136 bs137
        (List.replicate 4 0) 0 0 0 0 (n &&& 63) (n >>> 6) ent (entryGate arm) 1 →
      VerdictStaging v.or279 (List.replicate 4 0) bs bs.length nb gate
        (evalICmp .eq (ptestzU8k (List.replicate 4 0)) 0) := by
  intro v hv
  have hs := ifThen103Values_or279_staging (n := bs.length) (nb := nb) (k := k)
    (gate := gate) (ascii := List.replicate 4 (0 : BitVec 64))
    (u8k := List.replicate 4 (0 : BitVec 64))
    (err := evalICmp .eq (ptestzU8k (List.replicate 4 0)) 0) hstage hsucc h136 h137
    n b 0 0 0 0 (n &&& 63) (n >>> 6) ent (entryGate arm) (1 : BitVec 32)
    (by rw [hshr])
  rwa [hv]

/-- **`hstageByte` at the fused loop's exit.**  The arm's own read is at the
document's last byte, which `lastByte_eq_klByte` names. -/
theorem hstageByte_fusedExit (env : Env) (s : State) (c : FusedCarry)
    (n : BitVec 64) {bs : List UInt8} {nb : Nat} {gate : Bool} (last : UInt8)
    (hstage : VerdictStaging c.ascii c.u8k bs bs.length nb gate
      (evalICmp .eq (ptestzU8k c.u8k) 0))
    (hwin : readBytes s.mem c.b (64 * blocksOf bs.length) = some (padded bs))
    (hbs : n.toNat = bs.length) (hn0 : n ≠ 0)
    (hread : readBytes s.mem (c.b + (n.signExtend 64).toNat - 1) 1 = some [last]) :
    VerdictStaging c.ascii c.u8k bs bs.length nb gate
      (evalICmp .eq (ptestzU8k c.u8k) 0 |||
        lastByteBits (BitVec.ofNat 8 last.toNat)) :=
  staging_of_byte hstage last (by
      intro h
      apply hn0
      apply BitVec.eq_of_toNat_eq
      rw [hbs, h]
      rfl)
    (lastByte_eq_klByte s.mem bs c.b n last hwin hbs hn0 hread)

/-- **`hstageByte` at the ASCII phase's exit.** -/
theorem hstageByte_asciiExit (env : Env) (s : State) (c : AsciiCarry)
    (n : BitVec 64) {bs : List UInt8} {nb : Nat} {gate : Bool} (last : UInt8)
    (hstage : VerdictStaging (List.replicate 4 0) (List.replicate 4 0) bs bs.length
      nb gate (evalICmp .eq (ptestzU8k (List.replicate 4 0)) 0))
    (hwin : readBytes s.mem c.b (64 * blocksOf bs.length) = some (padded bs))
    (hbs : n.toNat = bs.length) (hn0 : n ≠ 0)
    (hread : readBytes s.mem (c.b + (n.signExtend 64).toNat - 1) 1 = some [last]) :
    VerdictStaging (List.replicate 4 0) (List.replicate 4 0) bs bs.length nb gate
      (evalICmp .eq (ptestzU8k (List.replicate 4 0)) 0 |||
        lastByteBits (BitVec.ofNat 8 last.toNat)) :=
  staging_of_byte hstage last (by
      intro h
      apply hn0
      apply BitVec.eq_of_toNat_eq
      rw [hbs, h]
      rfl)
    (lastByte_eq_klByte s.mem bs c.b n last hwin hbs hn0 hread)

/-! ### The latch edge's zero staging

The `for.end101` phis' zero lanes are the phase's ASCII word and accumulator.
They stage the caller's document exactly when it is ASCII: the zero word's bytes
are high-clear, the accumulator's packed word is `klAll = 0` because the padded
window is a valid prefix, and the error bit is clear because every ASCII byte is
out of the table's lead range. -/

/-- **The zero staging at an ASCII document.** -/
theorem staging_zero_of_ascii {bs : List UInt8} {n nb : Nat} {gate : Bool}
    (hbs : ∀ x ∈ bs, x.toNat < 0x80) (hn : n = bs.length)
    (hnb : nb = blocksOf bs.length) :
    VerdictStaging (List.replicate 4 0) (List.replicate 4 0) bs n nb gate
      (evalICmp .eq (ptestzU8k (List.replicate 4 0)) 0) := by
  have hnb' : nb = (n + 63) / 64 := by simpa [blocksOf, hn] using hnb
  -- the zero word's byte view
  have hzero : asciiBytes (List.replicate 4 (0 : BitVec 64)) =
      List.replicate 32 (0 : UInt8) := by
    unfold asciiBytes
    rw [JsonS1BlocksStaging.packLanes_replicate_zero]
    decide
  -- the window is a valid prefix, so the accumulator's fold is zero
  have hvalid : JSON.ValidPrefix (JSON.ByteString.literal
      (List.replicate 3 0 ++ bs ++ List.replicate (64 * nb - n) 0)) := by
    have := skip_sound bs hbs
    simpa [utf8WinPrefix, utf8Window, hn, hnb] using this
  have herr : klErrAll (utf8Window bs n nb) (64 * nb) := by
    have h := (klErrAll_window_iff bs n nb hn hnb').mpr hvalid
    simpa [utf8Window] using h.1
  have hklall : (klAll gate bs).all (fun x => decide (x = 0x00)) = true :=
    (klAll_zero_iff_klErrAll bs n nb gate hn hnb').mpr herr
  have hkl0 : bytesToNat (klAll gate bs) = 0 :=
    (bytesToNat_eq_zero_iff _).mpr ((all_eq_zero_iff _).mp hklall)
  -- the error bit's reading
  have hptz : ptestzU8k (List.replicate 4 (0 : BitVec 64)) = 1 := by
    unfold ptestzU8k
    rw [JsonS1BlocksStaging.packLanes_replicate_zero]
    decide
  have hbit : evalICmp .eq (ptestzU8k (List.replicate 4 0)) (0 : BitVec 32) = 0 := by
    rw [hptz]
    decide
  have hallZero : (List.replicate 4 (0 : BitVec 64)).all
      (fun x => decide (x = 0x00)) = true := by decide
  refine ⟨?_, by simp, hn, hnb, ?_, ?_, ?_⟩
  · simp
  · constructor
    · intro _
      exact hbs
    · intro _
      intro b hb
      rw [hzero] at hb
      obtain ⟨_, rfl⟩ := List.mem_replicate.mp hb
      decide
  · rw [show packLanes (List.replicate 4 (0 : BitVec 64)) = 0 from
      JsonS1BlocksStaging.packLanes_replicate_zero, hkl0]
  · rw [hbit]
    constructor
    · intro h
      exact absurd h (by decide)
    · rintro (h | ⟨hne, htail⟩)
      · exact absurd hallZero h
      · have hlt : n - 1 < bs.length := by
          rw [hn] at *
          omega
        have hhigh : (klByte bs (n - 1)).toNat < 0x80 := by
          rw [show klByte bs (n - 1) = bs.getD (n - 1) 0x00 from rfl,
            getD_of_lt _ _ hlt]
          exact hbs _ (List.getElem_mem hlt)
        exact absurd (klTailByte_true_ge htail) (by omega)

/-! ### Axiom footprints -/

#print axioms ite_ite_bit_one_iff
#print axioms ite_bit_one_iff
#print axioms ifThen103Values_or280_eq
#print axioms ifThen103Values_ptz138_eq_asciiProbe
#print axioms ifThen103Values_cond190_eq_one_iff
#print axioms ifThen103Values_cond191_eq_one_iff
#print axioms lookupName_ifThen103Out_cond191
#print axioms ifThen103Values_ptz138_ne_zero_iff
#print axioms packLanes_peelBlock
#print axioms blockHalfOr_high
#print axioms ifThen103Values_ptz138_ne_zero_iff_block
#print axioms ifThen103Values_cond191_of_block
#print axioms natToBytes_or
#print axioms asciiBytes_zipWith_or
#print axioms zipWith_or_all_high_iff
#print axioms staging_of_peel
#print axioms ifThen103Values_or279_staging
#print axioms lastByteBits_ofNat_toBitVec
#print axioms staging_of_byte
#print axioms readBytes_padded_byte
#print axioms lastByte_eq_klByte
#print axioms hsilent_fusedExit
#print axioms hsilent_asciiExit
#print axioms hsilent_shortPeel
#print axioms hstagePeel_fusedExit
#print axioms hstagePeel_asciiExit
#print axioms hstagePeel_shortPeel
#print axioms hstageByte_fusedExit
#print axioms hstageByte_asciiExit
#print axioms staging_zero_of_ascii

end LeanLLVM.Refinement.JsonS1BlocksPeelStaging
