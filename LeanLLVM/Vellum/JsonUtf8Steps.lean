/-
The step corpus of the pinned UTF-8 unit's emitted body.

`JsonUtf8IR` holds the fixture, its pin, the call environment `utf8Calls` and the
window the body stages; `JsonUtf8Spec` holds the specification the verdict is
judged against.  This module holds the body's instructions as step lemmas, the
backward `getelementptr` the seven backward sites need, the tables' tie to the
specification, and the two specification-side theorems the statement consumes:
the `klMust` bridge and the gate lemma.  The loop lemmas, the reduce and the tail,
and the refinement theorem itself are stated over these and are not in this
module yet; what is here is the part they are built from.

## The shape of a step

A step is stated at an **opaque environment** — `withEnv env s`, with the
operands it reads as *hypotheses* — and its conclusion adds one cell to that
environment.  That is `JsonEntrySteps`' shape, reused rather than rediscovered.

## The backward `getelementptr`

The body's seven backward sites — the six `-1`/`-2`/`-3` loads and the tail's
`-1` — read an index whose sign-extended value has the top bit set.
`step_gep64`'s `hpos : idx.toNat < 2 ^ 63` is the **forward** precondition and is
false at every one of them, so this module states the companion
`step_gep64_back`: the index is `2 ^ 64 - k` for a magnitude `k`, and the address
bound is the displacement against the base rather than the index's sign.  Its
third hypothesis, `k ≤ 2 ^ 63`, is the branch premise read at the magnitude —
with `idx.toNat = 2 ^ 64 - k` it *is* `2 ^ 63 ≤ idx.toNat` — and it is not
dispensable: for `k > 2 ^ 63` the index is below the forward bound and the
forward branch is the one that runs.  At the seven sites it follows from `k ≤ 3`.
-/
import LeanLLVM.Vellum.JsonUtf8IR
import LeanLLVM.Vellum.JsonUtf8Spec
import LeanLLVM.Vellum.JsonEntrySteps
import LeanLLVM.Vellum.JsonS1MasksSteps

namespace LeanLLVM.Vellum.JsonUtf8Steps

open LeanLLVM
open LeanLLVM.Vellum.JsonUtf8IR
open LeanLLVM.Vellum.JsonUtf8Spec
open LeanLLVM.Vellum.BitLanes
open LeanLLVM.Vellum.JsonEntrySteps
open LeanLLVM.Vellum.JsonS1MasksIR
  (evalInstr_load evalInstr_binop evalInstr_binopVec evalInstr_icmp evalInstr_zext
   evalInstr_call evalInstr_vecBitcast evalInstr_icmpVec evalOperands_cons
   vecLanes_self lookupName_bind_ne lookupName_bind_self
   zipReplicate_mapM mapM_some_map pshufbLanes_two_copies_lane getD_two_copies
   split16 split16' bitcastVecLanes_unpackLanes)
open LeanLLVM.Vellum.JsonS1MasksSteps
  (nibLanes andLanes shr4Lanes shr4Lanes_length hiNibbleLanes hiNibbleLanes_length
   nibbleLanes_eq and15_eq_mod packLanes_shr4_mod lane_shr4 shr4Lanes_getD
   unpackLanes_getElem unpackLanes_getElem_toNat)

/-! ### The fuel, and the run's own step relation -/

/-- `fuelOf` is the block count's budget: at most three control steps per gated
block and five outside the loops, so `3 * nb + 8` has three steps of slack.  The
constant's own definition and its worst-case reading are in `JsonUtf8IR`. -/
theorem fuelOf_eq (nb : Nat) : fuelOf nb = 3 * nb + 8 := rfl

/-! ### The backward `getelementptr` step

`evalInstr_gep_back` (`Semantics.lean`) is the semantics' branch for a
sign-extended index whose top bit is set: the displacement is
`(2 ^ 64 - v) * sizeBytes`, and the step is defined while that does not exceed the
base.  The step below states it in the form the body's sites supply — a magnitude
`k` with `idx.toNat = 2 ^ 64 - k` — and its third hypothesis is the branch
premise read at the magnitude: with `hidx`, `k ≤ 2 ^ 63` *is* `2 ^ 63 ≤ idx.toNat`.

**That hypothesis is not hygiene, and deleting it makes the lemma false.**  Take
`k = 2 ^ 63 + 1`, so `idx.toNat = 2 ^ 64 - k = 2 ^ 63 - 1`: the sign-extended index
is *below* `2 ^ 63`, `evalInstr_gep`'s **forward** branch is the one that runs, and
the address is `a + (2 ^ 63 - 1) * sizeBytes`.  This lemma would claim
`a - (2 ^ 63 + 1) * sizeBytes`.  At `a = 0` that is `0`, while the forward branch
reads `(2 ^ 63 - 1) * sizeBytes`, which is not `0`; and in the unsaturated form the
two candidate addresses differ by `2 * 2 ^ 63 * sizeBytes`, which is the whole of
what the bound buys.  `1 ≤ k` alone does not exclude that shape — `k ≤ 2 ^ 63` is
what does, and it is the backward branch's premise stated in `k` rather than in
the index's sign.  At the seven sites it is trivial: each supplies `k = 1`, `2`
or `3`.

The address conclusion is the base minus the displacement, so `k * sizeBytes ≤ a`
is the whole of the definedness: `a - k * sizeBytes` is a natural and
`(a - k * sizeBytes) + k * sizeBytes = a`. -/

/-- The magnitude reading of a sign-extended index: an index whose sign-extended
value is `2 ^ 64 - k` with `1 ≤ k ≤ 2 ^ 63` is at or above the forward bound, and
its displacement is that magnitude.  Both conjuncts are `omega` from the three
hypotheses — the branch premise is *derived* here, never assumed. -/
theorem signExtend_magnitude {w : Nat} (n : BitVec w) (k : Nat)
    (hidx : (n.signExtend 64).toNat = 2 ^ 64 - k) (hk1 : 1 ≤ k) (hk : k ≤ 2 ^ 63) :
    ¬ (n.signExtend 64).toNat < 2 ^ 63 ∧ 2 ^ 64 - (n.signExtend 64).toNat = k := by
  constructor
  · omega
  · omega

/-- `%d = getelementptr i8, ptr %base, i64 %off` at a backward index: `off` reads
`2 ^ 64 - k`, and the destination is the base minus that displacement.  The seven
sites the body has are all `i8`, and each supplies `k = 1`, `2` or `3`.

The branch is derived, not assumed: `hbig` below is `2 ^ 63 ≤ idx.toNat` and comes
from `hk` through `hidx`, and it is what leaves `evalInstr_gep`'s forward arm
unreachable.  `hneg` and `hmag` are the two facts `evalInstr_gep_back` asks for,
read at the sign-extended index. -/
theorem step_gep64_back (env : Env) (s : State) (d base off : String) (elem : Ty)
    (a k : Nat) (idx : BitVec 64)
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 idx))
    (hidx : idx.toNat = 2 ^ 64 - k) (hk1 : 1 ≤ k) (hk : k ≤ 2 ^ 63)
    (hka : k * elem.sizeBytes ≤ a) :
    evalInstr utf8Calls (withEnv env s) (.gep d elem (.reg base) (.reg off)) =
      some (withEnv ((d, .ptr (a - k * elem.sizeBytes)) :: env) s) := by
  have hse : (idx.signExtend 64).toNat = idx.toNat := by
    rw [BitVec.signExtend_eq]
  -- `k ≤ 2 ^ 63`, read at the index: the forward branch's bound is not met.
  have hbig : 2 ^ 63 ≤ idx.toNat := by omega
  have hneg : ¬ (idx.signExtend 64).toNat < 2 ^ 63 := by
    rw [hse]
    exact Nat.not_lt.mpr hbig
  have hmag : 2 ^ 64 - (idx.signExtend 64).toNat = k := by rw [hse]; omega
  rw [evalInstr_gep_back (hb := evalOperand_reg_of env s base (.ptr a) hb)
    (ho := evalOperand_reg_of env s off (.int 64 idx) ho) (hneg := hneg)
    (hk := by rw [hmag]; exact hka)]
  simp only [hmag, withEnv, State.bind]

/-! ### The scalar steps the two bodies need beyond `JsonEntrySteps`' set -/

/-- `%d = and i1 %a, %b`. -/
theorem step_and_reg (env : Env) (s : State) (d a b : String)
    (x y : BitVec 1) (ha : lookupName env a = some (.int 1 x))
    (hb : lookupName env b = some (.int 1 y)) :
    evalInstr utf8Calls (withEnv env s) (.binop d .and 1 (.reg a) (.reg b)) =
      some (withEnv ((d, .int 1 (x &&& y)) :: env) s) := by
  rw [evalInstr_binop (ha := evalOperand_reg_of env s a (.int 1 x) ha)
    (hb := evalOperand_reg_of env s b (.int 1 y) hb) (hr := by rfl)]
  simp only [withEnv, State.bind, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `%d = or i1 %a, %b`. -/
theorem step_or_reg (env : Env) (s : State) (d a b : String)
    (x y : BitVec 1) (ha : lookupName env a = some (.int 1 x))
    (hb : lookupName env b = some (.int 1 y)) :
    evalInstr utf8Calls (withEnv env s) (.binop d .or 1 (.reg a) (.reg b)) =
      some (withEnv ((d, .int 1 (x ||| y)) :: env) s) := by
  rw [evalInstr_binop (ha := evalOperand_reg_of env s a (.int 1 x) ha)
    (hb := evalOperand_reg_of env s b (.int 1 y) hb) (hr := by rfl)]
  simp only [withEnv, State.bind, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `%d = icmp ne i32 %src, <c>`. -/
theorem step_icmp_ne_imm (env : Env) (s : State) (d src : String) (w : Nat)
    (x c : BitVec w) (h : lookupName env src = some (.int w x)) :
    evalInstr utf8Calls (withEnv env s) (.icmp d .ne w (.reg src) (.imm (.int w c))) =
      some (withEnv ((d, .int 1 (BitVec.ofBool (x ≠ c))) :: env) s) := by
  rw [evalInstr_icmp (ha := evalOperand_reg_of env s src (.int w x) h)
    (hb := evalOperand_lit_of _ w c)]
  simp [withEnv, State.bind, evalICmp]

/-- `%d = icmp ult i64 %src, <c>`. -/
theorem step_icmp_ult_imm (env : Env) (s : State) (d src : String) (w : Nat)
    (x c : BitVec w) (h : lookupName env src = some (.int w x)) :
    evalInstr utf8Calls (withEnv env s) (.icmp d .ult w (.reg src) (.imm (.int w c))) =
      some (withEnv ((d, .int 1 (BitVec.ofBool (BitVec.ult x c))) :: env) s) := by
  rw [evalInstr_icmp (ha := evalOperand_reg_of env s src (.int w x) h)
    (hb := evalOperand_lit_of _ w c)]
  simp [withEnv, State.bind, evalICmp]

/-- `%d = icmp ugt i8 %src, <c>`. -/
theorem step_icmp_ugt_imm (env : Env) (s : State) (d src : String) (w : Nat)
    (x c : BitVec w) (h : lookupName env src = some (.int w x)) :
    evalInstr utf8Calls (withEnv env s) (.icmp d .ugt w (.reg src) (.imm (.int w c))) =
      some (withEnv ((d, .int 1 (BitVec.ofBool (BitVec.ult c x))) :: env) s) := by
  rw [evalInstr_icmp (ha := evalOperand_reg_of env s src (.int w x) h)
    (hb := evalOperand_lit_of _ w c)]
  simp [withEnv, State.bind, evalICmp]

/-- `%d = getelementptr i8, ptr %base, i64 <c>`: the immediate form, which the
tail's `-1` and every fixed offset in the two loop bodies use. -/
theorem step_gep64_imm (env : Env) (s : State) (d base : String) (elem : Ty)
    (a : Nat) (c : BitVec 64)
    (hb : lookupName env base = some (.ptr a))
    (hpos : (c.signExtend 64).toNat < 2 ^ 63) :
    evalInstr utf8Calls (withEnv env s)
        (.gep d elem (.reg base) (.imm (.int 64 c))) =
      some (withEnv ((d, .ptr (a + c.toNat * elem.sizeBytes)) :: env) s) := by
  rw [evalInstr_gep (hb := evalOperand_reg_of env s base (.ptr a) hb)
    (ho := evalOperand_lit_of _ 64 c) (hpos := by simpa using hpos)]
  simp only [withEnv, State.bind, BitVec.signExtend_eq]

/-- `%d = getelementptr i8, ptr %base, i64 <c>` at a negative constant: the
immediate form of `step_gep64_back`, with the magnitude `2 ^ 64 - c.toNat`. -/
theorem step_gep64_imm_back (env : Env) (s : State) (d base : String) (elem : Ty)
    (a k : Nat) (c : BitVec 64)
    (hb : lookupName env base = some (.ptr a))
    (hc : c.toNat = 2 ^ 64 - k) (hk1 : 1 ≤ k) (hk : k ≤ 2 ^ 63)
    (hka : k * elem.sizeBytes ≤ a) :
    evalInstr utf8Calls (withEnv env s)
        (.gep d elem (.reg base) (.imm (.int 64 c))) =
      some (withEnv ((d, .ptr (a - k * elem.sizeBytes)) :: env) s) := by
  have hse : (c.signExtend 64).toNat = c.toNat := by rw [BitVec.signExtend_eq]
  have hm := signExtend_magnitude c k (by rw [hse]; exact hc) hk1 hk
  rw [evalInstr_gep_back (hb := evalOperand_reg_of env s base (.ptr a) hb)
    (ho := evalOperand_lit_of _ 64 c) (hneg := hm.1)
    (hk := by rw [hm.2]; exact hka)]
  have hlt := c.isLt
  have hk' : 2 ^ 64 - c.toNat = k := by omega
  simp only [hse, hk', withEnv, State.bind]

/-- `256 ^ 32 = 2 ^ 256`: the thirty-two bytes of a 256-bit word. -/
theorem nat256 : (256 : Nat) ^ 32 = 2 ^ 256 := by
  rw [show (256 : Nat) = 2 ^ 8 from by decide, ← Nat.pow_mul]

/-! ### The three loads

The body loads `<4 x i64>`, `<32 x i8>` and `<16 x i16>` words.  Each is the
model's `loadValue` at its own lane width; the byte lanes are `unpackLanes`' at
that width, which is `storeValue`'s layout read back. -/

/-- The 32 bytes a 256-bit word's lanes occupy: `unpackLanes`' list at the byte
width.  `Memory.lean`'s `byteLanes` is the byte view of a byte *list*, and the two
meet at the word a byte list packs to: `byteLanes_eq_unpackLanes` states
`unpackLanes 8 n (bytesToNat bs) = byteLanes bs`, which is `wordBytes (bytesToNat
bs)` on the left.  A *loaded* `<32 x i8>` needs the other bridge, because
`loadValue` spells its lanes `bs.map UInt8.toBitVec` rather than
`BitVec.ofNat 8 ·.toNat`; that one is `map_toBitVec_eq_byteLanes`. -/
def wordBytes (V : Nat) : List (BitVec 8) := unpackLanes 8 32 V

theorem wordBytes_length (V : Nat) : (wordBytes V).length = 32 := by
  simp [wordBytes, unpackLanes_length]

/-- A loaded byte vector's lanes are `Memory.lean`'s `byteLanes` of the same
bytes: `loadValue` spells the pointwise map with `UInt8.toBitVec` and the memory
module with `BitVec.ofNat 8 ·.toNat`, and the two are the same byte. -/
theorem map_toBitVec_eq_byteLanes (bs : List UInt8) :
    (bs.map fun b => b.toBitVec) = byteLanes bs := by
  simp [byteLanes]

/-- `%d = load <32 x i8>, ptr %p`, at the thirty-two bytes the lane list holds.
`loadValue`'s `<n x i8>` arm maps the bytes one to one, so the value is the
window's own byte list and no unpacking is involved.

The byte count is **not** a hypothesis: `loadValue` reads the number of bytes its
type names, so `bs.length = 32` would be unused by this step, and a caller that
needs the value's `vecLanes` supplies the length itself.  Its absence is
therefore a consequence of the arm, not a dropped premise. -/
theorem step_load32_8 (env : Env) (s : State) (d p : String) (a : Nat)
    (bs : List UInt8) (hp : lookupName env p = some (.ptr a))
    (hr : readBytes s.mem a 32 = some bs) :
    evalInstr utf8Calls (withEnv env s) (.load d v32i8 (.reg p)) =
      some (withEnv ((d, .vec 32 8 (bs.map fun b => BitVec.ofNat 8 b.toNat)) :: env) s) := by
  have hv : loadValue (withEnv env s).mem v32i8 a =
      some (.vec 32 8 (bs.map fun b => BitVec.ofNat 8 b.toNat)) := by
    simp only [withEnv, loadValue]
    rw [hr]
  rw [evalInstr_load (v := .vec 32 8 (bs.map fun b => BitVec.ofNat 8 b.toNat))
    (hp := evalOperand_reg_of env s p (.ptr a) hp) hv]
  rfl

/-- `%d = load <4 x i64>, ptr %p`: the same thirty-two bytes at four 64-bit lanes. -/
theorem step_load4_64 (env : Env) (s : State) (d p : String) (a V : Nat)
    (hp : lookupName env p = some (.ptr a))
    (hr : readBytes s.mem a 32 = some (natToBytes V 32)) (hV : V < 2 ^ 256) :
    evalInstr utf8Calls (withEnv env s) (.load d v4i64 (.reg p)) =
      some (withEnv ((d, .vec 4 64 (unpackLanes 64 4 V)) :: env) s) := by
  have hv : loadValue (withEnv env s).mem v4i64 a =
      some (.vec 4 64 (unpackLanes 64 4 V)) := by
    simp only [withEnv, loadValue, ite_true, hr, natToBytes_toNat, nat256,
      Nat.mod_eq_of_lt hV]
  rw [evalInstr_load (v := .vec 4 64 (unpackLanes 64 4 V))
    (hp := evalOperand_reg_of env s p (.ptr a) hp) hv]
  rfl

/-- `%d = load <16 x i16>, ptr %p`: the same thirty-two bytes at sixteen 16-bit
lanes. -/
theorem step_load16_16 (env : Env) (s : State) (d p : String) (a V : Nat)
    (hp : lookupName env p = some (.ptr a))
    (hr : readBytes s.mem a 32 = some (natToBytes V 32)) (hV : V < 2 ^ 256) :
    evalInstr utf8Calls (withEnv env s) (.load d (.vec 16 (.int 16)) (.reg p)) =
      some (withEnv ((d, .vec 16 16 (unpackLanes 16 16 V)) :: env) s) := by
  have hv : loadValue (withEnv env s).mem (.vec 16 (.int 16)) a =
      some (.vec 16 16 (unpackLanes 16 16 V)) := by
    simp only [withEnv, loadValue, ite_true, hr, natToBytes_toNat, nat256,
      Nat.mod_eq_of_lt hV]
  rw [evalInstr_load (v := .vec 16 16 (unpackLanes 16 16 V))
    (hp := evalOperand_reg_of env s p (.ptr a) hp) hv]
  rfl

/-! ### The `klMust` bridge

The specification's `klMust` is `0x80 & ((p2 -s 0x60) | (p3 -s 0x70))` with the
surviving bit taken as the definition, and `subsSat_high_bit` supplies the
per-lane fact.  This section is the bridge the specification left as a limit: at
one position, the emission's masked word *is* the specification's word, so a
theorem consumes the equality rather than a caveat.

`and_highBit` says masking with `0x80` keeps a byte's bit 7 and clears the rest;
`or_high` says bit 7 of an `or` is the disjunction of the operands' bits; and
`subsSat_96_high`/`subsSat_112_high` are `subsSat_high_bit` at the two constants
the emission subtracts.  The three together are the bridge, and `klMust`'s own
definition closes it. -/

/-- A byte's bit 7 is set exactly when it is at least `0x80`. -/
theorem highBit_iff (z : BitVec 8) : (0x80 : Nat) ≤ z.toNat ↔ z.getLsbD 7 = true := by
  revert z
  decide

/-- Masking a byte with `0x80` keeps bit 7 and clears the rest. -/
theorem and_highBit (z : BitVec 8) :
    (BitVec.ofInt 8 0x80) &&& z =
      if 0x80 ≤ z.toNat then (BitVec.ofInt 8 0x80) else 0 := by
  revert z
  decide

/-- `subsSat_high_bit` at the emission's first constant: `p -s 0x60` has bit 7 set
exactly when `p ≥ 0xE0`. -/
theorem subsSat_96_high (p : UInt8) :
    (0x80 : Nat) ≤ (subsSat p.toBitVec (BitVec.ofInt 8 0x60)).toNat ↔ 0xE0 ≤ p.toNat := by
  have h := subsSat_high_bit p (0x60 : UInt8)
  have hc : (0x60 : UInt8).toBitVec = BitVec.ofInt 8 0x60 := by decide
  have hn : (0x60 : UInt8).toNat = 96 := by decide
  rw [hc, hn] at h
  rw [h]

/-- `subsSat_high_bit` at the emission's second constant: `p -s 0x70` has bit 7 set
exactly when `p ≥ 0xF0`. -/
theorem subsSat_112_high (p : UInt8) :
    (0x80 : Nat) ≤ (subsSat p.toBitVec (BitVec.ofInt 8 0x70)).toNat ↔ 0xF0 ≤ p.toNat := by
  have h := subsSat_high_bit p (0x70 : UInt8)
  have hc : (0x70 : UInt8).toBitVec = BitVec.ofInt 8 0x70 := by decide
  have hn : (0x70 : UInt8).toNat = 112 := by decide
  rw [hc, hn] at h
  rw [h]

/-- Bit 7 of an `or` is the disjunction of the operands' bits. -/
theorem or_high (a b : BitVec 8) :
    (0x80 : Nat) ≤ (a ||| b).toNat ↔ ((0x80 : Nat) ≤ a.toNat ∨ (0x80 : Nat) ≤ b.toNat) := by
  rw [highBit_iff, BitVec.getLsbD_or, Bool.or_eq_true, ← highBit_iff a, ← highBit_iff b]

/-- `(0x80 : UInt8).toBitVec` is the masked constant. -/
theorem u80 : (0x80 : UInt8).toBitVec = BitVec.ofInt 8 0x80 := by decide

/-- `(0 : UInt8).toBitVec` is the zero word. -/
theorem u0 : (0 : UInt8).toBitVec = (0 : BitVec 8) := by decide

/-- **The `klMust` bridge, at one position.**  The emission's masked word —
`0x80 & ((p2 -s 0x60) | (p3 -s 0x70))` — is the specification's `klMust` at the
same two bytes.  The scope's obligation (c): the equality is a theorem rather
than a documented limit, and it is `subsSat_high_bit`'s. -/
theorem klMust_bridge (p2 p3 : UInt8) :
    (BitVec.ofInt 8 0x80) &&& (subsSat p2.toBitVec (BitVec.ofInt 8 0x60) |||
      subsSat p3.toBitVec (BitVec.ofInt 8 0x70)) = (klMust p2 p3).toBitVec := by
  rw [and_highBit]
  by_cases hz : (0x80 : Nat) ≤ (subsSat p2.toBitVec (BitVec.ofInt 8 0x60) |||
      subsSat p3.toBitVec (BitVec.ofInt 8 0x70)).toNat
  · rw [ite_eq_left hz]
    have h : 0xE0 ≤ p2 ∨ 0xF0 ≤ p3 := by
      rw [or_high, subsSat_96_high, subsSat_112_high] at hz
      rwa [UInt8.le_iff_toNat_le, UInt8.le_iff_toNat_le]
    unfold klMust
    rw [ite_eq_left h, u80]
  · rw [ite_eq_right hz]
    have h : ¬ (0xE0 ≤ p2 ∨ 0xF0 ≤ p3) := by
      rw [or_high, subsSat_96_high, subsSat_112_high] at hz
      rwa [UInt8.le_iff_toNat_le, UInt8.le_iff_toNat_le]
    unfold klMust
    rw [ite_eq_right h, u0]

/-! ### The gate lemma

C62 (i): a block whose 64 bytes are all below `0x80`, entered with three
preceding bytes all below `0x80`, has an error vector of zero.  The per-position
fact is `klErrByte_ascii`: an ASCII window needs no continuation, so `must` is
zero, and the tables' two structural bits cancel — `T1[lo] & T2[hi] = 0x02` and
`T3[hi] = 0x01` for every byte below `0x80`, which is
`klT1T2_ascii_facts`/`klSc_ascii_facts` decided over `lo(p1) × hi(p1) × hi(c)`
restricted to the ASCII half of each nibble. -/

/-- The two structural bits at an ASCII pair: `T1[lo p1] & T2[hi p1] = 0x02` for
every `p1` below `0x80`, decided over the sixteen low nibbles and the eight high
ones. -/
theorem klT1T2_ascii_facts :
    ∀ (lo hi : Fin 16), hi.val < 8 → klAt klT1 lo.val &&& klAt klT2 hi.val = 0x02 := by
  decide

/-- `sc` is zero at an ASCII pair: the low-nibble table, the `0x02` the row above
leaves, and `T3`'s `0x01` at every high nibble below eight. -/
theorem klSc_ascii_facts :
    ∀ (lo hi hic : Fin 16), hi.val < 8 → hic.val < 8 →
      klSc (nib hi.val lo.val) (nib hic.val 0) = 0 := by
  decide

/-- A cleared table word at an ASCII pair. -/
theorem klSc_ascii (p1 c : UInt8) (h1 : p1.toNat < 0x80) (hc : c.toNat < 0x80) :
    klSc p1 c = 0 := by
  have hhi : p1.toNat / 16 < 8 := by omega
  have hhic : c.toNat / 16 < 8 := by omega
  have h1' : p1.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  have h2' : p1.toNat / 16 < 16 := by omega
  have h3' : c.toNat / 16 < 16 := by omega
  rw [klSc_nib p1 c]
  exact klSc_ascii_facts ⟨_, h1'⟩ ⟨_, h2'⟩ ⟨_, h3'⟩ hhi hhic

/-- `must` is zero at ASCII predecessors: neither is at or above `0xE0`. -/
theorem klMust_ascii (p2 p3 : UInt8) (h2 : p2.toNat < 0x80) (h3 : p3.toNat < 0x80) :
    klMust p2 p3 = 0 := by
  unfold klMust
  rw [ite_eq_right]
  simp only [UInt8.le_iff_toNat_le]
  have h1 : (0xE0 : UInt8).toNat = 224 := by decide
  have h2' : (0xF0 : UInt8).toNat = 240 := by decide
  omega

/-- **The per-position fact the gate rests on**: an ASCII window's error byte is
zero.  This is the true form of the local condition — the byte is admissible
because nothing requires a continuation here — and it is what the gate's skip
has to preserve, not a claim about a window of four admissible bytes. -/
theorem klErrByte_ascii (p3 p2 p1 c : UInt8)
    (h3 : p3.toNat < 0x80) (h2 : p2.toNat < 0x80) (h1 : p1.toNat < 0x80)
    (hc : c.toNat < 0x80) :
    klErrByte p3 p2 p1 c = 0 := by
  unfold klErrByte
  rw [klSc_ascii p1 c h1 hc, klMust_ascii p2 p3 h2 h3, UInt8.xor_self]

/-- An ASCII stream's error vector is thirty-two zero bytes. -/
theorem klErrVec_ascii (s : List UInt8) (h : ∀ k, (s.getD k 0x00).toNat < 0x80) :
    klErrVec s = List.replicate 32 0x00 := by
  unfold klErrVec
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    exact klErrByte_ascii _ _ _ _ (h i) (h (i + 1)) (h (i + 2)) (h (i + 3))

/-- Membership closure for the block's two streams. -/
theorem ascii_append {l m : List UInt8} (hl : ∀ b ∈ l, b.toNat < 0x80)
    (hm : ∀ b ∈ m, b.toNat < 0x80) : ∀ b ∈ l ++ m, b.toNat < 0x80 := by
  intro b hb
  rw [List.mem_append] at hb
  exact hb.elim (hl b) (hm b)

theorem ascii_take {l : List UInt8} (h : ∀ b ∈ l, b.toNat < 0x80) (n : Nat) :
    ∀ b ∈ l.take n, b.toNat < 0x80 := fun b hb => h b (List.mem_of_mem_take hb)

theorem ascii_drop {l : List UInt8} (h : ∀ b ∈ l, b.toNat < 0x80) (n : Nat) :
    ∀ b ∈ l.drop n, b.toNat < 0x80 := fun b hb => h b (List.mem_of_mem_drop hb)

/-- A read past an ASCII stream is a padded zero, which is ASCII. -/
theorem ascii_getD {l : List UInt8} (h : ∀ b ∈ l, b.toNat < 0x80) :
    ∀ k, (l.getD k 0x00).toNat < 0x80 := by
  intro k
  by_cases hk : k < l.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    exact h _ (List.getElem_mem hk)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    decide

/-- One half's error bytes at an ASCII stream. -/
theorem klErr32_ascii (pre blk : List UInt8) (h : ∀ b ∈ pre ++ blk, b.toNat < 0x80) :
    klErr32 pre blk = List.replicate 32 0x00 := by
  unfold klErr32
  exact klErrVec_ascii _ (ascii_getD h)

/-- **C62 (i), the gate lemma**: a block of ASCII bytes entered with ASCII bytes
before it has an error vector of zero, so the gated path's skip is sound.  `pre`
is the three bytes before the block — what the ABI stages — and every byte of
either stream `klErrBlk` reads is covered by the two ASCII hypotheses: the
block's lower and upper halves with their carries, by `ascii_take`/`ascii_drop`.

This is **stronger than the statement C62 (i) describes**, and deliberately: the
criterion is about the loop's state, where `pre` is exactly the three bytes the
ABI stages, and the length-three case is the instance the loop's induction
consumes.  The conclusion does not use `pre`'s length — extra or missing bytes are
only more ASCII positions or a shorter carry — so no length hypothesis appears
here.  A reader comparing this statement with C62 should read the narrower form
as an instantiation, not as a premise that went missing. -/
theorem utf8Skip_eq_zero (pre blk : List UInt8)
    (hpre : ∀ b ∈ pre, b.toNat < 0x80) (hblk : ∀ b ∈ blk, b.toNat < 0x80) :
    klErrBlk pre blk = List.replicate 32 0x00 := by
  have h1 : ∀ b ∈ pre ++ blk.take 32, b.toNat < 0x80 :=
    ascii_append hpre (ascii_take hblk 32)
  have h2 : ∀ b ∈ (pre ++ blk.take 32).drop 32 ++ blk.drop 32, b.toNat < 0x80 :=
    ascii_append (ascii_drop h1 32) (ascii_drop hblk 32)
  unfold klErrBlk
  rw [klErr32_ascii _ _ h1, klErr32_ascii _ _ h2]
  simp

/-! ### The tables, tied to the specification

The three tables reach the body's `pshuf.b` calls as literal `<32 x i8>` lane
lists (`JsonUtf8IR.t1Lanes` and its siblings), and the specification reads them as
`klT1`/`klT2`/`klT3`.  These three identities are what say the body and the
specification shuffle the same bytes; without them the statement would be about
two tables that happen to agree today. -/

theorem t1Lanes_eq : t1Lanes.map (BitVec.ofInt 8) = (klT1.toList).map (fun b => b.toBitVec) := by
  decide

theorem t2Lanes_eq : t2Lanes.map (BitVec.ofInt 8) = (klT2.toList).map (fun b => b.toBitVec) := by
  decide

theorem t3Lanes_eq : t3Lanes.map (BitVec.ofInt 8) = (klT3.toList).map (fun b => b.toBitVec) := by
  decide

/-! ### The interface invariant: `klStage`'s two lengths

`klStage` takes the document's length `n` as a parameter and derives its block
count from the byte list's length.  The two agree exactly when `n = bs.length`,
and *that* is the hypothesis the headline carries: with `n ≠ bs.length` the stage
silently evaluates a different document — `bs.length`'s blocks with `n`'s
tail test — so the verdict would be about neither.  Stated here, before any
theorem uses it, and stated as an equality of `klStage`'s two readings rather
than by dropping `n` from the definition (the ABI has it).

The witness of the false window reading corrected in `JsonUtf8Spec` is stated with
them, because the same paragraph is where a reader meets `klErrByte`. -/

/-- `klStage` at the document's own length.  The invariant the headline consumes:
substituting the byte list's length for `n` changes nothing, so a statement with
`n = bs.length` is a statement about the document the blocks cover. -/
theorem klStage_of_length (bs : List UInt8) (n : Nat) (gate : Bool) (hn : n = bs.length) :
    klStage bs n gate = klStage bs bs.length gate := by
  rw [hn]

/-- The refutation of the window reading of `klErrByte`, at the position whose
window is `(0xF0, 0x41, 0x80, 0x80)`: the position is zero because `NeedsCont`
holds through the `0xF0` three bytes back and both `p1` and `c` are continuations.
The two neighbours are where the sequence is broken, and the two theorems below
are those, so this statement is not left to a reader's reconstruction. -/
theorem klErrByte_window_witness : klErrByte 0xF0 0x41 0x80 0x80 = 0 := by decide

/-- The position one place before that witness: `0x82`, the `twoConts` and
`tooLong` bits together.  `NeedsCont` reads the `0xF0` three bytes back and
demands a continuation at `p1 = 0x41`, which an ASCII byte is not. -/
theorem klErrByte_window_witness_earlier : klErrByte 0x00 0xF0 0x41 0x80 = 0x82 := by
  decide

/-- The position two places before it: `0x01`, `tooShort` — the `0x41` after the
`0xF0` lead, not the continuation that lead requires. -/
theorem klErrByte_window_witness_earliest : klErrByte 0x00 0x00 0xF0 0x41 = 0x01 := by
  decide

/-- The pair the window reading would have called admitted is refused on its own,
which is the half of the correction a byte value cannot show. -/
theorem klPair_witness_refused : ¬ KlPair 0x41 0x80 := by
  decide

/-! ### `klAsciiBlk`, and what the skip condition is

The gate's `ascii` is `klAsciiBlk blk`, which is `decide` over
`(blk.foldl (· ||| ·) 0x00 &&& 0x80) = 0x00`.  "Every byte is below `0x80`" is a
symbolic statement about a `foldl`, so it is proved here **once**, over the
block's byte list, by induction with `BitVec.getLsbD_or`, and the two readings are
an equivalence so that either direction costs nothing later:

* `fold_or_u8_getLsbD` carries the fold's bit 7 as `init`'s bit or the list's
  `any`;
* `and80_u8` turns "the mask cleared bit 7" into "bit 7 is not set";
* `getLsbD_false_iff` turns bit 7 into the byte bound.

`decide` is the right instrument for the tables — `Fin 16` products, 256-case
single-byte facts — and the wrong one here: a symbolic `BitVec 8 × BitVec 8`
crosses the default heartbeat budget, and `UInt8` has no `Decidable (∀ …)`
instance at all.  `native_decide` is not available to this layer at any cost.
-/

/-- `x &&& 0x80 = 0` exactly when bit 7 of `x` is clear. -/
theorem and80_eq_zero (x : BitVec 8) :
    (x &&& BitVec.ofInt 8 0x80 = 0) ↔ x.getLsbD 7 = false := by
  revert x
  decide

/-- Bit 7 clear is the byte bound. -/
theorem getLsbD_false_iff (x : BitVec 8) : x.getLsbD 7 = false ↔ x.toNat < 0x80 := by
  have h := highBit_iff x
  constructor
  · intro hf
    have hnf : ¬ (x.getLsbD 7 = true) := by rw [hf]; simp
    have hlt : ¬ (0x80 ≤ x.toNat) := fun hge => hnf (h.mp hge)
    omega
  · intro hlt
    have hnf : ¬ (x.getLsbD 7 = true) := by
      intro ht
      have hge := h.mpr ht
      omega
    cases hv : x.getLsbD 7 with
    | false => rfl
    | true => exact absurd hv hnf

/-- The fold's bit 7: the initial byte's bit, or the list's, and nothing else.
This is the one induction the block's ASCII reading needs. -/
theorem fold_or_u8_getLsbD (l : List UInt8) (init : UInt8) :
    (l.foldl (· ||| ·) init).toBitVec.getLsbD 7 =
      (init.toBitVec.getLsbD 7 || l.any (fun b => b.toBitVec.getLsbD 7)) := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.any_cons]
      rw [ih, UInt8.toBitVec_or, BitVec.getLsbD_or]
      exact Bool.or_assoc ..

/-- The mask test at a byte. -/
theorem and80_u8 (w : UInt8) : (w &&& 0x80 = 0x00) ↔ w.toBitVec.getLsbD 7 = false := by
  have h := and80_eq_zero w.toBitVec
  constructor
  · intro hw
    refine h.mp ?_
    have hb := congrArg UInt8.toBitVec hw
    simpa [UInt8.toBitVec_and, u80, u0] using hb
  · intro hb
    have hz : w.toBitVec &&& BitVec.ofInt 8 0x80 = 0 := h.mpr hb
    apply UInt8.toBitVec_inj.mp
    simpa [UInt8.toBitVec_and, u80, u0] using hz

/-- **C62 (iii)'s byte test**: `klAsciiBlk` holds exactly when every byte of the
block is below `0x80`.  The gate's skip condition is the block's own bytes and
nothing else, which is what makes the `prev_ascii` the loop carries the previous
block's answer rather than a separate computation. -/
theorem klAsciiBlk_iff (blk : List UInt8) :
    klAsciiBlk blk = true ↔ ∀ b ∈ blk, b.toNat < 0x80 := by
  unfold klAsciiBlk
  rw [decide_eq_true_iff, and80_u8, fold_or_u8_getLsbD, UInt8.toBitVec_zero,
    BitVec.getLsbD_zero, Bool.false_or]
  constructor
  · intro h b hmem
    have hnf : ¬ ((fun b => b.toBitVec.getLsbD 7) b = true) :=
      (List.any_eq_false.mp h) b hmem
    cases hb : b.toBitVec.getLsbD 7 with
    | false => exact (getLsbD_false_iff b.toBitVec).mp hb
    | true => exact absurd hb hnf
  · intro hall
    rw [List.any_eq_false]
    intro b hmem htrue
    have hf : b.toBitVec.getLsbD 7 = false :=
      (getLsbD_false_iff b.toBitVec).mpr (hall b hmem)
    rw [hf] at htrue
    cases htrue

/-! ### The `ub` companion's statement

`utf8StageUndefinedStatement` is the **statement** of
`utf8_stage_undefined_of_no_read` (C63), recorded against the pinned body, the
staged window and the run's fuel, and standing without a proof: it is a `Prop`
definition, so nothing here asserts the claim and no proof obligation fires.  The
reason it is written now rather than after its proof is that a companion written
after the fact tends to acquire exactly the hypotheses its proof could reach —
which is how `step_gep64_back`'s missing `k ≤ 2 ^ 63` came about.  Here the
hypothesis set is C60's, unchanged and unweakened, so a later proof that wants a
smaller set has to say so rather than inherit it.

The claim, and why the interval is the one it is:

* the window is `[b - 3, b + 64 * nb)` — the three staged prefix bytes, the
  document, and the zero padding the block count rounds to.  The body reads
  nothing outside it: the tail's `b + n - 1` is a document byte and the block
  loads are the window's own 64-byte slices;
* a block's 64 bytes are read by the gate's own two loads on **both** gate paths,
  before the gate's test, so a document or padding byte unreadable anywhere in
  the window makes the run `ub` whatever the gate parameter is;
* the two staging clauses — three zero prefix bytes and zero padding — are what
  keep the witness from being vacuous at the window's ends: each makes its
  position readable, so the witness is a *document* byte.  That is not
  bookkeeping; it is why the interval in the statement and the interval the body
  reads are the same one.

The two facts the proof will consume, named here so the proof does not invent
them: a `readBytes` whose range contains an unwritten byte is `none`, so one
missing byte fails the whole load; and the window coverage splits at the block
boundary — block `i`'s loads cover `[b + 64 * i, b + 64 * (i + 1))` and the first
block's carry loads cover `[b - 3, b)`, so the claim is reused per half rather
than re-derived for the whole interval at once (`ub` is monotone in the loads
taken, so the split composes).

Its pin belongs with the theorem, not with this definition: a footprint on an
unproved statement is not evidence about anything, and C64's ceiling is a claim
about what is established. -/

/-- The statement of C63, `utf8_stage_undefined_of_no_read`: an unreadable byte
inside the window the body reads makes the run `ub`.  Stated, not proved. -/
def utf8StageUndefinedStatement : Prop :=
  ∀ (bs : LeanLLVM.JSON.Bytes) (n nb : Nat) (mem : Mem) (b : Nat) (ungated : Bool)
    (w : Nat),
    n = bs.length →
    nb = (n + 63) / 64 →
    3 ≤ b →
    n + 63 < 2 ^ 64 →
    n < 2 ^ 63 →
    0 < n →
    (∀ k, k < 3 → readByte mem (b - 3 + k) = some 0x00) →
    (∀ k, n ≤ k → k < 64 * nb → readByte mem (b + k) = some 0x00) →
    w < 3 + 64 * nb →
    readByte mem (b - 3 + w) = none →
    runFuel utf8Calls (fuelOf nb) utf8Function
      { (initState utf8Function
          [.ptr b, .int 64 (BitVec.ofNat 64 n),
           .int 32 (BitVec.ofNat 32 (if ungated then 1 else 0))]) with mem := mem } =
      some .ub

/-! ### The gate's two paths are one statement

`klAll` carries the gate as a parameter: a block whose sixty-four bytes are ASCII
and whose predecessor was ASCII is skipped by the gated path and evaluated by the
free one.  The two blocks above say the skip changes nothing — a skipped block
contributes `klErrBlk = 0` (`utf8Skip_eq_zero`) and OR-ing a zero vector in is the
identity (`zipWith_zero_right`) — and this section threads that into the fold, so
the verdict is one statement rather than two.

The induction carries three facts: the two gate values' states agree, the
accumulator keeps its lane count, and a set `prev_ascii` means the three bytes
before the current block are ASCII.  The last is what the skip condition needs,
it starts from the window's three zero prefix bytes, and it is carried forward by
`klPre_succ` and the block's own `klAsciiBlk_iff` reading.
-/

/-- The three bytes before block `bi`, as `klAll` reads them. -/
def klPre (win : List UInt8) (bi : Nat) : List UInt8 := (win.drop (64 * bi)).take 3

/-- Block `bi` of the window: sixty-four bytes from the position after the three
prefix bytes. -/
def klBlk (win : List UInt8) (bi : Nat) : List UInt8 := (win.drop (64 * bi + 3)).take 64

/-- `klAll`'s step at one block index and one state, with its `skip` condition
written as `klAll` writes it. -/
def klStep (win : List UInt8) (gate : Bool) (st : List UInt8 × Bool) (bi : Nat) :
    List UInt8 × Bool :=
  (if (gate && klAsciiBlk (klBlk win bi) && st.2) = true then st.1
   else List.zipWith (· ||| ·) st.1 (klErrBlk (klPre win bi) (klBlk win bi)),
   klAsciiBlk (klBlk win bi))

/-- One gate's run over `nb` blocks of the window. -/
def klRun (win : List UInt8) (gate : Bool) (nb : Nat) : List UInt8 × Bool :=
  (List.range nb).foldl (klStep win gate) (List.replicate 32 0x00, true)

/-- **`klAll` is this run.**  The specification's inline step and `klStep` are the
same function: the accumulator is the same `if`, and the second component is the
block's `klAsciiBlk` in both. -/
theorem klAll_eq_klRun (bs : List UInt8) (gate : Bool) :
    klAll gate bs = (klRun (0x00 :: 0x00 :: 0x00 :: bs) gate ((bs.length + 63) / 64)).1 :=
  rfl

/-- The three bytes before block `bi + 1` are block `bi`'s last three.  This is the
window arithmetic the loop's `prev_ascii` invariant rests on. -/
theorem klPre_succ (win : List UInt8) (bi : Nat) :
    klPre win (bi + 1) = (klBlk win bi).drop 61 := by
  unfold klPre klBlk
  rw [show 64 * (bi + 1) = 64 * bi + 3 + 61 from by omega, ← List.drop_drop,
    List.take_drop]

/-- **The gate's step is the same step.**  The state's `prev_ascii` is the whole
of the difference: if it is set, the two ASCII facts give a zero error vector
(`utf8Skip_eq_zero`, from the block's own reading) and `zipWith_zero_right` makes
skipping equal to OR-ing that zero vector in; if it is not set, neither run skips
and the condition is the same on both sides. -/
theorem klStep_gate (win : List UInt8) (bi : Nat) (st : List UInt8 × Bool)
    (hlen : st.1.length = 32)
    (hpre : st.2 = true → ∀ b ∈ klPre win bi, b.toNat < 0x80) :
    klStep win true st bi = klStep win false st bi := by
  unfold klStep
  by_cases hg : (true && klAsciiBlk (klBlk win bi) && st.2) = true
  · have hparts : klAsciiBlk (klBlk win bi) = true ∧ st.2 = true := by
      have := hg
      rw [Bool.and_eq_true, Bool.and_eq_true] at this
      exact ⟨this.1.2, this.2⟩
    obtain ⟨hascii, hprev⟩ := hparts
    have hzero : klErrBlk (klPre win bi) (klBlk win bi) = List.replicate 32 0x00 :=
      utf8Skip_eq_zero _ _ (hpre hprev) (klAsciiBlk_iff _ |>.mp hascii)
    have hfalse : ¬ (false && klAsciiBlk (klBlk win bi) && st.2) = true := by
      simp
    rw [ite_eq_left hg, ite_eq_right hfalse, hzero,
      zipWith_zero_right (· ||| ·) (0 : UInt8) st.1 (fun x => UInt8.or_zero) hlen]
  · have hfalse : ¬ (false && klAsciiBlk (klBlk win bi) && st.2) = true := by
      simp
    rw [ite_eq_right hg, ite_eq_right hfalse]

/-- The step keeps the accumulator's lane count. -/
theorem klStep_length (win : List UInt8) (gate : Bool) (st : List UInt8 × Bool) (bi : Nat)
    (hlen : st.1.length = 32) : (klStep win gate st bi).1.length = 32 := by
  unfold klStep
  by_cases hg : (gate && klAsciiBlk (klBlk win bi) && st.2) = true
  · rw [ite_eq_left hg]
    exact hlen
  · rw [ite_eq_right hg, List.length_zipWith, hlen]
    have hblk : (klErrBlk (klPre win bi) (klBlk win bi)).length = 32 := by
      simp [klErrBlk, klErr32, klErrVec]
    rw [hblk, Nat.min_self]

/-- **The run's invariant.**  The three things the block induction carries: the two
gate values' states agree, the accumulator keeps its lane count, and a set
`prev_ascii` means the three bytes before the next block are ASCII. -/
theorem klRun_invariant (bs : List UInt8) :
    ∀ nb : Nat,
      klRun (0x00 :: 0x00 :: 0x00 :: bs) true nb
        = klRun (0x00 :: 0x00 :: 0x00 :: bs) false nb ∧
      (klRun (0x00 :: 0x00 :: 0x00 :: bs) true nb).1.length = 32 ∧
      ((klRun (0x00 :: 0x00 :: 0x00 :: bs) true nb).2 = true →
        ∀ b ∈ klPre (0x00 :: 0x00 :: 0x00 :: bs) nb, b.toNat < 0x80) := by
  have hbase : ∀ b ∈ klPre (0x00 :: 0x00 :: 0x00 :: bs) 0, b.toNat < 0x80 := by
    intro b hb
    simp [klPre] at hb
    subst hb
    decide
  have hnext : ∀ bi, klAsciiBlk (klBlk (0x00 :: 0x00 :: 0x00 :: bs) bi) = true →
      ∀ b ∈ klPre (0x00 :: 0x00 :: 0x00 :: bs) (bi + 1), b.toNat < 0x80 := by
    intro bi hascii b hb
    rw [klPre_succ] at hb
    exact ascii_drop (klAsciiBlk_iff _ |>.mp hascii) 61 b hb
  intro nb
  induction nb with
  | zero =>
      exact ⟨rfl, rfl, fun _ => hbase⟩
  | succ n ih =>
      obtain ⟨heq, hlen, hpre⟩ := ih
      have hT : klRun (0x00 :: 0x00 :: 0x00 :: bs) true (n + 1)
          = klStep (0x00 :: 0x00 :: 0x00 :: bs) true
              (klRun (0x00 :: 0x00 :: 0x00 :: bs) true n) n := by
        unfold klRun
        rw [List.range_succ, List.foldl_append]
        rfl
      have hF : klRun (0x00 :: 0x00 :: 0x00 :: bs) false (n + 1)
          = klStep (0x00 :: 0x00 :: 0x00 :: bs) false
              (klRun (0x00 :: 0x00 :: 0x00 :: bs) true n) n := by
        have h1 : klRun (0x00 :: 0x00 :: 0x00 :: bs) false (n + 1)
            = klStep (0x00 :: 0x00 :: 0x00 :: bs) false
                (klRun (0x00 :: 0x00 :: 0x00 :: bs) false n) n := by
          unfold klRun
          rw [List.range_succ, List.foldl_append]
          rfl
        rw [h1, ← heq]
      have hstep := klStep_gate (0x00 :: 0x00 :: 0x00 :: bs) n
        (klRun (0x00 :: 0x00 :: 0x00 :: bs) true n) hlen hpre
      refine ⟨?_, ?_, ?_⟩
      · rw [hT, hF, hstep]
      · rw [hT]
        exact klStep_length _ true _ n hlen
      · intro h
        rw [hT] at h
        exact hnext n h

/-- **The gate invariance, unconditionally.**  No hypothesis survives into the
conclusion: the loop's own invariant — a set `prev_ascii` means the three bytes
before the block are ASCII — is proved from the window's three zero prefix bytes
and from `klPre_succ` with `klAsciiBlk_iff`, and the step equality is
`klStep_gate`.  This is what makes the headline one statement for both values of
the gate parameter. -/
theorem klAll_gate_invariant (bs : List UInt8) : klAll true bs = klAll false bs := by
  rw [klAll_eq_klRun bs true, klAll_eq_klRun bs false]
  exact congrArg Prod.fst (klRun_invariant bs ((bs.length + 63) / 64)).1

/-- The window whose `klPre win 1` is not ASCII: the theorem is unconditional, so
this instance needs nothing beyond it.  At `bi = 1` the three bytes before the
block include the `0xF0`, but the skip is decided by the *state's* `prev_ascii`,
which is block 0's flag, and block 0 holds the `0xF0` — so the state-conditioned
step is what carries this case. -/
theorem klAll_gate_invariant_counterexample :
    klAll true (List.replicate 61 0x41 ++ [0xF0, 0x41, 0x41] ++ List.replicate 64 0x41)
      = klAll false (List.replicate 61 0x41 ++ [0xF0, 0x41, 0x41]
          ++ List.replicate 64 0x41) :=
  klAll_gate_invariant _

/-- The same window's block 0 is not ASCII, so its `prev_ascii` is `false` and no
skip is taken at `bi = 1`. -/
theorem counterexample_block0_not_ascii :
    klAsciiBlk (klBlk (0x00 :: 0x00 :: 0x00 ::
      (List.replicate 61 0x41 ++ [0xF0, 0x41, 0x41] ++ List.replicate 64 0x41)) 0) = false := by
  decide

end LeanLLVM.Vellum.JsonUtf8Steps


