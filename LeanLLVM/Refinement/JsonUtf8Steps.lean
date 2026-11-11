/-
The step corpus of the pinned UTF-8 unit's emitted body.

`JsonUtf8IR` holds the fixture, its pin, the call environment `utf8Calls` and the
window the body stages; `JsonUtf8Spec` holds the specification the verdict is
judged against.  This module holds the body's instructions as step lemmas, the
backward `getelementptr` the seven backward sites need, the tables' tie to the
specification, and the two specification-side theorems the statement consumes:
the `klMust` bridge and the gate lemma.  The two loop bodies — `for.body` and
`if.then11.us`, each as one flat chain over its block — the reduce and the tail
are here too.  The loop *run* lemmas, which unroll those bodies a block at a
time, and the refinement theorem itself are stated over these and are not in
this module.

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
import LeanLLVM.Refinement.JsonUtf8IR
import LeanLLVM.Refinement.JsonUtf8Spec
import LeanLLVM.Refinement.JsonEntrySteps
import LeanLLVM.Refinement.JsonS1MasksSteps

namespace LeanLLVM.Refinement.JsonUtf8Steps

open LeanLLVM
open LeanLLVM.Refinement.JsonUtf8IR
open LeanLLVM.Refinement.JsonUtf8Spec
open LeanLLVM.Refinement.BitLanes
open LeanLLVM.Refinement.JsonEntrySteps
open LeanLLVM.Refinement.JsonS1MasksIR
  (evalInstr_load evalInstr_binop evalInstr_binopVec evalInstr_icmp evalInstr_zext
   evalInstr_call evalInstr_vecBitcast evalInstr_icmpVec evalOperands_cons
   vecLanes_self lookupName_bind_ne lookupName_bind_self
   zipReplicate_mapM mapM_some_map pshufbLanes_two_copies_lane getD_two_copies
   split16 split16' bitcastVecLanes_unpackLanes)
open LeanLLVM.Refinement.JsonS1MasksSteps
  (nibLanes andLanes shr4Lanes shr4Lanes_length hiNibbleLanes hiNibbleLanes_length
   nibbleLanes_eq and15_eq_mod packLanes_shr4_mod lane_shr4 shr4Lanes_getD
   unpackLanes_getElem unpackLanes_getElem_toNat mod_mul_div pshufbLanes_length)

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
staged window and the run's fuel, and proved by that theorem below: it is a
`Prop` definition, so the statement is a value in its own right and the proof is
the separate declaration that closes it.  It is written first rather than after
its proof because a companion written
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

Its pin belongs with the theorem, not with this definition: a footprint on a
statement's definition is not evidence about the claim, and C64's ceiling is a
claim about what is established. -/

/-- The statement of C63, `utf8_stage_undefined_of_no_read`: an unreadable byte
inside the window the body reads makes the run `ub`.  Proved below. -/
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

/-! ### The seven backward `getelementptr` sites

`step_gep64_imm_back` above is the immediate form.  The body's backward GEPs are
the three negative immediates at `i8`, and **all seven sites are one of those
three**: the six `-1`/`-2`/`-3` loads — the low half's at `b + 64 · bi`, the high
half's at `b + 64 · bi + 32` — and the tail's `-1` at `b + n`.  Each site's `k` is
the immediate's magnitude, so each needs `k ≤ a` and supplies it from `3 ≤ b`
along its own address chain (`1 ≤ b + 64·bi` and `1 ≤ b + n` from `3 ≤ b`).

The three instantiations below are the sites' *shape*; the loop and tail lemmas
apply them.  That application is the criterion: a backward step that compiles but
is used nowhere leaves the seven sites carrying what they carried before. -/

/-- `-1` as a backward magnitude. -/
theorem neg_toNat_one : ((BitVec.ofInt 64 (-1)) : BitVec 64).toNat = 2 ^ 64 - 1 := by decide

/-- `-2` as a backward magnitude. -/
theorem neg_toNat_two : ((BitVec.ofInt 64 (-2)) : BitVec 64).toNat = 2 ^ 64 - 2 := by decide

/-- `-3` as a backward magnitude. -/
theorem neg_toNat_three : ((BitVec.ofInt 64 (-3)) : BitVec 64).toNat = 2 ^ 64 - 3 := by decide

/-- An `i8` element is one byte, so a `k`-byte displacement is `k`. -/
theorem sizeBytes_i8 : (Ty.int 8).sizeBytes = 1 := rfl

/-- `%d = getelementptr i8, ptr %base, i64 -1`, at a base with one byte below the
index's magnitude: the site shape the six `-1` loads and the tail's use. -/
theorem step_gep64_m1 (env : Env) (s : State) (d base : String) (a : Nat)
    (hb : lookupName env base = some (.ptr a)) (ha : 1 ≤ a) :
    evalInstr utf8Calls (withEnv env s)
        (.gep d (.int 8) (.reg base) (.imm (.int 64 (BitVec.ofInt 64 (-1))))) =
      some (withEnv ((d, .ptr (a - 1)) :: env) s) := by
  have h := step_gep64_imm_back env s d base (.int 8) a 1 (BitVec.ofInt 64 (-1)) hb
    neg_toNat_one (by decide) (by decide) (by simpa [sizeBytes_i8] using ha)
  simpa [sizeBytes_i8] using h

/-- `%d = getelementptr i8, ptr %base, i64 -2`: the site shape of the two `-2`
loads. -/
theorem step_gep64_m2 (env : Env) (s : State) (d base : String) (a : Nat)
    (hb : lookupName env base = some (.ptr a)) (ha : 2 ≤ a) :
    evalInstr utf8Calls (withEnv env s)
        (.gep d (.int 8) (.reg base) (.imm (.int 64 (BitVec.ofInt 64 (-2))))) =
      some (withEnv ((d, .ptr (a - 2)) :: env) s) := by
  have h := step_gep64_imm_back env s d base (.int 8) a 2 (BitVec.ofInt 64 (-2)) hb
    neg_toNat_two (by decide) (by decide) (by simpa [sizeBytes_i8] using ha)
  simpa [sizeBytes_i8] using h

/-- `%d = getelementptr i8, ptr %base, i64 -3`: the site shape of the two `-3`
loads. -/
theorem step_gep64_m3 (env : Env) (s : State) (d base : String) (a : Nat)
    (hb : lookupName env base = some (.ptr a)) (ha : 3 ≤ a) :
    evalInstr utf8Calls (withEnv env s)
        (.gep d (.int 8) (.reg base) (.imm (.int 64 (BitVec.ofInt 64 (-3))))) =
      some (withEnv ((d, .ptr (a - 3)) :: env) s) := by
  have h := step_gep64_imm_back env s d base (.int 8) a 3 (BitVec.ofInt 64 (-3)) hb
    neg_toNat_three (by decide) (by decide) (by simpa [sizeBytes_i8] using ha)
  simpa [sizeBytes_i8] using h

/-! ### The lane identity: the body's packed words read as `klErrBlk`'s bytes

The DFA body computes, for each 32-byte half, one `<4 x i64>` word.  Read as bytes
it is `klErr32`'s error vector for that half, and the two halves or-ed is
`klErrBlk`.  The three tables reach the body as `pshuf.b` lane lists and the
specification as `klT1`/`klT2`/`klT3`, so this is where the two vocabularies meet:
`t1Lanes_eq` and its siblings say the bytes agree, the doubling says how the
shuffle addresses them within a 128-bit lane, and `nibbleLanes_eq` says the
`<16 x i16>` shift produces the high nibble.  The rest is `BitLanes`' algebra —
`unpackLanes_or`/`_and`/`_xor` and `packLanes_zipWith_*` carrying a `<4 x i64>`
operation to the byte lanes.

`getD` is the form both sides use: `pshuf.b`'s own definition reads its control
with `getD`, so a lane fact stated with `getD` applies without a bound hypothesis
at the consumer. -/

/-- The three tables as the lane lists the emission's `pshuf.b` calls carry. -/
def t1V : List (BitVec 8) := t1Lanes.map (BitVec.ofInt 8)

def t2V : List (BitVec 8) := t2Lanes.map (BitVec.ofInt 8)

def t3V : List (BitVec 8) := t3Lanes.map (BitVec.ofInt 8)

/-- One 128-bit lane of a table: the sixteen entries a `pshuf.b` control indexes
within, which are the first half of the specification's thirty-two-lane vector.
The emission writes the table twice, once per lane. -/
def t1HalfV : List (BitVec 8) := ((klT1.toList).map fun b => b.toBitVec).take 16

def t2HalfV : List (BitVec 8) := ((klT2.toList).map fun b => b.toBitVec).take 16

def t3HalfV : List (BitVec 8) := ((klT3.toList).map fun b => b.toBitVec).take 16

theorem t1HalfV_length : t1HalfV.length = 16 := by simp [t1HalfV]

theorem t2HalfV_length : t2HalfV.length = 16 := by simp [t2HalfV]

theorem t3HalfV_length : t3HalfV.length = 16 := by simp [t3HalfV]

/-- The specification's thirty-two-lane table is its first sixteen entries twice,
which is the doubling `pshuf.b`'s lane-local addressing needs. -/
theorem klT1_doubled : klT1.toList = klT1.toList.take 16 ++ klT1.toList.take 16 := by decide

theorem klT2_doubled : klT2.toList = klT2.toList.take 16 ++ klT2.toList.take 16 := by decide

theorem klT3_doubled : klT3.toList = klT3.toList.take 16 ++ klT3.toList.take 16 := by decide

/-- The two copies of a table's sixteen entries are that whole table's bytes:
`t1Lanes_eq` says the call's lanes and `klT1` are the same bytes, and this says
their split is the doubling. -/
theorem t1HalfV_doubled : t1HalfV ++ t1HalfV = (klT1.toList).map fun b => b.toBitVec := by
  decide

theorem t2HalfV_doubled : t2HalfV ++ t2HalfV = (klT2.toList).map fun b => b.toBitVec := by
  decide

theorem t3HalfV_doubled : t3HalfV ++ t3HalfV = (klT3.toList).map fun b => b.toBitVec := by
  decide

/-- The call's table lane list is that doubling: `t1Lanes_eq` ties the two
vocabularies' bytes and these rewrite the lane list into the two copies. -/
theorem t1V_eq : t1V = t1HalfV ++ t1HalfV := by
  unfold t1V
  rw [t1Lanes_eq, ← t1HalfV_doubled]

theorem t2V_eq : t2V = t2HalfV ++ t2HalfV := by
  unfold t2V
  rw [t2Lanes_eq, ← t2HalfV_doubled]

theorem t3V_eq : t3V = t3HalfV ++ t3HalfV := by
  unfold t3V
  rw [t3Lanes_eq, ← t3HalfV_doubled]

/-- A `Vector UInt8 32`'s list has thirty-two entries. -/
theorem klT_length (t : Vector UInt8 32) : t.toList.length = 32 := by simp

/-- `getD` inside a list is `getElem`. -/
theorem getD_of_lt {α : Type} {i : Nat} (l : List α) (d : α) (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- A table half's entry at a nibble is `klAt`'s, at the carrier the table is
indexed by. -/
theorem t1HalfV_getD (n : Nat) (hn : n < 16) :
    t1HalfV.getD n 0 = (klAt klT1 n).toBitVec := by
  rw [getD_of_lt t1HalfV 0 (by rw [t1HalfV_length]; exact hn)]
  unfold t1HalfV
  rw [List.getElem_take, List.getElem_map]
  congr 1
  unfold klAt
  rw [getD_of_lt klT1.toList 0x00 (by rw [klT_length]; omega)]

theorem t2HalfV_getD (n : Nat) (hn : n < 16) :
    t2HalfV.getD n 0 = (klAt klT2 n).toBitVec := by
  rw [getD_of_lt t2HalfV 0 (by rw [t2HalfV_length]; exact hn)]
  unfold t2HalfV
  rw [List.getElem_take, List.getElem_map]
  congr 1
  unfold klAt
  rw [getD_of_lt klT2.toList 0x00 (by rw [klT_length]; omega)]

theorem t3HalfV_getD (n : Nat) (hn : n < 16) :
    t3HalfV.getD n 0 = (klAt klT3 n).toBitVec := by
  rw [getD_of_lt t3HalfV 0 (by rw [t3HalfV_length]; exact hn)]
  unfold t3HalfV
  rw [List.getElem_take, List.getElem_map]
  congr 1
  unfold klAt
  rw [getD_of_lt klT3.toList 0x00 (by rw [klT_length]; omega)]

/-- A `pshuf.b` lane at `t1`: the lane's table entry, or zero when the control's
high bit is set (which no nibble control's is). -/
theorem pshufb_t1_lane (ctl : List (BitVec 8)) (hc : ctl.length = 32) {i : Nat} (hi : i < 32) :
    (pshufbLanes t1V ctl).getD i 0 =
      (if (ctl.getD i 0).getLsbD 7 = true then (0 : BitVec 8)
       else (klAt klT1 ((ctl.getD i 0).toNat % 16)).toBitVec) := by
  rw [t1V_eq, pshufbLanes_two_copies_lane t1HalfV t1HalfV_length ctl hi hc]
  by_cases hb : (ctl.getD i 0).getLsbD 7 = true
  · rw [ite_eq_left hb, ite_eq_left hb]
  · rw [ite_eq_right hb, ite_eq_right hb]
    exact t1HalfV_getD _ (Nat.mod_lt _ (by decide))

theorem pshufb_t2_lane (ctl : List (BitVec 8)) (hc : ctl.length = 32) {i : Nat} (hi : i < 32) :
    (pshufbLanes t2V ctl).getD i 0 =
      (if (ctl.getD i 0).getLsbD 7 = true then (0 : BitVec 8)
       else (klAt klT2 ((ctl.getD i 0).toNat % 16)).toBitVec) := by
  rw [t2V_eq, pshufbLanes_two_copies_lane t2HalfV t2HalfV_length ctl hi hc]
  by_cases hb : (ctl.getD i 0).getLsbD 7 = true
  · rw [ite_eq_left hb, ite_eq_left hb]
  · rw [ite_eq_right hb, ite_eq_right hb]
    exact t2HalfV_getD _ (Nat.mod_lt _ (by decide))

theorem pshufb_t3_lane (ctl : List (BitVec 8)) (hc : ctl.length = 32) {i : Nat} (hi : i < 32) :
    (pshufbLanes t3V ctl).getD i 0 =
      (if (ctl.getD i 0).getLsbD 7 = true then (0 : BitVec 8)
       else (klAt klT3 ((ctl.getD i 0).toNat % 16)).toBitVec) := by
  rw [t3V_eq, pshufbLanes_two_copies_lane t3HalfV t3HalfV_length ctl hi hc]
  by_cases hb : (ctl.getD i 0).getLsbD 7 = true
  · rw [ite_eq_left hb, ite_eq_left hb]
  · rw [ite_eq_right hb, ite_eq_right hb]
    exact t3HalfV_getD _ (Nat.mod_lt _ (by decide))

/-- A byte list's lane list, at an index. -/
theorem byteLanes_getD {bs : List UInt8} {i : Nat} (hi : i < bs.length) :
    (byteLanes bs).getD i 0 = (bs[i]).toBitVec := by
  rw [getD_of_lt (byteLanes bs) 0 (by rw [byteLanes_length]; exact hi)]
  simp [byteLanes]

/-- The same, in the `getElem` form the lane facts end at. -/
theorem byteLanes_getElem {bs : List UInt8} {i : Nat} (hi : i < bs.length) :
    (byteLanes bs)[i]'(by rw [byteLanes_length]; exact hi) = (bs[i]).toBitVec := by
  simp [byteLanes]

/-- `nibLanes`' entry: the byte masked to its low nibble. -/
theorem nibLanes_getD {l : List (BitVec 8)} {i : Nat} (hi : i < l.length) :
    (nibLanes l).getD i 0 = (l[i] &&& BitVec.ofInt 8 15) := by
  rw [getD_of_lt (nibLanes l) 0 (by rw [nibLanes, List.length_map]; exact hi)]
  simp [nibLanes]

/-- The low-nibble control's lane, read as a natural: it is the byte's own low
nibble. -/
theorem nibLanes_toNat {l : List (BitVec 8)} {i : Nat} (hi : i < l.length) :
    ((nibLanes l).getD i 0).toNat = (l[i]).toNat % 16 := by
  rw [nibLanes_getD hi]
  have h15 : (BitVec.ofInt 8 15) = (0x0F : BitVec 8) := by decide
  rw [h15, and15_eq_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- No low-nibble control sets its high bit: `pshuf.b`'s zero arm is never taken. -/
theorem nibLanes_getLsbD {l : List (BitVec 8)} {i : Nat} (hi : i < l.length) :
    ((nibLanes l).getD i 0).getLsbD 7 = false := by
  rw [getLsbD_false_iff, nibLanes_toNat hi]
  omega

/-- A high-nibble lane of the `<16 x i16>` shift. -/
theorem hiNibbleLanes_getD {V : Nat} {i : Nat} (hi : i < 32) :
    (hiNibbleLanes V).getD i 0 = BitVec.ofNat 8 ((V / 2 ^ (8 * i + 4)) % 16) := by
  rw [getD_of_lt (hiNibbleLanes V) 0 (by rw [hiNibbleLanes_length]; exact hi)]
  simp only [hiNibbleLanes, List.getElem_ofFn]

/-- The shift's own arithmetic: lane `i`'s high nibble is byte `i`'s. -/
theorem hiNibbleLanes_toNat {bs : List UInt8} (hlen : bs.length = 32) {i : Nat} (hi : i < 32) :
    ((hiNibbleLanes (bytesToNat bs)).getD i 0).toNat = (bs[i]).toNat / 16 := by
  rw [hiNibbleLanes_getD hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [show (2 : Nat) ^ (8 * i + 4) = 2 ^ (8 * i) * 2 ^ 4 from by rw [← Nat.pow_add],
    show (2 : Nat) ^ 4 = 16 from by decide,
    ← Nat.div_div_eq_div_mul,
    ← mod_mul_div _ 16 16 (by decide) (by decide)]
  rw [show (16 * 16 : Nat) = 256 from by decide,
    show (2 : Nat) ^ (8 * i) = 256 ^ i from by
      rw [show (256 : Nat) = 2 ^ 8 from by decide, ← Nat.pow_mul, Nat.mul_comm],
    bytesToNat_div_pow bs i, List.getElem?_eq_getElem (by omega), Option.map_some,
    Option.getD_some]

/-- No high-nibble control sets its high bit either. -/
theorem hiNibbleLanes_getLsbD {V : Nat} {i : Nat} (hi : i < 32) :
    ((hiNibbleLanes V).getD i 0).getLsbD 7 = false := by
  rw [getLsbD_false_iff, hiNibbleLanes_getD hi, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- `zipWith` read at an index, in the `getD` form the lane facts use. -/
theorem getD_zipWith {α β γ : Type} (f : α → β → γ) (a : List α) (b : List β)
    (za : α) (zb : β) (z : γ) {i : Nat}
    (hi : i < a.length) (hi' : i < b.length) :
    (List.zipWith f a b).getD i z = f (a.getD i za) (b.getD i zb) := by
  rw [getD_of_lt (List.zipWith f a b) z (by rw [List.length_zipWith]; exact Nat.lt_min.mpr ⟨hi, hi'⟩),
    List.getElem_zipWith, ← getD_of_lt a za hi, ← getD_of_lt b zb hi']

/-- The must word of one half as the emission forms it: the two saturating
subtracts against `0x70` and `0x60`, or-ed. -/
def mustHalf (p2 p3 : List (BitVec 8)) : List (BitVec 8) :=
  List.zipWith (· ||| ·)
    (List.zipWith subsSat p3 (List.replicate 32 (BitVec.ofInt 8 0x70)))
    (List.zipWith subsSat p2 (List.replicate 32 (BitVec.ofInt 8 0x60)))

/-- The structural word of one half as the emission forms it: the three table
lookups, the two `and`s, in the body's own order.  `V1` is the half's word as the
`<16 x i16>` shift sees it and `Vc` the same at the byte three positions later, so
the two high-nibble lookups read words rather than lane lists. -/
def scHalf (p1 : List (BitVec 8)) (V1 Vc : Nat) : List (BitVec 8) :=
  List.zipWith (· &&& ·)
    (List.zipWith (· &&& ·) (pshufbLanes t2V (hiNibbleLanes V1))
      (pshufbLanes t1V (nibLanes p1)))
    (pshufbLanes t3V (hiNibbleLanes Vc))

/-- The `t1` lookup of a half, at a lane: `T1`'s entry at the byte's low nibble. -/
theorem t1_lane_of (P : List UInt8) (h : P.length = 32) {i : Nat} (hi : i < 32) :
    (pshufbLanes t1V (nibLanes (byteLanes P))).getD i 0
      = (klAt klT1 ((P[i]).toNat % 16)).toBitVec := by
  have hbp : i < (byteLanes P).length := by rw [byteLanes_length, h]; exact hi
  have hlen : (nibLanes (byteLanes P)).length = 32 := by
    rw [nibLanes, List.length_map, byteLanes_length, h]
  rw [pshufb_t1_lane _ hlen hi, ite_eq_right (by rw [nibLanes_getLsbD hbp]; simp),
    nibLanes_toNat hbp, byteLanes_getElem (by rw [h]; exact hi), UInt8.toNat_toBitVec,
    Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))]

/-- The `t2` lookup of a half, at a lane: `T2`'s entry at the byte's high nibble,
which the `<16 x i16>` shift produced. -/
theorem t2_lane_of (bs : List UInt8) (h : bs.length = 32) {i : Nat} (hi : i < 32) :
    (pshufbLanes t2V (hiNibbleLanes (bytesToNat bs))).getD i 0
      = (klAt klT2 ((bs[i]).toNat / 16)).toBitVec := by
  rw [pshufb_t2_lane _ (hiNibbleLanes_length (bytesToNat bs)) hi,
    ite_eq_right (by rw [hiNibbleLanes_getLsbD hi]; simp),
    hiNibbleLanes_toNat h hi,
    Nat.mod_eq_of_lt (by have := (bs[i]).toNat_lt; omega)]

/-- The `t3` lookup of a half, at a lane: `T3`'s entry at the high nibble of the
byte three positions later. -/
theorem t3_lane_of (bs : List UInt8) (h : bs.length = 32) {i : Nat} (hi : i < 32) :
    (pshufbLanes t3V (hiNibbleLanes (bytesToNat bs))).getD i 0
      = (klAt klT3 ((bs[i]).toNat / 16)).toBitVec := by
  rw [pshufb_t3_lane _ (hiNibbleLanes_length (bytesToNat bs)) hi,
    ite_eq_right (by rw [hiNibbleLanes_getLsbD hi]; simp),
    hiNibbleLanes_toNat h hi,
    Nat.mod_eq_of_lt (by have := (bs[i]).toNat_lt; omega)]

/-- The three table words' `and`, in the order the emission writes it, is the
specification's order: `T1 & T2 & T3`. -/
theorem and_toBitVec_comm (a b c : UInt8) :
    b.toBitVec &&& a.toBitVec &&& c.toBitVec = (a &&& b &&& c).toBitVec := by
  rw [UInt8.toBitVec_and, UInt8.toBitVec_and, BitVec.and_comm b.toBitVec a.toBitVec]

/-- The must word of one half, at a lane: `(p3 -s 0x70) | (p2 -s 0x60)`. -/
theorem mustHalf_getD (P2 P3 : List UInt8) (h2 : P2.length = 32) (h3 : P3.length = 32)
    {i : Nat} (hi : i < 32) :
    (mustHalf (byteLanes P2) (byteLanes P3)).getD i 0
      = (subsSat (P3[i]).toBitVec (BitVec.ofInt 8 0x70)
          ||| subsSat (P2[i]).toBitVec (BitVec.ofInt 8 0x60)) := by
  have h3' : (byteLanes P3).length = 32 := by rw [byteLanes_length, h3]
  have h2' : (byteLanes P2).length = 32 := by rw [byteLanes_length, h2]
  have hr3 : (List.replicate 32 (BitVec.ofInt 8 0x70)).length = 32 := by simp
  have hr2 : (List.replicate 32 (BitVec.ofInt 8 0x60)).length = 32 := by simp
  unfold mustHalf
  rw [getD_zipWith (· ||| ·)
    (List.zipWith subsSat (byteLanes P3) (List.replicate 32 (BitVec.ofInt 8 0x70)))
    (List.zipWith subsSat (byteLanes P2) (List.replicate 32 (BitVec.ofInt 8 0x60)))
    (0 : BitVec 8) (0 : BitVec 8) (0 : BitVec 8)
    (by rw [List.length_zipWith, h3', hr3, Nat.min_self]; exact hi)
    (by rw [List.length_zipWith, h2', hr2, Nat.min_self]; exact hi)]
  rw [getD_zipWith subsSat (byteLanes P3) (List.replicate 32 (BitVec.ofInt 8 0x70))
      (0 : BitVec 8) (BitVec.ofInt 8 0x70) 0 (by rw [h3']; exact hi) (by rw [hr3]; exact hi),
    getD_zipWith subsSat (byteLanes P2) (List.replicate 32 (BitVec.ofInt 8 0x60))
      (0 : BitVec 8) (BitVec.ofInt 8 0x60) 0 (by rw [h2']; exact hi) (by rw [hr2]; exact hi),
    getD_of_lt (List.replicate 32 (BitVec.ofInt 8 0x70)) _ (by rw [hr3]; exact hi),
    getD_of_lt (List.replicate 32 (BitVec.ofInt 8 0x60)) _ (by rw [hr2]; exact hi),
    List.getElem_replicate, List.getElem_replicate,
    byteLanes_getD (by rw [h3]; exact hi), byteLanes_getD (by rw [h2]; exact hi)]

/-- The structural word of one half, at a lane: `T1[lo p1] & T2[hi p1] & T3[hi c]`.
The two high-nibble tables read the half's own `i16` shift, so the lane fact is
`hiNibbleLanes_toNat` applied at the word's two sources. -/
theorem scHalf_getD (P1 C : List UInt8) (V1 Vc : Nat) (h1 : P1.length = 32)
    (hc : C.length = 32) (hV1 : V1 = bytesToNat P1) (hVc : Vc = bytesToNat C)
    {i : Nat} (hi : i < 32) :
    (scHalf (byteLanes P1) V1 Vc).getD i 0 = (klSc (P1[i]) (C[i])).toBitVec := by
  have h1' : (byteLanes P1).length = 32 := by rw [byteLanes_length, h1]
  have hhc : (hiNibbleLanes Vc).length = 32 := hiNibbleLanes_length Vc
  have hh1 : (hiNibbleLanes V1).length = 32 := hiNibbleLanes_length V1
  have hn1 : (nibLanes (byteLanes P1)).length = 32 := by
    rw [nibLanes, List.length_map, h1']
  have hq1 : (pshufbLanes t1V (nibLanes (byteLanes P1))).length = 32 := by
    rw [pshufbLanes_length, hn1]
  have hq2 : (pshufbLanes t2V (hiNibbleLanes V1)).length = 32 := by
    rw [pshufbLanes_length, hh1]
  have hq3 : (pshufbLanes t3V (hiNibbleLanes Vc)).length = 32 := by
    rw [pshufbLanes_length, hhc]
  unfold scHalf
  rw [getD_zipWith (· &&& ·)
    (List.zipWith (· &&& ·) (pshufbLanes t2V (hiNibbleLanes V1))
      (pshufbLanes t1V (nibLanes (byteLanes P1))))
    (pshufbLanes t3V (hiNibbleLanes Vc)) (0 : BitVec 8) (0 : BitVec 8) (0 : BitVec 8)
    (by rw [List.length_zipWith, hq2, hq1, Nat.min_self]; exact hi) (by rw [hq3]; exact hi),
    getD_zipWith (· &&& ·) (pshufbLanes t2V (hiNibbleLanes V1))
      (pshufbLanes t1V (nibLanes (byteLanes P1))) (0 : BitVec 8) (0 : BitVec 8) (0 : BitVec 8)
      (by rw [hq2]; exact hi) (by rw [hq1]; exact hi)]
  rw [hV1, hVc, t2_lane_of P1 h1 hi, t1_lane_of P1 h1 hi, t3_lane_of C hc hi]
  unfold klSc
  exact and_toBitVec_comm _ _ _


/-! ### The packed word, and its byte reading

The half's error word is `errHalf` — the body's own expression, at the accumulator's
`<4 x i64>` — and `errHalfBytes` reads it back as bytes.  The distribution lemmas
carry the two `<4 x i64>` operations to the byte lanes, so the half's bytes are the
must word masked to its high bit, xor the structural word, lane by lane. -/

/-- The high-bit mask the emission's `<4 x i64>` `and` applies: `0x80` in every
byte. -/
def highLanes64 : List (BitVec 64) :=
  List.replicate 4 (BitVec.ofInt 64 (-9187201950435737472))

/-- The same mask read as bytes. -/
theorem highLanes64_bytes :
    bitcastVecLanes 8 32 highLanes64 = List.replicate 32 (BitVec.ofInt 8 0x80) := by
  decide

/-- The body's error word for one half, at the accumulator's own lane width. -/
def errHalf (p1 p2 p3 : List (BitVec 8)) (V1 Vc : Nat) : List (BitVec 64) :=
  List.zipWith (· ^^^ ·)
    (List.zipWith (· &&& ·) (bitcastVecLanes 64 4 (mustHalf p2 p3)) highLanes64)
    (bitcastVecLanes 64 4 (scHalf p1 V1 Vc))

/-- The same word read as bytes. -/
def errHalfBytes (p1 p2 p3 : List (BitVec 8)) (V1 Vc : Nat) : List (BitVec 8) :=
  bitcastVecLanes 8 32 (errHalf p1 p2 p3 V1 Vc)

/-- The `<32 x i8>` ↔ `<4 x i64>` bitcast commutes with `|||`. -/
theorem bitcastVecLanes_or64 (a b : List (BitVec 64)) (h : a.length = b.length) :
    bitcastVecLanes 8 32 (List.zipWith (· ||| ·) a b)
      = List.zipWith (· ||| ·) (bitcastVecLanes 8 32 a) (bitcastVecLanes 8 32 b) := by
  simp only [bitcastVecLanes, packLanes_zipWith_or h, unpackLanes_or]

/-- The same at `&&&`. -/
theorem bitcastVecLanes_and64 (a b : List (BitVec 64)) (h : a.length = b.length) :
    bitcastVecLanes 8 32 (List.zipWith (· &&& ·) a b)
      = List.zipWith (· &&& ·) (bitcastVecLanes 8 32 a) (bitcastVecLanes 8 32 b) := by
  simp only [bitcastVecLanes, packLanes_zipWith_and h, unpackLanes_and]

/-- The same at `^^^`. -/
theorem bitcastVecLanes_xor64 (a b : List (BitVec 64)) (h : a.length = b.length) :
    bitcastVecLanes 8 32 (List.zipWith (· ^^^ ·) a b)
      = List.zipWith (· ^^^ ·) (bitcastVecLanes 8 32 a) (bitcastVecLanes 8 32 b) := by
  simp only [bitcastVecLanes, packLanes_zipWith_xor h, unpackLanes_xor]

/-- A thirty-two-lane byte vector is its own bitcast: the packing and the split
at the same width are the identity there. -/
theorem bitcastVecLanes_self {l : List (BitVec 8)} (h : l.length = 32) :
    bitcastVecLanes 8 32 l = l := by
  unfold bitcastVecLanes
  simpa [h] using (unpackLanes_packLanes (w := 8) l)

/-- The two-step reading is the byte list itself: packing a byte list, splitting it
at `i64` and splitting the result back at `i8` returns the bytes. -/
theorem byteView_of64 {l : List (BitVec 8)} (h : l.length = 32) :
    bitcastVecLanes 8 32 (bitcastVecLanes 64 4 l) = l := by
  have hp : packLanes l < 2 ^ 256 := by
    have := packLanes_lt l
    rwa [show l.length * 8 = 256 from by omega] at this
  unfold bitcastVecLanes
  rw [packLanes_unpackLanes, show (4 * 64 : Nat) = 256 from by decide, Nat.mod_eq_of_lt hp]
  simpa [h] using (unpackLanes_packLanes (w := 8) l)

/-- The must word has thirty-two lanes. -/
theorem mustHalf_length (p2 p3 : List (BitVec 8)) (h2 : p2.length = 32)
    (h3 : p3.length = 32) : (mustHalf p2 p3).length = 32 := by
  unfold mustHalf
  simp [List.length_zipWith, h2, h3]

/-- The structural word has thirty-two lanes. -/
theorem scHalf_length (p1 : List (BitVec 8)) (V1 Vc : Nat) (h1 : p1.length = 32) :
    (scHalf p1 V1 Vc).length = 32 := by
  unfold scHalf
  simp [List.length_zipWith, pshufbLanes_length, hiNibbleLanes_length, nibLanes, h1]

/-- **The half's word, read as bytes**: the mask keeps the must word's high bit,
and the xor is byte-wise, so the body's `<4 x i64>` expression is the must/sc
pair at the byte lanes. -/
theorem errHalfBytes_eq_zip (p1 p2 p3 : List (BitVec 8)) (V1 Vc : Nat)
    (h1 : p1.length = 32) (h2 : p2.length = 32) (h3 : p3.length = 32) :
    errHalfBytes p1 p2 p3 V1 Vc
      = List.zipWith (· ^^^ ·)
          (List.zipWith (· &&& ·) (mustHalf p2 p3) (List.replicate 32 (BitVec.ofInt 8 0x80)))
          (scHalf p1 V1 Vc) := by
  have hm : (mustHalf p2 p3).length = 32 := mustHalf_length p2 p3 h2 h3
  have hs : (scHalf p1 V1 Vc).length = 32 := scHalf_length p1 V1 Vc h1
  have hl : (bitcastVecLanes 64 4 (mustHalf p2 p3)).length = 4 := by
    simp [bitcastVecLanes, unpackLanes_length]
  have hlg : highLanes64.length = 4 := by simp [highLanes64]
  unfold errHalfBytes errHalf
  rw [bitcastVecLanes_xor64
      (a := List.zipWith (· &&& ·) (bitcastVecLanes 64 4 (mustHalf p2 p3)) highLanes64)
      (b := bitcastVecLanes 64 4 (scHalf p1 V1 Vc))
      (h := by simp [List.length_zipWith, hl, hlg, bitcastVecLanes, unpackLanes_length]),
    bitcastVecLanes_and64 (a := bitcastVecLanes 64 4 (mustHalf p2 p3)) (b := highLanes64)
      (h := by simp [hl, hlg]),
    byteView_of64 (l := mustHalf p2 p3) hm, highLanes64_bytes,
    byteView_of64 (l := scHalf p1 V1 Vc) hs]

/-- `klErrVec`'s lane count. -/
theorem klErrVec_length (s : List UInt8) : (klErrVec s).length = 32 := by
  simp [klErrVec]

/-- A stream's byte inside its own length. -/
theorem klByte_eq_getElem {s : List UInt8} {j : Nat} (h : j < s.length) :
    klByte s j = s[j] := by
  unfold klByte
  rw [getD_of_lt s 0x00 h]

/-- A slice's lane, at the index the error vector reads. -/
theorem slice_getElem {s : List UInt8} {m i : Nat} (hi : i < 32) (hm : m + 32 ≤ s.length) :
    ((s.drop m).take 32)[i]'(by simp; omega) = s[m + i]'(by omega) := by
  rw [List.getElem_take, List.getElem_drop]

/-- The error vector's lane, in the `getD` form the identity compares at. -/
theorem byteLanes_klErrVec_getD {s : List UInt8} {i : Nat} (hi : i < 32) :
    (byteLanes (klErrVec s)).getD i 0
      = (klErrByte (klByte s i) (klByte s (i + 1)) (klByte s (i + 2))
          (klByte s (i + 3))).toBitVec := by
  rw [getD_of_lt (byteLanes (klErrVec s)) 0
    (by rw [byteLanes_length, klErrVec_length]; exact hi)]
  rw [byteLanes_getElem (by rw [klErrVec_length]; exact hi)]
  congr 1
  unfold klErrVec
  rw [List.getElem_map, List.getElem_range]

/-- **One half's error word is `klErr32`'s bytes.**  The four slices are `p3`, `p2`,
`p1` and `c` — the stream from the block's first carry byte, at offsets `0`, `1`,
`2` and `3` — and the lane's window is `(s[k], s[k+1], s[k+2], s[k+3])`, which is
`klErrByte`'s argument order.  `klMust_bridge` is what turns the emission's masked
must word into `klMust`, and the three lane facts turn the table lookups into
`klSc`'s three `klAt`s. -/
theorem errHalfBytes_eq (s : List UInt8) (h35 : 35 ≤ s.length) :
    errHalfBytes (byteLanes ((s.drop 2).take 32)) (byteLanes ((s.drop 1).take 32))
        (byteLanes (s.take 32)) (bytesToNat ((s.drop 2).take 32))
        (bytesToNat ((s.drop 3).take 32))
      = byteLanes (klErrVec s) := by
  have hP1 : ((s.drop 2).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop]; omega
  have hP2 : ((s.drop 1).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop]; omega
  have hP3 : (s.take 32).length = 32 := by
    simp only [List.length_take]; omega
  have hC : ((s.drop 3).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop]; omega
  have bP1 : (byteLanes ((s.drop 2).take 32)).length = 32 := by rw [byteLanes_length, hP1]
  have bP2 : (byteLanes ((s.drop 1).take 32)).length = 32 := by rw [byteLanes_length, hP2]
  have bP3 : (byteLanes (s.take 32)).length = 32 := by rw [byteLanes_length, hP3]
  have hmLen : (mustHalf (byteLanes ((s.drop 1).take 32)) (byteLanes (s.take 32))).length = 32 :=
    mustHalf_length _ _ bP2 bP3
  have hsLen : (scHalf (byteLanes ((s.drop 2).take 32)) (bytesToNat ((s.drop 2).take 32))
      (bytesToNat ((s.drop 3).take 32))).length = 32 := scHalf_length _ _ _ bP1
  rw [errHalfBytes_eq_zip _ _ _ _ _ bP1 bP2 bP3]
  apply List.ext_getElem
  · simp only [List.length_zipWith, List.length_replicate, hmLen, hsLen,
      byteLanes_length, klErrVec_length]
    omega
  · intro i h1 h2
    have hk : i < 32 := by
      simp only [List.length_zipWith, List.length_replicate, hmLen, hsLen] at h1
      omega
    rw [List.getElem_zipWith, List.getElem_zipWith, List.getElem_replicate]
    rw [← getD_of_lt (mustHalf (byteLanes ((s.drop 1).take 32)) (byteLanes (s.take 32))) 0
          (by rw [hmLen]; exact hk),
        ← getD_of_lt (scHalf (byteLanes ((s.drop 2).take 32)) (bytesToNat ((s.drop 2).take 32))
            (bytesToNat ((s.drop 3).take 32))) 0 (by rw [hsLen]; exact hk),
        ← getD_of_lt (byteLanes (klErrVec s)) 0
          (by rw [byteLanes_length, klErrVec_length]; exact hk)]
    rw [mustHalf_getD _ _ hP2 hP3 hk, scHalf_getD _ _ _ _ hP1 hC rfl rfl hk,
      byteLanes_klErrVec_getD hk]
    rw [BitVec.and_comm, BitVec.or_comm, klMust_bridge]
    rw [klByte_eq_getElem (by omega), klByte_eq_getElem (by omega),
      klByte_eq_getElem (by omega), klByte_eq_getElem (by omega)]
    simp only [List.getElem_take, List.getElem_drop]
    simp only [show (1 : Nat) + i = i + 1 from by omega,
      show (2 : Nat) + i = i + 2 from by omega, show (3 : Nat) + i = i + 3 from by omega]
    unfold klErrByte
    rw [BitVec.xor_comm, ← UInt8.toBitVec_xor, UInt8.toBitVec_inj]


/-! ### The block, and the accumulator

`klErrBlk` is the two halves' `klErr32`s or-ed, and `klErrVec` of the stream is one
half's.  The ties below say the body's block word is that byte list and that the
accumulator's `|||` is the specification's — the second at the byte carrier, because
the specification's accumulator is a `List UInt8` and the body's is a `<4 x i64>`
word. -/

/-- `klByte` of a taken prefix, inside it. -/
theorem klByte_take {s : List UInt8} (h : 35 ≤ s.length) {k : Nat} (hk : k < 35) :
    klByte (s.take 35) k = klByte s k := by
  unfold klByte
  rw [getD_of_lt (s.take 35) 0x00 (by simp; omega), getD_of_lt s 0x00 (by omega),
    List.getElem_take]

/-- `klErrVec` of a stream is unchanged by taking the first thirty-five bytes: a
lane reads `s[k .. k+3]` and the last lane's last read is index 34. -/
theorem klErrVec_take (s : List UInt8) (h : 35 ≤ s.length) :
    klErrVec (s.take 35) = klErrVec s := by
  apply List.ext_getElem
  · simp [klErrVec]
  · intro i h1 h2
    have hk : i < 32 := by simpa [klErrVec] using h1
    simp only [klErrVec, List.getElem_map, List.getElem_range]
    rw [klByte_take h (by omega), klByte_take h (by omega), klByte_take h (by omega),
      klByte_take h (by omega)]

/-- The byte carrier's `|||` is the lane carrier's: `byteLanes` commutes with the
accumulator's `zipWith`, which is what carries a word-level step to the
specification's `List UInt8`. -/
theorem byteLanes_zipWith_or_toBitVec (l₁ l₂ : List UInt8) :
    (List.zipWith (· ||| ·) l₁ l₂).map UInt8.toBitVec
      = List.zipWith (· ||| ·) (l₁.map UInt8.toBitVec) (l₂.map UInt8.toBitVec) := by
  induction l₁ generalizing l₂ with
  | nil => rfl
  | cons x xs ih =>
      cases l₂ with
      | nil => rfl
      | cons y ys =>
          simp only [List.zipWith_cons_cons, List.map_cons]
          rw [UInt8.toBitVec_or, ih]

theorem byteLanes_zipWith_or (l₁ l₂ : List UInt8) :
    byteLanes (List.zipWith (· ||| ·) l₁ l₂)
      = List.zipWith (· ||| ·) (byteLanes l₁) (byteLanes l₂) := by
  simpa [byteLanes] using byteLanes_zipWith_or_toBitVec l₁ l₂

/-- One block's error word, at the accumulator's lanes: the two halves or-ed. -/
def errBlk (lo hi : List (BitVec 64)) : List (BitVec 64) := List.zipWith (· ||| ·) lo hi

/-- The half identity, in the form a rewrite can find: `errHalfBytes` unfolds to
this, and a `rw` matches the `bitcastVecLanes` term rather than the abbreviation. -/
theorem errHalf_bitcast_eq (s : List UInt8) (h35 : 35 ≤ s.length) :
    bitcastVecLanes 8 32
        (errHalf (byteLanes ((s.drop 2).take 32)) (byteLanes ((s.drop 1).take 32))
          (byteLanes (s.take 32)) (bytesToNat ((s.drop 2).take 32))
          (bytesToNat ((s.drop 3).take 32)))
      = byteLanes (klErrVec s) :=
  errHalfBytes_eq s h35

/-- **One block's error word is `klErrBlk`'s bytes.**  The two halves' streams are
`s` and `s.drop 32` — the second half's three carry bytes are the first half's last
three — which is `klErrBlk`'s `(pre ++ blk.take 32).drop 32` read as a drop of the
whole stream. -/
theorem errBlkBytes_eq (s : List UInt8) (h67 : 67 ≤ s.length) :
    bitcastVecLanes 8 32
        (errBlk
          (errHalf (byteLanes ((s.drop 2).take 32)) (byteLanes ((s.drop 1).take 32))
            (byteLanes (s.take 32)) (bytesToNat ((s.drop 2).take 32))
            (bytesToNat ((s.drop 3).take 32)))
          (errHalf (byteLanes (((s.drop 32).drop 2).take 32))
            (byteLanes (((s.drop 32).drop 1).take 32)) (byteLanes ((s.drop 32).take 32))
            (bytesToNat (((s.drop 32).drop 2).take 32))
            (bytesToNat (((s.drop 32).drop 3).take 32))))
      = byteLanes (List.zipWith (· ||| ·) (klErrVec s) (klErrVec (s.drop 32))) := by
  unfold errBlk
  rw [bitcastVecLanes_or64 (h := by
    simp [errHalf, bitcastVecLanes, unpackLanes_length, highLanes64, List.length_zipWith])]
  rw [errHalf_bitcast_eq s (by omega),
    errHalf_bitcast_eq (s.drop 32) (by simp [List.length_drop]; omega),
    ← byteLanes_zipWith_or]

/-- **`klErrBlk` is the two halves' error vectors.**  The lower half is the first
thirty-five bytes of the stream and the upper half the same stream from offset
thirty-two, which is what the body's two loads-and-shifts produce. -/
theorem klErrBlk_eq_vecs (pre blk : List UInt8) (hpre : pre.length = 3)
    (hblk : 64 ≤ blk.length) :
    klErrBlk pre blk
      = List.zipWith (· ||| ·) (klErrVec (pre ++ blk)) (klErrVec ((pre ++ blk).drop 32)) := by
  have hlen : 67 ≤ (pre ++ blk).length := by
    rw [List.length_append, hpre]; omega
  have htake : pre ++ blk.take 32 = (pre ++ blk).take 35 := by
    rw [List.take_append, show (35 - pre.length) = 32 from by rw [hpre],
      show pre.take 35 = pre from List.take_of_length_le (by rw [hpre]; decide)]
  have hsplit : pre ++ blk = (pre ++ blk.take 32) ++ blk.drop 32 := by
    rw [List.append_assoc, List.take_append_drop]
  have hd2 : ((pre ++ blk.take 32) ++ blk.drop 32).drop 32
      = (pre ++ blk.take 32).drop 32 ++ blk.drop 32 :=
    List.drop_append_of_le_length (by rw [List.length_append, List.length_take]; omega)
  have hdrop : (pre ++ blk.take 32).drop 32 ++ blk.drop 32 = (pre ++ blk).drop 32 := by
    rw [hsplit, hd2]
  have hlen35 : 35 ≤ (pre ++ blk).length := by omega
  unfold klErrBlk klErr32
  rw [hdrop, htake, klErrVec_take (pre ++ blk) hlen35]


/-! ### The step corpus the two bodies need

The scalar steps are `JsonEntrySteps`' at this module's call environment; the
vector steps are the shapes this body uses — `zipWith` at a lane width, the two
splat-wise operations (`&& 0x0F` and the `<16 x i16>` shift), the three intrinsics
and the `phi`.  Each is stated at an opaque environment with its operands as
hypotheses, which is the shape `JsonEntrySteps` and `JsonS1MasksSteps` measured as
linear in instruction count.

The values are the lists `Value.vec` carries, so a step's conclusion is the list a
later lane fact reads and not a word a proof has to unpack. -/

/-- A byte-lane `zipWith` of two thirty-two-lane lists has thirty-two lanes. -/
theorem len32_zip (f : BitVec 8 → BitVec 8 → BitVec 8) (a b : List (BitVec 8))
    (ha : a.length = 32) (hb : b.length = 32) : (List.zipWith f a b).length = 32 := by
  rw [List.length_zipWith, ha, hb, Nat.min_self]

/-- The same at the accumulator's four lanes. -/
theorem len4_zip64 (f : BitVec 64 → BitVec 64 → BitVec 64) (a b : List (BitVec 64))
    (ha : a.length = 4) (hb : b.length = 4) : (List.zipWith f a b).length = 4 := by
  rw [List.length_zipWith, ha, hb, Nat.min_self]

/-- A nibble list has its input's lane count. -/
theorem nibLanes_len (l : List (BitVec 8)) : (nibLanes l).length = l.length := by
  simp [nibLanes]

/-- A `pshuf.b` result has the control's lane count. -/
theorem pshufb_len32 (t ctl : List (BitVec 8)) (h : ctl.length = 32) :
    (pshufbLanes t ctl).length = 32 := by rw [pshufbLanes_length, h]

/-- `zipWith` under `mapM`: a lane-wise operation over two equal-length lists. -/
theorem zip_mapM_binop {w : Nat} (op : BinOp) (f : BitVec w → BitVec w → BitVec w)
    (hf : ∀ x y, evalBinop op x y = some (f x y)) :
    ∀ (l₁ l₂ : List (BitVec w)), l₁.length = l₂.length →
      (l₁.zip l₂).mapM (fun p => evalBinop op p.1 p.2) = some (List.zipWith f l₁ l₂) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ _; rfl
  | cons x xs ih =>
      intro l₂ hlen
      cases l₂ with
      | nil => simp at hlen
      | cons y ys =>
          simp only [List.zip_cons_cons, List.mapM_cons, List.zipWith_cons_cons,
            List.length_cons] at hlen ⊢
          rw [hf x y, ih ys (by omega)]
          rfl

/-- `%d = and <n x w> %a, %b`. -/
theorem utf8_step_vec_and (env : Env) (s : State) (d a b : String) (n w : Nat)
    (x y : List (BitVec w))
    (hx : lookupName env a = some (.vec n w x)) (hy : lookupName env b = some (.vec n w y))
    (hxlen : x.length = n) (hylen : y.length = n) :
    evalInstr utf8Calls (withEnv env s) (.binopVec d .and n w (.reg a) (.reg b)) =
      some (withEnv ((d, .vec n w (List.zipWith (· &&& ·) x y)) :: env) s) := by
  rw [evalInstr_binopVec (l1 := x) (l2 := y) (ls := List.zipWith (· &&& ·) x y)
    hxlen hylen (by simp only [withEnv, evalOperand, hx])
    (by simp only [withEnv, evalOperand, hy])
    (zip_mapM_binop .and (· &&& ·) (fun x y => rfl) x y (by rw [hxlen, hylen]))]
  simp only [withEnv, State.bind]

/-- `%d = or <n x w> %a, %b`. -/
theorem utf8_step_vec_or (env : Env) (s : State) (d a b : String) (n w : Nat)
    (x y : List (BitVec w))
    (hx : lookupName env a = some (.vec n w x)) (hy : lookupName env b = some (.vec n w y))
    (hxlen : x.length = n) (hylen : y.length = n) :
    evalInstr utf8Calls (withEnv env s) (.binopVec d .or n w (.reg a) (.reg b)) =
      some (withEnv ((d, .vec n w (List.zipWith (· ||| ·) x y)) :: env) s) := by
  rw [evalInstr_binopVec (l1 := x) (l2 := y) (ls := List.zipWith (· ||| ·) x y)
    hxlen hylen (by simp only [withEnv, evalOperand, hx])
    (by simp only [withEnv, evalOperand, hy])
    (zip_mapM_binop .or (· ||| ·) (fun x y => rfl) x y (by rw [hxlen, hylen]))]
  simp only [withEnv, State.bind]

/-- `%d = xor <n x w> %a, %b`. -/
theorem utf8_step_vec_xor (env : Env) (s : State) (d a b : String) (n w : Nat)
    (x y : List (BitVec w))
    (hx : lookupName env a = some (.vec n w x)) (hy : lookupName env b = some (.vec n w y))
    (hxlen : x.length = n) (hylen : y.length = n) :
    evalInstr utf8Calls (withEnv env s) (.binopVec d .xor n w (.reg a) (.reg b)) =
      some (withEnv ((d, .vec n w (List.zipWith (· ^^^ ·) x y)) :: env) s) := by
  rw [evalInstr_binopVec (l1 := x) (l2 := y) (ls := List.zipWith (· ^^^ ·) x y)
    hxlen hylen (by simp only [withEnv, evalOperand, hx])
    (by simp only [withEnv, evalOperand, hy])
    (zip_mapM_binop .xor (· ^^^ ·) (fun x y => rfl) x y (by rw [hxlen, hylen]))]
  simp only [withEnv, State.bind]

/-- `%d = and <32 x i8> %r, splat (i8 15)`: the low nibbles. -/
theorem utf8_step_and15 (env : Env) (s : State) (d r : String) (l : List (BitVec 8))
    (h : lookupName env r = some (.vec 32 8 l)) (hlen : l.length = 32) :
    evalInstr utf8Calls (withEnv env s)
        (.binopVec d .and 32 8 (.reg r) (.imm (.splat 32 8 (BitVec.ofInt 8 15)))) =
      some (withEnv ((d, .vec 32 8 (nibLanes l)) :: env) s) := by
  have hm : (l.zip (List.replicate l.length (BitVec.ofInt 8 15))).mapM
      (fun p => evalBinop .and p.1 p.2) = some (nibLanes l) :=
    zipReplicate_mapM l (BitVec.ofInt 8 15) (fun a b => evalBinop .and a b)
      (fun x => x &&& BitVec.ofInt 8 15) (fun x => rfl)
  rw [evalInstr_binopVec (l1 := l)
    (l2 := List.replicate 32 (BitVec.ofInt 8 15)) (ls := nibLanes l) hlen (by simp)
    (by simp only [withEnv, evalOperand, h])
    (by simp [withEnv, evalOperand, Const.toValue])
    (by rw [← hlen]; exact hm)]
  simp only [withEnv, State.bind]

/-- `%d = lshr <16 x i16> %r, splat (i16 4)`: the `i16` shift the high-nibble
tables read. -/
theorem utf8_step_shr16 (env : Env) (s : State) (d r : String) (V : Nat)
    (h : lookupName env r = some (.vec 16 16 (unpackLanes 16 16 V))) :
    evalInstr utf8Calls (withEnv env s)
        (.binopVec d .lshr 16 16 (.reg r) (.imm (.splat 16 16 (BitVec.ofInt 16 4)))) =
      some (withEnv ((d, .vec 16 16 (shr4Lanes V)) :: env) s) := by
  have hm : ((unpackLanes 16 16 V).zip (List.replicate 16 (BitVec.ofInt 16 4))).mapM
      (fun p => evalBinop .lshr p.1 p.2) = some (shr4Lanes V) := by
    have h := zipReplicate_mapM (unpackLanes 16 16 V) (BitVec.ofInt 16 4)
      (fun a b => evalBinop .lshr a b) (fun x => x >>> 4)
      (fun x => by
        show some (BitVec.ushiftRight x (BitVec.ofInt 16 4).toNat) = some (x >>> 4)
        rw [show (BitVec.ofInt 16 4).toNat = 4 from by decide]; rfl)
    rwa [show (unpackLanes 16 16 V).length = 16 from unpackLanes_length 16 16 V] at h
  rw [evalInstr_binopVec (l1 := unpackLanes 16 16 V)
    (l2 := List.replicate 16 (BitVec.ofInt 16 4)) (ls := shr4Lanes V)
    (by rw [unpackLanes_length]) (by simp)
    (by simp only [withEnv, evalOperand, h])
    (by simp [withEnv, evalOperand, Const.toValue]) hm]
  simp only [withEnv, State.bind, shr4Lanes]

/-- `%d = bitcast <4 x i64> %r to <32 x i8>`. -/
theorem utf8_step_bc64_8 (env : Env) (s : State) (d r : String) (V : Nat) (hV : V < 2 ^ 256)
    (h : lookupName env r = some (.vec 4 64 (unpackLanes 64 4 V))) :
    evalInstr utf8Calls (withEnv env s) (.vecBitcast d 4 64 32 8 (.reg r)) =
      some (withEnv ((d, .vec 32 8 (unpackLanes 8 32 V)) :: env) s) := by
  rw [evalInstr_vecBitcast (hv := by simp only [withEnv, evalOperand, h])
    (hl := vecLanes_self (unpackLanes_length 64 4 V)) (hwidth := by decide)]
  rw [bitcastVecLanes_unpackLanes, show (4 * 64 : Nat) = 256 from by decide,
    Nat.mod_eq_of_lt hV]
  simp only [withEnv, State.bind]

/-- `%d = bitcast <4 x i64> %r to <16 x i16>`. -/
theorem utf8_step_bc64_16 (env : Env) (s : State) (d r : String) (V : Nat) (hV : V < 2 ^ 256)
    (h : lookupName env r = some (.vec 4 64 (unpackLanes 64 4 V))) :
    evalInstr utf8Calls (withEnv env s) (.vecBitcast d 4 64 16 16 (.reg r)) =
      some (withEnv ((d, .vec 16 16 (unpackLanes 16 16 V)) :: env) s) := by
  rw [evalInstr_vecBitcast (hv := by simp only [withEnv, evalOperand, h])
    (hl := vecLanes_self (unpackLanes_length 64 4 V)) (hwidth := by decide)]
  rw [bitcastVecLanes_unpackLanes, show (4 * 64 : Nat) = 256 from by decide,
    Nat.mod_eq_of_lt hV]
  simp only [withEnv, State.bind]

/-- `%d = bitcast <16 x i16> %r to <32 x i8>`. -/
theorem utf8_step_bc16_8 (env : Env) (s : State) (d r : String) (V : Nat)
    (h : lookupName env r = some (.vec 16 16 (shr4Lanes V))) :
    evalInstr utf8Calls (withEnv env s) (.vecBitcast d 16 16 32 8 (.reg r)) =
      some (withEnv ((d, .vec 32 8 (unpackLanes 8 32 (packLanes (shr4Lanes V)))) :: env) s) := by
  rw [evalInstr_vecBitcast (hv := by simp only [withEnv, evalOperand, h])
    (hl := vecLanes_self (shr4Lanes_length V)) (hwidth := by decide)]
  rfl

/-- `%d = bitcast <32 x i8> %r to <4 x i64>`. -/
theorem utf8_step_bc8_64 (env : Env) (s : State) (d r : String) (l : List (BitVec 8))
    (h : lookupName env r = some (.vec 32 8 l)) (hlen : l.length = 32) :
    evalInstr utf8Calls (withEnv env s) (.vecBitcast d 32 8 4 64 (.reg r)) =
      some (withEnv ((d, .vec 4 64 (unpackLanes 64 4 (packLanes l))) :: env) s) := by
  rw [evalInstr_vecBitcast (hv := by simp only [withEnv, evalOperand, h])
    (hl := vecLanes_self hlen) (hwidth := by decide)]
  rfl

/-- `%d = and <4 x i64> %r, splat (i64 …)`: the high-bit mask, which the emission
applies at the accumulator's own lanes. -/
theorem utf8_step_andHigh (env : Env) (s : State) (d r : String) (l : List (BitVec 64))
    (h : lookupName env r = some (.vec 4 64 l)) (hlen : l.length = 4) :
    evalInstr utf8Calls (withEnv env s)
        (.binopVec d .and 4 64 (.reg r)
          (.imm (.splat 4 64 (BitVec.ofInt 64 (-9187201950435737472))))) =
      some (withEnv ((d, .vec 4 64 (List.zipWith (· &&& ·) l highLanes64)) :: env) s) := by
  rw [evalInstr_binopVec (l1 := l) (l2 := highLanes64)
    (ls := List.zipWith (· &&& ·) l highLanes64) hlen (by simp [highLanes64])
    (by simp only [withEnv, evalOperand, h])
    (by simp only [evalOperand, Const.toValue, highLanes64])
    (zip_mapM_binop .and (· &&& ·) (fun _ _ => rfl) l highLanes64 (by simp [highLanes64, hlen]))]
  simp only [withEnv, State.bind]

/-- A `pshuf.b` call at a literal table, as the emission spells it. -/
theorem utf8_step_pshufb (env : Env) (s : State) (dst r : String) (tabInt : List Int)
    (tab ctl : List (BitVec 8)) (htabLen : tabInt.length = 32)
    (htab : tabInt.map (BitVec.ofInt 8) = tab)
    (h : lookupName env r = some (.vec 32 8 ctl)) :
    evalInstr utf8Calls (withEnv env s)
        (.call dst v32i8 "llvm.x86.avx2.pshuf.b"
          [(v32i8, .imm (.vector 8 (tabInt.map (BitVec.ofInt 8)))), (v32i8, .reg r)]) =
      some (withEnv ((dst, .vec 32 8 (pshufbLanes tab ctl)) :: env) s) := by
  have ha : evalOperands (withEnv env s)
      [(v32i8, .imm (.vector 8 (tabInt.map (BitVec.ofInt 8)))), (v32i8, .reg r)]
      = some [.vec 32 8 (tabInt.map (BitVec.ofInt 8)), .vec 32 8 ctl] := by
    rw [evalOperands_cons
      (v := .vec 32 8 (tabInt.map (BitVec.ofInt 8))) (vs := [.vec 32 8 ctl])
      (by simp [evalOperand, Const.toValue, List.length_map, htabLen])
      (evalOperands_cons (by simp only [withEnv, evalOperand, h]) rfl)]
  rw [evalInstr_call ha (utf8Calls_pshufb (tabInt.map (BitVec.ofInt 8)) ctl s.mem s.next), htab]
  simp only [withEnv, State.bind]

/-- `%d = call @llvm.usub.sat.v32i8(%r, splat (i8 c))`: the saturating subtract
against a splat constant. -/
theorem utf8_step_usubSat (env : Env) (s : State) (dst r : String) (c : Int)
    (l : List (BitVec 8)) (hlen : l.length = 32)
    (h : lookupName env r = some (.vec 32 8 l)) :
    evalInstr utf8Calls (withEnv env s)
        (.call dst v32i8 "llvm.usub.sat.v32i8"
          [(v32i8, .reg r), (v32i8, .imm (.splat 32 8 (BitVec.ofInt 8 c)))]) =
      some (withEnv ((dst, .vec 32 8
        (List.zipWith subsSat l (List.replicate 32 (BitVec.ofInt 8 c)))) :: env) s) := by
  have ha : evalOperands (withEnv env s)
      [(v32i8, .reg r), (v32i8, .imm (.splat 32 8 (BitVec.ofInt 8 c)))]
      = some [.vec 32 8 l, .vec 32 8 (List.replicate 32 (BitVec.ofInt 8 c))] := by
    rw [evalOperands_cons
      (v := .vec 32 8 l) (vs := [.vec 32 8 (List.replicate 32 (BitVec.ofInt 8 c))])
      (by simp only [withEnv, evalOperand, h])
      (evalOperands_cons (by simp [evalOperand, Const.toValue]) rfl)]
  rw [evalInstr_call ha (utf8Calls_usubSat l (List.replicate 32 (BitVec.ofInt 8 c)) s.mem s.next)]
  simp only [withEnv, State.bind]

/-- A `ptestz` call: the two operands packed into 256-bit words and the test read
there. -/
theorem utf8_step_ptestz (env : Env) (s : State) (dst a : String) (b : Operand)
    (la lb : List (BitVec 64)) (hbv : evalOperand (withEnv env s) b = some (.vec 4 64 lb))
    (hlen : lb.length = 4)
    (h : lookupName env a = some (.vec 4 64 la)) (hlena : la.length = 4) :
    evalInstr utf8Calls (withEnv env s)
        (.call dst (.int 32) "llvm.x86.avx.ptestz.256" [(v4i64, .reg a), (v4i64, b)]) =
      some (withEnv ((dst, .int 32 (ptestz (BitVec.ofNat 256 (packLanes la))
        (BitVec.ofNat 256 (packLanes lb)))) :: env) s) := by
  have ha : evalOperands (withEnv env s) [(v4i64, .reg a), (v4i64, b)]
      = some [.vec 4 64 la, .vec 4 64 lb] := by
    rw [evalOperands_cons (v := .vec 4 64 la) (vs := [.vec 4 64 lb])
      (by simp only [withEnv, evalOperand, h])
      (evalOperands_cons (v := .vec 4 64 lb) (vs := []) hbv rfl)]
  rw [evalInstr_call ha (utf8Calls_ptestz la lb s.mem s.next)]
  simp only [withEnv, State.bind]

/-- A `phi` reached from `p`, at this module's call environment. -/
theorem utf8_phi (env : Env) (s : State) (d : String) (ty : Ty) (inc : List (String × Operand))
    (p : String) (op : Operand) (v : Value) (hpre : s.pre = some p)
    (hinc : phiIncoming p inc = some op) (hop : evalOperand (withEnv env s) op = some v) :
    evalInstr utf8Calls (withEnv env s) (.phi d ty inc) = some (withEnv ((d, v) :: env) s) := by
  rw [evalInstr_phi (s := withEnv env s) hpre hinc hop]
  rfl

/-- An eight-bit load at a readable byte. -/
theorem utf8_step_load8 (env : Env) (s : State) (d p : String) (a : Nat) (v : BitVec 8)
    (hp : lookupName env p = some (.ptr a)) (hv : readBytes s.mem a 1 = some (natToBytes v.toNat 1)) :
    evalInstr utf8Calls (withEnv env s) (.load d (.int 8) (.reg p)) =
      some (withEnv ((d, .int 8 v) :: env) s) := by
  rw [evalInstr_load (hp := evalOperand_reg_of env s p (.ptr a) hp)
    (hv := by
      rw [show (withEnv env s).mem = s.mem from rfl]
      simp only [loadValue, show (8 = 0) = False from by decide, ite_false,
        show (8 + 7) / 8 = 1 from by decide, hv, natToBytes_toNat,
        show (256 : Nat) ^ 1 = 2 ^ 8 from by decide]
      rw [Nat.mod_eq_of_lt v.isLt, BitVec.ofNat_toNat])]
  simp [withEnv, State.bind]


/-! ### The algebra the accumulator step needs

`packLanes` is the natural a `<4 x i64>` word carries, and the specification's
accumulator is a byte list; the two meet at `packLanes (byteLanes bs) = bytesToNat
bs`.  The step's own arithmetic is then `Nat.or`'s, so the emitted `or` order and
the specification's are the same value. -/

/-- Packing a byte list's lanes is the list's natural. -/
theorem packLanes_byteLanes (bs : List UInt8) : packLanes (byteLanes bs) = bytesToNat bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      have h1 : packLanes (byteLanes (b :: bs))
          = b.toNat + 2 ^ 8 * packLanes (byteLanes bs) := by
        simp only [byteLanes, List.map_cons, packLanes]
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt b.toNat_lt]
      rw [h1, ih, show (2 : Nat) ^ 8 = 256 from by decide]
      simp only [bytesToNat]

/-- The byte bitcast does not change the word a lane list carries. -/
theorem packLanes_bitcast8 (l : List (BitVec 64)) (h : l.length = 4) :
    packLanes (bitcastVecLanes 8 32 l) = packLanes l := by
  unfold bitcastVecLanes
  rw [packLanes_unpackLanes, show (32 * 8 : Nat) = 256 from by decide,
    Nat.mod_eq_of_lt (by have := packLanes_lt l; rwa [h] at this)]

/-- The little-endian encoding inverts the interpretation. -/
theorem natToBytes_bytesToNat (bs : List UInt8) : natToBytes (bytesToNat bs) bs.length = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      show UInt8.ofNat ((b.toNat + 256 * bytesToNat bs) % 256) ::
          natToBytes ((b.toNat + 256 * bytesToNat bs) / 256) bs.length = b :: bs
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.toNat_lt,
        Nat.add_mul_div_left _ _ (by decide : 0 < 256), Nat.div_eq_of_lt b.toNat_lt,
        Nat.zero_add, ih, UInt8.ofNat_toNat]

/-- A slice of the stream, thirty-two bytes wide, is a full lane list. -/
theorem byteLanes_slice_length (s : List UInt8) (m : Nat) (hm : m + 32 ≤ s.length) :
    (byteLanes ((s.drop m).take 32)).length = 32 := by
  rw [byteLanes_length, List.length_take, List.length_drop]
  omega

/-- `bytesToNat` of an `|||` of two equally long byte lists is the `|||` of their
naturals. -/
theorem bytesToNat_zipWith_or (a b : List UInt8) (h : a.length = b.length) :
    bytesToNat (List.zipWith (· ||| ·) a b) = bytesToNat a ||| bytesToNat b := by
  rw [← packLanes_byteLanes, byteLanes_zipWith_or,
    packLanes_zipWith_or (by rw [byteLanes_length, byteLanes_length, h]),
    packLanes_byteLanes, packLanes_byteLanes]

/-- `klErrBlk` is a thirty-two-lane vector. -/
theorem klErrBlk_length (pre blk : List UInt8) : (klErrBlk pre blk).length = 32 := by
  simp [klErrBlk, klErr32, klErrVec]

/-- An `or`'s three terms in the order the two carriers write them: the emission
puts the accumulator between the halves and the specification puts it first. -/
theorem or_rotate (a b c : Nat) : (a ||| b) ||| c = b ||| (a ||| c) := by
  rw [Nat.or_comm a b, Nat.or_assoc]

/-- The high-nibble lanes from the shift are `nibbleLanes_eq`'s. -/
theorem nibLanes_shr4 (V : Nat) :
    nibLanes (unpackLanes 8 32 (packLanes (shr4Lanes V))) = hiNibbleLanes V := by
  rw [nibLanes]
  have h15 : (BitVec.ofInt 8 15) = (0x0F : BitVec 8) := by decide
  rw [h15]
  exact nibbleLanes_eq V

/-- The half word has four lanes. -/
theorem errHalf_length (p1 p2 p3 : List (BitVec 8)) (V1 Vc : Nat) (h1 : p1.length = 32)
    (h2 : p2.length = 32) (h3 : p3.length = 32) : (errHalf p1 p2 p3 V1 Vc).length = 4 := by
  unfold errHalf
  simp [List.length_zipWith, bitcastVecLanes, unpackLanes_length, highLanes64]

/-- The half's natural is its error vector's. -/
theorem packLanes_errHalf (s : List UInt8) (h35 : 35 ≤ s.length) :
    packLanes (errHalf (byteLanes ((s.drop 2).take 32)) (byteLanes ((s.drop 1).take 32))
        (byteLanes (s.take 32)) (bytesToNat ((s.drop 2).take 32))
        (bytesToNat ((s.drop 3).take 32))) = bytesToNat (klErrVec s) := by
  have h1 : (byteLanes ((s.drop 2).take 32)).length = 32 := byteLanes_slice_length s 2 (by omega)
  have h2 : (byteLanes ((s.drop 1).take 32)).length = 32 := byteLanes_slice_length s 1 (by omega)
  have h3 : (byteLanes (s.take 32)).length = 32 := by
    rw [byteLanes_length, List.length_take]; omega
  have hlen := errHalf_length _ _ _ (bytesToNat ((s.drop 2).take 32))
    (bytesToNat ((s.drop 3).take 32)) h1 h2 h3
  have h := congrArg packLanes (errHalf_bitcast_eq s h35)
  rwa [packLanes_bitcast8 _ hlen, packLanes_byteLanes] at h

/-- **The accumulator step, at the specification's own vocabulary.**  The body ors
the two halves' words into the word it carries; that word, read as a natural, is
the specification's accumulator list or-ed with `klErrBlk` — the vector `klErrAll`
counts its windows over. -/
theorem errBlk_word_eq (s : List UInt8) (acc : List UInt8) (u8k : List (BitVec 64))
    (pre blk : List UInt8) (hs : s = pre ++ blk) (h67 : 67 ≤ s.length)
    (hacc : acc.length = 32)
    (hu8klen : u8k.length = 4)
    (hpre3 : pre.length = 3) (hblk64 : blk.length = 64)
    (hu8k : packLanes u8k = bytesToNat acc) :
    List.zipWith (· ||| ·)
        (List.zipWith (· ||| ·)
          (errHalf (byteLanes ((s.drop 2).take 32)) (byteLanes ((s.drop 1).take 32))
            (byteLanes (s.take 32)) (bytesToNat ((s.drop 2).take 32))
            (bytesToNat ((s.drop 3).take 32)))
          u8k)
        (errHalf (byteLanes (((s.drop 32).drop 2).take 32))
          (byteLanes (((s.drop 32).drop 1).take 32)) (byteLanes ((s.drop 32).take 32))
          (bytesToNat (((s.drop 32).drop 2).take 32))
          (bytesToNat (((s.drop 32).drop 3).take 32)))
      = unpackLanes 64 4 (bytesToNat (List.zipWith (· ||| ·) acc (klErrBlk pre blk))) := by
  subst hs
  have hLs : 35 ≤ (pre ++ blk).length := by omega
  have hLs' : 35 ≤ ((pre ++ blk).drop 32).length := by rw [List.length_drop]; omega
  have h1 : (byteLanes (((pre ++ blk).drop 2).take 32)).length = 32 := byteLanes_slice_length (pre ++ blk) 2 (by omega)
  have h2 : (byteLanes (((pre ++ blk).drop 1).take 32)).length = 32 := byteLanes_slice_length (pre ++ blk) 1 (by omega)
  have h3 : (byteLanes ((pre ++ blk).take 32)).length = 32 := by
    rw [byteLanes_length, List.length_take]; omega
  have h4 : (byteLanes ((((pre ++ blk).drop 32).drop 2).take 32)).length = 32 := by
    rw [List.drop_drop]
    exact byteLanes_slice_length (pre ++ blk) 34 (by omega)
  have h5 : (byteLanes ((((pre ++ blk).drop 32).drop 1).take 32)).length = 32 := by
    rw [List.drop_drop]
    exact byteLanes_slice_length (pre ++ blk) 33 (by omega)
  have h6 : (byteLanes (((pre ++ blk).drop 32).take 32)).length = 32 := by
    rw [byteLanes_length, List.length_take, List.length_drop]; omega
  have eL : (errHalf (byteLanes (((pre ++ blk).drop 2).take 32)) (byteLanes (((pre ++ blk).drop 1).take 32))
      (byteLanes ((pre ++ blk).take 32)) (bytesToNat (((pre ++ blk).drop 2).take 32))
      (bytesToNat (((pre ++ blk).drop 3).take 32))).length = 4 :=
    errHalf_length _ _ _ (bytesToNat (((pre ++ blk).drop 2).take 32))
      (bytesToNat (((pre ++ blk).drop 3).take 32)) h1 h2 h3
  have eH : (errHalf (byteLanes ((((pre ++ blk).drop 32).drop 2).take 32))
      (byteLanes ((((pre ++ blk).drop 32).drop 1).take 32)) (byteLanes (((pre ++ blk).drop 32).take 32))
      (bytesToNat ((((pre ++ blk).drop 32).drop 2).take 32))
      (bytesToNat ((((pre ++ blk).drop 32).drop 3).take 32))).length = 4 :=
    errHalf_length _ _ _ (bytesToNat ((((pre ++ blk).drop 32).drop 2).take 32))
      (bytesToNat ((((pre ++ blk).drop 32).drop 3).take 32)) h4 h5 h6
  have hl4 : (List.zipWith (· ||| ·) (List.zipWith (· ||| ·)
      (errHalf (byteLanes (((pre ++ blk).drop 2).take 32)) (byteLanes (((pre ++ blk).drop 1).take 32))
        (byteLanes ((pre ++ blk).take 32)) (bytesToNat (((pre ++ blk).drop 2).take 32)) (bytesToNat (((pre ++ blk).drop 3).take 32)))
      u8k)
      (errHalf (byteLanes ((((pre ++ blk).drop 32).drop 2).take 32))
        (byteLanes ((((pre ++ blk).drop 32).drop 1).take 32)) (byteLanes (((pre ++ blk).drop 32).take 32))
        (bytesToNat ((((pre ++ blk).drop 32).drop 2).take 32))
        (bytesToNat ((((pre ++ blk).drop 32).drop 3).take 32)))).length = 4 := by
    simp only [List.length_zipWith, eL, hu8klen, eH, Nat.min_self]
  have hp : packLanes (List.zipWith (· ||| ·) (List.zipWith (· ||| ·)
      (errHalf (byteLanes (((pre ++ blk).drop 2).take 32)) (byteLanes (((pre ++ blk).drop 1).take 32))
        (byteLanes ((pre ++ blk).take 32)) (bytesToNat (((pre ++ blk).drop 2).take 32)) (bytesToNat (((pre ++ blk).drop 3).take 32)))
      u8k)
      (errHalf (byteLanes ((((pre ++ blk).drop 32).drop 2).take 32))
        (byteLanes ((((pre ++ blk).drop 32).drop 1).take 32)) (byteLanes (((pre ++ blk).drop 32).take 32))
        (bytesToNat ((((pre ++ blk).drop 32).drop 2).take 32))
        (bytesToNat ((((pre ++ blk).drop 32).drop 3).take 32))))
      = bytesToNat (List.zipWith (· ||| ·) acc (klErrBlk pre blk)) := by
    rw [packLanes_zipWith_or (by simp only [List.length_zipWith, eL, hu8klen, eH, Nat.min_self]),
      packLanes_zipWith_or (by simp only [eL, hu8klen, Nat.min_self]),
      hu8k, packLanes_errHalf (pre ++ blk) hLs, packLanes_errHalf ((pre ++ blk).drop 32) hLs',
      bytesToNat_zipWith_or _ _ (by rw [hacc, klErrBlk_length]),
      klErrBlk_eq_vecs pre blk hpre3 (by omega),
      bytesToNat_zipWith_or _ _ (by rw [klErrVec_length, klErrVec_length]),
      or_rotate]
  rw [← hp, ← hl4]
  exact (unpackLanes_packLanes (w := 64) _).symm


/-! ### The scalar and predicate steps, at `utf8Calls`

`JsonEntrySteps`' scalar steps are stated at `entryCalls`; the instruction arms they
describe do not consult the call environment, so these are the same statements at
this module's, which is what the two bodies run under. -/

theorem utf8_step_shl (env : Env) (s : State) (d src : String) (w : Nat)
    (x c : BitVec w) (h : lookupName env src = some (.int w x)) :
    evalInstr utf8Calls (withEnv env s) (.binop d .shl w (.reg src) (.imm (.int w c))) =
      some (withEnv ((d, .int w (x <<< c.toNat)) :: env) s) := by
  rw [evalInstr_binop (ha := evalOperand_reg_of env s src (.int w x) h)
    (hb := evalOperand_lit_of _ w c) (hr := by rfl)]
  simp only [withEnv, State.bind, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rfl

theorem utf8_step_add (env : Env) (s : State) (d src : String) (w : Nat)
    (x c : BitVec w) (h : lookupName env src = some (.int w x)) :
    evalInstr utf8Calls (withEnv env s) (.binop d .add w (.reg src) (.imm (.int w c))) =
      some (withEnv ((d, .int w (x + c)) :: env) s) := by
  rw [evalInstr_binop (ha := evalOperand_reg_of env s src (.int w x) h)
    (hb := evalOperand_lit_of _ w c) (hr := by rfl)]
  simp only [withEnv, State.bind, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem utf8_step_icmp_eq (env : Env) (s : State) (d a b : String) (w : Nat)
    (x y : BitVec w) (ha : lookupName env a = some (.int w x))
    (hb : lookupName env b = some (.int w y)) :
    evalInstr utf8Calls (withEnv env s) (.icmp d .eq w (.reg a) (.reg b)) =
      some (withEnv ((d, .int 1 (BitVec.ofBool (x = y))) :: env) s) := by
  rw [evalInstr_icmp (ha := evalOperand_reg_of env s a (.int w x) ha)
    (hb := evalOperand_reg_of env s b (.int w y) hb)]
  simp [withEnv, State.bind, evalICmp]

theorem utf8_step_icmp_ne_imm (env : Env) (s : State) (d src : String) (w : Nat)
    (x c : BitVec w) (h : lookupName env src = some (.int w x)) :
    evalInstr utf8Calls (withEnv env s) (.icmp d .ne w (.reg src) (.imm (.int w c))) =
      some (withEnv ((d, .int 1 (BitVec.ofBool (x ≠ c))) :: env) s) := by
  rw [evalInstr_icmp (ha := evalOperand_reg_of env s src (.int w x) h)
    (hb := evalOperand_lit_of _ w c)]
  simp [withEnv, State.bind, evalICmp]

theorem utf8_step_and1 (env : Env) (s : State) (d a b : String)
    (x y : BitVec 1) (ha : lookupName env a = some (.int 1 x))
    (hb : lookupName env b = some (.int 1 y)) :
    evalInstr utf8Calls (withEnv env s) (.binop d .and 1 (.reg a) (.reg b)) =
      some (withEnv ((d, .int 1 (x &&& y)) :: env) s) := by
  rw [evalInstr_binop (ha := evalOperand_reg_of env s a (.int 1 x) ha)
    (hb := evalOperand_reg_of env s b (.int 1 y) hb) (hr := by rfl)]
  simp only [withEnv, State.bind, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem utf8_step_or1 (env : Env) (s : State) (d a b : String)
    (x y : BitVec 1) (ha : lookupName env a = some (.int 1 x))
    (hb : lookupName env b = some (.int 1 y)) :
    evalInstr utf8Calls (withEnv env s) (.binop d .or 1 (.reg a) (.reg b)) =
      some (withEnv ((d, .int 1 (x ||| y)) :: env) s) := by
  rw [evalInstr_binop (ha := evalOperand_reg_of env s a (.int 1 x) ha)
    (hb := evalOperand_reg_of env s b (.int 1 y) hb) (hr := by rfl)]
  simp only [withEnv, State.bind, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `%d = getelementptr i8, ptr %base, i64 %off`, at a forward index. -/
theorem utf8_step_gep (env : Env) (s : State) (d base off : String) (elem : Ty)
    (a : Nat) (idx : BitVec 64)
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 idx))
    (hpos : idx.toNat < 2 ^ 63) :
    evalInstr utf8Calls (withEnv env s) (.gep d elem (.reg base) (.reg off)) =
      some (withEnv ((d, .ptr (a + idx.toNat * elem.sizeBytes)) :: env) s) := by
  rw [evalInstr_gep (hb := evalOperand_reg_of env s base (.ptr a) hb)
    (ho := evalOperand_reg_of env s off (.int 64 idx) ho)
    (hpos := by simpa using hpos)]
  simp only [withEnv, State.bind, BitVec.signExtend_eq]

/-- `%d = getelementptr i8, ptr %base, i64 <c>`, forward immediate. -/
theorem utf8_step_gep_imm (env : Env) (s : State) (d base : String) (elem : Ty)
    (a : Nat) (c : BitVec 64) (hb : lookupName env base = some (.ptr a))
    (hpos : (c.signExtend 64).toNat < 2 ^ 63) :
    evalInstr utf8Calls (withEnv env s) (.gep d elem (.reg base) (.imm (.int 64 c))) =
      some (withEnv ((d, .ptr (a + c.toNat * elem.sizeBytes)) :: env) s) := by
  rw [evalInstr_gep (hb := evalOperand_reg_of env s base (.ptr a) hb)
    (ho := evalOperand_lit_of _ 64 c) (hpos := by simpa using hpos)]
  simp only [withEnv, State.bind, BitVec.signExtend_eq]


/-! ### The body's own word, and its normalization

The chain below reads one instruction per line, so the value it builds is the
body's *own* expression: the tables' controls are the lane lists the shift and the
mask produce, not the nibble lists a reader names them by.  `errRaw` is that
expression as a definition, and `errRaw_bitcast_eq` is the one place the two
vocabularies are reconciled — `nibLanes_shr4` twice and `conf`'s counterpart.  A
normalization between two `ent_step` lines would be the same rewrite, but paid at
every site instead of once. -/

/-- One half's structural word at the controls the body forms. -/
def scRaw (V1 Vc : Nat) : List (BitVec 8) :=
  List.zipWith (· &&& ·)
    (List.zipWith (· &&& ·)
      (pshufbLanes t2V (nibLanes (unpackLanes 8 32 (packLanes (shr4Lanes V1)))))
      (pshufbLanes t1V (nibLanes (unpackLanes 8 32 V1))))
    (pshufbLanes t3V (nibLanes (unpackLanes 8 32 (packLanes (shr4Lanes Vc)))))

/-- The body's error word for one half, at the accumulator's lanes. -/
def errRaw (p2 p3 : List (BitVec 8)) (V1 Vc : Nat) : List (BitVec 64) :=
  List.zipWith (· ^^^ ·)
    (List.zipWith (· &&& ·) (bitcastVecLanes 64 4 (mustHalf p2 p3)) highLanes64)
    (bitcastVecLanes 64 4 (scRaw V1 Vc))

/-- The raw structural word is the nibble list's, by `nibbleLanes_eq`. -/
theorem scRaw_eq (V1 Vc : Nat) :
    scRaw V1 Vc = scHalf (unpackLanes 8 32 V1) V1 Vc := by
  unfold scRaw scHalf
  rw [nibLanes_shr4 V1, nibLanes_shr4 Vc]

/-- The raw word is the half word's. -/
theorem errRaw_eq (p2 p3 : List (BitVec 8)) (V1 Vc : Nat) :
    errRaw p2 p3 V1 Vc = errHalf (unpackLanes 8 32 V1) p2 p3 V1 Vc := by
  unfold errRaw errHalf
  rw [scRaw_eq]

/-- The half word has four lanes, at the raw expression. -/
theorem errRaw_length (p2 p3 : List (BitVec 8)) (V1 Vc : Nat)
    (h2 : p2.length = 32) (h3 : p3.length = 32) : (errRaw p2 p3 V1 Vc).length = 4 := by
  have hm : (mustHalf p2 p3).length = 32 := mustHalf_length p2 p3 h2 h3
  unfold errRaw
  simp [List.length_zipWith, bitcastVecLanes, unpackLanes_length, highLanes64]

/-! ### The raw word at the accumulator's vocabulary

The chains below read one instruction per line, so the environment carries the
body's own expression: the tables' controls are `nibLanes`' lists of the words
the bitcasts produced, which is `scRaw`'s vocabulary and not `scHalf`'s.  The
reconciliation is `errRaw_eq`'s, and it is paid once, in
`errRawBlk_word_eq`, instead of at every site inside a chain. -/

/-- A byte list's lanes have the list's length. -/
theorem len32_byteLanes (P : List UInt8) (h : P.length = 32) : (byteLanes P).length = 32 := by
  rw [byteLanes_length]; exact h

/-- The three tables' lane lists have thirty-two entries, which is the length
`pshuf.b`'s step asks of a literal table. -/
theorem t1Lanes_length : t1Lanes.length = 32 := by decide

theorem t2Lanes_length : t2Lanes.length = 32 := by decide

theorem t3Lanes_length : t3Lanes.length = 32 := by decide

/-- A `pshuf.b` result at a low-nibble control has thirty-two lanes. -/
theorem len32_pshufb_nib (t : List (BitVec 8)) (V : Nat) :
    (pshufbLanes t (nibLanes (unpackLanes 8 32 V))).length = 32 := by
  rw [pshufbLanes_length, nibLanes_len, unpackLanes_length]

/-- A `pshuf.b` result at a high-nibble control has thirty-two lanes. -/
theorem len32_pshufb_hi (t : List (BitVec 8)) (V : Nat) :
    (pshufbLanes t (nibLanes (unpackLanes 8 32 (packLanes (shr4Lanes V))))).length = 32 := by
  rw [pshufbLanes_length, nibLanes_len, unpackLanes_length]

/-- The block index's shift: `%bi << 6` is the block's byte offset.  The bound is
what keeps the shift from wrapping, and the loop's own `%bi < nb` supplies it. -/
theorem shl64_six (bi : Nat) (h : 64 * bi < 2 ^ 64) :
    BitVec.ofNat 64 bi <<< (BitVec.ofInt 64 6).toNat = BitVec.ofNat 64 (64 * bi) := by
  rw [show (BitVec.ofInt 64 6).toNat = 6 from by decide]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, toNat_ofNat64 bi (by omega), toNat_ofNat64 (64 * bi) h,
    Nat.shiftLeft_eq, show (2 : Nat) ^ 6 = 64 from by decide, Nat.mul_comm bi 64,
    Nat.mod_eq_of_lt h]

/-- **The accumulator step, at the un-folded word.**  The two `errRaw` halves are
the body's own expression — `scRaw`'s controls — and this is the one place they are
read as `errHalf`'s and then as `klErrBlk`'s: `errRaw_eq` twice, the two
`unpackLanes → byteLanes` steps the two `t1` controls need, and `errBlk_word_eq`
carrying the accumulator.  `errBlk_word_eq` is the whole of the tie to the
specification.

The conversion sits at the **body's end**, not after the loop: the ungated body's
own proof applies this lemma, so its conclusion is already the folded word, and
the loop's invariant, its header and the tail carry `klErrBlk`'s vocabulary.
Raw `errRaw` terms survive in exactly two statements — this one and
`utf8Gated_body`'s, which states the word the gated body emits — and the gated
loop's step pays the same conversion once per iteration, at its body's end. -/
theorem errRawBlk_word_eq (s : List UInt8) (acc : List UInt8) (u8k : List (BitVec 64))
    (pre blk : List UInt8) (hs : s = pre ++ blk) (h67 : 67 ≤ s.length)
    (hacc : acc.length = 32) (hu8klen : u8k.length = 4)
    (hpre3 : pre.length = 3) (hblk64 : blk.length = 64)
    (hu8k : packLanes u8k = bytesToNat acc) :
    List.zipWith (· ||| ·)
        (List.zipWith (· ||| ·)
          (errRaw (byteLanes ((s.drop 1).take 32)) (byteLanes (s.take 32))
            (bytesToNat ((s.drop 2).take 32)) (bytesToNat ((s.drop 3).take 32)))
          u8k)
        (errRaw (byteLanes (((s.drop 32).drop 1).take 32))
          (byteLanes ((s.drop 32).take 32))
          (bytesToNat (((s.drop 32).drop 2).take 32))
          (bytesToNat (((s.drop 32).drop 3).take 32)))
      = unpackLanes 64 4 (bytesToNat (List.zipWith (· ||| ·) acc (klErrBlk pre blk))) := by
  subst hs
  have h1 : (((pre ++ blk).drop 2).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop]; omega
  have h2 : ((((pre ++ blk).drop 32).drop 2).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop]; omega
  rw [errRaw_eq, errRaw_eq, byteLanes_eq_unpackLanes (n := 32) h1,
    byteLanes_eq_unpackLanes (n := 32) h2]
  exact errBlk_word_eq (pre ++ blk) acc u8k pre blk rfl h67 hacc hu8klen hpre3 hblk64 hu8k

/-! ### The ungated loop's body

`for.body` is sixty-five instruction lines: the two phis, the block's two
`<4 x i64>` and two `<16 x i16>` loads, the three carry loads, the two `pshuf.b`
triples, the six saturating subtracts and the accumulate.  The statement is in the
specification's vocabulary — the word the loop carries after the block is the
natural of the accumulator list or-ed with `klErrBlk`, the vector `klErrAll` counts
its windows over — and the body's own expression appears nowhere in it.

The stream is `pre ++ blk`: `pre` is the block's three carry bytes and `blk` its
sixty-four, so `pre ++ blk` is the sixty-seven bytes the eight loads read.
`B37 :: B38 :: … :: B56` are the loads' byte lists, tied to the stream's slices by
the `B…` hypotheses; a caller derives them from the window read.

The predecessor is a **parameter**, not `for.body` fixed: the loop enters this
block from `for.body.lr.ph` on its first iteration and from its own latch on every
later one, so this is *the* body step for both edges — the preheader is an
instance (the constant operands `splat (i64 0)` and `i64 0`), not a second
lemma.  Two lemmas would have to be kept in step, and nothing would say which one
a proof meant. -/
theorem utf8Ungated_body (env : Env) (s : State) (b nb bi : Nat) (acc : List UInt8)
    (pre blk : List UInt8) (u8k : List (BitVec 64))
    (B37 B38 B39 B40 B41 B54 B55 B56 : List UInt8)
    (p : String) (opA opB : Operand)
    (hpre : s.pre = some p)
    (hincA : phiIncoming p [("for.body", .reg "%or.i47"),
      ("for.body.lr.ph", .imm (.splat 4 64 (BitVec.ofInt 64 0)))] = some opA)
    (hincB : phiIncoming p [("for.body", .reg "%inc"),
      ("for.body.lr.ph", .imm (.int 64 (BitVec.ofInt 64 0)))] = some opB)
    (hopA : evalOperand (withEnv env s) opA = some (.vec 4 64 u8k))
    (hopB : evalOperand (withEnv (("%u8k.076", .vec 4 64 u8k) :: env) s) opB
      = some (.int 64 (BitVec.ofNat 64 bi)))
    (hb : lookupName env "%b" = some (.ptr b))
    (hdiv : lookupName env "%div44" = some (.int 64 (BitVec.ofNat 64 nb)))
    (hacc : acc.length = 32) (hu8klen : u8k.length = 4)
    (hpre3 : pre.length = 3) (hblk64 : blk.length = 64)
    (hu8kpack : packLanes u8k = bytesToNat acc)
    (hL37 : B37 = ((pre ++ blk).drop 3).take 32)
    (hL38 : B38 = (((pre ++ blk).drop 32).drop 3).take 32)
    (hL39 : B39 = ((pre ++ blk).drop 2).take 32)
    (hL40 : B40 = ((pre ++ blk).drop 1).take 32)
    (hL41 : B41 = (pre ++ blk).take 32)
    (hL54 : B54 = (((pre ++ blk).drop 32).drop 2).take 32)
    (hL55 : B55 = (((pre ++ blk).drop 32).drop 1).take 32)
    (hL56 : B56 = ((pre ++ blk).drop 32).take 32)
    (hread37 : readBytes s.mem (b + 64 * bi) 32 = some B37)
    (hread38 : readBytes s.mem (b + 64 * bi + 32) 32 = some B38)
    (hread39 : readBytes s.mem (b + 64 * bi - 1) 32 = some B39)
    (hread40 : readBytes s.mem (b + 64 * bi - 2) 32 = some B40)
    (hread41 : readBytes s.mem (b + 64 * bi - 3) 32 = some B41)
    (hread54 : readBytes s.mem (b + 64 * bi + 31) 32 = some B54)
    (hread55 : readBytes s.mem (b + 64 * bi + 30) 32 = some B55)
    (hread56 : readBytes s.mem (b + 64 * bi + 29) 32 = some B56)
    (hb3 : 3 ≤ b) (hbi64 : 64 * bi < 2 ^ 63) :
    ∃ env', denoteCode utf8Calls utf8ForBody.instrs (withEnv env s) = some (withEnv env' s) ∧
      lookupName env' "%or.i47" = some (.vec 4 64
        (unpackLanes 64 4 (bytesToNat (List.zipWith (· ||| ·) acc (klErrBlk pre blk))))) ∧
      lookupName env' "%inc" = some (.int 64 (BitVec.ofNat 64 bi + BitVec.ofInt 64 1)) ∧
      lookupName env' "%exitcond.not" = some (.int 1 (BitVec.ofBool
        (BitVec.ofNat 64 bi + BitVec.ofInt 64 1 = BitVec.ofNat 64 nb))) := by
  have h37 : B37.length = 32 := readBytes_length s.mem (b + 64 * bi) 32 hread37
  have h38 : B38.length = 32 := readBytes_length s.mem (b + 64 * bi + 32) 32 hread38
  have h39 : B39.length = 32 := readBytes_length s.mem (b + 64 * bi - 1) 32 hread39
  have h40 : B40.length = 32 := readBytes_length s.mem (b + 64 * bi - 2) 32 hread40
  have h41 : B41.length = 32 := readBytes_length s.mem (b + 64 * bi - 3) 32 hread41
  have h54 : B54.length = 32 := readBytes_length s.mem (b + 64 * bi + 31) 32 hread54
  have h55 : B55.length = 32 := readBytes_length s.mem (b + 64 * bi + 30) 32 hread55
  have h56 : B56.length = 32 := readBytes_length s.mem (b + 64 * bi + 29) 32 hread56
  have hV37 : B37 = natToBytes (bytesToNat B37) 32 :=
    (natToBytes_bytesToNat B37).symm.trans (by rw [h37])
  have hV38 : B38 = natToBytes (bytesToNat B38) 32 :=
    (natToBytes_bytesToNat B38).symm.trans (by rw [h38])
  have hV39 : B39 = natToBytes (bytesToNat B39) 32 :=
    (natToBytes_bytesToNat B39).symm.trans (by rw [h39])
  have hV54 : B54 = natToBytes (bytesToNat B54) 32 :=
    (natToBytes_bytesToNat B54).symm.trans (by rw [h54])
  have hlt37 : bytesToNat B37 < 2 ^ 256 := by
    have := bytesToNat_lt B37
    rwa [h37, show (256 : Nat) ^ 32 = 2 ^ 256 from by decide] at this
  have hlt38 : bytesToNat B38 < 2 ^ 256 := by
    have := bytesToNat_lt B38
    rwa [h38, show (256 : Nat) ^ 32 = 2 ^ 256 from by decide] at this
  have hlt39 : bytesToNat B39 < 2 ^ 256 := by
    have := bytesToNat_lt B39
    rwa [h39, show (256 : Nat) ^ 32 = 2 ^ 256 from by decide] at this
  have hlt54 : bytesToNat B54 < 2 ^ 256 := by
    have := bytesToNat_lt B54
    rwa [h54, show (256 : Nat) ^ 32 = 2 ^ 256 from by decide] at this
  refine ⟨?env', ?hrun, ?hval, ?hinc', ?hexit⟩
  case hrun =>
    simp only [utf8ForBody, reg, lit, splatOf, lanesOf, highBitMask, JsonUtf8IR.pshufb,
      JsonUtf8IR.usubSat]
    ent_step (utf8_phi env s "%u8k.076" v4i64 _ p opA (.vec 4 64 u8k) hpre hincA hopA)
    ent_step (utf8_phi (("%u8k.076", .vec 4 64 u8k) :: env) s "%bi.075" (.int 64) _ p opB
      (.int 64 (BitVec.ofNat 64 bi)) hpre hincB hopB)
    ent_step (utf8_step_shl _ _ "%shl" "%bi.075" 64 (BitVec.ofNat 64 bi) (BitVec.ofInt 64 6)
      (by ent_auto))
    rw [shl64_six bi (by omega)]
    ent_step (utf8_step_gep _ _ "%add.ptr" "%b" "%shl" (.int 8) b (BitVec.ofNat 64 (64 * bi))
      (by ent_auto) (by ent_auto) (by rw [toNat_ofNat64 (64 * bi) (by omega)]; exact hbi64))
    rw [show b + (BitVec.ofNat 64 (64 * bi)).toNat * (Ty.int 8).sizeBytes = b + 64 * bi from by
      rw [toNat_ofNat64 (64 * bi) (by omega), sizeBytes_i8, Nat.mul_one]]
    ent_step (step_load16_16 _ _ "%37" "%add.ptr" (b + 64 * bi) (bytesToNat B37) (by ent_auto)
      (by rw [← hV37]; exact hread37) hlt37)
    ent_step (utf8_step_gep_imm _ _ "%add.ptr3" "%add.ptr" (.int 8) (b + 64 * bi)
      (BitVec.ofInt 64 32) (by ent_auto) (by decide))
    rw [show b + 64 * bi + (BitVec.ofInt 64 32).toNat * (Ty.int 8).sizeBytes = b + 64 * bi + 32
      from by rw [show (BitVec.ofInt 64 32).toNat = 32 from by decide, sizeBytes_i8]]
    ent_step (step_load16_16 _ _ "%38" "%add.ptr3" (b + 64 * bi + 32) (bytesToNat B38)
      (by ent_auto) (by rw [← hV38]; exact hread38) hlt38)
    ent_step (step_gep64_m1 _ _ "%add.ptr.i.i" "%add.ptr" (b + 64 * bi) (by ent_auto) (by omega))
    ent_step (step_load4_64 _ _ "%39" "%add.ptr.i.i" (b + 64 * bi - 1) (bytesToNat B39)
      (by ent_auto) (by rw [← hV39]; exact hread39) hlt39)
    ent_step (step_gep64_m2 _ _ "%add.ptr3.i.i" "%add.ptr" (b + 64 * bi) (by ent_auto) (by omega))
    ent_step (step_load32_8 _ _ "%40" "%add.ptr3.i.i" (b + 64 * bi - 2) B40 (by ent_auto) hread40)
    ent_step (step_gep64_m3 _ _ "%add.ptr5.i.i" "%add.ptr" (b + 64 * bi) (by ent_auto) (by omega))
    ent_step (step_load32_8 _ _ "%41" "%add.ptr5.i.i" (b + 64 * bi - 3) B41 (by ent_auto) hread41)
    ent_step (utf8_step_bc64_8 _ _ "%42" "%39" (bytesToNat B39) hlt39 (by ent_auto))
    ent_step (utf8_step_and15 _ _ "%43" "%42" _ (by ent_auto) (by rw [unpackLanes_length]))
    ent_step (utf8_step_pshufb _ _ "%44" "%43" t1Lanes t1V _ t1Lanes_length rfl (by ent_auto))
    ent_step (utf8_step_bc64_16 _ _ "%45" "%39" (bytesToNat B39) hlt39 (by ent_auto))
    ent_step (utf8_step_shr16 _ _ "%46" "%45" (bytesToNat B39) (by ent_auto))
    ent_step (utf8_step_bc16_8 _ _ "%47" "%46" (bytesToNat B39) (by ent_auto))
    ent_step (utf8_step_and15 _ _ "%48" "%47" _ (by ent_auto) (by rw [unpackLanes_length]))
    ent_step (utf8_step_pshufb _ _ "%49" "%48" t2Lanes t2V _ t2Lanes_length rfl (by ent_auto))
    ent_step (utf8_step_vec_and _ _ "%and.i3741.i.i" "%49" "%44" 32 8 _ _ (by ent_auto)
      (by ent_auto) (len32_pshufb_hi t2V (bytesToNat B39)) (len32_pshufb_nib t1V (bytesToNat B39)))
    ent_step (utf8_step_shr16 _ _ "%50" "%37" (bytesToNat B37) (by ent_auto))
    ent_step (utf8_step_bc16_8 _ _ "%51" "%50" (bytesToNat B37) (by ent_auto))
    ent_step (utf8_step_and15 _ _ "%52" "%51" _ (by ent_auto) (by rw [unpackLanes_length]))
    ent_step (utf8_step_pshufb _ _ "%53" "%52" t3Lanes t3V _ t3Lanes_length rfl (by ent_auto))
    ent_step (utf8_step_vec_and _ _ "%and.i3542.i.i" "%and.i3741.i.i" "%53" 32 8 _ _ (by ent_auto)
      (by ent_auto) (len32_zip (· &&& ·) _ _ (len32_pshufb_hi t2V (bytesToNat B39))
        (len32_pshufb_nib t1V (bytesToNat B39)))
      (len32_pshufb_hi t3V (bytesToNat B37)))
    ent_step (utf8_step_bc8_64 _ _ "%and.i35.i.i" "%and.i3542.i.i" _
      (by ent_auto) (len32_zip (· &&& ·) _ _ (len32_zip (· &&& ·) _ _
        (len32_pshufb_hi t2V (bytesToNat B39)) (len32_pshufb_nib t1V (bytesToNat B39)))
        (len32_pshufb_hi t3V (bytesToNat B37))))
    ent_step (utf8_step_usubSat _ _ "%elt.sat.i40.i.i" "%40" 96 (byteLanes B40)
      (by rw [byteLanes_length]; exact h40) (by ent_auto))
    ent_step (utf8_step_usubSat _ _ "%elt.sat.i.i.i" "%41" 112 (byteLanes B41)
      (by rw [byteLanes_length]; exact h41) (by ent_auto))
    ent_step (utf8_step_vec_or _ _ "%or.i43.i.i" "%elt.sat.i.i.i" "%elt.sat.i40.i.i" 32 8 _ _
      (by ent_auto) (by ent_auto) (len32_zip subsSat _ _ (len32_byteLanes B41 h41) (by simp))
      (len32_zip subsSat _ _ (len32_byteLanes B40 h40) (by simp)))
    ent_step (utf8_step_bc8_64 _ _ "%or.i.i.i" "%or.i43.i.i" _
      (by ent_auto) (len32_zip (· ||| ·) _ _ (len32_zip subsSat _ _ (len32_byteLanes B41 h41) (by simp))
        (len32_zip subsSat _ _ (len32_byteLanes B40 h40) (by simp))))
    ent_step (utf8_step_andHigh _ _ "%and.i.i.i" "%or.i.i.i" _
      (by ent_auto) (by rw [unpackLanes_length]))
    ent_step (utf8_step_vec_xor _ _ "%xor.i.i.i" "%and.i.i.i" "%and.i35.i.i" 4 64 _ _ (by ent_auto)
      (by ent_auto) (len4_zip64 (· &&& ·) _ _ (by rw [unpackLanes_length]) (by simp [highLanes64]))
      (by rw [unpackLanes_length]))
    ent_step (utf8_step_gep_imm _ _ "%add.ptr.i4.i" "%add.ptr" (.int 8) (b + 64 * bi)
      (BitVec.ofInt 64 31) (by ent_auto) (by decide))
    rw [show b + 64 * bi + (BitVec.ofInt 64 31).toNat * (Ty.int 8).sizeBytes = b + 64 * bi + 31
      from by rw [show (BitVec.ofInt 64 31).toNat = 31 from by decide, sizeBytes_i8]]
    ent_step (step_load4_64 _ _ "%54" "%add.ptr.i4.i" (b + 64 * bi + 31) (bytesToNat B54)
      (by ent_auto) (by rw [← hV54]; exact hread54) hlt54)
    ent_step (utf8_step_gep_imm _ _ "%add.ptr3.i5.i" "%add.ptr" (.int 8) (b + 64 * bi)
      (BitVec.ofInt 64 30) (by ent_auto) (by decide))
    rw [show b + 64 * bi + (BitVec.ofInt 64 30).toNat * (Ty.int 8).sizeBytes = b + 64 * bi + 30
      from by rw [show (BitVec.ofInt 64 30).toNat = 30 from by decide, sizeBytes_i8]]
    ent_step (step_load32_8 _ _ "%55" "%add.ptr3.i5.i" (b + 64 * bi + 30) B55 (by ent_auto) hread55)
    ent_step (utf8_step_gep_imm _ _ "%add.ptr5.i6.i" "%add.ptr" (.int 8) (b + 64 * bi)
      (BitVec.ofInt 64 29) (by ent_auto) (by decide))
    rw [show b + 64 * bi + (BitVec.ofInt 64 29).toNat * (Ty.int 8).sizeBytes = b + 64 * bi + 29
      from by rw [show (BitVec.ofInt 64 29).toNat = 29 from by decide, sizeBytes_i8]]
    ent_step (step_load32_8 _ _ "%56" "%add.ptr5.i6.i" (b + 64 * bi + 29) B56 (by ent_auto) hread56)
    ent_step (utf8_step_bc64_8 _ _ "%57" "%54" (bytesToNat B54) hlt54 (by ent_auto))
    ent_step (utf8_step_and15 _ _ "%58" "%57" _ (by ent_auto) (by rw [unpackLanes_length]))
    ent_step (utf8_step_pshufb _ _ "%59" "%58" t1Lanes t1V _ t1Lanes_length rfl (by ent_auto))
    ent_step (utf8_step_bc64_16 _ _ "%60" "%54" (bytesToNat B54) hlt54 (by ent_auto))
    ent_step (utf8_step_shr16 _ _ "%61" "%60" (bytesToNat B54) (by ent_auto))
    ent_step (utf8_step_bc16_8 _ _ "%62" "%61" (bytesToNat B54) (by ent_auto))
    ent_step (utf8_step_and15 _ _ "%63" "%62" _ (by ent_auto) (by rw [unpackLanes_length]))
    ent_step (utf8_step_pshufb _ _ "%64" "%63" t2Lanes t2V _ t2Lanes_length rfl (by ent_auto))
    ent_step (utf8_step_vec_and _ _ "%and.i3741.i7.i" "%64" "%59" 32 8 _ _ (by ent_auto)
      (by ent_auto) (len32_pshufb_hi t2V (bytesToNat B54)) (len32_pshufb_nib t1V (bytesToNat B54)))
    ent_step (utf8_step_shr16 _ _ "%65" "%38" (bytesToNat B38) (by ent_auto))
    ent_step (utf8_step_bc16_8 _ _ "%66" "%65" (bytesToNat B38) (by ent_auto))
    ent_step (utf8_step_and15 _ _ "%67" "%66" _ (by ent_auto) (by rw [unpackLanes_length]))
    ent_step (utf8_step_pshufb _ _ "%68" "%67" t3Lanes t3V _ t3Lanes_length rfl (by ent_auto))
    ent_step (utf8_step_vec_and _ _ "%and.i3542.i8.i" "%and.i3741.i7.i" "%68" 32 8 _ _ (by ent_auto)
      (by ent_auto) (len32_zip (· &&& ·) _ _ (len32_pshufb_hi t2V (bytesToNat B54))
        (len32_pshufb_nib t1V (bytesToNat B54)))
      (len32_pshufb_hi t3V (bytesToNat B38)))
    ent_step (utf8_step_bc8_64 _ _ "%and.i35.i9.i" "%and.i3542.i8.i" _
      (by ent_auto) (len32_zip (· &&& ·) _ _ (len32_zip (· &&& ·) _ _
        (len32_pshufb_hi t2V (bytesToNat B54)) (len32_pshufb_nib t1V (bytesToNat B54)))
        (len32_pshufb_hi t3V (bytesToNat B38))))
    ent_step (utf8_step_usubSat _ _ "%elt.sat.i40.i10.i" "%55" 96 (byteLanes B55)
      (by rw [byteLanes_length]; exact h55) (by ent_auto))
    ent_step (utf8_step_usubSat _ _ "%elt.sat.i.i11.i" "%56" 112 (byteLanes B56)
      (by rw [byteLanes_length]; exact h56) (by ent_auto))
    ent_step (utf8_step_vec_or _ _ "%or.i43.i12.i" "%elt.sat.i.i11.i" "%elt.sat.i40.i10.i" 32 8 _ _
      (by ent_auto) (by ent_auto) (len32_zip subsSat _ _ (len32_byteLanes B56 h56) (by simp))
      (len32_zip subsSat _ _ (len32_byteLanes B55 h55) (by simp)))
    ent_step (utf8_step_bc8_64 _ _ "%or.i.i13.i" "%or.i43.i12.i" _
      (by ent_auto) (len32_zip (· ||| ·) _ _ (len32_zip subsSat _ _ (len32_byteLanes B56 h56) (by simp))
        (len32_zip subsSat _ _ (len32_byteLanes B55 h55) (by simp))))
    ent_step (utf8_step_andHigh _ _ "%and.i.i14.i" "%or.i.i13.i" _
      (by ent_auto) (by rw [unpackLanes_length]))
    ent_step (utf8_step_vec_xor _ _ "%xor.i.i15.i" "%and.i.i14.i" "%and.i35.i9.i" 4 64 _ _
      (by ent_auto) (by ent_auto) (len4_zip64 (· &&& ·) _ _ (by rw [unpackLanes_length])
        (by simp [highLanes64])) (by rw [unpackLanes_length]))
    ent_step (utf8_step_vec_or _ _ "%or.i.i" "%xor.i.i.i" "%u8k.076" 4 64 _ _ (by ent_auto)
      (by ent_auto) (by simp [List.length_zipWith, unpackLanes_length, highLanes64])
      hu8klen)
    ent_step (utf8_step_vec_or _ _ "%or.i47" "%or.i.i" "%xor.i.i15.i" 4 64 _ _ (by ent_auto)
      (by ent_auto) (by simp [List.length_zipWith, unpackLanes_length, highLanes64, hu8klen])
      (by simp [List.length_zipWith, unpackLanes_length, highLanes64]))
    ent_step (utf8_step_add _ _ "%inc" "%bi.075" 64 (BitVec.ofNat 64 bi) (BitVec.ofInt 64 1)
      (by ent_auto))
    ent_step (utf8_step_icmp_eq _ _ "%exitcond.not" "%inc" "%div44" 64 _ _
      (by ent_auto) (by ent_auto))
    rfl
  case hval =>
    ent_auto
    rw [lookupName_cons_self, Option.some.injEq]
    congr 1
    rw [hL37, hL38, hL39, hL40, hL41, hL54, hL55, hL56]
    exact errRawBlk_word_eq (pre ++ blk) acc u8k pre blk rfl
      (by rw [List.length_append]; omega) hacc hu8klen hpre3 hblk64 hu8kpack
  case hinc' => ent_auto
  case hexit => ent_auto

/-- `%d = icmp eq i32 %src, <c>`. -/
theorem utf8_step_icmp_eq_imm (env : Env) (s : State) (d src : String) (w : Nat)
    (x c : BitVec w) (h : lookupName env src = some (.int w x)) :
    evalInstr utf8Calls (withEnv env s) (.icmp d .eq w (.reg src) (.imm (.int w c))) =
      some (withEnv ((d, .int 1 (BitVec.ofBool (x = c))) :: env) s) := by
  rw [evalInstr_icmp (ha := evalOperand_reg_of env s src (.int w x) h)
    (hb := evalOperand_lit_of _ w c)]
  simp [withEnv, State.bind, evalICmp]

/-- `%d = and i32 %src, <c>`. -/
theorem utf8_step_and_imm (env : Env) (s : State) (d src : String) (w : Nat)
    (x c : BitVec w) (h : lookupName env src = some (.int w x)) :
    evalInstr utf8Calls (withEnv env s) (.binop d .and w (.reg src) (.imm (.int w c))) =
      some (withEnv ((d, .int w (x &&& c)) :: env) s) := by
  rw [evalInstr_binop (ha := evalOperand_reg_of env s src (.int w x) h)
    (hb := evalOperand_lit_of _ w c) (hr := by rfl)]
  simp only [withEnv, State.bind, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `%d = zext i1 %src to i64`, the returned verdict's width change. -/
theorem utf8_step_zext (env : Env) (s : State) (d src : String) (wIn wOut : Nat)
    (x : BitVec wIn) (h : lookupName env src = some (.int wIn x)) :
    evalInstr utf8Calls (withEnv env s) (.zext d wIn wOut (.reg src)) =
      some (withEnv ((d, .int wOut (BitVec.ofNat wOut x.toNat)) :: env) s) := by
  rw [evalInstr_zext (hv := evalOperand_reg_of env s src (.int wIn x) h)]
  simp [withEnv, State.bind]

/-! ### The gated loop's body

`if.then11.us` is the same DFA over the same two halves — fifty-eight
instruction lines instead of the ungated body's sixty-five, because the two
`<4 x i64>` halves `%0` and `%1` arrive already loaded from `for.body.us` and the
two phis are the header's.  The result is stated in `errRaw`'s vocabulary, in the
association the emission builds: `(%lower ||| %upper) ||| u8k`, where the ungated
body writes `(%lower ||| u8k) ||| %upper`.  The difference needs no lane-level
lemma, and asking for one would be the signal that the comparison had been raised
above the verdict: the two gate settings are compared as **verdicts** (C62 (ii)),
and a zero test does not see the order of the lanes' `|||`.  Each body therefore
stays in the order it emits, and the fold to `klErrBlk`'s word is paid where a
loop step consumes the body, once per iteration. -/
theorem utf8Gated_body (env : Env) (s : State) (b bi : Nat) (u8k : List (BitVec 64))
    (B3 B4 B5 B19 B20 B21 : List UInt8) (V0 V1 : Nat)
    (hu8k : lookupName env "%u8k.076.us" = some (.vec 4 64 u8k))
    (hptr : lookupName env "%add.ptr.us" = some (.ptr (b + 64 * bi)))
    (h0 : lookupName env "%0" = some (.vec 4 64 (unpackLanes 64 4 V0)))
    (h1 : lookupName env "%1" = some (.vec 4 64 (unpackLanes 64 4 V1)))
    (hu8klen : u8k.length = 4)
    (hV0 : V0 < 2 ^ 256) (hV1 : V1 < 2 ^ 256)
    (hread3 : readBytes s.mem (b + 64 * bi - 1) 32 = some B3)
    (hread4 : readBytes s.mem (b + 64 * bi - 2) 32 = some B4)
    (hread5 : readBytes s.mem (b + 64 * bi - 3) 32 = some B5)
    (hread19 : readBytes s.mem (b + 64 * bi + 31) 32 = some B19)
    (hread20 : readBytes s.mem (b + 64 * bi + 30) 32 = some B20)
    (hread21 : readBytes s.mem (b + 64 * bi + 29) 32 = some B21)
    (hb3 : 3 ≤ b) (hbi64 : 64 * bi < 2 ^ 63) :
    ∃ env', denoteCode utf8Calls utf8ThenUs.instrs (withEnv env s) = some (withEnv env' s) ∧
      lookupName env' "%or.i.us" = some (.vec 4 64
        (List.zipWith (· ||| ·)
          (List.zipWith (· ||| ·)
            (errRaw (byteLanes B4) (byteLanes B5) (bytesToNat B3) V0)
            (errRaw (byteLanes B20) (byteLanes B21) (bytesToNat B19) V1))
          u8k)) := by
  have h3 : B3.length = 32 := readBytes_length s.mem (b + 64 * bi - 1) 32 hread3
  have h4 : B4.length = 32 := readBytes_length s.mem (b + 64 * bi - 2) 32 hread4
  have h5 : B5.length = 32 := readBytes_length s.mem (b + 64 * bi - 3) 32 hread5
  have h19 : B19.length = 32 := readBytes_length s.mem (b + 64 * bi + 31) 32 hread19
  have h20 : B20.length = 32 := readBytes_length s.mem (b + 64 * bi + 30) 32 hread20
  have h21 : B21.length = 32 := readBytes_length s.mem (b + 64 * bi + 29) 32 hread21
  have hV3 : B3 = natToBytes (bytesToNat B3) 32 :=
    (natToBytes_bytesToNat B3).symm.trans (by rw [h3])
  have hV19 : B19 = natToBytes (bytesToNat B19) 32 :=
    (natToBytes_bytesToNat B19).symm.trans (by rw [h19])
  have hlt3 : bytesToNat B3 < 2 ^ 256 := by
    have := bytesToNat_lt B3
    rwa [h3, show (256 : Nat) ^ 32 = 2 ^ 256 from by decide] at this
  have hlt19 : bytesToNat B19 < 2 ^ 256 := by
    have := bytesToNat_lt B19
    rwa [h19, show (256 : Nat) ^ 32 = 2 ^ 256 from by decide] at this
  refine ⟨?env', ?hrun, ?hval⟩
  case hrun =>
    simp only [utf8ThenUs, reg, lit, splatOf, lanesOf, highBitMask, JsonUtf8IR.pshufb,
      JsonUtf8IR.usubSat]
    ent_step (step_gep64_m1 _ _ "%add.ptr.i.i48.us" "%add.ptr.us" (b + 64 * bi)
      (by ent_auto) (by omega))
    ent_step (step_load4_64 _ _ "%3" "%add.ptr.i.i48.us" (b + 64 * bi - 1) (bytesToNat B3)
      (by ent_auto) (by rw [← hV3]; exact hread3) hlt3)
    ent_step (step_gep64_m2 _ _ "%add.ptr3.i.i49.us" "%add.ptr.us" (b + 64 * bi)
      (by ent_auto) (by omega))
    ent_step (step_load32_8 _ _ "%4" "%add.ptr3.i.i49.us" (b + 64 * bi - 2) B4 (by ent_auto)
      hread4)
    ent_step (step_gep64_m3 _ _ "%add.ptr5.i.i50.us" "%add.ptr.us" (b + 64 * bi)
      (by ent_auto) (by omega))
    ent_step (step_load32_8 _ _ "%5" "%add.ptr5.i.i50.us" (b + 64 * bi - 3) B5 (by ent_auto)
      hread5)
    ent_step (utf8_step_bc64_8 _ _ "%6" "%3" (bytesToNat B3) hlt3 (by ent_auto))
    ent_step (utf8_step_and15 _ _ "%7" "%6" _ (by ent_auto) (by rw [unpackLanes_length]))
    ent_step (utf8_step_pshufb _ _ "%8" "%7" t1Lanes t1V _ t1Lanes_length rfl (by ent_auto))
    ent_step (utf8_step_bc64_16 _ _ "%9" "%3" (bytesToNat B3) hlt3 (by ent_auto))
    ent_step (utf8_step_shr16 _ _ "%10" "%9" (bytesToNat B3) (by ent_auto))
    ent_step (utf8_step_bc16_8 _ _ "%11" "%10" (bytesToNat B3) (by ent_auto))
    ent_step (utf8_step_and15 _ _ "%12" "%11" _ (by ent_auto) (by rw [unpackLanes_length]))
    ent_step (utf8_step_pshufb _ _ "%13" "%12" t2Lanes t2V _ t2Lanes_length rfl (by ent_auto))
    ent_step (utf8_step_vec_and _ _ "%and.i3741.i.i51.us" "%13" "%8" 32 8 _ _ (by ent_auto)
      (by ent_auto) (len32_pshufb_hi t2V (bytesToNat B3)) (len32_pshufb_nib t1V (bytesToNat B3)))
    ent_step (utf8_step_bc64_16 _ _ "%14" "%0" V0 hV0 (by ent_auto))
    ent_step (utf8_step_shr16 _ _ "%15" "%14" V0 (by ent_auto))
    ent_step (utf8_step_bc16_8 _ _ "%16" "%15" V0 (by ent_auto))
    ent_step (utf8_step_and15 _ _ "%17" "%16" _ (by ent_auto) (by rw [unpackLanes_length]))
    ent_step (utf8_step_pshufb _ _ "%18" "%17" t3Lanes t3V _ t3Lanes_length rfl (by ent_auto))
    ent_step (utf8_step_vec_and _ _ "%and.i3542.i.i52.us" "%and.i3741.i.i51.us" "%18" 32 8 _ _
      (by ent_auto) (by ent_auto)
      (len32_zip (· &&& ·) _ _ (len32_pshufb_hi t2V (bytesToNat B3))
        (len32_pshufb_nib t1V (bytesToNat B3)))
      (len32_pshufb_hi t3V V0))
    ent_step (utf8_step_bc8_64 _ _ "%and.i35.i.i53.us" "%and.i3542.i.i52.us" _
      (by ent_auto) (len32_zip (· &&& ·) _ _ (len32_zip (· &&& ·) _ _
        (len32_pshufb_hi t2V (bytesToNat B3)) (len32_pshufb_nib t1V (bytesToNat B3)))
        (len32_pshufb_hi t3V V0)))
    ent_step (utf8_step_usubSat _ _ "%elt.sat.i40.i.i54.us" "%4" 96 (byteLanes B4)
      (by rw [byteLanes_length]; exact h4) (by ent_auto))
    ent_step (utf8_step_usubSat _ _ "%elt.sat.i.i.i55.us" "%5" 112 (byteLanes B5)
      (by rw [byteLanes_length]; exact h5) (by ent_auto))
    ent_step (utf8_step_vec_or _ _ "%or.i43.i.i56.us" "%elt.sat.i.i.i55.us"
      "%elt.sat.i40.i.i54.us" 32 8 _ _ (by ent_auto) (by ent_auto)
      (len32_zip subsSat _ _ (len32_byteLanes B5 h5) (by simp))
      (len32_zip subsSat _ _ (len32_byteLanes B4 h4) (by simp)))
    ent_step (utf8_step_bc8_64 _ _ "%or.i.i.i57.us" "%or.i43.i.i56.us" _
      (by ent_auto) (len32_zip (· ||| ·) _ _ (len32_zip subsSat _ _ (len32_byteLanes B5 h5)
        (by simp)) (len32_zip subsSat _ _ (len32_byteLanes B4 h4) (by simp))))
    ent_step (utf8_step_andHigh _ _ "%and.i.i.i58.us" "%or.i.i.i57.us" _
      (by ent_auto) (by rw [unpackLanes_length]))
    ent_step (utf8_step_vec_xor _ _ "%xor.i.i.i59.us" "%and.i.i.i58.us" "%and.i35.i.i53.us"
      4 64 _ _ (by ent_auto) (by ent_auto)
      (len4_zip64 (· &&& ·) _ _ (by rw [unpackLanes_length]) (by simp [highLanes64]))
      (by rw [unpackLanes_length]))
    ent_step (utf8_step_gep_imm _ _ "%add.ptr.i4.i60.us" "%add.ptr.us" (.int 8)
      (b + 64 * bi) (BitVec.ofInt 64 31) (by ent_auto) (by decide))
    rw [show b + 64 * bi + (BitVec.ofInt 64 31).toNat * (Ty.int 8).sizeBytes = b + 64 * bi + 31
      from by rw [show (BitVec.ofInt 64 31).toNat = 31 from by decide, sizeBytes_i8]]
    ent_step (step_load4_64 _ _ "%19" "%add.ptr.i4.i60.us" (b + 64 * bi + 31) (bytesToNat B19)
      (by ent_auto) (by rw [← hV19]; exact hread19) hlt19)
    ent_step (utf8_step_gep_imm _ _ "%add.ptr3.i5.i61.us" "%add.ptr.us" (.int 8)
      (b + 64 * bi) (BitVec.ofInt 64 30) (by ent_auto) (by decide))
    rw [show b + 64 * bi + (BitVec.ofInt 64 30).toNat * (Ty.int 8).sizeBytes = b + 64 * bi + 30
      from by rw [show (BitVec.ofInt 64 30).toNat = 30 from by decide, sizeBytes_i8]]
    ent_step (step_load32_8 _ _ "%20" "%add.ptr3.i5.i61.us" (b + 64 * bi + 30) B20
      (by ent_auto) hread20)
    ent_step (utf8_step_gep_imm _ _ "%add.ptr5.i6.i62.us" "%add.ptr.us" (.int 8)
      (b + 64 * bi) (BitVec.ofInt 64 29) (by ent_auto) (by decide))
    rw [show b + 64 * bi + (BitVec.ofInt 64 29).toNat * (Ty.int 8).sizeBytes = b + 64 * bi + 29
      from by rw [show (BitVec.ofInt 64 29).toNat = 29 from by decide, sizeBytes_i8]]
    ent_step (step_load32_8 _ _ "%21" "%add.ptr5.i6.i62.us" (b + 64 * bi + 29) B21
      (by ent_auto) hread21)
    ent_step (utf8_step_bc64_8 _ _ "%22" "%19" (bytesToNat B19) hlt19 (by ent_auto))
    ent_step (utf8_step_and15 _ _ "%23" "%22" _ (by ent_auto) (by rw [unpackLanes_length]))
    ent_step (utf8_step_pshufb _ _ "%24" "%23" t1Lanes t1V _ t1Lanes_length rfl (by ent_auto))
    ent_step (utf8_step_bc64_16 _ _ "%25" "%19" (bytesToNat B19) hlt19 (by ent_auto))
    ent_step (utf8_step_shr16 _ _ "%26" "%25" (bytesToNat B19) (by ent_auto))
    ent_step (utf8_step_bc16_8 _ _ "%27" "%26" (bytesToNat B19) (by ent_auto))
    ent_step (utf8_step_and15 _ _ "%28" "%27" _ (by ent_auto) (by rw [unpackLanes_length]))
    ent_step (utf8_step_pshufb _ _ "%29" "%28" t2Lanes t2V _ t2Lanes_length rfl (by ent_auto))
    ent_step (utf8_step_vec_and _ _ "%and.i3741.i7.i63.us" "%29" "%24" 32 8 _ _ (by ent_auto)
      (by ent_auto) (len32_pshufb_hi t2V (bytesToNat B19))
      (len32_pshufb_nib t1V (bytesToNat B19)))
    ent_step (utf8_step_bc64_16 _ _ "%30" "%1" V1 hV1 (by ent_auto))
    ent_step (utf8_step_shr16 _ _ "%31" "%30" V1 (by ent_auto))
    ent_step (utf8_step_bc16_8 _ _ "%32" "%31" V1 (by ent_auto))
    ent_step (utf8_step_and15 _ _ "%33" "%32" _ (by ent_auto) (by rw [unpackLanes_length]))
    ent_step (utf8_step_pshufb _ _ "%34" "%33" t3Lanes t3V _ t3Lanes_length rfl (by ent_auto))
    ent_step (utf8_step_vec_and _ _ "%and.i3542.i8.i64.us" "%and.i3741.i7.i63.us" "%34" 32 8 _ _
      (by ent_auto) (by ent_auto)
      (len32_zip (· &&& ·) _ _ (len32_pshufb_hi t2V (bytesToNat B19))
        (len32_pshufb_nib t1V (bytesToNat B19)))
      (len32_pshufb_hi t3V V1))
    ent_step (utf8_step_bc8_64 _ _ "%and.i35.i9.i65.us" "%and.i3542.i8.i64.us" _
      (by ent_auto) (len32_zip (· &&& ·) _ _ (len32_zip (· &&& ·) _ _
        (len32_pshufb_hi t2V (bytesToNat B19)) (len32_pshufb_nib t1V (bytesToNat B19)))
        (len32_pshufb_hi t3V V1)))
    ent_step (utf8_step_usubSat _ _ "%elt.sat.i40.i10.i66.us" "%20" 96 (byteLanes B20)
      (by rw [byteLanes_length]; exact h20) (by ent_auto))
    ent_step (utf8_step_usubSat _ _ "%elt.sat.i.i11.i67.us" "%21" 112 (byteLanes B21)
      (by rw [byteLanes_length]; exact h21) (by ent_auto))
    ent_step (utf8_step_vec_or _ _ "%or.i43.i12.i68.us" "%elt.sat.i.i11.i67.us"
      "%elt.sat.i40.i10.i66.us" 32 8 _ _ (by ent_auto) (by ent_auto)
      (len32_zip subsSat _ _ (len32_byteLanes B21 h21) (by simp))
      (len32_zip subsSat _ _ (len32_byteLanes B20 h20) (by simp)))
    ent_step (utf8_step_bc8_64 _ _ "%or.i.i13.i69.us" "%or.i43.i12.i68.us" _
      (by ent_auto) (len32_zip (· ||| ·) _ _ (len32_zip subsSat _ _ (len32_byteLanes B21 h21)
        (by simp)) (len32_zip subsSat _ _ (len32_byteLanes B20 h20) (by simp))))
    ent_step (utf8_step_andHigh _ _ "%and.i.i14.i70.us" "%or.i.i13.i69.us" _
      (by ent_auto) (by rw [unpackLanes_length]))
    ent_step (utf8_step_vec_xor _ _ "%xor.i.i15.i71.us" "%and.i.i14.i70.us" "%and.i35.i9.i65.us"
      4 64 _ _ (by ent_auto) (by ent_auto)
      (len4_zip64 (· &&& ·) _ _ (by rw [unpackLanes_length]) (by simp [highLanes64]))
      (by rw [unpackLanes_length]))
    ent_step (utf8_step_vec_or _ _ "%35" "%xor.i.i.i59.us" "%xor.i.i15.i71.us" 4 64 _ _
      (by ent_auto) (by ent_auto)
      (by simp [List.length_zipWith, unpackLanes_length, highLanes64])
      (by simp [List.length_zipWith, unpackLanes_length, highLanes64]))
    ent_step (utf8_step_vec_or _ _ "%or.i.us" "%35" "%u8k.076.us" 4 64 _ _ (by ent_auto)
      (by ent_auto) (by simp [List.length_zipWith, unpackLanes_length, highLanes64])
      hu8klen)
    rfl
  case hval => ent_auto

/-! ### The reduce and the tail

`for.cond.cleanup` carries the accumulator out of whichever loop ran, tests it with
one `ptestz` at its own lanes, and forms the tail's guard — `n != 0 && n % 64 == 0`.
`if.then20` reads the document's last byte and tests it against `klTailByte`'s two
parts, and `if.end24` narrows the `i1` verdict the two branches carried into the
ABI's `i64`. -/
theorem utf8Reduce (env : Env) (s : State) (p : String) (op : Operand)
    (u8k : List (BitVec 64)) (n : Nat)
    (hpre : s.pre = some p)
    (hinc : phiIncoming p [("entry", .imm (.splat 4 64 (BitVec.ofInt 64 0))),
      ("if.end14.us", .reg "%u8k.2.us"), ("for.body", .reg "%or.i47")] = some op)
    (hop : evalOperand (withEnv env s) op = some (.vec 4 64 u8k))
    (hu8klen : u8k.length = 4)
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n))) :
    ∃ env', denoteCode utf8Calls utf8Cleanup.instrs (withEnv env s) = some (withEnv env' s) ∧
      lookupName env' "%36" = some (.int 32 (ptestz (BitVec.ofNat 256 (packLanes u8k))
        (BitVec.ofNat 256 (packLanes u8k)))) ∧
      lookupName env' "%tobool16.not" = some (.int 1 (BitVec.ofBool
        (ptestz (BitVec.ofNat 256 (packLanes u8k))
          (BitVec.ofNat 256 (packLanes u8k)) = BitVec.ofInt 32 0))) ∧
      lookupName env' "%tobool19.not" = some (.int 1 (BitVec.ofBool
        (BitVec.ofNat 64 n &&& BitVec.ofInt 64 63 = BitVec.ofInt 64 0))) ∧
      lookupName env' "%or.cond45" = some (.int 1
        (BitVec.ofBool (BitVec.ofNat 64 n ≠ BitVec.ofInt 64 0) &&&
          BitVec.ofBool (BitVec.ofNat 64 n &&& BitVec.ofInt 64 63 = BitVec.ofInt 64 0))) := by
  refine ⟨?env', ?hrun, ?h36, ?h16, ?h19, ?hcond⟩
  case hrun =>
    simp only [utf8Cleanup, reg, lit, splatOf, JsonUtf8IR.ptestz]
    ent_step (utf8_phi _ _ "%u8k.0.lcssa" v4i64
      [("entry", .imm (.splat 4 64 (BitVec.ofInt 64 0))), ("if.end14.us", .reg "%u8k.2.us"),
        ("for.body", .reg "%or.i47")] p op (.vec 4 64 u8k) hpre hinc hop)
    ent_step (utf8_step_ptestz _ _ "%36" "%u8k.0.lcssa" (.reg "%u8k.0.lcssa") u8k u8k
      (by simp only [withEnv, evalOperand]; ent_auto) hu8klen (by ent_auto) hu8klen)
    ent_step (utf8_step_icmp_eq_imm _ _ "%tobool16.not" "%36" 32 _ (BitVec.ofInt 32 0)
      (by ent_auto))
    ent_step (utf8_step_icmp_ne_imm _ _ "%tobool17.not" "%n" 64 (BitVec.ofNat 64 n)
      (BitVec.ofInt 64 0) (by ent_auto))
    ent_step (utf8_step_and_imm _ _ "%and" "%n" 64 (BitVec.ofNat 64 n) (BitVec.ofInt 64 63)
      (by ent_auto))
    ent_step (utf8_step_icmp_eq_imm _ _ "%tobool19.not" "%and" 64 _ (BitVec.ofInt 64 0)
      (by ent_auto))
    ent_step (utf8_step_and1 _ _ "%or.cond45" "%tobool17.not" "%tobool19.not" _ _
      (by ent_auto) (by ent_auto))
    rfl
  case h36 => ent_auto
  case h16 => ent_auto
  case h19 => ent_auto
  case hcond => ent_auto

theorem utf8Tail (env : Env) (s : State) (b n : Nat) (t16 : BitVec 1) (d : BitVec 8)
    (hb : lookupName env "%b" = some (.ptr b))
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (htn : lookupName env "%tobool16.not" = some (.int 1 t16))
    (hb3 : 3 ≤ b) (hn64 : n < 2 ^ 63)
    (hread : readBytes s.mem (b + n - 1) 1 = some (natToBytes d.toNat 1)) :
    ∃ env', denoteCode utf8Calls utf8Then20.instrs (withEnv env s) = some (withEnv env' s) ∧
      lookupName env' "%or2373" = some (.int 1
        (t16 ||| (BitVec.ofBool (BitVec.ult (BitVec.ofInt 8 (-12)) d) |||
          BitVec.ofBool (d &&& BitVec.ofInt 8 (-2) = BitVec.ofInt 8 (-64))))) := by
  refine ⟨?env', ?hrun, ?hval⟩
  case hrun =>
    simp only [utf8Then20, reg, lit]
    ent_step (utf8_step_gep _ _ "%69" "%b" "%n" (.int 8) b (BitVec.ofNat 64 n) (by ent_auto)
      (by ent_auto) (by rw [toNat_ofNat64 n (by omega)]; exact hn64))
    rw [show b + (BitVec.ofNat 64 n).toNat * (Ty.int 8).sizeBytes = b + n from by
      rw [toNat_ofNat64 n (by omega), sizeBytes_i8, Nat.mul_one]]
    ent_step (step_gep64_m1 _ _ "%arrayidx" "%69" (b + n) (by ent_auto) (by omega))
    ent_step (utf8_step_load8 _ _ "%70" "%arrayidx" (b + n - 1) d (by ent_auto)
      (by rw [show b + n - 1 = b + n - 1 from rfl]; exact hread))
    ent_step (utf8_step_and_imm _ _ "%71" "%70" 8 d (BitVec.ofInt 8 (-2)) (by ent_auto))
    ent_step (utf8_step_icmp_eq_imm _ _ "%cmp.i" "%71" 8 _ (BitVec.ofInt 8 (-64))
      (by ent_auto))
    ent_step (step_icmp_ugt_imm _ _ "%cmp3.i" "%70" 8 d (BitVec.ofInt 8 (-12)) (by ent_auto))
    ent_step (utf8_step_or1 _ _ "%72" "%cmp3.i" "%cmp.i" _ _ (by ent_auto) (by ent_auto))
    ent_step (utf8_step_or1 _ _ "%or2373" "%tobool16.not" "%72" _ _ (by ent_auto)
      (by ent_auto))
    rfl
  case hval => ent_auto

theorem utf8Return (env : Env) (s : State) (p : String) (op : Operand) (e : BitVec 1)
    (hpre : s.pre = some p)
    (hinc : phiIncoming p [("if.then20", .reg "%or2373"),
      ("for.cond.cleanup", .reg "%tobool16.not")] = some op)
    (hop : evalOperand (withEnv env s) op = some (.int 1 e)) :
    ∃ env', denoteCode utf8Calls utf8End24.instrs (withEnv env s) = some (withEnv env' s) ∧
      lookupName env' "%err.0" = some (.int 64 (BitVec.ofNat 64 e.toNat)) := by
  refine ⟨?env', ?hrun, ?hval⟩
  case hrun =>
    simp only [utf8End24, reg]
    ent_step (utf8_phi _ _ "%err.0.in" (.int 1)
      [("if.then20", .reg "%or2373"), ("for.cond.cleanup", .reg "%tobool16.not")] p op
      (.int 1 e) hpre hinc hop)
    ent_step (utf8_step_zext _ _ "%err.0" "%err.0.in" 1 64 e (by ent_auto))
    rfl
  case hval => ent_auto

/-! ### The blocks around the two loops

The run lemmas step block by block, so the blocks between the ABI's entry and the
loop bodies are stated here: `entry` (the block count and the zero-block guard),
`for.body.lr.ph` (the gate selection), `for.body.us` (the gated loop's header) and
`if.end14.us` (its latch).  Each is one chain, read the way `pos8`'s run lemmas
read a block. -/
theorem utf8_step_lshr_imm (env : Env) (s : State) (d src : String) (w : Nat)
    (x c : BitVec w) (h : lookupName env src = some (.int w x)) :
    evalInstr utf8Calls (withEnv env s) (.binop d .lshr w (.reg src) (.imm (.int w c))) =
      some (withEnv ((d, .int w (x >>> c.toNat)) :: env) s) := by
  rw [evalInstr_binop (ha := evalOperand_reg_of env s src (.int w x) h)
    (hb := evalOperand_lit_of _ w c) (hr := by rfl)]
  simp only [withEnv, State.bind, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ushiftRight_eq]

/-- `entry`: `%add = n + 63`, `%div44 = %add >>> 6`, `%cmp74.not = %add < 64`. -/
theorem utf8Entry_run (env : Env) (s : State) (n : Nat)
    (hn : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n))) :
    ∃ env', denoteCode utf8Calls utf8Entry.instrs (withEnv env s) = some (withEnv env' s) ∧
      lookupName env' "%div44" = some (.int 64
        ((BitVec.ofNat 64 n + BitVec.ofInt 64 63) >>> (BitVec.ofInt 64 6).toNat)) ∧
      lookupName env' "%cmp74.not" = some (.int 1 (BitVec.ofBool
        (BitVec.ult (BitVec.ofNat 64 n + BitVec.ofInt 64 63) (BitVec.ofInt 64 64)))) := by
  refine ⟨?env', ?hrun, ?hdiv, ?hcmp⟩
  case hrun =>
    simp only [utf8Entry, reg, lit]
    ent_step (utf8_step_add _ _ "%add" "%n" 64 (BitVec.ofNat 64 n) (BitVec.ofInt 64 63)
      (by ent_auto))
    ent_step (utf8_step_lshr_imm _ _ "%div44" "%add" 64
      (BitVec.ofNat 64 n + BitVec.ofInt 64 63) (BitVec.ofInt 64 6) (by ent_auto))
    ent_step (step_icmp_ult_imm _ _ "%cmp74.not" "%add" 64
      (BitVec.ofNat 64 n + BitVec.ofInt 64 63) (BitVec.ofInt 64 64) (by ent_auto))
    rfl
  case hdiv => ent_auto
  case hcmp => ent_auto

/-- `for.body.lr.ph`: `%tobool.not = (%ungated == 0)`, the gate selection. -/
theorem utf8LrPh_run (env : Env) (s : State) (ungated : BitVec 32)
    (hu : lookupName env "%ungated" = some (.int 32 ungated)) :
    ∃ env', denoteCode utf8Calls utf8LrPh.instrs (withEnv env s) = some (withEnv env' s) ∧
      lookupName env' "%tobool.not" = some (.int 1
        (BitVec.ofBool (ungated = BitVec.ofInt 32 0))) := by
  refine ⟨?env', ?hrun, ?hval⟩
  case hrun =>
    simp only [utf8LrPh, reg, lit]
    ent_step (utf8_step_icmp_eq_imm _ _ "%tobool.not" "%ungated" 32 ungated
      (BitVec.ofInt 32 0) (by ent_auto))
    rfl
  case hval => ent_auto

/-- `for.body.us`: the gated loop's header.  Three phis carry the state in, then
the block's two `<4 x i64>` loads, their `or`, the `ptestz` at the high-bit mask,
and the `ascii && prev_ascii` test the loop branches on. -/
theorem utf8ForBodyUs_run (env : Env) (s : State) (p : String) (opP opU opB : Operand)
    (b bi : Nat) (prev : BitVec 32) (u8kIn : List (BitVec 64))
    (B0 B1 : List UInt8)
    (hpre : s.pre = some p)
    (hincP : phiIncoming p [("if.end14.us", .reg "%2"),
      ("for.body.lr.ph", .imm (.int 32 (BitVec.ofInt 32 1)))] = some opP)
    (hincU : phiIncoming p [("if.end14.us", .reg "%u8k.2.us"),
      ("for.body.lr.ph", .imm (.splat 4 64 (BitVec.ofInt 64 0)))] = some opU)
    (hincB : phiIncoming p [("if.end14.us", .reg "%inc.us"),
      ("for.body.lr.ph", .imm (.int 64 (BitVec.ofInt 64 0)))] = some opB)
    (hopP : evalOperand (withEnv env s) opP = some (.int 32 prev))
    (hopU : evalOperand (withEnv (("%prev_ascii.077.us", .int 32 prev) :: env) s) opU
      = some (.vec 4 64 u8kIn))
    (hopB : evalOperand (withEnv (("%u8k.076.us", .vec 4 64 u8kIn) ::
      ("%prev_ascii.077.us", .int 32 prev) :: env) s) opB
      = some (.int 64 (BitVec.ofNat 64 bi)))
    (hb : lookupName env "%b" = some (.ptr b))
    (hread0 : readBytes s.mem (b + 64 * bi) 32 = some B0)
    (hread1 : readBytes s.mem (b + 64 * bi + 32) 32 = some B1)
    (hbi64 : 64 * bi < 2 ^ 63) :
    ∃ env', denoteCode utf8Calls utf8ForBodyUs.instrs (withEnv env s) = some (withEnv env' s) ∧
      lookupName env' "%prev_ascii.077.us" = some (.int 32 prev) ∧
      lookupName env' "%u8k.076.us" = some (.vec 4 64 u8kIn) ∧
      lookupName env' "%bi.075.us" = some (.int 64 (BitVec.ofNat 64 bi)) ∧
      lookupName env' "%add.ptr.us" = some (.ptr (b + 64 * bi)) ∧
      lookupName env' "%0" = some (.vec 4 64 (unpackLanes 64 4 (bytesToNat B0))) ∧
      lookupName env' "%1" = some (.vec 4 64 (unpackLanes 64 4 (bytesToNat B1))) ∧
      lookupName env' "%2" = some (.int 32 (ptestz
        (BitVec.ofNat 256 (packLanes (List.zipWith (· ||| ·) (unpackLanes 64 4 (bytesToNat B1))
          (unpackLanes 64 4 (bytesToNat B0)))))
        (BitVec.ofNat 256 (packLanes highLanes64)))) ∧
      lookupName env' "%or.cond.us" = some (.int 1
        (BitVec.ofBool (ptestz
          (BitVec.ofNat 256 (packLanes (List.zipWith (· ||| ·) (unpackLanes 64 4 (bytesToNat B1))
            (unpackLanes 64 4 (bytesToNat B0)))))
          (BitVec.ofNat 256 (packLanes highLanes64)) ≠ BitVec.ofInt 32 0) &&&
        BitVec.ofBool (prev ≠ BitVec.ofInt 32 0))) := by
  have h0 : B0.length = 32 := readBytes_length s.mem (b + 64 * bi) 32 hread0
  have h1 : B1.length = 32 := readBytes_length s.mem (b + 64 * bi + 32) 32 hread1
  have hV0 : B0 = natToBytes (bytesToNat B0) 32 :=
    (natToBytes_bytesToNat B0).symm.trans (by rw [h0])
  have hV1 : B1 = natToBytes (bytesToNat B1) 32 :=
    (natToBytes_bytesToNat B1).symm.trans (by rw [h1])
  have hlt0 : bytesToNat B0 < 2 ^ 256 := by
    have := bytesToNat_lt B0
    rwa [h0, show (256 : Nat) ^ 32 = 2 ^ 256 from by decide] at this
  have hlt1 : bytesToNat B1 < 2 ^ 256 := by
    have := bytesToNat_lt B1
    rwa [h1, show (256 : Nat) ^ 32 = 2 ^ 256 from by decide] at this
  refine ⟨?env', ?hrun, ?hP, ?hU, ?hB, ?hptr, ?h0', ?h1', ?h2, ?hcond⟩
  case hrun =>
    simp only [utf8ForBodyUs, reg, lit, splatOf, highBitMask, JsonUtf8IR.ptestz]
    ent_step (utf8_phi env s "%prev_ascii.077.us" (.int 32)
      [("if.end14.us", .reg "%2"), ("for.body.lr.ph", .imm (.int 32 (BitVec.ofInt 32 1)))]
      p opP (.int 32 prev) hpre hincP hopP)
    ent_step (utf8_phi (("%prev_ascii.077.us", .int 32 prev) :: env) s "%u8k.076.us" v4i64
      [("if.end14.us", .reg "%u8k.2.us"),
        ("for.body.lr.ph", .imm (.splat 4 64 (BitVec.ofInt 64 0)))]
      p opU (.vec 4 64 u8kIn) hpre hincU hopU)
    ent_step (utf8_phi (("%u8k.076.us", .vec 4 64 u8kIn) ::
      ("%prev_ascii.077.us", .int 32 prev) :: env) s "%bi.075.us" (.int 64)
      [("if.end14.us", .reg "%inc.us"), ("for.body.lr.ph", .imm (.int 64 (BitVec.ofInt 64 0)))]
      p opB (.int 64 (BitVec.ofNat 64 bi)) hpre hincB hopB)
    ent_step (utf8_step_shl _ _ "%shl.us" "%bi.075.us" 64 (BitVec.ofNat 64 bi)
      (BitVec.ofInt 64 6) (by ent_auto))
    rw [shl64_six bi (by omega)]
    ent_step (utf8_step_gep _ _ "%add.ptr.us" "%b" "%shl.us" (.int 8) b
      (BitVec.ofNat 64 (64 * bi)) (by ent_auto) (by ent_auto)
      (by rw [toNat_ofNat64 (64 * bi) (by omega)]; exact hbi64))
    rw [show b + (BitVec.ofNat 64 (64 * bi)).toNat * (Ty.int 8).sizeBytes = b + 64 * bi from by
      rw [toNat_ofNat64 (64 * bi) (by omega), sizeBytes_i8, Nat.mul_one]]
    ent_step (step_load4_64 _ _ "%0" "%add.ptr.us" (b + 64 * bi) (bytesToNat B0) (by ent_auto)
      (by rw [← hV0]; exact hread0) hlt0)
    ent_step (utf8_step_gep_imm _ _ "%add.ptr3.us" "%add.ptr.us" (.int 8) (b + 64 * bi)
      (BitVec.ofInt 64 32) (by ent_auto) (by decide))
    rw [show b + 64 * bi + (BitVec.ofInt 64 32).toNat * (Ty.int 8).sizeBytes = b + 64 * bi + 32
      from by rw [show (BitVec.ofInt 64 32).toNat = 32 from by decide, sizeBytes_i8]]
    ent_step (step_load4_64 _ _ "%1" "%add.ptr3.us" (b + 64 * bi + 32) (bytesToNat B1)
      (by ent_auto) (by rw [← hV1]; exact hread1) hlt1)
    ent_step (utf8_step_vec_or _ _ "%or.i46.us" "%1" "%0" 4 64 _ _ (by ent_auto) (by ent_auto)
      (by rw [unpackLanes_length]) (by rw [unpackLanes_length]))
    ent_step (utf8_step_ptestz _ _ "%2" "%or.i46.us"
      (.imm (.splat 4 64 (BitVec.ofInt 64 (-9187201950435737472))))
      (List.zipWith (· ||| ·) (unpackLanes 64 4 (bytesToNat B1))
        (unpackLanes 64 4 (bytesToNat B0))) highLanes64
      (by simp only [evalOperand, Const.toValue, highLanes64])
      (by simp [highLanes64]) (by ent_auto)
      (len4_zip64 (· ||| ·) _ _ (by rw [unpackLanes_length]) (by rw [unpackLanes_length])))
    ent_step (utf8_step_icmp_ne_imm _ _ "%tobool9.us" "%2" 32 _ (BitVec.ofInt 32 0)
      (by ent_auto))
    ent_step (utf8_step_icmp_ne_imm _ _ "%tobool10.us" "%prev_ascii.077.us" 32 prev
      (BitVec.ofInt 32 0) (by ent_auto))
    ent_step (utf8_step_and1 _ _ "%or.cond.us" "%tobool9.us" "%tobool10.us" _ _
      (by ent_auto) (by ent_auto))
    rfl
  case hP => ent_auto
  case hU => ent_auto
  case hB => ent_auto
  case hptr => ent_auto
  case h0' => ent_auto
  case h1' => ent_auto
  case h2 => ent_auto
  case hcond => ent_auto

/-- `if.end14.us`: the gated loop's latch.  The phi carries the accumulator in
from either edge, `%inc.us` is the block index's successor, and `%exitcond79.not`
is the loop's test. -/
theorem utf8EndUs_run (env : Env) (s : State) (p : String) (op : Operand)
    (u8k : List (BitVec 64)) (bi nb : Nat)
    (hpre : s.pre = some p)
    (hinc : phiIncoming p [("for.body.us", .reg "%u8k.076.us"),
      ("if.then11.us", .reg "%or.i.us")] = some op)
    (hop : evalOperand (withEnv env s) op = some (.vec 4 64 u8k))
    (hbi : lookupName env "%bi.075.us" = some (.int 64 (BitVec.ofNat 64 bi)))
    (hdiv : lookupName env "%div44" = some (.int 64 (BitVec.ofNat 64 nb))) :
    ∃ env', denoteCode utf8Calls utf8EndUs.instrs (withEnv env s) = some (withEnv env' s) ∧
      lookupName env' "%u8k.2.us" = some (.vec 4 64 u8k) ∧
      lookupName env' "%inc.us" = some (.int 64 (BitVec.ofNat 64 bi + BitVec.ofInt 64 1)) ∧
      lookupName env' "%exitcond79.not" = some (.int 1 (BitVec.ofBool
        (BitVec.ofNat 64 bi + BitVec.ofInt 64 1 = BitVec.ofNat 64 nb))) := by
  refine ⟨?env', ?hrun, ?hU, ?hI, ?hE⟩
  case hrun =>
    simp only [utf8EndUs, reg, lit]
    ent_step (utf8_phi _ _ "%u8k.2.us" v4i64
      [("for.body.us", .reg "%u8k.076.us"), ("if.then11.us", .reg "%or.i.us")]
      p op (.vec 4 64 u8k) hpre hinc hop)
    ent_step (utf8_step_add _ _ "%inc.us" "%bi.075.us" 64 (BitVec.ofNat 64 bi)
      (BitVec.ofInt 64 1) (by ent_auto))
    ent_step (utf8_step_icmp_eq _ _ "%exitcond79.not" "%inc.us" "%div44" 64 _ _
      (by ent_auto) (by ent_auto))
    rfl
  case hU => ent_auto
  case hI => ent_auto
  case hE => ent_auto

/-! ### The stepping surface at `utf8Function`

`step` looks a block up by name and runs its instructions, then its terminator;
the run lemmas below read one block per step, so the nine lookups and the two
`runFuel` reductions are stated once, here, rather than rediscovered per step. -/
theorem findBlock_utf8Entry : utf8Function.findBlock "entry" = some utf8Entry := by
  decide

theorem findBlock_utf8LrPh : utf8Function.findBlock "for.body.lr.ph" = some utf8LrPh := by
  decide

theorem findBlock_utf8ForBodyUs : utf8Function.findBlock "for.body.us" = some utf8ForBodyUs := by
  decide

theorem findBlock_utf8ThenUs : utf8Function.findBlock "if.then11.us" = some utf8ThenUs := by
  decide

theorem findBlock_utf8EndUs : utf8Function.findBlock "if.end14.us" = some utf8EndUs := by
  decide

theorem findBlock_utf8Cleanup : utf8Function.findBlock "for.cond.cleanup" = some utf8Cleanup := by
  decide

theorem findBlock_utf8ForBody : utf8Function.findBlock "for.body" = some utf8ForBody := by
  decide

theorem findBlock_utf8Then20 : utf8Function.findBlock "if.then20" = some utf8Then20 := by
  decide

theorem findBlock_utf8End24 : utf8Function.findBlock "if.end24" = some utf8End24 := by
  decide

/-- One block's step: its instructions then its terminator. -/
theorem step_of_utf8 (s : State) (name : String) (b : Block) (s' : State)
    (hpc : s.pc = name) (hfind : utf8Function.findBlock name = some b)
    (hbody : denoteCode utf8Calls b.instrs s = some s') :
    step utf8Calls utf8Function s = execTerm s' b.term := by
  simp [step, hpc, hfind, hbody]

/-- A jump spends one step of fuel. -/
theorem runFuel_jump_utf8 {s s' : State} {n : Nat}
    (h : step utf8Calls utf8Function s = .jump s') :
    runFuel utf8Calls (n + 1) utf8Function s = runFuel utf8Calls n utf8Function s' := by
  simp [runFuel, h]

/-- A return ends the run, and the outcome carries the returning state's memory. -/
theorem runFuel_ret_utf8 {s s' : State} {v : Option Value} {n : Nat}
    (h : step utf8Calls utf8Function s = .ret v s') :
    runFuel utf8Calls (n + 1) utf8Function s = some (.ret v s'.mem) := by
  simp [runFuel, h]

/-- A block whose run refuses the step is `ub` at any positive fuel. -/
theorem runFuel_ub_utf8 {s : State} {n : Nat} (h : step utf8Calls utf8Function s = .ub) :
    runFuel utf8Calls (n + 1) utf8Function s = some .ub := by
  simp [runFuel, h]

/-- Taking a prefix and then a prefix of the rest is one prefix. -/
theorem take_append_take_len {α : Type} (l : List α) (m k : Nat) :
    l.take m ++ (l.drop m).take k = l.take (m + k) := by
  induction m generalizing l with
  | zero => simp
  | succ m ih =>
      cases l with
      | nil => simp
      | cons x xs =>
          show x :: (xs.take m ++ (xs.drop m).take k) = (x :: xs).take (m + 1 + k)
          rw [show m + 1 + k = (m + k) + 1 from by omega, List.take_succ_cons, ih xs]

/-- A read inside the staged window: any thirty-two bytes at an interior offset
are the window's slice there. -/
theorem win_read (mem : Mem) (b nb j : Nat) (W : List UInt8)
    (hw : readBytes mem (b - 3) (3 + 64 * nb) = some W) (hb3 : 3 ≤ b)
    (hj : j + 32 ≤ 3 + 64 * nb) :
    readBytes mem (b - 3 + j) 32 = some ((W.drop j).take 32) := by
  have hN : j + (3 + 64 * nb - j) = 3 + 64 * nb := by omega
  have h1 : readBytes mem (b - 3) (j + (3 + 64 * nb - j)) = some W := by rw [hN]; exact hw
  obtain ⟨-, h2⟩ := readBytes_split mem (b - 3) j (3 + 64 * nb - j) h1
  have hM : 32 + ((3 + 64 * nb - j) - 32) = 3 + 64 * nb - j := by omega
  have h3 : readBytes mem ((b - 3) + j) (32 + ((3 + 64 * nb - j) - 32)) = some (W.drop j) := by
    rw [hM]; exact h2
  exact (readBytes_split mem ((b - 3) + j) 32 ((3 + 64 * nb - j) - 32) h3).1

/-! ### The window, byte by byte -/

theorem readBytes_eq_none_iff (m : Mem) (a n : Nat) :
    readBytes m a n = none ↔ ∃ k, k < n ∧ readByte m (a + k) = none := by
  induction n generalizing a with
  | zero => simp [readBytes]
  | succ n ih =>
      rw [readBytes]
      constructor
      · intro h
        cases hb : readByte m a with
        | none => exact ⟨0, Nat.succ_pos n, hb⟩
        | some b =>
            cases hr : readBytes m (a + 1) n with
            | none =>
                obtain ⟨k, hk, hkn⟩ := (ih (a + 1)).mp hr
                exact ⟨k + 1, by omega, by rw [show a + (k + 1) = a + 1 + k from by omega]; exact hkn⟩
            | some bs => rw [hb, hr] at h; exact absurd h (by simp)
      · rintro ⟨k, hk, hnone⟩
        cases hb : readByte m a with
        | none => simp
        | some b =>
            cases k with
            | zero =>
                rw [Nat.add_zero] at hnone
                rw [hb] at hnone
                exact absurd hnone (by simp)
            | succ j =>
                have h2 : readBytes m (a + 1) n = none :=
                  (ih (a + 1)).mpr ⟨j, by omega,
                    by rw [show a + 1 + j = a + (j + 1) from by omega]; exact hnone⟩
                simp [h2]

theorem readBytes_eq_none_of_readByte_none (m : Mem) {a p n : Nat}
    (h : readByte m a = none) (h1 : p ≤ a) (h2 : a < p + n) :
    readBytes m p n = none :=
  (readBytes_eq_none_iff m p n).mpr ⟨a - p, by omega,
    by rw [show p + (a - p) = a from by omega]; exact h⟩

theorem exists_readBytes_of_readable (m : Mem) (p n : Nat)
    (h : ∀ k, k < n → readByte m (p + k) ≠ none) : ∃ bs, readBytes m p n = some bs := by
  cases hr : readBytes m p n with
  | none =>
      obtain ⟨k, hk, hnone⟩ := (readBytes_eq_none_iff m p n).mp hr
      exact absurd hnone (h k hk)
  | some bs => exact ⟨bs, rfl⟩

/-! ### `klByte` past zero padding -/

theorem klByte_append_zeros (l z : List UInt8) (hz : ∀ x ∈ z, x = 0x00) (j : Nat) :
    klByte (l ++ z) j = klByte l j := by
  unfold klByte
  by_cases hj : j < l.length
  · rw [getD_of_lt (l ++ z) 0x00 (by rw [List.length_append]; omega),
        getD_of_lt l 0x00 hj, List.getElem_append_left hj]
  · by_cases hjz : j < (l ++ z).length
    · rw [getD_of_lt (l ++ z) 0x00 hjz, List.getElem_append_right (by omega),
        List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      exact hz _ (List.getElem_mem _)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega),
        List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]

theorem klByte_window (bs : List UInt8) (n nb j : Nat) :
    klByte (utf8Window bs n nb) j = klByte (0x00 :: 0x00 :: 0x00 :: bs) j := by
  rw [show utf8Window bs n nb
      = (0x00 :: 0x00 :: 0x00 :: bs) ++ List.replicate (64 * nb - n) 0x00 from rfl]
  exact klByte_append_zeros _ _ (by
    intro x hx
    exact List.eq_of_mem_replicate hx) j

theorem klErrWin_window (bs : List UInt8) (n nb t : Nat) :
    klErrWin (utf8Window bs n nb) t = klErrWin (0x00 :: 0x00 :: 0x00 :: bs) t := by
  simp only [klErrWin, klByte_window]

theorem klErrAll_window (bs : List UInt8) (n nb L : Nat) :
    klErrAll (utf8Window bs n nb) L ↔ klErrAll (0x00 :: 0x00 :: 0x00 :: bs) L := by
  unfold klErrAll
  constructor
  · intro h t ht
    rw [← klErrWin_window bs n nb t]
    exact h t ht
  · intro h t ht
    rw [klErrWin_window bs n nb t]
    exact h t ht

/-! ### The block's error vector, read from the window -/

theorem u8_or_eq_zero_iff (a b : UInt8) : a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have h1 : (a ||| b).toNat = 0 := by rw [h]; rfl
    rw [UInt8.toNat_or, Nat.or_eq_zero_iff] at h1
    exact ⟨UInt8.toNat_inj.mp h1.1, UInt8.toNat_inj.mp h1.2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem klByte_take_drop (l : List UInt8) (m n k : Nat) (hk : k < n) :
    klByte ((l.drop m).take n) k = klByte l (m + k) := by
  unfold klByte
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hk, List.getElem?_drop,
    ← List.getD_eq_getElem?_getD]

theorem klErrVec_getD (s : List UInt8) (j : Nat) (hj : j < 32) :
    (klErrVec s).getD j 0x00
      = klErrByte (klByte s j) (klByte s (j + 1)) (klByte s (j + 2)) (klByte s (j + 3)) := by
  unfold klErrVec
  rw [getD_of_lt (List.map _ (List.range 32)) 0x00 (by simp; omega), List.getElem_map,
    List.getElem_range (by simpa using hj)]

/-- `List.drop_take`'s statement, proved from `List`'s own recursion rather than
taken from the library: the library lemma carries `Classical.choice`, and nothing
in this slice's arithmetic needs a decision procedure. -/
theorem drop_take' {α : Type} (i j : Nat) (l : List α) :
    (l.take j).drop i = (l.drop i).take (j - i) := by
  induction l generalizing j i with
  | nil =>
      rw [List.take_nil, List.drop_nil, List.take_nil]
  | cons x xs ih =>
      cases j with
      | zero =>
          rw [List.take_zero, List.drop_nil, Nat.zero_sub, List.take_zero]
      | succ j =>
          cases i with
          | zero => rfl
          | succ i =>
              rw [Nat.succ_sub_succ]
              exact ih i j

theorem block_arg_lo (l : List UInt8) (m : Nat) :
    (l.drop m).take 3 ++ ((l.drop (m + 3)).take 64).take 32 = (l.drop m).take 35 := by
  rw [show l.drop (m + 3) = (l.drop m).drop 3 from by rw [List.drop_drop],
    List.take_take, Nat.min_eq_left (by decide : 32 ≤ 64)]
  exact take_append_take_len (l.drop m) 3 32

theorem block_arg_hi (l : List UInt8) (m : Nat) :
    ((l.drop m).take 3 ++ ((l.drop (m + 3)).take 64).take 32).drop 32 ++
      ((l.drop (m + 3)).take 64).drop 32 = (l.drop (m + 32)).take 35 := by
  rw [block_arg_lo l m, drop_take', drop_take',
    show l.drop (m + 3) = (l.drop m).drop 3 from by rw [List.drop_drop],
    show l.drop (m + 32) = (l.drop m).drop 32 from by rw [List.drop_drop],
    show List.drop 32 (List.drop 3 (l.drop m)) = List.drop 3 (List.drop 32 (l.drop m)) from by
      rw [show List.drop 32 (List.drop 3 (l.drop m)) = List.drop 35 (l.drop m) from by
            rw [List.drop_drop],
          show List.drop 3 (List.drop 32 (l.drop m)) = List.drop 35 (l.drop m) from by
            rw [List.drop_drop]]]
  exact take_append_take_len _ 3 32

theorem klErrBlk_getD_zero_iff (bs : List UInt8) (i j : Nat) (hj : j < 32) :
    (klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) i)
        (klBlk (0x00 :: 0x00 :: 0x00 :: bs) i)).getD j 0x00 = 0
      ↔ klErrWin (0x00 :: 0x00 :: 0x00 :: bs) (64 * i + j) ∧
        klErrWin (0x00 :: 0x00 :: 0x00 :: bs) (64 * i + 32 + j) := by
  unfold klErrBlk klPre klBlk klErr32
  rw [block_arg_hi (0x00 :: 0x00 :: 0x00 :: bs) (64 * i)]
  rw [block_arg_lo (0x00 :: 0x00 :: 0x00 :: bs) (64 * i)]
  rw [getD_zipWith (· ||| ·) _ _ 0x00 0x00 0x00
    (by rw [klErrVec_length]; exact hj) (by rw [klErrVec_length]; exact hj)]
  rw [klErrVec_getD _ _ hj, klErrVec_getD _ _ hj]
  have ja : j + 1 < 33 := Nat.add_lt_add_right hj 1
  have jb : j + 2 < 34 := Nat.add_lt_add_right ja 1
  have jc : j + 3 < 35 := Nat.add_lt_add_right jb 1
  have hj35 : j < 35 := Nat.lt_of_lt_of_le hj (by decide)
  have hj36 : j + 1 < 35 := Nat.lt_of_lt_of_le ja (by decide)
  have hj37 : j + 2 < 35 := Nat.lt_of_lt_of_le jb (by decide)
  have hj38 : j + 3 < 35 := jc
  simp only [klByte_take_drop _ _ _ _ hj35, klByte_take_drop _ _ _ _ hj36,
    klByte_take_drop _ _ _ _ hj37, klByte_take_drop _ _ _ _ hj38]
  rw [u8_or_eq_zero_iff]
  unfold klErrWin
  constructor
  · rintro ⟨h1, h2⟩
    simp only [Nat.add_assoc] at h1 h2 ⊢
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    simp only [Nat.add_assoc] at h1 h2 ⊢
    exact ⟨h1, h2⟩

/-! ### The accumulator the loop folds -/

/-- The accumulator after `i` blocks, in the step the ungated loop takes: each
block's error vector or-ed in, from the three carry bytes and the block's sixty-four. -/
def klAcc (bs : List UInt8) (i : Nat) : List UInt8 :=
  (List.range i).foldl (fun acc bi =>
    List.zipWith (· ||| ·) acc
      (klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) bi)
        (klBlk (0x00 :: 0x00 :: 0x00 :: bs) bi)))
    (List.replicate 32 0x00)

theorem klStep_false_fst (bs : List UInt8) (st : List UInt8 × Bool) (bi : Nat) :
    (klStep (0x00 :: 0x00 :: 0x00 :: bs) false st bi).1
      = List.zipWith (· ||| ·) st.1
          (klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) bi)
            (klBlk (0x00 :: 0x00 :: 0x00 :: bs) bi)) := by
  unfold klStep
  rw [ite_eq_right (by simp)]

theorem klRun_false_fst (bs : List UInt8) :
    ∀ (nb : Nat) (init : List UInt8) (b0 : Bool),
      (((List.range nb).foldl (fun (st : List UInt8 × Bool) bi =>
          klStep (0x00 :: 0x00 :: 0x00 :: bs) false st bi) (init, b0))).1
        = (List.range nb).foldl (fun acc bi => List.zipWith (· ||| ·) acc
            (klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) bi)
              (klBlk (0x00 :: 0x00 :: 0x00 :: bs) bi))) init := by
  intro nb
  induction nb with
  | zero => intro init b0; rfl
  | succ n ih =>
      intro init b0
      rw [List.range_succ, List.foldl_append, List.foldl_append,
        List.foldl_cons, List.foldl_nil, klStep_false_fst, ih]
      rfl

theorem klAll_false_eq_klAcc (bs : List UInt8) :
    klAll false bs = klAcc bs ((bs.length + 63) / 64) := by
  rw [klAll_eq_klRun]
  exact klRun_false_fst bs _ _ _

/-! ### The accumulator is zero exactly when every window reads zero -/

theorem zipWith_or_zero_iff (a b : List UInt8) (ha : a.length = 32) (hb : b.length = 32) :
    List.zipWith (· ||| ·) a b = List.replicate 32 0x00 ↔
      a = List.replicate 32 0x00 ∧ b = List.replicate 32 0x00 := by
  constructor
  · intro h
    have hzero : ∀ j, j < 32 → a.getD j 0x00 ||| b.getD j 0x00 = 0x00 := by
      intro j hj
      have hj2 : j < (List.replicate 32 (0x00 : UInt8)).length := by simp; omega
      have hh := congrArg (fun l => l.getD j 0x00) h
      rw [getD_zipWith (· ||| ·) a b 0x00 0x00 0x00 (by rw [ha]; omega) (by rw [hb]; omega),
        getD_of_lt (List.replicate 32 0x00) 0x00 hj2, List.getElem_replicate] at hh
      exact hh
    constructor
    · apply List.ext_getElem
      · rw [ha]; simp
      · intro j h1 h2
        rw [List.getElem_replicate]
        have hz := hzero j (by rw [ha] at h1; omega)
        rw [getD_of_lt a 0x00 h1,
          getD_of_lt b 0x00 (by rw [hb]; rw [ha] at h1; omega)] at hz
        exact (u8_or_eq_zero_iff _ _).mp hz |>.1
    · apply List.ext_getElem
      · rw [hb]; simp
      · intro j h1 h2
        rw [List.getElem_replicate]
        have hz := hzero j (by rw [hb] at h1; omega)
        rw [getD_of_lt a 0x00 (by rw [ha]; rw [hb] at h1; omega),
          getD_of_lt b 0x00 h1] at hz
        exact (u8_or_eq_zero_iff _ _).mp hz |>.2
  · rintro ⟨rfl, rfl⟩
    apply List.ext_getElem
    · simp
    · intro j h1 h2
      simp only [List.getElem_zipWith, List.getElem_replicate]
      decide

theorem all_zero_replicate (l : List UInt8) (h : l.length = 32) :
    l.all (fun x => decide (x = 0x00)) = true ↔ l = List.replicate 32 0x00 := by
  rw [List.all_eq_true]
  constructor
  · intro hh
    apply List.ext_getElem
    · rw [h]; simp
    · intro j h1 h2
      rw [List.getElem_replicate]
      exact of_decide_eq_true (hh l[j] (List.getElem_mem h1))
  · rintro rfl
    intro x hx
    rw [List.eq_of_mem_replicate hx]
    rfl

theorem eq_replicate_zero_iff_getD (l : List UInt8) (h : l.length = 32) :
    l = List.replicate 32 0x00 ↔ ∀ j, j < 32 → l.getD j 0x00 = 0x00 := by
  constructor
  · rintro rfl j hj
    rw [getD_of_lt (List.replicate 32 (0x00 : UInt8)) 0x00 (by simpa using hj),
      List.getElem_replicate]
  · intro hh
    apply List.ext_getElem
    · rw [h]; simp
    · intro j h1 h2
      rw [List.getElem_replicate]
      exact (getD_of_lt l 0x00 h1).symm.trans (hh j (by omega))

theorem klAcc_succ (bs : List UInt8) (i : Nat) :
    klAcc bs (i + 1) = List.zipWith (· ||| ·) (klAcc bs i)
      (klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) i)
        (klBlk (0x00 :: 0x00 :: 0x00 :: bs) i)) := by
  unfold klAcc
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem klAcc_length (bs : List UInt8) (i : Nat) : (klAcc bs i).length = 32 := by
  have key : ∀ (l : List Nat) (init : List UInt8), init.length = 32 →
      ((l.foldl (fun acc bi => List.zipWith (· ||| ·) acc
        (klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) bi)
          (klBlk (0x00 :: 0x00 :: 0x00 :: bs) bi))) init)).length = 32 := by
    intro l
    induction l with
    | nil => intro init h; exact h
    | cons x xs ih =>
        intro init h
        rw [List.foldl_cons]
        refine ih (List.zipWith (· ||| ·) init
          (klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) x)
            (klBlk (0x00 :: 0x00 :: 0x00 :: bs) x))) ?_
        rw [List.length_zipWith, h, klErrBlk_length, Nat.min_self]
  unfold klAcc
  exact key _ _ rfl

theorem klAcc_zero_iff (bs : List UInt8) :
    ∀ i, klAcc bs i = List.replicate 32 0x00 ↔
      ∀ bi, bi < i → klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) bi)
        (klBlk (0x00 :: 0x00 :: 0x00 :: bs) bi) = List.replicate 32 0x00 := by
  intro i
  induction i with
  | zero =>
      constructor
      · intro _ bi hb; omega
      · intro _; rfl
  | succ n ih =>
      have hs := klAcc_succ bs n
      constructor
      · intro h bi hb
        have hz := (zipWith_or_zero_iff (klAcc bs n)
          (klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) n)
            (klBlk (0x00 :: 0x00 :: 0x00 :: bs) n))
          (klAcc_length bs n) (klErrBlk_length _ _)).mp (by rw [← hs]; exact h)
        rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hlt | heq
        · exact ih.mp hz.1 bi hlt
        · subst heq; exact hz.2
      · intro h
        rw [hs]
        refine (zipWith_or_zero_iff (klAcc bs n)
          (klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) n)
            (klBlk (0x00 :: 0x00 :: 0x00 :: bs) n))
          (klAcc_length bs n) (klErrBlk_length _ _)).mpr ⟨?_, h n (by omega)⟩
        exact ih.mpr (fun bi hb => h bi (by omega))

/-- `Nat.div_lt_of_lt_mul`'s statement, proved from the division identity rather
than taken from the library: the library lemma carries `Classical.choice`. -/
theorem div_lt_of_lt_mul' {n m k : Nat} (h : m < n * k) : m / n < k := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [Nat.zero_mul] at h
    exact absurd h (Nat.not_lt_zero m)
  · refine Nat.lt_of_not_le (fun hk => ?_)
    have h1 : m / n * n ≤ m := Nat.div_mul_le_self m n
    have h1' : n * (m / n) ≤ m := by rw [Nat.mul_comm]; exact h1
    have h2 : n * k ≤ n * (m / n) := Nat.mul_le_mul_left n hk
    exact absurd (Nat.lt_of_lt_of_le h (Nat.le_trans h2 h1')) (Nat.lt_irrefl m)

theorem klAcc_zero_iff_klErrAll (bs : List UInt8) (nb : Nat) :
    klAcc bs nb = List.replicate 32 0x00 ↔ klErrAll (0x00 :: 0x00 :: 0x00 :: bs) (64 * nb) := by
  rw [klAcc_zero_iff, klErrAll]
  constructor
  · intro h t ht
    have hbi : t / 64 < nb :=
      div_lt_of_lt_mul' (by simpa [Nat.mul_comm] using ht)
    have hr : t % 64 < 64 := Nat.mod_lt _ (by decide)
    have ht' : 64 * (t / 64) + t % 64 = t := Nat.div_add_mod t 64
    rcases Nat.lt_or_ge (t % 64) 32 with h32 | h32
    · have hz : (klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) (t / 64))
          (klBlk (0x00 :: 0x00 :: 0x00 :: bs) (t / 64))).getD (t % 64) 0x00 = 0 := by
        rw [h (t / 64) hbi, getD_of_lt (List.replicate 32 (0x00 : UInt8)) 0x00 (by simpa using h32),
          List.getElem_replicate]
      have hw := (klErrBlk_getD_zero_iff bs (t / 64) (t % 64) h32).mp hz
      rw [← ht']
      exact hw.1
    · have h32' : t % 64 - 32 < 32 := by
        have hr64 : t % 64 < 64 := Nat.mod_lt _ (by decide)
        exact Nat.sub_lt_left_of_lt_add h32 (by simpa using hr64)
      have hz : (klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) (t / 64))
          (klBlk (0x00 :: 0x00 :: 0x00 :: bs) (t / 64))).getD (t % 64 - 32) 0x00 = 0 := by
        rw [h (t / 64) hbi, getD_of_lt (List.replicate 32 (0x00 : UInt8)) 0x00 (by simpa using h32'),
          List.getElem_replicate]
      have hw := (klErrBlk_getD_zero_iff bs (t / 64) (t % 64 - 32) h32').mp hz
      rw [← ht']
      have he : 64 * (t / 64) + 32 + (t % 64 - 32) = 64 * (t / 64) + t % 64 := by
        rw [Nat.add_assoc, Nat.add_sub_of_le h32]
      rw [← he]
      exact hw.2
  · intro h bi hbi
    apply (eq_replicate_zero_iff_getD _ (klErrBlk_length _ _)).mpr
    intro j hj
    have hle64 : 64 * bi + 64 ≤ 64 * nb :=
      calc 64 * bi + 64 = 64 * (bi + 1) := (Nat.mul_succ 64 bi).symm
        _ ≤ 64 * nb := Nat.mul_le_mul_left 64 (Nat.succ_le_of_lt hbi)
    have hle : 64 * bi + 32 ≤ 64 * nb :=
      Nat.le_trans (Nat.add_le_add_left (by decide : 32 ≤ 64) _) hle64
    have hlt : 64 * bi + j < 64 * nb :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _) hle
    have hlt2 : 64 * bi + 32 + j < 64 * nb := by
      rw [Nat.add_assoc]
      refine Nat.lt_of_lt_of_le (Nat.add_lt_add_left ?_ (64 * bi)) hle64
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj 32) (by decide)
    exact (klErrBlk_getD_zero_iff bs bi j hj).mpr ⟨h _ hlt, h _ hlt2⟩

theorem klAll_zero_iff_klErrAll (bs : List UInt8) (n nb : Nat) (gate : Bool)
    (hn : n = bs.length) (hnb : nb = (n + 63) / 64) :
    (klAll gate bs).all (fun x => decide (x = 0x00)) = true ↔
      klErrAll (utf8Window bs n nb) (64 * nb) := by
  have hnb' : nb = (bs.length + 63) / 64 := by rw [hnb, hn]
  have hsame : klAll gate bs = klAll false bs := by
    cases gate with
    | false => rfl
    | true => exact klAll_gate_invariant bs
  have hlen : (klAll false bs).length = 32 := by
    rw [klAll_false_eq_klAcc bs]
    exact klAcc_length bs _
  rw [klErrAll_window]
  constructor
  · intro h
    have h0 : (klAll false bs).all (fun x => decide (x = 0x00)) = true := by
      rw [← hsame]
      exact h
    have h1 : klAcc bs nb = List.replicate 32 0x00 := by
      rw [hnb', ← klAll_false_eq_klAcc bs]
      exact (all_zero_replicate _ hlen).mp h0
    exact klAcc_zero_iff_klErrAll bs nb |>.mp h1
  · intro h
    have h1 : klAcc bs nb = List.replicate 32 0x00 := (klAcc_zero_iff_klErrAll bs nb).mpr h
    have h0 : (klAcc bs nb).all (fun x => decide (x = 0x00)) = true :=
      (all_zero_replicate _ (klAcc_length bs nb)).mpr h1
    rw [hsame, klAll_false_eq_klAcc bs, ← hnb']
    exact h0


/-! ### The names the loop carries across a block -/

/-- The three cells the loop's bodies never write: the pointer, the document's
length and the block count. -/
def utf8Kept : List String := ["%b", "%n", "%div44"]

theorem denoteCode_kept (instrs : List Instr) (env env' : Env) (s : State)
    (hrun : denoteCode utf8Calls instrs (withEnv env s) = some (withEnv env' s))
    (hn : ∀ i ∈ instrs, i.dst? ∉ utf8Kept.map some) :
    ∀ n ∈ utf8Kept, lookupName env' n = lookupName env n := by
  intro n hmem
  have h := denoteCode_lookupName utf8Calls instrs n
    (fun i hi hd => hn i hi (hd.symm ▸ List.mem_map_of_mem (f := some) hmem))
    (withEnv env s) (withEnv env' s) hrun
  simpa [withEnv] using h

theorem utf8Kept_body : ∀ i ∈ utf8ForBody.instrs, i.dst? ∉ utf8Kept.map some := by decide

theorem utf8Kept_then : ∀ i ∈ utf8ThenUs.instrs, i.dst? ∉ utf8Kept.map some := by decide

theorem utf8Kept_us : ∀ i ∈ utf8ForBodyUs.instrs, i.dst? ∉ utf8Kept.map some := by decide

theorem utf8Kept_end : ∀ i ∈ utf8EndUs.instrs, i.dst? ∉ utf8Kept.map some := by decide

/-- A decided proposition's `ofBool` is one, at the carrier `i1`. -/
theorem ofBool_of_true {p : Prop} [Decidable p] (h : p) : (BitVec.ofBool p : BitVec 1) = 1 := by
  simp [h]

/-- A refuted proposition's `ofBool` is zero. -/
theorem ofBool_of_false {p : Prop} [Decidable p] (h : ¬ p) : (BitVec.ofBool p : BitVec 1) = 0 := by
  simp [h]

/-- A conditional branch on a true bit jumps to the taken block. -/
theorem execTerm_condbr_true {s : State} {c : Operand} {t f : String} {bit : BitVec 1}
    (h : evalOperand s c = some (.int 1 bit)) (hb : bit = 1) :
    execTerm s (.condbr c t f) = .jump { s with pc := t, pre := some s.pc } := by
  simp only [execTerm, h]
  rw [hb]
  simp

/-- A conditional branch on a zero bit jumps to the untaken block. -/
theorem execTerm_condbr_false {s : State} {c : Operand} {t f : String} {bit : BitVec 1}
    (h : evalOperand s c = some (.int 1 bit)) (hb : bit = 0) :
    execTerm s (.condbr c t f) = .jump { s with pc := f, pre := some s.pc } := by
  simp only [execTerm, h]
  rw [hb]
  simp

/-! ### The body's stream, sliced -/

/-- The bytes block `i` reads from: the window from the three carry bytes before
the block to the end of its sixty-four. -/
def utf8Stream (bs : List UInt8) (n nb i : Nat) : List UInt8 :=
  (utf8Window bs n nb).drop (64 * i)

theorem body_stream (l : List UInt8) :
    l.take 3 ++ (l.drop 3).take 64 = l.take 67 :=
  take_append_take_len l 3 64

theorem take67_drop (l : List UInt8) (c m : Nat) (h : c + m ≤ 67) :
    ((l.take 67).drop c).take m = (l.drop c).take m := by
  rw [drop_take', List.take_take, Nat.min_eq_left (Nat.le_sub_of_add_le' h)]

/-- The slice the body's `hL` hypothesis names, read as the stream's own bytes. -/
theorem stream_slice (bs : List UInt8) (n nb i c m : Nat) (h : c + m ≤ 67) :
    (((utf8Stream bs n nb i).take 3 ++ ((utf8Stream bs n nb i).drop 3).take 64).drop c).take m
      = ((utf8Stream bs n nb i).drop c).take m := by
  rw [body_stream]
  exact take67_drop _ c m h

/-- `klErrVec` depends only on the stream's bytes. -/
theorem klErrVec_eq_of_getD (s t : List UInt8) (h : ∀ k, k < 35 → klByte s k = klByte t k) :
    klErrVec s = klErrVec t := by
  unfold klErrVec
  apply List.map_congr_left
  intro k hk
  have hk32 : k < 32 := by simpa using hk
  have ha : k + 1 < 33 := Nat.add_lt_add_right hk32 1
  have hb : k + 2 < 34 := Nat.add_lt_add_right ha 1
  have hc : k + 3 < 35 := Nat.add_lt_add_right hb 1
  have h35 : k < 35 := Nat.lt_of_lt_of_le hk32 (by decide)
  have h36 : k + 1 < 35 := Nat.lt_of_lt_of_le ha (by decide)
  have h37 : k + 2 < 35 := Nat.lt_of_lt_of_le hb (by decide)
  have h38 : k + 3 < 35 := hc
  rw [h k h35, h (k + 1) h36, h (k + 2) h37, h (k + 3) h38]

/-- A thirty-five byte slice of the padded window and of the unpadded one read
the same error vector: the padding is zero, which `getD` already answers. -/
theorem klErrVec_slice_window (bs : List UInt8) (n nb m : Nat) :
    klErrVec (((utf8Window bs n nb).drop m).take 35)
      = klErrVec (((0x00 :: 0x00 :: 0x00 :: bs).drop m).take 35) := by
  apply klErrVec_eq_of_getD
  intro k hk
  rw [klByte_take_drop _ m 35 k hk, klByte_take_drop _ m 35 k hk, klByte_window]

/-- A block's error vector is the same in the padded window and the unpadded
one: the block's sixty-four bytes and its three carry bytes are the same bytes,
with the padding zero past the end. -/
theorem klErrBlk_window (bs : List UInt8) (n nb i : Nat) :
    klErrBlk (klPre (utf8Window bs n nb) i) (klBlk (utf8Window bs n nb) i)
      = klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) i)
          (klBlk (0x00 :: 0x00 :: 0x00 :: bs) i) := by
  have hP : klErrBlk (klPre (utf8Window bs n nb) i) (klBlk (utf8Window bs n nb) i)
      = List.zipWith (· ||| ·) (klErrVec (((utf8Window bs n nb).drop (64 * i)).take 35))
          (klErrVec (((utf8Window bs n nb).drop (64 * i + 32)).take 35)) := by
    unfold klErrBlk klPre klBlk klErr32
    rw [block_arg_hi (utf8Window bs n nb) (64 * i)]
    rw [block_arg_lo (utf8Window bs n nb) (64 * i)]
  have hW : klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) i)
        (klBlk (0x00 :: 0x00 :: 0x00 :: bs) i)
      = List.zipWith (· ||| ·)
          (klErrVec (((0x00 :: 0x00 :: 0x00 :: bs).drop (64 * i)).take 35))
          (klErrVec (((0x00 :: 0x00 :: 0x00 :: bs).drop (64 * i + 32)).take 35)) := by
    unfold klErrBlk klPre klBlk klErr32
    rw [block_arg_hi (0x00 :: 0x00 :: 0x00 :: bs) (64 * i)]
    rw [block_arg_lo (0x00 :: 0x00 :: 0x00 :: bs) (64 * i)]
  rw [hP, hW, klErrVec_slice_window bs n nb (64 * i),
    klErrVec_slice_window bs n nb (64 * i + 32)]

/-- One thirty-two byte read of the body, at the eight slice offsets the block
uses, in the address form the block's own instructions carry. -/
theorem win_read_slice (mem : Mem) (b nb : Nat) (W : List UInt8) (i c : Nat)
    (hw : readBytes mem (b - 3) (3 + 64 * nb) = some W) (hb : 3 ≤ b)
    (hc : c + 32 ≤ 67) (hj : 64 * i + c + 32 ≤ 3 + 64 * nb) :
    readBytes mem (b + 64 * i + c - 3) 32
      = some (((W.drop (64 * i)).drop c).take 32) := by
  have h := win_read mem b nb (64 * i + c) W hw hb (by omega)
  rw [show b - 3 + (64 * i + c) = b + 64 * i + c - 3 from by omega] at h
  rw [show List.drop (64 * i + c) W = List.drop c (List.drop (64 * i) W) from by
    rw [List.drop_drop]] at h
  exact h


/-! ### The block's error vector at the body's own slices, and the fold's step

The two facts both loops need at every block, stated once beside the slices they
name: the body's `pre ++ blk` slices read the specification's `klErrBlk` for the
block, and one block's contribution turns `klAcc`'s `i`-th step into its
`i + 1`-th. -/

/-- Block `i`'s error vector at the slices the body's own loads supply. -/
def utf8BlkErr (bs : List UInt8) (n nb i : Nat) : List UInt8 :=
  klErrBlk (List.take 3 (utf8Stream bs n nb i))
    (List.take 64 (List.drop 3 (utf8Stream bs n nb i)))

/-- One step of the accumulator fold. -/
def klAccStep (bs : List UInt8) (i : Nat) : List UInt8 :=
  List.zipWith (· ||| ·) (klAcc bs i)
    (klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) i)
      (klBlk (0x00 :: 0x00 :: 0x00 :: bs) i))

theorem klAcc_step (bs : List UInt8) (i : Nat) : klAcc bs (i + 1) = klAccStep bs i :=
  klAcc_succ bs i

/-- The body's slices read the block's `klErrBlk`. -/
theorem utf8BlkErr_eq (bs : List UInt8) (n nb i : Nat) :
    utf8BlkErr bs n nb i
      = klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) i)
          (klBlk (0x00 :: 0x00 :: 0x00 :: bs) i) := by
  unfold utf8BlkErr
  have h1 : List.take 3 (utf8Stream bs n nb i) = klPre (utf8Window bs n nb) i := by
    rw [klPre, utf8Stream]
  have h2 : List.take 64 (List.drop 3 (utf8Stream bs n nb i))
      = klBlk (utf8Window bs n nb) i := by
    rw [klBlk, utf8Stream, List.drop_drop]
  rw [h1, h2, klErrBlk_window]

/-- **One block's contribution.**  Or-ing the block's error vector into the
accumulator advances the fold by one block: this is the step both loop lemmas
conclude with. -/
theorem klAccStep_pack (bs : List UInt8) (n nb i : Nat) :
    packLanes (unpackLanes 64 4 (bytesToNat
        (List.zipWith (· ||| ·) (klAcc bs i) (utf8BlkErr bs n nb i))))
      = bytesToNat (klAcc bs (i + 1)) := by
  have hlen : (List.zipWith (· ||| ·) (klAcc bs i) (utf8BlkErr bs n nb i)).length = 32 := by
    rw [List.length_zipWith, klAcc_length, utf8BlkErr, klErrBlk_length, Nat.min_self]
  have hlt := bytesToNat_lt (List.zipWith (· ||| ·) (klAcc bs i) (utf8BlkErr bs n nb i))
  rw [hlen, show (256 : Nat) ^ 32 = 2 ^ 256 from by decide] at hlt
  rw [packLanes_unpackLanes, show (4 * 64) = 256 from by decide, Nat.mod_eq_of_lt hlt,
    klAcc_step, klAccStep, ← utf8BlkErr_eq]

/-! ### The ungated loop, one block at a time -/

/-- Taking `for.body`'s blocks one at a time.  The invariant is the folded word —
`packLanes u8k = bytesToNat (klAcc bs i)` — and the block's own error vector is
`klErrBlk` at the window's three carry bytes and its sixty-four, so the step is
`klAcc_succ`.  The conclusion is the run's own equality at a symbolic fuel: the
`r` blocks cost exactly `r` control steps, and any continuation `k` runs from the
state the loop leaves. -/
theorem utf8Ungated_loop_run (bs : List UInt8) (n nb b : Nat) (mem : Mem)
    (hnb : nb = (bs.length + 63) / 64)
    (hw : readBytes mem (b - 3) (3 + 64 * nb) = some (utf8Window bs n nb))
    (hb : 3 ≤ b) (hspan : 64 * (nb - 1) < 2 ^ 63) :
    ∀ (r i : Nat) (env : Env) (s : State) (p : String) (opA opB : Operand)
      (u8k : List (BitVec 64)),
      1 ≤ r → i + r = nb → s.pc = "for.body" → s.pre = some p → s.mem = mem →
      phiIncoming p [("for.body", .reg "%or.i47"),
        ("for.body.lr.ph", .imm (.splat 4 64 (BitVec.ofInt 64 0)))] = some opA →
      phiIncoming p [("for.body", .reg "%inc"),
        ("for.body.lr.ph", .imm (.int 64 (BitVec.ofInt 64 0)))] = some opB →
      evalOperand (withEnv env s) opA = some (.vec 4 64 u8k) →
      evalOperand (withEnv (("%u8k.076", .vec 4 64 u8k) :: env) s) opB
        = some (.int 64 (BitVec.ofNat 64 i)) →
      lookupName env "%b" = some (.ptr b) →
      lookupName env "%div44" = some (.int 64 (BitVec.ofNat 64 nb)) →
      lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)) →
      u8k.length = 4 → packLanes u8k = bytesToNat (klAcc bs i) →
      ∃ (env' : Env) (s' : State) (u8k' : List (BitVec 64)),
        s'.pc = "for.cond.cleanup" ∧ s'.pre = some "for.body" ∧ s'.mem = mem ∧
        lookupName env' "%or.i47" = some (.vec 4 64 u8k') ∧ u8k'.length = 4 ∧
        packLanes u8k' = bytesToNat (klAcc bs nb) ∧
        lookupName env' "%b" = some (.ptr b) ∧
        lookupName env' "%n" = some (.int 64 (BitVec.ofNat 64 n)) ∧
        lookupName env' "%div44" = some (.int 64 (BitVec.ofNat 64 nb)) ∧
        ∀ (k : Nat), runFuel utf8Calls (r + k) utf8Function (withEnv env s)
          = runFuel utf8Calls k utf8Function (withEnv env' s') := by
  intro r
  induction r with
  | zero => intro i env s p opA opB u8k hr _; omega
  | succ r' ih =>
      intro i env s p opA opB u8k hr hi hpc hpre hmem hincA hincB hopA hopB hb' hdiv hn
        hu8klen hu8kpack
      have hinb : i < nb := by omega
      have hi64 : 64 * i < 2 ^ 63 := by
        have h1 : i ≤ nb - 1 := by omega
        have h2 := Nat.mul_le_mul_left 64 h1
        omega
      have hWlen : (utf8Window bs n nb).length = 3 + 64 * nb :=
        readBytes_length mem (b - 3) (3 + 64 * nb) hw
      -- the eight reads and the eight slice identities
      have read37 : readBytes s.mem (b + 64 * i + 3 - 3) 32
          = some (((utf8Stream bs n nb i).drop 3).take 32) := by
        rw [hmem]; exact win_read_slice mem b nb _ i 3 hw hb (by omega) (by omega)
      have read38 : readBytes s.mem (b + 64 * i + 35 - 3) 32
          = some (((utf8Stream bs n nb i).drop 35).take 32) := by
        rw [hmem]; exact win_read_slice mem b nb _ i 35 hw hb (by omega) (by omega)
      have read39 : readBytes s.mem (b + 64 * i + 2 - 3) 32
          = some (((utf8Stream bs n nb i).drop 2).take 32) := by
        rw [hmem]; exact win_read_slice mem b nb _ i 2 hw hb (by omega) (by omega)
      have read40 : readBytes s.mem (b + 64 * i + 1 - 3) 32
          = some (((utf8Stream bs n nb i).drop 1).take 32) := by
        rw [hmem]; exact win_read_slice mem b nb _ i 1 hw hb (by omega) (by omega)
      have read41 : readBytes s.mem (b + 64 * i + 0 - 3) 32
          = some (((utf8Stream bs n nb i).drop 0).take 32) := by
        rw [hmem]; exact win_read_slice mem b nb _ i 0 hw hb (by omega) (by omega)
      have read54 : readBytes s.mem (b + 64 * i + 34 - 3) 32
          = some (((utf8Stream bs n nb i).drop 34).take 32) := by
        rw [hmem]; exact win_read_slice mem b nb _ i 34 hw hb (by omega) (by omega)
      have read55 : readBytes s.mem (b + 64 * i + 33 - 3) 32
          = some (((utf8Stream bs n nb i).drop 33).take 32) := by
        rw [hmem]; exact win_read_slice mem b nb _ i 33 hw hb (by omega) (by omega)
      have read56 : readBytes s.mem (b + 64 * i + 32 - 3) 32
          = some (((utf8Stream bs n nb i).drop 32).take 32) := by
        rw [hmem]; exact win_read_slice mem b nb _ i 32 hw hb (by omega) (by omega)
      have upper : ∀ c : Nat, c + 32 ≤ 35 →
          (((((utf8Stream bs n nb i).take 3 ++ ((utf8Stream bs n nb i).drop 3).take 64).drop 32).drop c).take 32)
            = ((utf8Stream bs n nb i).drop (32 + c)).take 32 := by
        intro c hc
        rw [List.drop_drop, stream_slice bs n nb i (32 + c) 32 (by omega)]
      have slice37 := stream_slice bs n nb i 3 32 (by omega)
      have slice38 := upper 3 (by omega)
      have slice39 := stream_slice bs n nb i 2 32 (by omega)
      have slice40 := stream_slice bs n nb i 1 32 (by omega)
      have slice41 := stream_slice bs n nb i 0 32 (by omega)
      have slice54 := upper 2 (by omega)
      have slice55 := upper 1 (by omega)
      have slice56 := upper 0 (by omega)
      have hstream67 : 67 ≤ (utf8Stream bs n nb i).length := by
        rw [utf8Stream, List.length_drop, hWlen]; omega
      obtain ⟨env'', hrunB, hval, hinc, hexit⟩ :=
        utf8Ungated_body env s b nb i (klAcc bs i)
          ((utf8Stream bs n nb i).take 3) (((utf8Stream bs n nb i).drop 3).take 64) u8k
          (((utf8Stream bs n nb i).drop 3).take 32) (((utf8Stream bs n nb i).drop 35).take 32)
          (((utf8Stream bs n nb i).drop 2).take 32) (((utf8Stream bs n nb i).drop 1).take 32)
          (((utf8Stream bs n nb i).drop 0).take 32) (((utf8Stream bs n nb i).drop 34).take 32)
          (((utf8Stream bs n nb i).drop 33).take 32) (((utf8Stream bs n nb i).drop 32).take 32)
          p opA opB hpre hincA hincB hopA hopB hb' hdiv
          (klAcc_length bs i) hu8klen (by simp; omega) (by simp; omega) hu8kpack
          slice37.symm slice38.symm slice39.symm slice40.symm slice41.symm
          slice54.symm slice55.symm slice56.symm
          read37 read38 read39 read40 read41 read54 read55 read56 hb hi64
      have hframe := fun (nm : String) (hm : nm ∈ utf8Kept) =>
        denoteCode_kept utf8ForBody.instrs env env'' s hrunB utf8Kept_body nm hm
      have hstep : step utf8Calls utf8Function (withEnv env s)
          = execTerm (withEnv env'' s)
              (.condbr (.reg "%exitcond.not") "for.cond.cleanup" "for.body") :=
        step_of_utf8 _ "for.body" utf8ForBody (withEnv env'' s) hpc findBlock_utf8ForBody hrunB
      have hexit' : evalOperand (withEnv env'' s) (.reg "%exitcond.not")
          = some (.int 1 (BitVec.ofBool
              (BitVec.ofNat 64 i + BitVec.ofInt 64 1 = BitVec.ofNat 64 nb))) := by
        simpa only [withEnv, evalOperand] using hexit
      have hone : (BitVec.ofInt 64 1 : BitVec 64) = BitVec.ofNat 64 1 := by decide
      have hnext : BitVec.ofNat 64 i + BitVec.ofInt 64 1 = BitVec.ofNat 64 (i + 1) := by
        rw [hone, ofNat64_add_ofNat i 1 (by omega)]
      by_cases hlast : i + 1 = nb
      · -- the loop is done: the test leaves for `for.cond.cleanup`
        have hbit : BitVec.ofNat 64 i + BitVec.ofInt 64 1 = BitVec.ofNat 64 nb := by
          rw [hnext, hlast]
        have hjump : step utf8Calls utf8Function (withEnv env s) = .jump
            ({ (withEnv env'' s) with pc := "for.cond.cleanup", pre := some "for.body" } : State) := by
          rw [hstep, execTerm_condbr_true hexit' (ofBool_of_true hbit),
            show (withEnv env'' s).pc = "for.body" from by rw [withEnv]; exact hpc]
        have hpack : packLanes (unpackLanes 64 4 (bytesToNat (List.zipWith (· ||| ·) (klAcc bs i)
            (utf8BlkErr bs n nb i)))) = bytesToNat (klAcc bs nb) := by
          rw [klAccStep_pack, hlast]
        have hr0 : r' = 0 := by omega
        refine ⟨env'', ({ (withEnv env'' s) with pc := "for.cond.cleanup", pre := some "for.body" } : State), _, rfl, rfl, hmem, hval, ?_, hpack, ?_, ?_, ?_, ?_⟩
        · rw [unpackLanes_length]
        · exact (hframe "%b" (by decide)).trans hb'
        · exact (hframe "%n" (by decide)).trans hn
        · exact (hframe "%div44" (by decide)).trans hdiv
        · intro k
          rw [show (r' + 1) + k = k + 1 from by omega, runFuel_jump_utf8 hjump]
          rfl
      · -- the loop continues at the next block
        have hlt : i + 1 < nb := by omega
        have hbit : BitVec.ofNat 64 i + BitVec.ofInt 64 1 ≠ BitVec.ofNat 64 nb := by
          intro hc
          rw [hnext] at hc
          exact hlast (ofNat64_inj (by omega) (by omega) hc)
        have hjump : step utf8Calls utf8Function (withEnv env s) = .jump
            ({ (withEnv env'' s) with pc := "for.body", pre := some "for.body" } : State) := by
          rw [hstep, execTerm_condbr_false hexit' (ofBool_of_false hbit),
            show (withEnv env'' s).pc = "for.body" from by rw [withEnv]; exact hpc]
        have hr' : 1 ≤ r' := by omega
        obtain ⟨env3, s3, u8k3, hpc3, hpre3, hmem3, hval3, hlen3, hpack3, hb3, hn3, hdiv3,
          hrun3⟩ :=
          ih (i + 1) env'' { (withEnv env'' s) with pc := "for.body", pre := some "for.body" }
            "for.body" (.reg "%or.i47") (.reg "%inc")
            (unpackLanes 64 4 (bytesToNat (List.zipWith (· ||| ·) (klAcc bs i)
              (klErrBlk (List.take 3 (utf8Stream bs n nb i))
                (List.take 64 (List.drop 3 (utf8Stream bs n nb i)))))))
            hr' (by omega) rfl rfl hmem rfl rfl
            (evalOperand_reg_of env'' _ "%or.i47" _ hval)
            (by
              rw [evalOperand_reg_of _ _ "%inc" _
                ((lookupName_cons_ne _ _ (by decide)).trans hinc), hnext])
            ((hframe "%b" (by decide)).trans hb')
            ((hframe "%div44" (by decide)).trans hdiv)
            ((hframe "%n" (by decide)).trans hn)
            (by rw [unpackLanes_length])
            (klAccStep_pack bs n nb i)
        refine ⟨env3, s3, u8k3, hpc3, hpre3, hmem3, hval3, hlen3, hpack3, hb3, hn3, hdiv3,
          ?_⟩
        intro k
        rw [show (r' + 1) + k = (r' + k) + 1 from by omega, runFuel_jump_utf8 hjump,
          show r' + k = r' + k from rfl]
        exact hrun3 k


/-! ### The gate's reading of its own test -/

theorem bytesToNat_eq_zero_iff (l : List UInt8) :
    bytesToNat l = 0 ↔ ∀ x ∈ l, x = 0 := by
  induction l with
  | nil => simp [bytesToNat]
  | cons b bs ih =>
      show b.toNat + 256 * bytesToNat bs = 0 ↔ ∀ x ∈ b :: bs, x = 0
      have hmul : 256 * bytesToNat bs = 0 ↔ bytesToNat bs = 0 := by
        constructor
        · intro h
          rcases Nat.mul_eq_zero.mp h with h1 | h1
          · omega
          · exact h1
        · intro h; rw [h, Nat.mul_zero]
      rw [Nat.add_eq_zero_iff, hmul, ih, List.forall_mem_cons]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨UInt8.toNat_inj.mp ?_, h2⟩
        simpa using h1
      · rintro ⟨h1, h2⟩
        exact ⟨by rw [h1]; rfl, h2⟩

theorem u8_and_high_lt (y : UInt8) : (y &&& 0x80) = 0 ↔ y.toNat < 0x80 := by
  have h := and80_eq_zero_iff_lt y.toBitVec
  rw [← UInt8.toBitVec_inj, UInt8.toBitVec_and,
    show (0x80 : UInt8).toBitVec = (0x80 : BitVec 8) from by decide,
    show (0 : UInt8).toBitVec = (0 : BitVec 8) from rfl]
  rw [h, UInt8.toNat_toBitVec]

theorem u8_or_lt (a b : UInt8) :
    (a ||| b).toNat < 0x80 ↔ a.toNat < 0x80 ∧ b.toNat < 0x80 := by
  have h := or_high a.toBitVec b.toBitVec
  rw [← UInt8.toBitVec_or, UInt8.toNat_toBitVec] at h
  constructor
  · intro hlt
    have hna : ¬ ((0x80 : Nat) ≤ a.toNat ∨ (0x80 : Nat) ≤ b.toNat) := by
      rintro (hc | hc)
      · exact absurd (h.mpr (Or.inl hc)) (Nat.not_le.mpr hlt)
      · exact absurd (h.mpr (Or.inr hc)) (Nat.not_le.mpr hlt)
    exact ⟨Nat.lt_of_not_le (fun hc => hna (Or.inl hc)),
      Nat.lt_of_not_le (fun hc => hna (Or.inr hc))⟩
  · rintro ⟨h1, h2⟩
    have hna : ¬ ((0x80 : Nat) ≤ a.toNat ∨ (0x80 : Nat) ≤ b.toNat) := by
      rintro (hc | hc)
      · exact absurd hc (Nat.not_le.mpr h1)
      · exact absurd hc (Nat.not_le.mpr h2)
    have hn : ¬ (0x80 : Nat) ≤ (a ||| b).toNat := fun hP => hna (h.mp hP)
    exact Nat.lt_of_not_le hn

theorem byteLanes_zipWith_and_toBitVec (l₁ l₂ : List UInt8) :
    (List.zipWith (· &&& ·) l₁ l₂).map UInt8.toBitVec
      = List.zipWith (· &&& ·) (l₁.map UInt8.toBitVec) (l₂.map UInt8.toBitVec) := by
  induction l₁ generalizing l₂ with
  | nil => rfl
  | cons x xs ih =>
      cases l₂ with
      | nil => rfl
      | cons y ys =>
          simp only [List.zipWith_cons_cons, List.map_cons]
          rw [UInt8.toBitVec_and, ih]

theorem byteLanes_zipWith_and (l₁ l₂ : List UInt8) :
    byteLanes (List.zipWith (· &&& ·) l₁ l₂)
      = List.zipWith (· &&& ·) (byteLanes l₁) (byteLanes l₂) := by
  simpa [byteLanes] using byteLanes_zipWith_and_toBitVec l₁ l₂

theorem bytesToNat_zipWith_and (a b : List UInt8) (h : a.length = b.length) :
    bytesToNat (List.zipWith (· &&& ·) a b) = bytesToNat a &&& bytesToNat b := by
  rw [← packLanes_byteLanes, byteLanes_zipWith_and,
    packLanes_zipWith_and (by rw [byteLanes_length, byteLanes_length, h]),
    packLanes_byteLanes, packLanes_byteLanes]

theorem packLanes_highLanes64 :
    packLanes highLanes64 = bytesToNat (List.replicate 32 (0x80 : UInt8)) := by
  have hlt : packLanes highLanes64 < 2 ^ 256 := by
    have h := packLanes_lt highLanes64
    rw [show (highLanes64.length * 64) = 256 from by simp [highLanes64],
      show (256 : Nat) = 2 ^ 8 from by decide] at h
    exact h
  have e1 : packLanes highLanes64
      = packLanes (unpackLanes 8 32 (packLanes highLanes64)) := by
    rw [packLanes_unpackLanes, show (32 * 8) = 256 from by decide, Nat.mod_eq_of_lt hlt]
  have hbyte : byteLanes (List.replicate 32 (0x80 : UInt8))
      = List.replicate 32 (BitVec.ofInt 8 0x80) := by
    unfold byteLanes
    rw [List.map_replicate, show UInt8.toNat (0x80 : UInt8) = 128 from by decide,
      show (BitVec.ofNat 8 128 : BitVec 8) = BitVec.ofInt 8 128 from by decide]
  rw [e1,
    show unpackLanes 8 32 (packLanes highLanes64)
      = List.replicate 32 (BitVec.ofInt 8 0x80) from highLanes64_bytes,
    ← packLanes_byteLanes, hbyte]

/-- The gate's packed word: the two halves' bytes or-ed, packed at the
accumulator's lane width. -/
def utf8GateWord (B0 B1 : List UInt8) : Nat :=
  packLanes (List.zipWith (· ||| ·) (unpackLanes 64 4 (bytesToNat B1))
    (unpackLanes 64 4 (bytesToNat B0)))

theorem utf8GateWord_eq (B0 B1 : List UInt8) (h0 : B0.length = 32) (h1 : B1.length = 32) :
    utf8GateWord B0 B1 = bytesToNat (List.zipWith (· ||| ·) B1 B0) := by
  have hV0 : bytesToNat B0 < 2 ^ 256 := by
    have h := bytesToNat_lt B0
    rwa [h0, show (256 : Nat) ^ 32 = 2 ^ 256 from by decide] at h
  have hV1 : bytesToNat B1 < 2 ^ 256 := by
    have h := bytesToNat_lt B1
    rwa [h1, show (256 : Nat) ^ 32 = 2 ^ 256 from by decide] at h
  unfold utf8GateWord
  rw [packLanes_zipWith_or (by rw [unpackLanes_length, unpackLanes_length]),
    packLanes_unpackLanes, packLanes_unpackLanes,
    show (4 * 64) = 256 from by decide,
    Nat.mod_eq_of_lt hV1, Nat.mod_eq_of_lt hV0,
    ← bytesToNat_zipWith_or B1 B0 (by rw [h1, h0])]

/-- **The gate's reading**: a block whose packed halves test clear against the
high-bit mask has every byte below `0x80`.  The `ptestz` answers one exactly on a
cleared and-word, the mask's own packed word is `0x80` in every byte, and the
`&&&` distributes over the byte list, so the test is "every byte's bit 7 is
clear". -/
theorem ascii_of_ptestz (B0 B1 : List UInt8) (h0 : B0.length = 32) (h1 : B1.length = 32)
    (h : ptestz (BitVec.ofNat 256 (utf8GateWord B0 B1))
        (BitVec.ofNat 256 (packLanes highLanes64)) = 1) :
    ∀ b ∈ B0 ++ B1, b.toNat < 0x80 := by
  have hWlt : utf8GateWord B0 B1 < 2 ^ 256 := by
    unfold utf8GateWord
    have h := packLanes_lt (List.zipWith (· ||| ·) (unpackLanes 64 4 (bytesToNat B1))
      (unpackLanes 64 4 (bytesToNat B0)))
    rw [List.length_zipWith, unpackLanes_length, unpackLanes_length, Nat.min_self,
      show (64 * 4) = 256 from by decide] at h
    exact h
  have hMlt : packLanes highLanes64 < 2 ^ 256 := by
    have h := packLanes_lt highLanes64
    rw [show (highLanes64.length * 64) = 256 from by simp [highLanes64],
      show (256 : Nat) = 2 ^ 8 from by decide] at h
    exact h
  have hp := (ptestz_eq_one_iff _ _).mp h
  have hz1 : ((BitVec.ofNat 256 (utf8GateWord B0 B1))
      &&& (BitVec.ofNat 256 (packLanes highLanes64))).toNat = 0 := by
    rw [hp]
    rfl
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hWlt, Nat.mod_eq_of_lt hMlt, utf8GateWord_eq B0 B1 h0 h1,
    packLanes_highLanes64,
    ← bytesToNat_zipWith_and _ _
      (by rw [List.length_zipWith, h1, h0, Nat.min_self]; simp),
    bytesToNat_eq_zero_iff] at hz1
  have key : ∀ (k : Nat) (hk : k < 32),
      (B0.get ⟨k, by rw [h0]; exact hk⟩).toNat < 0x80 ∧
      (B1.get ⟨k, by rw [h1]; exact hk⟩).toNat < 0x80 := by
    intro k hk
    have hc : (List.zipWith (· ||| ·) B1 B0).length = 32 := by
      rw [List.length_zipWith, h1, h0, Nat.min_self]
    have hlen : (List.zipWith (· &&& ·) (List.zipWith (· ||| ·) B1 B0)
        (List.replicate 32 (0x80 : UInt8))).length = 32 := by
      rw [List.length_zipWith]
      simp [hc]
    have hget : (List.zipWith (· &&& ·) (List.zipWith (· ||| ·) B1 B0)
        (List.replicate 32 (0x80 : UInt8)))[k]'(by rw [hlen]; exact hk) = 0 := by
      have := hz1 _ (List.getElem_mem (by rw [hlen]; exact hk))
      simpa using this
    simp only [List.getElem_zipWith, List.getElem_replicate] at hget
    rw [u8_and_high_lt, u8_or_lt] at hget
    exact ⟨hget.2, hget.1⟩
  intro b hb
  rw [List.mem_append] at hb
  rcases hb with hb | hb
  · obtain ⟨k, hk, hbk⟩ := List.mem_iff_getElem.mp hb
    rw [← hbk]
    exact (key k (by rw [h0] at hk; exact hk)).1
  · obtain ⟨k, hk, hbk⟩ := List.mem_iff_getElem.mp hb
    rw [← hbk]
    exact (key k (by rw [h1] at hk; exact hk)).2



/-! ### The span bound the loop's address arithmetic needs

`le_mul_div_sixtyfour` (`JsonUtf8IR`) bounds a length by its own block count;
this is the same fact read the other way, and the bound the loop's and the tail's
`getelementptr` indices need.  It is a lemma rather than a loop hypothesis
because the headline does **not** state it: it follows from `haddr` and `hpos`. -/

/-- `64 * ((n + 63) / 64) ≤ n + 63`: the block count times sixty-four does not
exceed the length rounded up. -/
theorem sixtyfour_mul_div_le (n : Nat) : 64 * ((n + 63) / 64) ≤ n + 63 := by
  rw [Nat.mul_comm]
  exact Nat.div_mul_le_self (n + 63) 64

/-- **The span bound.**  Under the block count's definition, the address bound
`n < 2 ^ 63` and `0 < n`, the last block's index is legal:
`64 * (nb - 1) < 2 ^ 63`.  This is what the loop lemmas take as their span
hypothesis, discharged here rather than assumed. -/
theorem utf8SpanBound (n nb : Nat) (hnb : nb = (n + 63) / 64) (haddr : n < 2 ^ 63)
    (hpos : 0 < n) : 64 * (nb - 1) < 2 ^ 63 := by
  have hle : 64 * nb ≤ n + 63 := by
    rw [hnb]
    exact sixtyfour_mul_div_le n
  have hnb1 : 1 ≤ nb := by
    rw [hnb]
    exact Nat.div_pos
      (Nat.le_trans (by decide : 64 ≤ 1 + 63) (Nat.add_le_add_right (Nat.succ_le_of_lt hpos) 63))
      (by decide)
  have hmul : 64 * (nb - 1) + 64 = 64 * nb := by
    have h1 : 64 * (nb - 1) = 64 * nb - 64 := by
      rw [Nat.mul_sub_left_distrib 64 nb 1, Nat.mul_one]
    rw [h1, Nat.sub_add_cancel (by simpa using Nat.mul_le_mul_left 64 hnb1)]
  refine (Nat.add_lt_add_iff_right (k := 64)).mp ?_
  have h3 : 64 * (nb - 1) + 64 ≤ n + 63 := by rw [hmul]; exact hle
  have h4 : n + 63 < 2 ^ 63 + 64 :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_right haddr 63)
      (Nat.add_le_add_left (by decide : 63 ≤ 64) _)
  exact Nat.lt_of_le_of_lt h3 h4

/-! ### The gate's own `i1` test -/

theorem ofBool_eq_one_iff {p : Prop} [Decidable p] :
    (BitVec.ofBool p : BitVec 1) = 1 ↔ p := by
  rw [show (BitVec.ofBool p : BitVec 1) = BitVec.ofBool (decide p) from rfl]
  cases hp : decide p with
  | false =>
      rw [BitVec.ofBool_false]
      refine ⟨fun h => absurd h (by decide), fun h => ?_⟩
      rw [decide_eq_true h] at hp
      exact absurd hp (by decide)
  | true =>
      rw [BitVec.ofBool_true]
      exact ⟨fun _ => of_decide_eq_true hp, fun _ => rfl⟩

theorem bit1_and_eq_one (a b : BitVec 1) : a &&& b = 1 ↔ a = 1 ∧ b = 1 := by
  have ha : a.toNat < 2 := a.isLt
  have hb : b.toNat < 2 := b.isLt
  constructor
  · intro h
    have h1 : (a &&& b).toNat = 1 := by rw [h]; rfl
    rw [BitVec.toNat_and] at h1
    have ha1 : a.toNat = 1 := by
      by_cases h0 : a.toNat = 0
      · rw [h0] at h1; simp at h1
      · omega
    have hb1 : b.toNat = 1 := by
      by_cases h0 : b.toNat = 0
      · rw [h0] at h1; simp at h1
      · omega
    exact ⟨BitVec.toNat_inj.mp (by rw [ha1]; rfl), BitVec.toNat_inj.mp (by rw [hb1]; rfl)⟩
  · rintro ⟨rfl, rfl⟩
    decide

theorem bit1_eq_zero_of_ne_one (a : BitVec 1) (h : a ≠ 1) : a = 0 := by
  have ha : a.toNat < 2 := a.isLt
  have h1 : a.toNat ≠ 1 := fun hc => h (BitVec.toNat_inj.mp (by rw [hc]; rfl))
  exact BitVec.toNat_inj.mp (by
    have : a.toNat = 0 := by omega
    rw [this]; rfl)

theorem ptestz_eq_one_or_zero (a b : BitVec 256) :
    BitLanes.ptestz a b = 0 ∨ BitLanes.ptestz a b = 1 := by
  unfold BitLanes.ptestz
  split <;> simp

/-- A `ptestz` that is not zero is one. -/
theorem ptestz_eq_one_of_ne_zero (a b : BitVec 256) (h : BitLanes.ptestz a b ≠ 0) :
    BitLanes.ptestz a b = 1 := by
  rcases ptestz_eq_one_or_zero a b with h0 | h1
  · exact absurd h0 h
  · exact h1

/-- The gate's own test at one block: `%or.cond.us` — the block's bytes are
ASCII and the block before it was. -/
def utf8GateBit (B0 B1 : List UInt8) (prev : BitVec 32) : BitVec 1 :=
  BitVec.ofBool (ptestz (BitVec.ofNat 256 (utf8GateWord B0 B1))
    (BitVec.ofNat 256 (packLanes highLanes64)) ≠ BitVec.ofInt 32 0) &&&
  BitVec.ofBool (prev ≠ BitVec.ofInt 32 0)

/-- **The gate's condition, read at the body's own test**: a taken skip means the
block's sixty-four bytes are ASCII and the block before it was. -/
theorem orcond_one_imp (B0 B1 : List UInt8) (prev : BitVec 32)
    (h0 : B0.length = 32) (h1 : B1.length = 32) (hp01 : prev = 0 ∨ prev = 1)
    (h : (BitVec.ofBool (ptestz (BitVec.ofNat 256 (utf8GateWord B0 B1))
          (BitVec.ofNat 256 (packLanes highLanes64)) ≠ 0) &&&
        BitVec.ofBool (prev ≠ 0) : BitVec 1) = 1) :
    (∀ b ∈ B0 ++ B1, b.toNat < 0x80) ∧ prev = 1 := by
  rw [bit1_and_eq_one, ofBool_eq_one_iff, ofBool_eq_one_iff] at h
  refine ⟨ascii_of_ptestz B0 B1 h0 h1 (ptestz_eq_one_of_ne_zero _ _ h.1), ?_⟩
  rcases hp01 with hq | hq
  · exact absurd hq h.2
  · exact hq

/-- The block's own `%2` reads the gate: one means every byte is below `0x80`. -/
theorem ptestz_ascii (B0 B1 : List UInt8) (h0 : B0.length = 32) (h1 : B1.length = 32)
    (h : ptestz (BitVec.ofNat 256 (utf8GateWord B0 B1))
        (BitVec.ofNat 256 (packLanes highLanes64)) = 1) :
    ∀ b ∈ B0 ++ B1, b.toNat < 0x80 :=
  ascii_of_ptestz B0 B1 h0 h1 h


/-- **The preheader edge.**  Entered from `for.body.lr.ph`, the ungated loop's two
phis select the constant operands — the zero lane list and `i64 0` — so
`utf8Ungated_body` is instantiated there with the constants, and at the latch with
`%or.i47`/`%inc`.  The two facts below are what a caller at that edge supplies. -/
theorem utf8Ungated_preheader_operands (s : State) :
    evalOperand s (.imm (.splat 4 64 (BitVec.ofInt 64 0)))
        = some (.vec 4 64 (unpackLanes 64 4 0)) ∧
      evalOperand s (.imm (.int 64 (BitVec.ofInt 64 0)))
        = some (.int 64 (BitVec.ofNat 64 0)) := by
  constructor <;> rfl

end LeanLLVM.Refinement.JsonUtf8Steps

namespace LeanLLVM.Refinement.JsonUtf8Steps

open LeanLLVM
open LeanLLVM.Refinement.JsonUtf8IR
open LeanLLVM.Refinement.JsonUtf8Spec
open LeanLLVM.Refinement.BitLanes
open LeanLLVM.Refinement.JsonEntrySteps
open LeanLLVM.Refinement.JsonS1MasksIR
  (evalInstr_load)

/-! ### What an unreadable byte does

`utf8StageUndefinedStatement` says that a byte the body cannot read makes the
run `ub`.  Two facts carry it, and neither is the run: the window's unreadable
position has a **least** one, which fixes the block a run first reaches with a
bad byte; and that block's header loads are the instructions that refuse, so its
`denoteCode` is `none`.

The staging clauses are what make the first fact a statement about a document
byte: the three prefix bytes and the padding are stated readable, so the least
position lies in `[3, 3 + n)` and names a block below the block count. -/

/-- A range that contains an unreadable byte has a least one, with every earlier
position readable.  The witness is the induction's own — no well-founded choice
enters, which is why the proof is by cases on the head rather than `Nat.find`. -/
theorem exists_least_unreadable (m : Mem) (p n : Nat)
    (h : ∃ k, k < n ∧ readByte m (p + k) = none) :
    ∃ k, k < n ∧ readByte m (p + k) = none ∧
      ∀ j, j < k → readByte m (p + j) ≠ none := by
  induction n generalizing p with
  | zero =>
      obtain ⟨k, hk, _⟩ := h
      exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
      obtain ⟨k, hk, hnone⟩ := h
      cases k with
      | zero => exact ⟨0, Nat.succ_pos n, by simpa using hnone, by omega⟩
      | succ j =>
          have hj : j < n := by omega
          have htail : readByte m (p + 1 + j) = none := by
            rw [show p + 1 + j = p + (j + 1) from by omega]
            exact hnone
          cases hp : readByte m p with
          | none => exact ⟨0, Nat.succ_pos n, hp, by omega⟩
          | some b =>
              obtain ⟨k', hk', hnone', hleast⟩ := ih (p + 1) ⟨j, hj, htail⟩
              refine ⟨k' + 1, by omega, ?_, ?_⟩
              · rw [show p + (k' + 1) = p + 1 + k' from by omega]
                exact hnone'
              · intro j' hj'
                cases j' with
                | zero =>
                    rw [Nat.add_zero]
                    intro hcon
                    rw [hp] at hcon
                    cases hcon
                | succ j'' =>
                    have hlt : j'' < k' := by omega
                    rw [show p + (j'' + 1) = p + 1 + j'' from by omega]
                    exact hleast j'' hlt

/-- **The least unreadable block.**  An unreadable position in the staged window
is a document byte, and its block index is below the block count; every byte of
every earlier block is readable, which is what lets the run reach this block. -/
theorem utf8_least_unreadable_block (mem : Mem) (b n nb w : Nat)
    (hb : 3 ≤ b)
    (hnb : nb = (n + 63) / 64)
    (hpre : ∀ k, k < 3 → readByte mem (b - 3 + k) = some 0x00)
    (hpad : ∀ k, n ≤ k → k < 64 * nb → readByte mem (b + k) = some 0x00)
    (hw : w < 3 + 64 * nb)
    (hbad : readByte mem (b - 3 + w) = none) :
    ∃ i j, i < nb ∧ j < 64 ∧ readByte mem (b + 64 * i + j) = none ∧
      ∀ i' j', i' < i → j' < 64 → readByte mem (b + 64 * i' + j') ≠ none := by
  obtain ⟨k, hk, hnone, hleast⟩ :=
    exists_least_unreadable mem (b - 3) (3 + 64 * nb) ⟨w, hw, hbad⟩
  have hk3 : 3 ≤ k := by
    refine Nat.le_of_not_lt (fun hlt => ?_)
    have hsome := hpre k hlt
    rw [hsome] at hnone
    cases hnone
  have hkend : k < 3 + n := by
    refine Nat.lt_of_not_le (fun hge => ?_)
    have hsome := hpad (k - 3) (by omega) (by omega)
    rw [show b + (k - 3) = b - 3 + k from by omega] at hsome
    rw [hsome] at hnone
    cases hnone
  refine ⟨(k - 3) / 64, (k - 3) % 64, ?_, ?_, ?_, ?_⟩
  · have h1 : k - 3 < n := by omega
    have h2 : n ≤ 64 * nb := by
      rw [hnb]
      exact JsonUtf8IR.le_mul_div_sixtyfour n
    exact div_lt_of_lt_mul' (by omega)
  · exact Nat.mod_lt _ (by decide)
  · rw [Nat.add_assoc, Nat.div_add_mod]
    rw [show b + (k - 3) = b - 3 + k from by omega]
    exact hnone
  · intro i' j' hi' hj'
    have hlt : 3 + 64 * i' + j' < k := by
      have hdiv : i' + 1 ≤ (k - 3) / 64 := by omega
      have hmul : (i' + 1) * 64 ≤ ((k - 3) / 64) * 64 := Nat.mul_le_mul_right 64 hdiv
      have hle : ((k - 3) / 64) * 64 ≤ k - 3 := Nat.div_mul_le_self (k - 3) 64
      omega
    have haddr : b + 64 * i' + j' = b - 3 + (3 + 64 * i' + j') := by omega
    rw [haddr]
    exact hleast (3 + 64 * i' + j') hlt

/-- A block all of whose sixty-four bytes are readable supplies the two
thirty-two-byte header loads: the halves the gate's own test reads. -/
theorem utf8_block_two_reads (mem : Mem) (b i : Nat)
    (h : ∀ j, j < 64 → readByte mem (b + 64 * i + j) ≠ none) :
    (∃ B0, readBytes mem (b + 64 * i) 32 = some B0) ∧
      ∃ B1, readBytes mem (b + 64 * i + 32) 32 = some B1 := by
  constructor
  · exact exists_readBytes_of_readable mem (b + 64 * i) 32
      (fun k hk => h k (by omega))
  · refine exists_readBytes_of_readable mem (b + 64 * i + 32) 32
      (fun k hk => ?_)
    rw [show b + 64 * i + 32 + k = b + 64 * i + (32 + k) from by omega]
    exact h (32 + k) (by omega)

/-- **`for.body.us` refuses the step when its block is unreadable.**  The three
phis, the shift and the address run; whichever half holds the bad byte, the
header load that reads it is `none`, so the block's `denoteCode` is `none`. -/
theorem utf8ForBodyUs_denote_none (env : Env) (s : State) (p : String)
    (opP opU opB : Operand) (b bi : Nat) (prev : BitVec 32) (u8kIn : List (BitVec 64))
    (hpre : s.pre = some p)
    (hincP : phiIncoming p [("if.end14.us", .reg "%2"),
      ("for.body.lr.ph", .imm (.int 32 (BitVec.ofInt 32 1)))] = some opP)
    (hincU : phiIncoming p [("if.end14.us", .reg "%u8k.2.us"),
      ("for.body.lr.ph", .imm (.splat 4 64 (BitVec.ofInt 64 0)))] = some opU)
    (hincB : phiIncoming p [("if.end14.us", .reg "%inc.us"),
      ("for.body.lr.ph", .imm (.int 64 (BitVec.ofInt 64 0)))] = some opB)
    (hopP : evalOperand (withEnv env s) opP = some (.int 32 prev))
    (hopU : evalOperand (withEnv (("%prev_ascii.077.us", .int 32 prev) :: env) s) opU
      = some (.vec 4 64 u8kIn))
    (hopB : evalOperand (withEnv (("%u8k.076.us", .vec 4 64 u8kIn) ::
      ("%prev_ascii.077.us", .int 32 prev) :: env) s) opB
      = some (.int 64 (BitVec.ofNat 64 bi)))
    (hb : lookupName env "%b" = some (.ptr b))
    (hbad : ∃ j, j < 64 ∧ readByte s.mem (b + 64 * bi + j) = none)
    (hbi64 : 64 * bi < 2 ^ 63) :
    denoteCode utf8Calls utf8ForBodyUs.instrs (withEnv env s) = none := by
  simp only [utf8ForBodyUs, reg, lit, splatOf, highBitMask, JsonUtf8IR.ptestz]
  ent_step (utf8_phi env s "%prev_ascii.077.us" (.int 32)
    [("if.end14.us", .reg "%2"), ("for.body.lr.ph", .imm (.int 32 (BitVec.ofInt 32 1)))]
    p opP (.int 32 prev) hpre hincP hopP)
  ent_step (utf8_phi (("%prev_ascii.077.us", .int 32 prev) :: env) s "%u8k.076.us" v4i64
    [("if.end14.us", .reg "%u8k.2.us"),
      ("for.body.lr.ph", .imm (.splat 4 64 (BitVec.ofInt 64 0)))]
    p opU (.vec 4 64 u8kIn) hpre hincU hopU)
  ent_step (utf8_phi (("%u8k.076.us", .vec 4 64 u8kIn) ::
    ("%prev_ascii.077.us", .int 32 prev) :: env) s "%bi.075.us" (.int 64)
    [("if.end14.us", .reg "%inc.us"), ("for.body.lr.ph", .imm (.int 64 (BitVec.ofInt 64 0)))]
    p opB (.int 64 (BitVec.ofNat 64 bi)) hpre hincB hopB)
  ent_step (utf8_step_shl _ _ "%shl.us" "%bi.075.us" 64 (BitVec.ofNat 64 bi)
    (BitVec.ofInt 64 6) (by ent_auto))
  rw [shl64_six bi (by omega)]
  ent_step (utf8_step_gep _ _ "%add.ptr.us" "%b" "%shl.us" (.int 8) b
    (BitVec.ofNat 64 (64 * bi)) (by ent_auto) (by ent_auto)
    (by rw [toNat_ofNat64 (64 * bi) (by omega)]; exact hbi64))
  rw [show b + (BitVec.ofNat 64 (64 * bi)).toNat * (Ty.int 8).sizeBytes = b + 64 * bi from by
    rw [toNat_ofNat64 (64 * bi) (by omega), sizeBytes_i8, Nat.mul_one]]
  obtain ⟨j, hj, hnone⟩ := hbad
  by_cases hj32 : j < 32
  · have hr : readBytes s.mem (b + 64 * bi) 32 = none :=
      readBytes_eq_none_of_readByte_none s.mem hnone (by omega) (by omega)
    exact denoteCode_cons_none _ _ _ _
      (evalInstr_load_none (p := .reg "%add.ptr.us") (hp := by ent_auto)
        (hv := loadValue_vec_int_of_readBytes_none (by decide) (by decide) hr))
  · cases hr : readBytes s.mem (b + 64 * bi) 32 with
    | none =>
        exact denoteCode_cons_none _ _ _ _
          (evalInstr_load_none (p := .reg "%add.ptr.us") (hp := by ent_auto)
            (hv := loadValue_vec_int_of_readBytes_none (by decide) (by decide) hr))
    | some B0 =>
        have hl0 : B0.length = 32 := readBytes_length s.mem (b + 64 * bi) 32 hr
        have hV : B0 = natToBytes (bytesToNat B0) 32 :=
          (natToBytes_bytesToNat B0).symm.trans (by rw [hl0])
        have hlt : bytesToNat B0 < 2 ^ 256 := by
          have h1 := bytesToNat_lt B0
          rwa [hl0, show (256 : Nat) ^ 32 = 2 ^ 256 from by decide] at h1
        ent_step (step_load4_64 _ _ "%0" "%add.ptr.us" (b + 64 * bi) (bytesToNat B0)
          (by ent_auto) (by rw [← hV]; exact hr) hlt)
        ent_step (utf8_step_gep_imm _ _ "%add.ptr3.us" "%add.ptr.us" (.int 8) (b + 64 * bi)
          (BitVec.ofInt 64 32) (by ent_auto) (by decide))
        rw [show b + 64 * bi + (BitVec.ofInt 64 32).toNat * (Ty.int 8).sizeBytes
          = b + 64 * bi + 32 from by
          rw [show (BitVec.ofInt 64 32).toNat = 32 from by decide, sizeBytes_i8]]
        have hr1 : readBytes s.mem (b + 64 * bi + 32) 32 = none :=
          readBytes_eq_none_of_readByte_none s.mem hnone (by omega) (by omega)
        exact denoteCode_cons_none _ _ _ _
          (evalInstr_load_none (p := .reg "%add.ptr3.us") (hp := by ent_auto)
            (hv := loadValue_vec_int_of_readBytes_none (by decide) (by decide) hr1))

/-- **`for.body` refuses the step when its block is unreadable**, by the same two
header loads at the `<16 x i16>` shape the ungated path reads. -/
theorem utf8ForBody_denote_none (env : Env) (s : State) (b bi : Nat)
    (u8k : List (BitVec 64)) (p : String) (opA opB : Operand)
    (hpre : s.pre = some p)
    (hincA : phiIncoming p [("for.body", .reg "%or.i47"),
      ("for.body.lr.ph", .imm (.splat 4 64 (BitVec.ofInt 64 0)))] = some opA)
    (hincB : phiIncoming p [("for.body", .reg "%inc"),
      ("for.body.lr.ph", .imm (.int 64 (BitVec.ofInt 64 0)))] = some opB)
    (hopA : evalOperand (withEnv env s) opA = some (.vec 4 64 u8k))
    (hopB : evalOperand (withEnv (("%u8k.076", .vec 4 64 u8k) :: env) s) opB
      = some (.int 64 (BitVec.ofNat 64 bi)))
    (hb : lookupName env "%b" = some (.ptr b))
    (hbad : ∃ j, j < 64 ∧ readByte s.mem (b + 64 * bi + j) = none)
    (hbi64 : 64 * bi < 2 ^ 63) :
    denoteCode utf8Calls utf8ForBody.instrs (withEnv env s) = none := by
  simp only [utf8ForBody, reg, lit, splatOf, lanesOf, highBitMask, JsonUtf8IR.pshufb,
    JsonUtf8IR.usubSat]
  ent_step (utf8_phi env s "%u8k.076" v4i64 _ p opA (.vec 4 64 u8k) hpre hincA hopA)
  ent_step (utf8_phi (("%u8k.076", .vec 4 64 u8k) :: env) s "%bi.075" (.int 64) _ p opB
    (.int 64 (BitVec.ofNat 64 bi)) hpre hincB hopB)
  ent_step (utf8_step_shl _ _ "%shl" "%bi.075" 64 (BitVec.ofNat 64 bi) (BitVec.ofInt 64 6)
    (by ent_auto))
  rw [shl64_six bi (by omega)]
  ent_step (utf8_step_gep _ _ "%add.ptr" "%b" "%shl" (.int 8) b (BitVec.ofNat 64 (64 * bi))
    (by ent_auto) (by ent_auto) (by rw [toNat_ofNat64 (64 * bi) (by omega)]; exact hbi64))
  rw [show b + (BitVec.ofNat 64 (64 * bi)).toNat * (Ty.int 8).sizeBytes = b + 64 * bi from by
    rw [toNat_ofNat64 (64 * bi) (by omega), sizeBytes_i8, Nat.mul_one]]
  obtain ⟨j, hj, hnone⟩ := hbad
  by_cases hj32 : j < 32
  · have hr : readBytes s.mem (b + 64 * bi) 32 = none :=
      readBytes_eq_none_of_readByte_none s.mem hnone (by omega) (by omega)
    exact denoteCode_cons_none _ _ _ _
      (evalInstr_load_none (p := .reg "%add.ptr") (hp := by ent_auto)
        (hv := loadValue_vec_int_of_readBytes_none (by decide) (by decide) hr))
  · cases hr : readBytes s.mem (b + 64 * bi) 32 with
    | none =>
        exact denoteCode_cons_none _ _ _ _
          (evalInstr_load_none (p := .reg "%add.ptr") (hp := by ent_auto)
            (hv := loadValue_vec_int_of_readBytes_none (by decide) (by decide) hr))
    | some B0 =>
        have hl0 : B0.length = 32 := readBytes_length s.mem (b + 64 * bi) 32 hr
        have hV : B0 = natToBytes (bytesToNat B0) 32 :=
          (natToBytes_bytesToNat B0).symm.trans (by rw [hl0])
        have hlt : bytesToNat B0 < 2 ^ 256 := by
          have h1 := bytesToNat_lt B0
          rwa [hl0, show (256 : Nat) ^ 32 = 2 ^ 256 from by decide] at h1
        ent_step (step_load16_16 _ _ "%37" "%add.ptr" (b + 64 * bi) (bytesToNat B0)
          (by ent_auto) (by rw [← hV]; exact hr) hlt)
        ent_step (utf8_step_gep_imm _ _ "%add.ptr3" "%add.ptr" (.int 8) (b + 64 * bi)
          (BitVec.ofInt 64 32) (by ent_auto) (by decide))
        rw [show b + 64 * bi + (BitVec.ofInt 64 32).toNat * (Ty.int 8).sizeBytes
          = b + 64 * bi + 32 from by
          rw [show (BitVec.ofInt 64 32).toNat = 32 from by decide, sizeBytes_i8]]
        have hr1 : readBytes s.mem (b + 64 * bi + 32) 32 = none :=
          readBytes_eq_none_of_readByte_none s.mem hnone (by omega) (by omega)
        exact denoteCode_cons_none _ _ _ _
          (evalInstr_load_none (p := .reg "%add.ptr3") (hp := by ent_auto)
            (hv := loadValue_vec_int_of_readBytes_none (by decide) (by decide) hr1))

/-- A block whose instructions refuse makes the step `ub`; the run reads that as
`ub` at any positive fuel (`runFuel_ub_utf8`).  Stated once here so the block
facts above meet the stepping surface at one place. -/
theorem step_ub_utf8 (s : State) (name : String) (b : Block)
    (hpc : s.pc = name) (hfind : utf8Function.findBlock name = some b)
    (hbody : denoteCode utf8Calls b.instrs s = none) :
    step utf8Calls utf8Function s = .ub := by
  simp [step, hpc, hfind, hbody]

end LeanLLVM.Refinement.JsonUtf8Steps
namespace LeanLLVM.Refinement.JsonUtf8Steps
open LeanLLVM
open LeanLLVM.Refinement.JsonUtf8IR
open LeanLLVM.Refinement.JsonUtf8Spec
open LeanLLVM.Refinement.BitLanes
open LeanLLVM.Refinement.JsonEntrySteps

/-! ### The gated loop, one block at a time

`for.body.us` is the header: three phis carry `%prev_ascii`, the accumulator and
the block index in, the block's two `<4 x i64>` halves are loaded, and
`%or.cond.us` is the gate — the block's bytes are ASCII and the block before it
was.  A taken gate jumps straight to the latch, so a skipped block costs two
control steps; an untaken gate runs `if.then11.us` first, so an evaluated block
costs three.  The fuel is therefore a bound `t ≤ 3 * r` with the run's equality
at every continuation, and it is the two branches' count that makes it an
existential rather than the ungated lemma's one step per block. -/

/-- A block's sixty-four bytes are its two thirty-two byte halves. -/
theorem blk_split (l : List UInt8) :
    (l.drop 3).take 64 = (l.drop 3).take 32 ++ (l.drop 35).take 32 := by
  rw [show (64 : Nat) = 32 + 32 from rfl,
    ← take_append_take_len (l.drop 3) 32 32, List.drop_drop]

/-- The latch does not write `%2`, so the next header's gate phi reads the bit
the previous header's `ptestz` produced. -/
theorem latch_keeps_two (env env' : Env) (s : State)
    (hrun : denoteCode utf8Calls utf8EndUs.instrs (withEnv env s) = some (withEnv env' s)) :
    lookupName env' "%2" = lookupName env "%2" :=
  denoteCode_lookupName utf8Calls utf8EndUs.instrs "%2" (by decide) _ _ hrun

/-- A name a block does not write survives its run, stated at the environment
rather than at the state's projection, so it composes with `Eq.trans`. -/
theorem denoteCode_lookupName_of_not_dst (instrs : List Instr) (env env' : Env) (s : State)
    (n : String) (hn : ∀ i ∈ instrs, i.dst? ≠ some n)
    (hrun : denoteCode utf8Calls instrs (withEnv env s) = some (withEnv env' s)) :
    lookupName env' n = lookupName env n :=
  denoteCode_lookupName utf8Calls instrs n hn (withEnv env s) (withEnv env' s) hrun

/-- A jump target written as an update of `withEnv env s` is a `withEnv` of the
updated state, so the block lemmas chain without unwrapping the environment. -/
theorem withEnv_setJmp (env : Env) (s : State) (pc : String) (pre : Option String) :
    ({ (withEnv env s) with pc := pc, pre := pre })
      = withEnv env { s with pc := pc, pre := pre } := rfl

/-- A register operand under `withEnv` reads the environment's cell. -/
theorem evalOperand_reg_withEnv (env : Env) (s : State) (n : String) :
    evalOperand (withEnv env s) (.reg n) = lookupName env n := rfl

/-- The emission's lane order does not change the packed word: the outer `|||`s
associate and commute lane by lane, so the gated body's
`(%lower ||| %upper) ||| u8k` packs to the natural the accumulator step is stated
at, which is the ungated body's `(%lower ||| u8k) ||| %upper`. -/
theorem packLanes_zipWith_or_reorder (A B u8k : List (BitVec 64))
    (hAB : A.length = B.length) (hBu : B.length = u8k.length) :
    packLanes (List.zipWith (· ||| ·) (List.zipWith (· ||| ·) A B) u8k)
      = packLanes (List.zipWith (· ||| ·) (List.zipWith (· ||| ·) A u8k) B) := by
  have hAu : A.length = u8k.length := hAB.trans hBu
  have hABu : (List.zipWith (· ||| ·) A B).length = u8k.length := by
    rw [List.length_zipWith, hAB, Nat.min_self, hBu]
  have hAuu : (List.zipWith (· ||| ·) A u8k).length = B.length := by
    rw [List.length_zipWith, hAu, Nat.min_self, hBu.symm]
  rw [packLanes_zipWith_or (a := List.zipWith (· ||| ·) A B) (b := u8k) hABu,
    packLanes_zipWith_or (a := A) (b := B) hAB,
    packLanes_zipWith_or (a := List.zipWith (· ||| ·) A u8k) (b := B) hAuu,
    packLanes_zipWith_or (a := A) (b := u8k) hAu,
    Nat.or_assoc, Nat.or_assoc, Nat.or_comm (packLanes B) (packLanes u8k)]

/-- Taking `for.body.us`'s blocks one at a time.  The invariant is the ungated
lemma's folded word — `packLanes u8k = bytesToNat (klAcc bs i)` — carried beside
the gate's own `prev_ascii`.  A skipped block runs the header and the latch, an
evaluated one runs the header, the DFA body and the latch, so the fuel is a bound
`t ≤ 3 * r` and the conclusion is an existential with the run's equality at every
continuation.  A skipped block contributes nothing to the fold
(`utf8Skip_eq_zero`); an evaluated one contributes its `klErrBlk`, read at the
emission's own `|||` order (`errRawBlk_word_eq`, reordered once per iteration). -/
theorem utf8Gated_loop_run (bs : List UInt8) (n nb b : Nat) (mem : Mem)
    (hnb : nb = (bs.length + 63) / 64)
    (hw : readBytes mem (b - 3) (3 + 64 * nb) = some (utf8Window bs n nb))
    (hb : 3 ≤ b) (hspan : 64 * (nb - 1) < 2 ^ 63) :
    ∀ (r i : Nat) (env : Env) (s : State) (p : String) (opP opU opB : Operand)
      (u8k : List (BitVec 64)) (prev : BitVec 32),
      1 ≤ r → i + r = nb → s.pc = "for.body.us" → s.pre = some p → s.mem = mem →
      phiIncoming p [("if.end14.us", .reg "%2"),
        ("for.body.lr.ph", .imm (.int 32 (BitVec.ofInt 32 1)))] = some opP →
      phiIncoming p [("if.end14.us", .reg "%u8k.2.us"),
        ("for.body.lr.ph", .imm (.splat 4 64 (BitVec.ofInt 64 0)))] = some opU →
      phiIncoming p [("if.end14.us", .reg "%inc.us"),
        ("for.body.lr.ph", .imm (.int 64 (BitVec.ofInt 64 0)))] = some opB →
      evalOperand (withEnv env s) opP = some (.int 32 prev) →
      evalOperand (withEnv (("%prev_ascii.077.us", .int 32 prev) :: env) s) opU
        = some (.vec 4 64 u8k) →
      evalOperand (withEnv (("%u8k.076.us", .vec 4 64 u8k) ::
        ("%prev_ascii.077.us", .int 32 prev) :: env) s) opB
        = some (.int 64 (BitVec.ofNat 64 i)) →
      lookupName env "%b" = some (.ptr b) →
      lookupName env "%div44" = some (.int 64 (BitVec.ofNat 64 nb)) →
      lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)) →
      u8k.length = 4 → packLanes u8k = bytesToNat (klAcc bs i) →
      (prev = 0 ∨ prev = 1) →
      (prev = 1 → ∀ b' ∈ klPre (utf8Window bs n nb) i, b'.toNat < 0x80) →
      ∃ (env' : Env) (s' : State) (u8k' : List (BitVec 64)) (t : Nat),
        s'.pc = "for.cond.cleanup" ∧ s'.pre = some "if.end14.us" ∧ s'.mem = mem ∧
        t ≤ 3 * r ∧
        lookupName env' "%u8k.2.us" = some (.vec 4 64 u8k') ∧ u8k'.length = 4 ∧
        packLanes u8k' = bytesToNat (klAcc bs nb) ∧
        lookupName env' "%b" = some (.ptr b) ∧
        lookupName env' "%n" = some (.int 64 (BitVec.ofNat 64 n)) ∧
        lookupName env' "%div44" = some (.int 64 (BitVec.ofNat 64 nb)) ∧
        ∀ (k : Nat), runFuel utf8Calls (t + k) utf8Function (withEnv env s)
          = runFuel utf8Calls k utf8Function (withEnv env' s') := by
  intro r
  induction r with
  | zero =>
      intro i env s p opP opU opB u8k prev hr _
      omega
  | succ r' ih =>
      intro i env s p opP opU opB u8k prev hr hi hpc hpre hmem hincP hincU hincB hopP hopU
        hopB hb' hdiv hn hu8klen hu8kpack hp01 hpAscii
      have hinb : i < nb := by omega
      have hi64 : 64 * i < 2 ^ 63 := by
        have h1 : i ≤ nb - 1 := by omega
        have h2 := Nat.mul_le_mul_left 64 h1
        omega
      have hWlen : (utf8Window bs n nb).length = 3 + 64 * nb :=
        readBytes_length mem (b - 3) (3 + 64 * nb) hw
      have hstreamLen : (utf8Stream bs n nb i).length = 3 + 64 * nb - 64 * i := by
        rw [utf8Stream, List.length_drop, hWlen]
      let S := utf8Stream bs n nb i
      have hSlen : S.length = 3 + 64 * nb - 64 * i := hstreamLen
      -- the eight reads the header and the DFA body take
      have read0 : readBytes s.mem (b + 64 * i) 32 = some ((S.drop 3).take 32) := by
        rw [hmem]
        have h := win_read_slice mem b nb (utf8Window bs n nb) i 3 hw hb (by omega) (by omega)
        rwa [show b + 64 * i + 3 - 3 = b + 64 * i from by omega] at h
      have read1 : readBytes s.mem (b + 64 * i + 32) 32 = some ((S.drop 35).take 32) := by
        rw [hmem]
        have h := win_read_slice mem b nb (utf8Window bs n nb) i 35 hw hb (by omega) (by omega)
        rwa [show b + 64 * i + 35 - 3 = b + 64 * i + 32 from by omega] at h
      have read3 : readBytes s.mem (b + 64 * i - 1) 32 = some ((S.drop 2).take 32) := by
        rw [hmem]
        have h := win_read_slice mem b nb (utf8Window bs n nb) i 2 hw hb (by omega) (by omega)
        rwa [show b + 64 * i + 2 - 3 = b + 64 * i - 1 from by omega] at h
      have read4 : readBytes s.mem (b + 64 * i - 2) 32 = some ((S.drop 1).take 32) := by
        rw [hmem]
        have h := win_read_slice mem b nb (utf8Window bs n nb) i 1 hw hb (by omega) (by omega)
        rwa [show b + 64 * i + 1 - 3 = b + 64 * i - 2 from by omega] at h
      have read5 : readBytes s.mem (b + 64 * i - 3) 32 = some (S.take 32) := by
        rw [hmem]
        have h := win_read_slice mem b nb (utf8Window bs n nb) i 0 hw hb (by omega) (by omega)
        rwa [show b + 64 * i + 0 - 3 = b + 64 * i - 3 from by omega] at h
      have read19 : readBytes s.mem (b + 64 * i + 31) 32 = some ((S.drop 34).take 32) := by
        rw [hmem]
        have h := win_read_slice mem b nb (utf8Window bs n nb) i 34 hw hb (by omega) (by omega)
        rwa [show b + 64 * i + 34 - 3 = b + 64 * i + 31 from by omega] at h
      have read20 : readBytes s.mem (b + 64 * i + 30) 32 = some ((S.drop 33).take 32) := by
        rw [hmem]
        have h := win_read_slice mem b nb (utf8Window bs n nb) i 33 hw hb (by omega) (by omega)
        rwa [show b + 64 * i + 33 - 3 = b + 64 * i + 30 from by omega] at h
      have read21 : readBytes s.mem (b + 64 * i + 29) 32 = some ((S.drop 32).take 32) := by
        rw [hmem]
        have h := win_read_slice mem b nb (utf8Window bs n nb) i 32 hw hb (by omega) (by omega)
        rwa [show b + 64 * i + 32 - 3 = b + 64 * i + 29 from by omega] at h
      -- their lengths, and the two halves' word bounds
      have hlenB0 : ((S.drop 3).take 32).length = 32 := by
        rw [List.length_take, List.length_drop, hSlen]; exact Nat.min_eq_left (by omega)
      have hlenB1 : ((S.drop 35).take 32).length = 32 := by
        rw [List.length_take, List.length_drop, hSlen]; exact Nat.min_eq_left (by omega)
      have hlen2 : ((S.drop 2).take 32).length = 32 := by
        rw [List.length_take, List.length_drop, hSlen]; exact Nat.min_eq_left (by omega)
      have hlen1 : ((S.drop 1).take 32).length = 32 := by
        rw [List.length_take, List.length_drop, hSlen]; exact Nat.min_eq_left (by omega)
      have hlen0 : (S.take 32).length = 32 := by
        rw [List.length_take, hSlen]; exact Nat.min_eq_left (by omega)
      have hlen34 : ((S.drop 34).take 32).length = 32 := by
        rw [List.length_take, List.length_drop, hSlen]; exact Nat.min_eq_left (by omega)
      have hlen33 : ((S.drop 33).take 32).length = 32 := by
        rw [List.length_take, List.length_drop, hSlen]; exact Nat.min_eq_left (by omega)
      have hlen32 : ((S.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop, hSlen]; exact Nat.min_eq_left (by omega)
      have hV0 : bytesToNat ((S.drop 3).take 32) < 2 ^ 256 := by
        have h := bytesToNat_lt ((S.drop 3).take 32)
        rwa [hlenB0, show (256 : Nat) ^ 32 = 2 ^ 256 from by decide] at h
      have hV1 : bytesToNat ((S.drop 35).take 32) < 2 ^ 256 := by
        have h := bytesToNat_lt ((S.drop 35).take 32)
        rwa [hlenB1, show (256 : Nat) ^ 32 = 2 ^ 256 from by decide] at h
      -- the header
      obtain ⟨env1, hrun1, hP1, hU1, hB1, hptr1, h01, h11, h21, hcond1⟩ :=
        utf8ForBodyUs_run env s p opP opU opB b i prev u8k ((S.drop 3).take 32)
          ((S.drop 35).take 32) hpre hincP hincU hincB hopP hopU hopB hb' read0 read1 hi64
      have hframe := fun (nm : String) (hm : nm ∈ utf8Kept) =>
        denoteCode_kept utf8ForBodyUs.instrs env env1 s hrun1 utf8Kept_us nm hm
      have hdiv1 : lookupName env1 "%div44" = some (.int 64 (BitVec.ofNat 64 nb)) :=
        (hframe "%div44" (by decide)).trans hdiv
      have hb1 : lookupName env1 "%b" = some (.ptr b) := (hframe "%b" (by decide)).trans hb'
      have hn1 : lookupName env1 "%n" = some (.int 64 (BitVec.ofNat 64 n)) :=
        (hframe "%n" (by decide)).trans hn
      have hstep1 : step utf8Calls utf8Function (withEnv env s)
          = execTerm (withEnv env1 s)
              (.condbr (.reg "%or.cond.us") "if.end14.us" "if.then11.us") :=
        step_of_utf8 _ "for.body.us" utf8ForBodyUs (withEnv env1 s) hpc findBlock_utf8ForBodyUs hrun1
      have hev1 : evalOperand (withEnv env1 s) (.reg "%or.cond.us")
          = some (.int 1 (utf8GateBit ((S.drop 3).take 32) ((S.drop 35).take 32) prev)) := by
        rw [evalOperand_reg_withEnv]
        exact hcond1
      have hpc1 : (withEnv env1 s).pc = "for.body.us" := hpc
      -- the block's own bytes, and the next block's `prev_ascii`
      have hklBlk : klBlk (utf8Window bs n nb) i
          = (S.drop 3).take 32 ++ (S.drop 35).take 32 := by
        unfold klBlk
        rw [show (utf8Window bs n nb).drop (64 * i + 3) = S.drop 3 from by
          show (utf8Window bs n nb).drop (64 * i + 3) = (utf8Stream bs n nb i).drop 3
          rw [utf8Stream, List.drop_drop]]
        exact blk_split S
      have hp01' : ptestz (BitVec.ofNat 256 (utf8GateWord ((S.drop 3).take 32)
            ((S.drop 35).take 32))) (BitVec.ofNat 256 (packLanes highLanes64)) = 0 ∨
          ptestz (BitVec.ofNat 256 (utf8GateWord ((S.drop 3).take 32)
            ((S.drop 35).take 32))) (BitVec.ofNat 256 (packLanes highLanes64)) = 1 :=
        ptestz_eq_one_or_zero _ _
      have hpAscii' : ptestz (BitVec.ofNat 256 (utf8GateWord ((S.drop 3).take 32)
            ((S.drop 35).take 32))) (BitVec.ofNat 256 (packLanes highLanes64)) = 1 →
          ∀ b' ∈ klPre (utf8Window bs n nb) (i + 1), b'.toNat < 0x80 := by
        intro h2 b' hb'
        rw [klPre_succ] at hb'
        have hblk : ∀ x ∈ klBlk (utf8Window bs n nb) i, x.toNat < 0x80 := by
          intro x hx
          rw [hklBlk] at hx
          exact ptestz_ascii _ _ hlenB0 hlenB1 h2 x hx
        exact ascii_drop hblk 61 b' hb'
      have hnext : BitVec.ofNat 64 i + BitVec.ofInt 64 1 = BitVec.ofNat 64 (i + 1) := by
        rw [show (BitVec.ofInt 64 1 : BitVec 64) = BitVec.ofNat 64 1 from by decide,
          ofNat64_add_ofNat i 1 (by omega)]
      by_cases hskip : utf8GateBit ((S.drop 3).take 32) ((S.drop 35).take 32) prev = 1
      · -- the gate skips: the block contributes nothing to the fold
        obtain ⟨hblkAscii, hprev1⟩ :=
          orcond_one_imp ((S.drop 3).take 32) ((S.drop 35).take 32) prev hlenB0 hlenB1 hp01
            (by simpa [utf8GateBit] using hskip)
        have hjump1 : step utf8Calls utf8Function (withEnv env s)
            = .jump (withEnv env1 { s with pc := "if.end14.us", pre := some "for.body.us" }) := by
          have h := hstep1
          rw [execTerm_condbr_true hev1 hskip, withEnv_setJmp, hpc1] at h
          exact h
        have hzero : klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) i)
            (klBlk (0x00 :: 0x00 :: 0x00 :: bs) i) = List.replicate 32 0x00 := by
          rw [← klErrBlk_window bs n nb i]
          refine utf8Skip_eq_zero _ _ (hpAscii hprev1) ?_
          intro x hx
          rw [hklBlk] at hx
          exact hblkAscii x hx
        have haccEq : klAcc bs (i + 1) = klAcc bs i := by
          rw [klAcc_step, klAccStep, hzero,
            zipWith_zero_right (· ||| ·) (0 : UInt8) (klAcc bs i) (fun x => by rw [UInt8.or_zero])
              (klAcc_length bs i)]
        obtain ⟨env2, hrun2, hU2, hI2, hE2⟩ :=
          utf8EndUs_run env1 { s with pc := "if.end14.us", pre := some "for.body.us" }
            "for.body.us" (.reg "%u8k.076.us") u8k i nb rfl rfl
            (by rw [evalOperand_reg_withEnv]; exact hU1) hB1 hdiv1
        have hstep2 : step utf8Calls utf8Function
            (withEnv env1 { s with pc := "if.end14.us", pre := some "for.body.us" })
            = execTerm (withEnv env2 { s with pc := "if.end14.us", pre := some "for.body.us" })
                (.condbr (.reg "%exitcond79.not") "for.cond.cleanup" "for.body.us") :=
          step_of_utf8 _ "if.end14.us" utf8EndUs _ rfl findBlock_utf8EndUs hrun2
        have hev2 : evalOperand
            (withEnv env2 { s with pc := "if.end14.us", pre := some "for.body.us" })
            (.reg "%exitcond79.not")
            = some (.int 1 (BitVec.ofBool
                (BitVec.ofNat 64 i + BitVec.ofInt 64 1 = BitVec.ofNat 64 nb))) := by
          rw [evalOperand_reg_withEnv]
          exact hE2
        have hframe2 := fun (nm : String) (hm : nm ∈ utf8Kept) =>
          denoteCode_kept utf8EndUs.instrs env1 env2
            { s with pc := "if.end14.us", pre := some "for.body.us" } hrun2 utf8Kept_end nm hm
        by_cases hlast : i + 1 = nb
        · -- the loop is done: the latch's test leaves for `for.cond.cleanup`
          have hbit : BitVec.ofNat 64 i + BitVec.ofInt 64 1 = BitVec.ofNat 64 nb := by
            rw [hnext, hlast]
          have hjump2 : step utf8Calls utf8Function
              (withEnv env1 { s with pc := "if.end14.us", pre := some "for.body.us" })
              = .jump (withEnv env2
                  { s with pc := "for.cond.cleanup", pre := some "if.end14.us" }) := by
            have h := hstep2
            rw [execTerm_condbr_true hev2 (ofBool_of_true hbit), withEnv_setJmp] at h
            exact h
          have hpack : packLanes u8k = bytesToNat (klAcc bs nb) := by
            rw [hu8kpack, ← hlast, haccEq]
          refine ⟨env2, { s with pc := "for.cond.cleanup", pre := some "if.end14.us" }, u8k, 2,
            rfl, rfl, hmem, by omega, hU2, hu8klen, hpack, ?_, ?_, ?_, ?_⟩
          · exact (hframe2 "%b" (by decide)).trans hb1
          · exact (hframe2 "%n" (by decide)).trans hn1
          · exact (hframe2 "%div44" (by decide)).trans hdiv1
          · intro k
            rw [show 2 + k = (1 + k) + 1 from by omega, runFuel_jump_utf8 hjump1,
              show 1 + k = k + 1 from by omega, runFuel_jump_utf8 hjump2]
        · -- the loop continues at the next block
          have hlt : i + 1 < nb := by omega
          have hbit : BitVec.ofNat 64 i + BitVec.ofInt 64 1 ≠ BitVec.ofNat 64 nb := by
            intro hc
            rw [hnext] at hc
            exact hlast (ofNat64_inj (by omega) (by omega) hc)
          have hjump2 : step utf8Calls utf8Function
              (withEnv env1 { s with pc := "if.end14.us", pre := some "for.body.us" })
              = .jump (withEnv env2
                  { s with pc := "for.body.us", pre := some "if.end14.us" }) := by
            have h := hstep2
            rw [execTerm_condbr_false hev2 (ofBool_of_false hbit), withEnv_setJmp] at h
            exact h
          have hr' : 1 ≤ r' := by omega
          obtain ⟨env3, s3, u8k3, t3, hpc3, hpre3, hmem3, ht3, hU3, hlen3, hpack3, hb3, hn3,
            hdiv3, hrun3⟩ :=
            ih (i + 1) env2 { s with pc := "for.body.us", pre := some "if.end14.us" }
              "if.end14.us" (.reg "%2") (.reg "%u8k.2.us") (.reg "%inc.us") u8k
              (ptestz (BitVec.ofNat 256 (utf8GateWord ((S.drop 3).take 32)
                ((S.drop 35).take 32))) (BitVec.ofNat 256 (packLanes highLanes64)))
              hr' (by omega) rfl rfl hmem rfl rfl rfl
              (by
                rw [evalOperand_reg_withEnv,
                  latch_keeps_two env1 env2
                    { s with pc := "if.end14.us", pre := some "for.body.us" } hrun2]
                exact h21)
              (by
                rw [evalOperand_reg_withEnv, lookupName_cons_ne _ _ (by decide)]
                exact hU2)
              (by
                rw [evalOperand_reg_withEnv, lookupName_cons_ne _ _ (by decide),
                  lookupName_cons_ne _ _ (by decide), hI2, hnext])
              ((hframe2 "%b" (by decide)).trans hb1)
              ((hframe2 "%div44" (by decide)).trans hdiv1)
              ((hframe2 "%n" (by decide)).trans hn1)
              hu8klen (by rw [hu8kpack, haccEq]) hp01' hpAscii'
          refine ⟨env3, s3, u8k3, 2 + t3, hpc3, hpre3, hmem3, by omega, hU3, hlen3, hpack3,
            hb3, hn3, hdiv3, ?_⟩
          intro k
          rw [show (2 + t3) + k = ((1 + t3) + k) + 1 from by omega,
            runFuel_jump_utf8 hjump1,
            show (1 + t3) + k = (t3 + k) + 1 from by omega,
            runFuel_jump_utf8 hjump2]
          exact hrun3 k
      · -- the gate does not skip: the DFA body runs, then the latch
        have hbit0 : utf8GateBit ((S.drop 3).take 32) ((S.drop 35).take 32) prev = 0 :=
          bit1_eq_zero_of_ne_one _ hskip
        have hjump1 : step utf8Calls utf8Function (withEnv env s)
            = .jump (withEnv env1 { s with pc := "if.then11.us", pre := some "for.body.us" }) := by
          have h := hstep1
          rw [execTerm_condbr_false hev1 hbit0, withEnv_setJmp, hpc1] at h
          exact h
        obtain ⟨envB, hrunB, hvalB⟩ :=
          utf8Gated_body env1 { s with pc := "if.then11.us", pre := some "for.body.us" }
            b i u8k ((S.drop 2).take 32) ((S.drop 1).take 32) (S.take 32)
            ((S.drop 34).take 32) ((S.drop 33).take 32) ((S.drop 32).take 32)
            (bytesToNat ((S.drop 3).take 32)) (bytesToNat ((S.drop 35).take 32))
            hU1 hptr1 h01 h11 hu8klen hV0 hV1 read3 read4 read5 read19 read20 read21 hb hi64
        -- the body's word, in the emission's `|||` order
        let A := errRaw (byteLanes ((S.drop 1).take 32)) (byteLanes (S.take 32))
          (bytesToNat ((S.drop 2).take 32)) (bytesToNat ((S.drop 3).take 32))
        let Bv := errRaw (byteLanes ((S.drop 33).take 32)) (byteLanes ((S.drop 32).take 32))
          (bytesToNat ((S.drop 34).take 32)) (bytesToNat ((S.drop 35).take 32))
        let G := List.zipWith (· ||| ·) (List.zipWith (· ||| ·) A Bv) u8k
        have hvalG : lookupName envB "%or.i.us" = some (.vec 4 64 G) := hvalB
        have hlenA : A.length = 4 :=
          errRaw_length _ _ _ _ (len32_byteLanes _ hlen1) (len32_byteLanes _ hlen0)
        have hlenBv : Bv.length = 4 :=
          errRaw_length _ _ _ _ (len32_byteLanes _ hlen33) (len32_byteLanes _ hlen32)
        have hglen : G.length = 4 := by
          show (List.zipWith (· ||| ·) (List.zipWith (· ||| ·) A Bv) u8k).length = 4
          rw [List.length_zipWith, List.length_zipWith, hlenA, hlenBv, Nat.min_self, hu8klen,
            Nat.min_self]
        -- the body's word is the fold's step
        have hpackG : packLanes G = bytesToNat (klAcc bs (i + 1)) := by
          have hbody :=
            errRawBlk_word_eq (S.take 67) (klAcc bs i) u8k
              (klPre (utf8Window bs n nb) i) (klBlk (utf8Window bs n nb) i)
              (by
                rw [← body_stream, klBlk,
                  show (utf8Window bs n nb).drop (64 * i + 3) = S.drop 3 from by
                    show (utf8Window bs n nb).drop (64 * i + 3) = (utf8Stream bs n nb i).drop 3
                    rw [utf8Stream, List.drop_drop]]
                rfl)
              (by rw [List.length_take, hSlen]; exact Nat.le_min.mpr ⟨by omega, by omega⟩)
              (klAcc_length bs i) hu8klen
              (by rw [klPre, List.length_take, List.length_drop, hWlen]
                  exact Nat.min_eq_left (by omega))
              (by rw [klBlk, List.length_take, List.length_drop, hWlen]
                  exact Nat.min_eq_left (by omega))
              hu8kpack
          rw [List.drop_drop, List.drop_drop, List.drop_drop] at hbody
          have h67 : ((S.take 67).take 32) = S.take 32 := by
            rw [List.take_take, Nat.min_eq_left (by decide)]
          rw [h67, take67_drop _ 1 32 (by omega), take67_drop _ 2 32 (by omega),
            take67_drop _ 3 32 (by omega), take67_drop _ 32 32 (by omega),
            take67_drop _ 33 32 (by omega), take67_drop _ 34 32 (by omega),
            take67_drop _ 35 32 (by omega)] at hbody
          have hkl : klErrBlk (klPre (utf8Window bs n nb) i) (klBlk (utf8Window bs n nb) i)
              = utf8BlkErr bs n nb i := by
            rw [utf8BlkErr_eq, klErrBlk_window]
          rw [hkl] at hbody
          have hp1 : packLanes G
              = packLanes (List.zipWith (· ||| ·) (List.zipWith (· ||| ·) A u8k) Bv) :=
            packLanes_zipWith_or_reorder A Bv u8k (hlenA.trans hlenBv.symm)
              (hlenBv.trans hu8klen.symm)
          have hstep : List.zipWith (· ||| ·) (List.zipWith (· ||| ·) A u8k) Bv
              = unpackLanes 64 4 (bytesToNat
                  (List.zipWith (· ||| ·) (klAcc bs i) (utf8BlkErr bs n nb i))) := hbody
          calc packLanes G
              = packLanes (List.zipWith (· ||| ·) (List.zipWith (· ||| ·) A u8k) Bv) := hp1
            _ = packLanes (unpackLanes 64 4 (bytesToNat
                  (List.zipWith (· ||| ·) (klAcc bs i) (utf8BlkErr bs n nb i)))) := by
                  rw [hstep]
            _ = bytesToNat (klAcc bs (i + 1)) := klAccStep_pack bs n nb i
        -- the latch, from the body's edge
        have hbiB : lookupName envB "%bi.075.us" = some (.int 64 (BitVec.ofNat 64 i)) :=
          (denoteCode_lookupName_of_not_dst utf8ThenUs.instrs env1 envB
            { s with pc := "if.then11.us", pre := some "for.body.us" } "%bi.075.us"
            (by decide) hrunB).trans hB1
        have hbB : lookupName envB "%b" = some (.ptr b) :=
          (denoteCode_kept utf8ThenUs.instrs env1 envB
            { s with pc := "if.then11.us", pre := some "for.body.us" } hrunB utf8Kept_then
            "%b" (by decide)).trans hb1
        have hnB : lookupName envB "%n" = some (.int 64 (BitVec.ofNat 64 n)) :=
          (denoteCode_kept utf8ThenUs.instrs env1 envB
            { s with pc := "if.then11.us", pre := some "for.body.us" } hrunB utf8Kept_then
            "%n" (by decide)).trans hn1
        have hdivB : lookupName envB "%div44" = some (.int 64 (BitVec.ofNat 64 nb)) :=
          (denoteCode_kept utf8ThenUs.instrs env1 envB
            { s with pc := "if.then11.us", pre := some "for.body.us" } hrunB utf8Kept_then
            "%div44" (by decide)).trans hdiv1
        obtain ⟨env2, hrun2, hU2, hI2, hE2⟩ :=
          utf8EndUs_run envB { s with pc := "if.end14.us", pre := some "if.then11.us" }
            "if.then11.us" (.reg "%or.i.us") G i nb rfl rfl
            (by rw [evalOperand_reg_withEnv]; exact hvalG) hbiB hdivB
        have hstep2 : step utf8Calls utf8Function
            (withEnv envB { s with pc := "if.end14.us", pre := some "if.then11.us" })
            = execTerm (withEnv env2 { s with pc := "if.end14.us", pre := some "if.then11.us" })
                (.condbr (.reg "%exitcond79.not") "for.cond.cleanup" "for.body.us") :=
          step_of_utf8 _ "if.end14.us" utf8EndUs _ rfl findBlock_utf8EndUs hrun2
        have hstepB : step utf8Calls utf8Function
            (withEnv env1 { s with pc := "if.then11.us", pre := some "for.body.us" })
            = .jump (withEnv envB { s with pc := "if.end14.us", pre := some "if.then11.us" }) :=
          step_of_utf8 _ "if.then11.us" utf8ThenUs _ rfl findBlock_utf8ThenUs hrunB
        have hev2 : evalOperand
            (withEnv env2 { s with pc := "if.end14.us", pre := some "if.then11.us" })
            (.reg "%exitcond79.not")
            = some (.int 1 (BitVec.ofBool
                (BitVec.ofNat 64 i + BitVec.ofInt 64 1 = BitVec.ofNat 64 nb))) := by
          rw [evalOperand_reg_withEnv]
          exact hE2
        have hframe2 := fun (nm : String) (hm : nm ∈ utf8Kept) =>
          denoteCode_kept utf8EndUs.instrs envB env2
            { s with pc := "if.end14.us", pre := some "if.then11.us" } hrun2 utf8Kept_end nm hm
        by_cases hlast : i + 1 = nb
        · -- the loop is done: the latch's test leaves for `for.cond.cleanup`
          have hbit : BitVec.ofNat 64 i + BitVec.ofInt 64 1 = BitVec.ofNat 64 nb := by
            rw [hnext, hlast]
          have hjump2 : step utf8Calls utf8Function
              (withEnv envB { s with pc := "if.end14.us", pre := some "if.then11.us" })
              = .jump (withEnv env2
                  { s with pc := "for.cond.cleanup", pre := some "if.end14.us" }) := by
            have h := hstep2
            rw [execTerm_condbr_true hev2 (ofBool_of_true hbit), withEnv_setJmp] at h
            exact h
          have hpack : packLanes G = bytesToNat (klAcc bs nb) := by
            rw [hpackG, hlast]
          refine ⟨env2, { s with pc := "for.cond.cleanup", pre := some "if.end14.us" }, G, 3,
            rfl, rfl, hmem, by omega, hU2, hglen, hpack, ?_, ?_, ?_, ?_⟩
          · exact (hframe2 "%b" (by decide)).trans hbB
          · exact (hframe2 "%n" (by decide)).trans hnB
          · exact (hframe2 "%div44" (by decide)).trans hdivB
          · intro k
            rw [show 3 + k = ((2 + k) + 1) from by omega, runFuel_jump_utf8 hjump1,
              show 2 + k = ((1 + k) + 1) from by omega, runFuel_jump_utf8 hstepB,
              show 1 + k = k + 1 from by omega, runFuel_jump_utf8 hjump2]
        · -- the loop continues at the next block
          have hlt : i + 1 < nb := by omega
          have hbit : BitVec.ofNat 64 i + BitVec.ofInt 64 1 ≠ BitVec.ofNat 64 nb := by
            intro hc
            rw [hnext] at hc
            exact hlast (ofNat64_inj (by omega) (by omega) hc)
          have hjump2 : step utf8Calls utf8Function
              (withEnv envB { s with pc := "if.end14.us", pre := some "if.then11.us" })
              = .jump (withEnv env2
                  { s with pc := "for.body.us", pre := some "if.end14.us" }) := by
            have h := hstep2
            rw [execTerm_condbr_false hev2 (ofBool_of_false hbit), withEnv_setJmp] at h
            exact h
          have hr' : 1 ≤ r' := by omega
          obtain ⟨env3, s3, u8k3, t3, hpc3, hpre3, hmem3, ht3, hU3, hlen3, hpack3, hb3, hn3,
            hdiv3, hrun3⟩ :=
            ih (i + 1) env2 { s with pc := "for.body.us", pre := some "if.end14.us" }
              "if.end14.us" (.reg "%2") (.reg "%u8k.2.us") (.reg "%inc.us") G
              (ptestz (BitVec.ofNat 256 (utf8GateWord ((S.drop 3).take 32)
                ((S.drop 35).take 32))) (BitVec.ofNat 256 (packLanes highLanes64)))
              hr' (by omega) rfl rfl hmem rfl rfl rfl
              (by
                rw [evalOperand_reg_withEnv,
                  latch_keeps_two envB env2
                    { s with pc := "if.end14.us", pre := some "if.then11.us" } hrun2,
                  denoteCode_lookupName_of_not_dst utf8ThenUs.instrs env1 envB
                    { s with pc := "if.then11.us", pre := some "for.body.us" } "%2"
                    (by decide) hrunB]
                exact h21)
              (by
                rw [evalOperand_reg_withEnv, lookupName_cons_ne _ _ (by decide)]
                exact hU2)
              (by
                rw [evalOperand_reg_withEnv, lookupName_cons_ne _ _ (by decide),
                  lookupName_cons_ne _ _ (by decide), hI2, hnext])
              ((hframe2 "%b" (by decide)).trans hbB)
              ((hframe2 "%div44" (by decide)).trans hdivB)
              ((hframe2 "%n" (by decide)).trans hnB)
              hglen hpackG hp01' hpAscii'
          refine ⟨env3, s3, u8k3, 3 + t3, hpc3, hpre3, hmem3, by omega, hU3, hlen3, hpack3,
            hb3, hn3, hdiv3, ?_⟩
          intro k
          rw [show (3 + t3) + k = ((2 + t3) + k) + 1 from by omega,
            runFuel_jump_utf8 hjump1,
            show (2 + t3) + k = ((1 + t3) + k) + 1 from by omega,
            runFuel_jump_utf8 hstepB,
            show (1 + t3) + k = (t3 + k) + 1 from by omega,
            runFuel_jump_utf8 hjump2]
          exact hrun3 k

end LeanLLVM.Refinement.JsonUtf8Steps

namespace LeanLLVM.Refinement.JsonUtf8Steps

open LeanLLVM
open LeanLLVM.Refinement.JsonUtf8IR
open LeanLLVM.Refinement.JsonUtf8Spec
open LeanLLVM.Refinement.BitLanes
open LeanLLVM.Refinement.JsonEntrySteps

/-! ### The entries, the block count, and a read inside a readable prefix -/

theorem ofNat64_add63 (n : Nat) (hn : n + 63 < 2 ^ 64) :
    (BitVec.ofNat 64 n + BitVec.ofInt 64 63) = BitVec.ofNat 64 (n + 63) := by
  have h63 : (BitVec.ofInt 64 63 : BitVec 64) = BitVec.ofNat 64 63 := by decide
  rw [h63]
  exact ofNat64_add_ofNat n 63 hn

theorem ofNat64_ushr (a : BitVec 64) (k : Nat) :
    BitVec.ofNat 64 (a.toNat >>> k) = a >>> k := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ushiftRight]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) a.isLt)

theorem div44_ofNat (n nb : Nat) (hn : n + 63 < 2 ^ 64) (hnb : nb = (n + 63) / 64) :
    (BitVec.ofNat 64 n + BitVec.ofInt 64 63) >>> (BitVec.ofInt 64 6).toNat
      = BitVec.ofNat 64 nb := by
  rw [ofNat64_add63 n hn]
  have h6 : (BitVec.ofInt 64 6).toNat = 6 := by decide
  rw [h6, ← ofNat64_ushr]
  have hto : (BitVec.ofNat 64 (n + 63)).toNat = n + 63 := toNat_ofNat64 (n + 63) hn
  have h64 : (2 : Nat) ^ 6 = 64 := by decide
  rw [hto, Nat.shiftRight_eq_div_pow, h64, hnb]

theorem ofNat64_ult_false (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : b ≤ a) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, toNat_ofNat64 a ha, toNat_ofNat64 b hb]
  omega

/-- A readable range reads back. -/
theorem prefix_readable_bytes (mem : Mem) (b i : Nat)
    (hb : 3 ≤ b)
    (hpre : ∀ k, k < 3 → readByte mem (b - 3 + k) = some 0x00)
    (hblk : ∀ i' j', i' < i → j' < 64 → readByte mem (b + 64 * i' + j') ≠ none) :
    ∃ W, readBytes mem (b - 3) (3 + 64 * i) = some W := by
  refine exists_readBytes_of_readable mem (b - 3) (3 + 64 * i) (fun k hk => ?_)
  by_cases h3 : k < 3
  · rw [hpre k h3]
    exact fun hc => by cases hc
  · have hk3 : 3 ≤ k := by omega
    have hm : k - 3 < 64 * i := by omega
    have hi' : (k - 3) / 64 < i := div_lt_of_lt_mul' hm
    have hj' : (k - 3) % 64 < 64 := Nat.mod_lt _ (by decide)
    have heq : b - 3 + k = b + 64 * ((k - 3) / 64) + (k - 3) % 64 := by
      have hdm := Nat.div_add_mod (k - 3) 64
      omega
    rw [heq]
    exact hblk _ _ hi' hj'

/-- A read of the whole range reads any thirty-two bytes at an interior offset. -/
theorem win_read_len (mem : Mem) (base L j : Nat) (W : List UInt8)
    (hw : readBytes mem base L = some W) (hj : j + 32 ≤ L) :
    readBytes mem (base + j) 32 = some ((W.drop j).take 32) := by
  have hN : j + (L - j) = L := by omega
  have h1 : readBytes mem base (j + (L - j)) = some W := by rw [hN]; exact hw
  obtain ⟨-, h2⟩ := readBytes_split mem base j (L - j) h1
  have hM : 32 + ((L - j) - 32) = L - j := by omega
  have h3 : readBytes mem (base + j) (32 + ((L - j) - 32)) = some (W.drop j) := by
    rw [hM]; exact h2
  exact (readBytes_split mem (base + j) 32 ((L - j) - 32) h3).1

/-- The block slices, read inside a readable prefix. -/
theorem win_read_slice_len (mem : Mem) (b L : Nat) (W : List UInt8) (j c : Nat)
    (hw : readBytes mem (b - 3) L = some W) (hb : 3 ≤ b)
    (hj : 64 * j + c + 32 ≤ L) :
    readBytes mem (b + 64 * j + c - 3) 32
      = some (((W.drop (64 * j)).drop c).take 32) := by
  have h := win_read_len mem (b - 3) L (64 * j + c) W hw (by omega)
  rw [show b - 3 + (64 * j + c) = b + 64 * j + c - 3 from by omega] at h
  rw [show List.drop (64 * j + c) W = List.drop c (List.drop (64 * j) W) from by
    rw [List.drop_drop]] at h
  exact h

/-- The body's `pre ++ blk` slice, at a stream. -/
theorem stream_slice_at (S : List UInt8) (c m : Nat) (h : c + m ≤ 67) :
    (((S.take 3 ++ (S.drop 3).take 64).drop c).take m) = (S.drop c).take m := by
  rw [body_stream]
  exact take67_drop _ c m h

/-- The pack of a block's word is its bytes' natural. -/
theorem packLanes_word (acc blkErr : List UInt8) (h : acc.length = 32)
    (hb : blkErr.length = 32) :
    packLanes (unpackLanes 64 4 (bytesToNat (List.zipWith (· ||| ·) acc blkErr)))
      = bytesToNat (List.zipWith (· ||| ·) acc blkErr) := by
  rw [packLanes_unpackLanes]
  exact Nat.mod_eq_of_lt (by
    have := bytesToNat_lt (List.zipWith (· ||| ·) acc blkErr)
    rw [List.length_zipWith, h, hb, Nat.min_self,
      show (256 : Nat) ^ 32 = 2 ^ 256 from by decide] at this
    exact this)

/-! ### Reaching the block a run cannot read — the ungated path -/

/-- `for.body` from the header of block `j` to the header of block `i`, one block
per control step, when every byte the blocks before `i` read is readable: the
prefix `[b - 3, b - 3 + (3 + 64 * i))` reads back, so the eight loads of each
block are its slices of that read and the body runs.  The accumulators are
carried as the loop lemma carries them, because the body states its word at them;
the statement ends at the header rather than at a verdict, which is what the
companion wants. -/
theorem utf8Ungated_reach (nb b i : Nat) (mem : Mem) (W : List UInt8)
    (hW : readBytes mem (b - 3) (3 + 64 * i) = some W)
    (hb : 3 ≤ b) (hinb : i < nb) (hnb64 : nb < 2 ^ 64)
    (hspan : 64 * (nb - 1) < 2 ^ 63) :
    ∀ (r j : Nat) (env : Env) (s : State) (p : String) (opA opB : Operand)
      (u8k : List (BitVec 64)) (acc : List UInt8),
      j + r = i → j < i → s.pc = "for.body" → s.pre = some p → s.mem = mem →
      phiIncoming p [("for.body", .reg "%or.i47"),
        ("for.body.lr.ph", .imm (.splat 4 64 (BitVec.ofInt 64 0)))] = some opA →
      phiIncoming p [("for.body", .reg "%inc"),
        ("for.body.lr.ph", .imm (.int 64 (BitVec.ofInt 64 0)))] = some opB →
      evalOperand (withEnv env s) opA = some (.vec 4 64 u8k) →
      evalOperand (withEnv (("%u8k.076", .vec 4 64 u8k) :: env) s) opB
        = some (.int 64 (BitVec.ofNat 64 j)) →
      lookupName env "%b" = some (.ptr b) →
      lookupName env "%div44" = some (.int 64 (BitVec.ofNat 64 nb)) →
      acc.length = 32 → u8k.length = 4 → packLanes u8k = bytesToNat acc →
      ∃ (env' : Env) (s' : State) (u8k' : List (BitVec 64)) (acc' : List UInt8),
        s'.pc = "for.body" ∧ s'.pre = some "for.body" ∧ s'.mem = mem ∧
        lookupName env' "%or.i47" = some (.vec 4 64 u8k') ∧ u8k'.length = 4 ∧
        acc'.length = 32 ∧ packLanes u8k' = bytesToNat acc' ∧
        lookupName env' "%b" = some (.ptr b) ∧
        lookupName env' "%div44" = some (.int 64 (BitVec.ofNat 64 nb)) ∧
        lookupName env' "%inc" = some (.int 64 (BitVec.ofNat 64 i)) ∧
        ∀ (k : Nat), runFuel utf8Calls (r + k) utf8Function (withEnv env s)
          = runFuel utf8Calls k utf8Function (withEnv env' s') := by
  have hWlen : W.length = 3 + 64 * i := readBytes_length mem (b - 3) (3 + 64 * i) hW
  intro r
  induction r with
  | zero =>
      intro j env s p opA opB u8k acc hi hjlt
      omega
  | succ r' ih =>
      intro j env s p opA opB u8k acc hi hjlt hpc hpre hmem hincA hincB hopA hopB hb' hdiv
        hacc hu8klen hu8kpack
      have hj64 : 64 * j < 2 ^ 63 := by
        have h1 : j ≤ nb - 1 := by omega
        have h2 := Nat.mul_le_mul_left 64 h1
        omega
      let S := W.drop (64 * j)
      have hSlen : S.length = 3 + 64 * i - 64 * j := by
        rw [show S = W.drop (64 * j) from rfl, List.length_drop, hWlen]
      have hS67 : 67 ≤ S.length := by omega
      -- the eight reads
      have read37 : readBytes s.mem (b + 64 * j + 3 - 3) 32 = some ((S.drop 3).take 32) := by
        rw [hmem]; exact win_read_slice_len mem b (3 + 64 * i) W j 3 hW hb (by omega)
      have read38 : readBytes s.mem (b + 64 * j + 35 - 3) 32 = some ((S.drop 35).take 32) := by
        rw [hmem]; exact win_read_slice_len mem b (3 + 64 * i) W j 35 hW hb (by omega)
      have read39 : readBytes s.mem (b + 64 * j + 2 - 3) 32 = some ((S.drop 2).take 32) := by
        rw [hmem]; exact win_read_slice_len mem b (3 + 64 * i) W j 2 hW hb (by omega)
      have read40 : readBytes s.mem (b + 64 * j + 1 - 3) 32 = some ((S.drop 1).take 32) := by
        rw [hmem]; exact win_read_slice_len mem b (3 + 64 * i) W j 1 hW hb (by omega)
      have read41 : readBytes s.mem (b + 64 * j + 0 - 3) 32 = some ((S.drop 0).take 32) := by
        rw [hmem]; exact win_read_slice_len mem b (3 + 64 * i) W j 0 hW hb (by omega)
      have read54 : readBytes s.mem (b + 64 * j + 34 - 3) 32 = some ((S.drop 34).take 32) := by
        rw [hmem]; exact win_read_slice_len mem b (3 + 64 * i) W j 34 hW hb (by omega)
      have read55 : readBytes s.mem (b + 64 * j + 33 - 3) 32 = some ((S.drop 33).take 32) := by
        rw [hmem]; exact win_read_slice_len mem b (3 + 64 * i) W j 33 hW hb (by omega)
      have read56 : readBytes s.mem (b + 64 * j + 32 - 3) 32 = some ((S.drop 32).take 32) := by
        rw [hmem]; exact win_read_slice_len mem b (3 + 64 * i) W j 32 hW hb (by omega)
      -- the body's `pre ++ blk` slices
      have upper : ∀ c : Nat, c + 32 ≤ 35 →
          ((((S.take 3 ++ (S.drop 3).take 64).drop 32).drop c).take 32)
            = (S.drop (32 + c)).take 32 := by
        intro c hc
        rw [List.drop_drop, stream_slice_at S (32 + c) 32 (by omega)]
      have slice37 := stream_slice_at S 3 32 (by omega)
      have slice38 := upper 3 (by omega)
      have slice39 := stream_slice_at S 2 32 (by omega)
      have slice40 := stream_slice_at S 1 32 (by omega)
      have slice41 := stream_slice_at S 0 32 (by omega)
      have slice54 := upper 2 (by omega)
      have slice55 := upper 1 (by omega)
      have slice56 := upper 0 (by omega)
      obtain ⟨env'', hrunB, hval, hinc, hexit⟩ :=
        utf8Ungated_body env s b nb j acc (S.take 3) ((S.drop 3).take 64) u8k
          ((S.drop 3).take 32) ((S.drop 35).take 32) ((S.drop 2).take 32)
          ((S.drop 1).take 32) ((S.drop 0).take 32) ((S.drop 34).take 32)
          ((S.drop 33).take 32) ((S.drop 32).take 32)
          p opA opB hpre hincA hincB hopA hopB hb' hdiv
          hacc hu8klen (by rw [List.length_take]; omega)
          (by rw [List.length_take, List.length_drop]; omega) hu8kpack
          slice37.symm slice38.symm slice39.symm slice40.symm slice41.symm
          slice54.symm slice55.symm slice56.symm
          read37 read38 read39 read40 read41 read54 read55 read56 hb hj64
      have hframe := fun (nm : String) (hm : nm ∈ utf8Kept) =>
        denoteCode_kept utf8ForBody.instrs env env'' s hrunB utf8Kept_body nm hm
      have hstep : step utf8Calls utf8Function (withEnv env s)
          = execTerm (withEnv env'' s)
              (.condbr (.reg "%exitcond.not") "for.cond.cleanup" "for.body") :=
        step_of_utf8 _ "for.body" utf8ForBody (withEnv env'' s) hpc findBlock_utf8ForBody hrunB
      have hexit' : evalOperand (withEnv env'' s) (.reg "%exitcond.not")
          = some (.int 1 (BitVec.ofBool
              (BitVec.ofNat 64 j + BitVec.ofInt 64 1 = BitVec.ofNat 64 nb))) := by
        simpa only [withEnv, evalOperand] using hexit
      have hone : (BitVec.ofInt 64 1 : BitVec 64) = BitVec.ofNat 64 1 := by decide
      have hnext : BitVec.ofNat 64 j + BitVec.ofInt 64 1 = BitVec.ofNat 64 (j + 1) := by
        rw [hone, ofNat64_add_ofNat j 1 (by omega)]
      have hlt : j + 1 < nb := by omega
      have hbit : BitVec.ofNat 64 j + BitVec.ofInt 64 1 ≠ BitVec.ofNat 64 nb := by
        intro hc
        rw [hnext] at hc
        exact absurd (ofNat64_inj (by omega) (by omega) hc) (by omega)
      have hjump : step utf8Calls utf8Function (withEnv env s) = .jump
          ({ (withEnv env'' s) with pc := "for.body", pre := some "for.body" } : State) := by
        rw [hstep, execTerm_condbr_false hexit' (ofBool_of_false hbit),
          show (withEnv env'' s).pc = "for.body" from by rw [withEnv]; exact hpc]
      let GE := unpackLanes 64 4 (bytesToNat
        (List.zipWith (· ||| ·) acc (klErrBlk (S.take 3) ((S.drop 3).take 64))))
      let AE := List.zipWith (· ||| ·) acc (klErrBlk (S.take 3) ((S.drop 3).take 64))
      have hGElen : GE.length = 4 := by
        rw [show GE = unpackLanes 64 4 _ from rfl, unpackLanes_length]
      have hAElen : AE.length = 32 := by
        rw [show AE = List.zipWith (· ||| ·) acc _ from rfl, List.length_zipWith, hacc,
          klErrBlk_length, Nat.min_self]
      have hGEpack : packLanes GE = bytesToNat AE := by
        rw [show GE = unpackLanes 64 4 _ from rfl, show AE = _ from rfl]
        exact packLanes_word acc _ hacc (klErrBlk_length _ _)
      have hvalE : lookupName env'' "%or.i47" = some (.vec 4 64 GE) := hval
      have hincE : lookupName env'' "%inc" = some (.int 64 (BitVec.ofNat 64 (j + 1))) := by
        rw [← hnext]; exact hinc
      have hbE : lookupName env'' "%b" = some (.ptr b) := (hframe "%b" (by decide)).trans hb'
      have hdivE : lookupName env'' "%div44" = some (.int 64 (BitVec.ofNat 64 nb)) :=
        (hframe "%div44" (by decide)).trans hdiv
      by_cases hr0 : r' = 0
      · have hji : j + 1 = i := by omega
        refine ⟨env'', ({ (withEnv env'' s) with pc := "for.body", pre := some "for.body" } : State),
          GE, AE, rfl, rfl, hmem, hvalE, hGElen, hAElen, hGEpack, hbE, hdivE, ?_, ?_⟩
        · rw [hincE, hji]
        · intro k
          rw [show (r' + 1) + k = k + 1 from by omega, runFuel_jump_utf8 hjump]
          rfl
      · have hr' : 1 ≤ r' := by omega
        obtain ⟨env3, s3, u8k3, acc3, hpc3, hpre3', hmem3, hval3, hlen3, hacc3, hpack3, hb3,
          hdiv3, hinc3, hrun3⟩ :=
          ih (j + 1) env'' { (withEnv env'' s) with pc := "for.body", pre := some "for.body" }
            "for.body" (.reg "%or.i47") (.reg "%inc") GE AE
            (by omega) (by omega) rfl rfl hmem rfl rfl
            (evalOperand_reg_of env'' _ "%or.i47" _ hvalE)
            (by
              rw [evalOperand_reg_of _ _ "%inc" _ ((lookupName_cons_ne _ _ (by decide)).trans hincE)])
            hbE hdivE hAElen hGElen hGEpack
        refine ⟨env3, s3, u8k3, acc3, hpc3, hpre3', hmem3, hval3, hlen3, hacc3, hpack3, hb3,
          hdiv3, hinc3, ?_⟩
        intro k
        rw [show (r' + 1) + k = (r' + k) + 1 from by omega, runFuel_jump_utf8 hjump]
        exact hrun3 k

/-- Four lanes pack below the thirty-two bytes' range, so any carried word is the
natural of a byte list. -/
theorem packLanes_fits (u8k : List (BitVec 64)) (h : u8k.length = 4) :
    ∃ acc : List UInt8, acc.length = 32 ∧ packLanes u8k = bytesToNat acc := by
  have hfit : packLanes u8k < 256 ^ 32 := by
    have h1 := packLanes_lt u8k
    have h2 : u8k.length * 64 = 256 := by rw [h]
    rw [h2, show (256 : Nat) ^ 32 = 2 ^ 256 from by decide] at h1
    exact h1
  refine ⟨natToBytes (packLanes u8k) 32, natToBytes_length _ _, ?_⟩
  show packLanes u8k = bytesToNat (natToBytes (packLanes u8k) 32)
  rw [natToBytes_toNat]
  exact (Nat.mod_eq_of_lt hfit).symm

/-! ### Reaching the block a run cannot read — the gated path -/

/-- `for.body.us` from the header of block `j` to the header of block `i` under
the same readable prefix.  A block costs at most three control steps — the header,
the gate's alternative, and the latch — so the fuel is a bound `t ≤ 3 * r` and
the conclusion is an existential with the run's equality at every continuation.
The gate's bit is not evaluated: whichever way it goes the latch is next, and the
skip contributes its carried word unchanged. -/
theorem utf8Gated_reach (nb b i : Nat) (mem : Mem) (W : List UInt8)
    (hW : readBytes mem (b - 3) (3 + 64 * i) = some W)
    (hb : 3 ≤ b) (hinb : i < nb) (hnb64 : nb < 2 ^ 64)
    (hspan : 64 * (nb - 1) < 2 ^ 63) :
    ∀ (r j : Nat) (env : Env) (s : State) (p : String) (opP opU opB : Operand)
      (u8k : List (BitVec 64)) (prev : BitVec 32) (acc : List UInt8),
      j + r = i → j < i → s.pc = "for.body.us" → s.pre = some p → s.mem = mem →
      phiIncoming p [("if.end14.us", .reg "%2"),
        ("for.body.lr.ph", .imm (.int 32 (BitVec.ofInt 32 1)))] = some opP →
      phiIncoming p [("if.end14.us", .reg "%u8k.2.us"),
        ("for.body.lr.ph", .imm (.splat 4 64 (BitVec.ofInt 64 0)))] = some opU →
      phiIncoming p [("if.end14.us", .reg "%inc.us"),
        ("for.body.lr.ph", .imm (.int 64 (BitVec.ofInt 64 0)))] = some opB →
      evalOperand (withEnv env s) opP = some (.int 32 prev) →
      evalOperand (withEnv (("%prev_ascii.077.us", .int 32 prev) :: env) s) opU
        = some (.vec 4 64 u8k) →
      evalOperand (withEnv (("%u8k.076.us", .vec 4 64 u8k) ::
        ("%prev_ascii.077.us", .int 32 prev) :: env) s) opB
        = some (.int 64 (BitVec.ofNat 64 j)) →
      lookupName env "%b" = some (.ptr b) →
      lookupName env "%div44" = some (.int 64 (BitVec.ofNat 64 nb)) →
      acc.length = 32 → u8k.length = 4 → packLanes u8k = bytesToNat acc →
      ∃ (env' : Env) (s' : State) (u8k' : List (BitVec 64)) (acc' : List UInt8)
        (prev' : BitVec 32) (t : Nat),
        s'.pc = "for.body.us" ∧ s'.pre = some "if.end14.us" ∧ s'.mem = mem ∧
        t ≤ 3 * r ∧
        lookupName env' "%2" = some (.int 32 prev') ∧
        lookupName env' "%u8k.2.us" = some (.vec 4 64 u8k') ∧ u8k'.length = 4 ∧
        acc'.length = 32 ∧ packLanes u8k' = bytesToNat acc' ∧
        lookupName env' "%b" = some (.ptr b) ∧
        lookupName env' "%div44" = some (.int 64 (BitVec.ofNat 64 nb)) ∧
        lookupName env' "%inc.us" = some (.int 64 (BitVec.ofNat 64 i)) ∧
        ∀ (k : Nat), runFuel utf8Calls (t + k) utf8Function (withEnv env s)
          = runFuel utf8Calls k utf8Function (withEnv env' s') := by
  have hWlen : W.length = 3 + 64 * i := readBytes_length mem (b - 3) (3 + 64 * i) hW
  intro r
  induction r with
  | zero =>
      intro j env s p opP opU opB u8k prev acc hi hjlt
      omega
  | succ r' ih =>
      intro j env s p opP opU opB u8k prev acc hi hjlt hpc hpre hmem hincP hincU hincB
        hopP hopU hopB hb' hdiv hacc hu8klen hu8kpack
      have hj64 : 64 * j < 2 ^ 63 := by
        have h1 : j ≤ nb - 1 := by omega
        have h2 := Nat.mul_le_mul_left 64 h1
        omega
      let S := W.drop (64 * j)
      have hSlen : S.length = 3 + 64 * i - 64 * j := by
        rw [show S = W.drop (64 * j) from rfl, List.length_drop, hWlen]
      have hlenB0 : ((S.drop 3).take 32).length = 32 := by
        rw [List.length_take, List.length_drop, hSlen]; exact Nat.min_eq_left (by omega)
      have hlenB1 : ((S.drop 35).take 32).length = 32 := by
        rw [List.length_take, List.length_drop, hSlen]; exact Nat.min_eq_left (by omega)
      have hlen1 : ((S.drop 1).take 32).length = 32 := by
        rw [List.length_take, List.length_drop, hSlen]; exact Nat.min_eq_left (by omega)
      have hlen0 : (S.take 32).length = 32 := by
        rw [List.length_take, hSlen]; exact Nat.min_eq_left (by omega)
      have hlen33 : ((S.drop 33).take 32).length = 32 := by
        rw [List.length_take, List.length_drop, hSlen]; exact Nat.min_eq_left (by omega)
      have hlen32 : ((S.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop, hSlen]; exact Nat.min_eq_left (by omega)
      have hV0 : bytesToNat ((S.drop 3).take 32) < 2 ^ 256 := by
        have h := bytesToNat_lt ((S.drop 3).take 32)
        rwa [hlenB0, show (256 : Nat) ^ 32 = 2 ^ 256 from by decide] at h
      have hV1 : bytesToNat ((S.drop 35).take 32) < 2 ^ 256 := by
        have h := bytesToNat_lt ((S.drop 35).take 32)
        rwa [hlenB1, show (256 : Nat) ^ 32 = 2 ^ 256 from by decide] at h
      -- the header's two loads
      have read0 : readBytes s.mem (b + 64 * j) 32 = some ((S.drop 3).take 32) := by
        rw [hmem]
        have h := win_read_slice_len mem b (3 + 64 * i) W j 3 hW hb (by omega)
        rwa [show b + 64 * j + 3 - 3 = b + 64 * j from by omega] at h
      have read1 : readBytes s.mem (b + 64 * j + 32) 32 = some ((S.drop 35).take 32) := by
        rw [hmem]
        have h := win_read_slice_len mem b (3 + 64 * i) W j 35 hW hb (by omega)
        rwa [show b + 64 * j + 35 - 3 = b + 64 * j + 32 from by omega] at h
      obtain ⟨env1, hrun1, hP1, hU1, hB1, hptr1, h01, h11, h21, hcond1⟩ :=
        utf8ForBodyUs_run env s p opP opU opB b j prev u8k ((S.drop 3).take 32)
          ((S.drop 35).take 32) hpre hincP hincU hincB hopP hopU hopB hb' read0 read1 hj64
      have hframe := fun (nm : String) (hm : nm ∈ utf8Kept) =>
        denoteCode_kept utf8ForBodyUs.instrs env env1 s hrun1 utf8Kept_us nm hm
      have hdiv1 : lookupName env1 "%div44" = some (.int 64 (BitVec.ofNat 64 nb)) :=
        (hframe "%div44" (by decide)).trans hdiv
      have hb1 : lookupName env1 "%b" = some (.ptr b) := (hframe "%b" (by decide)).trans hb'
      have hstep1 : step utf8Calls utf8Function (withEnv env s)
          = execTerm (withEnv env1 s)
              (.condbr (.reg "%or.cond.us") "if.end14.us" "if.then11.us") :=
        step_of_utf8 _ "for.body.us" utf8ForBodyUs (withEnv env1 s) hpc findBlock_utf8ForBodyUs hrun1
      have hev1 : evalOperand (withEnv env1 s) (.reg "%or.cond.us")
          = some (.int 1 (utf8GateBit ((S.drop 3).take 32) ((S.drop 35).take 32) prev)) := by
        rw [evalOperand_reg_withEnv]
        exact hcond1
      have hpc1 : (withEnv env1 s).pc = "for.body.us" := hpc
      have hone : (BitVec.ofInt 64 1 : BitVec 64) = BitVec.ofNat 64 1 := by decide
      have hnext : BitVec.ofNat 64 j + BitVec.ofInt 64 1 = BitVec.ofNat 64 (j + 1) := by
        rw [hone, ofNat64_add_ofNat j 1 (by omega)]
      have hlt : j + 1 < nb := by omega
      have hbit : BitVec.ofNat 64 j + BitVec.ofInt 64 1 ≠ BitVec.ofNat 64 nb := by
        intro hc
        rw [hnext] at hc
        exact absurd (ofNat64_inj (by omega) (by omega) hc) (by omega)
      by_cases hskip : utf8GateBit ((S.drop 3).take 32) ((S.drop 35).take 32) prev = 1
      · -- the gate skips: the block's word and the fold are carried unchanged
        have hjump1 : step utf8Calls utf8Function (withEnv env s)
            = .jump (withEnv env1 { s with pc := "if.end14.us", pre := some "for.body.us" }) := by
          have h := hstep1
          rw [execTerm_condbr_true hev1 hskip, withEnv_setJmp, hpc1] at h
          exact h
        obtain ⟨env2, hrun2, hU2, hI2, hE2⟩ :=
          utf8EndUs_run env1 { s with pc := "if.end14.us", pre := some "for.body.us" }
            "for.body.us" (.reg "%u8k.076.us") u8k j nb rfl rfl
            (by rw [evalOperand_reg_withEnv]; exact hU1) hB1 hdiv1
        have hstep2 : step utf8Calls utf8Function
            (withEnv env1 { s with pc := "if.end14.us", pre := some "for.body.us" })
            = execTerm (withEnv env2 { s with pc := "if.end14.us", pre := some "for.body.us" })
                (.condbr (.reg "%exitcond79.not") "for.cond.cleanup" "for.body.us") :=
          step_of_utf8 _ "if.end14.us" utf8EndUs _ rfl findBlock_utf8EndUs hrun2
        have hev2 : evalOperand
            (withEnv env2 { s with pc := "if.end14.us", pre := some "for.body.us" })
            (.reg "%exitcond79.not")
            = some (.int 1 (BitVec.ofBool
                (BitVec.ofNat 64 j + BitVec.ofInt 64 1 = BitVec.ofNat 64 nb))) := by
          rw [evalOperand_reg_withEnv]
          exact hE2
        have hframe2 := fun (nm : String) (hm : nm ∈ utf8Kept) =>
          denoteCode_kept utf8EndUs.instrs env1 env2
            { s with pc := "if.end14.us", pre := some "for.body.us" } hrun2 utf8Kept_end nm hm
        have hjump2 : step utf8Calls utf8Function
            (withEnv env1 { s with pc := "if.end14.us", pre := some "for.body.us" })
            = .jump (withEnv env2
                { s with pc := "for.body.us", pre := some "if.end14.us" }) := by
          have h := hstep2
          rw [execTerm_condbr_false hev2 (ofBool_of_false hbit), withEnv_setJmp] at h
          exact h
        have hP2 : lookupName env2 "%2" = some (.int 32
            (ptestz (BitVec.ofNat 256 (packLanes (List.zipWith (· ||| ·)
              (unpackLanes 64 4 (bytesToNat ((S.drop 35).take 32)))
              (unpackLanes 64 4 (bytesToNat ((S.drop 3).take 32))))))
              (BitVec.ofNat 256 (packLanes highLanes64)))) := by
          refine (latch_keeps_two env1 env2
            { s with pc := "if.end14.us", pre := some "for.body.us" } hrun2).trans ?_
          simpa only [utf8ForBodyUs, reg, lit, splatOf, highBitMask, JsonUtf8IR.ptestz]
            using h21
        by_cases hr0 : r' = 0
        · have hji : j + 1 = i := by omega
          refine ⟨env2, ({ s with pc := "for.body.us", pre := some "if.end14.us" } : State),
            u8k, acc, _, 2, rfl, rfl, hmem, by omega, hP2, hU2, hu8klen, hacc, hu8kpack,
            (hframe2 "%b" (by decide)).trans hb1,
            (hframe2 "%div44" (by decide)).trans hdiv1, ?_, ?_⟩
          · rw [hI2, hnext, hji]
          · intro k
            rw [show 2 + k = ((1 + k) + 1) from by omega, runFuel_jump_utf8 hjump1,
              show 1 + k = k + 1 from by omega, runFuel_jump_utf8 hjump2]
        · have hr' : 1 ≤ r' := by omega
          obtain ⟨env3, s3, u8k3, acc3, prev3, t3, hpc3, hpre3, hmem3, ht3, hP3, hU3, hlen3,
            hacc3, hpack3, hb3, hdiv3, hinc3, hrun3⟩ :=
            ih (j + 1) env2 { s with pc := "for.body.us", pre := some "if.end14.us" }
              "if.end14.us" (.reg "%2") (.reg "%u8k.2.us") (.reg "%inc.us") u8k
              (ptestz (BitVec.ofNat 256 (packLanes (List.zipWith (· ||| ·)
                (unpackLanes 64 4 (bytesToNat ((S.drop 35).take 32)))
                (unpackLanes 64 4 (bytesToNat ((S.drop 3).take 32))))))
                (BitVec.ofNat 256 (packLanes highLanes64)))
              acc (by omega) (by omega) rfl rfl hmem rfl rfl rfl
              (by rw [evalOperand_reg_withEnv]; exact hP2)
              (by
                rw [evalOperand_reg_withEnv, lookupName_cons_ne _ _ (by decide)]
                exact hU2)
              (by
                rw [evalOperand_reg_withEnv, lookupName_cons_ne _ _ (by decide),
                  lookupName_cons_ne _ _ (by decide), hI2, hnext])
              ((hframe2 "%b" (by decide)).trans hb1)
              ((hframe2 "%div44" (by decide)).trans hdiv1)
              hacc hu8klen hu8kpack
          refine ⟨env3, s3, u8k3, acc3, prev3, 2 + t3, hpc3, hpre3, hmem3, by omega, hP3, hU3,
            hlen3, hacc3, hpack3, hb3, hdiv3, hinc3, ?_⟩
          intro k
          rw [show (2 + t3) + k = ((1 + t3) + k) + 1 from by omega,
            runFuel_jump_utf8 hjump1,
            show (1 + t3) + k = (t3 + k) + 1 from by omega,
            runFuel_jump_utf8 hjump2]
          exact hrun3 k
      · -- the gate does not skip: the DFA body runs, then the latch
        have hskip0 : utf8GateBit ((S.drop 3).take 32) ((S.drop 35).take 32) prev = 0 :=
          bit1_eq_zero_of_ne_one _ hskip
        have hjump1 : step utf8Calls utf8Function (withEnv env s)
            = .jump (withEnv env1 { s with pc := "if.then11.us", pre := some "for.body.us" }) := by
          have h := hstep1
          rw [execTerm_condbr_false hev1 hskip0, withEnv_setJmp, hpc1] at h
          exact h
        -- the body's six reads
        have read3 : readBytes s.mem (b + 64 * j - 1) 32 = some ((S.drop 2).take 32) := by
          rw [hmem]
          have h := win_read_slice_len mem b (3 + 64 * i) W j 2 hW hb (by omega)
          rwa [show b + 64 * j + 2 - 3 = b + 64 * j - 1 from by omega] at h
        have read4 : readBytes s.mem (b + 64 * j - 2) 32 = some ((S.drop 1).take 32) := by
          rw [hmem]
          have h := win_read_slice_len mem b (3 + 64 * i) W j 1 hW hb (by omega)
          rwa [show b + 64 * j + 1 - 3 = b + 64 * j - 2 from by omega] at h
        have read5 : readBytes s.mem (b + 64 * j - 3) 32 = some (S.take 32) := by
          rw [hmem]
          have h := win_read_slice_len mem b (3 + 64 * i) W j 0 hW hb (by omega)
          rwa [show b + 64 * j + 0 - 3 = b + 64 * j - 3 from by omega,
            show ((W.drop (64 * j)).drop 0).take 32 = (W.drop (64 * j)).take 32 from by rw [List.drop_zero]] at h
        have read19 : readBytes s.mem (b + 64 * j + 31) 32 = some ((S.drop 34).take 32) := by
          rw [hmem]
          have h := win_read_slice_len mem b (3 + 64 * i) W j 34 hW hb (by omega)
          rwa [show b + 64 * j + 34 - 3 = b + 64 * j + 31 from by omega] at h
        have read20 : readBytes s.mem (b + 64 * j + 30) 32 = some ((S.drop 33).take 32) := by
          rw [hmem]
          have h := win_read_slice_len mem b (3 + 64 * i) W j 33 hW hb (by omega)
          rwa [show b + 64 * j + 33 - 3 = b + 64 * j + 30 from by omega] at h
        have read21 : readBytes s.mem (b + 64 * j + 29) 32 = some ((S.drop 32).take 32) := by
          rw [hmem]
          have h := win_read_slice_len mem b (3 + 64 * i) W j 32 hW hb (by omega)
          rwa [show b + 64 * j + 32 - 3 = b + 64 * j + 29 from by omega] at h
        obtain ⟨envB, hrunB, hvalB⟩ :=
          utf8Gated_body env1 { s with pc := "if.then11.us", pre := some "for.body.us" }
            b j u8k ((S.drop 2).take 32) ((S.drop 1).take 32) (S.take 32)
            ((S.drop 34).take 32) ((S.drop 33).take 32) ((S.drop 32).take 32)
            (bytesToNat ((S.drop 3).take 32)) (bytesToNat ((S.drop 35).take 32))
            hU1 hptr1 h01 h11 hu8klen hV0 hV1 read3 read4 read5 read19 read20 read21 hb hj64
        let A := errRaw (byteLanes ((S.drop 1).take 32)) (byteLanes (S.take 32))
          (bytesToNat ((S.drop 2).take 32)) (bytesToNat ((S.drop 3).take 32))
        let Bv := errRaw (byteLanes ((S.drop 33).take 32)) (byteLanes ((S.drop 32).take 32))
          (bytesToNat ((S.drop 34).take 32)) (bytesToNat ((S.drop 35).take 32))
        let G := List.zipWith (· ||| ·) (List.zipWith (· ||| ·) A Bv) u8k
        have hvalG : lookupName envB "%or.i.us" = some (.vec 4 64 G) := hvalB
        have hlenA : A.length = 4 :=
          errRaw_length _ _ _ _ (len32_byteLanes _ hlen1) (len32_byteLanes _ hlen0)
        have hlenBv : Bv.length = 4 :=
          errRaw_length _ _ _ _ (len32_byteLanes _ hlen33) (len32_byteLanes _ hlen32)
        have hglen : G.length = 4 := by
          show (List.zipWith (· ||| ·) (List.zipWith (· ||| ·) A Bv) u8k).length = 4
          rw [List.length_zipWith, List.length_zipWith, hlenA, hlenBv, Nat.min_self, hu8klen,
            Nat.min_self]
        have hbiB : lookupName envB "%bi.075.us" = some (.int 64 (BitVec.ofNat 64 j)) :=
          (denoteCode_lookupName_of_not_dst utf8ThenUs.instrs env1 envB
            { s with pc := "if.then11.us", pre := some "for.body.us" } "%bi.075.us"
            (by decide) hrunB).trans hB1
        have hbB : lookupName envB "%b" = some (.ptr b) :=
          (denoteCode_kept utf8ThenUs.instrs env1 envB
            { s with pc := "if.then11.us", pre := some "for.body.us" } hrunB utf8Kept_then
            "%b" (by decide)).trans hb1
        have hdivB : lookupName envB "%div44" = some (.int 64 (BitVec.ofNat 64 nb)) :=
          (denoteCode_kept utf8ThenUs.instrs env1 envB
            { s with pc := "if.then11.us", pre := some "for.body.us" } hrunB utf8Kept_then
            "%div44" (by decide)).trans hdiv1
        obtain ⟨env2, hrun2, hU2, hI2, hE2⟩ :=
          utf8EndUs_run envB { s with pc := "if.end14.us", pre := some "if.then11.us" }
            "if.then11.us" (.reg "%or.i.us") G j nb rfl rfl
            (by rw [evalOperand_reg_withEnv]; exact hvalG) hbiB hdivB
        have hstep2 : step utf8Calls utf8Function
            (withEnv envB { s with pc := "if.end14.us", pre := some "if.then11.us" })
            = execTerm (withEnv env2 { s with pc := "if.end14.us", pre := some "if.then11.us" })
                (.condbr (.reg "%exitcond79.not") "for.cond.cleanup" "for.body.us") :=
          step_of_utf8 _ "if.end14.us" utf8EndUs _ rfl findBlock_utf8EndUs hrun2
        have hstepB : step utf8Calls utf8Function
            (withEnv env1 { s with pc := "if.then11.us", pre := some "for.body.us" })
            = .jump (withEnv envB { s with pc := "if.end14.us", pre := some "if.then11.us" }) :=
          step_of_utf8 _ "if.then11.us" utf8ThenUs _ rfl findBlock_utf8ThenUs hrunB
        have hev2 : evalOperand
            (withEnv env2 { s with pc := "if.end14.us", pre := some "if.then11.us" })
            (.reg "%exitcond79.not")
            = some (.int 1 (BitVec.ofBool
                (BitVec.ofNat 64 j + BitVec.ofInt 64 1 = BitVec.ofNat 64 nb))) := by
          rw [evalOperand_reg_withEnv]
          exact hE2
        have hframe2 := fun (nm : String) (hm : nm ∈ utf8Kept) =>
          denoteCode_kept utf8EndUs.instrs envB env2
            { s with pc := "if.end14.us", pre := some "if.then11.us" } hrun2 utf8Kept_end nm hm
        have hjump2 : step utf8Calls utf8Function
            (withEnv envB { s with pc := "if.end14.us", pre := some "if.then11.us" })
            = .jump (withEnv env2
                { s with pc := "for.body.us", pre := some "if.end14.us" }) := by
          have h := hstep2
          rw [execTerm_condbr_false hev2 (ofBool_of_false hbit), withEnv_setJmp] at h
          exact h
        have hP2 : lookupName env2 "%2" = some (.int 32
            (ptestz (BitVec.ofNat 256 (packLanes (List.zipWith (· ||| ·)
              (unpackLanes 64 4 (bytesToNat ((S.drop 35).take 32)))
              (unpackLanes 64 4 (bytesToNat ((S.drop 3).take 32))))))
              (BitVec.ofNat 256 (packLanes highLanes64)))) := by
          refine (latch_keeps_two envB env2
            { s with pc := "if.end14.us", pre := some "if.then11.us" } hrun2).trans ?_
          refine (denoteCode_lookupName_of_not_dst utf8ThenUs.instrs env1 envB
            { s with pc := "if.then11.us", pre := some "for.body.us" } "%2" (by decide) hrunB).trans ?_
          simpa only [utf8ForBodyUs, reg, lit, splatOf, highBitMask, JsonUtf8IR.ptestz]
            using h21
        obtain ⟨accG, haccG, hpackG⟩ := packLanes_fits G hglen
        by_cases hr0 : r' = 0
        · have hji : j + 1 = i := by omega
          refine ⟨env2, ({ s with pc := "for.body.us", pre := some "if.end14.us" } : State),
            G, accG, _, 3, rfl, rfl, hmem, by omega, hP2, hU2, hglen, haccG, hpackG,
            (hframe2 "%b" (by decide)).trans hbB,
            (hframe2 "%div44" (by decide)).trans hdivB, ?_, ?_⟩
          · rw [hI2, hnext, hji]
          · intro k
            rw [show 3 + k = ((2 + k) + 1) from by omega, runFuel_jump_utf8 hjump1,
              show 2 + k = ((1 + k) + 1) from by omega, runFuel_jump_utf8 hstepB,
              show 1 + k = k + 1 from by omega, runFuel_jump_utf8 hjump2]
        · have hr' : 1 ≤ r' := by omega
          obtain ⟨env3, s3, u8k3, acc3, prev3, t3, hpc3, hpre3, hmem3, ht3, hP3, hU3, hlen3,
            hacc3, hpack3, hb3, hdiv3, hinc3, hrun3⟩ :=
            ih (j + 1) env2 { s with pc := "for.body.us", pre := some "if.end14.us" }
              "if.end14.us" (.reg "%2") (.reg "%u8k.2.us") (.reg "%inc.us") G
              (ptestz (BitVec.ofNat 256 (packLanes (List.zipWith (· ||| ·)
                (unpackLanes 64 4 (bytesToNat ((S.drop 35).take 32)))
                (unpackLanes 64 4 (bytesToNat ((S.drop 3).take 32))))))
                (BitVec.ofNat 256 (packLanes highLanes64)))
              accG (by omega) (by omega) rfl rfl hmem rfl rfl rfl
              (by rw [evalOperand_reg_withEnv]; exact hP2)
              (by
                rw [evalOperand_reg_withEnv, lookupName_cons_ne _ _ (by decide)]
                exact hU2)
              (by
                rw [evalOperand_reg_withEnv, lookupName_cons_ne _ _ (by decide),
                  lookupName_cons_ne _ _ (by decide), hI2, hnext])
              ((hframe2 "%b" (by decide)).trans hbB)
              ((hframe2 "%div44" (by decide)).trans hdivB)
              haccG hglen hpackG
          refine ⟨env3, s3, u8k3, acc3, prev3, 3 + t3, hpc3, hpre3, hmem3, by omega, hP3, hU3,
            hlen3, hacc3, hpack3, hb3, hdiv3, hinc3, ?_⟩
          intro k
          rw [show (3 + t3) + k = ((2 + t3) + k) + 1 from by omega,
            runFuel_jump_utf8 hjump1,
            show (2 + t3) + k = ((1 + t3) + k) + 1 from by omega,
            runFuel_jump_utf8 hstepB,
            show (1 + t3) + k = (t3 + k) + 1 from by omega,
            runFuel_jump_utf8 hjump2]
          exact hrun3 k

/-! ### The companion

The statement `utf8StageUndefinedStatement` is read at the pinned body: the
window's unreadable byte has a least position, whose block index is below the
block count; the prefix the earlier blocks read reads back; whichever loop the
gate parameter selects reaches that block's header, whose two loads are the
instructions that refuse; and the run is `ub`.  The fuel bound is `fuelOf nb`,
which is why the two loops' per-block budgets and the five steps around them fit.
-/
theorem initState_utf8_pc (b n : Nat) (u : BitVec 32) :
    (initState utf8Function [.ptr b, .int 64 (BitVec.ofNat 64 n), .int 32 u]).pc = "entry" := rfl

theorem lookupName_initState_utf8 (b n : Nat) (u : BitVec 32) :
    lookupName (initState utf8Function
      [.ptr b, .int 64 (BitVec.ofNat 64 n), .int 32 u]).env "%b" = some (.ptr b) ∧
    lookupName (initState utf8Function
      [.ptr b, .int 64 (BitVec.ofNat 64 n), .int 32 u]).env "%n"
        = some (.int 64 (BitVec.ofNat 64 n)) ∧
    lookupName (initState utf8Function
      [.ptr b, .int 64 (BitVec.ofNat 64 n), .int 32 u]).env "%ungated"
        = some (.int 32 u) := by
  have hbn : ¬ ("%b" = "%n") := by decide
  have hbu : ¬ ("%b" = "%ungated") := by decide
  have hnu : ¬ ("%n" = "%ungated") := by decide
  refine ⟨?_, ?_, ?_⟩
  · simp only [initState, utf8Function, List.map, List.zip, List.zipWith, lookupName, ite_true]
  · simp only [initState, utf8Function, List.map, List.zip, List.zipWith, lookupName]
    rw [ite_eq_right hbn, ite_true]
  · simp only [initState, utf8Function, List.map, List.zip, List.zipWith, lookupName]
    rw [ite_eq_right hbu, ite_eq_right hnu, ite_true]

theorem utf8_stage_undefined_of_no_read : utf8StageUndefinedStatement := by
  intro bs n nb mem b ungated w hn hnb hb hlen haddr hpos hpre hpad hw hbad
  have hnbpos : 0 < nb := by
    rw [hnb]
    exact Nat.div_pos (by omega) (by decide)
  have hnb64 : nb < 2 ^ 64 := by
    have h := Nat.div_le_self (n + 63) 64
    omega
  have hspan : 64 * (nb - 1) < 2 ^ 63 := utf8SpanBound n nb hnb haddr hpos
  -- the least unreadable block, and the prefix the blocks before it read
  obtain ⟨i, jb, hib, hjb, hbadbyte, hblkread⟩ :=
    utf8_least_unreadable_block mem b n nb w hb hnb hpre hpad hw hbad
  obtain ⟨W, hW⟩ := prefix_readable_bytes mem b i hb hpre hblkread
  -- the initial state, and the two steps before the loop
  let s0 : State := { (initState utf8Function
    [.ptr b, .int 64 (BitVec.ofNat 64 n),
      .int 32 (BitVec.ofNat 32 (if ungated then 1 else 0))]) with mem := mem }
  obtain ⟨hini_b, hini_n, hini_u⟩ :=
    lookupName_initState_utf8 b n (BitVec.ofNat 32 (if ungated then 1 else 0))
  have hpc0 : s0.pc = "entry" :=
    initState_utf8_pc b n (BitVec.ofNat 32 (if ungated then 1 else 0))
  obtain ⟨env1, hrun1, hdiv1, hcmp1⟩ := utf8Entry_run s0.env s0 n hini_n
  have hkeep1 := fun (nm : String) (hm : ∀ i ∈ utf8Entry.instrs, i.dst? ≠ some nm) =>
    denoteCode_lookupName_of_not_dst utf8Entry.instrs s0.env env1 s0 nm hm hrun1
  have hb1 : lookupName env1 "%b" = some (.ptr b) := (hkeep1 "%b" (by decide)).trans hini_b
  have hn1 : lookupName env1 "%n" = some (.int 64 (BitVec.ofNat 64 n)) :=
    (hkeep1 "%n" (by decide)).trans hini_n
  have hu1 : lookupName env1 "%ungated"
      = some (.int 32 (BitVec.ofNat 32 (if ungated then 1 else 0))) :=
    (hkeep1 "%ungated" (by decide)).trans hini_u
  have hdiv1' : lookupName env1 "%div44" = some (.int 64 (BitVec.ofNat 64 nb)) := by
    rw [hdiv1, div44_ofNat n nb hlen hnb]
  have hev0 : evalOperand (withEnv env1 s0) (.reg "%cmp74.not")
      = some (.int 1 (BitVec.ofBool
          ((BitVec.ofNat 64 n + BitVec.ofInt 64 63).ult (BitVec.ofInt 64 64)))) := by
    rw [evalOperand_reg_withEnv]
    exact hcmp1
  have hguard : BitVec.ofBool
      ((BitVec.ofNat 64 n + BitVec.ofInt 64 63).ult (BitVec.ofInt 64 64)) = 0 := by
    rw [ofNat64_add63 n hlen,
      show (BitVec.ofInt 64 64 : BitVec 64) = BitVec.ofNat 64 64 from by decide,
      ofNat64_ult_false (n + 63) 64 hlen (by decide) (by omega)]
    rfl
  let s1 : State := { s0 with pc := "for.body.lr.ph", pre := some "entry" }
  have hstep0 : step utf8Calls utf8Function s0
      = execTerm (withEnv env1 s0)
          (.condbr (.reg "%cmp74.not") "for.cond.cleanup" "for.body.lr.ph") :=
    step_of_utf8 s0 "entry" utf8Entry (withEnv env1 s0) hpc0 findBlock_utf8Entry hrun1
  have hjump0 : step utf8Calls utf8Function s0 = .jump (withEnv env1 s1) := by
    rw [hstep0, execTerm_condbr_false hev0 hguard, withEnv_setJmp, withEnv_pc, hpc0]
  obtain ⟨env2, hrun2, htb⟩ :=
    utf8LrPh_run env1 s1 (BitVec.ofNat 32 (if ungated then 1 else 0)) hu1
  have hkeep2 := fun (nm : String) (hm : ∀ i ∈ utf8LrPh.instrs, i.dst? ≠ some nm) =>
    denoteCode_lookupName_of_not_dst utf8LrPh.instrs env1 env2 s1 nm hm hrun2
  have hb2 : lookupName env2 "%b" = some (.ptr b) := (hkeep2 "%b" (by decide)).trans hb1
  have hdiv2 : lookupName env2 "%div44" = some (.int 64 (BitVec.ofNat 64 nb)) :=
    (hkeep2 "%div44" (by decide)).trans hdiv1'
  have hev1 : evalOperand (withEnv env2 s1) (.reg "%tobool.not")
      = some (.int 1 (BitVec.ofBool
          (BitVec.ofNat 32 (if ungated then 1 else 0) = BitVec.ofInt 32 0))) := by
    rw [evalOperand_reg_withEnv]
    exact htb
  have hbi64 : 64 * i < 2 ^ 63 := by
    have h1 : i ≤ nb - 1 := by omega
    have h2 := Nat.mul_le_mul_left 64 h1
    omega
  have hpack0 : packLanes (unpackLanes 64 4 0) = bytesToNat (List.replicate 32 0x00) := by
    rw [packLanes_unpackLanes]
    have hz : bytesToNat (List.replicate 32 0x00) = 0 :=
      (bytesToNat_eq_zero_iff _).mpr (by intro x hx; simpa using hx)
    rw [hz]
  -- the gate's two values, each to its loop
  by_cases hg : ungated = true
  · -- the free loop: `%tobool.not` is false, so `for.body`
    have hbit : BitVec.ofBool
        (BitVec.ofNat 32 (if ungated then 1 else 0) = BitVec.ofInt 32 0) = 0 := by
      refine ofBool_of_false (fun hc => ?_)
      rw [show (if ungated then 1 else 0) = 1 from by simp [hg]] at hc
      exact absurd hc (by decide)
    let s2 : State := { s1 with pc := "for.body", pre := some "for.body.lr.ph" }
    have hstep1 : step utf8Calls utf8Function (withEnv env1 s1)
        = execTerm (withEnv env2 s1)
            (.condbr (.reg "%tobool.not") "for.body.us" "for.body") :=
      step_of_utf8 (withEnv env1 s1) "for.body.lr.ph" utf8LrPh (withEnv env2 s1) rfl
        findBlock_utf8LrPh hrun2
    have hjump1 : step utf8Calls utf8Function (withEnv env1 s1) = .jump (withEnv env2 s2) := by
      rw [hstep1, execTerm_condbr_false hev1 hbit, withEnv_setJmp, withEnv_pc]
    by_cases hi0 : i = 0
    · -- the first block is the one that cannot be read
      have hbad0 : ∃ j, j < 64 ∧ readByte s2.mem (b + 64 * 0 + j) = none := by
        refine ⟨jb, hjb, ?_⟩
        rw [← hi0]
        exact hbadbyte
      have hnone := utf8ForBody_denote_none env2 s2 b 0 (unpackLanes 64 4 0) "for.body.lr.ph"
        (.imm (.splat 4 64 (BitVec.ofInt 64 0))) (.imm (.int 64 (BitVec.ofInt 64 0)))
        rfl rfl rfl (utf8Ungated_preheader_operands s2).1
        (utf8Ungated_preheader_operands s2).2 hb2 hbad0 (by decide : 64 * 0 < 2 ^ 63)
      have hub : step utf8Calls utf8Function (withEnv env2 s2) = .ub :=
        step_ub_utf8 (withEnv env2 s2) "for.body" utf8ForBody rfl findBlock_utf8ForBody hnone
      have hrun : runFuel utf8Calls 3 utf8Function s0 = some .ub := by
        rw [show 3 = (1 + 1) + 1 from rfl, runFuel_jump_utf8 hjump0,
          runFuel_jump_utf8 hjump1]
        simp [runFuel, hub]
      rw [fuelOf_eq]
      exact runFuel_mono_le (by omega) hrun
    · have hi_pos : 0 < i := by omega
      obtain ⟨env3, s3, u8k3, acc3, hpc3, hpre3, hmem3, hval3, hlen3, hacc3, hpack3, hb3,
        hdiv3, hinc3, hrun3⟩ :=
        utf8Ungated_reach nb b i mem W hW hb hib hnb64 hspan
          i 0 env2 s2 "for.body.lr.ph"
          (.imm (.splat 4 64 (BitVec.ofInt 64 0))) (.imm (.int 64 (BitVec.ofInt 64 0)))
          (unpackLanes 64 4 0) (List.replicate 32 0x00)
          (by omega) hi_pos rfl rfl rfl rfl rfl
          (utf8Ungated_preheader_operands s2).1
          (utf8Ungated_preheader_operands s2).2
          hb2 hdiv2 (by simp) (by rw [unpackLanes_length]) hpack0
      have hbad3 : ∃ j, j < 64 ∧ readByte s3.mem (b + 64 * i + j) = none := by
        refine ⟨jb, hjb, ?_⟩
        rw [hmem3]
        exact hbadbyte
      have hnone := utf8ForBody_denote_none env3 s3 b i u8k3 "for.body"
        (.reg "%or.i47") (.reg "%inc") hpre3 rfl rfl
        (by rw [evalOperand_reg_withEnv]; exact hval3)
        (by
          rw [evalOperand_reg_withEnv, lookupName_cons_ne _ _ (by decide)]
          exact hinc3)
        hb3 hbad3 hbi64
      have hub : step utf8Calls utf8Function (withEnv env3 s3) = .ub :=
        step_ub_utf8 (withEnv env3 s3) "for.body" utf8ForBody
          (by rw [withEnv_pc]; exact hpc3) findBlock_utf8ForBody hnone
      have hrun : runFuel utf8Calls (i + 3) utf8Function s0 = some .ub := by
        rw [show i + 3 = (i + 1 + 1) + 1 from by omega, runFuel_jump_utf8 hjump0,
          show i + 1 + 1 = (i + 1) + 1 from by omega, runFuel_jump_utf8 hjump1,
          hrun3 1]
        simp [runFuel, hub]
      rw [fuelOf_eq]
      exact runFuel_mono_le (by omega) hrun
  · -- the gated loop: `%tobool.not` is true, so `for.body.us`
    have hgf : ungated = false := by cases ungated <;> simp_all
    have hbit : BitVec.ofBool
        (BitVec.ofNat 32 (if ungated then 1 else 0) = BitVec.ofInt 32 0) = 1 := by
      refine ofBool_of_true ?_
      rw [show (if ungated then 1 else 0) = 0 from by simp [hgf]]
      decide
    let s2 : State := { s1 with pc := "for.body.us", pre := some "for.body.lr.ph" }
    have hstep1 : step utf8Calls utf8Function (withEnv env1 s1)
        = execTerm (withEnv env2 s1)
            (.condbr (.reg "%tobool.not") "for.body.us" "for.body") :=
      step_of_utf8 (withEnv env1 s1) "for.body.lr.ph" utf8LrPh (withEnv env2 s1) rfl
        findBlock_utf8LrPh hrun2
    have hjump1 : step utf8Calls utf8Function (withEnv env1 s1) = .jump (withEnv env2 s2) := by
      rw [hstep1, execTerm_condbr_true hev1 hbit, withEnv_setJmp, withEnv_pc]
    by_cases hi0 : i = 0
    · -- the first block is the one that cannot be read
      have hbad0 : ∃ j, j < 64 ∧ readByte s2.mem (b + 64 * 0 + j) = none := by
        refine ⟨jb, hjb, ?_⟩
        rw [← hi0]
        exact hbadbyte
      have hnone := utf8ForBodyUs_denote_none env2 s2 "for.body.lr.ph"
        (.imm (.int 32 (BitVec.ofInt 32 1)))
        (.imm (.splat 4 64 (BitVec.ofInt 64 0)))
        (.imm (.int 64 (BitVec.ofInt 64 0)))
        b 0 (BitVec.ofInt 32 1) (unpackLanes 64 4 0) rfl rfl rfl rfl rfl
        (utf8Ungated_preheader_operands s2).1
        (utf8Ungated_preheader_operands s2).2
        hb2 hbad0 (by decide : 64 * 0 < 2 ^ 63)
      have hub : step utf8Calls utf8Function (withEnv env2 s2) = .ub :=
        step_ub_utf8 (withEnv env2 s2) "for.body.us" utf8ForBodyUs rfl
          findBlock_utf8ForBodyUs hnone
      have hrun : runFuel utf8Calls 3 utf8Function s0 = some .ub := by
        rw [show 3 = (1 + 1) + 1 from rfl, runFuel_jump_utf8 hjump0,
          runFuel_jump_utf8 hjump1]
        simp [runFuel, hub]
      rw [fuelOf_eq]
      exact runFuel_mono_le (by omega) hrun
    · have hi_pos : 0 < i := by omega
      obtain ⟨env3, s3, u8k3, acc3, prev3, t, hpc3, hpre3, hmem3, ht, hP3, hU3, hlen3, hacc3,
        hpack3, hb3, hdiv3, hinc3, hrun3⟩ :=
        utf8Gated_reach nb b i mem W hW hb hib hnb64 hspan
          i 0 env2 s2 "for.body.lr.ph"
          (.imm (.int 32 (BitVec.ofInt 32 1)))
          (.imm (.splat 4 64 (BitVec.ofInt 64 0)))
          (.imm (.int 64 (BitVec.ofInt 64 0)))
          (unpackLanes 64 4 0) (BitVec.ofInt 32 1) (List.replicate 32 0x00)
          (by omega) hi_pos rfl rfl rfl rfl rfl rfl
          (by rfl) (utf8Ungated_preheader_operands s2).1
          (utf8Ungated_preheader_operands s2).2
          hb2 hdiv2 (by simp) (by rw [unpackLanes_length]) hpack0
      have hbad3 : ∃ j, j < 64 ∧ readByte s3.mem (b + 64 * i + j) = none := by
        refine ⟨jb, hjb, ?_⟩
        rw [hmem3]
        exact hbadbyte
      have hnone := utf8ForBodyUs_denote_none env3 s3 "if.end14.us"
        (.reg "%2") (.reg "%u8k.2.us") (.reg "%inc.us") b i prev3 u8k3 hpre3 rfl rfl rfl
        (by rw [evalOperand_reg_withEnv]; exact hP3)
        (by
          rw [evalOperand_reg_withEnv, lookupName_cons_ne _ _ (by decide)]
          exact hU3)
        (by
          rw [evalOperand_reg_withEnv, lookupName_cons_ne _ _ (by decide),
            lookupName_cons_ne _ _ (by decide)]
          exact hinc3)
        hb3 hbad3 hbi64
      have hub : step utf8Calls utf8Function (withEnv env3 s3) = .ub :=
        step_ub_utf8 (withEnv env3 s3) "for.body.us" utf8ForBodyUs
          (by rw [withEnv_pc]; exact hpc3) findBlock_utf8ForBodyUs hnone
      have hrun : runFuel utf8Calls (t + 3) utf8Function s0 = some .ub := by
        rw [show t + 3 = (t + 1 + 1) + 1 from by omega, runFuel_jump_utf8 hjump0,
          show t + 1 + 1 = (t + 1) + 1 from by omega, runFuel_jump_utf8 hjump1,
          hrun3 1]
        simp [runFuel, hub]
      rw [fuelOf_eq]
      exact runFuel_mono_le (by omega) hrun

end LeanLLVM.Refinement.JsonUtf8Steps

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonUtf8Steps
open LeanLLVM.Refinement.JsonUtf8Spec
open LeanLLVM.Refinement.JsonUtf8IR
open LeanLLVM.Refinement.JsonEntrySteps
namespace LeanLLVM.Refinement.JsonUtf8Steps

theorem literal_append_bytes (l m : List UInt8) :
    ByteString.literal (l ++ m) = ByteString.literal l ++ ByteString.literal m := by
  apply ByteString.eq_of_toList_eq
  rw [ByteString.toList_append, ByteString.toList_literal, ByteString.toList_literal,
    ByteString.toList_literal]

/-- Appending bytes to both sides of a span. -/
theorem utf8Spans_append_right {a r d : Bytes} (h : Utf8Spans a r) :
    Utf8Spans (a ++ d) (r ++ d) := by
  induction h with
  | nil t => exact Utf8Spans.nil (t ++ d)
  | char hc hr ih =>
      cases hc with
      | one hx =>
          rw [ByteString.cons_append]
          exact Utf8Spans.char (Utf8Char.one (rest := _ ++ d) hx) ih
      | two h0 h0' h1 h1' =>
          rw [ByteString.cons_append, ByteString.cons_append]
          exact Utf8Spans.char (Utf8Char.two (rest := _ ++ d) h0 h0' h1 h1') ih
      | three₀ h1 h1' h2 h2' =>
          rw [ByteString.cons_append, ByteString.cons_append, ByteString.cons_append]
          exact Utf8Spans.char (Utf8Char.three₀ (rest := _ ++ d) h1 h1' h2 h2') ih
      | three₁ h0 h0' h1 h1' h2 h2' =>
          rw [ByteString.cons_append, ByteString.cons_append, ByteString.cons_append]
          exact Utf8Spans.char (Utf8Char.three₁ (rest := _ ++ d) h0 h0' h1 h1' h2 h2') ih
      | three₂ h1 h1' h2 h2' =>
          rw [ByteString.cons_append, ByteString.cons_append, ByteString.cons_append]
          exact Utf8Spans.char (Utf8Char.three₂ (rest := _ ++ d) h1 h1' h2 h2') ih
      | three₃ h0 h0' h1 h1' h2 h2' =>
          rw [ByteString.cons_append, ByteString.cons_append, ByteString.cons_append]
          exact Utf8Spans.char (Utf8Char.three₃ (rest := _ ++ d) h0 h0' h1 h1' h2 h2') ih
      | four₀ h1 h1' h2 h2' h3 h3' =>
          rw [ByteString.cons_append, ByteString.cons_append, ByteString.cons_append,
            ByteString.cons_append]
          exact Utf8Spans.char (Utf8Char.four₀ (rest := _ ++ d) h1 h1' h2 h2' h3 h3') ih
      | four₁ h0 h0' h1 h1' h2 h2' h3 h3' =>
          rw [ByteString.cons_append, ByteString.cons_append, ByteString.cons_append,
            ByteString.cons_append]
          exact Utf8Spans.char (Utf8Char.four₁ (rest := _ ++ d) h0 h0' h1 h1' h2 h2' h3 h3') ih
      | four₂ h1 h1' h2 h2' h3 h3' =>
          rw [ByteString.cons_append, ByteString.cons_append, ByteString.cons_append,
            ByteString.cons_append]
          exact Utf8Spans.char (Utf8Char.four₂ (rest := _ ++ d) h1 h1' h2 h2' h3 h3') ih

/-- Two spans compose. -/
theorem utf8Spans_trans {a r s : Bytes} (h1 : Utf8Spans a r) (h2 : Utf8Spans r s) :
    Utf8Spans a s := by
  induction h1 with
  | nil t => exact h2
  | char hc hr ih => exact Utf8Spans.char hc (ih h2)

/-- A run of zero bytes is a complete document. -/
theorem utf8Spans_replicate_zero (p : Nat) :
    Utf8Spans (ByteString.literal (List.replicate p (0x00 : UInt8))) ByteString.empty := by
  induction p with
  | zero => exact Utf8Spans.nil ByteString.empty
  | succ p ih =>
      rw [List.replicate_succ]
      rw [ByteString.literal_cons]
      exact Utf8Spans.char (Utf8Char.one (by decide)) ih

theorem peel_byte (u : List UInt8) (b0 : UInt8) (rest : List UInt8)
    (h : u ++ [0x00] = b0 :: rest) :
    (u = [] ∧ rest = [] ∧ b0 = 0x00) ∨ ∃ t, u = b0 :: t ∧ rest = t ++ [0x00] := by
  rcases List.append_eq_cons_iff.mp h with ⟨rfl, h⟩ | ⟨t, rfl, ht⟩
  · left
    have h' : ([0x00] : List UInt8) = b0 :: rest := h
    simp only [List.cons.injEq, List.nil_eq] at h'
    exact ⟨rfl, h'.2, h'.1.symm⟩
  · exact Or.inr ⟨t, rfl, ht⟩

theorem peel_list : ∀ (bs : List UInt8) (u rest : List UInt8),
    u ++ [0x00] = bs ++ rest →
    (∃ t, u = bs ++ t ∧ rest = t ++ [0x00]) ∨ (u ++ [0x00] = bs ∧ rest = []) := by
  intro bs
  induction bs with
  | nil =>
      intro u rest h
      exact Or.inl ⟨u, rfl, h.symm⟩
  | cons b bs ih =>
      intro u rest h
      rcases peel_byte u b (bs ++ rest) h with ⟨hu, hrest, -⟩ | ⟨t, hu, ht⟩
      · obtain ⟨hbs, hrest'⟩ := List.append_eq_nil_iff.mp hrest
        right
        refine ⟨?_, hrest'⟩
        simpa [hu, hbs, hrest'] using h
      · rcases ih t rest ht.symm with ⟨t', ht', hrest⟩ | ⟨ht', hrest⟩
        · left
          exact ⟨t', by rw [hu, ht']; rfl, hrest⟩
        · right
          refine ⟨?_, hrest⟩
          rw [hu]
          rw [show b :: t ++ [0x00] = b :: (t ++ [0x00]) from rfl, ht']

theorem getLast_append_singleton_zero (u bs : List UInt8) (h : u ++ [0x00] = bs) :
    bs.getLast? = some 0x00 := by
  have := congrArg List.getLast? h
  rw [List.getLast?_append] at this
  simpa using this.symm

theorem utf8Spans_strip_zero_tail (u : List UInt8) :
    Utf8Spans (ByteString.literal (u ++ [0x00])) ByteString.empty →
      Utf8Spans (ByteString.literal u) ByteString.empty := by
  suffices H : ∀ k, ∀ u : List UInt8, u.length = k →
      Utf8Spans (ByteString.literal (u ++ [0x00])) ByteString.empty →
      Utf8Spans (ByteString.literal u) ByteString.empty from
    fun h => H u.length u rfl h
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro u hk h
    rcases utf8Spans_cases h with hnil | ⟨b', c, hc, hr⟩
    · exfalso
      have h1 := congrArg ByteArray.toList hnil
      simp only [ByteString.toList_empty, ByteString.toList_literal] at h1
      have h2 := congrArg List.length h1
      simp only [List.length_nil, List.length_append, List.length_cons] at h2
      omega
    · generalize hb : ByteString.literal (u ++ [0x00]) = b2 at hc
      cases hc with
      | one hx =>
          rename_i c0
          have hb' : u ++ [0x00] = c0 :: b'.toList := by
            have := congrArg ByteArray.toList hb
            simpa [ByteString.toList_literal, ByteString.toList_cons] using this
          rcases peel_list [c0] u b'.toList hb' with ⟨t, hu, hrt⟩ | ⟨hu, hrt⟩
          · have hrest : b' = ByteString.literal (t ++ [0x00]) := by
              apply ByteString.eq_of_toList_eq
              rw [ByteString.toList_literal]
              exact hrt
            have hlt : t.length < k := by
              rw [← hk, hu]
              simp only [List.length_append, List.length_cons, List.length_nil]
              omega
            have hr' : Utf8Spans (ByteString.literal (t ++ [0x00])) ByteString.empty :=
              hrest ▸ hr
            have hrec := ih t.length hlt t rfl hr'
            rw [hu, literal_append_bytes]
            simp only [ByteString.literal_cons, ByteString.cons_append]
            exact Utf8Spans.char (Utf8Char.one (rest := ByteString.literal t) hx) hrec
          · have hlen : u.length = 0 := by
              have := congrArg List.length hu
              simp only [List.length_append, List.length_cons, List.length_nil] at this
              omega
            have hu0 : u = [] := List.eq_nil_of_length_eq_zero hlen
            rw [hu0]
            exact Utf8Spans.nil ByteString.empty
      | two h0 h0' h1 h1' =>
          rename_i c0 c1
          have hb' : u ++ [0x00] = c0 :: c1 :: b'.toList := by
            have := congrArg ByteArray.toList hb
            simpa [ByteString.toList_literal, ByteString.toList_cons] using this
          rcases peel_list [c0, c1] u b'.toList hb' with ⟨t, hu, hrt⟩ | ⟨hu, hrt⟩
          · have hrest : b' = ByteString.literal (t ++ [0x00]) := by
              apply ByteString.eq_of_toList_eq
              rw [ByteString.toList_literal]
              exact hrt
            have hlt : t.length < k := by
              rw [← hk, hu]
              simp only [List.length_append, List.length_cons, List.length_nil]
              omega
            have hr' : Utf8Spans (ByteString.literal (t ++ [0x00])) ByteString.empty :=
              hrest ▸ hr
            have hrec := ih t.length hlt t rfl hr'
            rw [hu, literal_append_bytes]
            simp only [ByteString.literal_cons, ByteString.cons_append]
            exact Utf8Spans.char (Utf8Char.two (rest := ByteString.literal t) h0 h0' h1 h1') hrec
          · exfalso
            have hl := getLast_append_singleton_zero u [c0, c1] hu
            simp only [List.getLast?_cons_cons, List.getLast?_singleton,
              Option.some.injEq] at hl
            rw [hl] at h1
            exact absurd h1 (by decide)
      | three₀ h1 h1' h2 h2' =>
          rename_i c1 c2
          have hb' : u ++ [0x00] = 0xE0 :: c1 :: c2 :: b'.toList := by
            have := congrArg ByteArray.toList hb
            simpa [ByteString.toList_literal, ByteString.toList_cons] using this
          rcases peel_list [0xE0, c1, c2] u b'.toList hb' with ⟨t, hu, hrt⟩ | ⟨hu, hrt⟩
          · have hrest : b' = ByteString.literal (t ++ [0x00]) := by
              apply ByteString.eq_of_toList_eq
              rw [ByteString.toList_literal]
              exact hrt
            have hlt : t.length < k := by
              rw [← hk, hu]
              simp only [List.length_append, List.length_cons, List.length_nil]
              omega
            have hr' : Utf8Spans (ByteString.literal (t ++ [0x00])) ByteString.empty :=
              hrest ▸ hr
            have hrec := ih t.length hlt t rfl hr'
            rw [hu, literal_append_bytes]
            simp only [ByteString.literal_cons, ByteString.cons_append]
            exact Utf8Spans.char (Utf8Char.three₀ (rest := ByteString.literal t) h1 h1' h2 h2') hrec
          · exfalso
            have hl := getLast_append_singleton_zero u [0xE0, c1, c2] hu
            simp only [List.getLast?_cons_cons, List.getLast?_singleton,
              Option.some.injEq] at hl
            rw [hl] at h2
            exact absurd h2 (by decide)
      | three₁ h0 h0' h1 h1' h2 h2' =>
          rename_i c0 c1 c2
          have hb' : u ++ [0x00] = c0 :: c1 :: c2 :: b'.toList := by
            have := congrArg ByteArray.toList hb
            simpa [ByteString.toList_literal, ByteString.toList_cons] using this
          rcases peel_list [c0, c1, c2] u b'.toList hb' with ⟨t, hu, hrt⟩ | ⟨hu, hrt⟩
          · have hrest : b' = ByteString.literal (t ++ [0x00]) := by
              apply ByteString.eq_of_toList_eq
              rw [ByteString.toList_literal]
              exact hrt
            have hlt : t.length < k := by
              rw [← hk, hu]
              simp only [List.length_append, List.length_cons, List.length_nil]
              omega
            have hr' : Utf8Spans (ByteString.literal (t ++ [0x00])) ByteString.empty :=
              hrest ▸ hr
            have hrec := ih t.length hlt t rfl hr'
            rw [hu, literal_append_bytes]
            simp only [ByteString.literal_cons, ByteString.cons_append]
            exact Utf8Spans.char (Utf8Char.three₁ (rest := ByteString.literal t) h0 h0' h1 h1' h2 h2') hrec
          · exfalso
            have hl := getLast_append_singleton_zero u [c0, c1, c2] hu
            simp only [List.getLast?_cons_cons, List.getLast?_singleton,
              Option.some.injEq] at hl
            rw [hl] at h2
            exact absurd h2 (by decide)
      | three₂ h1 h1' h2 h2' =>
          rename_i c1 c2
          have hb' : u ++ [0x00] = 0xED :: c1 :: c2 :: b'.toList := by
            have := congrArg ByteArray.toList hb
            simpa [ByteString.toList_literal, ByteString.toList_cons] using this
          rcases peel_list [0xED, c1, c2] u b'.toList hb' with ⟨t, hu, hrt⟩ | ⟨hu, hrt⟩
          · have hrest : b' = ByteString.literal (t ++ [0x00]) := by
              apply ByteString.eq_of_toList_eq
              rw [ByteString.toList_literal]
              exact hrt
            have hlt : t.length < k := by
              rw [← hk, hu]
              simp only [List.length_append, List.length_cons, List.length_nil]
              omega
            have hr' : Utf8Spans (ByteString.literal (t ++ [0x00])) ByteString.empty :=
              hrest ▸ hr
            have hrec := ih t.length hlt t rfl hr'
            rw [hu, literal_append_bytes]
            simp only [ByteString.literal_cons, ByteString.cons_append]
            exact Utf8Spans.char (Utf8Char.three₂ (rest := ByteString.literal t) h1 h1' h2 h2') hrec
          · exfalso
            have hl := getLast_append_singleton_zero u [0xED, c1, c2] hu
            simp only [List.getLast?_cons_cons, List.getLast?_singleton,
              Option.some.injEq] at hl
            rw [hl] at h2
            exact absurd h2 (by decide)
      | three₃ h0 h0' h1 h1' h2 h2' =>
          rename_i c0 c1 c2
          have hb' : u ++ [0x00] = c0 :: c1 :: c2 :: b'.toList := by
            have := congrArg ByteArray.toList hb
            simpa [ByteString.toList_literal, ByteString.toList_cons] using this
          rcases peel_list [c0, c1, c2] u b'.toList hb' with ⟨t, hu, hrt⟩ | ⟨hu, hrt⟩
          · have hrest : b' = ByteString.literal (t ++ [0x00]) := by
              apply ByteString.eq_of_toList_eq
              rw [ByteString.toList_literal]
              exact hrt
            have hlt : t.length < k := by
              rw [← hk, hu]
              simp only [List.length_append, List.length_cons, List.length_nil]
              omega
            have hr' : Utf8Spans (ByteString.literal (t ++ [0x00])) ByteString.empty :=
              hrest ▸ hr
            have hrec := ih t.length hlt t rfl hr'
            rw [hu, literal_append_bytes]
            simp only [ByteString.literal_cons, ByteString.cons_append]
            exact Utf8Spans.char (Utf8Char.three₃ (rest := ByteString.literal t) h0 h0' h1 h1' h2 h2') hrec
          · exfalso
            have hl := getLast_append_singleton_zero u [c0, c1, c2] hu
            simp only [List.getLast?_cons_cons, List.getLast?_singleton,
              Option.some.injEq] at hl
            rw [hl] at h2
            exact absurd h2 (by decide)
      | four₀ h1 h1' h2 h2' h3 h3' =>
          rename_i c1 c2 c3
          have hb' : u ++ [0x00] = 0xF0 :: c1 :: c2 :: c3 :: b'.toList := by
            have := congrArg ByteArray.toList hb
            simpa [ByteString.toList_literal, ByteString.toList_cons] using this
          rcases peel_list [0xF0, c1, c2, c3] u b'.toList hb' with ⟨t, hu, hrt⟩ | ⟨hu, hrt⟩
          · have hrest : b' = ByteString.literal (t ++ [0x00]) := by
              apply ByteString.eq_of_toList_eq
              rw [ByteString.toList_literal]
              exact hrt
            have hlt : t.length < k := by
              rw [← hk, hu]
              simp only [List.length_append, List.length_cons, List.length_nil]
              omega
            have hr' : Utf8Spans (ByteString.literal (t ++ [0x00])) ByteString.empty :=
              hrest ▸ hr
            have hrec := ih t.length hlt t rfl hr'
            rw [hu, literal_append_bytes]
            simp only [ByteString.literal_cons, ByteString.cons_append]
            exact Utf8Spans.char (Utf8Char.four₀ (rest := ByteString.literal t) h1 h1' h2 h2' h3 h3') hrec
          · exfalso
            have hl := getLast_append_singleton_zero u [0xF0, c1, c2, c3] hu
            simp only [List.getLast?_cons_cons, List.getLast?_singleton,
              Option.some.injEq] at hl
            rw [hl] at h3
            exact absurd h3 (by decide)
      | four₁ h0 h0' h1 h1' h2 h2' h3 h3' =>
          rename_i c0 c1 c2 c3
          have hb' : u ++ [0x00] = c0 :: c1 :: c2 :: c3 :: b'.toList := by
            have := congrArg ByteArray.toList hb
            simpa [ByteString.toList_literal, ByteString.toList_cons] using this
          rcases peel_list [c0, c1, c2, c3] u b'.toList hb' with ⟨t, hu, hrt⟩ | ⟨hu, hrt⟩
          · have hrest : b' = ByteString.literal (t ++ [0x00]) := by
              apply ByteString.eq_of_toList_eq
              rw [ByteString.toList_literal]
              exact hrt
            have hlt : t.length < k := by
              rw [← hk, hu]
              simp only [List.length_append, List.length_cons, List.length_nil]
              omega
            have hr' : Utf8Spans (ByteString.literal (t ++ [0x00])) ByteString.empty :=
              hrest ▸ hr
            have hrec := ih t.length hlt t rfl hr'
            rw [hu, literal_append_bytes]
            simp only [ByteString.literal_cons, ByteString.cons_append]
            exact Utf8Spans.char (Utf8Char.four₁ (rest := ByteString.literal t) h0 h0' h1 h1' h2 h2' h3 h3') hrec
          · exfalso
            have hl := getLast_append_singleton_zero u [c0, c1, c2, c3] hu
            simp only [List.getLast?_cons_cons, List.getLast?_singleton,
              Option.some.injEq] at hl
            rw [hl] at h3
            exact absurd h3 (by decide)
      | four₂ h1 h1' h2 h2' h3 h3' =>
          rename_i c1 c2 c3
          have hb' : u ++ [0x00] = 0xF4 :: c1 :: c2 :: c3 :: b'.toList := by
            have := congrArg ByteArray.toList hb
            simpa [ByteString.toList_literal, ByteString.toList_cons] using this
          rcases peel_list [0xF4, c1, c2, c3] u b'.toList hb' with ⟨t, hu, hrt⟩ | ⟨hu, hrt⟩
          · have hrest : b' = ByteString.literal (t ++ [0x00]) := by
              apply ByteString.eq_of_toList_eq
              rw [ByteString.toList_literal]
              exact hrt
            have hlt : t.length < k := by
              rw [← hk, hu]
              simp only [List.length_append, List.length_cons, List.length_nil]
              omega
            have hr' : Utf8Spans (ByteString.literal (t ++ [0x00])) ByteString.empty :=
              hrest ▸ hr
            have hrec := ih t.length hlt t rfl hr'
            rw [hu, literal_append_bytes]
            simp only [ByteString.literal_cons, ByteString.cons_append]
            exact Utf8Spans.char (Utf8Char.four₂ (rest := ByteString.literal t) h1 h1' h2 h2' h3 h3') hrec
          · exfalso
            have hl := getLast_append_singleton_zero u [0xF4, c1, c2, c3] hu
            simp only [List.getLast?_cons_cons, List.getLast?_singleton,
              Option.some.injEq] at hl
            rw [hl] at h3
            exact absurd h3 (by decide)

theorem utf8Char_byte_ne_zero {b : Bytes} {c : Nat} {r : Bytes} (h : Utf8Char b c r) :
    ∀ (n : Nat) (z : UInt8), 1 ≤ n → n < b.length - r.length →
      b.toList[n - 1]? = some z → z ≠ 0x00 := by
  cases h with
  | one hx =>
      rename_i b0
      intro n z hn hlen hz
      simp only [ByteString.length_eq_size, ByteString.size_cons] at hlen
      omega
  | two h0 h0' h1 h1' =>
      rename_i b0 b1
      intro n z hn hlen hz
      simp only [ByteString.length_eq_size, ByteString.size_cons] at hlen
      have hcases : n = 1 ∨ n = 2 := by omega
      rcases hcases with rfl | rfl
      · simp only [ByteString.toList_cons] at hz
        simp at hz
        intro hc
        rw [hc] at hz
        rw [hz] at h0
        exact absurd h0 (by decide)
      · simp only [ByteString.toList_cons] at hz
        simp at hz
        intro hc
        rw [hc] at hz
        rw [hz] at h1
        exact absurd h1 (by decide)
  | three₀ h1 h1' h2 h2' =>
      rename_i b1 b2
      intro n z hn hlen hz
      simp only [ByteString.length_eq_size, ByteString.size_cons] at hlen
      have hcases : n = 1 ∨ n = 2 ∨ n = 3 := by omega
      rcases hcases with rfl | rfl | rfl
      · simp only [ByteString.toList_cons] at hz
        simp at hz
        intro hc
        rw [hc] at hz
        exact absurd hz (by decide)
      · simp only [ByteString.toList_cons] at hz
        simp at hz
        intro hc
        rw [hc] at hz
        rw [hz] at h1
        exact absurd h1 (by decide)
      · simp only [ByteString.toList_cons] at hz
        simp at hz
        intro hc
        rw [hc] at hz
        rw [hz] at h2
        exact absurd h2 (by decide)
  | three₁ h0 h0' h1 h1' h2 h2' =>
      rename_i b0 b1 b2
      intro n z hn hlen hz
      simp only [ByteString.length_eq_size, ByteString.size_cons] at hlen
      have hcases : n = 1 ∨ n = 2 ∨ n = 3 := by omega
      rcases hcases with rfl | rfl | rfl
      · simp only [ByteString.toList_cons] at hz
        simp at hz
        intro hc
        rw [hc] at hz
        rw [hz] at h0
        exact absurd h0 (by decide)
      · simp only [ByteString.toList_cons] at hz
        simp at hz
        intro hc
        rw [hc] at hz
        rw [hz] at h1
        exact absurd h1 (by decide)
      · simp only [ByteString.toList_cons] at hz
        simp at hz
        intro hc
        rw [hc] at hz
        rw [hz] at h2
        exact absurd h2 (by decide)
  | three₂ h1 h1' h2 h2' =>
      rename_i b1 b2
      intro n z hn hlen hz
      simp only [ByteString.length_eq_size, ByteString.size_cons] at hlen
      have hcases : n = 1 ∨ n = 2 ∨ n = 3 := by omega
      rcases hcases with rfl | rfl | rfl
      · simp only [ByteString.toList_cons] at hz
        simp at hz
        intro hc
        rw [hc] at hz
        exact absurd hz (by decide)
      · simp only [ByteString.toList_cons] at hz
        simp at hz
        intro hc
        rw [hc] at hz
        rw [hz] at h1
        exact absurd h1 (by decide)
      · simp only [ByteString.toList_cons] at hz
        simp at hz
        intro hc
        rw [hc] at hz
        rw [hz] at h2
        exact absurd h2 (by decide)
  | three₃ h0 h0' h1 h1' h2 h2' =>
      rename_i b0 b1 b2
      intro n z hn hlen hz
      simp only [ByteString.length_eq_size, ByteString.size_cons] at hlen
      have hcases : n = 1 ∨ n = 2 ∨ n = 3 := by omega
      rcases hcases with rfl | rfl | rfl
      · simp only [ByteString.toList_cons] at hz
        simp at hz
        intro hc
        rw [hc] at hz
        rw [hz] at h0
        exact absurd h0 (by decide)
      · simp only [ByteString.toList_cons] at hz
        simp at hz
        intro hc
        rw [hc] at hz
        rw [hz] at h1
        exact absurd h1 (by decide)
      · simp only [ByteString.toList_cons] at hz
        simp at hz
        intro hc
        rw [hc] at hz
        rw [hz] at h2
        exact absurd h2 (by decide)
  | four₀ h1 h1' h2 h2' h3 h3' =>
      rename_i b1 b2 b3
      intro n z hn hlen hz
      simp only [ByteString.length_eq_size, ByteString.size_cons] at hlen
      have hcases : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
      rcases hcases with rfl | rfl | rfl | rfl
      · simp only [ByteString.toList_cons] at hz
        simp at hz
        intro hc
        rw [hc] at hz
        exact absurd hz (by decide)
      · simp only [ByteString.toList_cons] at hz
        simp at hz
        intro hc
        rw [hc] at hz
        rw [hz] at h1
        exact absurd h1 (by decide)
      · simp only [ByteString.toList_cons] at hz
        simp at hz
        intro hc
        rw [hc] at hz
        rw [hz] at h2
        exact absurd h2 (by decide)
      · simp only [ByteString.toList_cons] at hz
        simp at hz
        intro hc
        rw [hc] at hz
        rw [hz] at h3
        exact absurd h3 (by decide)
  | four₁ h0 h0' h1 h1' h2 h2' h3 h3' =>
      rename_i b0 b1 b2 b3
      intro n z hn hlen hz
      simp only [ByteString.length_eq_size, ByteString.size_cons] at hlen
      have hcases : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
      rcases hcases with rfl | rfl | rfl | rfl
      · simp only [ByteString.toList_cons] at hz
        simp at hz
        intro hc
        rw [hc] at hz
        rw [hz] at h0
        exact absurd h0 (by decide)
      · simp only [ByteString.toList_cons] at hz
        simp at hz
        intro hc
        rw [hc] at hz
        rw [hz] at h1
        exact absurd h1 (by decide)
      · simp only [ByteString.toList_cons] at hz
        simp at hz
        intro hc
        rw [hc] at hz
        rw [hz] at h2
        exact absurd h2 (by decide)
      · simp only [ByteString.toList_cons] at hz
        simp at hz
        intro hc
        rw [hc] at hz
        rw [hz] at h3
        exact absurd h3 (by decide)
  | four₂ h1 h1' h2 h2' h3 h3' =>
      rename_i b1 b2 b3
      intro n z hn hlen hz
      simp only [ByteString.length_eq_size, ByteString.size_cons] at hlen
      have hcases : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
      rcases hcases with rfl | rfl | rfl | rfl
      · simp only [ByteString.toList_cons] at hz
        simp at hz
        intro hc
        rw [hc] at hz
        exact absurd hz (by decide)
      · simp only [ByteString.toList_cons] at hz
        simp at hz
        intro hc
        rw [hc] at hz
        rw [hz] at h1
        exact absurd h1 (by decide)
      · simp only [ByteString.toList_cons] at hz
        simp at hz
        intro hc
        rw [hc] at hz
        rw [hz] at h2
        exact absurd h2 (by decide)
      · simp only [ByteString.toList_cons] at hz
        simp at hz
        intro hc
        rw [hc] at hz
        rw [hz] at h3
        exact absurd h3 (by decide)

/-- A proper prefix of one character's encoding never ends in `0x00`: the
encoding's later bytes are continuations and the one-byte character's own byte is
its whole length. -/
theorem not_utf8PrefixOf_append_zero (l : List UInt8) :
    ¬ Utf8PrefixOf (ByteString.literal (l ++ [0x00])) := by
  intro hp
  obtain ⟨hne, b, c, r, hc, hlt, hpre⟩ := hp
  unfold HasPrefix at hpre
  rw [ByteString.drop_zero] at hpre
  have hlitlen : (ByteString.literal (l ++ [0x00])).length = (l ++ [0x00]).length := by
    rw [ByteString.length_eq_size, ByteString.size_literal]
  have hpre' : b.take (l ++ [0x00]).length = ByteString.literal (l ++ [0x00]) := by
    rwa [hlitlen] at hpre
  have hlen1 : 1 ≤ (l ++ [0x00]).length := by simp
  have htake : b.toList.take (l ++ [0x00]).length = l ++ [0x00] := by
    have := congrArg ByteArray.toList hpre'
    rwa [ByteString.toList_take, ByteString.toList_literal] at this
  have hlt2 : (l ++ [0x00]).length < b.length - r.length := by
    rwa [hlitlen] at hlt
  have hbyte : b.toList[(l ++ [0x00]).length - 1]? = some 0x00 := by
    have h1 : (b.toList.take (l ++ [0x00]).length)[(l ++ [0x00]).length - 1]?
        = b.toList[(l ++ [0x00]).length - 1]? := by
      simp
    rw [← h1, htake]
    have h2 : (l ++ [0x00]).length - 1 = l.length := by simp
    rw [h2, List.getElem?_append_right (Nat.le_refl l.length)]
    simp
  exact (utf8Char_byte_ne_zero hc (l ++ [0x00]).length 0x00 hlen1 hlt2 hbyte) rfl


/-- Peeling `p` trailing zeros from a complete span. -/
theorem utf8Spans_strip_zeros_tail (u : List UInt8) (p : Nat) :
    Utf8Spans (ByteString.literal (u ++ List.replicate p 0x00)) ByteString.empty →
      Utf8Spans (ByteString.literal u) ByteString.empty := by
  revert u
  induction p with
  | zero =>
      intro u h
      simpa using h
  | succ p ih =>
      intro u h
      have hrew : ByteString.literal (u ++ List.replicate (p + 1) 0x00)
          = ByteString.literal ((u ++ List.replicate p 0x00) ++ [0x00]) := by
        rw [List.replicate_succ', List.append_assoc]
      rw [hrew] at h
      exact ih u (utf8Spans_strip_zero_tail (u ++ List.replicate p 0x00) h)

/-- **The padded window read as a document.**  With at least one padding byte, a
valid prefix of the staged window is exactly a concatenation of complete
characters: the three prefix zeros are complete characters, the padding zeros are
complete characters, and a truncated final character of the document is completed
— or broken — by a `0x00` that no character can contain. -/
theorem validPrefix_padded_iff_utf8Chars (bs : List UInt8) (p : Nat) (hp : 1 ≤ p) :
    ValidPrefix (ByteString.literal (List.replicate 3 0x00 ++ bs ++ List.replicate p 0x00)) ↔
      Utf8Chars (ByteString.literal bs) := by
  have hsplit : List.replicate 3 (0x00 : UInt8) ++ bs ++ List.replicate p 0x00
      = 0x00 :: 0x00 :: 0x00 :: (bs ++ List.replicate p 0x00) := rfl
  constructor
  · intro hv
    have hv3 : ValidPrefix
        (ByteString.literal (0x00 :: 0x00 :: 0x00 :: (bs ++ List.replicate p 0x00))) := by
      rwa [hsplit] at hv
    have hv' : ValidPrefix (ByteString.literal (bs ++ List.replicate p 0x00)) :=
      validPrefix_three_cons hv3
    rw [validPrefix_iff] at hv'
    rcases hv' with hchars | ⟨t, hspans, hpref⟩
    · exact utf8Spans_strip_zeros_tail bs p hchars
    · exfalso
      obtain ⟨k, hk⟩ := utf8Spans_literal_tail hspans
      have htne : t ≠ ByteString.empty := hpref.1
      have hklt : k < (bs ++ List.replicate p 0x00).length := by
        by_cases h : k < (bs ++ List.replicate p 0x00).length
        · exact h
        · exfalso
          apply htne
          rw [hk, List.drop_eq_nil_of_le (Nat.le_of_not_lt h)]
          rfl
      have hzlast : (List.replicate p (0x00 : UInt8)).getLast? = some 0x00 := by
        have hp' : p = (p - 1) + 1 := by omega
        rw [hp', List.replicate_succ']
        rw [List.getLast?_append]
        simp
      have huget : (bs ++ List.replicate p (0x00 : UInt8)).getLast? = some 0x00 := by
        rw [List.getLast?_append, hzlast]
        simp
      have hdropget :
          ((bs ++ List.replicate p (0x00 : UInt8)).drop k).getLast? = some 0x00 := by
        rw [List.getLast?_eq_getElem?, List.getElem?_drop, List.length_drop]
        have hidx : k + ((bs ++ List.replicate p (0x00 : UInt8)).length - k - 1)
            = (bs ++ List.replicate p (0x00 : UInt8)).length - 1 := by omega
        rw [hidx, ← List.getLast?_eq_getElem?, huget]
      obtain ⟨l', hl'⟩ := List.getLast?_eq_some_iff.mp hdropget
      have htform : t = ByteString.literal (l' ++ [0x00]) := by
        rw [hk, hl']
      exact (not_utf8PrefixOf_append_zero l') (htform ▸ hpref)
  · intro hchars
    have h2 : Utf8Spans (ByteString.literal (bs ++ List.replicate p 0x00))
        (ByteString.literal (List.replicate p 0x00)) := by
      have happ := utf8Spans_append_right hchars (d := ByteString.literal (List.replicate p 0x00))
      rwa [← literal_append_bytes, ByteString.empty_append] at happ
    have h1 : Utf8Spans (ByteString.literal (bs ++ List.replicate p 0x00)) ByteString.empty :=
      utf8Spans_trans h2 (utf8Spans_replicate_zero p)
    have hv : ValidPrefix (ByteString.literal (bs ++ List.replicate p 0x00)) :=
      validPrefix_of_utf8Chars h1
    have hv3 := validPrefix_three_cons_back hv
    rw [hsplit]
    exact hv3



theorem ofBool_bool_eq_one (b : Bool) : (BitVec.ofBool b = (1 : BitVec 1)) ↔ b = true := by
  cases b <;> decide

theorem ofBool_bool_eq_zero (b : Bool) : (BitVec.ofBool b = (0 : BitVec 1)) ↔ b = false := by
  cases b <;> decide

theorem bit1_or_eq_zero_iff (a b : BitVec 1) : (a ||| b) = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have h' : (a ||| b).toNat = 0 := by rw [h]; rfl
    rw [BitVec.toNat_or, Nat.or_eq_zero_iff] at h'
    exact ⟨BitVec.toNat_inj.mp h'.1, BitVec.toNat_inj.mp h'.2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

def utf8TailBit (d : BitVec 8) : BitVec 1 :=
  BitVec.ofBool (BitVec.ult (BitVec.ofInt 8 (-12)) d) |||
    BitVec.ofBool (d &&& BitVec.ofInt 8 (-2) = BitVec.ofInt 8 (-64))

theorem ofInt8_neg12 : (BitVec.ofInt 8 (-12) : BitVec 8) = BitVec.ofNat 8 244 := by decide
theorem ofInt8_neg2 : (BitVec.ofInt 8 (-2) : BitVec 8) = BitVec.ofNat 8 254 := by decide
theorem ofInt8_neg64 : (BitVec.ofInt 8 (-64) : BitVec 8) = BitVec.ofNat 8 192 := by decide

theorem u8_toBitVec_ofNat_244 : (BitVec.ofNat 8 244 : BitVec 8) = (0xF4 : UInt8).toBitVec := by
  decide
theorem u8_toBitVec_ofNat_254 : (BitVec.ofNat 8 254 : BitVec 8) = (0xFE : UInt8).toBitVec := by
  decide
theorem u8_toBitVec_ofNat_192 : (BitVec.ofNat 8 192 : BitVec 8) = (0xC0 : UInt8).toBitVec := by
  decide

theorem tail_ult_decide_iff (x : UInt8) :
    (decide ((0xF4 : UInt8).toBitVec.toNat < x.toBitVec.toNat) = false) ↔
      (decide ((0xF5 : UInt8) ≤ x) = false) := by
  simp only [decide_eq_false_iff_not, UInt8.toNat_toBitVec, UInt8.le_iff_toNat_le,
    UInt8.toNat_ofNat]
  constructor
  · intro h hc
    exact h (by omega)
  · intro h hc
    exact h (by omega)

theorem tail_eq_decide_iff (x : UInt8) :
    (decide ((x &&& (0xFE : UInt8)).toBitVec = (0xC0 : UInt8).toBitVec) = false) ↔
      (decide ((x &&& 0xFE) = 0xC0) = false) := by
  simp only [decide_eq_false_iff_not, UInt8.toBitVec_inj]

theorem utf8TailBit_zero_iff (x : UInt8) :
    utf8TailBit x.toBitVec = 0 ↔ klTailByte x = false := by
  unfold utf8TailBit klTailByte
  rw [bit1_or_eq_zero_iff, ofBool_bool_eq_zero, ofBool_bool_eq_zero,
    Bool.or_eq_false_iff]
  rw [BitVec.ult_eq_decide, ofInt8_neg12, u8_toBitVec_ofNat_244,
    ofInt8_neg2, ofInt8_neg64, u8_toBitVec_ofNat_254, u8_toBitVec_ofNat_192,
    ← UInt8.toBitVec_and]
  exact ⟨fun h => ⟨tail_eq_decide_iff x |>.mpr h.2, tail_ult_decide_iff x |>.mpr h.1⟩,
    fun h => ⟨tail_ult_decide_iff x |>.mp h.2, tail_eq_decide_iff x |>.mp h.1⟩⟩


theorem ofInt32_zero : (BitVec.ofInt 32 0 : BitVec 32) = 0 := by decide

theorem all_eq_zero_iff (l : List UInt8) :
    (l.all (fun x => decide (x = 0x00))) = true ↔ ∀ x ∈ l, x = 0x00 := by
  rw [List.all_eq_true]
  constructor
  · intro h x hx
    exact of_decide_eq_true (h x hx)
  · intro h x hx
    exact decide_eq_true (h x hx)

theorem ofNat256_eq_zero_iff (V : Nat) (hV : V < 2 ^ 256) :
    (BitVec.ofNat 256 V = 0) ↔ V = 0 := by
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat] at h'
    have h2 : V % 2 ^ 256 = 0 := by simpa using h'
    rwa [Nat.mod_eq_of_lt hV] at h2
  · intro h
    rw [h]
    rfl

theorem t16_zero_iff (bs : List UInt8) (n nb : Nat) (gate : Bool)
    (u8k : List (BitVec 64))
    (hn : n = bs.length) (hnb : nb = (n + 63) / 64)
    (hu8klen : u8k.length = 4)
    (hpack : packLanes u8k = bytesToNat (klAcc bs nb)) :
    (BitVec.ofBool (decide (BitLanes.ptestz (BitVec.ofNat 256 (packLanes u8k))
        (BitVec.ofNat 256 (packLanes u8k)) = BitVec.ofInt 32 0)) = (0 : BitVec 1)) ↔
      klErrAll (utf8Window bs n nb) (64 * nb) := by
  rw [ofBool_bool_eq_zero, decide_eq_false_iff_not, ofInt32_zero,
    BitLanes.ptestz_eq_zero_iff]
  rw [show ¬ (BitVec.ofNat 256 (packLanes u8k) &&& BitVec.ofNat 256 (packLanes u8k) ≠ 0)
      ↔ (BitVec.ofNat 256 (packLanes u8k) = 0) from by
    rw [BitVec.and_self]
    exact Decidable.not_not]
  have hlt := packLanes_lt u8k
  rw [hu8klen, show (4 : Nat) * 64 = 256 from rfl] at hlt
  rw [ofNat256_eq_zero_iff _ hlt, hpack, bytesToNat_eq_zero_iff, ← all_eq_zero_iff]
  have hnb' : nb = (bs.length + 63) / 64 := by rw [hnb, hn]
  have hsame : klAcc bs nb = klAll gate bs := by
    rw [hnb', ← klAll_false_eq_klAcc bs]
    cases gate with
    | false => rfl
    | true => exact (klAll_gate_invariant bs).symm
  rw [hsame]
  exact klAll_zero_iff_klErrAll bs n nb gate hn hnb


theorem ofNat64_ne_zero_iff (n : Nat) (hn : n < 2 ^ 63) :
    (BitVec.ofNat 64 n ≠ BitVec.ofInt 64 0) ↔ n ≠ 0 := by
  have h0 : (BitVec.ofInt 64 0 : BitVec 64) = 0 := by decide
  rw [h0]
  constructor
  · intro h hn0
    apply h
    rw [hn0]
    rfl
  · intro h hx
    apply h
    have hh := congrArg BitVec.toNat hx
    rw [BitVec.toNat_ofNat] at hh
    have h2 : n % 2 ^ 64 = 0 := by simpa using hh
    have hlt : n < 2 ^ 64 := by omega
    rwa [Nat.mod_eq_of_lt hlt] at h2

theorem nat_and63_eq_mod (n : Nat) : n &&& 63 = n % 64 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show (64 : Nat) = 2 ^ 6 from by decide]
  rw [Nat.testBit_and, Nat.testBit_mod_two_pow]
  rcases Nat.lt_or_ge i 6 with hi | hi
  · have h63 : (63 : Nat).testBit i = true := by
      have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hdec : decide (i < 6) = true := by rw [decide_eq_true_eq]; exact hi
    rw [h63, hdec, Bool.true_and, Bool.and_true]
  · have h63 : (63 : Nat).testBit i = false := by
      apply Nat.testBit_lt_two_pow
      have h2 : (2 : Nat) ^ 6 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hi
      omega
    have hdec : decide (i < 6) = false := by rw [decide_eq_false_iff_not]; omega
    rw [h63, hdec, Bool.false_and, Bool.and_false]

theorem nat_and_one_eq_self {n : Nat} (h : n < 2) : n &&& 1 = n := by
  have hn : n = 0 ∨ n = 1 := by omega
  rcases hn with rfl | rfl <;> decide

theorem and63_eq_zero_iff (n : Nat) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n &&& BitVec.ofInt 64 63 = BitVec.ofInt 64 0) ↔ n % 64 = 0 := by
  have h63 : (BitVec.ofInt 64 63 : BitVec 64) = BitVec.ofNat 64 63 := by decide
  have h0 : (BitVec.ofInt 64 0 : BitVec 64) = 0 := by decide
  rw [h63, h0, BitVec.toNat_eq]
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h63' : (63 : Nat) % 2 ^ 64 = 63 := by decide
  rw [h63']
  have hzero : (0 : BitVec 64).toNat = 0 := rfl
  rw [hzero, Nat.mod_eq_of_lt hn, nat_and63_eq_mod]

theorem bit1_one_and (x : BitVec 1) : ((1 : BitVec 1) &&& x) = x := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_and]
  have hx : x.toNat < 2 := x.isLt
  have h1 : (1 : BitVec 1).toNat = 1 := rfl
  rw [h1, Nat.and_comm]
  exact nat_and_one_eq_self hx

theorem bitvec_toNat_eq_zero_iff {w : Nat} (e : BitVec w) : e.toNat = 0 ↔ e = 0 := by
  constructor
  · intro h
    apply BitVec.toNat_inj.mp
    rw [h]
    rfl
  · intro h
    rw [h]
    rfl

theorem natToBytes_u8 (x : UInt8) : natToBytes x.toBitVec.toNat 1 = [x] := by
  rw [UInt8.toNat_toBitVec]
  simp [natToBytes]

theorem klByte_eq_of_drop_cons {s : List UInt8} {i : Nat} {a : UInt8} {as : List UInt8}
    (h : s.drop i = a :: as) : klByte s i = a := by
  have h' := klByte_drop_any s i 0
  rw [Nat.add_zero, h] at h'
  rw [h']
  rfl

theorem klByte_window_tail (bs : List UInt8) (n nb : Nat) (hn : 1 ≤ n) :
    klByte (utf8Window bs n nb) (n + 2) = klByte bs (n - 1) := by
  rw [klByte_window]
  rw [show n + 2 = 3 + (n - 1) from by omega, klByte_drop]
  rfl

theorem evalOperand_reg_utf8 (env : Env) (s : State) (n : String) :
    evalOperand (withEnv env s) (.reg n) = lookupName env n := by
  simp only [withEnv, evalOperand]

theorem utf8_cleanup_run
    (bs : List UInt8) (n nb b : Nat) (mem : Mem) (gate : Bool)
    (env : Env) (s : State) (p : String) (op : Operand) (u8k : List (BitVec 64))
    (hn : n = bs.length) (hnb : nb = (n + 63) / 64)
    (hb : 3 ≤ b) (hn64 : n < 2 ^ 63) (hpos : 0 < n)
    (hread : readBytes mem (b - 3) (3 + 64 * nb) = some (utf8Window bs n nb))
    (hpc : s.pc = "for.cond.cleanup") (hpre : s.pre = some p) (hmem : s.mem = mem)
    (hinc : phiIncoming p [("entry", .imm (.splat 4 64 (BitVec.ofInt 64 0))),
      ("if.end14.us", .reg "%u8k.2.us"), ("for.body", .reg "%or.i47")] = some op)
    (hop : evalOperand (withEnv env s) op = some (.vec 4 64 u8k))
    (hu8klen : u8k.length = 4)
    (hpack : packLanes u8k = bytesToNat (klAcc bs nb))
    (hnl : lookupName env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hbl : lookupName env "%b" = some (.ptr b)) :
    ∃ (err' : Nat) (mem' : Mem),
      runFuel utf8Calls 3 utf8Function (withEnv env s) =
        some (.ret (some (.int 64 err')) mem') ∧
      (err' = 0 ∨ err' = 1) ∧
      (err' = 0 ↔ utf8WinPrefix (utf8Window bs n nb)) ∧
      mem' = mem := by
  obtain ⟨env1, hrun1, h36, ht16, ht19, hcond⟩ :=
    utf8Reduce env s p op u8k n hpre hinc hop hu8klen hnl
  have hstep1 : step utf8Calls utf8Function (withEnv env s)
      = execTerm (withEnv env1 s)
          (.condbr (.reg "%or.cond45") "if.then20" "if.end24") :=
    step_of_utf8 _ "for.cond.cleanup" utf8Cleanup _ hpc findBlock_utf8Cleanup hrun1
  have hkept_cleanup : ∀ i ∈ utf8Cleanup.instrs, i.dst? ∉ utf8Kept.map some := by decide
  have hbl1 : lookupName env1 "%b" = some (.ptr b) :=
    (denoteCode_kept utf8Cleanup.instrs env env1 s hrun1 hkept_cleanup "%b"
      (by decide)).trans hbl
  have hnl1 : lookupName env1 "%n" = some (.int 64 (BitVec.ofNat 64 n)) :=
    (denoteCode_kept utf8Cleanup.instrs env env1 s hrun1 hkept_cleanup "%n"
      (by decide)).trans hnl
  have ht16zero : (BitVec.ofBool (decide (BitLanes.ptestz
        (BitVec.ofNat 256 (packLanes u8k)) (BitVec.ofNat 256 (packLanes u8k))
        = BitVec.ofInt 32 0)) = (0 : BitVec 1)) ↔
      klErrAll (utf8Window bs n nb) (64 * nb) :=
    t16_zero_iff bs n nb gate u8k hn hnb hu8klen hpack
  have hb1 : (BitVec.ofBool (decide (BitVec.ofNat 64 n ≠ BitVec.ofInt 64 0))
      : BitVec 1) = 1 := by
    rw [ofBool_bool_eq_one, decide_eq_true_eq]
    exact ofNat64_ne_zero_iff n hn64 |>.mpr (by omega)
  have hb2 : ((BitVec.ofBool (decide (BitVec.ofNat 64 n &&& BitVec.ofInt 64 63
        = BitVec.ofInt 64 0)) : BitVec 1) = 1) ↔ n % 64 = 0 := by
    rw [ofBool_bool_eq_one, decide_eq_true_eq]
    exact and63_eq_zero_iff n (by omega)
  have hnb_le : n ≤ 64 * nb := by
    rw [hnb]; exact LeanLLVM.Refinement.JsonUtf8IR.le_mul_div_sixtyfour n
  have htot : (n + 2) + (1 + 64 * nb - n) = 3 + 64 * nb := by omega
  have hread' : readBytes mem (b - 3) ((n + 2) + (1 + 64 * nb - n))
      = some (utf8Window bs n nb) := by
    rw [htot]; exact hread
  obtain ⟨_, hdropread⟩ :=
    readBytes_split mem (b - 3) (n + 2) (1 + 64 * nb - n) hread'
  have haddr : b - 3 + (n + 2) = b + n - 1 := by omega
  rw [haddr] at hdropread
  obtain ⟨hone, _⟩ := readBytes_split mem (b + n - 1) 1 (64 * nb - n) (by
    rw [show 1 + (64 * nb - n) = 1 + 64 * nb - n from by omega]; exact hdropread)
  have hlenpos : 0 < ((utf8Window bs n nb).drop (n + 2)).length := by
    rw [List.length_drop, utf8Window_length bs n nb hn hnb]
    omega
  obtain ⟨x, xs, hx⟩ : ∃ x xs, (utf8Window bs n nb).drop (n + 2) = x :: xs := by
    cases h : (utf8Window bs n nb).drop (n + 2) with
    | nil => rw [h] at hlenpos; simp at hlenpos
    | cons x xs => exact ⟨x, xs, rfl⟩
  have hklast : klByte (utf8Window bs n nb) (n + 2) = klByte bs (n - 1) :=
    klByte_window_tail bs n nb (by omega)
  have hxbyte : x = klByte bs (n - 1) := by
    rw [← klByte_eq_of_drop_cons hx, hklast]
  have htake1 : ((utf8Window bs n nb).drop (n + 2)).take 1 = [x] := by
    rw [hx]; rfl
  have hreadtail : readBytes mem (b + n - 1) 1
      = some (natToBytes x.toBitVec.toNat 1) := by
    rw [hone, htake1, natToBytes_u8]
  have hreadtail' : readBytes s.mem (b + n - 1) 1
      = some (natToBytes x.toBitVec.toNat 1) := by
    rw [hmem]; exact hreadtail
  let t16 : BitVec 1 := BitVec.ofBool (decide (BitLanes.ptestz
    (BitVec.ofNat 256 (packLanes u8k)) (BitVec.ofNat 256 (packLanes u8k))
    = BitVec.ofInt 32 0))
  have ht16' : lookupName env1 "%tobool16.not" = some (.int 1 t16) := ht16
  let s1 : State := { s with pc := "if.then20", pre := some "for.cond.cleanup" }
  let s2 : State := { s with pc := "if.end24", pre := some "if.then20" }
  let s3 : State := { s with pc := "if.end24", pre := some "for.cond.cleanup" }
  by_cases hmod : n % 64 = 0
  · have hbit2one : (BitVec.ofBool (decide (BitVec.ofNat 64 n &&& BitVec.ofInt 64 63
        = BitVec.ofInt 64 0)) : BitVec 1) = 1 := hb2.mpr hmod
    have hguard : (BitVec.ofBool (decide (BitVec.ofNat 64 n ≠ BitVec.ofInt 64 0))
        &&& BitVec.ofBool (decide (BitVec.ofNat 64 n &&& BitVec.ofInt 64 63
          = BitVec.ofInt 64 0)) : BitVec 1) = 1 := by
      rw [hb1, bit1_one_and, hbit2one]
    have heval : evalOperand (withEnv env1 s) (.reg "%or.cond45")
        = some (.int 1 (BitVec.ofBool (decide (BitVec.ofNat 64 n
            ≠ BitVec.ofInt 64 0)) &&& BitVec.ofBool (decide (BitVec.ofNat 64 n
              &&& BitVec.ofInt 64 63 = BitVec.ofInt 64 0)))) := by
      rw [evalOperand_reg_utf8]; exact hcond
    have hjump1 : step utf8Calls utf8Function (withEnv env s) = .jump (withEnv env1 s1) := by
      rw [hstep1]
      simpa only [s1, withEnv, hpc] using execTerm_condbr_true heval hguard
    have htail := utf8Tail env1 s1 b n t16 x.toBitVec
      (by simpa only [s1, withEnv] using hbl1) (by simpa only [s1, withEnv] using hnl1)
      (by simpa only [s1, withEnv] using ht16') hb hn64
      (by simpa only [s1, withEnv] using hreadtail')
    obtain ⟨env2, hrun2, hval⟩ := htail
    have hstep2 : step utf8Calls utf8Function (withEnv env1 s1) = .jump (withEnv env2 s2) := by
      rw [step_of_utf8 _ "if.then20" utf8Then20 _ (by simp only [withEnv, s1]) findBlock_utf8Then20 hrun2]
      simpa only [utf8Then20, s1, s2, withEnv] using execTerm_br (withEnv env2 s1) "if.end24"
    have hret := utf8Return env2 s2 "if.then20" (.reg "%or2373") (t16 ||| utf8TailBit x.toBitVec)
      (by simp only [s2]) (by simp [phiIncoming])
      (by rw [evalOperand_reg_utf8]
          show lookupName env2 "%or2373" = some (.int 1 (t16 ||| utf8TailBit x.toBitVec))
          exact hval)
    obtain ⟨env3, hrun3, hval3⟩ := hret
    have hevret : evalOperand (withEnv env3 s2) (.reg "%err.0")
        = some (.int 64 (BitVec.ofNat 64 (t16 ||| utf8TailBit x.toBitVec).toNat)) := by
      rw [evalOperand_reg_utf8]; exact hval3
    have hstep3 : step utf8Calls utf8Function (withEnv env2 s2)
        = .ret (some (.int 64 (BitVec.ofNat 64 (t16 ||| utf8TailBit x.toBitVec).toNat)))
          (withEnv env3 s2) := by
      rw [step_of_utf8 _ "if.end24" utf8End24 _ (by simp only [withEnv, s2]) findBlock_utf8End24 hrun3]
      show execTerm (withEnv env3 s2) (.ret (.int 64) (some (.reg "%err.0"))) = _
      rw [execTerm_ret_reg (withEnv env3 s2) "%err.0"
        (.int 64 (BitVec.ofNat 64 (t16 ||| utf8TailBit x.toBitVec).toNat)) hevret]
    refine ⟨(t16 ||| utf8TailBit x.toBitVec).toNat, mem, ?_, ?_, ?_, ?_⟩
    · refine Eq.trans (runFuel_jump_utf8 (n := 2) hjump1)
        (Eq.trans (runFuel_jump_utf8 (n := 1) hstep2) ?_)
      have h2 : runFuel utf8Calls 1 utf8Function (withEnv env2 s2)
          = some (.ret (some (.int 64 ((t16 ||| utf8TailBit x.toBitVec).toNat)))
              (withEnv env3 s2).mem) :=
        runFuel_ret_utf8 (n := 0) hstep3
      rw [show (withEnv env3 s2).mem = mem from by simp only [withEnv, s2]; exact hmem] at h2
      exact h2
    · have his := (t16 ||| utf8TailBit x.toBitVec).isLt
      omega
    · have hmide : ((t16 ||| utf8TailBit x.toBitVec).toNat = 0) ↔
          (klErrAll (utf8Window bs n nb) (64 * nb) ∧
            ¬ (klTailByte (klByte bs (n - 1)) = true)) := by
        rw [bitvec_toNat_eq_zero_iff]
        rw [bit1_or_eq_zero_iff, show (utf8TailBit x.toBitVec = 0) ↔ klTailByte x = false from
          utf8TailBit_zero_iff x]
        rw [show (klTailByte x = false) ↔ ¬ (klTailByte x = true) from by
          rw [Bool.not_eq_true]]
        rw [hxbyte]
        exact ⟨fun h => ⟨ht16zero.mp h.1, h.2⟩, fun h => ⟨ht16zero.mpr h.1, h.2⟩⟩
      rw [hmide]
      have hclause : ¬ (klTailByte (klByte bs (n - 1)) = true) ↔
          ¬ (n ≠ 0 ∧ n % 64 = 0 ∧ klTailByte (klByte bs (n - 1)) = true) := by
        have hn0 : n ≠ 0 := by omega
        constructor
        · intro h hc; exact h hc.2.2
        · intro h ht; exact h ⟨hn0, hmod, ht⟩
      rw [hclause]
      show (klErrAll (utf8Window bs n nb) (64 * nb) ∧
          ¬ (n ≠ 0 ∧ n % 64 = 0 ∧ klTailByte (klByte bs (n - 1)) = true)) ↔
        ValidPrefix (ByteString.literal (utf8Window bs n nb))
      exact klErrAll_window_iff bs n nb hn hnb
    · rfl
  · have hbit2zero : (BitVec.ofBool (decide (BitVec.ofNat 64 n &&& BitVec.ofInt 64 63
        = BitVec.ofInt 64 0)) : BitVec 1) = 0 := by
      rw [ofBool_bool_eq_zero, decide_eq_false_iff_not]
      intro hh
      exact hmod ((and63_eq_zero_iff n (by omega)).mp hh)
    have hguard : (BitVec.ofBool (decide (BitVec.ofNat 64 n ≠ BitVec.ofInt 64 0))
        &&& BitVec.ofBool (decide (BitVec.ofNat 64 n &&& BitVec.ofInt 64 63
          = BitVec.ofInt 64 0)) : BitVec 1) = 0 := by
      rw [hb1, bit1_one_and, hbit2zero]
    have heval : evalOperand (withEnv env1 s) (.reg "%or.cond45")
        = some (.int 1 (BitVec.ofBool (decide (BitVec.ofNat 64 n
            ≠ BitVec.ofInt 64 0)) &&& BitVec.ofBool (decide (BitVec.ofNat 64 n
              &&& BitVec.ofInt 64 63 = BitVec.ofInt 64 0)))) := by
      rw [evalOperand_reg_utf8]; exact hcond
    have hjump1 : step utf8Calls utf8Function (withEnv env s) = .jump (withEnv env1 s3) := by
      rw [hstep1]
      simpa only [s3, withEnv, hpc] using execTerm_condbr_false heval hguard
    have hret := utf8Return env1 s3 "for.cond.cleanup" (.reg "%tobool16.not") t16
      (by simp only [s3]) (by simp [phiIncoming])
      (by rw [evalOperand_reg_utf8]
          show lookupName env1 "%tobool16.not" = some (.int 1 t16)
          exact ht16')
    obtain ⟨env3, hrun3, hval3⟩ := hret
    have hevret : evalOperand (withEnv env3 s3) (.reg "%err.0")
        = some (.int 64 (BitVec.ofNat 64 t16.toNat)) := by
      rw [evalOperand_reg_utf8]; exact hval3
    have hstep3 : step utf8Calls utf8Function (withEnv env1 s3)
        = .ret (some (.int 64 (BitVec.ofNat 64 t16.toNat))) (withEnv env3 s3) := by
      rw [step_of_utf8 _ "if.end24" utf8End24 _ (by simp only [withEnv, s3]) findBlock_utf8End24 hrun3]
      show execTerm (withEnv env3 s3) (.ret (.int 64) (some (.reg "%err.0"))) = _
      rw [execTerm_ret_reg (withEnv env3 s3) "%err.0"
        (.int 64 (BitVec.ofNat 64 t16.toNat)) hevret]
    refine ⟨t16.toNat, mem, ?_, ?_, ?_, ?_⟩
    · refine Eq.trans (runFuel_jump_utf8 (n := 2) hjump1) ?_
      have h2 : runFuel utf8Calls 2 utf8Function (withEnv env1 s3)
          = some (.ret (some (.int 64 (t16.toNat))) (withEnv env3 s3).mem) :=
        runFuel_ret_utf8 (n := 1) hstep3
      rw [show (withEnv env3 s3).mem = mem from by simp only [withEnv, s3]; exact hmem] at h2
      exact h2
    · have his := t16.isLt
      omega
    · have hmide : (t16.toNat = 0) ↔
          (klErrAll (utf8Window bs n nb) (64 * nb) ∧
            ¬ (n ≠ 0 ∧ n % 64 = 0 ∧ klTailByte (klByte bs (n - 1)) = true)) := by
        rw [bitvec_toNat_eq_zero_iff]
        have hC : ¬ (n ≠ 0 ∧ n % 64 = 0 ∧ klTailByte (klByte bs (n - 1)) = true) := by
          intro hc; exact hmod hc.2.1
        rw [ht16zero]
        exact ⟨fun h => ⟨h, hC⟩, fun h => h.1⟩
      rw [hmide]
      show (klErrAll (utf8Window bs n nb) (64 * nb) ∧
          ¬ (n ≠ 0 ∧ n % 64 = 0 ∧ klTailByte (klByte bs (n - 1)) = true)) ↔
        ValidPrefix (ByteString.literal (utf8Window bs n nb))
      exact klErrAll_window_iff bs n nb hn hnb
    · rfl

/-! ### The entry and the gate selection -/

theorem ofInt64_63 : (BitVec.ofInt 64 63 : BitVec 64) = BitVec.ofNat 64 63 := by decide
theorem ofInt64_6_toNat : (BitVec.ofInt 64 6 : BitVec 64).toNat = 6 := by decide
theorem ofInt64_64_toNat : (BitVec.ofInt 64 64 : BitVec 64).toNat = 64 := by decide
theorem ofInt64_0 : (BitVec.ofInt 64 0 : BitVec 64) = 0 := by decide

theorem stage_ofNat64_add63 (n : Nat) (hn : n + 63 < 2 ^ 64) :
    (BitVec.ofNat 64 n + BitVec.ofInt 64 63) = BitVec.ofNat 64 (n + 63) := by
  rw [ofInt64_63]
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h63 : (63 : Nat) % 2 ^ 64 = 63 := by decide
  rw [h63]
  have hn64 : n < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hn64, Nat.mod_eq_of_lt hn]

theorem stage_div44_ofNat (n nb : Nat) (hlen : n + 63 < 2 ^ 64) (hnb : nb = (n + 63) / 64) :
    ((BitVec.ofNat 64 n + BitVec.ofInt 64 63) >>> (BitVec.ofInt 64 6).toNat)
      = BitVec.ofNat 64 nb := by
  rw [stage_ofNat64_add63 n hlen, ofInt64_6_toNat]
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hx : (n + 63) % 2 ^ 64 = n + 63 := Nat.mod_eq_of_lt hlen
  rw [hx, Nat.shiftRight_eq_div_pow]
  have h64 : (2 : Nat) ^ 6 = 64 := by decide
  rw [h64, hnb]
  symm
  exact Nat.mod_eq_of_lt (by
    have := Nat.div_le_self (n + 63) 64
    omega)

theorem stage_ofNat64_ult_false (n : Nat) (hlen : n + 63 < 2 ^ 64) (hpos : 0 < n) :
    BitVec.ult (BitVec.ofNat 64 n + BitVec.ofInt 64 63) (BitVec.ofInt 64 64) = false := by
  rw [stage_ofNat64_add63 n hlen, BitVec.ult_eq_decide, ofInt64_64_toNat, BitVec.toNat_ofNat]
  have hx : (n + 63) % 2 ^ 64 = n + 63 := Nat.mod_eq_of_lt hlen
  rw [hx]
  rw [decide_eq_false_iff_not]
  omega

theorem ofNat32_ungated_ne (ungated : Bool) :
    ((BitVec.ofNat 32 (if ungated then 1 else 0)) = (BitVec.ofInt 32 0 : BitVec 32))
      ↔ ungated = false := by
  have h0 : (BitVec.ofInt 32 0 : BitVec 32) = 0 := by decide
  rw [h0]
  cases ungated with
  | false => decide
  | true => decide

/-! ### The headline: `utf8_stage_refines` -/

theorem packLanes_replicate_zero {w : Nat} (k : Nat) :
    packLanes (List.replicate k (0 : BitVec w)) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, packLanes]
      rw [show ((0 : BitVec w)).toNat = 0 from rfl, ih, Nat.mul_zero, Nat.add_zero]

theorem bytesToNat_replicate_zero (k : Nat) :
    bytesToNat (List.replicate k (0x00 : UInt8)) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, bytesToNat]
      rw [show ((0x00 : UInt8)).toNat = 0 from rfl, ih, Nat.mul_zero, Nat.add_zero]

theorem ofInt32_1 : (BitVec.ofInt 32 1 : BitVec 32) = 1 := by decide

theorem utf8_stage_refines
    (bs : LeanLLVM.JSON.Bytes) (n nb : Nat) (mem : Mem) (b : Nat) (ungated : Bool)
    (hn : n = bs.length) (hnb : nb = (n + 63) / 64)
    (hb : 3 ≤ b) (hlen : n + 63 < 2 ^ 64) (haddr : n < 2 ^ 63)
    (hread : readBytes mem (b - 3) (3 + 64 * nb)
      = some (utf8Window bs.toList n nb))
    (hpos : 0 < n) :
    ∃ (err' : Nat) (mem' : Mem),
      runFuel utf8Calls (fuelOf nb) utf8Function
        { (initState utf8Function [.ptr b, .int 64 n, .int 32 (if ungated then 1 else 0)])
          with mem := mem } = some (.ret (some (.int 64 err')) mem') ∧
      (err' = 0 ∨ err' = 1) ∧
      (err' = 0 ↔ utf8WinPrefix (utf8Window bs.toList n nb)) ∧
      mem' = mem := by
  have hn64 : n < 2 ^ 64 := by omega
  have hnlist : n = bs.toList.length := by
    rw [hn]
    simp only [ByteString.length_eq_size]
    exact (ByteString.toList_length bs).symm
  have hnb' : nb = (bs.toList.length + 63) / 64 := by rw [hnb, hnlist]
  have hspan : 64 * (nb - 1) < 2 ^ 63 := utf8SpanBound n nb hnb haddr hpos
  have hnb1 : 1 ≤ nb := by
    rw [hnb]
    exact Nat.div_pos
      (Nat.le_trans (by decide : 64 ≤ 1 + 63)
        (Nat.add_le_add_right (Nat.succ_le_of_lt hpos) 63)) (by decide)
  let S0 : State :=
    { (initState utf8Function [.ptr b, .int 64 n, .int 32 (if ungated then 1 else 0)])
        with mem := mem }
  have hS0pc : S0.pc = "entry" := by
    simp only [S0, initState, utf8Function, List.map, List.zip, lookupName]
    simp [Function.entry?, List.head?]
    rfl
  have hS0b : lookupName S0.env "%b" = some (.ptr b) := by
    simp [S0, initState, utf8Function, List.zip, List.map, lookupName]
  have hS0n : lookupName S0.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) := by
    simp [S0, initState, utf8Function, List.zip, List.map, lookupName]
  have hS0u : lookupName S0.env "%ungated"
      = some (.int 32 (BitVec.ofNat 32 (if ungated then 1 else 0))) := by
    simp [S0, initState, utf8Function, List.zip, List.map, lookupName]
    split <;> rfl
  obtain ⟨env1, hrunE, hdiv, hcmp⟩ := utf8Entry_run S0.env S0 n hS0n
  have hdiv1 : lookupName env1 "%div44" = some (.int 64 (BitVec.ofNat 64 nb)) := by
    rw [stage_div44_ofNat n nb hlen hnb] at hdiv
    exact hdiv
  have hb1e : lookupName env1 "%b" = some (.ptr b) := by
    have h := denoteCode_lookupName utf8Calls utf8Entry.instrs "%b"
      (by decide) (withEnv S0.env S0) (withEnv env1 S0) hrunE
    have h' : lookupName env1 "%b" = lookupName S0.env "%b" := by
      simpa [withEnv] using h
    exact h'.trans hS0b
  have hn1e : lookupName env1 "%n" = some (.int 64 (BitVec.ofNat 64 n)) := by
    have h := denoteCode_lookupName utf8Calls utf8Entry.instrs "%n"
      (by decide) (withEnv S0.env S0) (withEnv env1 S0) hrunE
    have h' : lookupName env1 "%n" = lookupName S0.env "%n" := by
      simpa [withEnv] using h
    exact h'.trans hS0n
  have hu1e : lookupName env1 "%ungated"
      = some (.int 32 (BitVec.ofNat 32 (if ungated then 1 else 0))) := by
    have h := denoteCode_lookupName utf8Calls utf8Entry.instrs "%ungated"
      (by decide) (withEnv S0.env S0) (withEnv env1 S0) hrunE
    have h' : lookupName env1 "%ungated" = lookupName S0.env "%ungated" := by
      simpa [withEnv] using h
    exact h'.trans hS0u
  have hbitE : (BitVec.ofBool (BitVec.ult (BitVec.ofNat 64 n + BitVec.ofInt 64 63)
      (BitVec.ofInt 64 64)) : BitVec 1) = 0 := by
    rw [ofBool_bool_eq_zero]
    exact stage_ofNat64_ult_false n hlen hpos
  have hstepE : step utf8Calls utf8Function S0
      = .jump (withEnv env1 { S0 with pc := "for.body.lr.ph", pre := some "entry" }) := by
    have h1 : step utf8Calls utf8Function (withEnv S0.env S0)
        = execTerm (withEnv env1 S0) utf8Entry.term :=
      step_of_utf8 _ "entry" utf8Entry _ hS0pc findBlock_utf8Entry hrunE
    have h2 : (withEnv S0.env S0) = S0 := rfl
    rw [h2] at h1
    rw [h1]
    show execTerm (withEnv env1 S0)
        (.condbr (.reg "%cmp74.not") "for.cond.cleanup" "for.body.lr.ph") = _
    have hev : evalOperand (withEnv env1 S0) (.reg "%cmp74.not")
        = some (.int 1 (BitVec.ofBool (BitVec.ult (BitVec.ofNat 64 n
            + BitVec.ofInt 64 63) (BitVec.ofInt 64 64)))) := by
      rw [evalOperand_reg_utf8]; exact hcmp
    rw [execTerm_condbr_false hev hbitE]
    simp only [withEnv, hS0pc]
  -- the gate selection
  let S1 : State := { S0 with pc := "for.body.lr.ph", pre := some "entry" }
  obtain ⟨env2, hrunL, htobool⟩ :=
    utf8LrPh_run env1 S1 (BitVec.ofNat 32 (if ungated then 1 else 0)) hu1e
  have hdiv2 : lookupName env2 "%div44" = some (.int 64 (BitVec.ofNat 64 nb)) :=
    (denoteCode_lookupName utf8Calls utf8LrPh.instrs "%div44" (by decide)
      (withEnv env1 S1) (withEnv env2 S1) hrunL).trans (by simpa [withEnv] using hdiv1)
  have hb2 : lookupName env2 "%b" = some (.ptr b) :=
    (denoteCode_lookupName utf8Calls utf8LrPh.instrs "%b" (by decide)
      (withEnv env1 S1) (withEnv env2 S1) hrunL).trans (by simpa [withEnv] using hb1e)
  have hn2 : lookupName env2 "%n" = some (.int 64 (BitVec.ofNat 64 n)) :=
    (denoteCode_lookupName utf8Calls utf8LrPh.instrs "%n" (by decide)
      (withEnv env1 S1) (withEnv env2 S1) hrunL).trans (by simpa [withEnv] using hn1e)
  have hUng : (BitVec.ofNat 32 (if ungated then 1 else 0)
      = (BitVec.ofInt 32 0 : BitVec 32)) ↔ ungated = false := ofNat32_ungated_ne ungated
  -- the preheader operands
  let u8k0 : List (BitVec 64) := List.replicate 4 (BitVec.ofInt 64 0)
  have hu8k0len : u8k0.length = 4 := by simp [u8k0]
  have hpack0 : packLanes u8k0 = bytesToNat (klAcc bs.toList 0) := by
    rw [show klAcc bs.toList 0 = List.replicate 32 (0x00 : UInt8) from rfl,
      bytesToNat_replicate_zero]
    exact packLanes_replicate_zero 4
  -- case on the gate
  cases ungated with
  | false =>
      -- the gated loop
      have hbitL : (BitVec.ofBool (decide (BitVec.ofNat 32 0
          = (BitVec.ofInt 32 0 : BitVec 32))) : BitVec 1) = 1 := by
        rw [ofBool_bool_eq_one, decide_eq_true_eq]
        exact (hUng).mpr rfl
      have hstepL : step utf8Calls utf8Function (withEnv env1 S1)
          = .jump (withEnv env2 { S1 with pc := "for.body.us", pre := some "for.body.lr.ph" }) := by
        have h1 : step utf8Calls utf8Function (withEnv env1 S1)
            = execTerm (withEnv env2 S1) utf8LrPh.term :=
          step_of_utf8 _ "for.body.lr.ph" utf8LrPh _ (by rfl) findBlock_utf8LrPh hrunL
        rw [h1]
        show execTerm (withEnv env2 S1)
            (.condbr (.reg "%tobool.not") "for.body.us" "for.body") = _
        have hev : evalOperand (withEnv env2 S1) (.reg "%tobool.not")
            = some (.int 1 (BitVec.ofBool (decide (BitVec.ofNat 32 0
                = (BitVec.ofInt 32 0 : BitVec 32))))) := by
          rw [evalOperand_reg_utf8]; exact htobool
        rw [execTerm_condbr_true hev hbitL]
        simp only [withEnv, S1]
      let S2 : State := { S1 with pc := "for.body.us", pre := some "for.body.lr.ph" }
      have hpAscii : (BitVec.ofInt 32 1 : BitVec 32) = 1 →
          ∀ b' ∈ klPre (utf8Window bs.toList n nb) 0, b'.toNat < 0x80 := by
        intro _ b' hb'
        simp only [klPre, Nat.zero_mul, List.drop_zero] at hb'
        change b' ∈ List.take 3 (List.replicate 3 (0x00 : UInt8) ++ bs.toList
          ++ List.replicate (64 * nb - n) 0x00) at hb'
        rw [List.append_assoc] at hb'
        rw [List.take_append_of_le_length (l₁ := List.replicate 3 (0x00 : UInt8))
          (l₂ := bs.toList ++ List.replicate (64 * nb - n) 0x00) (i := 3) (by simp)] at hb'
        rw [List.take_replicate, Nat.min_self] at hb'
        simp only [List.mem_replicate] at hb'
        obtain ⟨-, hb''⟩ := hb'
        rw [hb'']
        decide
      obtain ⟨env', s', u8k', t, hpc', hpre', hmem', ht, hU', hlen', hpack', hb', hn',
        hdiv', hrun'⟩ :=
        utf8Gated_loop_run bs.toList n nb b mem hnb' hread hb hspan nb 0 env2 S2
          "for.body.lr.ph" (.imm (.int 32 (BitVec.ofInt 32 1)))
          (.imm (.splat 4 64 (BitVec.ofInt 64 0)))
          (.imm (.int 64 (BitVec.ofInt 64 0))) u8k0 (BitVec.ofInt 32 1)
          hnb1 (by omega) (by rfl) (by rfl) rfl
          (by simp [phiIncoming])
          (by simp [phiIncoming])
          (by simp [phiIncoming])
          (by simp only [evalOperand]; rfl)
          (by simp only [withEnv, evalOperand]; rfl)
          (by simp only [withEnv, evalOperand]; rfl)
          hb2 hdiv2 hn2 hu8k0len hpack0 (Or.inr ofInt32_1) hpAscii
      obtain ⟨err', mem', hrunC, herr01, herrVP, hmemC⟩ :=
        utf8_cleanup_run bs.toList n nb b mem false env' s' "if.end14.us"
          (.reg "%u8k.2.us") u8k' hnlist hnb hb haddr hpos hread
          (by rw [← hpc']) (by rw [← hpre']) hmem'
          (by simp [phiIncoming]) (by rw [evalOperand_reg_utf8]; exact hU')
          hlen' hpack' hn' hb'
      have hloop : runFuel utf8Calls (t + 3) utf8Function (withEnv env2 S2)
          = some (.ret (some (.int 64 err')) mem') := by
        rw [hrun' 3]; exact hrunC
      have htotal : runFuel utf8Calls (1 + (1 + (t + 3))) utf8Function S0
          = some (.ret (some (.int 64 err')) mem') := by
        rw [show (1 : Nat) + (1 + (t + 3)) = (1 + (t + 3)) + 1 from by omega,
          runFuel_jump_utf8 hstepE,
          show (1 + (t + 3)) = (t + 3) + 1 from by omega,
          runFuel_jump_utf8 hstepL, hloop]
      have hle : 1 + (1 + (t + 3)) ≤ fuelOf nb := by
        have := ht
        rw [fuelOf_eq]
        omega
      refine ⟨err', mem', ?_, herr01, herrVP, hmemC⟩
      exact runFuel_mono_le hle htotal
  | true =>
      -- the ungated loop
      have hbitL : (BitVec.ofBool (decide (BitVec.ofNat 32 1
          = (BitVec.ofInt 32 0 : BitVec 32))) : BitVec 1) = 0 := by
        rw [ofBool_bool_eq_zero, decide_eq_false_iff_not]
        intro hh
        exact absurd (hUng.mp hh) (by decide)
      have hstepL : step utf8Calls utf8Function (withEnv env1 S1)
          = .jump (withEnv env2 { S1 with pc := "for.body", pre := some "for.body.lr.ph" }) := by
        have h1 : step utf8Calls utf8Function (withEnv env1 S1)
            = execTerm (withEnv env2 S1) utf8LrPh.term :=
          step_of_utf8 _ "for.body.lr.ph" utf8LrPh _ (by rfl) findBlock_utf8LrPh hrunL
        rw [h1]
        show execTerm (withEnv env2 S1)
            (.condbr (.reg "%tobool.not") "for.body.us" "for.body") = _
        have hev : evalOperand (withEnv env2 S1) (.reg "%tobool.not")
            = some (.int 1 (BitVec.ofBool (decide (BitVec.ofNat 32 1
                = (BitVec.ofInt 32 0 : BitVec 32))))) := by
          rw [evalOperand_reg_utf8]; exact htobool
        rw [execTerm_condbr_false hev hbitL]
        simp only [withEnv, S1]
      let S2 : State := { S1 with pc := "for.body", pre := some "for.body.lr.ph" }
      obtain ⟨env', s', u8k', hpc', hpre', hmem', hU', hlen', hpack', hb', hn',
        hdiv', hrun'⟩ :=
        utf8Ungated_loop_run bs.toList n nb b mem hnb' hread hb hspan nb 0 env2 S2
          "for.body.lr.ph"
          (.imm (.splat 4 64 (BitVec.ofInt 64 0)))
          (.imm (.int 64 (BitVec.ofInt 64 0))) u8k0
          hnb1 (by omega) (by rfl) (by rfl) rfl
          (by simp [phiIncoming])
          (by simp [phiIncoming])
          (by simp only [evalOperand]; rfl)
          (by simp only [withEnv, evalOperand]; rfl)
          hb2 hdiv2 hn2 hu8k0len hpack0
      obtain ⟨err', mem', hrunC, herr01, herrVP, hmemC⟩ :=
        utf8_cleanup_run bs.toList n nb b mem false env' s' "for.body"
          (.reg "%or.i47") u8k' hnlist hnb hb haddr hpos hread
          (by rw [← hpc']) (by rw [← hpre']) hmem'
          (by simp [phiIncoming]) (by rw [evalOperand_reg_utf8]; exact hU')
          hlen' hpack' hn' hb'
      have hloop : runFuel utf8Calls (nb + 3) utf8Function (withEnv env2 S2)
          = some (.ret (some (.int 64 err')) mem') := by
        rw [hrun' 3]; exact hrunC
      have htotal : runFuel utf8Calls (1 + (1 + (nb + 3))) utf8Function S0
          = some (.ret (some (.int 64 err')) mem') := by
        rw [show (1 : Nat) + (1 + (nb + 3)) = (1 + (nb + 3)) + 1 from by omega,
          runFuel_jump_utf8 hstepE,
          show (1 + (nb + 3)) = (nb + 3) + 1 from by omega,
          runFuel_jump_utf8 hstepL, hloop]
      have hle : 1 + (1 + (nb + 3)) ≤ fuelOf nb := by
        rw [fuelOf_eq]; omega
      refine ⟨err', mem', ?_, herr01, herrVP, hmemC⟩
      exact runFuel_mono_le hle htotal

theorem utf8_stage_refines_chars
    (bs : LeanLLVM.JSON.Bytes) (n nb : Nat) (mem : Mem) (b : Nat) (ungated : Bool)
    (hn : n = bs.length) (hnb : nb = (n + 63) / 64)
    (hb : 3 ≤ b) (hlen : n + 63 < 2 ^ 64) (haddr : n < 2 ^ 63)
    (hread : readBytes mem (b - 3) (3 + 64 * nb) = some (utf8Window bs.toList n nb))
    (hpos : 0 < n) (hmod : n % 64 ≠ 0) :
    ∃ (err' : Nat) (mem' : Mem),
      runFuel utf8Calls (fuelOf nb) utf8Function
        { (initState utf8Function [.ptr b, .int 64 n, .int 32 (if ungated then 1 else 0)])
          with mem := mem } = some (.ret (some (.int 64 err')) mem') ∧
      (err' = 0 ↔ Utf8Chars bs) ∧
      mem' = mem := by
  obtain ⟨err', mem', hrun, -, hVP, hmem'⟩ :=
    utf8_stage_refines bs n nb mem b ungated hn hnb hb hlen haddr hread hpos
  have hnle : n ≤ 64 * nb := by
    rw [hnb]; exact LeanLLVM.Refinement.JsonUtf8IR.le_mul_div_sixtyfour n
  have hne : 64 * nb ≠ n := by
    intro h
    apply hmod
    rw [← h]
    exact Nat.mul_mod_right 64 nb
  have hp1 : 1 ≤ 64 * nb - n := by omega
  refine ⟨err', mem', hrun, ?_, hmem'⟩
  have hbridge := validPrefix_padded_iff_utf8Chars bs.toList (64 * nb - n) hp1
  rw [hVP]
  show ValidPrefix (ByteString.literal (List.replicate 3 (0x00 : UInt8) ++ bs.toList
      ++ List.replicate (64 * nb - n) (0x00 : UInt8))) ↔ Utf8Chars bs
  rw [show ByteString.literal bs.toList = bs from ByteString.literal_toList bs] at hbridge
  exact hbridge

theorem utf8_stage_refines_mod0
    (bs : LeanLLVM.JSON.Bytes) (n nb : Nat) (mem : Mem) (b : Nat) (ungated : Bool)
    (hn : n = bs.length) (hnb : nb = (n + 63) / 64)
    (hb : 3 ≤ b) (hlen : n + 63 < 2 ^ 64) (haddr : n < 2 ^ 63)
    (hread : readBytes mem (b - 3) (3 + 64 * nb) = some (utf8Window bs.toList n nb))
    (hpos : 0 < n) (hmod : n % 64 = 0) :
    ∃ (err' : Nat) (mem' : Mem),
      runFuel utf8Calls (fuelOf nb) utf8Function
        { (initState utf8Function [.ptr b, .int 64 n, .int 32 (if ungated then 1 else 0)])
          with mem := mem } = some (.ret (some (.int 64 err')) mem') ∧
      (err' = 0 ↔ ValidPrefix bs) ∧
      mem' = mem := by
  obtain ⟨err', mem', hrun, -, hVP, hmem'⟩ :=
    utf8_stage_refines bs n nb mem b ungated hn hnb hb hlen haddr hread hpos
  refine ⟨err', mem', hrun, ?_, hmem'⟩
  have hp0 : 64 * nb - n = 0 := pad_eq_zero_of_mod hnb hmod
  rw [hVP]
  show ValidPrefix (ByteString.literal (List.replicate 3 (0x00 : UInt8) ++ bs.toList
      ++ List.replicate (64 * nb - n) (0x00 : UInt8))) ↔ ValidPrefix bs
  have hz : List.replicate (0 : Nat) (0x00 : UInt8) = [] := List.replicate_zero
  rw [hp0, hz, List.append_nil]
  have hsplit : List.replicate 3 (0x00 : UInt8) ++ bs.toList
      = 0x00 :: 0x00 :: 0x00 :: bs.toList := rfl
  rw [hsplit]
  constructor
  · intro h
    have h' := validPrefix_three_cons h
    rwa [ByteString.literal_toList] at h'
  · intro h
    apply validPrefix_three_cons_back
    rwa [ByteString.literal_toList]


set_option linter.unusedVariables false in
/-- **The stage's verdict at `n = 0`.**

`utf8_stage_refines` does not cover this case and this is not a case of it: at
`n = 0` the body reads no byte, so the headline's hypothesis on the
`3 + 64 * nb`-byte window would be a fiction about a window the run never
touches, and its `hpos` is false.  Stated separately, the case says what the run
actually does: the accumulator is the empty fold and the window has no block.

The run is three steps.  `entry` computes `%div44 = 0` and `%cmp74.not = true`,
so control passes both loops to `for.cond.cleanup`.  The reduce's `ptestz` of the
zero accumulator — the `entry` phi's zero splat — answers one, so `%tobool16.not`
is zero; the tail guard is false because `%n` is zero; and `if.end24`
zero-extends that zero to the returned word.  No block and no tail is read, so
the caller's memory comes back unchanged, and three steps sit inside
`fuelOf 0 = 8` with five to spare.

The hypothesis set is the headline's, not a narrower one: `hn`, `hnb`, `hb` and
`hread` are exactly the obligations `utf8_stage_refines` puts on a caller, and at
`n = 0` the read hypothesis is precisely the staged window's three zero prefix
bytes.  The body consumes none of them here, and they stay in the statement so
that a caller splitting on `n` discharges the same obligations on either side.
The headline's other two bounds are absent because `n = 0` settles them outright
(`0 + 63 < 2 ^ 64`, `0 < 2 ^ 63`), and `hpos` is absent because it is false.

Footprint: `[propext, Quot.sound]` — no `Classical.choice`, since the entry's
`%n` lookup is read through `lookupName_initState_utf8` and the two phi edges
through `decide` rather than through the `simp` route that decides a string
disequality by `String.ofList_injective`. -/
theorem utf8_stage_refines_zero
    (bs : LeanLLVM.JSON.Bytes) (n nb : Nat) (mem : Mem) (b : Nat) (ungated : Bool)
    (hn : n = bs.length) (hnb : nb = (n + 63) / 64)
    (hb : 3 ≤ b)
    (hread : readBytes mem (b - 3) (3 + 64 * nb) = some (utf8Window bs.toList n nb))
    (hn0 : n = 0) :
    runFuel utf8Calls (fuelOf nb) utf8Function
      { (initState utf8Function [.ptr b, .int 64 n, .int 32 (if ungated then 1 else 0)])
        with mem := mem } = some (.ret (some (.int 64 0)) mem) := by
  subst hn0
  have hnb0 : nb = 0 := by
    rw [hnb]
  let S0 : State :=
    { (initState utf8Function [.ptr b, .int 64 0, .int 32 (if ungated then 1 else 0)])
        with mem := mem }
  have hS0pc : S0.pc = "entry" :=
    initState_utf8_pc b 0 (BitVec.ofNat 32 (if ungated then 1 else 0))
  have hS0n : lookupName S0.env "%n" = some (.int 64 (BitVec.ofNat 64 0)) :=
    (lookupName_initState_utf8 b 0 (BitVec.ofNat 32 (if ungated then 1 else 0))).2.1
  obtain ⟨env1, hrunE, hdiv, hcmp⟩ := utf8Entry_run S0.env S0 0 hS0n
  let S1 : State := { S0 with pc := "for.cond.cleanup", pre := some "entry" }
  have hn1 : lookupName env1 "%n" = some (.int 64 (BitVec.ofNat 64 0)) := by
    have h := denoteCode_lookupName utf8Calls utf8Entry.instrs "%n"
      (by decide) (withEnv S0.env S0) (withEnv env1 S0) hrunE
    have h' : lookupName env1 "%n" = lookupName S0.env "%n" := by
      simpa [withEnv] using h
    exact h'.trans hS0n
  have hbitE : (BitVec.ofBool (BitVec.ult (BitVec.ofNat 64 0 + BitVec.ofInt 64 63)
      (BitVec.ofInt 64 64)) : BitVec 1) = 1 := by
    rw [ofBool_bool_eq_one, stage_ofNat64_add63 0 (by decide), BitVec.ult_eq_decide,
      ofInt64_64_toNat, BitVec.toNat_ofNat]
    rw [show (0 + 63) % 2 ^ 64 = 63 from by decide]
    decide
  have hstepE : step utf8Calls utf8Function S0 = .jump (withEnv env1 S1) := by
    have h1 : step utf8Calls utf8Function (withEnv S0.env S0)
        = execTerm (withEnv env1 S0) utf8Entry.term :=
      step_of_utf8 _ "entry" utf8Entry _ hS0pc findBlock_utf8Entry hrunE
    have h2 : (withEnv S0.env S0) = S0 := rfl
    rw [h2] at h1
    rw [h1]
    show execTerm (withEnv env1 S0)
        (.condbr (.reg "%cmp74.not") "for.cond.cleanup" "for.body.lr.ph") = _
    have hev : evalOperand (withEnv env1 S0) (.reg "%cmp74.not")
        = some (.int 1 (BitVec.ofBool (BitVec.ult (BitVec.ofNat 64 0
            + BitVec.ofInt 64 63) (BitVec.ofInt 64 64)))) := by
      rw [evalOperand_reg_utf8]; exact hcmp
    rw [execTerm_condbr_true hev hbitE]
    simp only [withEnv, S1, hS0pc]
  let u8k0 : List (BitVec 64) := List.replicate 4 (BitVec.ofInt 64 0)
  have hu8k0len : u8k0.length = 4 := by simp [u8k0]
  obtain ⟨env2, hrunC, h36, ht16, ht19, hcond⟩ :=
    utf8Reduce env1 S1 "entry" (.imm (.splat 4 64 (BitVec.ofInt 64 0))) u8k0 0
      rfl (by decide) (by simp only [evalOperand]; rfl) hu8k0len hn1
  have hpack0 : packLanes u8k0 = 0 := by
    have hz : u8k0 = List.replicate 4 (0 : BitVec 64) := by
      simp only [u8k0, show (BitVec.ofInt 64 0 : BitVec 64) = 0 from by decide]
    rw [hz]
    exact packLanes_replicate_zero 4
  have h256 : BitVec.ofNat 256 (packLanes u8k0) = (0 : BitVec 256) :=
    (ofNat256_eq_zero_iff _ (by rw [hpack0]; decide)).mpr hpack0
  have hpt : BitLanes.ptestz (BitVec.ofNat 256 (packLanes u8k0))
      (BitVec.ofNat 256 (packLanes u8k0)) = (1 : BitVec 32) := by
    rw [h256, BitLanes.ptestz_eq_one_iff]
    simp
  have ht16z : lookupName env2 "%tobool16.not" = some (.int 1 (0 : BitVec 1)) := by
    rw [ht16, hpt, ofInt32_zero]
    rw [show (BitVec.ofBool (decide ((1 : BitVec 32) = (0 : BitVec 32))) : BitVec 1) = 0
      from (ofBool_bool_eq_zero (decide ((1 : BitVec 32) = (0 : BitVec 32)))).mpr (by decide)]
  have hcondz : lookupName env2 "%or.cond45" = some (.int 1 (0 : BitVec 1)) := by
    rw [hcond]
    have h1 : (BitVec.ofBool (decide (BitVec.ofNat 64 0 ≠ (BitVec.ofInt 64 0 : BitVec 64)))
        : BitVec 1) = 0 :=
      (ofBool_bool_eq_zero (decide (BitVec.ofNat 64 0 ≠ (BitVec.ofInt 64 0 : BitVec 64)))).mpr
        (by decide)
    have h2 : (BitVec.ofBool (decide (BitVec.ofNat 64 0 &&& (BitVec.ofInt 64 63 : BitVec 64)
        = (BitVec.ofInt 64 0 : BitVec 64))) : BitVec 1) = 1 :=
      (ofBool_bool_eq_one (decide (BitVec.ofNat 64 0 &&& (BitVec.ofInt 64 63 : BitVec 64)
        = (BitVec.ofInt 64 0 : BitVec 64)))).mpr (by decide)
    rw [h1, h2]
    simp
  let S2 : State := { S1 with pc := "if.end24", pre := some "for.cond.cleanup" }
  have hstepC : step utf8Calls utf8Function (withEnv env1 S1) = .jump (withEnv env2 S2) := by
    have h1 : step utf8Calls utf8Function (withEnv env1 S1)
        = execTerm (withEnv env2 S1) utf8Cleanup.term :=
      step_of_utf8 _ "for.cond.cleanup" utf8Cleanup _ (by simp only [withEnv, S1])
        findBlock_utf8Cleanup hrunC
    rw [h1]
    show execTerm (withEnv env2 S1) (.condbr (.reg "%or.cond45") "if.then20" "if.end24") = _
    have hev : evalOperand (withEnv env2 S1) (.reg "%or.cond45")
        = some (.int 1 (0 : BitVec 1)) := by
      rw [evalOperand_reg_utf8]; exact hcondz
    rw [execTerm_condbr_false hev rfl]
    simp only [withEnv, S2, S1]
  obtain ⟨env3, hrunR, hval⟩ := utf8Return env2 S2 "for.cond.cleanup"
    (.reg "%tobool16.not") (0 : BitVec 1) (by simp only [S2]) (by decide)
    (by rw [evalOperand_reg_utf8]; exact ht16z)
  have hevret : evalOperand (withEnv env3 S2) (.reg "%err.0") = some (.int 64 0) := by
    rw [evalOperand_reg_utf8]
    exact hval
  have hstepR : step utf8Calls utf8Function (withEnv env2 S2)
      = .ret (some (.int 64 0)) (withEnv env3 S2) := by
    rw [step_of_utf8 _ "if.end24" utf8End24 _ (by simp only [withEnv, S2]) findBlock_utf8End24 hrunR]
    show execTerm (withEnv env3 S2) (.ret (.int 64) (some (.reg "%err.0"))) = _
    rw [execTerm_ret_reg (withEnv env3 S2) "%err.0" (.int 64 0) hevret]
  have hfuel : fuelOf nb = 8 := by rw [fuelOf_eq, hnb0]
  rw [hfuel]
  refine Eq.trans (runFuel_jump_utf8 (n := 7) hstepE) ?_
  refine Eq.trans (runFuel_jump_utf8 (n := 6) hstepC) ?_
  simpa only [withEnv, S2, S1, S0] using runFuel_ret_utf8 (n := 5) hstepR

/-- info: 'LeanLLVM.Refinement.JsonUtf8Steps.utf8_stage_refines_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms utf8_stage_refines_zero
end LeanLLVM.Refinement.JsonUtf8Steps
