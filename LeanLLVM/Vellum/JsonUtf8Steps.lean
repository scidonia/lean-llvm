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

theorem block_arg_lo (l : List UInt8) (m : Nat) :
    (l.drop m).take 3 ++ ((l.drop (m + 3)).take 64).take 32 = (l.drop m).take 35 := by
  rw [show l.drop (m + 3) = (l.drop m).drop 3 from by rw [List.drop_drop],
    List.take_take, Nat.min_eq_left (by omega : 32 ≤ 64)]
  exact take_append_take_len (l.drop m) 3 32

theorem block_arg_hi (l : List UInt8) (m : Nat) :
    ((l.drop m).take 3 ++ ((l.drop (m + 3)).take 64).take 32).drop 32 ++
      ((l.drop (m + 3)).take 64).drop 32 = (l.drop (m + 32)).take 35 := by
  rw [block_arg_lo l m, List.drop_take, List.drop_take,
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
  simp only [klByte_take_drop _ _ _ _ (by omega : j < 35),
    klByte_take_drop _ _ _ _ (by omega : j + 1 < 35),
    klByte_take_drop _ _ _ _ (by omega : j + 2 < 35),
    klByte_take_drop _ _ _ _ (by omega : j + 3 < 35)]
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

theorem klAcc_zero_iff_klErrAll (bs : List UInt8) (nb : Nat) :
    klAcc bs nb = List.replicate 32 0x00 ↔ klErrAll (0x00 :: 0x00 :: 0x00 :: bs) (64 * nb) := by
  rw [klAcc_zero_iff, klErrAll]
  constructor
  · intro h t ht
    have hbi : t / 64 < nb := by
      refine Nat.div_lt_of_lt_mul ?_
      omega
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
    · have h32' : t % 64 - 32 < 32 := by omega
      have hz : (klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) (t / 64))
          (klBlk (0x00 :: 0x00 :: 0x00 :: bs) (t / 64))).getD (t % 64 - 32) 0x00 = 0 := by
        rw [h (t / 64) hbi, getD_of_lt (List.replicate 32 (0x00 : UInt8)) 0x00 (by simpa using h32'),
          List.getElem_replicate]
      have hw := (klErrBlk_getD_zero_iff bs (t / 64) (t % 64 - 32) h32').mp hz
      rw [← ht']
      have he : 64 * (t / 64) + 32 + (t % 64 - 32) = 64 * (t / 64) + t % 64 := by omega
      rw [← he]
      exact hw.2
  · intro h bi hbi
    apply (eq_replicate_zero_iff_getD _ (klErrBlk_length _ _)).mpr
    intro j hj
    have hlt : 64 * bi + j < 64 * nb := by omega
    have hlt2 : 64 * bi + 32 + j < 64 * nb := by omega
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
  rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega : m ≤ 67 - c)]

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
  rw [h k (by omega), h (k + 1) (by omega), h (k + 2) (by omega), h (k + 3) (by omega)]

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
      have hpackNext : packLanes (unpackLanes 64 4 (bytesToNat (List.zipWith (· ||| ·) (klAcc bs i)
          (klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) i)
            (klBlk (0x00 :: 0x00 :: 0x00 :: bs) i))))) = bytesToNat (klAcc bs (i + 1)) := by
        have hlt := bytesToNat_lt (List.zipWith (· ||| ·) (klAcc bs i)
          (klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) i)
            (klBlk (0x00 :: 0x00 :: 0x00 :: bs) i)))
        rw [List.length_zipWith, klAcc_length, klErrBlk_length, Nat.min_self,
          show (256 : Nat) ^ 32 = 2 ^ 256 from by decide] at hlt
        rw [packLanes_unpackLanes, Nat.mod_eq_of_lt hlt, klAcc_succ bs i]
      have hblkEq : klErrBlk (List.take 3 (utf8Stream bs n nb i))
          (List.take 64 (List.drop 3 (utf8Stream bs n nb i)))
          = klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) i)
              (klBlk (0x00 :: 0x00 :: 0x00 :: bs) i) := by
        have h1 : List.take 3 (utf8Stream bs n nb i)
            = klPre (utf8Window bs n nb) i := by
          rw [klPre, utf8Stream]
        have h2 : List.take 64 (List.drop 3 (utf8Stream bs n nb i))
            = klBlk (utf8Window bs n nb) i := by
          rw [klBlk, utf8Stream, List.drop_drop]
        rw [h1, h2, klErrBlk_window]
      by_cases hlast : i + 1 = nb
      · -- the loop is done: the test leaves for `for.cond.cleanup`
        have hbit : BitVec.ofNat 64 i + BitVec.ofInt 64 1 = BitVec.ofNat 64 nb := by
          rw [hnext, hlast]
        have hjump : step utf8Calls utf8Function (withEnv env s) = .jump
            ({ (withEnv env'' s) with pc := "for.cond.cleanup", pre := some "for.body" } : State) := by
          rw [hstep, execTerm_condbr_true hexit' (ofBool_of_true hbit),
            show (withEnv env'' s).pc = "for.body" from by rw [withEnv]; exact hpc]
        have hpack : packLanes (unpackLanes 64 4 (bytesToNat (List.zipWith (· ||| ·) (klAcc bs i)
            (klErrBlk (List.take 3 (utf8Stream bs n nb i))
              (List.take 64 (List.drop 3 (utf8Stream bs n nb i))))))) = bytesToNat (klAcc bs nb) := by
          rw [hblkEq, hpackNext, hlast]
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
            (by rw [hblkEq]; exact hpackNext)
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
      intro hc
      have h2 : (0x80 : Nat) ≤ (a ||| b).toNat := h.mpr hc
      omega
    omega
  · rintro ⟨h1, h2⟩
    have hna : ¬ ((0x80 : Nat) ≤ a.toNat ∨ (0x80 : Nat) ≤ b.toNat) := by omega
    have hn : ¬ (0x80 : Nat) ≤ (a ||| b).toNat := fun hP => hna (h.mp hP)
    omega

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

end LeanLLVM.Vellum.JsonUtf8Steps
