/-
`num_fast_el1`'s three out-of-line callees, answered, and the two tables staged.

`JsonStage2NumFastArm` states the conversion arm's boundary as an environment's
gap: `s2HelperCalls` answers none of `num_d8_el1`, `num_el_el1`, `stk_mul_u64`,
so at each of their sites the body's step is `ub`.  This module supplies the
environment and the staging that boundary names.

**The callee models.**  `kernel/json/measured/numf_el1.h` carries
`num_d8_el1` (eight ASCII digits at a pointer, into a `uint32`), `numel_el.h`
carries `num_el_el1` (the deferred Eisel-Lemire kernel over the `EPOW` table),
and `kernel/json/stage2.c` carries `stk_mul_u64` (a `StkBn` multiplied in place
by a `uint64`).  Each is modelled here from that text:

* `numD8Answer` reads eight bytes, tests each against `'0' … '9'`, and on
  success writes the `uint32` the two SIMD multiplies compute — the decimal
  value of the eight digits — and returns one; otherwise it returns zero and
  writes nothing;
* `numElAnswer` is `num_el_el1`'s control flow: the range gate, the zero
  mantissa's `0.0`, the table lookup, the normalised product's high half, the
  three-value guard window, `el_pack`/`el_exact`'s rounding and the range
  refusal.  Its table is a parameter, `epow : Int → Option EPow`, because the
  kernel reads a `static const` array that is data, not code: a model that
  invented the 91 rows would be asserting the table rather than reading it.
  A missing row is a refusal, which is the staging's default and not the
  kernel's own range test;
* `numStkMulAnswer` reads a `StkBn` (96 `uint64` limbs and the `int` count at
  offset 768), multiplies it by the second argument with `stk_mul_add`'s
  carry chain, and writes the count and limbs back.

**The environment.**  `numFastCalls base epow` answers those three symbols and
delegates every other symbol to `base`; `stage2NumFastCalls` is the composition
with the walk's `s2HelperCalls`, so the lifetime markers, `memset` and the trap
keep their answers and only the conversion's three callees change.

**The tables.**  `NumFastTables` fixes the two tables' addresses through the
environment and their contents through the memory.  `numFastTableEnv` and
`numFastTableMem` are a concrete staging: twenty `NUMF_EL1_P10` rows
(`10 ^ i` as a little-endian `uint64`) and twenty-three `NUMF_EL1_POW10` rows
(`10 ^ i` as binary64).  `numFastTables_holds` is the predicate at that staging.

What this does *not* do is prove `NumFastBodyArm` at the environment.  The arm
is a statement about the whole conversion path — the inlined scan, the inlined
tier-1 arithmetic, the inlined fallback — and its conclusion is `strtodSpec`'s
eight bytes.  Supplying the environment removes the obstruction the arm names
(the `calls` parameter), and the arm is still open; `JsonStage2NumFastArm`'s
header carries the remaining obligations.

**The approximation boundary, precisely.**  The arm's conclusion is *not* an
unconditional equality this tree can assert, because one of the body's three
branches is an approximation whose exactness is the tree's obligation rather
than a fact these definitions establish:

* **tier 1** (`digitCount ≤ 15`, `|eff| ≤ 22`) is a single IEEE multiply or
  divide of exact operands, and `LeanLLVM.StrtodTier1.emittedRefinesOn_tier1`
  proves its binary64 encoding is `strtodSpec`'s at the model;
* **tier 2** is `numElEl1`'s Eisel-Lemire decision.  Outside the guard window
  `hp ∈ [hh - 2, hh]` it rounds from the high 64 bits of `W * hi` alone, without
  forming the exact rational and without the low half of the product.  The
  window's decision *is* proved to be `roundMag`'s for the kernel as
  `LeanLLVM.ElGuardRefine` writes it: `elGuardRefinesOn` states and proves
  `elTier2Code w q = some c → roundMag (valueTicks w q) = .fin c` for
  `0 < w < 2 ^ 64`, with `not_elGuardRefinesUnbounded` showing the word bound is
  load-bearing, and `JsonStage2Body.numTier2Binary_eq_strtodSpec` composes it at
  the model.  What is *not* in this tree is the correspondence from this file's
  `numElEl1 epow` — the body's callee model, with the table as a parameter — to
  `elTier2Code`: the two are written from the same C text but no lemma relates
  their `elPack`/`elExact` forms, so a body-level arm at `stage2NumFastCalls`
  inherits that gap rather than `elGuardRefinesOn`'s result.  The stop is that
  bridge, not the guard slice;
* **tier 3** (the fallback) is reached whenever the kernel refuses, and its
  obligation is the bracketing argument `LeanLLVM.StrtodTier3` states and
  partly proves.

So the boundary this module and `JsonStage2NumFastArm` leave is: the environment
is supplied and the three sites are reachable, while the
conversion's agreement with `strtodSpec` is conditional on the tier-2 kernel's
exactness bound and the tier-3 traversal, neither of which is a staging fact.
-/
import LeanLLVM.Refinement.JsonStage2NumFastArm
import LeanLLVM.Binary64

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval

/-! ### `num_d8_el1`: eight ASCII digits into a `uint32`

`numf_el1.h`'s reader subtracts `'0'` from each of the eight bytes and accepts
when every difference is at most nine, then computes the eight digits' decimal
number by the two `madd` instructions.  `d8Value` is that number, `none` at a
non-digit. -/

/-- One ASCII digit's value, or `none` when the byte is outside `'0' … '9'`.
The C's `(uint8_t)(b - '0') <= 9` is this test in `UInt8` arithmetic. -/
def asciiDigit (b : UInt8) : Option Nat :=
  if 0x30 ≤ b ∧ b ≤ 0x39 then some (b.toNat - 0x30) else none

/-- The eight digits' decimal value: `d8Value [d0,…,d7]` is
`d0 * 10^7 + … + d7`, and `none` when a byte is not a digit. -/
def d8Value : List UInt8 → Option Nat
  | [] => some 0
  | b :: rest =>
      match asciiDigit b, d8Value rest with
      | some d, some v => some (d * 10 ^ rest.length + v)
      | _, _ => none

/-- The reader's answer: a successful read writes the `uint32` value and
returns one; a non-digit or an absent byte writes nothing and returns zero. -/
def numD8Answer (args : List Value) (mem : Mem) (next : Nat) : Option CallOutcome :=
  match args with
  | [.ptr p, .ptr v] =>
      match readBytes mem p 8 with
      | some bs =>
          match d8Value bs with
          | some w =>
              some { ret := .int 32 1, mem := writeBytes mem v (natToBytes w 4),
                     next := next }
          | none => some { ret := .int 32 0, mem := mem, next := next }
      | none => some { ret := .int 32 0, mem := mem, next := next }
  | _ => none

/-- The reader's success answer, at the exact read. -/
theorem numD8Answer_read {p v w : Nat} {bs : List UInt8} {mem : Mem} {next : Nat}
    (hread : readBytes mem p 8 = some bs) (hval : d8Value bs = some w) :
    numD8Answer [.ptr p, .ptr v] mem next =
      some { ret := .int 32 1, mem := writeBytes mem v (natToBytes w 4), next := next } := by
  simp only [numD8Answer, hread, hval]

/-- The reader's refusal answer, at the exact read. -/
theorem numD8Answer_refuse {p v : Nat} {bs : List UInt8} {mem : Mem} {next : Nat}
    (hread : readBytes mem p 8 = some bs) (hval : d8Value bs = none) :
    numD8Answer [.ptr p, .ptr v] mem next =
      some { ret := .int 32 0, mem := mem, next := next } := by
  simp only [numD8Answer, hread, hval]

/-! ### `stk_mul_u64`: a `StkBn` multiplied in place

`stage2.c`'s `StkBn` is `uint64_t w[96]` followed by `int n`, so the count's
cell is at offset `96 * 8 = 768`.  `stk_mul_add(a, m, 0)` folds the carry over
the live limbs and then extends while a carry remains, which is `stkMulWords`.
The model reads the count and the limbs, multiplies, and writes the new count
and limbs back. -/

/-- The limb count's offset in `StkBn`: `96` limbs precede the `int`. -/
def stkCountOffset : Nat := 768

/-- `k` limbs from `a`, little-endian, as their `uint64` values. -/
def stkLimbs (mem : Mem) (a : Nat) : Nat → Option (List Nat)
  | 0 => some []
  | k + 1 =>
      match stkLimbs mem a k, readBytes mem (a + 8 * k) 8 with
      | some ws, some bs => some (ws ++ [bytesToNat bs])
      | _, _ => none

/-- The limb count the struct holds, as the `int`'s four bytes read. -/
def stkCount (mem : Mem) (a : Nat) : Option Nat :=
  (readBytes mem (a + stkCountOffset) 4).map bytesToNat

/-- `stk_mul_add`'s fold: each limb times the multiplier plus the carry, the low
`64` bits kept and the carry carried.  The second component is the final carry. -/
def stkMulFold : List Nat → Nat → Nat → List Nat × Nat
  | [], _, c => ([], c)
  | w :: ws, m, c =>
      let t := w * m + c
      let rest := stkMulFold ws m (t / 2 ^ 64)
      (t % 2 ^ 64 :: rest.1, rest.2)

/-- The carry's limbs, low first, while it is nonzero. -/
def stkCarryLimbs : Nat → List Nat
  | 0 => []
  | c + 1 => (c + 1) % 2 ^ 64 :: stkCarryLimbs ((c + 1) / 2 ^ 64)

/-- `a <- a * m`, the limbs the C's `stk_mul_add(a, m, 0)` leaves. -/
def stkMulWords (ws : List Nat) (m : Nat) : List Nat :=
  let r := stkMulFold ws m 0
  r.1 ++ stkCarryLimbs r.2

/-- The limbs written back at `a`, eight bytes each. -/
def stkWriteLimbs (mem : Mem) (a : Nat) : List Nat → Mem
  | [] => mem
  | w :: ws => stkWriteLimbs (writeBytes mem a (natToBytes (w % 2 ^ 64) 8)) (a + 8) ws

/-- The multiply's answer: the count is read, the limbs are multiplied, and the
new count and limbs are written.  The `ret` is the caller's discarded value. -/
def numStkMulAnswer (args : List Value) (mem : Mem) (next : Nat) : Option CallOutcome :=
  match args with
  | [.ptr a, .int 64 m] =>
      match stkCount mem a with
      | some n =>
          match stkLimbs mem a n with
          | some ws =>
              let ws' := stkMulWords ws m.toNat
              some { ret := .int 1 0,
                     mem := writeBytes (stkWriteLimbs mem a ws') (a + stkCountOffset)
                       (natToBytes ws'.length 4),
                     next := next }
          | none => some { ret := .int 1 0, mem := mem, next := next }
      | none => some { ret := .int 1 0, mem := mem, next := next }
  | _ => none

/-! ### `num_el_el1`: the deferred Eisel-Lemire kernel

The kernel's table row: `hi` and `lo` of the normalised significand and its
binary exponent.  `epow_table.h` supplies the 91 rows; the model takes the
lookup as a parameter, so the table is the staging's data rather than a literal
the proof would be asserting. -/

/-- One `EPOW` row: `10 ^ q = (hi * 2 ^ 64 + lo) * 2 ^ e`. -/
structure EPow where
  hi : Nat
  lo : Nat
  e : Int

/-- `EL_HALF(ub)`: half of the guard slice. -/
def elHalf (ub : Nat) : Nat := 2 ^ (9 + ub)

/-- `el_pack`: the 53-bit significand, the round-up bit and the carry decide the
binary64 pattern, or `none` when the exponent leaves the normal range. -/
def elPack (m up ub : Nat) (t : EPow) (lz : Nat) : Option Nat :=
  let mm := m + up
  let ov := mm / 2 ^ 53
  let sh := 10 + ub + ov
  let eu : Int := 180 + (sh : Int) + t.e - (lz : Int)
  if eu > 1023 ∨ eu < -1022 then none
  else some ((eu + 1023).toNat * 2 ^ 52 + mm % 2 ^ 52)

/-- `el_exact`: both halves of the product, the exact rounding decision, and the
`q < 0` refusals the C's `undec` test makes. -/
def elExact (W lz : Nat) (t : EPow) (q : Int) : Option Nat :=
  let A := W * t.hi
  let B := W * t.lo
  let Alo := A % 2 ^ 64
  let Ahi := A / 2 ^ 64
  let L := B % 2 ^ 64
  let c := B / 2 ^ 64
  let Rlo := Alo + c
  let Rhi := Ahi + (if Rlo < Alo then 1 else 0)
  let ub := Rhi / 2 ^ 63
  let sh := 10 + ub
  let m := Rhi / 2 ^ sh
  let hp := Rhi % 2 ^ (10 + ub)
  let hh := elHalf ub
  let tie := hp = hh
  let close := hp = hh - 1
  let undec := (tie ∧ Rlo ||| L = 0) ∨ (close ∧ Rlo = 2 ^ 64 - 1)
  if undec ∧ q < 0 then none
  else
    let tieUp : Nat := if tie ∧ (Rlo ||| L ≠ 0 ∨ m % 2 = 1) then 1 else 0
    let up : Nat := (if hp > hh then 1 else 0) + tieUp
    elPack m up ub t lz

/-- The kernel: the range gate, the zero mantissa, then the two-multiply guard
window or the single-multiply fast path.  `none` is the C's `return 0` (the
caller's slow path); `some bits` is the accepted binary64. -/
def numElEl1 (epow : Int → Option EPow) (w : Nat) (q : Int) : Option Nat :=
  if q < -45 ∨ 45 < q then none
  else if w = 0 then some 0
  else
    match epow q with
    | none => none
    | some t =>
        let lz := 64 - Nat.size w
        let W := w * 2 ^ lz
        let Ahi := (W * t.hi) / 2 ^ 64
        let ub := Ahi / 2 ^ 63
        let hp := Ahi % 2 ^ (10 + ub)
        let hh := elHalf ub
        if hh ≤ hp + 2 ∧ hp ≤ hh then elExact W lz t q
        else elPack (Ahi / 2 ^ (10 + ub)) (if hp > hh then 1 else 0) ub t lz

/-- The kernel's answer: accepted writes the eight bytes and returns one;
declined writes nothing and returns zero. -/
def numElAnswer (epow : Int → Option EPow) (args : List Value) (mem : Mem)
    (next : Nat) : Option CallOutcome :=
  match args with
  | [.int 64 w, .int 64 q, .ptr out] =>
      match numElEl1 epow w.toNat q.toInt with
      | some bits =>
          some { ret := .int 32 1, mem := writeBytes mem out (natToBytes bits 8),
                 next := next }
      | none => some { ret := .int 32 0, mem := mem, next := next }
  | _ => none

/-! ### The environment

`numFastCalls` answers the three symbols and delegates everything else, so
composing it with `s2HelperCalls` keeps the lifetime markers, `memset` and the
trap. -/

/-- The conversion's three callees answered; every other symbol to `base`. -/
def numFastCalls (base : Calls) (epow : Int → Option EPow) : Calls :=
  fun callee args mem next =>
    if callee = "num_d8_el1" then numD8Answer args mem next
    else if callee = "num_el_el1" then numElAnswer epow args mem next
    else if callee = "stk_mul_u64" then numStkMulAnswer args mem next
    else base callee args mem next

/-- The walk's environment with the conversion's three callees answered. -/
def stage2NumFastCalls (epow : Int → Option EPow) : Calls :=
  numFastCalls s2HelperCalls epow

/-- The eight-digit reader is answered. -/
theorem stage2NumFastCalls_num_d8 (epow : Int → Option EPow) (args : List Value)
    (mem : Mem) (next : Nat) :
    stage2NumFastCalls epow "num_d8_el1" args mem next = numD8Answer args mem next := by
  simp only [stage2NumFastCalls, numFastCalls, if_true]

/-- The kernel is answered. -/
theorem stage2NumFastCalls_num_el (epow : Int → Option EPow) (args : List Value)
    (mem : Mem) (next : Nat) :
    stage2NumFastCalls epow "num_el_el1" args mem next =
      numElAnswer epow args mem next := by
  simp only [stage2NumFastCalls, numFastCalls,
    if_neg (by decide : ¬ ("num_el_el1" = "num_d8_el1")), if_true]

/-- The big multiply is answered. -/
theorem stage2NumFastCalls_stk_mul (epow : Int → Option EPow) (args : List Value)
    (mem : Mem) (next : Nat) :
    stage2NumFastCalls epow "stk_mul_u64" args mem next =
      numStkMulAnswer args mem next := by
  simp only [stage2NumFastCalls, numFastCalls,
    if_neg (by decide : ¬ ("stk_mul_u64" = "num_d8_el1")),
    if_neg (by decide : ¬ ("stk_mul_u64" = "num_el_el1")), if_true]

/-- The lifetime marker keeps the walk's answer. -/
theorem stage2NumFastCalls_lifetime (epow : Int → Option EPow) (args : List Value)
    (mem : Mem) (next : Nat) :
    stage2NumFastCalls epow "llvm.lifetime.start.p0" args mem next =
      some { ret := .int 1 0, mem := mem, next := next } := by
  simp only [stage2NumFastCalls, numFastCalls,
    if_neg (by decide : ¬ ("llvm.lifetime.start.p0" = "num_d8_el1")),
    if_neg (by decide : ¬ ("llvm.lifetime.start.p0" = "num_el_el1")),
    if_neg (by decide : ¬ ("llvm.lifetime.start.p0" = "stk_mul_u64")),
    s2HelperCalls_lifetime_start]

/-! ### A `call` the environment answers

The `some` counterpart of the arm's `denoteCode_call_none`: the chain continues
at the callee's outcome, binding its return value under the destination. -/

/-- A `call` whose answer the environment has continues the chain at the
callee's return, memory and allocator state. -/
theorem denoteCode_call_some (calls : Calls) (env : Env) (s : State) (d : String)
    (ty : Ty) (callee : String) (args : List (Ty × Operand)) (vs : List Value)
    (r : CallOutcome)
    (hargs : evalOperands (stateAt env s) args = some vs)
    (hsome : calls callee vs s.mem s.next = some r) (is : List Instr) :
    denoteCode calls (.call d ty callee args :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt ((d, r.ret) :: env) { s with mem := r.mem, next := r.next }) := by
  rw [denoteCode_cons_of _ _ _ _ _ ?_]
  simp only [evalInstr]
  rw [hargs]
  dsimp only [stateAt]
  rw [hsome]

/-! ### The two tables, staged

`NumFastTables` fixes the two addresses through the environment and the rows
through the memory.  The staging below is concrete: `NUMF_EL1_P10` at `10000`
with twenty `10 ^ i` rows, `NUMF_EL1_POW10` at `20000` with twenty-three, and
the two symbol bindings.  `bytesAt` is the memory a byte list occupies from an
address, so `readBytes` at a row's address is the row. -/

/-- The memory a byte list occupies from `a`, one cell per byte. -/
def bytesAt : Nat → List UInt8 → Mem
  | _, [] => []
  | a, b :: bs => (a, b) :: bytesAt (a + 1) bs

/-- The table's first address. -/
def p10Base : Nat := 10000

/-- The second table's address. -/
def pdBase : Nat := 20000

/-- `NUMF_EL1_P10`'s rows: `10 ^ i` little-endian, eight bytes each. -/
def p10Rows : List UInt8 :=
  (List.range 20).flatMap (fun i => natToBytes ((10 : Nat) ^ i) 8)

/-- `NUMF_EL1_POW10`'s rows: the binary64 `10 ^ i`, eight bytes each. -/
def pdRows : List UInt8 :=
  (List.range 23).flatMap (fun i => natToBytes (uitofpBits ((10 : Nat) ^ i)).toNat 8)

/-- The two tables, as the staging's memory. -/
def numFastTableMem : Mem := bytesAt p10Base p10Rows ++ bytesAt pdBase pdRows

/-- The staging's environment: the two symbols' addresses. -/
def numFastTableEnv : Env :=
  [("@NUMF_EL1_P10", .ptr p10Base), ("@NUMF_EL1_POW10", .ptr pdBase)]

/-- `NUMF_EL1_P10`'s twenty rows read back at their addresses.  The finitary
form is the `decide`; the row lemma reads it at each index. -/
theorem p10_row_all :
    ((List.range 20).all (fun i => decide
      (readBytes numFastTableMem (p10Base + 8 * i) 8 =
        some (natToBytes ((10 : Nat) ^ i) 8)))) = true := by
  decide

/-- Each `P10` row. -/
theorem p10_row (i : Nat) (hi : i < 20) :
    readBytes numFastTableMem (p10Base + 8 * i) 8 =
      some (natToBytes ((10 : Nat) ^ i) 8) := by
  have h := p10_row_all
  rw [List.all_eq_true] at h
  exact of_decide_eq_true (h i (List.mem_range.mpr hi))

/-- `NUMF_EL1_POW10`'s twenty-three rows read back at their addresses. -/
theorem pd_row_all :
    ((List.range 23).all (fun i => decide
      (readBytes numFastTableMem (pdBase + 8 * i) 8 =
        some (natToBytes (uitofpBits ((10 : Nat) ^ i)).toNat 8)))) = true := by
  decide

/-- Each `POW10` row. -/
theorem pd_row (i : Nat) (hi : i < 23) :
    readBytes numFastTableMem (pdBase + 8 * i) 8 =
      some (natToBytes (uitofpBits ((10 : Nat) ^ i)).toNat 8) := by
  have h := pd_row_all
  rw [List.all_eq_true] at h
  exact of_decide_eq_true (h i (List.mem_range.mpr hi))

/-- The two symbol bindings. -/
theorem numFastTableEnv_p10 :
    lookupName numFastTableEnv "@NUMF_EL1_P10" = some (.ptr p10Base) := by decide

theorem numFastTableEnv_pd :
    lookupName numFastTableEnv "@NUMF_EL1_POW10" = some (.ptr pdBase) := by decide

/-- **The staging satisfies `NumFastTables`.**  The two addresses are the
staging's, and the rows are the emitted initialisers'. -/
theorem numFastTables_holds : NumFastTables numFastTableEnv numFastTableMem := by
  refine ⟨p10Base, pdBase, numFastTableEnv_p10, numFastTableEnv_pd, ?_, ?_⟩
  · intro i hi
    exact p10_row i hi
  · intro i hi
    exact pd_row i hi

/-! ### An `icmp` against an immediate, at any width -/

/-- `%d = icmp eq iN %a, <c>`: the comparison's bit, at the width the operands
carry.  `evalInstr_icmp` is already width-generic; this is its reading at a
register and an immediate. -/
theorem step_icmp_eq_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w} (ha : lookupName env a = some (.int w x)) :
    evalInstr calls (stateAt env s) (.icmp d .eq w (.reg a) (.imm (.int w c))) =
      some (stateAt ((d, .int 1 (evalICmp .eq x c)) :: env) s) := by
  simpa only [stateAt, State.bind] using
    LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_icmp
      (calls := calls) (s := stateAt env s)
      (ha := evalOperand_reg_of env s a (.int w x) ha)
      (hb := evalOperand_lit_of (stateAt env s) w c)

/-- The index's own chain step, with the table symbol as the base: a
`getelementptr i64` adds eight bytes per step.  The body reads `@NUMF_EL1_P10`
as a `global` operand, which `evalOperand` resolves under the symbol's spelling
exactly as a register is; the address is the staging's. -/
theorem denoteCode_gep_i64_global (calls : Calls) (env : Env) (s : State)
    (d base off : String) {a : Nat} {idx : BitVec 64}
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 idx))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63) (is : List Instr) :
    denoteCode calls (.gep d (.int 64) (.global base) (.reg off) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt ((d, .ptr (a + (idx.signExtend 64).toNat * (Ty.int 64).sizeBytes)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ ?_]
  simp only [evalInstr, evalOperand, stateAt, hb, ho, hpos, ite_true, State.bind]

/-- A `condbr` at a state that holds its condition is a jump: one of the two
targets, whichever the bit selects. -/
theorem execTerm_condbr_reg_jump (s : State) (c t f : String) {bit : BitVec 1}
    (hc : lookupName s.env c = some (.int 1 bit)) :
    ∃ t' : State, execTerm s (.condbr (.reg c) t f) = .jump t' := by
  simp only [execTerm, evalOperand, hc]
  rcases bitVec1_eq_zero_or_one bit with h | h
  · exact ⟨{ s with pc := f, pre := some s.pc }, by simp [h]⟩
  · exact ⟨{ s with pc := t, pre := some s.pc }, by simp [h]⟩

/-! ### The three sites, answered

The `some` counterparts of the arm's `_none` theorems, at the same pinned
instruction lists.  Because the callees' answers are `some` at every argument
shape they accept, the block's chain is defined and its control step is a jump.
Each proof reads the callee's outcome explicitly — accepted or declined — so the
bit the block computes is the kernel's or the reader's own return test. -/

/-- `if.end268`'s run: the marker, the kernel, the decision's bit. -/
theorem numFast_ifEnd268_denote_some (epow : Int → Option EPow) {env : Env}
    {s : State} {a b : BitVec 64} {q : Nat}
    (ha : lookupName env "%add244" = some (.int 64 a))
    (hb : lookupName env "%sub231" = some (.int 64 b))
    (hd : lookupName env "%d269" = some (.ptr q)) :
    ∃ (r : CallOutcome) (x : BitVec 32), r.ret = .int 32 x ∧
      denoteCode (stage2NumFastCalls epow) numFastIfEnd268Instrs (stateAt env s) =
        some (stateAt
          (("%tobool271.not", .int 1 (evalICmp .eq x 0)) ::
           ("%call270", .int 32 x) :: env)
          { s with mem := r.mem, next := r.next }) := by
  have hargs : evalOperands (stateAt env { s with mem := s.mem, next := s.next })
      [((Ty.int 64), (Operand.reg "%add244")),
       ((Ty.int 64), (Operand.reg "%sub231")),
       (Ty.ptr, (Operand.reg "%d269"))]
      = some [.int 64 a, .int 64 b, .ptr q] := by
    simp only [evalOperands, evalOperand, stateAt, ha, hb, hd]
  have hstep : ∀ (r : CallOutcome) (x : BitVec 32), r.ret = .int 32 x →
      stage2NumFastCalls epow "num_el_el1"
        [.int 64 a, .int 64 b, .ptr q] s.mem s.next = some r →
      denoteCode (stage2NumFastCalls epow) numFastIfEnd268Instrs (stateAt env s) =
        some (stateAt
          (("%tobool271.not", .int 1 (evalICmp .eq x 0)) ::
           ("%call270", .int 32 x) :: env)
          { s with mem := r.mem, next := r.next }) := by
    intro r x hx hsome
    unfold numFastIfEnd268Instrs
    rw [denoteCode_callVoid_some _ _ _ _ _ _ _
      (evalOperands_lifetimeMark (s := s) hd) (stage2NumFastCalls_lifetime _ _ _ _) _]
    rw [denoteCode_call_some _ _ _ _ _ _ _ _ r hargs hsome _]
    simp only [hx]
    rw [denoteCode_cons_of _ _ _ _ _ (step_icmp_eq_imm_w (stage2NumFastCalls epow)
      (("%call270", .int 32 x) :: env) { s with mem := r.mem, next := r.next }
      "%tobool271.not" "%call270" 32
      (lookupName_cons_self "%call270" (.int 32 x) env))]
    rw [denoteCode_nil]
    rfl
  cases hdec : numElEl1 epow a.toNat b.toInt with
  | none =>
      refine ⟨{ ret := .int 32 0, mem := s.mem, next := s.next }, 0, rfl, ?_⟩
      exact hstep _ 0 rfl (by rw [stage2NumFastCalls_num_el]; simp only [numElAnswer, hdec])
  | some bits =>
      refine ⟨{ ret := .int 32 1, mem := writeBytes s.mem q (natToBytes bits 8),
                next := s.next }, 1, rfl, ?_⟩
      exact hstep _ 1 rfl (by rw [stage2NumFastCalls_num_el]; simp only [numElAnswer, hdec])

/-- The tier-2 site's control step, at the answered environment: a jump. -/
theorem numFast_step_ifEnd268_jump (epow : Int → Option EPow) {env : Env} {s : State}
    {a b : BitVec 64} {q : Nat} (hpc : s.pc = "if.end268")
    (ha : lookupName env "%add244" = some (.int 64 a))
    (hb : lookupName env "%sub231" = some (.int 64 b))
    (hd : lookupName env "%d269" = some (.ptr q)) :
    ∃ t : State, step (stage2NumFastCalls epow) numFastBody (stateAt env s) = .jump t := by
  obtain ⟨r, x, hx, hcode⟩ := numFast_ifEnd268_denote_some (s := s) epow ha hb hd
  have hfind : numFastBody.findBlock (stateAt env s).pc =
      some ⟨"if.end268", numFastIfEnd268Instrs,
        Term.condbr (Operand.reg "%tobool271.not") "cleanup282.thread462" "cleanup282"⟩ := by
    rw [show (stateAt env s).pc = "if.end268" from hpc]
    exact numFast_findBlock_if_end268_named
  have hbit : lookupName
      (stateAt (("%tobool271.not", .int 1 (evalICmp .eq x 0)) ::
        ("%call270", .int 32 x) :: env) { s with mem := r.mem, next := r.next }).env
      "%tobool271.not" = some (.int 1 (evalICmp .eq x 0)) := by
    simp only [stateAt, lookupName_cons_self]
  obtain ⟨t, ht⟩ := execTerm_condbr_reg_jump
    (stateAt (("%tobool271.not", .int 1 (evalICmp .eq x 0)) ::
      ("%call270", .int 32 x) :: env) { s with mem := r.mem, next := r.next })
    "%tobool271.not" "cleanup282.thread462" "cleanup282" hbit
  exact ⟨t, by simp only [step, hfind, hcode, ht]⟩

/-- `while.body.preheader`'s run: the marker, the address, the reader, the
decision's bit. -/
theorem numFast_whileBodyPreheader_denote_some (epow : Int → Option EPow)
    {env : Env} {s : State} {a v8a : Nat} {idx : BitVec 64}
    (hp : lookupName env "%p" = some (.ptr a))
    (ho : lookupName env "%inc26" = some (.int 64 idx))
    (hv8 : lookupName env "%v8" = some (.ptr v8a))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63) :
    ∃ (r : CallOutcome) (x : BitVec 32), r.ret = .int 32 x ∧
      denoteCode (stage2NumFastCalls epow) numFastWhileBodyPreheaderInstrs
        (stateAt env s) =
        some (stateAt
          (("%tobool.not932", .int 1 (evalICmp .eq x 0)) ::
           ("%call931", .int 32 x) ::
           ("%add.ptr930", .ptr (a + (idx.signExtend 64).toNat)) :: env)
          { s with mem := r.mem, next := r.next }) := by
  have hstep : ∀ (r : CallOutcome) (x : BitVec 32), r.ret = .int 32 x →
      stage2NumFastCalls epow "num_d8_el1"
        [.ptr (a + (idx.signExtend 64).toNat), .ptr v8a] s.mem s.next = some r →
      denoteCode (stage2NumFastCalls epow) numFastWhileBodyPreheaderInstrs
        (stateAt env s) =
        some (stateAt
          (("%tobool.not932", .int 1 (evalICmp .eq x 0)) ::
           ("%call931", .int 32 x) ::
           ("%add.ptr930", .ptr (a + (idx.signExtend 64).toNat)) :: env)
          { s with mem := r.mem, next := r.next }) := by
    intro r x hx hsome
    unfold numFastWhileBodyPreheaderInstrs
    rw [denoteCode_callVoid_some _ _ _ "llvm.lifetime.start.p0"
      [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000004#64))),
       (Ty.ptr, (Operand.reg "%v8"))]
      [.int 64 0x0000000000000004#64, .ptr v8a]
      { ret := .int 1 0, mem := s.mem, next := s.next }
      (evalOperands_lifetimeMark (s := s) hv8) (stage2NumFastCalls_lifetime _ _ _ _) _]
    rw [denoteCode_gep8_reg _ _ _ "%add.ptr930" "%p" "%inc26" hp ho hpos _]
    rw [denoteCode_call_some _ _ _ _ _ _ _ _ r
      (by
        have h1 := lookupName_cons_self "%add.ptr930"
          (.ptr (a + (idx.signExtend 64).toNat)) env
        have h2 := lookupName_cons_tail (k := "%add.ptr930")
          (v := .ptr (a + (idx.signExtend 64).toNat)) (by decide) hv8
        simp only [evalOperands, evalOperand, stateAt, h1, h2])
      hsome _]
    simp only [hx]
    rw [denoteCode_cons_of _ _ _ _ _ (step_icmp_eq_imm_w (stage2NumFastCalls epow)
      (("%call931", .int 32 x) ::
       ("%add.ptr930", .ptr (a + (idx.signExtend 64).toNat)) :: env)
      { s with mem := r.mem, next := r.next }
      "%tobool.not932" "%call931" 32
      (lookupName_cons_self "%call931" (.int 32 x)
        (("%add.ptr930", .ptr (a + (idx.signExtend 64).toNat)) :: env)))]
    rw [denoteCode_nil]
    rfl
  -- the reader's two outcomes
  cases hread : readBytes s.mem (a + (idx.signExtend 64).toNat) 8 with
  | none =>
      refine ⟨{ ret := .int 32 0, mem := s.mem, next := s.next }, 0, rfl, ?_⟩
      exact hstep _ 0 rfl (by rw [stage2NumFastCalls_num_d8]; simp only [numD8Answer, hread])
  | some bs =>
      cases hval : d8Value bs with
      | none =>
          refine ⟨{ ret := .int 32 0, mem := s.mem, next := s.next }, 0, rfl, ?_⟩
          exact hstep _ 0 rfl (by rw [stage2NumFastCalls_num_d8]; simp only [numD8Answer, hread, hval])
      | some w =>
          refine ⟨{ ret := .int 32 1, mem := writeBytes s.mem v8a (natToBytes w 4),
                    next := s.next }, 1, rfl, ?_⟩
          exact hstep _ 1 rfl (by rw [stage2NumFastCalls_num_d8]; simp only [numD8Answer, hread, hval])

/-- The fast path's reader's control step, at the answered environment: a jump. -/
theorem numFast_step_whileBodyPreheader_jump (epow : Int → Option EPow)
    {env : Env} {s : State} {a v8a : Nat} {idx : BitVec 64}
    (hpc : s.pc = "while.body.preheader")
    (hp : lookupName env "%p" = some (.ptr a))
    (ho : lookupName env "%inc26" = some (.int 64 idx))
    (hv8 : lookupName env "%v8" = some (.ptr v8a))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63) :
    ∃ t : State, step (stage2NumFastCalls epow) numFastBody (stateAt env s) = .jump t := by
  obtain ⟨r, x, hx, hcode⟩ := numFast_whileBodyPreheader_denote_some (s := s) epow hp ho hv8 hpos
  have hfind : numFastBody.findBlock (stateAt env s).pc =
      some ⟨"while.body.preheader", numFastWhileBodyPreheaderInstrs,
        Term.condbr (Operand.reg "%tobool.not932") "cleanup.thread" "cleanup"⟩ := by
    rw [show (stateAt env s).pc = "while.body.preheader" from hpc]
    exact numFast_findBlock_while_body_preheader_named
  have hbit : lookupName
      (stateAt (("%tobool.not932", .int 1 (evalICmp .eq x 0)) ::
        ("%call931", .int 32 x) ::
        ("%add.ptr930", .ptr (a + (idx.signExtend 64).toNat)) :: env)
        { s with mem := r.mem, next := r.next }).env
      "%tobool.not932" = some (.int 1 (evalICmp .eq x 0)) := by
    simp only [stateAt, lookupName_cons_self]
  obtain ⟨t, ht⟩ := execTerm_condbr_reg_jump
    (stateAt (("%tobool.not932", .int 1 (evalICmp .eq x 0)) ::
      ("%call931", .int 32 x) ::
      ("%add.ptr930", .ptr (a + (idx.signExtend 64).toNat)) :: env)
      { s with mem := r.mem, next := r.next })
    "%tobool.not932" "cleanup.thread" "cleanup" hbit
  exact ⟨t, by simp only [step, hfind, hcode, ht]⟩

/-- `if.then178.i.i`'s run: the `phi`, the table address, the load, the big
multiply. -/
theorem numFast_ifThen178_denote_some (epow : Int → Option EPow) {env : Env}
    {s : State} {p10 pow : Nat} {k v : BitVec 64}
    (hpre : s.pre = some "while.end176.i.i")
    (hk : lookupName env "%sub175.i.i" = some (.int 64 k))
    (hg : lookupName env "@NUMF_EL1_P10" = some (.ptr p10))
    (hpos : (k.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (p10 + (k.signExtend 64).toNat * (Ty.int 64).sizeBytes) 8
      = some (natToBytes v.toNat 8))
    (hpow : lookupName env "%pow.i.i" = some (.ptr pow)) :
    ∃ s' : State,
      denoteCode (stage2NumFastCalls epow) numFastIfThen178Instrs
        (stateAt env s) = some s' := by
  have hbase : lookupName (("%k168.0.lcssa829.i.i", .int 64 k) :: env) "@NUMF_EL1_P10"
      = some (.ptr p10) :=
    lookupName_cons_tail (k := "%k168.0.lcssa829.i.i") (v := .int 64 k) (by decide) hg
  have hidx : lookupName (("%k168.0.lcssa829.i.i", .int 64 k) :: env) "%k168.0.lcssa829.i.i"
      = some (.int 64 k) :=
    lookupName_cons_self "%k168.0.lcssa829.i.i" (.int 64 k) env
  have hargs : evalOperands
      (stateAt (("%107", .int 64 v) ::
        ("%arrayidx180.i.i", .ptr (p10 + (k.signExtend 64).toNat * (Ty.int 64).sizeBytes)) ::
        ("%k168.0.lcssa829.i.i", .int 64 k) :: env) s)
      [(Ty.ptr, (Operand.reg "%pow.i.i")), ((Ty.int 64), (Operand.reg "%107"))]
      = some [.ptr pow, .int 64 v] := by
    have h107 : lookupName
        (("%107", .int 64 v) ::
          ("%arrayidx180.i.i", .ptr (p10 + (k.signExtend 64).toNat * (Ty.int 64).sizeBytes)) ::
          ("%k168.0.lcssa829.i.i", .int 64 k) :: env) "%107" = some (.int 64 v) :=
      lookupName_cons_self "%107" (.int 64 v)
        (("%arrayidx180.i.i", .ptr (p10 + (k.signExtend 64).toNat * (Ty.int 64).sizeBytes)) ::
          ("%k168.0.lcssa829.i.i", .int 64 k) :: env)
    have hpow' : lookupName
        (("%107", .int 64 v) ::
          ("%arrayidx180.i.i", .ptr (p10 + (k.signExtend 64).toNat * (Ty.int 64).sizeBytes)) ::
          ("%k168.0.lcssa829.i.i", .int 64 k) :: env) "%pow.i.i" = some (.ptr pow) :=
      lookupName_cons_tail (k := "%107") (v := .int 64 v) (by decide)
        (lookupName_cons_tail (k := "%arrayidx180.i.i")
          (v := .ptr (p10 + (k.signExtend 64).toNat * (Ty.int 64).sizeBytes)) (by decide)
          (lookupName_cons_tail (k := "%k168.0.lcssa829.i.i") (v := .int 64 k) (by decide)
            hpow))
    simp only [evalOperands, evalOperand, stateAt, h107, hpow']
  have hstep : ∀ (r : CallOutcome),
      stage2NumFastCalls epow "stk_mul_u64" [.ptr pow, .int 64 v] s.mem s.next = some r →
      ∃ s', denoteCode (stage2NumFastCalls epow) numFastIfThen178Instrs
        (stateAt env s) = some s' := by
    intro r hsome
    unfold numFastIfThen178Instrs
    rw [denoteCode_phi _ _ _ "%k168.0.lcssa829.i.i" (Ty.int 64)
      _ (p := "while.end176.i.i") (op := Operand.reg "%sub175.i.i") (v := .int 64 k)
      hpre numFast_ifThen178_phiIncoming
      (by simp only [evalOperand, stateAt, hk]) _ (by simp only [startsWithPhi])]
    rw [denoteCode_gep_i64_global _ _ _ "%arrayidx180.i.i" "@NUMF_EL1_P10" "%k168.0.lcssa829.i.i"
      hbase hidx hpos _]
    rw [denoteCode_load64 _ _ _ "%107" "%arrayidx180.i.i"
      (lookupName_cons_self "%arrayidx180.i.i"
        (.ptr (p10 + (k.signExtend 64).toNat * (Ty.int 64).sizeBytes))
        (("%k168.0.lcssa829.i.i", .int 64 k) :: env))
      (by simpa only [stateAt] using hread) _]
    rw [denoteCode_callVoid_some _ _ _ "stk_mul_u64"
      [(Ty.ptr, (Operand.reg "%pow.i.i")), ((Ty.int 64), (Operand.reg "%107"))]
      [.ptr pow, .int 64 v] r hargs hsome _]
    exact ⟨_, by rw [denoteCode_nil]⟩
  -- the multiply's answer at the three read shapes
  cases hc : stkCount s.mem pow with
  | none =>
      have hr : stage2NumFastCalls epow "stk_mul_u64" [.ptr pow, .int 64 v] s.mem s.next
          = some { ret := .int 1 0, mem := s.mem, next := s.next } := by
        rw [stage2NumFastCalls_stk_mul]
        simp only [numStkMulAnswer, hc]
      exact hstep _ hr
  | some n =>
      cases hl : stkLimbs s.mem pow n with
      | none =>
          have hr : stage2NumFastCalls epow "stk_mul_u64" [.ptr pow, .int 64 v] s.mem s.next
              = some { ret := .int 1 0, mem := s.mem, next := s.next } := by
            rw [stage2NumFastCalls_stk_mul]
            simp only [numStkMulAnswer, hc, hl]
          exact hstep _ hr
      | some ws =>
          have hr : stage2NumFastCalls epow "stk_mul_u64" [.ptr pow, .int 64 v] s.mem s.next
              = some { ret := .int 1 0,
                       mem := writeBytes (stkWriteLimbs s.mem pow (stkMulWords ws v.toNat))
                         (pow + stkCountOffset) (natToBytes (stkMulWords ws v.toNat).length 4),
                       next := s.next } := by
            rw [stage2NumFastCalls_stk_mul]
            simp only [numStkMulAnswer, hc, hl]
          exact hstep _ hr

/-- The fallback's big multiply's control step, at the answered environment: the
block continues to `if.end198.i.i`. -/
theorem numFast_step_ifThen178_jump (epow : Int → Option EPow) {env : Env} {s : State}
    {p10 pow : Nat} {k v : BitVec 64}
    (hpc : s.pc = "if.then178.i.i")
    (hpre : s.pre = some "while.end176.i.i")
    (hk : lookupName env "%sub175.i.i" = some (.int 64 k))
    (hg : lookupName env "@NUMF_EL1_P10" = some (.ptr p10))
    (hpos : (k.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (p10 + (k.signExtend 64).toNat * (Ty.int 64).sizeBytes) 8
      = some (natToBytes v.toNat 8))
    (hpow : lookupName env "%pow.i.i" = some (.ptr pow)) :
    ∃ t : State, step (stage2NumFastCalls epow) numFastBody (stateAt env s) = .jump t := by
  obtain ⟨s', hcode⟩ := numFast_ifThen178_denote_some (s := s) epow hpre hk hg hpos hread hpow
  have hfind : numFastBody.findBlock (stateAt env s).pc =
      some ⟨"if.then178.i.i", numFastIfThen178Instrs, Term.br "if.end198.i.i"⟩ := by
    rw [show (stateAt env s).pc = "if.then178.i.i" from hpc]
    exact numFast_findBlock_if_then178_named
  exact ⟨{ s' with pc := "if.end198.i.i", pre := some s'.pc },
    by simp only [step, hfind, hcode, execTerm]⟩

/-! ### Axiom footprints

The staging and the three sites, pinned with `#guard_msgs` so the build checks
the footprint.  `#print axioms` prints `sorryAx` for a `sorry`-backed
declaration, which is the control the other modules in this tree record. -/

/-- info: 'LeanLLVM.Refinement.numFastTables_holds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numFastTables_holds

/-- info: 'LeanLLVM.Refinement.numD8Answer_read' depends on axioms: [propext] -/
#guard_msgs in
#print axioms numD8Answer_read

/-- info: 'LeanLLVM.Refinement.numFast_ifEnd268_denote_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numFast_ifEnd268_denote_some

/-- info: 'LeanLLVM.Refinement.numFast_step_ifEnd268_jump' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numFast_step_ifEnd268_jump

/-- info: 'LeanLLVM.Refinement.numFast_whileBodyPreheader_denote_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numFast_whileBodyPreheader_denote_some

/-- info: 'LeanLLVM.Refinement.numFast_ifThen178_denote_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms numFast_ifThen178_denote_some

end LeanLLVM.Refinement
