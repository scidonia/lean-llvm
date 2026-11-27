/-
The producer's arm of the count tie: the two limb counts, from the calls.

`JsonStage2NumFastFallback.fbStkCounts` is where the comparator's copy fit comes
from: the epilogue names it, `numCmp_count_le_of_stkCounts` reads the count the
copy is given, and `numCmpCopyLen_le` turns `96` limbs into `776` bytes.  The
producer's half — the blocks that fill `%v` — is the converter's ingest and its
power nests, which `JsonStage2NumFastToDouble` says it does not state.  This
module supplies the half that needs no semantics of the number stored: a count
is bounded by the *calls the emitting code makes*, because one `stk_mul_add`
appends at most one limb (`stkMulAdd_length_le`).  The calls are the C's own
loops (`kernel/json/stage2.c`, `to_double`):

* the digit ingest — `for (j = 0; j < R; j++) { …; if (++cn == 19)
  stk_mul_add(&m, NUMF_EL1_P10[19], chunk); … }` and `if (cn)
  stk_mul_add(&m, NUMF_EL1_P10[cn], chunk)` — makes `R / 19` calls plus one for
  the residual chunk, and `stk_zero` starts the count at zero, so
  `m.n <= ceil(R / 19)`; the digit guard `R < 768` caps `R` at `768` and the
  count at `41`;
* the sticky power nest — `while (k >= 27) { stk_mul_u64(&pow, 5^27); k -= 27; }`
  then `if (k) stk_mul_u64(&pow, STK_P5[k])` — starts from `stk_from_u64(&pow, 1)`,
  one limb, so `pow.n <= 1 + ceil(k / 27) <= 42` at `k = -S <= 1091`;
* the exact power nest — the same loop with `10^19` and `NUMF_EL1_P10[k]` — gives
  `pow.n <= 1 + ceil(k / 19) <= 59`; and on the `S >= 0` branch that loop folds
  `10^S` into the significand instead, adding at most `ceil(S / 19) <= 17` to
  the ingest's count, so `m.n <= 58` there.

| nest | cell | calls | bound |
|---|---|---|---|
| ingest (`for.body132.i.i` … `if.end151.i.i.sink.split`) | `m.n` = `v + 768` | `nestSteps 19 R` | `41` |
| fold, `S >= 0` (`while.body187.i.i` … `while.end190.i.i`) | `m.n` | `nestSteps 19 R + nestSteps 19 S` | `58` |
| sticky power (`while.body.i.i` … `while.end.i.i`) | `pow.n` = `v + 1544` | `nestSteps 27 k` | `42` |
| exact power (`while.body173.i.i` … `while.end176.i.i`) | `pow.n` | `nestSteps 19 k` | `59` |

All four are below `fbStkCapacity` (`96`), so `fbStkCounts_of_ties` turns the
producer's ties into the epilogue's premise, and `numCmp_copyLen_le_of_ties`
turns them into the copy's `776`.  The pins `ingest_limbs_at_max`,
`pow_five_limbs_at_max`, `pow_ten_limbs_at_max` and `fold_limbs_at_max` are the
numbers themselves, at the largest guard the clamps admit.

**What the bounds are, and are not.**  These are *iteration* counts: they need
no decode of the lexeme, and they are what the code's latches give.  The
value-based bounds of `JsonStage2NumFastStkArith` are tighter (`10 ^ 768` and
`10 ^ 309` for the significand, `5 ^ 1091` and `10 ^ 1091` for the power) but
need the memory tie that the number held is the model's; either way the answer
is under `96`.

**What is owed.**  The store's own count is now proved: `stkMulAddAnswer` — the
add-carry variant of `numStkMulAnswer` — leaves
`stkCount mem a = some (stkMulAddLimbs ws m c).length` (`stkMulAddAnswer_count`),
and `stkMulAddRun_exact` composes it over a nest's calls, so a run from
`stk_zero`'s zero (or `stk_from_u64`'s one) gives the tie with no count bound
carried.  What remains is that the emitted body *is* that run:
`mem = (stkMulAddRun base a ws calls).1` with `calls.length = nestSteps`.  That is
a statement about the inlined bodies (`for.body.i.i.i`:1415,
`while.body.us.i.i.i.i`:1709, `for.body.i566.i.i`:2012) which this tree does not
state; the store itself, the step lemma, the ceiling and the bridge are proved.
The last section below takes the tie from the other side: the store's own block
says which word it writes, so the tie is that word within the bound, and only the
nest's trip count is left (`stkCount_writeCount_bytes`,
`fbStkCounts_of_cleanup_end151`).

There is no `sorry`, `admit` or `native_decide` below.
-/
import LeanLLVM.Refinement.JsonStage2NumFastStkArith
import LeanLLVM.Refinement.JsonStage2NumFastCalleeMul
import LeanLLVM.Refinement.JsonStage2NumFastToDouble

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.NumFastCalleeCmp
open LeanLLVM.Refinement.NumFastFallback
open LeanLLVM.Refinement.NumFastStkArith
open LeanLLVM.Refinement.NumFastToDouble

namespace NumFastProducerCount

/-! ### The cells the count stores write

The IR's offsets and the model's offsets name the same cells.  `%n.i.i.i` is
`%v.i.i + 0x300` (`JsonStage2HelperIRNumFast`, `if.end126.i.i`), which
`stkCount` reads at `a + 768`; `%pow.i.i` is `%v.i.i + 0x308` and the power's
count `%n.i539.i.i` is `%v.i.i + 0x608`.  `%S128.i.i` and `%sticky127.i.i` are
the scale the branches test and the sticky word. -/

/-- The significand's count cell is the one `stkCount` reads. -/
theorem n_cell_eq_countOffset : (0x300 : Nat) = stkCountOffset := by decide

/-- The power's limbs start at `776`, one `StkBn` past the significand's. -/
theorem pow_cell_offset : (0x308 : Nat) = 776 := by decide

/-- The power's count cell is `stkCount mem (v + 776)`, the second count
`fbStkCounts` names. -/
theorem pow_n_cell_eq : (0x608 : Nat) = 776 + stkCountOffset := by decide

/-- The scale `S` the branches test sits past both `StkBn`s. -/
theorem S_cell_offset : (0x610 : Nat) = 1552 := by decide

/-- The sticky word sits after the scale. -/
theorem sticky_cell_offset : (0x618 : Nat) = 1560 := by decide

/-! ### The rows the nests multiply by

Each nest's multiplier is a 64-bit immediate in the unrolled body: `10 ^ 19` for
the ingest's chunks and for the exact power nest, `5 ^ 27` for the sticky one.
The step's arithmetic needs them below `2 ^ 64`, and each is. -/

/-- The ingest's chunk multiplier is `NUMF_EL1_P10[19]`. -/
theorem ingest_multiplier : (0x8ac7230489e80000 : Nat) = 10 ^ 19 := by decide

/-- It fits a limb. -/
theorem ingest_multiplier_lt : (10 : Nat) ^ 19 < 2 ^ 64 := by decide

/-- The sticky nest's multiplier is the largest power of five that fits a
limb. -/
theorem five_multiplier : (0x6765c793fa10079d : Nat) = 5 ^ 27 := by decide

/-- It fits a limb. -/
theorem five_multiplier_lt : (5 : Nat) ^ 27 < 2 ^ 64 := by decide

/-- The ten-power nests' residual row is `NUMF_EL1_P10[k]` at `k <= 19`, and it
fits a limb. -/
theorem ten_residual_lt {k : Nat} (hk : k ≤ 19) : (10 : Nat) ^ k < 2 ^ 64 := by
  calc (10 : Nat) ^ k ≤ 10 ^ 19 := Nat.pow_le_pow_right (by decide) hk
    _ < 2 ^ 64 := ingest_multiplier_lt

/-- The sticky nest's residual row is `STK_P5[k]` at `k < 27`, and it fits a
limb. -/
theorem five_residual_lt {k : Nat} (hk : k ≤ 26) : (5 : Nat) ^ k < 2 ^ 64 := by
  calc (5 : Nat) ^ k ≤ 5 ^ 26 := Nat.pow_le_pow_right (by decide) hk
    _ < 2 ^ 64 := by decide

/-- `5 ^ 27` is what the sticky loop subtracts, and `10 ^ 19` what the exact
loops subtract: the IR's steps are the unsigned `-27` and `-19`. -/
theorem step_five : (0xffffffffffffffe5 : Nat) + 27 = 2 ^ 64 := by decide

theorem step_ten : (0xffffffffffffffed : Nat) + 19 = 2 ^ 64 := by decide

/-! ### One call, and a sequence of them

`stk_mul_add(a, m, add)` folds `w * m + carry` over the live limbs and then
extends while a nonzero carry remains.  The fold keeps the input's limbs
(`stkMulFold_fst_length`) and a 64-bit addend keeps the carry a 64-bit word
(`stkMulFold_carry_lt`), so one call appends at most one limb — whatever its
multiplier and addend.  That is the step the ingest needs (its calls pass a
chunk as the addend) and the one the power nests need (their calls pass `0`). -/

/-- The limbs one `stk_mul_add` call leaves: the fold's kept limbs and the
carry's extending ones. -/
def stkMulAddLimbs (ws : List Nat) (m c : Nat) : List Nat :=
  (stkMulFold ws m c).1 ++ stkCarryLimbs (stkMulFold ws m c).2

/-- **One `stk_mul_add` call appends at most one limb.** -/
theorem stkMulAdd_length_le {ws : List Nat} {m c : Nat}
    (hws : ∀ w ∈ ws, w < 2 ^ 64) (hm : m < 2 ^ 64) (hc : c < 2 ^ 64) :
    (stkMulAddLimbs ws m c).length ≤ ws.length + 1 := by
  unfold stkMulAddLimbs
  rw [List.length_append, stkMulFold_fst_length]
  have hcarry : (stkMulFold ws m c).2 < 2 ^ 64 := stkMulFold_carry_lt hws hm hc
  have hlen : (stkCarryLimbs (stkMulFold ws m c).2).length ≤ 1 :=
    stkCarryLimbs_length_le hcarry
  omega

/-- A call's limbs are 64-bit words, so a call's output can feed the next
call's hypothesis. -/
theorem stkMulAdd_lt {ws : List Nat} {m c : Nat}
    (hws : ∀ w ∈ ws, w < 2 ^ 64) (hm : m < 2 ^ 64) (hc : c < 2 ^ 64) :
    ∀ w ∈ stkMulAddLimbs ws m c, w < 2 ^ 64 := by
  intro w hw
  unfold stkMulAddLimbs at hw
  rcases List.mem_append.mp hw with h | h
  · exact stkMulFold_fst_lt ws m c w h
  · exact stkCarryLimbs_lt (stkMulFold_carry_lt hws hm hc) w h

/-- `t` `stk_mul_add` calls in order, each from the list the previous left. -/
def stkMulAddCalls : List (Nat × Nat) → List Nat → List Nat
  | [], ws => ws
  | p :: ps, ws => stkMulAddCalls ps (stkMulAddLimbs ws p.1 p.2)

/-- **`t` `stk_mul_add` calls append at most `t` limbs.**  The rows are the
calls' own, so the ingest's `(10^19, chunk)` and `(10^cn, chunk)` pairs and the
nests' `(5^27, 0)` and `(5^k, 0)` pairs are both instances. -/
theorem stkMulAddCalls_length_le (calls : List (Nat × Nat)) (ws : List Nat)
    (hpc : ∀ p ∈ calls, p.1 < 2 ^ 64 ∧ p.2 < 2 ^ 64)
    (hws : ∀ w ∈ ws, w < 2 ^ 64) :
    (stkMulAddCalls calls ws).length ≤ ws.length + calls.length := by
  induction calls generalizing ws with
  | nil => simp [stkMulAddCalls]
  | cons p ps ih =>
      have hlt : p.1 < 2 ^ 64 ∧ p.2 < 2 ^ 64 := hpc p (by simp)
      have hnext : ∀ w ∈ stkMulAddLimbs ws p.1 p.2, w < 2 ^ 64 :=
        stkMulAdd_lt hws hlt.1 hlt.2
      have hstep : (stkMulAddLimbs ws p.1 p.2).length ≤ ws.length + 1 :=
        stkMulAdd_length_le hws hlt.1 hlt.2
      have hrest : (stkMulAddCalls ps (stkMulAddLimbs ws p.1 p.2)).length
          ≤ (stkMulAddLimbs ws p.1 p.2).length + ps.length :=
        ih (stkMulAddLimbs ws p.1 p.2) (fun q hq => hpc q (by simp [hq])) hnext
      have hunfold : stkMulAddCalls (p :: ps) ws
          = stkMulAddCalls ps (stkMulAddLimbs ws p.1 p.2) := rfl
      rw [hunfold, List.length_cons]
      omega

/-! ### The add-carry answer, and the count it writes

`numStkMulAnswer` models `stk_mul_add(a, m, 0)`; the ingest passes its chunk as
the addend.  `stkMulAddAnswer` is that call's memory step.  Its count cell holds
the limbs' length: the limbs are written first and the count last, so one append
leaves `stkCount mem a = some (stkMulAddLimbs ws m c).length` — the store's own
count, not an unconstrained four-byte read.  The addend's reach is one limb by
`stkMulAdd_length_le`. -/

/-- The addend-0 instance is `numStkMulAnswer`'s multiply. -/
theorem stkMulAddLimbs_zero (ws : List Nat) (m : Nat) :
    stkMulAddLimbs ws m 0 = stkMulWords ws m := rfl

/-- One append's memory: the limbs at `a`, then the count at `a + 768`. -/
def stkMulAddMem (mem : Mem) (a : Nat) (ws : List Nat) (m c : Nat) : Mem :=
  let ws' := stkMulAddLimbs ws m c
  writeBytes (stkWriteLimbs mem a ws') (a + stkCountOffset) (natToBytes ws'.length 4)

/-- **The append's count cell is the limbs' length.**  The count is written last,
after the limbs, so the four-byte read at `a + 768` is the count's write; a count
below `2 ^ 32` makes the little-endian round trip exact. -/
theorem stkCount_writeCount (mem : Mem) (a : Nat) (ws : List Nat)
    (hlen : ws.length < 2 ^ 32) :
    stkCount (writeBytes (stkWriteLimbs mem a ws) (a + stkCountOffset)
      (natToBytes ws.length 4)) a = some ws.length := by
  simp only [stkCount]
  have hread : readBytes (writeBytes (stkWriteLimbs mem a ws) (a + stkCountOffset)
      (natToBytes ws.length 4)) (a + stkCountOffset) 4 = some (natToBytes ws.length 4) := by
    rw [← natToBytes_length ws.length 4]
    exact readBytes_writeBytes_same _ _
  rw [hread]
  simp only [Option.map, Option.some.injEq]
  rw [natToBytes_toNat]
  have h256 : 256 ^ 4 = 2 ^ 32 := by decide
  rw [h256, Nat.mod_eq_of_lt hlen]

/-- The inlined append's memory step: `stk_mul_add(a, m, c)`, with the chunk as
the addend.  The count is the old count, the limbs are the old limbs, and the
result is the fold with the addend. -/
def stkMulAddAnswer (a m c : Nat) (mem : Mem) (next : Nat) : Option CallOutcome :=
  match stkCount mem a with
  | some n =>
      match stkLimbs mem a n with
      | some ws => some { ret := .int 1 0, mem := stkMulAddMem mem a ws m c, next := next }
      | none => some { ret := .int 1 0, mem := mem, next := next }
  | none => some { ret := .int 1 0, mem := mem, next := next }

/-- The same step at `stk_mul_add`'s three arguments, as a callee's answer. -/
def numStkMulAddAnswer (args : List Value) (mem : Mem) (next : Nat) : Option CallOutcome :=
  match args with
  | [.ptr a, .int 64 m, .int 64 c] => stkMulAddAnswer a m.toNat c.toNat mem next
  | _ => none

/-- **One append writes the loop's own count.**  From a count cell holding `n`
and the `n` limbs it names, the step's memory holds the new limbs' length in the
same cell. -/
theorem stkMulAddAnswer_count {a m c : Nat} {mem : Mem} {next n : Nat} {ws : List Nat}
    (hcnt : stkCount mem a = some n) (hl : stkLimbs mem a n = some ws)
    (hwords : ∀ w ∈ ws, w < 2 ^ 64) (hm : m < 2 ^ 64) (hc : c < 2 ^ 64)
    (hwslen : ws.length ≤ 96) :
    ∃ mem', stkMulAddAnswer a m c mem next
        = some { ret := .int 1 0, mem := mem', next := next }
      ∧ stkCount mem' a = some (stkMulAddLimbs ws m c).length := by
  have hlen : (stkMulAddLimbs ws m c).length ≤ ws.length + 1 :=
    stkMulAdd_length_le hwords hm hc
  have hlt : (stkMulAddLimbs ws m c).length < 2 ^ 32 := by omega
  refine ⟨_, ?_, stkCount_writeCount mem a (stkMulAddLimbs ws m c) hlt⟩
  simp only [stkMulAddAnswer, stkMulAddMem, hcnt, hl]

/-- The store's count at the ingest's own call shape, as a `Value` list. -/
theorem numStkMulAddAnswer_count {a : Nat} {m c : BitVec 64} {mem : Mem} {next n : Nat}
    {ws : List Nat} (hcnt : stkCount mem a = some n) (hl : stkLimbs mem a n = some ws)
    (hwords : ∀ w ∈ ws, w < 2 ^ 64) (hm : m.toNat < 2 ^ 64) (hc : c.toNat < 2 ^ 64)
    (hwslen : ws.length ≤ 96) :
    ∃ mem', numStkMulAddAnswer [.ptr a, .int 64 m, .int 64 c] mem next
        = some { ret := .int 1 0, mem := mem', next := next }
      ∧ stkCount mem' a = some (stkMulAddLimbs ws m.toNat c.toNat).length := by
  obtain ⟨mem', h, hc'⟩ := stkMulAddAnswer_count hcnt hl hwords hm hc hwslen
  refine ⟨mem', ?_, hc'⟩
  simpa only [numStkMulAddAnswer] using h

/-- **The out-of-line `stk_mul_u64` writes its own count too.**  Its write is the
addend-0 instance of the append: `stkMulWords ws m` is `stkMulAddLimbs ws m 0`. -/
theorem numStkMulAnswer_count {a : Nat} {m : BitVec 64} {mem : Mem} {next n : Nat}
    {ws : List Nat} (hcnt : stkCount mem a = some n) (hl : stkLimbs mem a n = some ws)
    (hwords : ∀ w ∈ ws, w < 2 ^ 64) (hm : m.toNat < 2 ^ 64) (hwslen : ws.length ≤ 96) :
    ∃ mem', numStkMulAnswer [.ptr a, .int 64 m] mem next
        = some { ret := .int 1 0, mem := mem', next := next }
      ∧ stkCount mem' a = some (stkMulWords ws m.toNat).length := by
  have hcarry : (stkMulFold ws m.toNat 0).2 < 2 ^ 64 :=
    stkMulFold_carry_lt hwords hm (by decide)
  have hlen : (stkMulWords ws m.toNat).length ≤ ws.length + 1 :=
    stkMulWords_length_le hcarry
  have hlt : (stkMulWords ws m.toNat).length < 2 ^ 32 := by omega
  refine ⟨_, ?_, stkCount_writeCount mem a (stkMulWords ws m.toNat) hlt⟩
  simp only [numStkMulAnswer, hcnt, hl]

/-! ### The limbs a written prefix reads back

The next call needs the limbs the previous one wrote, so the step's memory must
read them back at the same count.  The reads sit below the count's write and
above the earlier limbs' writes, which is what the two inductions below say. -/

/-- Writes below a read's range do not disturb it. -/
theorem readBytes_stkWriteLimbs_below (mem : Mem) :
    ∀ (ws : List Nat) (a q k : Nat), q + k ≤ a →
      readBytes (stkWriteLimbs mem a ws) q k = readBytes mem q k
  | [], _, _, _, _ => rfl
  | w :: ws, a, q, k, h => by
      show readBytes (stkWriteLimbs (writeBytes mem a (natToBytes (w % 2 ^ 64) 8))
        (a + 8) ws) q k = readBytes mem q k
      rw [readBytes_stkWriteLimbs_below (writeBytes mem a (natToBytes (w % 2 ^ 64) 8))
        ws (a + 8) q k (by omega)]
      exact readBytes_writeBytes_below mem (natToBytes (w % 2 ^ 64) 8) k q a h

/-- A written limb reads back at its own address. -/
theorem readBytes_stkWriteLimbs_at : (ws : List Nat) → (mem : Mem) → (a k : Nat) →
    (∀ w ∈ ws, w < 2 ^ 64) → k < ws.length →
      readBytes (stkWriteLimbs mem a ws) (a + 8 * k) 8
        = some (natToBytes ((ws.drop k).headD 0 % 2 ^ 64) 8)
  | [], mem, a, k, _, hk => absurd hk (by simp)
  | w :: ws, mem, a, k, hw, hk => by
      cases k with
      | zero =>
          show readBytes (stkWriteLimbs (writeBytes mem a (natToBytes (w % 2 ^ 64) 8))
            (a + 8) ws) a 8 = some (natToBytes (w % 2 ^ 64) 8)
          rw [readBytes_stkWriteLimbs_below (writeBytes mem a (natToBytes (w % 2 ^ 64) 8))
            ws (a + 8) a 8 (by omega)]
          exact readBytes_writeBytes_same mem (natToBytes (w % 2 ^ 64) 8) (addr := a)
      | succ j =>
          have hw' : ∀ u ∈ ws, u < 2 ^ 64 := fun u hu => hw u (by simp [hu])
          have hk' : j < ws.length := by simpa using hk
          show readBytes (stkWriteLimbs (writeBytes mem a (natToBytes (w % 2 ^ 64) 8))
            (a + 8) ws) (a + 8 * (j + 1)) 8
              = some (natToBytes (((w :: ws).drop (j + 1)).headD 0 % 2 ^ 64) 8)
          rw [show a + 8 * (j + 1) = (a + 8) + 8 * j from by omega]
          rw [readBytes_stkWriteLimbs_at ws (writeBytes mem a (natToBytes (w % 2 ^ 64) 8))
            (a + 8) j hw' hk']
          rfl

/-- The first limb of a drop is a limb of the list. -/
theorem headD_drop_lt : (l : List Nat) → (∀ w ∈ l, w < 2 ^ 64) → ∀ k, k < l.length →
    (l.drop k).headD 0 < 2 ^ 64
  | [], _, k, hk => absurd hk (by simp)
  | w :: ws, hw, k, hk => by
      cases k with
      | zero => exact hw w (by simp)
      | succ j =>
          have hw' : ∀ u ∈ ws, u < 2 ^ 64 := fun u hu => hw u (by simp [hu])
          have hk' : j < ws.length := by simpa using hk
          exact headD_drop_lt ws hw' j hk'

/-- Taking one more element appends the head of the drop. -/
theorem take_succ_headD_drop : (l : List Nat) → ∀ k, k < l.length →
    l.take k ++ [(l.drop k).headD 0] = l.take (k + 1)
  | [], k, hk => absurd hk (by simp)
  | w :: ws, k, hk => by
      cases k with
      | zero => rfl
      | succ j =>
          have hk' : j < ws.length := by simpa using hk
          show w :: (ws.take j ++ [(ws.drop j).headD 0]) = w :: ws.take (j + 1)
          rw [take_succ_headD_drop ws j hk']

/-- A prefix of the written limbs reads back as that prefix. -/
theorem stkLimbs_stkWriteLimbs_take (mem : Mem) (a : Nat) (ws : List Nat)
    (hw : ∀ w ∈ ws, w < 2 ^ 64) :
    ∀ k, k ≤ ws.length → stkLimbs (stkWriteLimbs mem a ws) a k = some (ws.take k) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      have hk' : k ≤ ws.length := by omega
      have hklt : k < ws.length := by omega
      have hstep : stkLimbs (stkWriteLimbs mem a ws) a (k + 1)
          = some (ws.take k ++
              [bytesToNat (natToBytes ((ws.drop k).headD 0 % 2 ^ 64) 8)]) := by
        simp only [stkLimbs, ih hk', readBytes_stkWriteLimbs_at ws mem a k hw hklt]
      rw [hstep]
      have hval : bytesToNat (natToBytes ((ws.drop k).headD 0 % 2 ^ 64) 8)
          = (ws.drop k).headD 0 := by
        rw [natToBytes_toNat]
        have h256 : 256 ^ 8 = 2 ^ 64 := by decide
        rw [h256, Nat.mod_mod]
        exact Nat.mod_eq_of_lt (headD_drop_lt ws hw k hklt)
      rw [hval, take_succ_headD_drop ws k hklt]

/-- **The whole written limb list reads back at its own count.** -/
theorem stkLimbs_stkWriteLimbs (mem : Mem) (a : Nat) (ws : List Nat)
    (hw : ∀ w ∈ ws, w < 2 ^ 64) :
    stkLimbs (stkWriteLimbs mem a ws) a ws.length = some ws := by
  have h := stkLimbs_stkWriteLimbs_take mem a ws hw ws.length (le_refl _)
  simpa using h

/-- A write above a `stkLimbs` read does not disturb it. -/
theorem stkLimbs_writeBytes_above (mem : Mem) (a : Nat) :
    ∀ (k start : Nat) (bs : List UInt8), a + 8 * k ≤ start →
      stkLimbs (writeBytes mem start bs) a k = stkLimbs mem a k
  | 0, _, _, _ => rfl
  | k + 1, start, bs, h => by
      simp only [stkLimbs]
      rw [stkLimbs_writeBytes_above mem a k start bs (by omega)]
      rw [readBytes_writeBytes_below mem bs 8 (a + 8 * k) start (by omega)]

/-- **The count's write does not disturb the limbs it counts.**  The count sits at
`a + 768`, at or above the last limb's read when there are at most `96`. -/
theorem stkLimbs_writeCount (mem : Mem) (a : Nat) (ws : List Nat)
    (hw : ∀ w ∈ ws, w < 2 ^ 64) (hlen : ws.length ≤ 96) :
    stkLimbs (writeBytes (stkWriteLimbs mem a ws) (a + stkCountOffset)
      (natToBytes ws.length 4)) a ws.length = some ws := by
  rw [stkLimbs_writeBytes_above (stkWriteLimbs mem a ws) a ws.length (a + stkCountOffset)
    (natToBytes ws.length 4) (by
      have hoff : stkCountOffset = 768 := rfl
      omega)]
  exact stkLimbs_stkWriteLimbs mem a ws hw

/-! ### The ceilings

`stage2.c` writes every one of the four nests as `while (k >= c) { multiply;
k -= c; }` followed by `if (k) multiply`, so the calls are `k / c` plus one for
a nonzero remainder, whatever the row.  `nestSteps` is that count, and the guard
`k <= c * t` at the clamps is what pins it. -/

/-- The multiplies a nest performs at exponent `k` and chunk `c`: one for each
full chunk and one for the remainder. -/
def nestSteps (c k : Nat) : Nat := k / c + if k % c = 0 then 0 else 1

/-- **The ceiling.**  `k <= c * t` digits, folded `c` at a time, take at most
`t` multiplies.  This is the whole arithmetic of the four bounds: the loops'
guards are `k >= c`, so `t` chunks cover `k`. -/
theorem nestSteps_le {c k t : Nat} (hc : 0 < c) (hk : k ≤ c * t) :
    nestSteps c k ≤ t := by
  unfold nestSteps
  have hdecomp : c * (k / c) + k % c = k := Nat.div_add_mod k c
  have hmod : k % c < c := Nat.mod_lt _ hc
  rcases Nat.eq_zero_or_pos (k % c) with hr | hr
  · have hzero : (if k % c = 0 then 0 else 1) = 0 := by simp [hr]
    rw [hzero, Nat.add_zero]
    have hk' : k = c * (k / c) := by
      have h := hdecomp
      rw [hr, Nat.add_zero] at h
      exact h.symm
    rw [hk'] at hk
    exact Nat.le_of_mul_le_mul_left hk hc
  · have hone : (if k % c = 0 then 0 else 1) = 1 := by
      simp [show k % c ≠ 0 from ne_of_gt hr]
    rw [hone]
    have hlow : c * (k / c) < k := by omega
    have hlt : c * (k / c) < c * t := lt_of_lt_of_le hlow hk
    have hquot : k / c < t := Nat.lt_of_mul_lt_mul_left hlt
    omega

/-- **The ingest's count, at the digit guard.**  `R <= 768` retained digits are
`40` chunks of `19` and a residual chunk: at most `41` limbs. -/
theorem ingest_limbs_le {R : Nat} (hR : R ≤ 768) : nestSteps 19 R ≤ 41 :=
  nestSteps_le (by decide) (by omega)

/-- The same number, at the largest `R` the guard admits. -/
theorem ingest_limbs_at_max : nestSteps 19 768 = 41 := by decide

/-- **The sticky power's count.**  `k = -S <= 1091` (`window_pow_k_le`) is `40`
steps of `27` and a residual: one limb of `1` plus `41` is at most `42`. -/
theorem pow_five_limbs_le {k : Nat} (hk : k ≤ 1091) : 1 + nestSteps 27 k ≤ 42 := by
  have h := nestSteps_le (c := 27) (k := k) (t := 41) (by decide) (by omega)
  omega

/-- The same number, at the largest `k` the clamps admit. -/
theorem pow_five_limbs_at_max : 1 + nestSteps 27 1091 = 42 := by decide

/-- **The exact power's count.**  `k = -S <= 1091` is `57` steps of `19` and a
residual: one limb of `1` plus `58` is at most `59`. -/
theorem pow_ten_limbs_le {k : Nat} (hk : k ≤ 1091) : 1 + nestSteps 19 k ≤ 59 := by
  have h := nestSteps_le (c := 19) (k := k) (t := 58) (by decide) (by omega)
  omega

/-- The same number, at the largest `k` the clamps admit. -/
theorem pow_ten_limbs_at_max : 1 + nestSteps 19 1091 = 59 := by decide

/-- **The significand's count on the `S >= 0` fold.**  The ingest's `41` limbs
and `ceil(S / 19) <= 17` folds of `10^19` at `S <= 309` (the `f >= 309` clamp
did not fire, so `S = f - (R - 1) <= 309`) are at most `58`. -/
theorem fold_limbs_le {R S : Nat} (hR : R ≤ 768) (hS : S ≤ 309) :
    nestSteps 19 R + nestSteps 19 S ≤ 58 := by
  have h1 : nestSteps 19 R ≤ 41 := nestSteps_le (by decide) (by omega)
  have h2 : nestSteps 19 S ≤ 17 := nestSteps_le (by decide) (by omega)
  omega

/-- The same number, at the largest pair the guard and the clamp admit. -/
theorem fold_limbs_at_max : nestSteps 19 768 + nestSteps 19 309 = 58 := by decide

/-- All four bounds are within the array's capacity. -/
theorem ingest_limbs_le_capacity {R : Nat} (hR : R ≤ 768) :
    nestSteps 19 R ≤ fbStkCapacity := by
  have h := ingest_limbs_le hR
  have hcap : fbStkCapacity = 96 := rfl
  omega

theorem pow_five_limbs_le_capacity {k : Nat} (hk : k ≤ 1091) :
    1 + nestSteps 27 k ≤ fbStkCapacity := by
  have h := pow_five_limbs_le hk
  have hcap : fbStkCapacity = 96 := rfl
  omega

theorem pow_ten_limbs_le_capacity {k : Nat} (hk : k ≤ 1091) :
    1 + nestSteps 19 k ≤ fbStkCapacity := by
  have h := pow_ten_limbs_le hk
  have hcap : fbStkCapacity = 96 := rfl
  omega

theorem fold_limbs_le_capacity {R S : Nat} (hR : R ≤ 768) (hS : S ≤ 309) :
    nestSteps 19 R + nestSteps 19 S ≤ fbStkCapacity := by
  have h := fold_limbs_le hR hS
  have hcap : fbStkCapacity = 96 := rfl
  omega

/-! ### The ties at the stores

A count cell is a four-byte read (`stkCount`).  Each tie below says the cell
holds at most the number of limbs the nest's calls can add, and names the stores
that write it.  The store's own count is proved (`stkMulAddAnswer_count`), and
`stkMulAddRun_exact` composes it over the calls; the tie follows once the nest's
memory is the model's run, `stkMulAddRun`. -/

/-- **The producer's count tie, at the store that writes a `StkBn`'s count.**
`a` is the `StkBn`'s base, so the cell is `a + 768`: `%n.i.i.i` for the
significand and `%n.i539.i.i` for the power.  `emitted` is the number of limbs
the nest's calls can append — one each, by `stkMulAdd_length_le`, from the count
its entry set (`stk_zero`'s zero, `stk_from_u64`'s one).

**This is a premise only about the run.**  The store's count is proved
(`stkMulAddAnswer_count`), and `stkMulAddRun_exact` composes it over a nest's
calls, so the tie follows from the memory being the model's run
(`stkMulAddRun` from the entry's zero or one).  What is not stated here is that
the emitted body is that run.  Each instantiation names its stores and its
entry. -/
def stkBnCountTie (mem : Mem) (a emitted : Nat) : Prop :=
  ∃ n, stkCount mem a = some n ∧ n ≤ emitted

/-- The ingest's tie, at `%n.i.i.i` (`v + 768`).  The stores are
`for.cond.cleanup.i.i`'s (from `%78`) and `if.end151.i.i.sink.split`'s (from
`%inc12.us.i522.i.i.sink`, the append at `while.body.us.i520.i.i`).  The chunk
loop calls `stk_mul_add` once per `19` digits (`if.then140.i.i` →
`for.body.i.i.i`) and the residual once (`if.then148.i.i` →
`for.body.i527.i.i`); `stk_zero` starts the count at zero, so the emitted count
is `nestSteps 19 R` and the guard `%cmp29.i.i` makes it at most `41`.  A run of
`for.body132.i.i` … `if.end151.i.i.sink.split` would discharge it. -/
def ingestCountTie (mem : Mem) (v R : Nat) : Prop :=
  stkBnCountTie mem v (nestSteps 19 R)

/-- The significand's tie on the `S >= 0` fold, at `%n.i.i.i` again: the stores
are `while.end190.i.i`'s (from `%116`, the `10^19` loop's count), the loop's
append at `while.body.us.i.i601.i.i`, and the residual's append at
`while.body.us.i.i624.i.i`.  The ingest's calls came first, then
`nestSteps 19 S` folds of `10^19` (`while.body187.i.i` → `for.body.i.i588.i.i`)
and the residual `for.body.lr.ph.i.i608.i.i`, so the emitted count is their sum
— at most `58` at `R <= 768` and `S <= 309`.  A run of
`while.cond184.preheader.i.i` … `for.body.i.i611.i.i` discharges it. -/
def foldCountTie (mem : Mem) (v R S : Nat) : Prop :=
  stkBnCountTie mem v (nestSteps 19 R + nestSteps 19 S)

/-- The power's tie on the sticky branch, at `%n.i539.i.i` (`v + 1544`): the
entry's `store 1` at `if.end151.i.i`, the loop's store at `while.end.i.i`, and
the append's at `while.body.us.i.i.i.i` (whose condition is that the carry
reached `2 ^ 64`).  `stk_from_u64(&v.pow, 1)` starts the count at one; the loop
calls `stk_mul_u64` once per `5 ^ 27` (`while.body.i.i` → `for.body.i.i.i.i`)
and the residual once (`for.body.lr.ph.i.i542.i.i`), so the emitted count is
`1 + nestSteps 27 k` — at most `42` at `k = -S <= 1091`.  A run of
`if.then153.i.i` … `while.end.i.i` discharges it. -/
def powFiveCountTie (mem : Mem) (v k : Nat) : Prop :=
  stkBnCountTie mem (v + 776) (1 + nestSteps 27 k)

/-- The power's tie on the `S >= 0` branch, at the same cell: the exact branch's
fold leaves the power at the entry's `1` (`stk_from_u64(&v.pow, 1)`, the store
of `1` to `%n.i539.i.i` at `if.end151.i.i`), so no multiply runs at all.  A run
of `if.end151.i.i` … `while.cond184.preheader.i.i` discharges it. -/
def powOneCountTie (mem : Mem) (v : Nat) : Prop :=
  stkBnCountTie mem (v + 776) 1

/-- The power's tie on the exact branch, at the same cell: the stores are
`while.body.us.i.i557.i.i`'s, `while.end176.thread.i.i`'s (`1`) and
`while.end176.i.i`'s.  `10 ^ 19` per loop step (`while.body173.i.i` →
`for.body.i.i566.i.i`), and the out-of-line `stk_mul_u64` for the residual
(`if.then178.i.i`), so the emitted count is `1 + nestSteps 19 k` — at most `59`
at `k = -S <= 1091`.  A run of `if.then167.i.i` … `while.end176.i.i`
discharges it. -/
def powTenCountTie (mem : Mem) (v k : Nat) : Prop :=
  stkBnCountTie mem (v + 776) (1 + nestSteps 19 k)

/-! ### The run, and the count invariant that grows by `nestSteps`

A nest is a sequence of the append calls above.  `stkMulAddRun` carries the
memory and the limbs list through a list of `(multiplier, addend)` calls; the
invariant `stkBnLimbs` says the count cell holds the limbs' length and the limbs
are the ones it names.  One answered call keeps the invariant
(`stkMulAddRun_exact`), so the count grows by at most one per call
(`stkMulAddCalls_length_le`) — the iteration's count invariant, at `nestSteps`. -/

/-- The limbs and the count a `StkBn` holds together: the count is their length,
and the limbs are what the count names. -/
def stkBnLimbs (mem : Mem) (a : Nat) (ws : List Nat) : Prop :=
  stkCount mem a = some ws.length ∧ stkLimbs mem a ws.length = some ws

/-- The calls' memories, the limbs carried alongside. -/
def stkMulAddRun (mem : Mem) (a : Nat) (ws : List Nat) : List (Nat × Nat) → Mem × List Nat
  | [] => (mem, ws)
  | p :: ps =>
      stkMulAddRun (stkMulAddMem mem a ws p.1 p.2) a (stkMulAddLimbs ws p.1 p.2) ps

/-- The run's limb list is `stkMulAddCalls`. -/
theorem stkMulAddRun_snd (mem : Mem) (a : Nat) (ws : List Nat)
    (calls : List (Nat × Nat)) :
    (stkMulAddRun mem a ws calls).2 = stkMulAddCalls calls ws := by
  induction calls generalizing mem ws with
  | nil => rfl
  | cons p ps ih =>
      simp only [stkMulAddRun, stkMulAddCalls]
      exact ih (stkMulAddMem mem a ws p.1 p.2) (stkMulAddLimbs ws p.1 p.2)

/-- **One answered call keeps the count tied to the limbs.** -/
theorem stkMulAddRun_exact {a : Nat} :
    ∀ (calls : List (Nat × Nat)) (mem : Mem) (ws : List Nat),
      stkBnLimbs mem a ws → (∀ w ∈ ws, w < 2 ^ 64) →
      (∀ p ∈ calls, p.1 < 2 ^ 64 ∧ p.2 < 2 ^ 64) →
      ws.length + calls.length ≤ 96 →
      stkBnLimbs (stkMulAddRun mem a ws calls).1 a (stkMulAddRun mem a ws calls).2
  | [], mem, ws, h, _, _, _ => by simpa [stkMulAddRun] using h
  | p :: ps, mem, ws, _, hwords, hpc, hcap => by
      have hp : p.1 < 2 ^ 64 ∧ p.2 < 2 ^ 64 := hpc p (by simp)
      have hle : (stkMulAddLimbs ws p.1 p.2).length ≤ ws.length + 1 :=
        stkMulAdd_length_le hwords hp.1 hp.2
      have hwords' : ∀ w ∈ stkMulAddLimbs ws p.1 p.2, w < 2 ^ 64 :=
        stkMulAdd_lt hwords hp.1 hp.2
      have hlen96 : (stkMulAddLimbs ws p.1 p.2).length ≤ 96 := by
        simp only [List.length_cons] at hcap
        omega
      have hcap' : (stkMulAddLimbs ws p.1 p.2).length + ps.length ≤ 96 := by
        simp only [List.length_cons] at hcap
        omega
      have hstep : stkBnLimbs (stkMulAddMem mem a ws p.1 p.2) a
          (stkMulAddLimbs ws p.1 p.2) :=
        ⟨stkCount_writeCount mem a (stkMulAddLimbs ws p.1 p.2) (by omega),
          stkLimbs_writeCount mem a (stkMulAddLimbs ws p.1 p.2) hwords' hlen96⟩
      exact stkMulAddRun_exact ps (stkMulAddMem mem a ws p.1 p.2)
        (stkMulAddLimbs ws p.1 p.2) hstep hwords' (fun q hq => hpc q (by simp [hq])) hcap'

/-- **The run's count tie grows by the calls.** -/
theorem stkMulAddRun_countTie {a : Nat} {mem : Mem} {ws : List Nat}
    {calls : List (Nat × Nat)} (h : stkBnLimbs mem a ws)
    (hwords : ∀ w ∈ ws, w < 2 ^ 64)
    (hpc : ∀ p ∈ calls, p.1 < 2 ^ 64 ∧ p.2 < 2 ^ 64)
    (hcap : ws.length + calls.length ≤ 96) :
    stkBnCountTie (stkMulAddRun mem a ws calls).1 a (ws.length + calls.length) := by
  have hex := stkMulAddRun_exact calls mem ws h hwords hpc hcap
  refine ⟨_, hex.1, ?_⟩
  rw [stkMulAddRun_snd]
  exact stkMulAddCalls_length_le calls ws hpc hwords

/-! ### The frames the two nests need

The ingest writes below `v + 776` and the power below `v + 1544`; each nest's
run leaves the other's cells alone.  These are the reads the branch composes. -/

/-- An append writes inside `[a, a + 776)`, so a read at or above it is the
underlying memory's. -/
theorem readBytes_stkMulAddMem_above {mem : Mem} {a : Nat} {ws : List Nat} {m c : Nat}
    (hwords : ∀ w ∈ ws, w < 2 ^ 64) (hm : m < 2 ^ 64) (hc : c < 2 ^ 64)
    (hlen : ws.length ≤ 95) {q k : Nat} (hq : a + 776 ≤ q) :
    readBytes (stkMulAddMem mem a ws m c) q k = readBytes mem q k := by
  have hcap : (stkMulAddLimbs ws m c).length ≤ 96 := by
    have := stkMulAdd_length_le hwords hm hc
    omega
  show readBytes (writeBytes (stkWriteLimbs mem a (stkMulAddLimbs ws m c))
      (a + stkCountOffset) (natToBytes (stkMulAddLimbs ws m c).length 4)) q k
      = readBytes mem q k
  have h1 : readBytes (writeBytes (stkWriteLimbs mem a (stkMulAddLimbs ws m c))
      (a + stkCountOffset) (natToBytes (stkMulAddLimbs ws m c).length 4)) q k
      = readBytes (stkWriteLimbs mem a (stkMulAddLimbs ws m c)) q k := by
    refine readBytes_writeBytes_above_stk _ _ k q (a + stkCountOffset) ?_
    rw [natToBytes_length]
    have hoff : stkCountOffset = 768 := rfl
    omega
  have h2 : readBytes (stkWriteLimbs mem a (stkMulAddLimbs ws m c)) q k
      = readBytes mem q k :=
    readBytes_stkWriteLimbs_above mem (stkMulAddLimbs ws m c) a q k (by omega)
  exact h1.trans h2

/-- An append writes at or above `a`, so a read below it is the underlying
memory's. -/
theorem readBytes_stkMulAddMem_below {mem : Mem} {a : Nat} {ws : List Nat} {m c : Nat}
    {q k : Nat} (hqk : q + k ≤ a) :
    readBytes (stkMulAddMem mem a ws m c) q k = readBytes mem q k := by
  show readBytes (writeBytes (stkWriteLimbs mem a (stkMulAddLimbs ws m c))
      (a + stkCountOffset) (natToBytes (stkMulAddLimbs ws m c).length 4)) q k
      = readBytes mem q k
  have h1 : readBytes (writeBytes (stkWriteLimbs mem a (stkMulAddLimbs ws m c))
      (a + stkCountOffset) (natToBytes (stkMulAddLimbs ws m c).length 4)) q k
      = readBytes (stkWriteLimbs mem a (stkMulAddLimbs ws m c)) q k := by
    refine readBytes_writeBytes_below _ _ k q (a + stkCountOffset) ?_
    have hoff : stkCountOffset = 768 := rfl
    omega
  have h2 := readBytes_stkWriteLimbs_below mem (stkMulAddLimbs ws m c) a q k hqk
  exact h1.trans h2

/-- The run does not touch reads at or above `a + 776`. -/
theorem readBytes_stkMulAddRun_above {a : Nat} :
    ∀ (calls : List (Nat × Nat)) (mem : Mem) (ws : List Nat) (q k : Nat),
      (∀ w ∈ ws, w < 2 ^ 64) →
      (∀ p ∈ calls, p.1 < 2 ^ 64 ∧ p.2 < 2 ^ 64) →
      ws.length + calls.length ≤ 96 → a + 776 ≤ q →
      readBytes (stkMulAddRun mem a ws calls).1 q k = readBytes mem q k
  | [], _, _, _, _, _, _, _, _ => rfl
  | p :: ps, mem, ws, q, k, hwords, hpc, hcap, hq => by
      have hp : p.1 < 2 ^ 64 ∧ p.2 < 2 ^ 64 := hpc p (by simp)
      have hwsle : ws.length ≤ 95 := by
        simp only [List.length_cons] at hcap
        omega
      have hcap' : (stkMulAddLimbs ws p.1 p.2).length + ps.length ≤ 96 := by
        simp only [List.length_cons] at hcap
        have := stkMulAdd_length_le hwords hp.1 hp.2
        omega
      have hstep := readBytes_stkMulAddMem_above (mem := mem) (a := a) (ws := ws)
        (m := p.1) (c := p.2) (q := q) (k := k) hwords hp.1 hp.2 hwsle hq
      have hr := readBytes_stkMulAddRun_above ps (stkMulAddMem mem a ws p.1 p.2)
        (stkMulAddLimbs ws p.1 p.2) q k (stkMulAdd_lt hwords hp.1 hp.2)
        (fun q' hq' => hpc q' (by simp [hq'])) hcap' hq
      exact hr.trans hstep

/-- The run does not touch reads below `a`. -/
theorem readBytes_stkMulAddRun_below {a : Nat} :
    ∀ (calls : List (Nat × Nat)) (mem : Mem) (ws : List Nat) (q k : Nat),
      (∀ w ∈ ws, w < 2 ^ 64) →
      (∀ p ∈ calls, p.1 < 2 ^ 64 ∧ p.2 < 2 ^ 64) →
      q + k ≤ a → readBytes (stkMulAddRun mem a ws calls).1 q k = readBytes mem q k
  | [], _, _, _, _, _, _, _ => rfl
  | p :: ps, mem, ws, q, k, hwords, hpc, hqk => by
      have hp : p.1 < 2 ^ 64 ∧ p.2 < 2 ^ 64 := hpc p (by simp)
      have hstep := readBytes_stkMulAddMem_below (mem := mem) (a := a) (ws := ws)
        (m := p.1) (c := p.2) (q := q) (k := k) hqk
      have hr := readBytes_stkMulAddRun_below ps (stkMulAddMem mem a ws p.1 p.2)
        (stkMulAddLimbs ws p.1 p.2) q k (stkMulAdd_lt hwords hp.1 hp.2)
        (fun q' hq' => hpc q' (by simp [hq'])) hqk
      exact hr.trans hstep

/-- **The ingest's tie, from its run.**  The base is `stk_zero`'s `0` limbs, and
the calls are `nestSteps 19 R`. -/
theorem ingestCountTie_of_run {mem : Mem} {v R : Nat} {calls : List (Nat × Nat)}
    (hR : R ≤ 768) (hzero : stkCount mem v = some 0)
    (hpc : ∀ p ∈ calls, p.1 < 2 ^ 64 ∧ p.2 < 2 ^ 64)
    (hlen : calls.length = nestSteps 19 R) :
    ingestCountTie (stkMulAddRun mem v [] calls).1 v R := by
  have hcap : ([] : List Nat).length + calls.length ≤ 96 := by
    have hnil : ([] : List Nat).length = 0 := rfl
    rw [hlen]
    have := ingest_limbs_le hR
    omega
  have htie := stkMulAddRun_countTie (a := v) (ws := []) ⟨hzero, rfl⟩ (by simp) hpc hcap
  simpa [ingestCountTie, hlen] using htie

/-- **The sticky power's tie, from its run.**  The base is `stk_from_u64`'s one
limb, and the calls are `nestSteps 27 k`. -/
theorem powFiveCountTie_of_run {mem : Mem} {v k : Nat} {calls : List (Nat × Nat)}
    (hk : k ≤ 1091) (hone : stkCount mem (v + 776) = some 1)
    (hl1 : stkLimbs mem (v + 776) 1 = some [1])
    (hpc : ∀ p ∈ calls, p.1 < 2 ^ 64 ∧ p.2 < 2 ^ 64)
    (hlen : calls.length = nestSteps 27 k) :
    powFiveCountTie (stkMulAddRun mem (v + 776) [1] calls).1 v k := by
  have hcap : ([1] : List Nat).length + calls.length ≤ 96 := by
    have h1 : ([1] : List Nat).length = 1 := rfl
    rw [hlen]
    have := pow_five_limbs_le hk
    omega
  have htie := stkMulAddRun_countTie (a := v + 776) (ws := [1])
    ⟨hone, hl1⟩ (by simp) hpc hcap
  simpa [powFiveCountTie, hlen] using htie

/-- **The exact power's tie, from its run.** -/
theorem powTenCountTie_of_run {mem : Mem} {v k : Nat} {calls : List (Nat × Nat)}
    (hk : k ≤ 1091) (hone : stkCount mem (v + 776) = some 1)
    (hl1 : stkLimbs mem (v + 776) 1 = some [1])
    (hpc : ∀ p ∈ calls, p.1 < 2 ^ 64 ∧ p.2 < 2 ^ 64)
    (hlen : calls.length = nestSteps 19 k) :
    powTenCountTie (stkMulAddRun mem (v + 776) [1] calls).1 v k := by
  have hcap : ([1] : List Nat).length + calls.length ≤ 96 := by
    have h1 : ([1] : List Nat).length = 1 := rfl
    rw [hlen]
    have := pow_ten_limbs_le hk
    omega
  have htie := stkMulAddRun_countTie (a := v + 776) (ws := [1])
    ⟨hone, hl1⟩ (by simp) hpc hcap
  simpa [powTenCountTie, hlen] using htie

/-- **The significand's tie on the `S >= 0` fold, from its run.**  The ingest's
calls come first, then the fold's. -/
theorem foldCountTie_of_run {mem : Mem} {v R S : Nat} {calls : List (Nat × Nat)}
    (hR : R ≤ 768) (hS : S ≤ 309) (hzero : stkCount mem v = some 0)
    (hpc : ∀ p ∈ calls, p.1 < 2 ^ 64 ∧ p.2 < 2 ^ 64)
    (hlen : calls.length = nestSteps 19 R + nestSteps 19 S) :
    foldCountTie (stkMulAddRun mem v [] calls).1 v R S := by
  have hcap : ([] : List Nat).length + calls.length ≤ 96 := by
    have hnil : ([] : List Nat).length = 0 := rfl
    rw [hlen]
    have := fold_limbs_le hR hS
    omega
  have htie := stkMulAddRun_countTie (a := v) (ws := []) ⟨hzero, rfl⟩ (by simp) hpc hcap
  simpa [foldCountTie, hlen] using htie

/-! ### The two nests on one struct

The ingest fills `v`'s `StkBn` and the power its neighbour at `v + 776`; the
ingest's run leaves the power's cells alone and the power's leaves the
significand's count alone.  So the sticky branch's two ties hold on the memory
both runs leave, and `fbStkCounts_of_ties` consumes them. -/

/-- The ingest run does not touch the power's count cell at `v + 1544`. -/
theorem ingestRun_pow_count {mem : Mem} {v R : Nat} {calls : List (Nat × Nat)}
    (hR : R ≤ 768) (hpc : ∀ p ∈ calls, p.1 < 2 ^ 64 ∧ p.2 < 2 ^ 64)
    (hlen : calls.length = nestSteps 19 R) :
    stkCount (stkMulAddRun mem v [] calls).1 (v + 776)
      = stkCount mem (v + 776) := by
  have hcap : ([] : List Nat).length + calls.length ≤ 96 := by
    have hnil : ([] : List Nat).length = 0 := rfl
    rw [hlen]
    have := ingest_limbs_le hR
    omega
  simp only [stkCount]
  rw [readBytes_stkMulAddRun_above calls mem [] ((v + 776) + stkCountOffset) 4
    (by simp) hpc hcap (by omega)]

/-- The ingest run does not touch the power's limbs at `v + 776`. -/
theorem ingestRun_pow_limbs {mem : Mem} {v R : Nat} {calls : List (Nat × Nat)}
    (hR : R ≤ 768) (hpc : ∀ p ∈ calls, p.1 < 2 ^ 64 ∧ p.2 < 2 ^ 64)
    (hlen : calls.length = nestSteps 19 R) :
    stkLimbs (stkMulAddRun mem v [] calls).1 (v + 776) 1
      = stkLimbs mem (v + 776) 1 := by
  have hcap : ([] : List Nat).length + calls.length ≤ 96 := by
    have hnil : ([] : List Nat).length = 0 := rfl
    rw [hlen]
    have := ingest_limbs_le hR
    omega
  simp only [stkLimbs]
  rw [readBytes_stkMulAddRun_above calls mem [] (v + 776) 8
    (by simp) hpc hcap (by omega)]

/-- The power run does not touch the significand's count cell at `v + 768`. -/
theorem powRun_v_count {mem : Mem} {v : Nat} {calls : List (Nat × Nat)}
    (hpc : ∀ p ∈ calls, p.1 < 2 ^ 64 ∧ p.2 < 2 ^ 64) :
    stkCount (stkMulAddRun mem (v + 776) [1] calls).1 v = stkCount mem v := by
  simp only [stkCount]
  rw [readBytes_stkMulAddRun_below calls mem [1] (v + stkCountOffset) 4
    (by simp) hpc (by
      have hoff : stkCountOffset = 768 := rfl
      omega)]

/-- **The sticky branch's two ties, from the two runs.** -/
theorem sticky_ties_of_runs {mem0 : Mem} {v R k : Nat} {callsM callsP : List (Nat × Nat)}
    (hR : R ≤ 768) (hk : k ≤ 1091)
    (hzero : stkCount mem0 v = some 0)
    (hone : stkCount mem0 (v + 776) = some 1)
    (hl1 : stkLimbs mem0 (v + 776) 1 = some [1])
    (hpcM : ∀ p ∈ callsM, p.1 < 2 ^ 64 ∧ p.2 < 2 ^ 64)
    (hpcP : ∀ p ∈ callsP, p.1 < 2 ^ 64 ∧ p.2 < 2 ^ 64)
    (hlenM : callsM.length = nestSteps 19 R)
    (hlenP : callsP.length = nestSteps 27 k) :
    stkBnCountTie (stkMulAddRun (stkMulAddRun mem0 v [] callsM).1 (v + 776) [1] callsP).1
        v (nestSteps 19 R)
      ∧ stkBnCountTie
          (stkMulAddRun (stkMulAddRun mem0 v [] callsM).1 (v + 776) [1] callsP).1
          (v + 776) (1 + nestSteps 27 k) := by
  have hM : stkBnCountTie (stkMulAddRun mem0 v [] callsM).1 v (nestSteps 19 R) :=
    ingestCountTie_of_run hR hzero hpcM hlenM
  have hcnt1 : stkCount (stkMulAddRun mem0 v [] callsM).1 (v + 776) = some 1 := by
    rw [ingestRun_pow_count hR hpcM hlenM, hone]
  have hl1' : stkLimbs (stkMulAddRun mem0 v [] callsM).1 (v + 776) 1 = some [1] := by
    rw [ingestRun_pow_limbs hR hpcM hlenM, hl1]
  have hP := powFiveCountTie_of_run hk hcnt1 hl1' hpcP hlenP
  obtain ⟨n0, hn0, hle0⟩ := hM
  refine ⟨⟨n0, ?_, hle0⟩, hP⟩
  rw [powRun_v_count hpcP, hn0]

/-! ### The bridge to the epilogue

`fbStkCounts` asks for two counts and their two bounds; the ties give the counts
and the pins give the bounds.  From there the comparator's copy is `≤ 776` bytes
(`numCmpCopyLen_le_of_value` at `96`, and `numCmpCopyLen_le` at the count). -/

/-- **The ties give the epilogue's premise.** -/
theorem fbStkCounts_of_ties {mem : Mem} {v emM emP : Nat}
    (hm : stkBnCountTie mem v emM) (hp : stkBnCountTie mem (v + 776) emP)
    (hM : emM ≤ fbStkCapacity) (hP : emP ≤ fbStkCapacity) :
    fbStkCounts mem v := by
  obtain ⟨nm, hnm, hnmle⟩ := hm
  obtain ⟨np, hnp, hnple⟩ := hp
  exact ⟨nm, np, hnm, hnp, le_trans hnmle hM, le_trans hnple hP⟩

/-- **The copy's fit, from the producer's ties.**  The count word the comparator
reads at `%v + 1544` is the power's, and it is inside both arrays. -/
theorem numCmp_copyLen_le_of_ties {mem : Mem} {v emM emP : Nat} {nw : BitVec 32}
    (hm : stkBnCountTie mem v emM) (hp : stkBnCountTie mem (v + 776) emP)
    (hM : emM ≤ fbStkCapacity) (hP : emP ≤ fbStkCapacity)
    (hread : readBytes mem (v + 1544) 4 = some (natToBytes nw.toNat 4)) :
    numCmpCopyLen nw ≤ 776 :=
  numCmp_copyLen_le_of_stkCounts (fbStkCounts_of_ties hm hp hM hP) hread

/-- **The sticky branch, end to end.**  `R <= 768`, `k <= 1091`, the ingest's
and the sticky power's ties, and the count word: the copy takes at most `776`
bytes, with no count bound carried as a hypothesis. -/
theorem numCmp_copyLen_le_of_sticky {mem : Mem} {v R k : Nat} {nw : BitVec 32}
    (hR : R ≤ 768) (hk : k ≤ 1091)
    (hm : ingestCountTie mem v R) (hp : powFiveCountTie mem v k)
    (hread : readBytes mem (v + 1544) 4 = some (natToBytes nw.toNat 4)) :
    numCmpCopyLen nw ≤ 776 :=
  numCmp_copyLen_le_of_ties hm hp
    (ingest_limbs_le_capacity hR) (pow_five_limbs_le_capacity hk) hread

/-- **The exact branch with `S < 0`, end to end.** -/
theorem numCmp_copyLen_le_of_exact {mem : Mem} {v R k : Nat} {nw : BitVec 32}
    (hR : R ≤ 768) (hk : k ≤ 1091)
    (hm : ingestCountTie mem v R) (hp : powTenCountTie mem v k)
    (hread : readBytes mem (v + 1544) 4 = some (natToBytes nw.toNat 4)) :
    numCmpCopyLen nw ≤ 776 :=
  numCmp_copyLen_le_of_ties hm hp
    (ingest_limbs_le_capacity hR) (pow_ten_limbs_le_capacity hk) hread

/-- **The exact branch with `S >= 0`, end to end.**  Here the power is the
entry's `1` (`while.end.thread.i.i`) and the significand carries the folds. -/
theorem numCmp_copyLen_le_of_fold {mem : Mem} {v R S : Nat} {nw : BitVec 32}
    (hR : R ≤ 768) (hS : S ≤ 309)
    (hm : foldCountTie mem v R S) (hp : powOneCountTie mem v)
    (hread : readBytes mem (v + 1544) 4 = some (natToBytes nw.toNat 4)) :
    numCmpCopyLen nw ≤ 776 :=
  numCmp_copyLen_le_of_ties hm hp
    (fold_limbs_le_capacity hR hS) (by have hcap : fbStkCapacity = 96 := rfl; omega) hread

/-! ### The sticky branch from the runs

The two runs' calls and the entry's two stores, with the clamp `R <= 768` and
`k <= 1091`: the copy takes at most `776` bytes with no count tie and no count
bound carried as a hypothesis. -/

/-- **The sticky branch, end to end.** -/
theorem numCmp_copyLen_le_of_sticky_runs {mem0 : Mem} {v R k : Nat} {nw : BitVec 32}
    {callsM callsP : List (Nat × Nat)}
    (hR : R ≤ 768) (hk : k ≤ 1091)
    (hzero : stkCount mem0 v = some 0)
    (hone : stkCount mem0 (v + 776) = some 1)
    (hl1 : stkLimbs mem0 (v + 776) 1 = some [1])
    (hpcM : ∀ p ∈ callsM, p.1 < 2 ^ 64 ∧ p.2 < 2 ^ 64)
    (hpcP : ∀ p ∈ callsP, p.1 < 2 ^ 64 ∧ p.2 < 2 ^ 64)
    (hlenM : callsM.length = nestSteps 19 R)
    (hlenP : callsP.length = nestSteps 27 k)
    (hread : readBytes
        (stkMulAddRun (stkMulAddRun mem0 v [] callsM).1 (v + 776) [1] callsP).1
        (v + 1544) 4 = some (natToBytes nw.toNat 4)) :
    numCmpCopyLen nw ≤ 776 := by
  have hties := sticky_ties_of_runs hR hk hzero hone hl1 hpcM hpcP hlenM hlenP
  exact numCmp_copyLen_le_of_ties hties.1 hties.2
    (ingest_limbs_le_capacity hR) (pow_five_limbs_le_capacity hk) hread

/-! ### The ties read off the stores' own blocks

The route above carries the whole memory: `stkMulAddRun` names the run a nest's
calls make, and a tie follows once the memory *is* that run.  The tie itself asks
for less.  `stkBnCountTie` wants the count cell to hold some `n` within the
emitted bound, and a count store writes one four-byte word, so the cell's read is
that word — independent of the limbs, of the multiplies, and of any model.

The block the store sits in says which word and where.  `JsonStage2NumFastToDouble`
states the stores below at their own pins: `cleanup_denote` and
`sinkSplit_denote` write the ingest's limb counter at `%v + 0x300` (`%78` at the
cleanup, its increment at the residue's spill), `end151_denote` writes the
literal `1` at `%v + 0x608`, and `end176_denote` and `whileEnd_denote` write the
power's limb counter there.  Composing a store with the readback therefore *is*
the tie, and what stays behind is a single `Nat` inequality on the word the block
stored — not a memory shape and not a limb list.

**The stores that have no block lemma.**  The blocks that append the last limb
and bump the count in one step — `while.body.us.i.i.i`
(`JsonStage2HelperIRNumFast:1415`) and `while.body.us.i520.i.i` (`:1549`) for
the ingest, `while.body.us.i.i557.i.i` (`:1853`) and `while.body.us.i.i624.i.i`
(`:2303`) for the power and the fold — are not stated in
`JsonStage2NumFastToDouble`: its header names the unrolled bodies and the carry
blocks as "not stated here yet".  They are stated beside it: the ingest's two in
`JsonStage2NumFastIngestAppend` (`bus1415_*`, `bus520_*`), the exact power's in
`JsonStage2NumFastPowAppend` (`bus557_*`), the fold's in
`JsonStage2NumFastFoldAppend` (`bus624_*`), and `while.end190.i.i`, which spills
the fold's count `%116` at `%n.i.i.i` (`JsonStage2HelperIRNumFast:2229`), has its
own `denote` in `JsonStage2NumFastToDouble` with the readback and the tie beside
it (`end190_readback`, `end190_spill_tie`).  What those modules do not supply is
the loop invariant that hands each append its counter — `bus557_readback` takes
`c.toNat = w` for exactly that reason — so the counts are reached here through
the exits until the loops' invariants are stated. -/

/-- **A count store reads back at its own cell.**  The store writes four bytes at
`base + 768` and `stkCount mem base` reads exactly those four bytes. -/
theorem stkCount_writeCount_bytes (mem : Mem) (base k : Nat) (hk : k < 2 ^ 32) :
    stkCount (writeBytes mem (base + stkCountOffset) (natToBytes k 4)) base = some k := by
  have hread : readBytes (writeBytes mem (base + stkCountOffset) (natToBytes k 4))
      (base + stkCountOffset) (natToBytes k 4).length = some (natToBytes k 4) :=
    readBytes_writeBytes_same mem (natToBytes k 4)
  rw [natToBytes_length] at hread
  unfold stkCount
  rw [hread]
  show some (bytesToNat (natToBytes k 4)) = some k
  rw [natToBytes_toNat, show (256 : Nat) ^ 4 = 2 ^ 32 from by decide,
    Nat.mod_eq_of_lt hk]

/-- A write at or above a `StkBn`'s count cell leaves the cell's read alone. -/
theorem stkCount_writeBytes_above (mem : Mem) (base start : Nat) (bs : List UInt8)
    (h : base + stkCountOffset + 4 ≤ start) :
    stkCount (writeBytes mem start bs) base = stkCount mem base := by
  unfold stkCount
  rw [readBytes_writeBytes_below mem bs 4 (base + stkCountOffset) start h]

/-- The memory `if.end151.i.i` leaves: one limb and the count `1` of the power,
at the frame's `+ 0x308` and `+ 0x608`. -/
def end151Mem (mem : Mem) (v : Nat) : Mem :=
  writeBytes (writeBytes mem (v + 776) (natToBytes 1 8)) (v + 1544) (natToBytes 1 4)

/-- `if.end151.i.i`'s chain, with its two stores written at the frame's own
offsets — `0x308` is `776` and `0x608` is `776 + 768`. -/
theorem end151_denote_mem {calls : Calls} {env : Env} {s : State}
    {v : Nat} {st : BitVec 32}
    (hv : lookupName env "%v.i.i" = some (.ptr v))
    (hst : lookupName env "%sticky.0714.i.i" = some (.int 32 st)) :
    denoteCode calls end151Instrs (stateAt env s) =
      some (stateAt (end151Env env v st) { s with mem := end151Mem s.mem v }) := by
  rw [end151_denote hv hst]
  simp only [end151Mem,
    show ((0x0000000000000308#64).signExtend 64).toNat = 776 from by decide,
    show ((0x0000000000000608#64).signExtend 64).toNat = 1544 from by decide,
    show (0x0000000000000001#64).toNat = 1 from by decide,
    show (0x0000000000000001#32).toNat = 1 from by decide]

/-- **The staging's own store is the power's `1`.**  `if.end151.i.i` sets
`%n.i539.i.i` to the literal, and the four bytes it writes are the read
`stkCount` performs at `v + 776`; the tie holds with no hypothesis beyond the
block's own. -/
theorem powOneCountTie_of_end151 {calls : Calls} {env : Env} {s : State}
    {v : Nat} {st : BitVec 32}
    (hv : lookupName env "%v.i.i" = some (.ptr v))
    (hst : lookupName env "%sticky.0714.i.i" = some (.int 32 st)) :
    ∃ (env' : Env) (s' : State),
      denoteCode calls end151Instrs (stateAt env s) = some (stateAt env' s')
      ∧ powOneCountTie s'.mem v := by
  refine ⟨end151Env env v st, { s with mem := end151Mem s.mem v },
    end151_denote_mem hv hst, ?_⟩
  have hoff : (v + 776) + stkCountOffset = v + 1544 := by
    unfold stkCountOffset; omega
  refine ⟨1, ?_, by decide⟩
  unfold end151Mem
  rw [← hoff]
  exact stkCount_writeCount_bytes (writeBytes s.mem (v + 776) (natToBytes 1 8))
    (v + 776) 1 (by decide)

/-- **The cleanup's own store is the ingest's count.**  `for.cond.cleanup.i.i`
writes the limb counter `%78` at `%v + 0x300`; the tie's `n` is that word, so
the tie follows from a bound on the counter alone. -/
theorem ingestCountTie_of_cleanup {calls : Calls} {env : Env} {s : State}
    {x : BitVec 32} {v : Nat} {c : BitVec 32} {R : Nat}
    (hx : lookupName env "%78" = some (.int 32 x))
    (hn : lookupName env "%n.i.i.i" = some (.ptr (v + stkCountOffset)))
    (hc : lookupName env "%cn.1.i.i" = some (.int 32 c))
    (hR : R ≤ 768) (hxle : x.toNat ≤ nestSteps 19 R) :
    ∃ (env' : Env) (s' : State),
      denoteCode calls cleanupInstrs (stateAt env s) = some (stateAt env' s')
      ∧ ingestCountTie s'.mem v R := by
  have hx32 : x.toNat < 2 ^ 32 := by
    have := ingest_limbs_le hR
    omega
  refine ⟨cleanupEnv env c,
    { s with mem := writeBytes s.mem (v + stkCountOffset) (natToBytes x.toNat 4) },
    cleanup_denote hx hn hc, ?_⟩
  exact ⟨x.toNat, stkCount_writeCount_bytes s.mem v x.toNat hx32, hxle⟩

/-- **The residue's exit is the ingest's count.**  `if.end151.i.i.sink.split`
writes the counter `%inc12.us.i522.i.i.sink` — the chunk loop's phi — at
`%v + 0x300`, so the tie is that word, and a bound on it is what remains. -/
theorem ingestCountTie_of_sinkSplit {calls : Calls} {env : Env} {s : State}
    {pre : String} {op : Operand} {k : BitVec 32} {v : Nat} {R : Nat}
    (hpre : s.pre = some pre)
    (hop : phiIncoming pre
      [("while.body.us.i520.i.i", (Operand.reg "%inc12.us.i522.i.i")),
       ("if.end126.i.i", (Operand.imm (Const.int 32 0x00000000#32)))] = some op)
    (hov : evalOperand (stateAt env s) op = some (.int 32 k))
    (hn : lookupName env "%n.i.i.i" = some (.ptr (v + stkCountOffset)))
    (hR : R ≤ 768) (hkle : k.toNat ≤ nestSteps 19 R) :
    ∃ (env' : Env) (s' : State),
      denoteCode calls sinkSplitBlock (stateAt env s) = some (stateAt env' s')
      ∧ ingestCountTie s'.mem v R := by
  have hk32 : k.toNat < 2 ^ 32 := by
    have := ingest_limbs_le hR
    omega
  refine ⟨_, { s with mem := writeBytes s.mem (v + stkCountOffset) (natToBytes k.toNat 4) },
    sinkSplit_denote hpre hop hov hn, ?_⟩
  exact ⟨k.toNat, stkCount_writeCount_bytes s.mem v k.toNat hk32, hkle⟩

/-- **The outer multiply's spill is the power's count.**  `while.end176.i.i`
writes the group counter `%inc12.us.i.i581758.i.i` at `%v + 0x608`, which is the
read `stkCount` performs at `v + 776`; the tie is that word within `em`. -/
theorem powCountTie_of_end176 {calls : Calls} {env : Env} {s : State}
    {k : BitVec 32} {r : BitVec 64} {v em : Nat}
    (hk : lookupName env "%inc12.us.i.i581758.i.i" = some (.int 32 k))
    (hn : lookupName env "%n.i539.i.i" = some (.ptr ((v + 776) + stkCountOffset)))
    (hr : lookupName env "%sub175.i.i" = some (.int 64 r))
    (hem : em < 2 ^ 32) (hkle : k.toNat ≤ em) :
    ∃ (env' : Env) (s' : State),
      denoteCode calls end176Instrs (stateAt env s) = some (stateAt env' s')
      ∧ stkBnCountTie s'.mem (v + 776) em := by
  have hk32 : k.toNat < 2 ^ 32 := Nat.lt_of_le_of_lt hkle hem
  refine ⟨end176Env env r,
    { s with mem := writeBytes s.mem ((v + 776) + stkCountOffset) (natToBytes k.toNat 4) },
    end176_denote hk hn hr, ?_⟩
  exact ⟨k.toNat, stkCount_writeCount_bytes s.mem (v + 776) k.toNat hk32, hkle⟩

/-- **The sticky peel's merge is the power's count.**  `while.end.i.i` writes the
counter `%inc12.us.i.i744.i.i` at `%v + 0x608` after the out-of-line multiplies;
the tie is that word within `em`.  `whileEnd_denote` is the block's chain, and
`whileEndState` is the state that chain leaves. -/
theorem powCountTie_of_whileEnd {calls : Calls} {env : Env} {s : State}
    {inc12 : BitVec 32} {d : BitVec 64} {v em : Nat}
    (hn : lookupName env "%n.i539.i.i" = some (.ptr ((v + 776) + stkCountOffset)))
    (hinc : lookupName env "%inc12.us.i.i744.i.i" = some (.int 32 inc12))
    (hd : lookupName env "%sub158.i.i" = some (.int 64 d))
    (hem : em < 2 ^ 32) (hle : inc12.toNat ≤ em) :
    ∃ (env' : Env) (s' : State),
      denoteCode calls whileEndInstrs (stateAt env s) = some (stateAt env' s')
      ∧ stkBnCountTie s'.mem (v + 776) em := by
  refine ⟨whileEndEnv env inc12 d,
    { s with mem := writeBytes s.mem ((v + 776) + stkCountOffset) (natToBytes inc12.toNat 4) },
    ?_, ?_⟩
  · exact whileEnd_denote hn hinc hd
  · refine ⟨inc12.toNat, ?_, hle⟩
    exact stkCount_writeCount_bytes s.mem (v + 776) inc12.toNat (Nat.lt_of_le_of_lt hle hem)

/-- **The two count stores leave `fbStkCounts`.**  The ingest's count sits at
`v + 768`; the staging's two writes at `v + 776` and `v + 1544` are above it, so
the first survives them, and the second is the power's own cell. -/
theorem fbStkCounts_of_count_stores (mem : Mem) (v x : Nat) (hx : x ≤ 96) :
    fbStkCounts
      (end151Mem (writeBytes mem (v + stkCountOffset) (natToBytes x 4)) v) v := by
  have hx32 : x < 2 ^ 32 := by
    have hcap : fbStkCapacity = 96 := rfl
    omega
  have h1 : v + stkCountOffset + 4 ≤ v + 1544 := by
    unfold stkCountOffset; omega
  have h2 : v + stkCountOffset + 4 ≤ v + 776 := by
    unfold stkCountOffset; omega
  have h3 : (v + 776) + stkCountOffset = v + 1544 := by
    unfold stkCountOffset; omega
  refine ⟨x, 1, ?_, ?_, hx, by decide⟩
  · unfold end151Mem
    rw [stkCount_writeBytes_above _ v (v + 1544) _ h1,
      stkCount_writeBytes_above _ v (v + 776) _ h2]
    exact stkCount_writeCount_bytes mem v x hx32
  · unfold end151Mem
    rw [← h3]
    exact stkCount_writeCount_bytes _ (v + 776) 1 (by decide)

/-- **The ingest's exit into the staging, end to end.**  `for.cond.cleanup.i.i`
writes the significand's count and `if.end151.i.i` the power's one limb and count;
the two stores are the two blocks' own `denote`s, and after them `fbStkCounts`
holds.  The only fact left is the limb counter's bound. -/
theorem fbStkCounts_of_cleanup_end151 {calls : Calls} {env : Env} {s : State}
    {x : BitVec 32} {c : BitVec 32} {st : BitVec 32} {v R : Nat}
    (hx : lookupName env "%78" = some (.int 32 x))
    (hn : lookupName env "%n.i.i.i" = some (.ptr (v + stkCountOffset)))
    (hc : lookupName env "%cn.1.i.i" = some (.int 32 c))
    (hv : lookupName env "%v.i.i" = some (.ptr v))
    (hst : lookupName env "%sticky.0714.i.i" = some (.int 32 st))
    (hR : R ≤ 768) (hxle : x.toNat ≤ nestSteps 19 R) :
    ∃ (env1 : Env) (s1 : State) (env2 : Env) (s2 : State),
      denoteCode calls cleanupInstrs (stateAt env s) = some (stateAt env1 s1) ∧
      denoteCode calls end151Instrs (stateAt env1 s1) = some (stateAt env2 s2) ∧
      fbStkCounts s2.mem v := by
  have hxcap : x.toNat ≤ 96 := by
    have hcap : fbStkCapacity = 96 := rfl
    have := ingest_limbs_le_capacity hR
    omega
  have hv' : lookupName (cleanupEnv env c) "%v.i.i" = some (.ptr v) := by
    simp only [cleanupEnv]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact hv
  have hst' : lookupName (cleanupEnv env c) "%sticky.0714.i.i" = some (.int 32 st) := by
    simp only [cleanupEnv]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact hst
  let s1 : State := { s with mem := writeBytes s.mem (v + stkCountOffset) (natToBytes x.toNat 4) }
  have hclean : denoteCode calls cleanupInstrs (stateAt env s)
      = some (stateAt (cleanupEnv env c) s1) := cleanup_denote hx hn hc
  have hend : denoteCode calls end151Instrs (stateAt (cleanupEnv env c) s1)
      = some (stateAt (end151Env (cleanupEnv env c) v st)
          { s1 with mem := end151Mem s1.mem v }) := end151_denote_mem hv' hst'
  exact ⟨cleanupEnv env c, s1, end151Env (cleanupEnv env c) v st,
    { s1 with mem := end151Mem s1.mem v }, hclean, hend,
    fbStkCounts_of_count_stores s.mem v x.toNat hxcap⟩

/-! ### Axiom footprints

The add-carry store, the run's step invariant, and the ties read off the stores'
own blocks, pinned so the build checks them. -/

/-- info: 'LeanLLVM.Refinement.NumFastProducerCount.stkMulAddAnswer_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stkMulAddAnswer_count

/-- info: 'LeanLLVM.Refinement.NumFastProducerCount.stkMulAddRun_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stkMulAddRun_exact

/-- info: 'LeanLLVM.Refinement.NumFastProducerCount.powOneCountTie_of_end151' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms powOneCountTie_of_end151

/-- info: 'LeanLLVM.Refinement.NumFastProducerCount.ingestCountTie_of_cleanup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ingestCountTie_of_cleanup

/-- info: 'LeanLLVM.Refinement.NumFastProducerCount.fbStkCounts_of_cleanup_end151' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fbStkCounts_of_cleanup_end151

/-- info: 'LeanLLVM.Refinement.NumFastProducerCount.powCountTie_of_end176' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms powCountTie_of_end176

end NumFastProducerCount

end LeanLLVM.Refinement
