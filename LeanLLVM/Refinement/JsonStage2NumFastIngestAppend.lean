/-
The ingest's two carry appends, and the count each leaves behind.

`stage2.c`'s digit ingest multiplies the significand by `10 ^ 19` and adds the
next digit once per group; when a group's `i128` carry is non-zero it is
truncated to a limb, stored at `%v + 8 * n`, and the limb count is bumped.  The
block leaves the bumped counter in a register; the count's cell is written by
the block that follows it (`for.cond.cleanup.i.i` for the chunk loop,
`if.end151.i.i.sink.split` for the residual).

`JsonStage2NumFastToDouble` states the staging (`if.end151.i.i`), the two count
stores (`for.cond.cleanup.i.i`, `if.end151.i.i.sink.split`) and the two nests'
other carry blocks, but not the two blocks that append the ingest's final carry:
`while.body.us.i.i.i` (the chunk loop's drain, into `for.inc143.i.i`) and
`while.body.us.i520.i.i` (the residual chunk's drain, into
`if.end151.i.i.sink.split`).  This module states both at their pins, in the
to_double module's idiom — a list of instructions, the environment the chain
leaves, `denoteCode` over the block and `step` at the block's own pin — and
proves what the count readback needs: the store extends the list `stkLimbs`
reads by the carry's low word, the count's cell is untouched, and the bumped
word the block carries is that list's length.  Composed with the sink split's
own store (`sinkSplit_step`), the residual block therefore leaves
`stkCount mem v = some (ws ++ [w]).length`: the tie's `∃ n` is discharged.
`bus520_count_tie` closes its `n ≤ nestSteps 19 R` from the chunk loop's exit
invariant (`ingestChunkInvariant`), and that invariant is also the premise of
the cleanup path's `fbStkCounts_of_cleanup_end151`.

There is no `sorry`, `admit` or `native_decide` below.
-/
import LeanLLVM.Refinement.JsonStage2NumFastProducerCount

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.NumFastTier1
open LeanLLVM.Refinement.NumFastToDouble
open LeanLLVM.Refinement.NumFastFallback
open LeanLLVM.Refinement.NumFastProducerCount

namespace NumFastIngestAppend

/-! ### The count word's arithmetic

The block truncates an `i128` carry to the limb the store writes, and bumps a
32-bit counter.  Both words are read back at `Nat`s below. -/

/-- Sign extension at equal width is the identity. -/
theorem signExtend_self_64_toNat (x : BitVec 64) : (x.signExtend 64).toNat = x.toNat := by
  rw [BitVec.signExtend_eq]

/-- A non-negative 32-bit counter's sign extension is its zero extension. -/
theorem sext32_toNat {x : BitVec 32} (hmsb : x.msb = false) :
    (BitVec.signExtend 64 x).toNat = x.toNat := by
  rw [BitVec.toNat_signExtend, hmsb]
  simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
  rw [BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (by decide : (2 : Nat) ^ 32 ≤ 2 ^ 64))]

/-- The `%idxprom` cell's 64-bit value is the counter, when its top bit is
clear.  This is the `(k.signExtend 64).toNat = k.toNat` hypothesis the block
chains take, discharged once for the two ingest appends. -/
theorem sext32_idx_toNat {x : BitVec 32} (hmsb : x.msb = false) :
    ((BitVec.ofNat 64
      (BitVec.signExtend 64 (BitVec.ofNat 32 x.toNat)).toNat).signExtend 64).toNat
        = x.toNat := by
  rw [signExtend_self_64_toNat, BitVec.toNat_ofNat]
  rw [show BitVec.ofNat 32 x.toNat = x from by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]]
  rw [sext32_toNat hmsb,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (by decide : (2 : Nat) ^ 32 ≤ 2 ^ 64))]

/-- A count the guard admits has its top bit clear. -/
theorem msb32_false_of_lt {x : BitVec 32} (hx : x.toNat < 2 ^ 31) : x.msb = false := by
  rw [BitVec.msb_eq_decide, decide_eq_false_iff_not, show (32 - 1) = 31 from rfl]
  have h2 : (2 : Nat) ^ 31 = 2147483648 := by decide
  rw [h2] at hx ⊢
  omega

/-- The bump's own word: `x + 1` at 32 bits, read at its value. -/
theorem inc32_toNat (x : BitVec 32) (hx : x.toNat ≤ 95) :
    (x + 0x0000000000000001#32).toNat = x.toNat + 1 := by
  have h1 : (0x0000000000000001#32 : BitVec 32).toNat = 1 := by decide
  rw [BitVec.toNat_add_of_lt (by
    rw [h1, show (2 : Nat) ^ 32 = 4294967296 from by decide]; omega), h1]

/-! ### The `stkLimbs` frame the append needs

The block writes eight bytes at `a + 8 * n`, the index the count names.  That is
above the `n` limbs `stkLimbs` reads and below the count's cell at `a + 768`, so
the read grows by exactly the one word and the count's read is unchanged. -/

/-- A `stkLimbs` read names as many limbs as it was asked for. -/
theorem stkLimbs_length {mem : Mem} {a k : Nat} {ws : List Nat}
    (h : stkLimbs mem a k = some ws) : ws.length = k := by
  induction k generalizing ws with
  | zero =>
      simp only [stkLimbs, Option.some.injEq] at h
      subst h
      rfl
  | succ k ih =>
      cases hk : stkLimbs mem a k with
      | none =>
          simp only [stkLimbs, hk] at h
          exact absurd h (by simp)
      | some ws0 =>
          cases hb : readBytes mem (a + 8 * k) 8 with
          | none =>
              simp only [stkLimbs, hk, hb] at h
              exact absurd h (by simp)
          | some bs =>
              simp only [stkLimbs, hk, hb, Option.some.injEq] at h
              subst h
              simp only [List.length_append, List.length_singleton, ih hk]

/-- **An eight-byte store at the count's index appends one limb.** -/
theorem stkLimbs_writeBytes_append (mem : Mem) (a n : Nat) (w : BitVec 64)
    (ws : List Nat) (hws : stkLimbs mem a n = some ws) :
    stkLimbs (writeBytes mem (a + 8 * n) (natToBytes w.toNat 8)) a (n + 1)
      = some (ws ++ [w.toNat]) := by
  have hb : bytesToNat (natToBytes w.toNat 8) = w.toNat := by
    rw [natToBytes_toNat, show (256 : Nat) ^ 8 = 2 ^ 64 from by decide,
      Nat.mod_eq_of_lt w.isLt]
  have hread : readBytes (writeBytes mem (a + 8 * n) (natToBytes w.toNat 8))
      (a + 8 * n) 8 = some (natToBytes w.toNat 8) := by
    have h := readBytes_writeBytes_same mem (natToBytes w.toNat 8) (addr := a + 8 * n)
    rwa [natToBytes_length] at h
  simp only [stkLimbs]
  rw [stkLimbs_writeBytes_above mem a n (a + 8 * n) (natToBytes w.toNat 8) (le_refl _),
    hws, hread]
  show some (ws ++ [bytesToNat (natToBytes w.toNat 8)]) = some (ws ++ [w.toNat])
  rw [hb]

/-- A store below the count's cell leaves the count's read alone. -/
theorem stkCount_writeBytes_below (mem : Mem) (base start : Nat) (bs : List UInt8)
    (h : start + bs.length ≤ base + stkCountOffset) :
    stkCount (writeBytes mem start bs) base = stkCount mem base := by
  unfold stkCount
  rw [readBytes_writeBytes_above_stk mem bs 4 (base + stkCountOffset) start h]

/-- A count store at `a + 768` leaves the `96`-limb read it counts alone. -/
theorem stkLimbs_writeCount_frame (mem : Mem) (a : Nat) (ws : List Nat)
    (h : stkLimbs mem a ws.length = some ws) (hlen : ws.length ≤ 96) :
    stkLimbs (writeBytes mem (a + stkCountOffset) (natToBytes ws.length 4)) a ws.length
      = some ws := by
  rw [stkLimbs_writeBytes_above mem a ws.length (a + stkCountOffset) (natToBytes ws.length 4) (by unfold stkCountOffset; omega)]
  exact h

/-! ### The chunk loop's drain: `while.body.us.i.i.i`

`%70` is the significand's limb counter (the phi at `for.body132.i.i`, fed back
through `%78`); the block truncates the last group's `i128` carry, stores it at
`%v + 8 * %70`, bumps the counter into `%inc12.us.i.i.i`, and continues at
`for.inc143.i.i`.  The counter's cell is not written here: the latch carries the
bumped word to `%78`, and `for.cond.cleanup.i.i`'s own `denote` writes it. -/

/-- The block's instructions. -/
def bus1415Instrs : List Instr :=
  [Instr.trunc "%conv9.us.i.i.i" 128 64 (Operand.reg "%carry.0.lcssa.i.i.i"),
   Instr.binop "%inc12.us.i.i.i" (BinOp.add) 32 (Operand.reg "%70")
     (Operand.imm (Const.int 32 0x0000000000000001#32)),
   Instr.sext "%idxprom13.us.i.i.i" 32 64 (Operand.reg "%70"),
   Instr.gep "%arrayidx14.us.i.i.i" (Ty.int 64) (Operand.reg "%v.i.i")
     (Operand.reg "%idxprom13.us.i.i.i"),
   Instr.store (Ty.int 64) (Operand.reg "%conv9.us.i.i.i")
     (Operand.reg "%arrayidx14.us.i.i.i")]

theorem bus1415_find :
    numFastBody.findBlock "while.body.us.i.i.i" =
      some ⟨"while.body.us.i.i.i", bus1415Instrs, Term.br "for.inc143.i.i"⟩ := by
  simpa only [bus1415Instrs] using numFast_findBlock_while_body_us_i_i_i

/-- The environment the block leaves: the address, the index, the bumped
counter, and the truncated carry in front of the incoming cells. -/
def bus1415Env (env : Env) (v : Nat) (x : BitVec 32) (c : BitVec 128) : Env :=
  ("%arrayidx14.us.i.i.i", .ptr (v + x.toNat * 8)) ::
  ("%idxprom13.us.i.i.i", .int 64 (BitVec.ofNat 64
    (BitVec.signExtend 64 (BitVec.ofNat 32 x.toNat)).toNat)) ::
  ("%inc12.us.i.i.i", .int 32 (x + 0x0000000000000001#32)) ::
  ("%conv9.us.i.i.i", .int 64 (BitVec.ofNat 64 (c.toNat % 2 ^ 64))) :: env

theorem bus1415_denote {calls : Calls} {env : Env} {s : State}
    {x : BitVec 32} {c : BitVec 128} {v : Nat}
    (hx : lookupName env "%70" = some (.int 32 x))
    (hc : lookupName env "%carry.0.lcssa.i.i.i" = some (.int 128 c))
    (hv : lookupName env "%v.i.i" = some (.ptr v))
    (hmsb : x.msb = false) (hpos : x.toNat < 2 ^ 63) :
    denoteCode calls bus1415Instrs (stateAt env s) =
      some (stateAt (bus1415Env env v x c)
        { s with mem := writeBytes s.mem (v + x.toNat * 8) (natToBytes (BitVec.ofNat 64 (c.toNat % 2 ^ 64)).toNat 8) }) := by
  have hidx : ((BitVec.ofNat 64
      (BitVec.signExtend 64 (BitVec.ofNat 32 x.toNat)).toNat).signExtend 64).toNat
        = x.toNat := sext32_idx_toNat hmsb
  unfold bus1415Instrs
  rw [denoteCode_trunc calls env s "%conv9.us.i.i.i" "%carry.0.lcssa.i.i.i" 128 64 hc]
  rw [NumFastToDouble.denoteCode_add_imm_w calls
    (("%conv9.us.i.i.i", .int 64 (BitVec.ofNat 64 (c.toNat % 2 ^ 64))) :: env) s
    "%inc12.us.i.i.i" "%70" 32
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact hx)]
  rw [NumFastToDouble.denoteCode_sext calls
    (("%inc12.us.i.i.i", .int 32 (x + 0x0000000000000001#32)) ::
      ("%conv9.us.i.i.i", .int 64 (BitVec.ofNat 64 (c.toNat % 2 ^ 64))) :: env) s
    "%idxprom13.us.i.i.i" "%70" 32 64
    (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
        exact hx)]
  rw [NumFastTier1.denoteCode_gep64_reg calls
    (("%idxprom13.us.i.i.i", .int 64 (BitVec.ofNat 64
        (BitVec.signExtend 64 (BitVec.ofNat 32 x.toNat)).toNat)) ::
      ("%inc12.us.i.i.i", .int 32 (x + 0x0000000000000001#32)) ::
      ("%conv9.us.i.i.i", .int 64 (BitVec.ofNat 64 (c.toNat % 2 ^ 64))) :: env) s
    "%arrayidx14.us.i.i.i" "%v.i.i" "%idxprom13.us.i.i.i"
    (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact hv)
    (lookupName_cons_self ..) (by rw [hidx]; exact hpos)]
  rw [hidx]
  rw [denoteCode_store64 calls
    (("%arrayidx14.us.i.i.i", .ptr (v + x.toNat * 8)) ::
      ("%idxprom13.us.i.i.i", .int 64 (BitVec.ofNat 64
        (BitVec.signExtend 64 (BitVec.ofNat 32 x.toNat)).toNat)) ::
      ("%inc12.us.i.i.i", .int 32 (x + 0x0000000000000001#32)) ::
      ("%conv9.us.i.i.i", .int 64 (BitVec.ofNat 64 (c.toNat % 2 ^ 64))) :: env) s
    "%conv9.us.i.i.i" "%arrayidx14.us.i.i.i"
    (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact lookupName_cons_self ..)
    (lookupName_cons_self ..)]
  simp only [denoteCode_nil, bus1415Env, stateAt]

/-- **The drain's step**, into the latch `for.inc143.i.i`. -/
theorem bus1415_step {calls : Calls} {env : Env} {s : State}
    {x : BitVec 32} {c : BitVec 128} {v : Nat}
    (hpc : s.pc = "while.body.us.i.i.i")
    (hx : lookupName env "%70" = some (.int 32 x))
    (hc : lookupName env "%carry.0.lcssa.i.i.i" = some (.int 128 c))
    (hv : lookupName env "%v.i.i" = some (.ptr v))
    (hmsb : x.msb = false) (hpos : x.toNat < 2 ^ 63) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (bus1415Env env v x c)
        { s with mem := writeBytes s.mem (v + x.toNat * 8) (natToBytes (BitVec.ofNat 64 (c.toNat % 2 ^ 64)).toNat 8),
                 pc := "for.inc143.i.i", pre := some "while.body.us.i.i.i" }) := by
  refine numFast_step_at (s' := stateAt (bus1415Env env v x c)
      { s with mem := writeBytes s.mem (v + x.toNat * 8) (natToBytes (BitVec.ofNat 64 (c.toNat % 2 ^ 64)).toNat 8) })
    (b := ⟨"while.body.us.i.i.i", bus1415Instrs, Term.br "for.inc143.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using bus1415_find
  · simpa only [stateAt] using bus1415_denote (calls := calls) hx hc hv hmsb hpos
  · simp only [execTerm, stateAt, hpc]

/-- **The ingest append's readback.**  From the `n` limbs the count names, the
block's store leaves `n + 1` — the old list plus the carry's low word — and
its counter cell holds `n + 1`; the count's own cell is unchanged, so the
latch's word, written by the cleanup's `denote`, is the list's length. -/
theorem bus1415_readback {calls : Calls} {env : Env} {s : State}
    {x : BitVec 32} {c : BitVec 128} {v : Nat} {ws : List Nat}
    (hx : lookupName env "%70" = some (.int 32 x))
    (hc : lookupName env "%carry.0.lcssa.i.i.i" = some (.int 128 c))
    (hv : lookupName env "%v.i.i" = some (.ptr v))
    (hmsb : x.msb = false) (hpos : x.toNat < 2 ^ 63)
    (hxle : x.toNat ≤ 95)
    (hlimbs : stkLimbs s.mem v x.toNat = some ws) :
    ∃ (env' : Env) (s' : State),
      denoteCode calls bus1415Instrs (stateAt env s) = some (stateAt env' s')
      ∧ lookupName env' "%inc12.us.i.i.i"
          = some (.int 32 (x + 0x0000000000000001#32))
      ∧ stkLimbs s'.mem v (x.toNat + 1)
          = some (ws ++ [(BitVec.ofNat 64 (c.toNat % 2 ^ 64)).toNat])
      ∧ stkCount s'.mem v = stkCount s.mem v := by
  let s' : State := { s with mem := writeBytes s.mem (v + x.toNat * 8) (natToBytes (BitVec.ofNat 64 (c.toNat % 2 ^ 64)).toNat 8) }
  refine ⟨bus1415Env env v x c, s',
    bus1415_denote (calls := calls) hx hc hv hmsb hpos, ?_, ?_, ?_⟩
  · simp only [bus1415Env]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact lookupName_cons_self ..
  · show stkLimbs (writeBytes s.mem (v + x.toNat * 8) (natToBytes (BitVec.ofNat 64 (c.toNat % 2 ^ 64)).toNat 8)) v (x.toNat + 1) = _
    rw [show v + x.toNat * 8 = v + 8 * x.toNat from by rw [Nat.mul_comm x.toNat 8]]
    exact stkLimbs_writeBytes_append s.mem v x.toNat
      (BitVec.ofNat 64 (c.toNat % 2 ^ 64)) ws hlimbs
  · show stkCount (writeBytes s.mem (v + x.toNat * 8) (natToBytes (BitVec.ofNat 64 (c.toNat % 2 ^ 64)).toNat 8)) v = stkCount s.mem v
    rw [show v + x.toNat * 8 = v + 8 * x.toNat from by rw [Nat.mul_comm x.toNat 8]]
    exact stkCount_writeBytes_below s.mem v (v + 8 * x.toNat) _
      (by rw [natToBytes_length, show stkCountOffset = 768 from rfl]; omega)

/-! ### The residual chunk's drain: `while.body.us.i520.i.i`

The same block at `%78` (the counter the latch carries), continuing into
`if.end151.i.i.sink.split`, which writes the bumped word to the count's cell.
The composition below is the count readback: the sink split's store lands on
the cell `stkCount` reads, and the store the block made is above the limbs the
count names. -/

/-- The block's instructions. -/
def bus520Instrs : List Instr :=
  [Instr.trunc "%conv9.us.i521.i.i" 128 64 (Operand.reg "%carry.0.lcssa.i518.i.i"),
   Instr.binop "%inc12.us.i522.i.i" (BinOp.add) 32 (Operand.reg "%78")
     (Operand.imm (Const.int 32 0x0000000000000001#32)),
   Instr.sext "%idxprom13.us.i523.i.i" 32 64 (Operand.reg "%78"),
   Instr.gep "%arrayidx14.us.i524.i.i" (Ty.int 64) (Operand.reg "%v.i.i")
     (Operand.reg "%idxprom13.us.i523.i.i"),
   Instr.store (Ty.int 64) (Operand.reg "%conv9.us.i521.i.i")
     (Operand.reg "%arrayidx14.us.i524.i.i")]

theorem bus520_find :
    numFastBody.findBlock "while.body.us.i520.i.i" =
      some ⟨"while.body.us.i520.i.i", bus520Instrs,
        Term.br "if.end151.i.i.sink.split"⟩ := by
  simpa only [bus520Instrs] using numFast_findBlock_while_body_us_i520_i_i

/-- The environment the block leaves: the address, the index, the bumped
counter, and the truncated carry in front of the incoming cells. -/
def bus520Env (env : Env) (v : Nat) (x : BitVec 32) (c : BitVec 128) : Env :=
  ("%arrayidx14.us.i524.i.i", .ptr (v + x.toNat * 8)) ::
  ("%idxprom13.us.i523.i.i", .int 64 (BitVec.ofNat 64
    (BitVec.signExtend 64 (BitVec.ofNat 32 x.toNat)).toNat)) ::
  ("%inc12.us.i522.i.i", .int 32 (x + 0x0000000000000001#32)) ::
  ("%conv9.us.i521.i.i", .int 64 (BitVec.ofNat 64 (c.toNat % 2 ^ 64))) :: env

theorem bus520_denote {calls : Calls} {env : Env} {s : State}
    {x : BitVec 32} {c : BitVec 128} {v : Nat}
    (hx : lookupName env "%78" = some (.int 32 x))
    (hc : lookupName env "%carry.0.lcssa.i518.i.i" = some (.int 128 c))
    (hv : lookupName env "%v.i.i" = some (.ptr v))
    (hmsb : x.msb = false) (hpos : x.toNat < 2 ^ 63) :
    denoteCode calls bus520Instrs (stateAt env s) =
      some (stateAt (bus520Env env v x c)
        { s with mem := writeBytes s.mem (v + x.toNat * 8) (natToBytes (BitVec.ofNat 64 (c.toNat % 2 ^ 64)).toNat 8) }) := by
  have hidx : ((BitVec.ofNat 64
      (BitVec.signExtend 64 (BitVec.ofNat 32 x.toNat)).toNat).signExtend 64).toNat
        = x.toNat := sext32_idx_toNat hmsb
  unfold bus520Instrs
  rw [denoteCode_trunc calls env s "%conv9.us.i521.i.i" "%carry.0.lcssa.i518.i.i" 128 64 hc]
  rw [NumFastToDouble.denoteCode_add_imm_w calls
    (("%conv9.us.i521.i.i", .int 64 (BitVec.ofNat 64 (c.toNat % 2 ^ 64))) :: env) s
    "%inc12.us.i522.i.i" "%78" 32
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact hx)]
  rw [NumFastToDouble.denoteCode_sext calls
    (("%inc12.us.i522.i.i", .int 32 (x + 0x0000000000000001#32)) ::
      ("%conv9.us.i521.i.i", .int 64 (BitVec.ofNat 64 (c.toNat % 2 ^ 64))) :: env) s
    "%idxprom13.us.i523.i.i" "%78" 32 64
    (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
        exact hx)]
  rw [NumFastTier1.denoteCode_gep64_reg calls
    (("%idxprom13.us.i523.i.i", .int 64 (BitVec.ofNat 64
        (BitVec.signExtend 64 (BitVec.ofNat 32 x.toNat)).toNat)) ::
      ("%inc12.us.i522.i.i", .int 32 (x + 0x0000000000000001#32)) ::
      ("%conv9.us.i521.i.i", .int 64 (BitVec.ofNat 64 (c.toNat % 2 ^ 64))) :: env) s
    "%arrayidx14.us.i524.i.i" "%v.i.i" "%idxprom13.us.i523.i.i"
    (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact hv)
    (lookupName_cons_self ..) (by rw [hidx]; exact hpos)]
  rw [hidx]
  rw [denoteCode_store64 calls
    (("%arrayidx14.us.i524.i.i", .ptr (v + x.toNat * 8)) ::
      ("%idxprom13.us.i523.i.i", .int 64 (BitVec.ofNat 64
        (BitVec.signExtend 64 (BitVec.ofNat 32 x.toNat)).toNat)) ::
      ("%inc12.us.i522.i.i", .int 32 (x + 0x0000000000000001#32)) ::
      ("%conv9.us.i521.i.i", .int 64 (BitVec.ofNat 64 (c.toNat % 2 ^ 64))) :: env) s
    "%conv9.us.i521.i.i" "%arrayidx14.us.i524.i.i"
    (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact lookupName_cons_self ..)
    (lookupName_cons_self ..)]
  simp only [denoteCode_nil, bus520Env, stateAt]

/-- **The residual drain's step**, into the staging's spill. -/
theorem bus520_step {calls : Calls} {env : Env} {s : State}
    {x : BitVec 32} {c : BitVec 128} {v : Nat}
    (hpc : s.pc = "while.body.us.i520.i.i")
    (hx : lookupName env "%78" = some (.int 32 x))
    (hc : lookupName env "%carry.0.lcssa.i518.i.i" = some (.int 128 c))
    (hv : lookupName env "%v.i.i" = some (.ptr v))
    (hmsb : x.msb = false) (hpos : x.toNat < 2 ^ 63) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (bus520Env env v x c)
        { s with mem := writeBytes s.mem (v + x.toNat * 8) (natToBytes (BitVec.ofNat 64 (c.toNat % 2 ^ 64)).toNat 8),
                 pc := "if.end151.i.i.sink.split",
                 pre := some "while.body.us.i520.i.i" }) := by
  refine numFast_step_at (s' := stateAt (bus520Env env v x c)
      { s with mem := writeBytes s.mem (v + x.toNat * 8) (natToBytes (BitVec.ofNat 64 (c.toNat % 2 ^ 64)).toNat 8) })
    (b := ⟨"while.body.us.i520.i.i", bus520Instrs,
      Term.br "if.end151.i.i.sink.split"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using bus520_find
  · simpa only [stateAt] using bus520_denote (calls := calls) hx hc hv hmsb hpos
  · simp only [execTerm, stateAt, hpc]

/-- **The residual append's count readback, through the staging's store.**  The
block extends the list to `n + 1` and bumps `%inc12.us.i522.i.i`; the sink split
then writes that word to `%n.i.i.i`, so the count's cell reads back the list's
length: `stkCount mem v = some (ws ++ [w]).length`.  The sink split's store is
`n + 1`, which is the list's length by construction, and the count store does
not disturb the limbs it counts. -/
theorem bus520_count_read {calls : Calls} {env : Env} {s : State}
    {x : BitVec 32} {c : BitVec 128} {v : Nat} {ws : List Nat}
    (hpc : s.pc = "while.body.us.i520.i.i")
    (hx : lookupName env "%78" = some (.int 32 x))
    (hc : lookupName env "%carry.0.lcssa.i518.i.i" = some (.int 128 c))
    (hv : lookupName env "%v.i.i" = some (.ptr v))
    (hn : lookupName env "%n.i.i.i" = some (.ptr (v + stkCountOffset)))
    (hmsb : x.msb = false) (hpos : x.toNat < 2 ^ 63)
    (hxle : x.toNat ≤ 95)
    (hwslt : ∀ z ∈ ws, z < 2 ^ 64)
    (hlimbs : stkLimbs s.mem v x.toNat = some ws) :
    ∃ (s1 s2 : State),
      step calls numFastBody (stateAt env s) = .jump s1
      ∧ step calls numFastBody s1 = .jump s2
      ∧ stkCount s2.mem v = some (x.toNat + 1)
      ∧ stkLimbs s2.mem v (x.toNat + 1)
          = some (ws ++ [(BitVec.ofNat 64 (c.toNat % 2 ^ 64)).toNat]) := by
  let env1 : Env := bus520Env env v x c
  let m1 : Mem := writeBytes s.mem (v + x.toNat * 8) (natToBytes (BitVec.ofNat 64 (c.toNat % 2 ^ 64)).toNat 8)
  let s1 : State := stateAt env1 { s with mem := m1, pc := "if.end151.i.i.sink.split", pre := some "while.body.us.i520.i.i" }
  let m2 : Mem := writeBytes s1.mem (v + stkCountOffset) (natToBytes (x + 0x0000000000000001#32).toNat 4)
  let s2 : State := stateAt
    (("%inc12.us.i522.i.i.sink", .int 32 (x + 0x0000000000000001#32)) :: env1)
    { s1 with mem := m2, pc := "if.end151.i.i", pre := some "if.end151.i.i.sink.split" }
  have h1 : step calls numFastBody (stateAt env s) = .jump s1 :=
    bus520_step (calls := calls) hpc hx hc hv hmsb hpos
  have hidx1 : lookupName env1 "%inc12.us.i522.i.i"
      = some (.int 32 (x + 0x0000000000000001#32)) := by
    simp only [env1, bus520Env]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact lookupName_cons_self ..
  have hn1 : lookupName env1 "%n.i.i.i" = some (.ptr (v + stkCountOffset)) := by
    simp only [env1, bus520Env]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact hn
  have hop : phiIncoming "while.body.us.i520.i.i"
      [("while.body.us.i520.i.i", (Operand.reg "%inc12.us.i522.i.i")),
       ("if.end126.i.i", (Operand.imm (Const.int 32 0x0000000000000000#32)))]
        = some (.reg "%inc12.us.i522.i.i") := by
    simp [phiIncoming]
  have hov : evalOperand (stateAt env1 s1) (.reg "%inc12.us.i522.i.i")
      = some (.int 32 (x + 0x0000000000000001#32)) :=
    evalOperand_reg_of env1 s1 "%inc12.us.i522.i.i"
      (.int 32 (x + 0x0000000000000001#32)) hidx1
  have h2 : step calls numFastBody s1 = .jump s2 :=
    sinkSplit_step (calls := calls) (env := env1) (s := s1)
      (pre := "while.body.us.i520.i.i") (op := (.reg "%inc12.us.i522.i.i"))
      (k := (x + 0x0000000000000001#32)) (a := v + stkCountOffset)
      rfl rfl hop hov hn1
  refine ⟨s1, s2, h1, h2, ?_, ?_⟩
  · show stkCount (writeBytes s1.mem (v + stkCountOffset) (natToBytes (x + 0x0000000000000001#32).toNat 4)) v = some (x.toNat + 1)
    rw [inc32_toNat x hxle]
    exact stkCount_writeCount_bytes s1.mem v (x.toNat + 1)
      (by rw [show (2 : Nat) ^ 32 = 4294967296 from by decide]; omega)
  · have hlen : ws.length = x.toNat := stkLimbs_length hlimbs
    have hwlen : (ws ++ [(BitVec.ofNat 64 (c.toNat % 2 ^ 64)).toNat]).length
        = x.toNat + 1 := by
      simp only [List.length_append, List.length_singleton, hlen]
    have hlimbs1 : stkLimbs s1.mem v (x.toNat + 1)
        = some (ws ++ [(BitVec.ofNat 64 (c.toNat % 2 ^ 64)).toNat]) := by
      show stkLimbs (writeBytes s.mem (v + x.toNat * 8) (natToBytes (BitVec.ofNat 64 (c.toNat % 2 ^ 64)).toNat 8)) v (x.toNat + 1) = _
      rw [show v + x.toNat * 8 = v + 8 * x.toNat from by rw [Nat.mul_comm x.toNat 8]]
      exact stkLimbs_writeBytes_append s.mem v x.toNat
        (BitVec.ofNat 64 (c.toNat % 2 ^ 64)) ws hlimbs
    have hwlt : ∀ z ∈ ws ++ [(BitVec.ofNat 64 (c.toNat % 2 ^ 64)).toNat],
        z < 2 ^ 64 := by
      intro z hz
      rcases List.mem_append.mp hz with h | h
      · exact hwslt z h
      · simp only [List.mem_singleton] at h
        subst h
        exact BitVec.isLt _
    have hlen96 : (ws ++ [(BitVec.ofNat 64 (c.toNat % 2 ^ 64)).toNat]).length ≤ 96 := by
      rw [hwlen]; omega
    show stkLimbs (writeBytes s1.mem (v + stkCountOffset) (natToBytes (x + 0x0000000000000001#32).toNat 4)) v (x.toNat + 1) = _
    rw [show (x + 0x0000000000000001#32).toNat
        = (ws ++ [(BitVec.ofNat 64 (c.toNat % 2 ^ 64)).toNat]).length from by
      rw [inc32_toNat x hxle]; exact hwlen.symm]
    rw [show x.toNat + 1
        = (ws ++ [(BitVec.ofNat 64 (c.toNat % 2 ^ 64)).toNat]).length from hwlen.symm]
    exact stkLimbs_writeCount_frame s1.mem v
      (ws ++ [(BitVec.ofNat 64 (c.toNat % 2 ^ 64)).toNat])
      (by rw [hwlen]; exact hlimbs1) hlen96

/-! ### The chunk loop's invariant, and the tie it supplies

The chunk loop (`for.body132.i.i` … `for.inc143.i.i`) calls `stk_mul_add` once
per nineteen digits, and one call appends at most one limb
(`stkMulAddCalls_length_le`), so at its exit the significand holds at most
`R / 19` limbs and the count's cell names exactly the limbs present.  The
residual chunk's call is the nest's last: `for.cond.cleanup.i.i` reaches
`if.then148.i.i` and the drain `while.body.us.i520.i.i` only when `%cn.1.i.i`
is non-zero, which is the non-zero remainder `R % 19`.  So the counter the
drain reads is below `nestSteps 19 R`, and its bump reaches that bound.  That
is the hypothesis `bus520_count_read` takes — its `≤ 95` bound, sign extension
and 64-bit limbs all follow from `R ≤ 768` — and the postcondition is the
epilogue's tie `ingestCountTie`, which `fbStkCounts_of_ties` reads. -/

/-- The chunk loop's exit, as the residual drain reads it: the count's cell
holds the limbs present, the counter is at most one per nineteen digits, and
the residual chunk exists (the drain is reached only on a non-zero
`%cn.1.i.i`, which is the non-zero remainder). -/
def ingestChunkInvariant (mem : Mem) (v R : Nat) (x : BitVec 32)
    (ws : List Nat) : Prop :=
  x.toNat ≤ R / 19 ∧ R % 19 ≠ 0 ∧ stkBnLimbs mem v ws ∧ ws.length = x.toNat

/-- The residual call exists exactly on the non-zero remainder: `nestSteps`
counts the chunk loop's `R / 19` calls and the residual one. -/
theorem nestSteps_of_residual {R : Nat} (h : R % 19 ≠ 0) :
    nestSteps 19 R = R / 19 + 1 := by
  simp [nestSteps, h]

/-- **The invariant is the count bound the cleanup store takes.**  Each of the
chunk loop's `R / 19` calls appends at most one limb, so the counter is inside
the nest's call count: `x ≤ nestSteps 19 R`, exactly the premise
`fbStkCounts_of_cleanup_end151` reads for `%78`. -/
theorem ingestChunkInvariant_count_le {mem : Mem} {v R : Nat} {x : BitVec 32}
    {ws : List Nat} (hinv : ingestChunkInvariant mem v R x ws) :
    x.toNat ≤ nestSteps 19 R := by
  unfold ingestChunkInvariant at hinv
  have hx := hinv.1
  unfold nestSteps
  split <;> omega

/-- **The residual drain's count tie, from the chunk loop's invariant.**  From
`x ≤ R / 19` the counter is at most `40`, so the block's sign extension and
`≤ 95` bound hold; `bus520_count_read` then leaves the extended limb list and
the bumped count `x + 1`, which is at most `nestSteps 19 R` because the residual
call is the nest's last.  The conclusion is `stkBnLimbs` at the new list and
`ingestCountTie`, the premise the epilogue's `fbStkCounts_of_ties` consumes. -/
theorem bus520_count_tie {calls : Calls} {env : Env} {s : State}
    {x : BitVec 32} {c : BitVec 128} {v R : Nat} {ws : List Nat}
    (hpc : s.pc = "while.body.us.i520.i.i")
    (hx : lookupName env "%78" = some (.int 32 x))
    (hc : lookupName env "%carry.0.lcssa.i518.i.i" = some (.int 128 c))
    (hv : lookupName env "%v.i.i" = some (.ptr v))
    (hn : lookupName env "%n.i.i.i" = some (.ptr (v + stkCountOffset)))
    (hR : R ≤ 768)
    (hwords : ∀ z ∈ ws, z < 2 ^ 64)
    (hinv : ingestChunkInvariant s.mem v R x ws) :
    ∃ (s1 s2 : State),
      step calls numFastBody (stateAt env s) = .jump s1
      ∧ step calls numFastBody s1 = .jump s2
      ∧ stkBnLimbs s2.mem v (ws ++ [(BitVec.ofNat 64 (c.toNat % 2 ^ 64)).toNat])
      ∧ ingestCountTie s2.mem v R := by
  unfold ingestChunkInvariant at hinv
  obtain ⟨hxdiv, hres, hbl, hlen⟩ := hinv
  have hx40 : x.toNat ≤ 40 := by
    have hdiv : R / 19 ≤ 40 := by omega
    omega
  have hmsb : x.msb = false := msb32_false_of_lt (by omega : x.toNat < 2 ^ 31)
  have hpos : x.toNat < 2 ^ 63 := by omega
  have hxle : x.toNat ≤ 95 := by omega
  have hlimbs : stkLimbs s.mem v x.toNat = some ws := by
    rw [← hlen]
    exact hbl.2
  obtain ⟨s1, s2, h1, h2, hcnt, hlimbs'⟩ :=
    bus520_count_read (calls := calls) hpc hx hc hv hn hmsb hpos hxle hwords hlimbs
  have hlen' : (ws ++ [(BitVec.ofNat 64 (c.toNat % 2 ^ 64)).toNat]).length
      = x.toNat + 1 := by
    simp only [List.length_append, List.length_singleton, hlen]
  have hx1 : x.toNat + 1 ≤ nestSteps 19 R := by
    rw [nestSteps_of_residual hres]
    omega
  refine ⟨s1, s2, h1, h2, ⟨?_, ?_⟩, ⟨x.toNat + 1, hcnt, hx1⟩⟩
  · rw [hlen']
    exact hcnt
  · rw [hlen']
    exact hlimbs'

/-- **The cleanup exit, from the same invariant.**  `fbStkCounts_of_cleanup_end151`
takes `%78 ≤ nestSteps 19 R`; `ingestChunkInvariant_count_le` supplies it, so
the cleanup path reaches `fbStkCounts` with no count bound carried separately.
This is the residual drain's sibling path: the invariant is what both stores
read. -/
theorem fbStkCounts_of_chunkEnd151 {calls : Calls} {env : Env} {s : State}
    {x : BitVec 32} {c : BitVec 32} {st : BitVec 32} {v R : Nat} {ws : List Nat}
    (hx : lookupName env "%78" = some (.int 32 x))
    (hn : lookupName env "%n.i.i.i" = some (.ptr (v + stkCountOffset)))
    (hc : lookupName env "%cn.1.i.i" = some (.int 32 c))
    (hv : lookupName env "%v.i.i" = some (.ptr v))
    (hst : lookupName env "%sticky.0714.i.i" = some (.int 32 st))
    (hR : R ≤ 768) (hinv : ingestChunkInvariant s.mem v R x ws) :
    ∃ (env1 : Env) (s1 : State) (env2 : Env) (s2 : State),
      denoteCode calls cleanupInstrs (stateAt env s) = some (stateAt env1 s1) ∧
      denoteCode calls end151Instrs (stateAt env1 s1) = some (stateAt env2 s2) ∧
      fbStkCounts s2.mem v :=
  fbStkCounts_of_cleanup_end151 hx hn hc hv hst hR (ingestChunkInvariant_count_le hinv)

/-! ### Axiom footprints

The readback and the tie from the invariant, pinned so the build checks them. -/

/-- info: 'LeanLLVM.Refinement.NumFastIngestAppend.bus520_count_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bus520_count_read

/-- info: 'LeanLLVM.Refinement.NumFastIngestAppend.bus520_count_tie' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bus520_count_tie

/-- info: 'LeanLLVM.Refinement.NumFastIngestAppend.fbStkCounts_of_chunkEnd151' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fbStkCounts_of_chunkEnd151

end NumFastIngestAppend

end LeanLLVM.Refinement
