/-
The significand fold's append, and the count its spill leaves behind.

`stage2.c`'s `to_double` folds the residual scale into the significand with
`stk_mul_u64(&m, NUMF_EL1_P10[k])`: the block `for.body.i.i611.i.i` multiplies
the `%116` live limbs by the table row and keeps each low word, carrying the
high half; `while.cond.preheader.i.i622.i.i` then asks whether the last `i128`
carry still fits a limb, and `while.body.us.i.i624.i.i` appends it at
`%v + 8 * %116`, bumps the counter into `%inc12.us.i.i626.i.i`, and writes the
bumped word to the count's cell `%n.i.i.i`.  This is the fold's own append, not
the ingest's: the ingest's two drains (`while.body.us.i.i.i`,
`while.body.us.i520.i.i`) truncate an `i128` carry and leave the counter's cell
to the block that follows, while this block stores the count itself.

The count's other write is the one outside the append: `while.end190.i.i`, the
loop exit the non-negative route reaches through `while.body187.i.i` and
`stk_mul_u64.exit605.i.i`, spills the `%116` `phi` — the count the nest already
holds — at the same cell before it tests the residual.  That store is not an
append: it writes a word the limbs' length already is, so it leaves the limbs
untouched.  The block's own `denoteCode`, its two `phi`s and its branch are
`JsonStage2NumFastToDouble`'s (`end190_denote`, `end190_step_rung`,
`end190_step_end`, at the block's pin); what was owed is the readback of the
cell that store writes, which is `end190_readback` below, and the tie it carries
(`end190_spill_tie`).

`bus624_denote` and `bus624_step` are new: the block has no statement in
`JsonStage2NumFastToDouble`, whose neighbouring `bus557` lane states the power's
same append.  Both appends store four bytes at the count's cell and eight at
`%v + 8 * n`; the readbacks compose the two stores with the model's
`stkCount`/`stkLimbs` reads (`stkCount_writeCount_bytes`,
`stkLimbs_writeBytes_append`, `stkLimbs_writeBytes_above`), so each is an
equation on the cell and the limb list rather than a memory shape.

There is no `sorry`, `admit` or `native_decide` below.
-/
import LeanLLVM.Refinement.JsonStage2NumFastIngestAppend

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
open LeanLLVM.Refinement.NumFastIngestAppend

namespace NumFastFoldAppend

/-! ### The fold's append: `while.body.us.i.i624.i.i`

`%116` is the limb counter, `%wide.trip.count.i.i610.i.i` its zero extension
(the `gep` index), `%shr.i.i619.i.i.lcssa.off0` the last `i128` carry's high
word, and `%n.i.i.i` the count's cell at `%v + 0x300`.  The block stores the
carry at `%v + 8 * %116`, then bumps the counter and stores it. -/

/-- The block's instructions. -/
def bus624Instrs : List Instr :=
  [Instr.binop "%inc12.us.i.i626.i.i" (BinOp.add) 32 (Operand.reg "%116")
     (Operand.imm (Const.int 32 0x0000000000000001#32)),
   Instr.gep "%arrayidx14.us.i.i627.i.i" (Ty.int 64) (Operand.reg "%v.i.i")
     (Operand.reg "%wide.trip.count.i.i610.i.i"),
   Instr.store (Ty.int 64) (Operand.reg "%shr.i.i619.i.i.lcssa.off0")
     (Operand.reg "%arrayidx14.us.i.i627.i.i"),
   Instr.store (Ty.int 32) (Operand.reg "%inc12.us.i.i626.i.i")
     (Operand.reg "%n.i.i.i")]

theorem bus624_find :
    numFastBody.findBlock "while.body.us.i.i624.i.i" =
      some ⟨"while.body.us.i.i624.i.i", bus624Instrs, Term.br "if.end195.i.i"⟩ := by
  simpa only [bus624Instrs] using numFast_findBlock_while_body_us_i_i624_i_i

/-- The environment the block leaves: the address, the bumped counter, and the
incoming cells behind them. -/
def bus624Env (env : Env) (v : Nat) (x : BitVec 32) : Env :=
  ("%arrayidx14.us.i.i627.i.i", .ptr (v + x.toNat * 8)) ::
  ("%inc12.us.i.i626.i.i", .int 32 (x + 0x0000000000000001#32)) :: env

/-- The memory the block leaves: the carry at `%v + 8 * %116`, then the bumped
count at its cell. -/
def bus624Mem (mem : Mem) (v : Nat) (x : BitVec 32) (c : BitVec 64) : Mem :=
  writeBytes (writeBytes mem (v + x.toNat * 8) (natToBytes c.toNat 8))
    (v + stkCountOffset) (natToBytes (x + 0x0000000000000001#32).toNat 4)

/-- The block's chain: the bump, the address, the carry's store at the count's
index, and the bumped count at its cell. -/
theorem bus624_denote {calls : Calls} {env : Env} {s : State}
    {x : BitVec 32} {c wv : BitVec 64} {v : Nat}
    (hx : lookupName env "%116" = some (.int 32 x))
    (hv : lookupName env "%v.i.i" = some (.ptr v))
    (hw : lookupName env "%wide.trip.count.i.i610.i.i" = some (.int 64 wv))
    (hwv : (wv.signExtend 64).toNat = x.toNat) (hpos : x.toNat < 2 ^ 63)
    (hc : lookupName env "%shr.i.i619.i.i.lcssa.off0" = some (.int 64 c))
    (hn : lookupName env "%n.i.i.i" = some (.ptr (v + stkCountOffset))) :
    denoteCode calls bus624Instrs (stateAt env s) =
      some (stateAt (bus624Env env v x) { s with mem := bus624Mem s.mem v x c }) := by
  unfold bus624Instrs
  rw [NumFastToDouble.denoteCode_add_imm_w calls env s
    "%inc12.us.i.i626.i.i" "%116" 32 hx]
  rw [NumFastTier1.denoteCode_gep64_reg calls
    (("%inc12.us.i.i626.i.i", .int 32 (x + 0x0000000000000001#32)) :: env) s
    "%arrayidx14.us.i.i627.i.i" "%v.i.i" "%wide.trip.count.i.i610.i.i"
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact hv)
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact hw)
    (by rw [hwv]; exact hpos)]
  rw [hwv]
  rw [denoteCode_store64 calls
    (("%arrayidx14.us.i.i627.i.i", .ptr (v + x.toNat * 8)) ::
      ("%inc12.us.i.i626.i.i", .int 32 (x + 0x0000000000000001#32)) :: env) s
    "%shr.i.i619.i.i.lcssa.off0" "%arrayidx14.us.i.i627.i.i"
    (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact hc)
    (lookupName_cons_self ..)]
  rw [NumFastToDouble.denoteCode_store32 calls
    (("%arrayidx14.us.i.i627.i.i", .ptr (v + x.toNat * 8)) ::
      ("%inc12.us.i.i626.i.i", .int 32 (x + 0x0000000000000001#32)) :: env)
    { s with mem := writeBytes s.mem (v + x.toNat * 8) (natToBytes c.toNat 8) }
    "%inc12.us.i.i626.i.i" "%n.i.i.i"
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact lookupName_cons_self ..)
    (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact hn)]
  simp only [denoteCode_nil, bus624Env, bus624Mem, stateAt]

/-- **The append's step**, into the join `if.end195.i.i`. -/
theorem bus624_step {calls : Calls} {env : Env} {s : State}
    {x : BitVec 32} {c wv : BitVec 64} {v : Nat}
    (hpc : s.pc = "while.body.us.i.i624.i.i")
    (hx : lookupName env "%116" = some (.int 32 x))
    (hv : lookupName env "%v.i.i" = some (.ptr v))
    (hw : lookupName env "%wide.trip.count.i.i610.i.i" = some (.int 64 wv))
    (hwv : (wv.signExtend 64).toNat = x.toNat) (hpos : x.toNat < 2 ^ 63)
    (hc : lookupName env "%shr.i.i619.i.i.lcssa.off0" = some (.int 64 c))
    (hn : lookupName env "%n.i.i.i" = some (.ptr (v + stkCountOffset))) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (bus624Env env v x)
        { s with mem := bus624Mem s.mem v x c,
                 pc := "if.end195.i.i", pre := some "while.body.us.i.i624.i.i" }) := by
  refine numFast_step_at (s' := stateAt (bus624Env env v x)
      { s with mem := bus624Mem s.mem v x c })
    (b := ⟨"while.body.us.i.i624.i.i", bus624Instrs, Term.br "if.end195.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using bus624_find
  · simpa only [stateAt] using bus624_denote (calls := calls) hx hv hw hwv hpos hc hn
  · simp only [execTerm, stateAt, hpc]

/-- **The append's readback.**  From the `%116` limbs the count names, the
block's limb store leaves `%116 + 1` — the old list plus the carry's high word —
and its second store puts the bumped word in the count's cell, so the cell holds
exactly the list's length.  The index `%wide.trip.count.i.i610.i.i` is the
counter's zero extension, which is the hypothesis `hwv`; `hxle` is the room the
`StkBn` has left for the appended limb. -/
theorem bus624_readback {calls : Calls} {env : Env} {s : State}
    {x : BitVec 32} {c wv : BitVec 64} {v : Nat} {ws : List Nat}
    (hx : lookupName env "%116" = some (.int 32 x))
    (hv : lookupName env "%v.i.i" = some (.ptr v))
    (hw : lookupName env "%wide.trip.count.i.i610.i.i" = some (.int 64 wv))
    (hwv : (wv.signExtend 64).toNat = x.toNat) (hpos : x.toNat < 2 ^ 63)
    (hc : lookupName env "%shr.i.i619.i.i.lcssa.off0" = some (.int 64 c))
    (hn : lookupName env "%n.i.i.i" = some (.ptr (v + stkCountOffset)))
    (hxle : x.toNat ≤ 95)
    (hlimbs : stkLimbs s.mem v x.toNat = some ws) :
    ∃ (env' : Env) (s' : State),
      denoteCode calls bus624Instrs (stateAt env s) = some (stateAt env' s')
      ∧ stkLimbs s'.mem v (x.toNat + 1) = some (ws ++ [c.toNat])
      ∧ stkCount s'.mem v = some (x.toNat + 1) := by
  have hinc : (x + 0x0000000000000001#32).toNat = x.toNat + 1 := inc32_toNat x hxle
  let s' : State := { s with mem := bus624Mem s.mem v x c }
  refine ⟨bus624Env env v x, s',
    bus624_denote (calls := calls) hx hv hw hwv hpos hc hn, ?_, ?_⟩
  · show stkLimbs (bus624Mem s.mem v x c) v (x.toNat + 1)
      = some (ws ++ [c.toNat])
    unfold bus624Mem
    rw [stkLimbs_writeBytes_above
      (writeBytes s.mem (v + x.toNat * 8) (natToBytes c.toNat 8))
      v (x.toNat + 1) (v + stkCountOffset) _
      (by unfold stkCountOffset; omega)]
    rw [show v + x.toNat * 8 = v + 8 * x.toNat from by rw [Nat.mul_comm]]
    exact stkLimbs_writeBytes_append s.mem v x.toNat c ws hlimbs
  · show stkCount (bus624Mem s.mem v x c) v = some (x.toNat + 1)
    unfold bus624Mem
    rw [hinc]
    exact stkCount_writeCount_bytes
      (writeBytes s.mem (v + x.toNat * 8) (natToBytes c.toNat 8))
      v (x.toNat + 1) (by omega)

/-! ### The fold's spill: `while.end190.i.i`

The block's `%116` `phi` is the count the nest hands its exit, and the store
writes that word at `%n.i.i.i` before the residual test and the branch.  The
block's `denoteCode` and its two edges are `JsonStage2NumFastToDouble`'s; the
readback below is the cell the store leaves. -/

/-- **The spill's readback.**  The block writes the count the `%116` `phi`
selects at the count's cell, and its four bytes are above every limb read the
count names, so the limbs the pre-state held are the limbs the post-state reads.
The `phi`-selected values are `end190_denote`'s hypotheses; `hn96` is the room
the `StkBn` gives the limbs the store must not disturb. -/
theorem end190_readback {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 : Operand} {c : BitVec 32} {kk : BitVec 64}
    {v n : Nat} {ws : List Nat}
    (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("while.cond184.preheader.i.i", (Operand.reg "%n.i.promoted751.i.i")),
       ("stk_mul_u64.exit605.i.i", (Operand.reg "%115"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 32 c))
    (hop2 : phiIncoming pre
      [("while.cond184.preheader.i.i", (Operand.reg "%add108.i.i")),
       ("stk_mul_u64.exit605.i.i", (Operand.reg "%sub189.i.i"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 64 kk))
    (hn : lookupName env "%n.i.i.i" = some (.ptr (v + stkCountOffset)))
    (hn96 : n ≤ 96)
    (hlimbs : stkLimbs s.mem v n = some ws) :
    ∃ (env' : Env) (s' : State),
      denoteCode calls end190Block (stateAt env s) = some (stateAt env' s')
      ∧ stkCount s'.mem v = some c.toNat
      ∧ stkLimbs s'.mem v n = some ws := by
  refine ⟨end190Env env c kk, end190State env c kk (v + stkCountOffset) s,
    ?_, ?_, ?_⟩
  · rw [show stateAt (end190Env env c kk)
        (end190State env c kk (v + stkCountOffset) s)
        = end190State env c kk (v + stkCountOffset) s from rfl]
    exact end190_denote hpre hop1 hov1 hop2 hov2 hn
  · show stkCount (writeBytes s.mem (v + stkCountOffset) (natToBytes c.toNat 4)) v
      = some c.toNat
    exact stkCount_writeCount_bytes s.mem v c.toNat c.isLt
  · show stkLimbs (writeBytes s.mem (v + stkCountOffset) (natToBytes c.toNat 4)) v n
      = some ws
    rw [stkLimbs_writeBytes_above s.mem v n (v + stkCountOffset) _
      (by unfold stkCountOffset; omega)]
    exact hlimbs

/-- **The spill is the limbs' own length.**  When the pre-state's count names
the limbs, the word the block spills is that list's length, so the block leaves
`stkBnLimbs` — the count and the limbs agree.  This is the tie the exits that
follow read: the store is idempotent with respect to the limbs and writes the
count they already have. -/
theorem end190_spill_tie {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 : Operand} {c : BitVec 32} {kk : BitVec 64}
    {v : Nat} {ws : List Nat}
    (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("while.cond184.preheader.i.i", (Operand.reg "%n.i.promoted751.i.i")),
       ("stk_mul_u64.exit605.i.i", (Operand.reg "%115"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 32 c))
    (hop2 : phiIncoming pre
      [("while.cond184.preheader.i.i", (Operand.reg "%add108.i.i")),
       ("stk_mul_u64.exit605.i.i", (Operand.reg "%sub189.i.i"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 64 kk))
    (hn : lookupName env "%n.i.i.i" = some (.ptr (v + stkCountOffset)))
    (hc96 : c.toNat ≤ 96)
    (hlimbs : stkLimbs s.mem v c.toNat = some ws) :
    ∃ (env' : Env) (s' : State),
      denoteCode calls end190Block (stateAt env s) = some (stateAt env' s')
      ∧ stkBnLimbs s'.mem v ws := by
  obtain ⟨env', s', hden, hcnt, hlimbs'⟩ :=
    end190_readback (calls := calls) hpre hop1 hov1 hop2 hov2 hn hc96 hlimbs
  refine ⟨env', s', hden, ?_, ?_⟩
  · rw [stkLimbs_length hlimbs]; exact hcnt
  · rw [stkLimbs_length hlimbs]; exact hlimbs'

/-! ### Axiom footprints

The two readbacks and the tie, pinned so the build checks them. -/

/-- info: 'LeanLLVM.Refinement.NumFastFoldAppend.bus624_readback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bus624_readback

/-- info: 'LeanLLVM.Refinement.NumFastFoldAppend.end190_readback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms end190_readback

/-- info: 'LeanLLVM.Refinement.NumFastFoldAppend.end190_spill_tie' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms end190_spill_tie

end NumFastFoldAppend

end LeanLLVM.Refinement
