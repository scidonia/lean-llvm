/-
The exact power nest's append: `while.body.us.i.i557.i.i`.

`stage2.c`'s exact power multiplies the significand's `StkBn` at `%v + 0x308` by
`10 ^ 19` once per nineteen units of the exponent; the loop's last `i128` carry,
when it reaches `2 ^ 64`, is spilled as one more limb.  The block truncates the
high word into `%shr.i.i552.i.i.lcssa.off0`, stores it at `%pow + 8 * n`, bumps
the count `%92` into `%inc12.us.i.i559.i.i`, and writes that word to the power's
count cell `%n.i539.i.i` — `%v + 0x608`, the cell `stkCount mem (v + 776)`
reads.  Unlike the ingest's two drains, the block writes the count itself, so
its readback is the tie at the power's cell without a following store.

`JsonStage2NumFastToDouble` states the block's instruction list, environment,
`denoteCode` and step in the to_double idiom; this module states the same four
at the block's own pin for the counting lane, and proves what the append does to
what `stkLimbs` and `stkCount` read: the limb list grows by the carry's low
word at the index the count names, and the count's cell holds that list's
length.  The two registers the block reads for the same number — the counter
`%92` and the index `%wide.trip.count.i.i543.i.i` — are tied by hypothesis
(`hcnt`); that equality is the loop's invariant at the append, not a fact the
block's own instructions supply.

There is no `sorry`, `admit` or `native_decide` below.
-/
import LeanLLVM.Refinement.JsonStage2NumFastIngestAppend

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.NumFastToDouble
open LeanLLVM.Refinement.NumFastProducerCount
open LeanLLVM.Refinement.NumFastIngestAppend

namespace NumFastPowAppend

/-! ### The counter's arithmetic

The block bumps a 32-bit counter, and the readback reads the bumped word at its
value.  The guard's `≤ 95` is the top of the count's range at this append. -/

/-- The bump's own word: `x + 1` at 32 bits, read at its value. -/
theorem inc32_toNat' (x : BitVec 32) (hx : x.toNat ≤ 95) :
    (x + 0x00000001#32).toNat = x.toNat + 1 := by
  have h1 : (0x00000001#32 : BitVec 32).toNat = 1 := by decide
  rw [BitVec.toNat_add_of_lt (by
    rw [h1, show (2 : Nat) ^ 32 = 4294967296 from by decide]; omega), h1]

/-! ### The block, at its pin

`%pow.i.i` is the power's `StkBn` limb array (`%v + 0x308`, one `StkBn` past the
significand's), `%n.i539.i.i` its count cell (`%v + 0x608`), and the index is
the count `%92` sign-extended by the widen at the nest's head. -/

/-- The block's instructions. -/
def bus557Instrs : List Instr :=
  [Instr.binop "%inc12.us.i.i559.i.i" (BinOp.add) 32 (Operand.reg "%92")
     (Operand.imm (Const.int 32 0x00000001#32)),
   Instr.gep "%arrayidx14.us.i.i560.i.i" (Ty.int 64) (Operand.reg "%pow.i.i")
     (Operand.reg "%wide.trip.count.i.i543.i.i"),
   Instr.store (Ty.int 64) (Operand.reg "%shr.i.i552.i.i.lcssa.off0")
     (Operand.reg "%arrayidx14.us.i.i560.i.i"),
   Instr.store (Ty.int 32) (Operand.reg "%inc12.us.i.i559.i.i")
     (Operand.reg "%n.i539.i.i")]

theorem bus557_find :
    numFastBody.findBlock "while.body.us.i.i557.i.i" =
      some ⟨"while.body.us.i.i557.i.i", bus557Instrs, Term.br "if.end198.i.i"⟩ := by
  simpa only [bus557Instrs] using numFast_findBlock_while_body_us_i_i557_i_i

/-- The environment the block leaves: the address, the bumped counter, and the
incoming cells.  The stores bind nothing of their own. -/
def bus557Env (env : Env) (pow : Nat) (w : Nat) (c : BitVec 32) : Env :=
  ("%arrayidx14.us.i.i560.i.i", .ptr (pow + w * 8)) ::
  ("%inc12.us.i.i559.i.i", .int 32 (c + 0x00000001#32)) :: env

theorem bus557_denote {calls : Calls} {env : Env} {s : State}
    {c : BitVec 32} {pow w : Nat} {wv off : BitVec 64} {n : Nat}
    (h92 : lookupName env "%92" = some (.int 32 c))
    (hpow : lookupName env "%pow.i.i" = some (.ptr pow))
    (hw : lookupName env "%wide.trip.count.i.i543.i.i" = some (.int 64 wv))
    (hwv : (wv.signExtend 64).toNat = w) (hpos : w < 2 ^ 63)
    (hoff : lookupName env "%shr.i.i552.i.i.lcssa.off0" = some (.int 64 off))
    (hn : lookupName env "%n.i539.i.i" = some (.ptr n)) :
    denoteCode calls bus557Instrs (stateAt env s) =
      some (stateAt (bus557Env env pow w c)
        { s with mem := writeBytes (writeBytes s.mem (pow + w * 8)
            (natToBytes off.toNat 8)) n (natToBytes (c + 0x00000001#32).toNat 4) }) := by
  unfold bus557Instrs
  rw [JsonScanLane.denoteCode_add_imm_w calls env s "%inc12.us.i.i559.i.i" "%92" 32 h92]
  rw [NumFastTier1.denoteCode_gep64_reg calls
    (("%inc12.us.i.i559.i.i", .int 32 (c + 0x00000001#32)) :: env) s
    "%arrayidx14.us.i.i560.i.i" "%pow.i.i" "%wide.trip.count.i.i543.i.i"
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact hpow)
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact hw) (by rw [hwv]; exact hpos)]
  rw [hwv]
  rw [denoteCode_store64 calls
    (("%arrayidx14.us.i.i560.i.i", .ptr (pow + w * 8)) ::
      ("%inc12.us.i.i559.i.i", .int 32 (c + 0x00000001#32)) :: env) s
    "%shr.i.i552.i.i.lcssa.off0" "%arrayidx14.us.i.i560.i.i"
    (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact hoff)
    (lookupName_cons_self ..)]
  rw [NumFastToDouble.denoteCode_store32 calls
    (("%arrayidx14.us.i.i560.i.i", .ptr (pow + w * 8)) ::
      ("%inc12.us.i.i559.i.i", .int 32 (c + 0x00000001#32)) :: env)
    { s with mem := writeBytes s.mem (pow + w * 8) (natToBytes off.toNat 8) }
    "%inc12.us.i.i559.i.i" "%n.i539.i.i"
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact lookupName_cons_self ..)
    (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact hn)]
  simp only [denoteCode_nil, bus557Env, stateAt]

/-- **The append's step**, out of `while.body.us.i.i557.i.i` into the merge
`if.end198.i.i`. -/
theorem bus557_step {calls : Calls} {env : Env} {s : State}
    {c : BitVec 32} {pow w : Nat} {wv off : BitVec 64} {n : Nat}
    (hpc : s.pc = "while.body.us.i.i557.i.i")
    (h92 : lookupName env "%92" = some (.int 32 c))
    (hpow : lookupName env "%pow.i.i" = some (.ptr pow))
    (hw : lookupName env "%wide.trip.count.i.i543.i.i" = some (.int 64 wv))
    (hwv : (wv.signExtend 64).toNat = w) (hpos : w < 2 ^ 63)
    (hoff : lookupName env "%shr.i.i552.i.i.lcssa.off0" = some (.int 64 off))
    (hn : lookupName env "%n.i539.i.i" = some (.ptr n)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (bus557Env env pow w c)
        { s with mem := writeBytes (writeBytes s.mem (pow + w * 8)
            (natToBytes off.toNat 8)) n (natToBytes (c + 0x00000001#32).toNat 4),
                 pc := "if.end198.i.i", pre := some "while.body.us.i.i557.i.i" }) := by
  refine numFast_step_at (s' := stateAt (bus557Env env pow w c)
      { s with mem := writeBytes (writeBytes s.mem (pow + w * 8)
          (natToBytes off.toNat 8)) n (natToBytes (c + 0x00000001#32).toNat 4) })
    (b := ⟨"while.body.us.i.i557.i.i", bus557Instrs, Term.br "if.end198.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using bus557_find
  · simpa only [stateAt] using bus557_denote h92 hpow hw hwv hpos hoff hn
  · simp only [execTerm, stateAt, hpc]

/-! ### The readback

The power's `StkBn` starts at `v + 776` (`%v + 0x308`) and its count cell
`%n.i539.i.i` at `v + 776 + 768` (`%v + 0x608`).  The store at `%pow + 8 * n`
lands above the `n` limbs `stkLimbs` reads and below the count's cell when
`n ≤ 95`, so the limb list grows by exactly the spilled word and the count's
cell holds the bumped counter. -/

/-- **The append's readback.**  From the `n` limbs the power's count names, the
block leaves `n + 1` — the old list plus the spilled high word — and its count
cell holds that list's length.  The tying hypothesis is `hcnt`: the counter the
block bumps and the index it stores at are the same number. -/
theorem bus557_readback {calls : Calls} {env : Env} {s : State}
    {c : BitVec 32} {v w : Nat} {wv off : BitVec 64} {ws : List Nat}
    (h92 : lookupName env "%92" = some (.int 32 c))
    (hpow : lookupName env "%pow.i.i" = some (.ptr (v + 776)))
    (hw : lookupName env "%wide.trip.count.i.i543.i.i" = some (.int 64 wv))
    (hwv : (wv.signExtend 64).toNat = w) (hpos : w < 2 ^ 63)
    (hoff : lookupName env "%shr.i.i552.i.i.lcssa.off0" = some (.int 64 off))
    (hn : lookupName env "%n.i539.i.i" = some (.ptr (v + 776 + stkCountOffset)))
    (hcnt : c.toNat = w) (hcle : c.toNat ≤ 95)
    (hlimbs : stkLimbs s.mem (v + 776) w = some ws) :
    ∃ (env' : Env) (s' : State),
      denoteCode calls bus557Instrs (stateAt env s) = some (stateAt env' s')
      ∧ lookupName env' "%inc12.us.i.i559.i.i"
          = some (.int 32 (c + 0x00000001#32))
      ∧ stkLimbs s'.mem (v + 776) (w + 1) = some (ws ++ [off.toNat])
      ∧ stkCount s'.mem (v + 776) = some (w + 1) := by
  let m1 : Mem := writeBytes s.mem ((v + 776) + w * 8) (natToBytes off.toNat 8)
  let m2 : Mem := writeBytes m1 ((v + 776) + stkCountOffset)
    (natToBytes (c + 0x00000001#32).toNat 4)
  let s' : State := { s with mem := m2 }
  have hlen : ws.length = w := stkLimbs_length hlimbs
  have hlen' : (ws ++ [off.toNat]).length = w + 1 := by
    simp only [List.length_append, List.length_singleton, hlen]
  have h96 : (ws ++ [off.toNat]).length ≤ 96 := by
    rw [hlen']; omega
  have hinc : (c + 0x00000001#32).toNat = c.toNat + 1 := inc32_toNat' c hcle
  refine ⟨bus557Env env (v + 776) w c, s', ?_, ?_, ?_, ?_⟩
  · simpa only [s', m1, m2] using
      bus557_denote (calls := calls) h92 hpow hw hwv hpos hoff hn
  · simp only [bus557Env]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact lookupName_cons_self ..
  · have happ : stkLimbs m1 (v + 776) (w + 1) = some (ws ++ [off.toNat]) := by
      have h := stkLimbs_writeBytes_append s.mem (v + 776) w off ws hlimbs
      have haddr : (v + 776) + w * 8 = (v + 776) + 8 * w := by
        simp only [Nat.mul_comm w 8]
      simpa only [m1, haddr] using h
    have hframe := stkLimbs_writeCount_frame m1 (v + 776) (ws ++ [off.toNat])
      (by rw [hlen']; exact happ) h96
    show stkLimbs m2 (v + 776) (w + 1) = some (ws ++ [off.toNat])
    simp only [m2]
    rw [show (c + 0x00000001#32).toNat = (ws ++ [off.toNat]).length from by
      rw [hinc, hlen']; omega]
    rw [← hlen']
    exact hframe
  · have hcount : stkCount m2 (v + 776) = some (w + 1) := by
      have hk : (c + 0x00000001#32).toNat < 2 ^ 32 := by
        rw [hinc, show (2 : Nat) ^ 32 = 4294967296 from by decide]
        omega
      show stkCount m2 (v + 776) = some (w + 1)
      simp only [m2]
      rw [stkCount_writeCount_bytes m1 (v + 776) ((c + 0x00000001#32).toNat) hk]
      simp only [hinc, hcnt]
    exact hcount

/-- **The append leaves the power's limbs and count together.**  The readback,
read as the invariant the count tie consumes: the power's count cell names the
list the append wrote, limb for limb. -/
theorem bus557_bnLimbs {calls : Calls} {env : Env} {s : State}
    {c : BitVec 32} {v w : Nat} {wv off : BitVec 64} {ws : List Nat}
    (h92 : lookupName env "%92" = some (.int 32 c))
    (hpow : lookupName env "%pow.i.i" = some (.ptr (v + 776)))
    (hw : lookupName env "%wide.trip.count.i.i543.i.i" = some (.int 64 wv))
    (hwv : (wv.signExtend 64).toNat = w) (hpos : w < 2 ^ 63)
    (hoff : lookupName env "%shr.i.i552.i.i.lcssa.off0" = some (.int 64 off))
    (hn : lookupName env "%n.i539.i.i" = some (.ptr (v + 776 + stkCountOffset)))
    (hcnt : c.toNat = w) (hcle : c.toNat ≤ 95)
    (hlimbs : stkLimbs s.mem (v + 776) w = some ws) :
    ∃ (env' : Env) (s' : State),
      denoteCode calls bus557Instrs (stateAt env s) = some (stateAt env' s')
      ∧ stkBnLimbs s'.mem (v + 776) (ws ++ [off.toNat]) := by
  obtain ⟨env', s', hd, _, hl, hc⟩ :=
    bus557_readback (calls := calls) h92 hpow hw hwv hpos hoff hn hcnt hcle hlimbs
  have hlen' : (ws ++ [off.toNat]).length = w + 1 := by
    simp only [List.length_append, List.length_singleton, stkLimbs_length hlimbs]
  refine ⟨env', s', hd, ?_⟩
  unfold stkBnLimbs
  exact ⟨by rw [hlen']; exact hc, by rw [hlen']; exact hl⟩

/-! ### Axiom footprints

The readback and the invariant it feeds, pinned so the build checks them. -/

/-- info: 'LeanLLVM.Refinement.NumFastPowAppend.bus557_readback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bus557_readback

/-- info: 'LeanLLVM.Refinement.NumFastPowAppend.bus557_bnLimbs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bus557_bnLimbs

end NumFastPowAppend

end LeanLLVM.Refinement
