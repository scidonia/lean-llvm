/-
The peel epilogue's exit, and where it actually leads.

`JsonStage2NumFastTier3Peel` takes the region from the peel's entry to
`while.cond.preheader.i.i577.i.i.epilog-lcssa` — the epilogue's exit — within
`2 + (k + 1)` control steps, carrying the table's base, the residue and the
shifted `i128` sum.  What that leaves open is where the exit goes.  It is not the
copy's entry: the copy's loop is `for.body87.i.i`, entered from
`for.body87.i.i.preheader`, whose only predecessor is `if.end83.i.i` — upstream of
the whole peel, in `to_double`'s digit copy.  The epilogue's exit reaches
`while.cond.preheader.i.i577.i.i`, whose two successors are the store block
`while.body.us.i.i579.i.i` and `stk_mul_u64.exit583.i.i`, and that block's own
successors are the outer `while.body173.i.i` (back to the peel nest) and
`while.end176.i.i` (on to `if.end198.i.i`, the ladder's start).

**The tie, and its cells.**  `t3PeelExit` and `t3PeelExitWord` name the residue
and the shifted sum, which the epilogue's last visit left, but not the two cells
the exit block reads: `%add4.i.i572.i.i.epil` (the last visit's own `i128` sum,
which the `phi` at `while.cond.preheader.i.i577.i.i` selects) and the outer loop's
counter.  They are hypotheses here rather than part of the peel's exit word,
because the epilogue *writes* `%add4.i.i572.i.i.epil` on its last visit — the
tie takes it from that visit's own state — while `%inc12.us.i.i581759761.i.i`,
`%k168.0762.i.i` and `%wide.trip.count.i.i565.i.i` are cells the peel never
writes, so any state the peel's induction leaves carries them.

**The run.**  `t3_tie_lcssa_step` is the exit block's own step — the truncation
and the branch — `t3_tie_cond_step_exit`/`_store` the test's two arms, and
`t3_tie_store_step` the store block's: `%inc12` advancing by one, the carry's high
word written at `%pow.i.i + 8 * %wide.trip.count`, and the branch to
`stk_mul_u64.exit583.i.i`.  `t3_peel_exit_tie` is the disjunction: the epilogue's
exit reaches `stk_mul_u64.exit583.i.i` in two control steps with the counter
unchanged and the memory untouched, or in three with both advanced, carrying the
cells the landing block reads.  The landing block's own four steps
(`t3_tie_exit_step_from_cond`/`_from_store`, and their `_end` forms at the outer
test's other bit) take it to `while.body173.i.i` or `while.end176.i.i` one step
further; they are stated so the caller continues from the tie's own word rather
than re-deriving the block.

**What the slice consumes.**  The outer loop over `%k168` (`while.body173.i.i` →
the peel nest) is not this module's: the tie's exit states are the two blocks its
simulation is entered at, with the residual and the carried sum the peel spent.
-/
import LeanLLVM.Refinement.JsonStage2NumFastTier3Peel

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.NumFastTier3
open LeanLLVM.Refinement.NumFastTier3Copy
open LeanLLVM.Refinement.NumFastTier3Peel

namespace NumFastTier3PeelTie

/-- A leading `phi` run of two members at the `stateAt` shape the `numFast` blocks
use: `JsonEntrySteps`' run is stated at its own `withEnv`, which is `stateAt`'s
body under another name. -/
theorem t3_denoteCode_phi2 (calls : Calls) (env : Env) (s : State)
    (d1 : String) (ty1 : Ty) (inc1 : List (String × Operand))
    (d2 : String) (ty2 : Ty) (inc2 : List (String × Operand))
    {p : String} {op1 : Operand} {v1 : Value} {op2 : Operand} {v2 : Value}
    (is : List Instr) (hpre : s.pre = some p)
    (hinc1 : phiIncoming p inc1 = some op1)
    (hop1 : evalOperand (stateAt env s) op1 = some v1)
    (hinc2 : phiIncoming p inc2 = some op2)
    (hop2 : evalOperand (stateAt env s) op2 = some v2)
    {hst : startsWithPhi is = false} :
    denoteCode calls (.phi d1 ty1 inc1 :: .phi d2 ty2 inc2 :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d2, v2) :: (d1, v1) :: env) s) := by
  simpa only [stateAt, JsonEntrySteps.withEnv] using
    JsonEntrySteps.denoteCode_phi2 calls env s d1 ty1 inc1 d2 ty2 inc2 is
      hpre hinc1 hop1 hinc2 hop2 (hst := hst)

/-- The `i128` bound the peel-exit test compares against: `2 ^ 64`. -/
def t3TieBound : BitVec 128 := 0x00000000000000010000000000000000#128

/-- `%d = icmp ult iN %a, <c>`, at any width. -/
theorem t3_step_icmp_ult_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w} (ha : lookupName env a = some (.int w x)) :
    evalInstr calls (stateAt env s) (.icmp d .ult w (.reg a) (.imm (.int w c))) =
      some (stateAt ((d, .int 1 (evalICmp .ult x c)) :: env) s) := by
  simpa only [stateAt, State.bind] using
    LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_icmp
      (calls := calls) (s := stateAt env s)
      (ha := evalOperand_reg_of env s a (.int w x) ha)
      (hb := evalOperand_lit_of (stateAt env s) w c)

theorem t3_denoteCode_icmp_ult_imm_w (calls : Calls) (env : Env) (s : State)
    (d a : String) (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) (is : List Instr) :
    denoteCode calls (.icmp d .ult w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp .ult x c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (t3_step_icmp_ult_imm_w calls env s d a w ha)]

/-! ### The epilogue's exit block

`while.cond.preheader.i.i577.i.i.epilog-lcssa` truncates the last visit's shifted
`i128` sum to its low word and branches to the test. -/

/-- The exit block's instructions, from its pin. -/
def t3TieLcssaInstrs : List Instr :=
  [Instr.trunc "%extract.t1098" 128 64 (Operand.reg "%shr.i.i574.i.i.epil")]

/-- The environment the exit block leaves. -/
def t3TieLcssaEnv (env : Env) (off : BitVec 64) : Env :=
  ("%extract.t1098", .int 64 off) :: env

/-- **The epilogue's exit block steps.**  The shifted sum's low word, then the
branch to the test. -/
theorem t3_tie_lcssa_step {calls : Calls} {env : Env} {s : State} {carry : BitVec 128}
    (hpc : s.pc = "while.cond.preheader.i.i577.i.i.epilog-lcssa")
    (hcarry : lookupName env "%shr.i.i574.i.i.epil" = some (.int 128 carry)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3TieLcssaEnv env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
        { s with pc := "while.cond.preheader.i.i577.i.i",
                 pre := some "while.cond.preheader.i.i577.i.i.epilog-lcssa" }) := by
  refine numFast_step_at (s' := stateAt (t3TieLcssaEnv env (BitVec.ofNat 64
      (carry.toNat % 2 ^ 64))) s)
    (b := ⟨"while.cond.preheader.i.i577.i.i.epilog-lcssa", t3TieLcssaInstrs,
      Term.br "while.cond.preheader.i.i577.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, t3TieLcssaInstrs]
      using numFast_findBlock_while_cond_preheader_i_i577_i_i_epilog_lcssa
  · simpa only [t3TieLcssaInstrs, t3TieLcssaEnv, denoteCode_nil] using
      denoteCode_cons_of calls (.trunc "%extract.t1098" 128 64
        (Operand.reg "%shr.i.i574.i.i.epil")) [] (stateAt env s)
        (stateAt (t3TieLcssaEnv env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) s)
        (step_trunc calls env s "%extract.t1098" "%shr.i.i574.i.i.epil" 128 64 hcarry)
  · simp only [execTerm, stateAt, hpc]

/-! ### The test: `while.cond.preheader.i.i577.i.i`

The two `phi`s select the epilogue's edge — the last visit's `i128` sum and the
truncated low word — and the block tests the sum against `2 ^ 64`.  The taken
arm is the store block, the refused arm `stk_mul_u64.exit583.i.i` directly, so
the block's own test is what decides whether the carry's high word is stored. -/

/-- The test block's instructions, from its pin. -/
def t3TieCondInstrs : List Instr :=
  [Instr.phi "%add4.i.i572.i.i.lcssa" (Ty.int 128)
     [("while.cond.preheader.i.i577.i.i.unr-lcssa", (Operand.reg "%add4.i.i572.i.i.lcssa.ph")),
      ("while.cond.preheader.i.i577.i.i.epilog-lcssa", (Operand.reg "%add4.i.i572.i.i.epil"))],
   Instr.phi "%shr.i.i574.i.i.lcssa.off0" (Ty.int 64)
     [("while.cond.preheader.i.i577.i.i.unr-lcssa",
        (Operand.reg "%shr.i.i574.i.i.lcssa.ph.off0")),
      ("while.cond.preheader.i.i577.i.i.epilog-lcssa", (Operand.reg "%extract.t1098"))],
   Instr.icmp "%tobool.not31.i.i578.i.i" (IPred.ult) 128
     (Operand.reg "%add4.i.i572.i.i.lcssa") (Operand.imm (Const.int 128 t3TieBound))]

theorem t3_tie_cond_pin :
    numFastBody.findBlock "while.cond.preheader.i.i577.i.i" =
      some ⟨"while.cond.preheader.i.i577.i.i", t3TieCondInstrs,
        Term.condbr (Operand.reg "%tobool.not31.i.i578.i.i")
          "stk_mul_u64.exit583.i.i" "while.body.us.i.i579.i.i"⟩ := by
  simpa only [t3TieCondInstrs, t3TieBound]
    using numFast_findBlock_while_cond_preheader_i_i577_i_i

/-- The environment the test leaves: the two carried cells and its bit. -/
def t3TieCondEnv (env : Env) (a : BitVec 128) (off : BitVec 64) : Env :=
  ("%tobool.not31.i.i578.i.i", .int 1 (evalICmp .ult a t3TieBound)) ::
  ("%shr.i.i574.i.i.lcssa.off0", .int 64 off) ::
  ("%add4.i.i572.i.i.lcssa", .int 128 a) :: env

/-- The test's chain at the epilogue's edge. -/
theorem t3_tie_cond_denote {calls : Calls} {env : Env} {s : State}
    {a : BitVec 128} {off : BitVec 64}
    (hpre : s.pre = some "while.cond.preheader.i.i577.i.i.epilog-lcssa")
    (ha : lookupName env "%add4.i.i572.i.i.epil" = some (.int 128 a))
    (hoff : lookupName env "%extract.t1098" = some (.int 64 off)) :
    denoteCode calls t3TieCondInstrs (stateAt env s) =
      some (stateAt (t3TieCondEnv env a off) s) := by
  unfold t3TieCondInstrs
  rw [t3_denoteCode_phi2 (calls := calls) (env := env) (s := s)
    "%add4.i.i572.i.i.lcssa" (Ty.int 128) _
    "%shr.i.i574.i.i.lcssa.off0" (Ty.int 64) _
    [Instr.icmp "%tobool.not31.i.i578.i.i" (IPred.ult) 128
      (Operand.reg "%add4.i.i572.i.i.lcssa") (Operand.imm (Const.int 128 t3TieBound))]
    hpre (by decide) (evalOperand_reg_of env s "%add4.i.i572.i.i.epil" (.int 128 a) ha)
    (by decide) (evalOperand_reg_of env s "%extract.t1098" (.int 64 off) hoff)
    (hst := by rfl)]
  rw [t3_denoteCode_icmp_ult_imm_w calls
    (("%shr.i.i574.i.i.lcssa.off0", .int 64 off) ::
      ("%add4.i.i572.i.i.lcssa", .int 128 a) :: env) s
    "%tobool.not31.i.i578.i.i" "%add4.i.i572.i.i.lcssa" 128
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact lookupName_cons_self ..) []]
  simp only [denoteCode_nil, t3TieCondEnv, t3TieBound, stateAt]

/-- **The test's step, refused: the residual fits one word.** -/
theorem t3_tie_cond_step_exit {calls : Calls} {env : Env} {s : State}
    {a : BitVec 128} {off : BitVec 64}
    (hpc : s.pc = "while.cond.preheader.i.i577.i.i")
    (hpre : s.pre = some "while.cond.preheader.i.i577.i.i.epilog-lcssa")
    (ha : lookupName env "%add4.i.i572.i.i.epil" = some (.int 128 a))
    (hoff : lookupName env "%extract.t1098" = some (.int 64 off))
    (hbit : evalICmp .ult a t3TieBound = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3TieCondEnv env a off)
        { s with pc := "stk_mul_u64.exit583.i.i",
                 pre := some "while.cond.preheader.i.i577.i.i" }) := by
  refine numFast_step_at (s' := stateAt (t3TieCondEnv env a off) s)
    (b := ⟨"while.cond.preheader.i.i577.i.i", t3TieCondInstrs,
      Term.condbr (Operand.reg "%tobool.not31.i.i578.i.i")
        "stk_mul_u64.exit583.i.i" "while.body.us.i.i579.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using t3_tie_cond_pin
  · simpa only [denoteCode_nil] using t3_tie_cond_denote hpre ha hoff
  · rw [numFast_execTerm_condbr_one (s := stateAt (t3TieCondEnv env a off) s) _
      "stk_mul_u64.exit583.i.i" "while.body.us.i.i579.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- **The test's step, taken: the carry's high word is stored.** -/
theorem t3_tie_cond_step_store {calls : Calls} {env : Env} {s : State}
    {a : BitVec 128} {off : BitVec 64}
    (hpc : s.pc = "while.cond.preheader.i.i577.i.i")
    (hpre : s.pre = some "while.cond.preheader.i.i577.i.i.epilog-lcssa")
    (ha : lookupName env "%add4.i.i572.i.i.epil" = some (.int 128 a))
    (hoff : lookupName env "%extract.t1098" = some (.int 64 off))
    (hbit : evalICmp .ult a t3TieBound = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3TieCondEnv env a off)
        { s with pc := "while.body.us.i.i579.i.i",
                 pre := some "while.cond.preheader.i.i577.i.i" }) := by
  refine numFast_step_at (s' := stateAt (t3TieCondEnv env a off) s)
    (b := ⟨"while.cond.preheader.i.i577.i.i", t3TieCondInstrs,
      Term.condbr (Operand.reg "%tobool.not31.i.i578.i.i")
        "stk_mul_u64.exit583.i.i" "while.body.us.i.i579.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using t3_tie_cond_pin
  · simpa only [denoteCode_nil] using t3_tie_cond_denote hpre ha hoff
  · rw [numFast_execTerm_condbr_zero (s := stateAt (t3TieCondEnv env a off) s) _
      "stk_mul_u64.exit583.i.i" "while.body.us.i.i579.i.i"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-! ### The store block: `while.body.us.i.i579.i.i`

The outer loop's counter advances, the carry's high word is stored at
`%pow.i.i + 8 * %wide.trip.count`, and the block branches to
`stk_mul_u64.exit583.i.i`. -/

/-- The store block's instructions, from its pin. -/
def t3TieStoreInstrs : List Instr :=
  [Instr.binop "%inc12.us.i.i581.i.i" (BinOp.add) 32
     (Operand.reg "%inc12.us.i.i581759761.i.i") (Operand.imm (Const.int 32 0x00000001#32)),
   Instr.gep "%arrayidx14.us.i.i582.i.i" (Ty.int 64) (Operand.reg "%pow.i.i")
     (Operand.reg "%wide.trip.count.i.i565.i.i"),
   Instr.store (Ty.int 64) (Operand.reg "%shr.i.i574.i.i.lcssa.off0")
     (Operand.reg "%arrayidx14.us.i.i582.i.i")]

theorem t3_tie_store_pin :
    numFastBody.findBlock "while.body.us.i.i579.i.i" =
      some ⟨"while.body.us.i.i579.i.i", t3TieStoreInstrs,
        Term.br "stk_mul_u64.exit583.i.i"⟩ := by
  simpa only [t3TieStoreInstrs] using numFast_findBlock_while_body_us_i_i579_i_i

/-- The environment the store block leaves. -/
def t3TieStoreEnv (env : Env) (k : BitVec 32) (pow w : Nat) (off : BitVec 64) : Env :=
  ("%arrayidx14.us.i.i582.i.i", .ptr (pow + w * 8)) ::
  ("%inc12.us.i.i581.i.i", .int 32 (k + 0x00000001#32)) :: env

/-- **The store block's step.**  The counter advances, the carry's high word lands
at the table's row `%wide.trip.count`, and the block branches to
`stk_mul_u64.exit583.i.i`. -/
theorem t3_tie_store_step {calls : Calls} {env : Env} {s : State}
    {k : BitVec 32} {off : BitVec 64} {pow w : Nat} {wv : BitVec 64}
    (hpc : s.pc = "while.body.us.i.i579.i.i")
    (hk : lookupName env "%inc12.us.i.i581759761.i.i" = some (.int 32 k))
    (hpow : lookupName env "%pow.i.i" = some (.ptr pow))
    (hw : lookupName env "%wide.trip.count.i.i565.i.i" = some (.int 64 wv))
    (hwv : (wv.signExtend 64).toNat = w)
    (hpos : w < 2 ^ 63)
    (hoff : lookupName env "%shr.i.i574.i.i.lcssa.off0" = some (.int 64 off)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3TieStoreEnv env k pow w off)
        { s with pc := "stk_mul_u64.exit583.i.i",
                 mem := writeBytes s.mem (pow + w * 8) (natToBytes off.toNat 8),
                 pre := some "while.body.us.i.i579.i.i" }) := by
  have hgep : lookupName
      (("%inc12.us.i.i581.i.i", .int 32 (k + 0x00000001#32)) :: env)
      "%pow.i.i" = some (.ptr pow) := by
    rw [lookupName_cons_ne _ _ (by decide)]; exact hpow
  have hwid : lookupName
      (("%inc12.us.i.i581.i.i", .int 32 (k + 0x00000001#32)) :: env)
      "%wide.trip.count.i.i565.i.i" = some (.int 64 wv) := by
    rw [lookupName_cons_ne _ _ (by decide)]; exact hw
  have hoff' : lookupName
      (("%arrayidx14.us.i.i582.i.i", .ptr (pow + w * 8)) ::
        ("%inc12.us.i.i581.i.i", .int 32 (k + 0x00000001#32)) :: env)
      "%shr.i.i574.i.i.lcssa.off0" = some (.int 64 off) := by
    rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact hoff
  refine numFast_step_at (s' := stateAt (t3TieStoreEnv env k pow w off)
      { s with mem := writeBytes s.mem (pow + w * 8) (natToBytes off.toNat 8) })
    (b := ⟨"while.body.us.i.i579.i.i", t3TieStoreInstrs,
      Term.br "stk_mul_u64.exit583.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using t3_tie_store_pin
  · rw [t3TieStoreInstrs,
      denoteCode_cons_of _ _ _ _ _ (JsonScanLane.step_add_imm_w calls env s
        "%inc12.us.i.i581.i.i" "%inc12.us.i.i581759761.i.i" 32 hk)]
    rw [denoteCode_cons_of _ _ _ _ _ (NumFastTier1.step_gep64_reg calls
      (("%inc12.us.i.i581.i.i", .int 32 (k + 0x00000001#32)) :: env) s
      "%arrayidx14.us.i.i582.i.i" "%pow.i.i" "%wide.trip.count.i.i565.i.i"
      hgep hwid (by rw [hwv]; exact hpos))]
    rw [hwv]
    rw [denoteCode_cons_of _ _ _ _ _ (step_store64 calls
      (("%arrayidx14.us.i.i582.i.i", .ptr (pow + w * 8)) ::
        ("%inc12.us.i.i581.i.i", .int 32 (k + 0x00000001#32)) :: env)
      s "%shr.i.i574.i.i.lcssa.off0" "%arrayidx14.us.i.i582.i.i" hoff'
      (lookupName_cons_self ..))]
    simp only [denoteCode_nil, t3TieStoreEnv, hwv, stateAt]
  · simp only [execTerm, stateAt, hpc]

/-! ### The block the tie lands on: `stk_mul_u64.exit583.i.i`

Its `phi` selects the outer counter from the edge that delivered — the test's own
refused arm or the store block — and then the block computes the residual
`%k168 - 19` and the outer loop's test `%k168 >s 37`. -/

/-- The landing block's instructions, from its pin. -/
def t3TieExitInstrs : List Instr :=
  [Instr.phi "%inc12.us.i.i581758.i.i" (Ty.int 32)
     [("while.body173.i.i", (Operand.reg "%inc12.us.i.i581759761.i.i")),
      ("while.cond.preheader.i.i577.i.i", (Operand.reg "%inc12.us.i.i581759761.i.i")),
      ("while.body.us.i.i579.i.i", (Operand.reg "%inc12.us.i.i581.i.i"))],
   Instr.binop "%sub175.i.i" (BinOp.add) 64 (Operand.reg "%k168.0762.i.i")
     (Operand.imm (Const.int 64 0xffffffffffffffed#64)),
   Instr.icmp "%cmp171.i.i" (IPred.sgt) 64 (Operand.reg "%k168.0762.i.i")
     (Operand.imm (Const.int 64 0x0000000000000025#64))]

theorem t3_tie_exit_pin :
    numFastBody.findBlock "stk_mul_u64.exit583.i.i" =
      some ⟨"stk_mul_u64.exit583.i.i", t3TieExitInstrs,
        Term.condbr (Operand.reg "%cmp171.i.i") "while.body173.i.i" "while.end176.i.i"⟩ := by
  simpa only [t3TieExitInstrs] using numFast_findBlock_stk_mul_u64_exit583_i_i

/-- The environment the landing block leaves. -/
def t3TieExitEnv (env : Env) (k : BitVec 32) (kk : BitVec 64) : Env :=
  ("%cmp171.i.i", .int 1 (evalICmp .sgt kk 0x0000000000000025#64)) ::
  ("%sub175.i.i", .int 64 (kk + 0xffffffffffffffed#64)) ::
  ("%inc12.us.i.i581758.i.i", .int 32 k) :: env

/-- The landing block's chain from either of the two edges the tie delivers. -/
theorem t3_tie_exit_denote {calls : Calls} {env : Env} {s : State}
    {k : BitVec 32} {kk : BitVec 64} {pre inc : String}
    (hpre : s.pre = some pre) (hinc : phiIncoming pre
      [("while.body173.i.i", (Operand.reg "%inc12.us.i.i581759761.i.i")),
       ("while.cond.preheader.i.i577.i.i", (Operand.reg "%inc12.us.i.i581759761.i.i")),
       ("while.body.us.i.i579.i.i", (Operand.reg "%inc12.us.i.i581.i.i"))] = some (.reg inc))
    (hk : lookupName env inc = some (.int 32 k))
    (hkk : lookupName env "%k168.0762.i.i" = some (.int 64 kk)) :
    denoteCode calls t3TieExitInstrs (stateAt env s) =
      some (stateAt (t3TieExitEnv env k kk) s) := by
  unfold t3TieExitInstrs
  rw [denoteCode_phi calls env s "%inc12.us.i.i581758.i.i" (Ty.int 32) _
    hpre hinc (evalOperand_reg_of env s inc (.int 32 k) hk)
    [Instr.binop "%sub175.i.i" (BinOp.add) 64 (Operand.reg "%k168.0762.i.i")
        (Operand.imm (Const.int 64 0xffffffffffffffed#64)),
      Instr.icmp "%cmp171.i.i" (IPred.sgt) 64 (Operand.reg "%k168.0762.i.i")
        (Operand.imm (Const.int 64 0x0000000000000025#64))]
    (by rfl)]
  rw [denoteCode_cons_of _ _ _ _ _ (step_add_imm calls
    (("%inc12.us.i.i581758.i.i", .int 32 k) :: env) s "%sub175.i.i" "%k168.0762.i.i"
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact hkk))]
  rw [denoteCode_cons_of _ _ _ _ _ (NumFastTier1.step_icmp_sgt_imm calls
    (("%sub175.i.i", .int 64 (kk + 0xffffffffffffffed#64)) ::
      ("%inc12.us.i.i581758.i.i", .int 32 k) :: env) s "%cmp171.i.i" "%k168.0762.i.i"
    (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact hkk))]
  simp only [denoteCode_nil, t3TieExitEnv, stateAt]

/-- **The landing block's step, from the test's refused arm.** -/
theorem t3_tie_exit_step_from_cond {calls : Calls} {env : Env} {s : State}
    {k : BitVec 32} {kk : BitVec 64}
    (hpc : s.pc = "stk_mul_u64.exit583.i.i")
    (hpre : s.pre = some "while.cond.preheader.i.i577.i.i")
    (hk : lookupName env "%inc12.us.i.i581759761.i.i" = some (.int 32 k))
    (hkk : lookupName env "%k168.0762.i.i" = some (.int 64 kk))
    (hbit : evalICmp .sgt kk 0x0000000000000025#64 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3TieExitEnv env k kk)
        { s with pc := "while.body173.i.i", pre := some "stk_mul_u64.exit583.i.i" }) := by
  refine numFast_step_at (s' := stateAt (t3TieExitEnv env k kk) s)
    (b := ⟨"stk_mul_u64.exit583.i.i", t3TieExitInstrs,
      Term.condbr (Operand.reg "%cmp171.i.i") "while.body173.i.i" "while.end176.i.i"⟩)
    ?_ ?_ ?_
  · simpa only [stateAt, hpc] using t3_tie_exit_pin
  · simpa only [denoteCode_nil] using t3_tie_exit_denote (pre := "while.cond.preheader.i.i577.i.i")
      (inc := "%inc12.us.i.i581759761.i.i") hpre (by decide) hk hkk
  · rw [numFast_execTerm_condbr_one (s := stateAt (t3TieExitEnv env k kk) s) _
      "while.body173.i.i" "while.end176.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- **The landing block's step, from the test's refused arm, the outer test
refused.** -/
theorem t3_tie_exit_step_from_cond_end {calls : Calls} {env : Env} {s : State}
    {k : BitVec 32} {kk : BitVec 64}
    (hpc : s.pc = "stk_mul_u64.exit583.i.i")
    (hpre : s.pre = some "while.cond.preheader.i.i577.i.i")
    (hk : lookupName env "%inc12.us.i.i581759761.i.i" = some (.int 32 k))
    (hkk : lookupName env "%k168.0762.i.i" = some (.int 64 kk))
    (hbit : evalICmp .sgt kk 0x0000000000000025#64 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3TieExitEnv env k kk)
        { s with pc := "while.end176.i.i", pre := some "stk_mul_u64.exit583.i.i" }) := by
  refine numFast_step_at (s' := stateAt (t3TieExitEnv env k kk) s)
    (b := ⟨"stk_mul_u64.exit583.i.i", t3TieExitInstrs,
      Term.condbr (Operand.reg "%cmp171.i.i") "while.body173.i.i" "while.end176.i.i"⟩)
    ?_ ?_ ?_
  · simpa only [stateAt, hpc] using t3_tie_exit_pin
  · simpa only [denoteCode_nil] using t3_tie_exit_denote (pre := "while.cond.preheader.i.i577.i.i")
      (inc := "%inc12.us.i.i581759761.i.i") hpre (by decide) hk hkk
  · rw [numFast_execTerm_condbr_zero (s := stateAt (t3TieExitEnv env k kk) s) _
      "while.body173.i.i" "while.end176.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- **The landing block's step, from the store block.** -/
theorem t3_tie_exit_step_from_store {calls : Calls} {env : Env} {s : State}
    {k : BitVec 32} {kk : BitVec 64}
    (hpc : s.pc = "stk_mul_u64.exit583.i.i")
    (hpre : s.pre = some "while.body.us.i.i579.i.i")
    (hk : lookupName env "%inc12.us.i.i581.i.i" = some (.int 32 k))
    (hkk : lookupName env "%k168.0762.i.i" = some (.int 64 kk))
    (hbit : evalICmp .sgt kk 0x0000000000000025#64 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3TieExitEnv env k kk)
        { s with pc := "while.body173.i.i", pre := some "stk_mul_u64.exit583.i.i" }) := by
  refine numFast_step_at (s' := stateAt (t3TieExitEnv env k kk) s)
    (b := ⟨"stk_mul_u64.exit583.i.i", t3TieExitInstrs,
      Term.condbr (Operand.reg "%cmp171.i.i") "while.body173.i.i" "while.end176.i.i"⟩)
    ?_ ?_ ?_
  · simpa only [stateAt, hpc] using t3_tie_exit_pin
  · simpa only [denoteCode_nil] using t3_tie_exit_denote (pre := "while.body.us.i.i579.i.i")
      (inc := "%inc12.us.i.i581.i.i") hpre (by decide) hk hkk
  · rw [numFast_execTerm_condbr_one (s := stateAt (t3TieExitEnv env k kk) s) _
      "while.body173.i.i" "while.end176.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- **The landing block's step, from the store block, the outer test refused.** -/
theorem t3_tie_exit_step_from_store_end {calls : Calls} {env : Env} {s : State}
    {k : BitVec 32} {kk : BitVec 64}
    (hpc : s.pc = "stk_mul_u64.exit583.i.i")
    (hpre : s.pre = some "while.body.us.i.i579.i.i")
    (hk : lookupName env "%inc12.us.i.i581.i.i" = some (.int 32 k))
    (hkk : lookupName env "%k168.0762.i.i" = some (.int 64 kk))
    (hbit : evalICmp .sgt kk 0x0000000000000025#64 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3TieExitEnv env k kk)
        { s with pc := "while.end176.i.i", pre := some "stk_mul_u64.exit583.i.i" }) := by
  refine numFast_step_at (s' := stateAt (t3TieExitEnv env k kk) s)
    (b := ⟨"stk_mul_u64.exit583.i.i", t3TieExitInstrs,
      Term.condbr (Operand.reg "%cmp171.i.i") "while.body173.i.i" "while.end176.i.i"⟩)
    ?_ ?_ ?_
  · simpa only [stateAt, hpc] using t3_tie_exit_pin
  · simpa only [denoteCode_nil] using t3_tie_exit_denote (pre := "while.body.us.i.i579.i.i")
      (inc := "%inc12.us.i.i581.i.i") hpre (by decide) hk hkk
  · rw [numFast_execTerm_condbr_zero (s := stateAt (t3TieExitEnv env k kk) s) _
      "while.body173.i.i" "while.end176.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-! ### The tie

From the epilogue's exit — the state `t3PeelExit` and `t3PeelExitWord` name, plus
the two cells the exit block reads and the epilogue's last visit wrote — the run
reaches `stk_mul_u64.exit583.i.i` within three control steps, with the counter
and the memory the arm's own.  The landing block's chain and the branch to the
outer loop's body or its end are the four steps stated above it. -/

/-- The two blocks the tie can land on. -/
def t3TieLands (e : State) : Prop :=
  e.pc = "while.end176.i.i" ∨ e.pc = "while.body173.i.i"

/-- What the state the tie lands on carries: the outer counter, the residual and
the outer test's bit. -/
def t3TieWord (kk : BitVec 64) : State → Prop := fun e =>
  (∃ k : BitVec 32,
    lookupName e.env "%inc12.us.i.i581758.i.i" = some (.int 32 k)) ∧
  lookupName e.env "%sub175.i.i" = some (.int 64 (kk + 0xffffffffffffffed#64)) ∧
  lookupName e.env "%cmp171.i.i" = some (.int 1 (evalICmp .sgt kk 0x0000000000000025#64)) ∧
  ((e.pc = "while.body173.i.i") = (evalICmp .sgt kk 0x0000000000000025#64 = (1 : BitVec 1)))

/-- The tie's word at the loop's body: the counter the landing block selected, the
residual and the bit, at a state whose program counter is `while.body173.i.i`. -/
theorem t3TieWord_body {env : Env} {base : State} {kk : BitVec 64} {k : BitVec 32}
    {pre : Option String} {pc : String}
    (hpc : pc = "while.body173.i.i")
    (hsgt : evalICmp .sgt kk 0x0000000000000025#64 = (1 : BitVec 1)) :
    t3TieWord kk (stateAt (t3TieExitEnv env k kk)
      { base with pc := pc, pre := pre }) := by
  subst hpc
  refine ⟨⟨k, ?_⟩, ?_, ?_, ?_⟩
  · simp only [stateAt, t3TieExitEnv]; block_lk
  · simp only [stateAt, t3TieExitEnv]; block_lk
  · simp only [stateAt, t3TieExitEnv]; block_lk
  · simp only [stateAt]; rw [hsgt]; simp

/-- The tie's word at the outer loop's end: the same, with the test refused. -/
theorem t3TieWord_end {env : Env} {base : State} {kk : BitVec 64} {k : BitVec 32}
    {pre : Option String} {pc : String}
    (hpc : pc = "while.end176.i.i")
    (hsgt : evalICmp .sgt kk 0x0000000000000025#64 = (0 : BitVec 1)) :
    t3TieWord kk (stateAt (t3TieExitEnv env k kk)
      { base with pc := pc, pre := pre }) := by
  subst hpc
  refine ⟨⟨k, ?_⟩, ?_, ?_, ?_⟩
  · simp only [stateAt, t3TieExitEnv]; block_lk
  · simp only [stateAt, t3TieExitEnv]; block_lk
  · simp only [stateAt, t3TieExitEnv]; block_lk
  · simp only [stateAt]; rw [hsgt]; simp

/-- **The tie: the epilogue's exit reaches the outer path's landing block.**  From
the exit state the peel's induction hands back — with the last visit's `i128` sum
and the outer loop's three cells — the run reaches `stk_mul_u64.exit583.i.i`
within three control steps when the residual fits one word (the exit block's
truncation and the test) and within four when it does not (the store block as
well), carrying the counter, the outer input and the memory the arm's own.

The epilogue's exit does not reach the copy's entry: `for.body87.i.i` is entered
from `for.body87.i.i.preheader`, whose only predecessor is `if.end83.i.i`, which
is upstream of the peel.  This block is where the exit actually goes, and its own
chain to `while.body173.i.i` or `while.end176.i.i` is stated just above. -/
theorem t3_peel_exit_tie {calls : Calls} {env : Env} {s : State}
    {addr xt : Nat} {carry : BitVec 128} {a : BitVec 128}
    {k : BitVec 32} {kk : BitVec 64} {wv : BitVec 64} {w : Nat}
    (hpc : s.pc = "while.cond.preheader.i.i577.i.i.epilog-lcssa")
    (hpow : lookupName env "%pow.i.i" = some (.ptr addr))
    (hxt : lookupName env "%xtraiter1083" = some (.int 64 (BitVec.ofNat 64 xt)))
    (hcarry : lookupName env "%shr.i.i574.i.i.epil" = some (.int 128 carry))
    (hadd : lookupName env "%add4.i.i572.i.i.epil" = some (.int 128 a))
    (hk : lookupName env "%inc12.us.i.i581759761.i.i" = some (.int 32 k))
    (hkk : lookupName env "%k168.0762.i.i" = some (.int 64 kk))
    (hw : lookupName env "%wide.trip.count.i.i565.i.i" = some (.int 64 wv))
    (hwv : (wv.signExtend 64).toNat = w) (hwpos : w < 2 ^ 63)
    (k' : Nat) :
    ∃ (e : State) (j : Nat), j ≤ 4 ∧ t3TieLands e ∧ t3TieWord kk e ∧
      (e.mem = s.mem ∨
        e.mem = writeBytes s.mem (addr + w * 8)
          (natToBytes (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)).toNat 8)) ∧
      runFuel calls (j + k') numFastBody (stateAt env s) =
        runFuel calls k' numFastBody e := by
  have hstep1 : step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3TieLcssaEnv env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
        { s with pc := "while.cond.preheader.i.i577.i.i",
                 pre := some "while.cond.preheader.i.i577.i.i.epilog-lcssa" }) :=
    t3_tie_lcssa_step hpc hcarry
  have hoff : lookupName (t3TieLcssaEnv env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
      "%extract.t1098" = some (.int 64 (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) := by
    simp only [t3TieLcssaEnv, lookupName_cons_self]
  have hadd' : lookupName (t3TieLcssaEnv env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
      "%add4.i.i572.i.i.epil" = some (.int 128 a) := by
    simp only [t3TieLcssaEnv]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact hadd
  have hpow' : lookupName (t3TieLcssaEnv env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
      "%pow.i.i" = some (.ptr addr) := by
    simp only [t3TieLcssaEnv]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact hpow
  have hk' : lookupName (t3TieLcssaEnv env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
      "%inc12.us.i.i581759761.i.i" = some (.int 32 k) := by
    simp only [t3TieLcssaEnv]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact hk
  have hkk' : lookupName (t3TieLcssaEnv env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
      "%k168.0762.i.i" = some (.int 64 kk) := by
    simp only [t3TieLcssaEnv]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact hkk
  have hw' : lookupName (t3TieLcssaEnv env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
      "%wide.trip.count.i.i565.i.i" = some (.int 64 wv) := by
    simp only [t3TieLcssaEnv]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact hw
  have hoffnew : BitVec.ofNat 64 (carry.toNat % 2 ^ 64) = BitVec.ofNat 64 (carry.toNat % 2 ^ 64) :=
    rfl
  by_cases hult : evalICmp .ult a t3TieBound = (1 : BitVec 1)
  · -- the refused test: the landing block directly
    have hstep2 : step calls numFastBody
        (stateAt (t3TieLcssaEnv env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
          { s with pc := "while.cond.preheader.i.i577.i.i",
                   pre := some "while.cond.preheader.i.i577.i.i.epilog-lcssa" }) =
        .jump (stateAt (t3TieCondEnv (t3TieLcssaEnv env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
          a (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
          { s with pc := "stk_mul_u64.exit583.i.i",
                   pre := some "while.cond.preheader.i.i577.i.i" }) :=
      t3_tie_cond_step_exit rfl rfl hadd' hoff hult
    by_cases hsgt : evalICmp .sgt kk 0x0000000000000025#64 = (1 : BitVec 1)
    · refine ⟨stateAt (t3TieExitEnv
        (t3TieCondEnv (t3TieLcssaEnv env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
          a (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) k kk)
        { s with pc := "while.body173.i.i", pre := some "stk_mul_u64.exit583.i.i" },
        3, by omega, Or.inr rfl, ?_, Or.inl rfl, ?_⟩
      · exact t3TieWord_body (base := { s with pre := some "stk_mul_u64.exit583.i.i" }) rfl hsgt
      · rw [show 3 + k' = 1 + (1 + (1 + k')) from by omega]
        rw [runFuel_jump_prefix hstep1 (1 + (1 + k'))]
        rw [runFuel_jump_prefix hstep2 (1 + k')]
        have h3 : step calls numFastBody
            (stateAt (t3TieCondEnv (t3TieLcssaEnv env
              (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) a
              (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
              { s with pc := "stk_mul_u64.exit583.i.i",
                       pre := some "while.cond.preheader.i.i577.i.i" }) =
            .jump (stateAt (t3TieExitEnv
              (t3TieCondEnv (t3TieLcssaEnv env
                (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) a
                (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) k kk)
              { s with pc := "while.body173.i.i",
                       pre := some "stk_mul_u64.exit583.i.i" }) :=
          t3_tie_exit_step_from_cond (by rfl) (by rfl) hk' hkk' hsgt
        rw [runFuel_jump_prefix h3]
    · have hsgt0 : evalICmp .sgt kk 0x0000000000000025#64 = (0 : BitVec 1) := by
        rcases bitVec1_eq_zero_or_one (evalICmp .sgt kk 0x0000000000000025#64) with h | h
        · exact h
        · exact absurd h hsgt
      refine ⟨stateAt (t3TieExitEnv
        (t3TieCondEnv (t3TieLcssaEnv env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
          a (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) k kk)
        { s with pc := "while.end176.i.i", pre := some "stk_mul_u64.exit583.i.i" },
        3, by omega, Or.inl rfl, ?_, Or.inl rfl, ?_⟩
      · exact t3TieWord_end (base := { s with pre := some "stk_mul_u64.exit583.i.i" }) rfl hsgt0
      · rw [show 3 + k' = 1 + (1 + (1 + k')) from by omega]
        rw [runFuel_jump_prefix hstep1 (1 + (1 + k'))]
        rw [runFuel_jump_prefix hstep2 (1 + k')]
        have h4 : step calls numFastBody
            (stateAt (t3TieCondEnv (t3TieLcssaEnv env
              (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) a
              (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
              { s with pc := "stk_mul_u64.exit583.i.i",
                       pre := some "while.cond.preheader.i.i577.i.i" }) =
            .jump (stateAt (t3TieExitEnv
              (t3TieCondEnv (t3TieLcssaEnv env
                (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) a
                (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) k kk)
              { s with pc := "while.end176.i.i",
                       pre := some "stk_mul_u64.exit583.i.i" }) :=
          t3_tie_exit_step_from_cond_end (by rfl) (by rfl) hk' hkk' hsgt0
        rw [runFuel_jump_prefix h4 k']
  · have hult0 : evalICmp .ult a t3TieBound = (0 : BitVec 1) := by
      rcases bitVec1_eq_zero_or_one (evalICmp .ult a t3TieBound) with h | h
      · exact h
      · exact absurd h hult
    have hstep2 : step calls numFastBody
        (stateAt (t3TieLcssaEnv env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
          { s with pc := "while.cond.preheader.i.i577.i.i",
                   pre := some "while.cond.preheader.i.i577.i.i.epilog-lcssa" }) =
        .jump (stateAt (t3TieCondEnv (t3TieLcssaEnv env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
          a (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
          { s with pc := "while.body.us.i.i579.i.i",
                   pre := some "while.cond.preheader.i.i577.i.i" }) :=
      t3_tie_cond_step_store rfl rfl hadd' hoff hult0
    have hoff'' : lookupName
        (t3TieCondEnv (t3TieLcssaEnv env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
          a (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
        "%shr.i.i574.i.i.lcssa.off0"
        = some (.int 64 (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) := by
      simp only [t3TieCondEnv, lookupName_cons_ne, lookupName_cons_self]
      rfl
    have hpow'' : lookupName
        (t3TieCondEnv (t3TieLcssaEnv env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
          a (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
        "%pow.i.i" = some (.ptr addr) := by
      simp only [t3TieCondEnv]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      exact hpow'
    have hk'' : lookupName
        (t3TieCondEnv (t3TieLcssaEnv env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
          a (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
        "%inc12.us.i.i581759761.i.i" = some (.int 32 k) := by
      simp only [t3TieCondEnv]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      exact hk'
    have hw'' : lookupName
        (t3TieCondEnv (t3TieLcssaEnv env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
          a (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
        "%wide.trip.count.i.i565.i.i" = some (.int 64 wv) := by
      simp only [t3TieCondEnv]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      exact hw'
    have hkk'' : lookupName
        (t3TieCondEnv (t3TieLcssaEnv env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
          a (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
        "%k168.0762.i.i" = some (.int 64 kk) := by
      simp only [t3TieCondEnv]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      exact hkk'
    have hstep3 : step calls numFastBody
        (stateAt
          (t3TieCondEnv (t3TieLcssaEnv env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
            a (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
          { s with pc := "while.body.us.i.i579.i.i",
                   pre := some "while.cond.preheader.i.i577.i.i" }) =
        .jump (stateAt
          (t3TieStoreEnv
            (t3TieCondEnv (t3TieLcssaEnv env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
              a (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) k addr w
            (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
          { s with pc := "stk_mul_u64.exit583.i.i",
                   mem := writeBytes s.mem (addr + w * 8)
                     (natToBytes (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)).toNat 8),
                   pre := some "while.body.us.i.i579.i.i" }) :=
      t3_tie_store_step rfl hk'' hpow'' hw'' hwv hwpos hoff''
    have hk3 : lookupName
        (t3TieStoreEnv
          (t3TieCondEnv (t3TieLcssaEnv env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
            a (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) k addr w
          (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
        "%inc12.us.i.i581.i.i" = some (.int 32 (k + 0x00000001#32)) := by
      simp only [t3TieStoreEnv]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
    have hkk3 : lookupName
        (t3TieStoreEnv
          (t3TieCondEnv (t3TieLcssaEnv env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
            a (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) k addr w
          (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
        "%k168.0762.i.i" = some (.int 64 kk) := by
      simp only [t3TieStoreEnv]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      exact hkk''
    by_cases hsgt : evalICmp .sgt kk 0x0000000000000025#64 = (1 : BitVec 1)
    · refine ⟨stateAt (t3TieExitEnv
        (t3TieStoreEnv
          (t3TieCondEnv (t3TieLcssaEnv env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
            a (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) k addr w
          (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) (k + 0x00000001#32) kk)
        { s with pc := "while.body173.i.i",
                 mem := writeBytes s.mem (addr + w * 8)
                   (natToBytes (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)).toNat 8),
                 pre := some "stk_mul_u64.exit583.i.i" },
        4, by omega, Or.inr rfl, ?_, Or.inr (by rfl), ?_⟩
      · exact t3TieWord_body (base := { s with
          mem := writeBytes s.mem (addr + w * 8)
            (natToBytes (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)).toNat 8),
          pre := some "stk_mul_u64.exit583.i.i" }) rfl hsgt
      · rw [show 4 + k' = 1 + (1 + (1 + (1 + k'))) from by omega]
        rw [runFuel_jump_prefix hstep1 (1 + (1 + (1 + k')))]
        rw [runFuel_jump_prefix hstep2 (1 + (1 + k'))]
        rw [runFuel_jump_prefix hstep3 (1 + k')]
        have h5 : step calls numFastBody
            (stateAt (t3TieStoreEnv
              (t3TieCondEnv (t3TieLcssaEnv env
                (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) a
                (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) k addr w
              (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
              { s with pc := "stk_mul_u64.exit583.i.i",
                       mem := writeBytes s.mem (addr + w * 8)
                         (natToBytes (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)).toNat 8),
                       pre := some "while.body.us.i.i579.i.i" }) =
            .jump (stateAt (t3TieExitEnv
              (t3TieStoreEnv
                (t3TieCondEnv (t3TieLcssaEnv env
                  (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) a
                  (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) k addr w
                (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
              (k + 0x00000001#32) kk)
              { s with pc := "while.body173.i.i",
                       mem := writeBytes s.mem (addr + w * 8)
                         (natToBytes (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)).toNat 8),
                       pre := some "stk_mul_u64.exit583.i.i" }) :=
          t3_tie_exit_step_from_store (by rfl) (by rfl) hk3 hkk3 hsgt
        rw [runFuel_jump_prefix h5 k']
    · have hsgt0 : evalICmp .sgt kk 0x0000000000000025#64 = (0 : BitVec 1) := by
        rcases bitVec1_eq_zero_or_one (evalICmp .sgt kk 0x0000000000000025#64) with h | h
        · exact h
        · exact absurd h hsgt
      refine ⟨stateAt (t3TieExitEnv
        (t3TieStoreEnv
          (t3TieCondEnv (t3TieLcssaEnv env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
            a (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) k addr w
          (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) (k + 0x00000001#32) kk)
        { s with pc := "while.end176.i.i",
                 mem := writeBytes s.mem (addr + w * 8)
                   (natToBytes (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)).toNat 8),
                 pre := some "stk_mul_u64.exit583.i.i" },
        4, by omega, Or.inl rfl, ?_, Or.inr (by rfl), ?_⟩
      · exact t3TieWord_end (base := { s with
          mem := writeBytes s.mem (addr + w * 8)
            (natToBytes (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)).toNat 8),
          pre := some "stk_mul_u64.exit583.i.i" }) rfl hsgt0
      · rw [show 4 + k' = 1 + (1 + (1 + (1 + k'))) from by omega]
        rw [runFuel_jump_prefix hstep1 (1 + (1 + (1 + k')))]
        rw [runFuel_jump_prefix hstep2 (1 + (1 + k'))]
        rw [runFuel_jump_prefix hstep3 (1 + k')]
        have h6 : step calls numFastBody
            (stateAt (t3TieStoreEnv
              (t3TieCondEnv (t3TieLcssaEnv env
                (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) a
                (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) k addr w
              (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
              { s with pc := "stk_mul_u64.exit583.i.i",
                       mem := writeBytes s.mem (addr + w * 8)
                         (natToBytes (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)).toNat 8),
                       pre := some "while.body.us.i.i579.i.i" }) =
            .jump (stateAt (t3TieExitEnv
              (t3TieStoreEnv
                (t3TieCondEnv (t3TieLcssaEnv env
                  (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) a
                  (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) k addr w
                (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
              (k + 0x00000001#32) kk)
              { s with pc := "while.end176.i.i",
                       mem := writeBytes s.mem (addr + w * 8)
                         (natToBytes (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)).toNat 8),
                       pre := some "stk_mul_u64.exit583.i.i" }) :=
          t3_tie_exit_step_from_store_end (by rfl) (by rfl) hk3 hkk3 hsgt0
        rw [runFuel_jump_prefix h6 k']

/-! ### Axiom footprints -/

#print axioms t3_tie_lcssa_step
#print axioms t3_tie_cond_pin
#print axioms t3_tie_cond_denote
#print axioms t3_tie_cond_step_exit
#print axioms t3_tie_cond_step_store
#print axioms t3_tie_store_step
#print axioms t3_tie_exit_pin
#print axioms t3_tie_exit_denote
#print axioms t3_tie_exit_step_from_cond
#print axioms t3_tie_exit_step_from_store
#print axioms t3TieWord_body
#print axioms t3TieWord_end
#print axioms t3_peel_exit_tie

end NumFastTier3PeelTie

end LeanLLVM.Refinement
