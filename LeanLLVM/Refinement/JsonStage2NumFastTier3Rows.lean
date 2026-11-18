/-
Tier 3's ladder at its row blocks: one row's charge, the rows' split, and the
positive loop at the emitted rows.

`JsonStage2NumFastTier3Ladder` fixes the two loops' heads at their pins and both
of each head's edges.  A loop's remaining arm is its row block's own step, and
what the two invariants share is the arithmetic of `t3Rows`: the row a residual
of `e` applies is `min e 22`, and the rows after it are the rows of the
remainder.

**The rows' split.**  `t3Rows_eq_cons` is the row list at a positive exponent:
`min e 22` and the rest.  `t3Rows_drop_eq` reads the tail at a counter as
`t3Rows (e - 22 * c)`, `t3Rows_drop_sum` that the residual after `c` rows is
`e - 22 * c`, and `t3Rows_drop_split` is the pair the loops' invariants need:
the next row is the minimum of the residual and the stride, and the rows after it
are the list's own tail.  `t3Rows_getElem_eq_min` is the same at the row's index
and `t3Rows_take_succ_split` at `take`, so the carried double's next row is an
append of one row.

**The carried double.**  `t3MulCarried_succ` and `t3DivCarried_succ` read the
fold at one more row: the carried double after `c + 1` rows is the one after `c`
multiplied or divided by the row the table holds at `c`.

**The positive row block.**  `t3_mulBody_denote` and `t3_mulBody_step` are
`while.body206.i.i`'s chain and terminator at the block's pin: the stride test,
its select, the table read, the `fmul`, the residual's subtraction, the bitcast
and the overflow test.  The row's code is `t3RowHolds`' (`t3RowHolds_of_pow10`),
a product that does not overflow is a finite pattern (`fmulBits_pack_fin`), and
such a pattern is below the infinity encoding (`packMag_fin_false_le`), so the
test refuses (`evalICmp_ugt_max_fin_zero`) — the branch the ladder's simulation
takes.

**The positive loop at the emitted rows.**  `t3MulLoop_step` discharges
`t3MulLoopOf`'s `step_loop` at `rows = t3Rows E` from the split lemmas and the
two steps, `t3MulLoop_exit` its `step_exit`, and `t3MulLoop_t3Rows` is the loop
itself, with its run `t3MulLoop_run_t3Rows` at the rows' own count.  The two
facts the emitted code reads but does not compute are stated for the whole run
rather than assumed at each iteration: the staging's table bytes (`hstage`) and
the magnitude conditions under which no row overflows (`hno`, and its consequence
`hpack` that every carried double is a finite pattern).

**The instruction vocabulary the blocks need.**  `icmp ugt`
(`step_icmp_ugt_imm`) and the `double`-to-`i64` bitcast (`step_bitcastToInt`)
for the multiply's overflow test, `ashr` (`step_ashr_imm`) for the division's
index, and `fcmp oeq` against a register (`step_fcmp_oeq`) or the zero literal
the division's test names (`step_fcmp_oeq_imm`), each with its `denoteCode` form.

**The negative row block.**  `t3_divBody_denote` is `while.body232.i.i`'s chain
at its pin: the `ult` test against `-22`, the negation and `ashr` that recover
`min (-e) 22` (`t3DivIndex`, `t3DivUlt`, `select_ult_min_neg`), the table read at
the recovered index, the `fdiv`, the residual's addition (`ofNat_add_ofInt_neg`),
and the `fcmp` against zero.  `t3_divBody_step` is the block's terminator at
`t3DivBodyEnv`.  The zero test's refusal reads the carried double's shape rather
than a magnitude bound: the quotient's value is the *next* carried double
(`t3DivCarried_succ`), and the staging asserts each of those is a positive
finite code (`hpack`), so the pattern is not the zero encoding
(`packMag_fin_false_ne_zero`) and the comparison is false
(`fcmpOeqBits_packMag_fin_false`).  Nothing weaker would do — a code divided by a
larger one's tick value rounds to `⟨0, 0⟩` — so what the arm supplies is that
hypothesis, not an underflow inequality.

**The negative loop at the emitted rows.**  `t3DivLoop_step` discharges
`t3DivLoopOf`'s `step_loop` at `rows = t3Rows E`, `t3DivLoop_exit` its
`step_exit`, and `t3DivLoop_t3Rows` is the loop itself, with its run
`t3DivLoop_run_t3Rows` at the rows' own count.  The two facts the emitted code
reads but does not compute are the same two the positive loop takes, at the
negative block's registers: the staging's table bytes (`hstage`) and the carried
double's shape (`hpack`, every carried double a positive finite code).  No
magnitude inequality joins them: the branch is the zero test, and `hpack` at the
next counter is the whole of what refuses it.
-/
import LeanLLVM.Refinement.JsonStage2NumFastTier3Ladder

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.NumFastTier1
open LeanLLVM.Refinement.NumFastTier3
open LeanLLVM.Refinement.NumFastTier3Ladder
open LeanLLVM.StrtodTier3

namespace NumFastTier3Rows

/-! ### The instruction vocabulary the row blocks need

`while.body206.i.i`'s overflow test is `icmp ugt` on the `double`-to-`i64` bitcast;
`while.body232.i.i`'s index is an `ashr` of the negated residual, and its exit
test an `fcmp oeq` against zero.  Each is the instruction's own `evalInstr`,
stated at a register read so a block's chain can rewrite one instruction at a
time. -/

/-- `%d = icmp ugt i64 %a, <c>`. -/
theorem step_icmp_ugt_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 64} (ha : lookupName env a = some (.int 64 x)) :
    evalInstr calls (stateAt env s) (.icmp d .ugt 64 (.reg a) (.imm (.int 64 c))) =
      some (stateAt ((d, .int 1 (evalICmp .ugt x c)) :: env) s) := by
  have ha' : evalOperand (stateAt env s) (.reg a) = some (.int 64 x) :=
    BlockEval.evalOperand_reg_of env s a (.int 64 x) ha
  have h := JsonS1MasksIR.evalInstr_icmp (calls := calls) (s := stateAt env s) (d := d)
    (pred := .ugt) (w := 64) (a := (.reg a)) (b := (.imm (.int 64 c)))
    ha' (BlockEval.evalOperand_lit_of (stateAt env s) 64 c)
  rw [h]
  simp only [stateAt, State.bind]

theorem denoteCode_icmp_ugt_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 64} (ha : lookupName env a = some (.int 64 x)) (is : List Instr) :
    denoteCode calls (.icmp d .ugt 64 (.reg a) (.imm (.int 64 c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp .ugt x c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_icmp_ugt_imm calls env s d a ha)]

/-- `%d = bitcast double %v to i64`: the sign and exponent fields are the word's
high bits, which is what the emitted overflow test compares. -/
theorem step_bitcastToInt (calls : Calls) (env : Env) (s : State) (d v : String)
    {x : BitVec 64} (hv : lookupName env v = some (.float x)) :
    evalInstr calls (stateAt env s) (.bitcastToInt d (.reg v)) =
      some (stateAt ((d, .int 64 x) :: env) s) := by
  simp only [evalInstr, evalOperand, stateAt, hv, State.bind]

theorem denoteCode_bitcastToInt (calls : Calls) (env : Env) (s : State) (d v : String)
    {x : BitVec 64} (hv : lookupName env v = some (.float x)) (is : List Instr) :
    denoteCode calls (.bitcastToInt d (.reg v) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 64 x) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_bitcastToInt calls env s d v hv)]

/-- `%d = ashr i64 %a, <c>`. -/
theorem step_ashr_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 64} (ha : lookupName env a = some (.int 64 x)) :
    evalInstr calls (stateAt env s) (.binop d .ashr 64 (.reg a) (.imm (.int 64 c))) =
      some (stateAt ((d, .int 64 (BitVec.sshiftRight x c.toNat)) :: env) s) := by
  have ha' : evalOperand (stateAt env s) (.reg a) = some (.int 64 x) :=
    BlockEval.evalOperand_reg_of env s a (.int 64 x) ha
  have h := JsonS1MasksIR.evalInstr_binop (s := stateAt env s) (calls := calls)
    (d := d) (op := .ashr) (w := 64) (a := (.reg a)) (b := (.imm (.int 64 c)))
    (x := x) (y := c) (r := (BitVec.sshiftRight x c.toNat).toNat)
    ha' (BlockEval.evalOperand_lit_of (stateAt env s) 64 c)
    (by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])
  simpa only [stateAt, State.bind, BitVec.ofNat_toNat, BitVec.setWidth_eq] using h

theorem denoteCode_ashr_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 64} (ha : lookupName env a = some (.int 64 x)) (is : List Instr) :
    denoteCode calls (.binop d .ashr 64 (.reg a) (.imm (.int 64 c)) :: is)
        (stateAt env s) =
      denoteCode calls is
        (stateAt ((d, .int 64 (BitVec.sshiftRight x c.toNat)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_ashr_imm calls env s d a ha)]

/-- `%d = fcmp oeq double %a, %b`. -/
theorem step_fcmp_oeq (calls : Calls) (env : Env) (s : State) (d a b : String)
    {x y : BitVec 64}
    (ha : lookupName env a = some (.float x)) (hb : lookupName env b = some (.float y)) :
    evalInstr calls (stateAt env s) (.fcmp d .oeq (.reg a) (.reg b)) =
      some (stateAt ((d, .int 1 (if fcmpOeqBits x y then 1 else 0)) :: env) s) := by
  simp only [evalInstr, evalOperand, stateAt, ha, hb, State.bind]

theorem denoteCode_fcmp_oeq (calls : Calls) (env : Env) (s : State) (d a b : String)
    {x y : BitVec 64}
    (ha : lookupName env a = some (.float x)) (hb : lookupName env b = some (.float y))
    (is : List Instr) :
    denoteCode calls (.fcmp d .oeq (.reg a) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt ((d, .int 1 (if fcmpOeqBits x y then 1 else 0)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_fcmp_oeq calls env s d a b ha hb)]

/-- `%d = fcmp oeq double %a, <c>`. -/
theorem step_fcmp_oeq_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x y : BitVec 64} (ha : lookupName env a = some (.float x)) :
    evalInstr calls (stateAt env s) (.fcmp d .oeq (.reg a) (.imm (.float y))) =
      some (stateAt ((d, .int 1 (if fcmpOeqBits x y then 1 else 0)) :: env) s) := by
  simp only [evalInstr, evalOperand, Const.toValue, stateAt, ha, State.bind]

theorem denoteCode_fcmp_oeq_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x y : BitVec 64} (ha : lookupName env a = some (.float x)) (is : List Instr) :
    denoteCode calls (.fcmp d .oeq (.reg a) (.imm (.float y)) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt ((d, .int 1 (if fcmpOeqBits x y then 1 else 0)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_fcmp_oeq_imm calls env s d a ha)]

/-! ### The positive row block

`while.body206.i.i` applies one table row to the carried double.  Its chain is
the stride test `%124.min = %e10.0.i.i <u 22`, the select that clamps the
exponent, the table read at `@NUMF_EL1_POW10 + 8 * %124`, the `fmul`, the
residual's subtraction, the bitcast and the overflow test. -/

/-- An `icmp ult` against an immediate, at `Nat` readings: the bit is the
comparison's truth. -/
theorem evalICmp_ult_ofNat_imm {resid c : Nat} (hresid : resid < 2 ^ 64)
    (hc : c < 2 ^ 64) :
    evalICmp .ult (BitVec.ofNat 64 resid) (BitVec.ofNat 64 c) =
      BitVec.ofBool (resid < c) := by
  rw [evalICmp, BitVec.ult_eq_decide, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hresid, Nat.mod_eq_of_lt hc]

/-- The select's clamp is `min`: `%124` is `%e10.0.i.i` below the stride and the
stride at or above it. -/
theorem select_ult_min {resid : Nat} (hresid : resid < 2 ^ 63) :
    (if evalICmp .ult (BitVec.ofNat 64 resid) (0x0000000000000016#64) =
        (1 : BitVec 1)
      then BitVec.ofNat 64 resid else (0x0000000000000016#64))
      = BitVec.ofNat 64 (min resid 22) := by
  have hbit : evalICmp .ult (BitVec.ofNat 64 resid) (0x0000000000000016#64)
      = BitVec.ofBool (resid < 22) :=
    evalICmp_ult_ofNat_imm (by omega) (by decide)
  rw [hbit]
  by_cases h : resid < 22
  · have hb : BitVec.ofBool (resid < 22) = (1 : BitVec 1) := by simp [h]
    rw [hb, ite_eq_left rfl, Nat.min_eq_left (by omega)]
  · have hb : BitVec.ofBool (resid < 22) = (0 : BitVec 1) := by simp [h]
    rw [hb, ite_eq_right (by decide), Nat.min_eq_right (by omega)]

/-- The clamp's immediate select, at the value the test leaves. -/
theorem step_select_imm_ite (calls : Calls) (env : Env) (s : State) (d c a : String)
    {bb : BitVec 1} {x y : BitVec 64}
    (hc : lookupName env c = some (.int 1 bb))
    (ha : lookupName env a = some (.int 64 x)) :
    evalInstr calls (stateAt env s) (.select d (.int 64) (.reg c) (.reg a)
        (.imm (.int 64 y))) =
      some (stateAt ((d, .int 64 (if bb = 1 then x else y)) :: env) s) := by
  rcases BlockEval.bitVec1_eq_zero_or_one bb with h0 | h1
  · subst h0
    simp only [evalInstr, evalOperand, stateAt, hc, ha, Const.toValue, State.bind,
      show ((0 : BitVec 1) = 1) = False from by decide, ite_false, ite_true]
  · subst h1
    simp only [evalInstr, evalOperand, stateAt, hc, ha, Const.toValue, State.bind,
      ite_true]

theorem denoteCode_select_imm_ite (calls : Calls) (env : Env) (s : State)
    (d c a : String) {bb : BitVec 1} {x y : BitVec 64}
    (hc : lookupName env c = some (.int 1 bb))
    (ha : lookupName env a = some (.int 64 x)) (is : List Instr) :
    denoteCode calls (.select d (.int 64) (.reg c) (.reg a) (.imm (.int 64 y)) :: is)
        (stateAt env s) =
      denoteCode calls is
        (stateAt ((d, .int 64 (if bb = 1 then x else y)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_select_imm_ite calls env s d c a hc ha)]

/-- The positive row block's instructions, from its pin. -/
def t3MulBodyInstrs : List Instr :=
  [Instr.icmp "%124.min" (IPred.ult) 64 (Operand.reg "%e10.0.i.i")
    (Operand.imm (Const.int 64 0x0000000000000016#64)),
   Instr.select "%124" (Ty.int 64) (Operand.reg "%124.min")
    (Operand.reg "%e10.0.i.i") (Operand.imm (Const.int 64 0x0000000000000016#64)),
   Instr.gep "%arrayidx216.i.i" Ty.double (Operand.global "@NUMF_EL1_POW10")
    (Operand.reg "%124"),
   Instr.load "%125" Ty.double (Operand.reg "%arrayidx216.i.i"),
   Instr.fmul "%mul217.i.i" (Operand.reg "%d201.0.i.i") (Operand.reg "%125"),
   Instr.binop "%sub219.i.i" (BinOp.sub) 64 (Operand.reg "%e10.0.i.i")
    (Operand.reg "%124"),
   Instr.bitcastToInt "%.cast.i.i.i" (Operand.reg "%mul217.i.i"),
   Instr.icmp "%cmp221.i.i" (IPred.ugt) 64 (Operand.reg "%.cast.i.i.i")
    (Operand.imm (Const.int 64 0x7fefffffffffffff#64))]

theorem t3_mulBody_find :
    numFastBody.findBlock t3MulBody =
      some ⟨t3MulBody, t3MulBodyInstrs,
        Term.condbr (Operand.reg "%cmp221.i.i") t3LadderJoin t3MulHead⟩ := by
  simpa only [t3MulBody, t3MulHead, t3LadderJoin, t3MulBodyInstrs]
    using t3_mulBody_pin

/-- The environment the positive row block leaves. -/
def t3MulBodyEnv (env : Env) (e d p : BitVec 64) (m address : Nat) : Env :=
  ("%cmp221.i.i", .int 1 (evalICmp .ugt (fmulBits d p) 0x7fefffffffffffff#64)) ::
  ("%.cast.i.i.i", .int 64 (fmulBits d p)) ::
  ("%sub219.i.i", .int 64 (e - BitVec.ofNat 64 m)) ::
  ("%mul217.i.i", .float (fmulBits d p)) ::
  ("%125", .float p) ::
  ("%arrayidx216.i.i", .ptr (address + m * 8)) ::
  ("%124", .int 64 (BitVec.ofNat 64 m)) ::
  ("%124.min", .int 1 (evalICmp .ult e 0x0000000000000016#64)) :: env

/-- **The positive row block's chain.**  The residual exponent's clamp, the
table's row at it, one `fmul`, and the overflow test. -/
theorem t3_mulBody_denote {calls : Calls} {env : Env} {s : State}
    {resid : Nat} {d p : BitVec 64} {address : Nat}
    (he : lookupName env "%e10.0.i.i" = some (.int 64 (BitVec.ofNat 64 resid)))
    (hd : lookupName env "%d201.0.i.i" = some (.float d))
    (hb : lookupName env "@NUMF_EL1_POW10" = some (.ptr address))
    (hresid : resid < 2 ^ 63)
    (hread : readBytes s.mem (address + min resid 22 * 8) 8
      = some (natToBytes p.toNat 8)) :
    denoteCode calls t3MulBodyInstrs (stateAt env s) =
      some (stateAt (t3MulBodyEnv env (BitVec.ofNat 64 resid) d p
        (min resid 22) address) s) := by
  have hm64 : min resid 22 < 2 ^ 64 := by omega
  have hpos : (BitVec.signExtend 64 (BitVec.ofNat 64 (min resid 22))).toNat
      < 2 ^ 63 := by
    rw [BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm64]
    omega
  have hread' : readBytes s.mem
      (address + (BitVec.signExtend 64 (BitVec.ofNat 64 (min resid 22))).toNat * 8)
        8 = some (natToBytes p.toNat 8) := by
    simpa only [BitVec.signExtend_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hm64] using hread
  unfold t3MulBodyInstrs
  rw [BlockEval.denoteCode_icmp_ult_imm calls env s "%124.min" "%e10.0.i.i" he]
  rw [denoteCode_select_imm_ite calls _ s "%124" "%124.min" "%e10.0.i.i"
    (by block_lk) (by block_lk)]
  rw [select_ult_min (resid := resid) hresid]
  rw [NumFastTier1.denoteCode_gep_double_global calls _ s "%arrayidx216.i.i"
    "@NUMF_EL1_POW10" "%124" (by block_lk) (by block_lk) hpos]
  rw [NumFastTier1.denoteCode_load_double calls _ s "%125" "%arrayidx216.i.i"
    (by block_lk) hread']
  rw [NumFastTier1.denoteCode_fmul calls _ s "%mul217.i.i" "%d201.0.i.i" "%125"
    (by block_lk) (by block_lk)]
  rw [BlockEval.denoteCode_sub_reg calls _ s "%sub219.i.i" "%e10.0.i.i" "%124"
    (by block_lk) (by block_lk)]
  rw [denoteCode_bitcastToInt calls _ s "%.cast.i.i.i" "%mul217.i.i" (by block_lk)]
  rw [denoteCode_icmp_ugt_imm calls _ s "%cmp221.i.i" "%.cast.i.i.i" (by block_lk)]
  simp only [denoteCode_nil, stateAt, t3MulBodyEnv, BitVec.signExtend_eq,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm64]

/-- **The positive row block's step.**  The block reads its row, multiplies, and
jumps back to the head: the overflow test's bit is the caller's, since the
terminator branches on it. -/
theorem t3_mulBody_step {calls : Calls} {env : Env} {s : State}
    {resid : Nat} {d p : BitVec 64} {address : Nat}
    (hpc : s.pc = t3MulBody)
    (he : lookupName env "%e10.0.i.i" = some (.int 64 (BitVec.ofNat 64 resid)))
    (hd : lookupName env "%d201.0.i.i" = some (.float d))
    (hb : lookupName env "@NUMF_EL1_POW10" = some (.ptr address))
    (hresid : resid < 2 ^ 63)
    (hread : readBytes s.mem (address + min resid 22 * 8) 8
      = some (natToBytes p.toNat 8))
    (hbit : evalICmp .ugt (fmulBits d p) 0x7fefffffffffffff#64 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3MulBodyEnv env (BitVec.ofNat 64 resid) d p
        (min resid 22) address)
        { s with pc := t3MulHead, pre := some t3MulBody }) := by
  refine numFast_step_at
    (s' := stateAt (t3MulBodyEnv env (BitVec.ofNat 64 resid) d p
      (min resid 22) address) s)
    (b := ⟨t3MulBody, t3MulBodyInstrs,
      Term.condbr (Operand.reg "%cmp221.i.i") t3LadderJoin t3MulHead⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using t3_mulBody_find
  · simpa only [stateAt] using t3_mulBody_denote he hd hb hresid hread
  · have hlk : lookupName (t3MulBodyEnv env (BitVec.ofNat 64 resid) d p
        (min resid 22) address) "%cmp221.i.i"
        = some (.int 1 (evalICmp .ugt (fmulBits d p) 0x7fefffffffffffff#64)) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_zero _ "%cmp221.i.i" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-! ### The magnitude facts the row's charge reads

The row block's test is a statement about the product's encoding: the table's row
is a power of ten and the clamp is at most the stride, so the row is a code
(`t3RowHolds`, by `pow10_uitofp_spec`), and a product that does not overflow is a
finite pattern — below the infinity encoding, so the test refuses. -/

/-- The signed test against zero, at a positive residual below the sign bit. -/
theorem evalICmp_sgt_ofNat_zero {n : Nat} (h0 : 0 < n) (hn : n < 2 ^ 63) :
    evalICmp .sgt (BitVec.ofNat 64 n) (0 : BitVec 64) = (1 : BitVec 1) := by
  have htoNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmsb : (BitVec.ofNat 64 n).msb = false := by
    rw [BitVec.msb_eq_decide, htoNat]
    simp only [decide_eq_false_iff_not]
    omega
  have htoInt : (BitVec.ofNat 64 n).toInt = (n : Int) := by
    rw [BitVec.toInt_eq_toNat_of_msb hmsb, htoNat]
  rw [show evalICmp .sgt (BitVec.ofNat 64 n) (0 : BitVec 64)
      = BitVec.ofBool (((0 : BitVec 64)).slt (BitVec.ofNat 64 n)) from rfl]
  rw [BitVec.slt_eq_decide]
  have hz : ((0 : BitVec 64)).toInt = (0 : Int) := by decide
  rw [hz, htoInt]
  have hpos : ((0 : Int) < (n : Int)) := by omega
  rw [show decide ((0 : Int) < (n : Int)) = true from by
    rw [decide_eq_true_eq]
    omega]
  rfl

/-- A code's tick value is at most the largest finite pattern. -/
theorem magTicks_fin_le {c : Code} (hc : c.IsMag) :
    Mag.toNat (.fin c) ≤ 0x7fefffffffffffff := by
  show c.expField * 2 ^ 52 + (if c.expField = 0 then c.mant else c.mant - 2 ^ 52)
    ≤ 0x7fefffffffffffff
  have hbig : (2 : Nat) ^ 52 ≤ 0x7fefffffffffffff := by decide
  rcases hc with ⟨hE, hm⟩ | ⟨h1, h2, h3, h4⟩
  · rw [hE]
    simp only [ite_true, Nat.zero_mul, Nat.zero_add]
    exact Nat.le_trans (Nat.le_of_lt hm) hbig
  · rw [ite_eq_right (by omega : ¬ c.expField = 0)]
    have h53 : (2 : Nat) ^ 53 = 2 * 2 ^ 52 := by
      rw [show (53 : Nat) = 52 + 1 from by decide, Nat.pow_succ, Nat.mul_comm]
    have h2' : c.mant < 2 * 2 ^ 52 := by rw [← h53]; exact h4
    have hm' : c.mant - 2 ^ 52 ≤ 2 ^ 52 - 1 := by omega
    have h1' : c.expField * 2 ^ 52 ≤ 2046 * 2 ^ 52 := Nat.mul_le_mul_right _ h2
    have hsum := Nat.add_le_add h1' hm'
    have heq : 2046 * 2 ^ 52 + (2 ^ 52 - 1) = 0x7fefffffffffffff := by decide
    rw [heq] at hsum
    exact hsum

/-- A finite code's pattern is below the infinity encoding, so the emitted
overflow test reads zero at it. -/
theorem packMag_fin_false_le {c : Code} (hc : c.IsMag) :
    (packMag (.fin c) false).toNat ≤ 0x7fefffffffffffff := by
  have hle := magTicks_fin_le hc
  have hshow : packMag (.fin c) false = BitVec.ofNat 64 (Mag.toNat (.fin c)) := by
    simp only [packMag, Bool.false_eq_true, ite_false, Nat.zero_add]
  rw [hshow, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : Mag.toNat (.fin c) < 2 ^ 64)]
  exact hle

/-- The emitted overflow test at a finite code's pattern is zero. -/
theorem evalICmp_ugt_max_fin_zero {c : Code} (hc : c.IsMag) :
    evalICmp .ugt (packMag (.fin c) false) (0x7fefffffffffffff#64) =
      (0 : BitVec 1) := by
  have hle := packMag_fin_false_le hc
  have hmax : ((0x7fefffffffffffff#64 : BitVec 64)).toNat = 0x7fefffffffffffff := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)]
  have hne : evalICmp .ugt (packMag (.fin c) false) (0x7fefffffffffffff#64)
      ≠ (1 : BitVec 1) := by
    intro h1
    have h2 := (evalICmp_ugt_one_iff _ _).1 h1
    rw [BitVec.ult_iff_toNat_lt, hmax] at h2
    omega
  rcases BlockEval.bitVec1_eq_zero_or_one _ with h | h
  · exact h
  · exact absurd h hne

/-- The table's row at a power of ten is a code: `pow10_uitofp_spec` at the
stride's bound. -/
theorem t3RowHolds_of_pow10 {m : Nat} (hm : m ≤ 22) :
    ∃ r : Code, t3RowHolds m r ∧ uitofpBits (10 ^ m) = packMag (.fin r) false := by
  obtain ⟨r, hp, hM, ht⟩ := NumFastTier1.pow10_uitofp_spec hm
  exact ⟨r, ⟨hM, ht⟩, hp⟩

/-- **A row's product that does not overflow is a finite pattern.**  The product's
rounding is a code, and the pattern the block's test reads is below the infinity
encoding. -/
theorem fmulBits_pack_fin {c₁ c₂ : Code} (h₁ : c₁.IsMag) (h₂ : c₂.IsMag)
    (hno : ¬ overflowTicks * 2 ^ 1074 ≤ c₁.ticks * c₂.ticks) :
    ∃ k : Code,
      fmulBits (packMag (.fin c₁) false) (packMag (.fin c₂) false) =
        packMag (.fin k) false ∧ k.IsMag := by
  have hfin : ∃ k : Code, roundMag (c₁.ticks * c₂.ticks) (2 ^ 1074) = .fin k := by
    unfold roundMag
    rw [ite_eq_right hno]
    split <;> exact ⟨_, rfl⟩
  obtain ⟨k, hk⟩ := hfin
  refine ⟨k, ?_, NumFastTier3.roundMag_isMag (by decide) hno hk⟩
  rw [NumFastTier1.fmulBits_pack h₁ h₂, hk]

/-- The residual's `Nat` reading: a subtraction of two `Nat`s below `2 ^ 64`. -/
theorem ofNat_sub_ofNat' {n i : Nat} (hi : i ≤ n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 i = BitVec.ofNat 64 (n - i) := by
  refine BitVec.toNat_inj.1 ?_
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have hi' : (BitVec.ofNat 64 i).toNat = i := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hle : BitVec.ofNat 64 i ≤ BitVec.ofNat 64 n := by
    rw [BitVec.le_def, hi', hn']
    omega
  rw [BitVec.toNat_sub_of_le hle, hn', hi', BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]

/-- The ladder's residual after a counter: the rows it has not applied. -/
def t3Resid (E c : Nat) : Nat := ((t3Rows E).drop c).sum

/-- The positive ladder head's carried double, from the environment's own
builder. -/
theorem t3MulHeadEnv_d201 {env : Env} {e d : BitVec 64} :
    lookupName (t3MulHeadEnv env e d) "%d201.0.i.i" = some (.float d) := by
  simp only [t3MulHeadEnv]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]

/-- The positive ladder head's residual exponent. -/
theorem t3MulHeadEnv_e10 {env : Env} {e d : BitVec 64} :
    lookupName (t3MulHeadEnv env e d) "%e10.0.i.i" = some (.int 64 e) := by
  simp only [t3MulHeadEnv]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_self]

/-- The positive row block's residual after the row. -/
theorem t3MulBodyEnv_sub219 {env : Env} {e d p : BitVec 64} {m address : Nat} :
    lookupName (t3MulBodyEnv env e d p m address) "%sub219.i.i"
      = some (.int 64 (e - BitVec.ofNat 64 m)) := by
  simp only [t3MulBodyEnv]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_self]

/-- The positive row block's carried double. -/
theorem t3MulBodyEnv_mul217 {env : Env} {e d p : BitVec 64} {m address : Nat} :
    lookupName (t3MulBodyEnv env e d p m address) "%mul217.i.i"
      = some (.float (fmulBits d p)) := by
  simp only [t3MulBodyEnv]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide), lookupName_cons_self]

/-! ### The negative row block

`while.body232.i.i` divides the carried double by one table row.  Its index is
not the residual directly: the block tests `%e10.2.i.i <u -22`, negates the
residual by `* -2 ^ 32` and shifts the high word back, so `%126` is `-e`; the
select then takes the clamp, exactly `min (-e) 22`.  The block's chain
(`t3_divBody_denote`) and its terminator (`t3_divBody_step`) are the same shape
as the positive block's, at the negative index arithmetic; the zero test's
refusal is `fcmpOeqBits_packMag_fin_false`, at the next carried double's shape,
so `t3DivLoopOf`'s two arms are the loop below. -/

/-- The emitted index's recovery: at a negative residual `-k` the negate-and-shift
is `k`. -/
theorem t3DivIndex {k : Nat} (h0 : 0 < k) (hk : k < 2 ^ 31) :
    ((BitVec.ofInt 64 (-(k : Int)) * 0xffffffff00000000#64).sshiftRight 32)
      = BitVec.ofNat 64 k := by
  have hmul : BitVec.ofInt 64 (-(k : Int)) * 0xffffffff00000000#64
      = BitVec.ofNat 64 (k * 2 ^ 32) := by bv_omega
  rw [hmul, BitVec.sshiftRight_eq]
  have hmsb : (BitVec.ofNat 64 (k * 2 ^ 32)).msb = false := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp
    omega
  have htoInt : (BitVec.ofNat 64 (k * 2 ^ 32)).toInt = ((k * 2 ^ 32 : Nat) : Int) := by
    rw [BitVec.toInt_eq_toNat_of_msb hmsb, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  rw [htoInt]
  rw [show (((k * 2 ^ 32 : Nat) : Int) >>> 32) = ((k : Int)) from by
    rw [Int.shiftRight_eq_div_pow]
    omega]
  rw [BitVec.ofInt_natCast]

/-- The block's `ult` test: at `-k` the comparison against `-22` is `22 < k`. -/
theorem t3DivUlt {k : Nat} (h0 : 0 < k) (hk : k < 2 ^ 63) :
    evalICmp .ult (BitVec.ofInt 64 (-(k : Int))) (0xffffffffffffffea#64) =
      BitVec.ofBool (22 < k) := by
  have h1 : (BitVec.ofInt 64 (-(k : Int))).toNat = 2 ^ 64 - k := by
    rw [BitVec.toNat_ofInt]
    omega
  have h2 : ((0xffffffffffffffea#64 : BitVec 64)).toNat = 2 ^ 64 - 22 := by decide
  rw [evalICmp, BitVec.ult_eq_decide, h1, h2]
  by_cases h : 22 < k
  · rw [show decide (22 < k) = true from by simp [h],
      show decide (2 ^ 64 - k < 2 ^ 64 - 22) = true from by
        rw [decide_eq_true_eq]; omega]
  · rw [show decide (22 < k) = false from by simp [h],
      show decide (2 ^ 64 - k < 2 ^ 64 - 22) = false from by
        rw [decide_eq_false_iff_not]; omega]

/-- The clamp's select at the negative residual: the arm is the stride, the
register the recovered index. -/
theorem select_ult_min_neg {k : Nat} (h0 : 0 < k) (hk : k < 2 ^ 63) :
    (if evalICmp .ult (BitVec.ofInt 64 (-(k : Int))) (0xffffffffffffffea#64) =
        (1 : BitVec 1)
      then (0x0000000000000016#64 : BitVec 64) else BitVec.ofNat 64 k)
      = BitVec.ofNat 64 (min k 22) := by
  have hbit := t3DivUlt h0 hk
  rw [hbit]
  by_cases h : 22 < k
  · have hb : BitVec.ofBool (22 < k) = (1 : BitVec 1) := by simp [h]
    rw [hb, ite_eq_left rfl, Nat.min_eq_right (by omega)]
  · have hb : BitVec.ofBool (22 < k) = (0 : BitVec 1) := by simp [h]
    rw [hb, ite_eq_right (by decide), Nat.min_eq_left (by omega)]

/-- The clamp's select with the immediate as the tested arm. -/
theorem step_select_imm_reg_ite (calls : Calls) (env : Env) (s : State)
    (d c b : String) {bb : BitVec 1} {y x : BitVec 64}
    (hc : lookupName env c = some (.int 1 bb))
    (hb : lookupName env b = some (.int 64 x)) :
    evalInstr calls (stateAt env s)
        (.select d (.int 64) (.reg c) (.imm (.int 64 y)) (.reg b)) =
      some (stateAt ((d, .int 64 (if bb = 1 then y else x)) :: env) s) := by
  rcases BlockEval.bitVec1_eq_zero_or_one bb with h | h
  · subst h
    simp only [evalInstr, evalOperand, stateAt, hc, hb, Const.toValue, State.bind,
      show ((0 : BitVec 1) = 1) = False from by decide, ite_false, ite_true]
  · subst h
    simp only [evalInstr, evalOperand, stateAt, hc, hb, Const.toValue, State.bind,
      ite_true]

theorem denoteCode_select_imm_reg_ite (calls : Calls) (env : Env) (s : State)
    (d c b : String) {bb : BitVec 1} {y x : BitVec 64}
    (hc : lookupName env c = some (.int 1 bb))
    (hb : lookupName env b = some (.int 64 x)) (is : List Instr) :
    denoteCode calls
        (.select d (.int 64) (.reg c) (.imm (.int 64 y)) (.reg b) :: is)
        (stateAt env s) =
      denoteCode calls is
        (stateAt ((d, .int 64 (if bb = 1 then y else x)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_select_imm_reg_ite calls env s d c b hc hb)]

/-- `%d = mul i64 %a, <c>`. -/
theorem step_mul_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 64} (ha : lookupName env a = some (.int 64 x)) :
    evalInstr calls (stateAt env s) (.binop d .mul 64 (.reg a) (.imm (.int 64 c))) =
      some (stateAt ((d, .int 64 (x * c)) :: env) s) := by
  have ha' : evalOperand (stateAt env s) (.reg a) = some (.int 64 x) :=
    BlockEval.evalOperand_reg_of env s a (.int 64 x) ha
  have h := JsonS1MasksIR.evalInstr_binop (s := stateAt env s) (calls := calls)
    (d := d) (op := .mul) (w := 64) (a := (.reg a)) (b := (.imm (.int 64 c)))
    (x := x) (y := c) (r := (x * c).toNat)
    ha' (BlockEval.evalOperand_lit_of (stateAt env s) 64 c)
    (by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])
  simpa only [stateAt, State.bind, BitVec.ofNat_toNat, BitVec.setWidth_eq] using h

theorem denoteCode_mul_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 64} (ha : lookupName env a = some (.int 64 x)) (is : List Instr) :
    denoteCode calls (.binop d .mul 64 (.reg a) (.imm (.int 64 c)) :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 64 (x * c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_mul_imm calls env s d a ha)]

/-- The negative row block's instructions, from its pin. -/
def t3DivBodyInstrs : List Instr :=
  [Instr.icmp "%cmp234.i.i" (IPred.ult) 64 (Operand.reg "%e10.2.i.i")
    (Operand.imm (Const.int 64 0xffffffffffffffea#64)),
   Instr.binop "%.neg.i.i" (BinOp.mul) 64 (Operand.reg "%e10.2.i.i")
    (Operand.imm (Const.int 64 0xffffffff00000000#64)),
   Instr.binop "%126" (BinOp.ashr) 64 (Operand.reg "%.neg.i.i")
    (Operand.imm (Const.int 64 0x0000000000000020#64)),
   Instr.select "%idxprom242.i.i" (Ty.int 64) (Operand.reg "%cmp234.i.i")
    (Operand.imm (Const.int 64 0x0000000000000016#64)) (Operand.reg "%126"),
   Instr.gep "%arrayidx243.i.i" Ty.double (Operand.global "@NUMF_EL1_POW10")
    (Operand.reg "%idxprom242.i.i"),
   Instr.load "%127" Ty.double (Operand.reg "%arrayidx243.i.i"),
   Instr.fdiv "%div.i.i" (Operand.reg "%d201.2.i.i") (Operand.reg "%127"),
   Instr.binop "%add245.i.i" (BinOp.add) 64 (Operand.reg "%idxprom242.i.i")
    (Operand.reg "%e10.2.i.i"),
   Instr.fcmp "%cmp246.i.i" (FPred.oeq) (Operand.reg "%div.i.i")
    (Operand.imm (Const.float 0x0000000000000000#64))]

theorem t3_divBody_find :
    numFastBody.findBlock t3DivBody =
      some ⟨t3DivBody, t3DivBodyInstrs,
        Term.condbr (Operand.reg "%cmp246.i.i") "while.end253.i.i" t3DivHead⟩ := by
  simpa only [t3DivBody, t3DivHead, t3DivBodyInstrs] using t3_divBody_pin

/-- The environment the negative row block leaves. -/
def t3DivBodyEnv (env : Env) (ev d p : BitVec 64) (k m address : Nat) : Env :=
  ("%cmp246.i.i", .int 1 (if fcmpOeqBits (fdivBits d p) (0 : BitVec 64) then 1 else 0)) ::
  ("%add245.i.i", .int 64 (BitVec.ofNat 64 m + ev)) ::
  ("%div.i.i", .float (fdivBits d p)) ::
  ("%127", .float p) ::
  ("%arrayidx243.i.i", .ptr (address + m * 8)) ::
  ("%idxprom242.i.i", .int 64 (BitVec.ofNat 64 m)) ::
  ("%126", .int 64 (BitVec.ofNat 64 k)) ::
  ("%.neg.i.i", .int 64 (ev * 0xffffffff00000000#64)) ::
  ("%cmp234.i.i", .int 1 (evalICmp .ult ev 0xffffffffffffffea#64)) :: env

/-- The residual's addition at a negative exponent: the row's index plus `-k`. -/
theorem ofNat_add_ofInt_neg {m k : Nat} (hmk : m ≤ k) (hk : k < 2 ^ 64) :
    BitVec.ofNat 64 m + BitVec.ofInt 64 (-(k : Int)) =
      BitVec.ofInt 64 (-((k - m : Nat) : Int)) := by
  bv_omega

/-- The negative head's test at a residual `-k` below the sign bit. -/
theorem evalICmp_slt_ofInt_neg {k : Nat} (h0 : 0 < k) (hk : k < 2 ^ 63) :
    evalICmp .slt (BitVec.ofInt 64 (-(k : Int))) (0 : BitVec 64) = (1 : BitVec 1) := by
  have htoInt : (BitVec.ofInt 64 (-(k : Int))).toInt = -(k : Int) := by
    refine BitVec.toInt_ofInt_eq_self (by decide) ?_ ?_ <;> omega
  rw [show evalICmp .slt (BitVec.ofInt 64 (-(k : Int))) (0 : BitVec 64)
      = BitVec.ofBool ((BitVec.ofInt 64 (-(k : Int))).slt (0 : BitVec 64)) from rfl]
  have hz : BitVec.toInt (0 : BitVec 64) = 0 := by decide
  rw [BitVec.slt_eq_decide, htoInt, hz]
  rw [show decide (-(k : Int) < 0) = true from by rw [decide_eq_true_eq]; omega]
  rfl

/-- The same test at a spent residual: the exponent is zero. -/
theorem evalICmp_slt_ofInt_neg_zero :
    evalICmp .slt (BitVec.ofInt 64 (-((0 : Nat) : Int))) (0 : BitVec 64) =
      (0 : BitVec 1) := by
  decide

/-- A positive finite code's pattern is not the zero pattern.  The zero pattern
is the code `⟨0, 0⟩`, whose magnitude is zero ticks. -/
theorem packMag_fin_false_ne_zero {c : Code} (hc : c.IsMag) (hpos : 0 < c.ticks) :
    packMag (.fin c) false ≠ (0 : BitVec 64) := by
  intro h
  have h1 := NumFastTier1.magTicks_ofBits_packMag_false hc
  rw [h] at h1
  have h2 : F64.magTicks (F64.ofBits (0 : BitVec 64)) = 0 := by decide
  omega

/-- **The zero test refuses at a positive finite code's pattern.**  The quotient
`fdivBits` answers is `packMag` of a code (`fdivBits_pack`), and a code with a
positive tick value is not the zero pattern, so `fcmp oeq` against zero reads
false there. -/
theorem fcmpOeqBits_packMag_fin_false {c : Code} (hc : c.IsMag) (hpos : 0 < c.ticks) :
    fcmpOeqBits (packMag (.fin c) false) (0 : BitVec 64) = false := by
  have hnan := NumFastTier1.isNaN_ofBits_packMag_false hc
  have hzero := NumFastTier1.isZero_ofBits_packMag_false hc hpos
  have hne := packMag_fin_false_ne_zero hc hpos
  have hnan0 : (F64.ofBits (0 : BitVec 64)).isNaN = false := by decide
  have hzero0 : (F64.ofBits (0 : BitVec 64)).isZero = true := by decide
  unfold fcmpOeqBits
  dsimp only
  rw [hnan, hnan0, hzero, hzero0]
  rw [show (packMag (.fin c) false == (0 : BitVec 64)) = false from by
    rw [beq_eq_false_iff_ne]; exact hne]
  rfl

/-- **The negative row block's chain.**  The `ult` test against `-22`, the
negate-and-shift index, the clamp, the table's row, one `fdiv`, the residual's
addition and the zero test. -/
theorem t3_divBody_denote {calls : Calls} {env : Env} {s : State}
    {k : Nat} {d p : BitVec 64} {address : Nat}
    (he : lookupName env "%e10.2.i.i"
      = some (.int 64 (BitVec.ofInt 64 (-(k : Int)))))
    (hd : lookupName env "%d201.2.i.i" = some (.float d))
    (hb : lookupName env "@NUMF_EL1_POW10" = some (.ptr address))
    (h0 : 0 < k) (hk : k < 2 ^ 31)
    (hread : readBytes s.mem (address + min k 22 * 8) 8
      = some (natToBytes p.toNat 8)) :
    denoteCode calls t3DivBodyInstrs (stateAt env s) =
      some (stateAt (t3DivBodyEnv env (BitVec.ofInt 64 (-(k : Int))) d p k
        (min k 22) address) s) := by
  have hm64 : min k 22 < 2 ^ 64 := by omega
  have hpos : (BitVec.signExtend 64 (BitVec.ofNat 64 (min k 22))).toNat < 2 ^ 63 := by
    rw [BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm64]
    omega
  have hread' : readBytes s.mem
      (address + (BitVec.signExtend 64 (BitVec.ofNat 64 (min k 22))).toNat * 8)
        8 = some (natToBytes p.toNat 8) := by
    simpa only [BitVec.signExtend_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hm64] using hread
  unfold t3DivBodyInstrs
  rw [BlockEval.denoteCode_icmp_ult_imm calls env s "%cmp234.i.i" "%e10.2.i.i" he]
  rw [denoteCode_mul_imm calls _ s "%.neg.i.i" "%e10.2.i.i" (by block_lk)]
  rw [denoteCode_ashr_imm calls _ s "%126" "%.neg.i.i" (by block_lk)]
  rw [show (0x0000000000000020#64 : BitVec 64).toNat = 32 from by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)]]
  rw [t3DivIndex h0 hk]
  rw [denoteCode_select_imm_reg_ite calls _ s "%idxprom242.i.i" "%cmp234.i.i" "%126"
    (by block_lk) (by block_lk)]
  rw [select_ult_min_neg (k := k) h0 (by omega)]
  rw [NumFastTier1.denoteCode_gep_double_global calls _ s "%arrayidx243.i.i"
    "@NUMF_EL1_POW10" "%idxprom242.i.i" (by block_lk) (by block_lk) hpos]
  rw [NumFastTier1.denoteCode_load_double calls _ s "%127" "%arrayidx243.i.i"
    (by block_lk) hread']
  rw [NumFastTier1.denoteCode_fdiv calls _ s "%div.i.i" "%d201.2.i.i" "%127"
    (by block_lk) (by block_lk)]
  rw [BlockEval.denoteCode_add_reg calls _ s "%add245.i.i" "%idxprom242.i.i"
    "%e10.2.i.i" (by block_lk) (by block_lk)]
  rw [denoteCode_fcmp_oeq_imm calls _ s "%cmp246.i.i" "%div.i.i" (by block_lk)]
  simp only [denoteCode_nil, stateAt, t3DivBodyEnv, BitVec.signExtend_eq,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm64]
  all_goals rfl

/-- **The negative row block's step.**  The block reads its row, divides, and
jumps back to the head; the zero test's bit is the caller's, since the terminator
branches on it. -/
theorem t3_divBody_step {calls : Calls} {env : Env} {s : State}
    {k : Nat} {d p : BitVec 64} {address : Nat}
    (hpc : s.pc = t3DivBody)
    (he : lookupName env "%e10.2.i.i"
      = some (.int 64 (BitVec.ofInt 64 (-(k : Int)))))
    (hd : lookupName env "%d201.2.i.i" = some (.float d))
    (hb : lookupName env "@NUMF_EL1_POW10" = some (.ptr address))
    (h0 : 0 < k) (hk : k < 2 ^ 31)
    (hread : readBytes s.mem (address + min k 22 * 8) 8
      = some (natToBytes p.toNat 8))
    (hbit : fcmpOeqBits (fdivBits d p) (0 : BitVec 64) = false) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3DivBodyEnv env (BitVec.ofInt 64 (-(k : Int))) d p k
        (min k 22) address)
        { s with pc := t3DivHead, pre := some t3DivBody }) := by
  refine numFast_step_at
    (s' := stateAt (t3DivBodyEnv env (BitVec.ofInt 64 (-(k : Int))) d p k
      (min k 22) address) s)
    (b := ⟨t3DivBody, t3DivBodyInstrs,
      Term.condbr (Operand.reg "%cmp246.i.i") "while.end253.i.i" t3DivHead⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using t3_divBody_find
  · simpa only [stateAt] using t3_divBody_denote he hd hb h0 hk hread
  · have hlk : lookupName (t3DivBodyEnv env (BitVec.ofInt 64 (-(k : Int))) d p k
        (min k 22) address) "%cmp246.i.i"
        = some (.int 1 (if fcmpOeqBits (fdivBits d p) (0 : BitVec 64) then 1 else 0)) :=
      lookupName_cons_self ..
    have hbit0 : (if fcmpOeqBits (fdivBits d p) (0 : BitVec 64) then
        (1 : BitVec 1) else 0) = (0 : BitVec 1) := by
      rw [hbit]
      rfl
    rw [numFast_execTerm_condbr_zero _ "%cmp246.i.i" _ _ hlk hbit0]
    simp only [stateAt, hpc]

/-! ### The negative row block's registers

The head's two `phi`s and the row block's two residual registers, read out of
the environment builders the two blocks leave. -/

theorem t3DivHeadEnv_e10 {env : Env} {e d : BitVec 64} :
    lookupName (t3DivHeadEnv env e d) "%e10.2.i.i" = some (.int 64 e) := by
  simp only [t3DivHeadEnv]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_self]

theorem t3DivHeadEnv_d201 {env : Env} {e d : BitVec 64} :
    lookupName (t3DivHeadEnv env e d) "%d201.2.i.i" = some (.float d) := by
  simp only [t3DivHeadEnv]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]

theorem t3DivBodyEnv_add245 {env : Env} {ev d p : BitVec 64} {k m address : Nat} :
    lookupName (t3DivBodyEnv env ev d p k m address) "%add245.i.i"
      = some (.int 64 (BitVec.ofNat 64 m + ev)) := by
  simp only [t3DivBodyEnv]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]

theorem t3DivBodyEnv_div {env : Env} {ev d p : BitVec 64} {k m address : Nat} :
    lookupName (t3DivBodyEnv env ev d p k m address) "%div.i.i"
      = some (.float (fdivBits d p)) := by
  simp only [t3DivBodyEnv]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_self]

/-! ### The rows at a counter

`t3Rows e` is `min e 22` and the rest until `e` is spent, so at a counter inside
it the next row is the residual's minimum with the stride, and what follows is
the list's own tail. -/

/-- **The rows at a positive exponent.**  The first row is the exponent clamped
at the stride, and the rows after it are the ladder's at the remainder. -/
theorem t3Rows_eq_cons {e : Nat} (h : 0 < e) :
    t3Rows e = min e 22 :: t3Rows (e - 22) := by
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  rw [t3Rows]
  split
  · rename_i hle
    simp only [t3Stride] at hle
    have h22 : (e' + 1) - 22 = 0 := by omega
    rw [h22, Nat.min_eq_left hle, t3Rows]
  · rename_i hle
    simp only [t3Stride] at hle
    rw [Nat.min_eq_right (by omega)]
    simp only [t3Stride]

/-- **The rows after `c`.**  The tail of the ladder at a counter inside it is the
ladder of the residual `e - 22 * c`. -/
theorem t3Rows_drop_eq (e c : Nat) (hc : c ≤ (t3Rows e).length) :
    (t3Rows e).drop c = t3Rows (e - 22 * c) := by
  induction c generalizing e with
  | zero => simp
  | succ c ih =>
    have he : e ≠ 0 := by
      intro h0
      subst h0
      rw [t3Rows] at hc
      simp at hc
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    have heq : t3Rows (e' + 1) = min (e' + 1) 22 :: t3Rows (e' + 1 - 22) :=
      t3Rows_eq_cons (Nat.succ_pos e')
    have hlen : (t3Rows (e' + 1)).length = (t3Rows (e' + 1 - 22)).length + 1 := by
      rw [heq]
      simp
    rw [hlen] at hc
    rw [heq, List.drop_succ_cons, ih (e' + 1 - 22) (by omega)]
    congr 1
    omega

/-- **The residual after `c` rows.**  The rows left spend exactly the exponent
minus the rows already spent. -/
theorem t3Rows_drop_sum {e c : Nat} (hc : c ≤ (t3Rows e).length) :
    ((t3Rows e).drop c).sum = e - 22 * c := by
  rw [t3Rows_drop_eq e c hc, t3Rows_sum]

/-- **The rows' split at a counter.**  A counter inside the ladder leaves the
next row — the residual clamped at the stride — and the list's own tail. -/
theorem t3Rows_drop_split {e c : Nat} (hc : c < (t3Rows e).length) :
    (t3Rows e).drop c
      = min ((t3Rows e).drop c).sum 22 :: (t3Rows e).drop (c + 1) := by
  have hc' : c ≤ (t3Rows e).length := Nat.le_of_lt hc
  have hsum : ((t3Rows e).drop c).sum = e - 22 * c := t3Rows_drop_sum hc'
  have hrne : e - 22 * c ≠ 0 := by
    intro h0
    have hlen : ((t3Rows e).drop c).length = 0 := by
      rw [t3Rows_drop_eq e c hc', h0]
      rw [t3Rows]
      rfl
    rw [List.length_drop] at hlen
    omega
  have hsplit : (t3Rows e).drop c = t3Rows (e - 22 * c) := t3Rows_drop_eq e c hc'
  have hstep : (t3Rows e).drop (c + 1) = t3Rows (e - 22 * (c + 1)) :=
    t3Rows_drop_eq e (c + 1) (by omega)
  have hnext : e - 22 * c - 22 = e - 22 * (c + 1) := by omega
  rw [hsum, hsplit, t3Rows_eq_cons (Nat.pos_of_ne_zero hrne), hstep, hnext]

/-- **The next row.**  A counter inside the ladder reads the residual's minimum
with the stride. -/
theorem t3Rows_getElem_eq_min {e c : Nat} (hc : c < (t3Rows e).length) :
    (t3Rows e)[c] = min ((t3Rows e).drop c).sum 22 := by
  have hsum : ((t3Rows e).drop c).sum = e - 22 * c :=
    t3Rows_drop_sum (Nat.le_of_lt hc)
  have h := t3Rows_drop_split hc
  rw [hsum] at h
  rw [List.drop_eq_getElem_cons hc] at h
  rw [hsum]
  exact (List.cons.inj h).1

/-- **The rows' prefix at one more row.**  Taking one more row is taking the
rows so far and the next one. -/
theorem t3Rows_take_succ_split {e c : Nat} (hc : c < (t3Rows e).length) :
    (t3Rows e).take (c + 1) = (t3Rows e).take c ++ [(t3Rows e)[c]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hc]
  rfl

/-! ### The carried double at one more row -/

/-- **The multiply fold's next row.**  The carried double after `c + 1` rows is
the one after `c` scaled by the row at `c`. -/
theorem t3MulCarried_succ {d0 : BitVec 64} {rows : List Nat} {c : Nat}
    (hc : c < rows.length) :
    t3MulCarried d0 rows (c + 1)
      = fmulBits (t3MulCarried d0 rows c) (uitofpBits (10 ^ rows[c])) := by
  unfold t3MulCarried
  rw [List.take_add_one, List.getElem?_eq_getElem hc]
  simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- **The divide fold's next row.** -/
theorem t3DivCarried_succ {d0 : BitVec 64} {rows : List Nat} {c : Nat}
    (hc : c < rows.length) :
    t3DivCarried d0 rows (c + 1)
      = fdivBits (t3DivCarried d0 rows c) (uitofpBits (10 ^ rows[c])) := by
  unfold t3DivCarried
  rw [List.take_add_one, List.getElem?_eq_getElem hc]
  simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-! ### The positive loop's back edge, at the emitted rows

The loop shape `t3MulLoopOf` asks for one iteration: from the head at a residual
the ladder has not spent, the row block applies the next row and the head is
re-entered.  The split lemmas above name that row — `min` of the residual and the
stride — and its tail; the carried double's next row is `t3MulCarried_succ`; the
per-edge step is `t3_mulHead_step_one*` and `t3_mulBody_step`.

The two facts the emitted code reads but does not compute are the staging's: the
table's bytes at the row's address (`hstage`), and the magnitude conditions under
which the overflow test is refused (`hno`, and its consequence that every
carried double is a finite pattern, `hpack`).  Both are stated for the whole run,
so the iteration's simulation is on the branch that does not overflow. -/

/-- **The positive loop's step at the emitted rows.**  One iteration from the
head reaches the head again with the counter advanced, one row applied, within
two control steps. -/
theorem t3MulLoop_step (calls : Calls) (d0 : BitVec 64) (E address : Nat) (hE : E ≤ 342)
    (hpack : ∀ c, c ≤ (t3Rows E).length →
      ∃ k : Code, t3MulCarried d0 (t3Rows E) c = packMag (.fin k) false ∧ k.IsMag)
    (hstage : ∀ (env : Env) (s : State) (resid : Nat) (d : BitVec 64),
      lookupName env "%e10.0.i.i" = some (.int 64 (BitVec.ofNat 64 resid)) →
      lookupName env "%d201.0.i.i" = some (.float d) →
        lookupName env "@NUMF_EL1_POW10" = some (.ptr address) ∧
        readBytes s.mem (address + min resid 22 * 8) 8
          = some (natToBytes (uitofpBits (10 ^ min resid 22)).toNat 8))
    (hno : ∀ c, c < (t3Rows E).length →
      ¬ overflowTicks * 2 ^ 1074
        ≤ F64.magTicks (F64.ofBits (t3MulCarried d0 (t3Rows E) c))
            * (10 ^ min (t3Resid E c) 22 * 2 ^ 1074)) :
    ∀ (r : Nat) (s : State) (c : Nat),
      t3MulInv d0 (t3Rows E) (r + 1) s c → t3MulAtBound (t3Rows E) s c = false →
      ∃ (e' : State) (c' : Nat) (j : Nat), j ≤ 2 ∧ e'.pc = t3MulHead ∧ c < c' ∧
        t3MulInv d0 (t3Rows E) r e' c' ∧
        ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e' := by
  intro r s c hinv hbound
  obtain ⟨hpc, hcr, hpre, hc0, hcpos⟩ := hinv
  have hc_lt : c < (t3Rows E).length := by omega
  have hc_le : c ≤ (t3Rows E).length := by omega
  have hresid_ne : t3Resid E c ≠ 0 := by
    intro h0
    have htrue : decide (t3Resid E c = 0) = true := by simp [h0]
    have hfalse : decide (t3Resid E c = 0) = false := hbound
    rw [htrue] at hfalse
    exact Bool.noConfusion hfalse
  have hresid_pos : 0 < t3Resid E c := Nat.pos_of_ne_zero hresid_ne
  have hresid_lt : t3Resid E c < 2 ^ 63 := by
    have h1 : t3Resid E c = E - 22 * c := t3Rows_drop_sum hc_le
    omega
  have hbit_sgt : evalICmp .sgt (BitVec.ofNat 64 (t3Resid E c)) (0 : BitVec 64)
      = (1 : BitVec 1) :=
    evalICmp_sgt_ofNat_zero hresid_pos hresid_lt
  -- The head's step: the carried double and the state it leaves at the row block.
  obtain ⟨d, hd_eq, hstep1⟩ :
      ∃ d : BitVec 64, d = t3MulCarried d0 (t3Rows E) c ∧
        step calls numFastBody s =
          .jump (stateAt (t3MulHeadEnv s.env (BitVec.ofNat 64 (t3Resid E c)) d)
            { s with pc := t3MulBody, pre := some t3MulHead }) := by
    rcases Nat.eq_zero_or_pos c with hc_eq | hc_gt
    · subst hc_eq
      obtain ⟨hsub200, hconv202⟩ := hc0 rfl
      have hpre0 : s.pre = some "if.end198.i.i" := by
        rw [hpre, ite_eq_left rfl]
      refine ⟨t3MulCarried d0 (t3Rows E) 0, rfl, ?_⟩
      have h := t3_mulHead_step_one_entry (calls := calls) (env := s.env) (s := s)
        hpc hpre0 hsub200 hconv202 hbit_sgt
      exact h
    · obtain ⟨hsub219, hmul217⟩ := hcpos hc_gt
      have hpre0 : s.pre = some t3MulBody := by
        rw [hpre, ite_eq_right (by omega : ¬ c = 0)]
      refine ⟨t3MulCarried d0 (t3Rows E) c, rfl, ?_⟩
      have h := t3_mulHead_step_one (calls := calls) (env := s.env) (s := s)
        hpc hpre0 hsub219 hmul217 hbit_sgt
      exact h
  -- The carried double is a finite pattern, and the row's code from the table.
  obtain ⟨kc, hkc, hkcM⟩ := hpack c hc_le
  have hdpack : d = packMag (.fin kc) false := by rw [hd_eq, hkc]
  obtain ⟨rc, hrcHolds, hrcp⟩ :=
    t3RowHolds_of_pow10 (m := min (t3Resid E c) 22) (Nat.min_le_right _ _)
  have hno_c : ¬ overflowTicks * 2 ^ 1074 ≤ kc.ticks * rc.ticks := by
    have h0 := hno c hc_lt
    rw [hkc, NumFastTier1.magTicks_ofBits_packMag_false hkcM, ← hrcHolds.2] at h0
    exact h0
  obtain ⟨k', hk', hk'M⟩ := fmulBits_pack_fin hkcM hrcHolds.1 hno_c
  have hbit_body : evalICmp .ugt
      (fmulBits d (uitofpBits (10 ^ min (t3Resid E c) 22)))
      (0x7fefffffffffffff#64) = (0 : BitVec 1) := by
    rw [hdpack, hrcp, hk']
    exact evalICmp_ugt_max_fin_zero hk'M
  -- The staging's two facts, at the row block's own environment.
  have he1 : lookupName (t3MulHeadEnv s.env (BitVec.ofNat 64 (t3Resid E c)) d)
      "%e10.0.i.i" = some (.int 64 (BitVec.ofNat 64 (t3Resid E c))) :=
    t3MulHeadEnv_e10
  have hd1 : lookupName (t3MulHeadEnv s.env (BitVec.ofNat 64 (t3Resid E c)) d)
      "%d201.0.i.i" = some (.float d) := t3MulHeadEnv_d201
  obtain ⟨htbl, hread⟩ := hstage _ _ (t3Resid E c) d he1 hd1
  let e' : State := stateAt
    (t3MulBodyEnv (t3MulHeadEnv s.env (BitVec.ofNat 64 (t3Resid E c)) d)
      (BitVec.ofNat 64 (t3Resid E c)) d
      (uitofpBits (10 ^ min (t3Resid E c) 22)) (min (t3Resid E c) 22) address)
    { s with pc := t3MulHead, pre := some t3MulBody }
  have hstep2 : step calls numFastBody
      (stateAt (t3MulHeadEnv s.env (BitVec.ofNat 64 (t3Resid E c)) d)
        { s with pc := t3MulBody, pre := some t3MulHead }) = .jump e' := by
    have h := t3_mulBody_step (calls := calls)
      (env := t3MulHeadEnv s.env (BitVec.ofNat 64 (t3Resid E c)) d)
      (s := { s with pc := t3MulBody, pre := some t3MulHead }) (resid := t3Resid E c)
      (d := d) (p := uitofpBits (10 ^ min (t3Resid E c) 22))
      (address := address) rfl he1 hd1 htbl hresid_lt hread hbit_body
    exact h
  refine ⟨e', c + 1, 2, by omega, rfl, by omega, ?_, ?_⟩
  · -- the invariant at the row block's exit
    refine ⟨rfl, by omega, rfl, ?_, ?_⟩
    · intro h0
      omega
    · intro _
      refine ⟨?_, ?_⟩
      · simp only [e', stateAt]
        rw [t3MulBodyEnv_sub219]
        have hsplit := t3Rows_drop_split hc_lt
        have hsum : t3Resid E c = (t3Rows E)[c] + t3Resid E (c + 1) := by
          have hrow : (t3Rows E)[c] = min (t3Resid E c) 22 := t3Rows_getElem_eq_min hc_lt
          have hs := congrArg List.sum (t3Rows_drop_split hc_lt)
          simp only [t3Resid] at hs hrow
          rw [← hrow] at hs
          simp only [List.sum_cons] at hs
          simpa only [t3Resid] using hs
        have hrow : (t3Rows E)[c] = min (t3Resid E c) 22 := t3Rows_getElem_eq_min hc_lt
        have hi : min (t3Resid E c) 22 ≤ t3Resid E c := Nat.min_le_left _ _
        have hsub : t3Resid E c - min (t3Resid E c) 22 = t3Resid E (c + 1) := by omega
        rw [ofNat_sub_ofNat' hi (by omega), hsub]
        rfl
      · simp only [e', stateAt]
        rw [t3MulBodyEnv_mul217]
        have hcar := t3MulCarried_succ (d0 := d0) (rows := t3Rows E) hc_lt
        have hrow : (t3Rows E)[c] = min (t3Resid E c) 22 := t3Rows_getElem_eq_min hc_lt
        rw [hcar, ← hd_eq, ← hrow]
  · intro k
    rw [show 2 + k = 1 + (1 + k) from by omega]
    rw [runFuel_jump_prefix hstep1 (1 + k)]
    exact runFuel_jump_prefix hstep2 k

/-! ### The positive loop's exit, and the loop at the emitted rows

At the bound the residual is zero, so the head's test is refused and the loop
leaves for the ladder's join in one control step.  With the step above, this
discharges both arms `t3MulLoopOf` asks for, and the loop's run is stated at the
rows' own count. -/

/-- The signed test at a spent residual. -/
theorem evalICmp_sgt_zero : evalICmp .sgt (0 : BitVec 64) (0 : BitVec 64) =
    (0 : BitVec 1) := by decide

/-- **The positive loop's exit.**  At the bound the head jumps to the join. -/
theorem t3MulLoop_exit (calls : Calls) (d0 : BitVec 64) (E : Nat) :
    ∀ (r : Nat) (s : State) (c : Nat),
      t3MulInv d0 (t3Rows E) r s c → t3MulAtBound (t3Rows E) s c = true →
      ∃ (e : State) (j : Nat), j ≤ 2 ∧ e.pc = t3LadderJoin ∧ t3MulExitWord e ∧
        ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e := by
  intro r s c hinv hbound
  obtain ⟨hpc, hcr, hpre, hc0, hcpos⟩ := hinv
  have hresid : t3Resid E c = 0 := by
    simpa only [t3MulAtBound, t3Resid, decide_eq_true_eq] using hbound
  have hbit : evalICmp .sgt (BitVec.ofNat 64 (t3Resid E c)) (0 : BitVec 64)
      = (0 : BitVec 1) := by
    rw [hresid]
    exact evalICmp_sgt_zero
  rcases Nat.eq_zero_or_pos c with hc_eq | hc_gt
  · subst hc_eq
    obtain ⟨hsub200, hconv202⟩ := hc0 rfl
    have hpre0 : s.pre = some "if.end198.i.i" := by rw [hpre, ite_eq_left rfl]
    refine ⟨stateAt (t3MulHeadEnv s.env (BitVec.ofNat 64 (t3Resid E 0))
        (t3MulCarried d0 (t3Rows E) 0)) { s with pc := t3LadderJoin, pre := some t3MulHead },
      1, by omega, rfl, ⟨rfl, ?_, ?_⟩, ?_⟩
    · simp only [stateAt]
      rw [t3MulHeadEnv_e10]
      simp
    · simp only [stateAt]
      rw [t3MulHeadEnv_d201]
      simp
    · intro k
      exact runFuel_jump_prefix
        (t3_mulHead_step_zero_entry (calls := calls) (env := s.env) (s := s)
          hpc hpre0 hsub200 hconv202 hbit) k
  · obtain ⟨hsub219, hmul217⟩ := hcpos hc_gt
    have hpre0 : s.pre = some t3MulBody := by
      rw [hpre, ite_eq_right (by omega : ¬ c = 0)]
    refine ⟨stateAt (t3MulHeadEnv s.env (BitVec.ofNat 64 (t3Resid E c))
        (t3MulCarried d0 (t3Rows E) c)) { s with pc := t3LadderJoin, pre := some t3MulHead },
      1, by omega, rfl, ⟨rfl, ?_, ?_⟩, ?_⟩
    · simp only [stateAt]
      rw [t3MulHeadEnv_e10]
      simp
    · simp only [stateAt]
      rw [t3MulHeadEnv_d201]
      simp
    · intro k
      exact runFuel_jump_prefix
        (t3_mulHead_step_zero (calls := calls) (env := s.env) (s := s)
          hpc hpre0 hsub219 hmul217 hbit) k

/-- **The positive loop at the emitted rows.** -/
def t3MulLoop_t3Rows (calls : Calls) (d0 : BitVec 64) (E address : Nat) (hE : E ≤ 342)
    (hpack : ∀ c, c ≤ (t3Rows E).length →
      ∃ k : Code, t3MulCarried d0 (t3Rows E) c = packMag (.fin k) false ∧ k.IsMag)
    (hstage : ∀ (env : Env) (s : State) (resid : Nat) (d : BitVec 64),
      lookupName env "%e10.0.i.i" = some (.int 64 (BitVec.ofNat 64 resid)) →
      lookupName env "%d201.0.i.i" = some (.float d) →
        lookupName env "@NUMF_EL1_POW10" = some (.ptr address) ∧
        readBytes s.mem (address + min resid 22 * 8) 8
          = some (natToBytes (uitofpBits (10 ^ min resid 22)).toNat 8))
    (hno : ∀ c, c < (t3Rows E).length →
      ¬ overflowTicks * 2 ^ 1074
        ≤ F64.magTicks (F64.ofBits (t3MulCarried d0 (t3Rows E) c))
            * (10 ^ min (t3Resid E c) 22 * 2 ^ 1074)) :
    BoundLoop calls numFastBody :=
  t3MulLoopOf calls d0 (t3Rows E) (t3MulLoop_exit calls d0 E)
    (t3MulLoop_step calls d0 E address hE hpack hstage hno)

/-- **The positive loop's run at the emitted rows.** -/
theorem t3MulLoop_run_t3Rows (calls : Calls) (d0 : BitVec 64) (E address : Nat)
    (hE : E ≤ 342)
    (hpack : ∀ c, c ≤ (t3Rows E).length →
      ∃ k : Code, t3MulCarried d0 (t3Rows E) c = packMag (.fin k) false ∧ k.IsMag)
    (hstage : ∀ (env : Env) (s : State) (resid : Nat) (d : BitVec 64),
      lookupName env "%e10.0.i.i" = some (.int 64 (BitVec.ofNat 64 resid)) →
      lookupName env "%d201.0.i.i" = some (.float d) →
        lookupName env "@NUMF_EL1_POW10" = some (.ptr address) ∧
        readBytes s.mem (address + min resid 22 * 8) 8
          = some (natToBytes (uitofpBits (10 ^ min resid 22)).toNat 8))
    (hno : ∀ c, c < (t3Rows E).length →
      ¬ overflowTicks * 2 ^ 1074
        ≤ F64.magTicks (F64.ofBits (t3MulCarried d0 (t3Rows E) c))
            * (10 ^ min (t3Resid E c) 22 * 2 ^ 1074))
    (s : State) (c : Nat) (h : t3MulInv d0 (t3Rows E) (t3Rows E).length s c) (k : Nat)
    {o : Outcome}
    (hcont : ∀ (e : State), e.pc = t3LadderJoin → t3MulExitWord e →
      runFuel calls k numFastBody e = some o) :
    runFuel calls (((t3Rows E).length + 1) * 2 + k) numFastBody s = some o :=
  (t3MulLoop_t3Rows calls d0 E address hE hpack hstage hno).run_at s c h k hcont

/-! ### The negative loop's back edge, at the emitted rows

The negative loop's iteration is the mirror of the positive one at the division
block: the head's test reads the residual `-resid` as negative, the block applies
the row `min resid 22` and adds `-resid` to it, and the head is re-entered.

Two facts are the emitted code's rather than arithmetic's, and both are stated
for the whole run: the staging's table bytes at the row's address (`hstage`, at
the negative block's own registers) and the carried double's shape
(`hpack`, which here says every carried double is a positive finite code).  The
second is what refuses the row's zero test: the quotient's value is the *next*
carried double, and the row's zero test compares that value with zero — so the
positive-code assertion at `c + 1` is the whole of the refusal, and no underflow
inequality is needed beside it.  A code divided by a larger one's tick value does
round to the zero encoding, which is why the assertion is a hypothesis of the
step and not a theorem of the arithmetic. -/

/-- **The negative loop's step at the emitted rows.**  One iteration from the
head reaches the head again with the counter advanced, one row applied, within
two control steps. -/
theorem t3DivLoop_step (calls : Calls) (d0 : BitVec 64) (E address : Nat) (hE : E ≤ 342)
    (hpack : ∀ c, c ≤ (t3Rows E).length →
      ∃ k : Code, t3DivCarried d0 (t3Rows E) c = packMag (.fin k) false ∧
        k.IsMag ∧ 0 < k.ticks)
    (hstage : ∀ (env : Env) (s : State) (k : Nat) (d : BitVec 64),
      lookupName env "%e10.2.i.i" = some (.int 64 (BitVec.ofInt 64 (-(k : Int)))) →
      lookupName env "%d201.2.i.i" = some (.float d) →
        lookupName env "@NUMF_EL1_POW10" = some (.ptr address) ∧
        readBytes s.mem (address + min k 22 * 8) 8
          = some (natToBytes (uitofpBits (10 ^ min k 22)).toNat 8)) :
    ∀ (r : Nat) (s : State) (c : Nat),
      t3DivInv d0 (t3Rows E) (r + 1) s c → t3DivAtBound (t3Rows E) s c = false →
      ∃ (e' : State) (c' : Nat) (j : Nat), j ≤ 2 ∧ e'.pc = t3DivHead ∧ c < c' ∧
        t3DivInv d0 (t3Rows E) r e' c' ∧
        ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e' := by
  intro r s c hinv hbound
  obtain ⟨hpc, hcr, hpre, hc0, hcpos⟩ := hinv
  have hc_lt : c < (t3Rows E).length := by omega
  have hc_le : c ≤ (t3Rows E).length := Nat.le_of_lt hc_lt
  have hresid_ne : t3Resid E c ≠ 0 := by
    intro h0
    have htrue : decide (t3Resid E c = 0) = true := by simp [h0]
    have hfalse : decide (t3Resid E c = 0) = false := hbound
    rw [htrue] at hfalse
    exact Bool.noConfusion hfalse
  have hresid_pos : 0 < t3Resid E c := Nat.pos_of_ne_zero hresid_ne
  have hresid_le : t3Resid E c ≤ 342 := by
    have h1 : t3Resid E c = E - 22 * c := t3Rows_drop_sum hc_le
    omega
  have hresid_lt : t3Resid E c < 2 ^ 31 := by omega
  have hbit_slt : evalICmp .slt
      (BitVec.ofInt 64 (-((t3Resid E c : Nat) : Int))) (0 : BitVec 64) = (1 : BitVec 1) :=
    evalICmp_slt_ofInt_neg hresid_pos (by omega)
  have hrow : (t3Rows E)[c] = min (t3Resid E c) 22 := t3Rows_getElem_eq_min hc_lt
  -- The head's step: the carried double and the state it leaves at the row block.
  obtain ⟨d, hd_eq, hstep1⟩ :
      ∃ d : BitVec 64, d = t3DivCarried d0 (t3Rows E) c ∧
        step calls numFastBody s =
          .jump (stateAt (t3DivHeadEnv s.env
            (BitVec.ofInt 64 (-((t3Resid E c : Nat) : Int))) d)
            { s with pc := t3DivBody, pre := some t3DivHead }) := by
    rcases Nat.eq_zero_or_pos c with hc_eq | hc_gt
    · subst hc_eq
      obtain ⟨hph, hdph⟩ := hc0 rfl
      have hpre0 : s.pre = some "while.cond229.i.i.preheader" := by
        rw [hpre, ite_eq_left rfl]
      exact ⟨t3DivCarried d0 (t3Rows E) 0, rfl,
        t3_divHead_step_one_entry (calls := calls) (env := s.env) (s := s)
          hpc hpre0 hph hdph hbit_slt⟩
    · obtain ⟨hadd, hdiv⟩ := hcpos hc_gt
      have hpre0 : s.pre = some t3DivBody := by
        rw [hpre, ite_eq_right (by omega : ¬ c = 0)]
      exact ⟨t3DivCarried d0 (t3Rows E) c, rfl,
        t3_divHead_step_one (calls := calls) (env := s.env) (s := s)
          hpc hpre0 hadd hdiv hbit_slt⟩
  -- The quotient's value is the next row's carried double, so the test is refused.
  have hq : fdivBits d (uitofpBits (10 ^ min (t3Resid E c) 22))
      = t3DivCarried d0 (t3Rows E) (c + 1) := by
    rw [hd_eq, ← hrow]
    exact (t3DivCarried_succ (d0 := d0) (rows := t3Rows E) hc_lt).symm
  have hbit_body : fcmpOeqBits
      (fdivBits d (uitofpBits (10 ^ min (t3Resid E c) 22))) (0 : BitVec 64) = false := by
    rw [hq]
    obtain ⟨kk, hkk, hkkM, hkkpos⟩ := hpack (c + 1) (by omega)
    rw [hkk]
    exact fcmpOeqBits_packMag_fin_false hkkM hkkpos
  -- The staging's two facts, at the row block's own environment.
  have he1 : lookupName (t3DivHeadEnv s.env
      (BitVec.ofInt 64 (-((t3Resid E c : Nat) : Int))) d) "%e10.2.i.i"
      = some (.int 64 (BitVec.ofInt 64 (-((t3Resid E c : Nat) : Int)))) :=
    t3DivHeadEnv_e10
  have hd1 : lookupName (t3DivHeadEnv s.env
      (BitVec.ofInt 64 (-((t3Resid E c : Nat) : Int))) d) "%d201.2.i.i"
      = some (.float d) := t3DivHeadEnv_d201
  obtain ⟨htbl, hread⟩ := hstage _ _ (t3Resid E c) d he1 hd1
  let e' : State := stateAt
    (t3DivBodyEnv (t3DivHeadEnv s.env
      (BitVec.ofInt 64 (-((t3Resid E c : Nat) : Int))) d)
      (BitVec.ofInt 64 (-((t3Resid E c : Nat) : Int))) d
      (uitofpBits (10 ^ min (t3Resid E c) 22)) (t3Resid E c)
      (min (t3Resid E c) 22) address)
    { s with pc := t3DivHead, pre := some t3DivBody }
  have hstep2 : step calls numFastBody
      (stateAt (t3DivHeadEnv s.env
        (BitVec.ofInt 64 (-((t3Resid E c : Nat) : Int))) d)
        { s with pc := t3DivBody, pre := some t3DivHead }) = .jump e' := by
    exact t3_divBody_step (calls := calls)
      (env := t3DivHeadEnv s.env (BitVec.ofInt 64 (-((t3Resid E c : Nat) : Int))) d)
      (s := { s with pc := t3DivBody, pre := some t3DivHead })
      (k := t3Resid E c) (d := d)
      (p := uitofpBits (10 ^ min (t3Resid E c) 22)) (address := address)
      rfl he1 hd1 htbl hresid_pos hresid_lt hread hbit_body
  refine ⟨e', c + 1, 2, by omega, rfl, by omega, ?_, ?_⟩
  · -- the invariant at the row block's exit
    refine ⟨rfl, by omega, rfl, ?_, ?_⟩
    · intro h0
      omega
    · intro _
      refine ⟨?_, ?_⟩
      · simp only [e', stateAt]
        rw [t3DivBodyEnv_add245]
        have hsum : t3Resid E c = (t3Rows E)[c] + t3Resid E (c + 1) := by
          have hs := congrArg List.sum (t3Rows_drop_split hc_lt)
          simp only [t3Resid] at hs hrow
          rw [← hrow] at hs
          simp only [List.sum_cons] at hs
          simpa only [t3Resid] using hs
        have hi : min (t3Resid E c) 22 ≤ t3Resid E c := Nat.min_le_left _ _
        have hsub : t3Resid E c - min (t3Resid E c) 22 = t3Resid E (c + 1) := by omega
        rw [ofNat_add_ofInt_neg hi (by omega), hsub]
        rfl
      · simp only [e', stateAt]
        rw [t3DivBodyEnv_div, hq]
  · intro k
    rw [show 2 + k = 1 + (1 + k) from by omega]
    rw [runFuel_jump_prefix hstep1 (1 + k)]
    exact runFuel_jump_prefix hstep2 k

/-- **The negative loop's exit.**  At the bound the residual is zero, so the
head's test is refused and the loop leaves for `while.end253.i.i` in one control
step. -/
theorem t3DivLoop_exit (calls : Calls) (d0 : BitVec 64) (E : Nat) :
    ∀ (r : Nat) (s : State) (c : Nat),
      t3DivInv d0 (t3Rows E) r s c → t3DivAtBound (t3Rows E) s c = true →
      ∃ (e : State) (j : Nat), j ≤ 2 ∧ e.pc = "while.end253.i.i" ∧ t3DivExitWord e ∧
        ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e := by
  intro r s c hinv hbound
  obtain ⟨hpc, hcr, hpre, hc0, hcpos⟩ := hinv
  have hresid : ((t3Rows E).drop c).sum = 0 := by
    simpa only [t3DivAtBound, decide_eq_true_eq] using hbound
  have hbit : evalICmp .slt (BitVec.ofInt 64 (-((((t3Rows E).drop c).sum : Nat) : Int)))
      (0 : BitVec 64) = (0 : BitVec 1) := by
    simpa only [hresid] using evalICmp_slt_ofInt_neg_zero
  rcases Nat.eq_zero_or_pos c with hc_eq | hc_gt
  · subst hc_eq
    obtain ⟨hph, hdph⟩ := hc0 rfl
    have hpre0 : s.pre = some "while.cond229.i.i.preheader" := by
      rw [hpre, ite_eq_left rfl]
    refine ⟨stateAt (t3DivHeadEnv s.env
        (BitVec.ofInt 64 (-((((t3Rows E).drop 0).sum : Nat) : Int)))
        (t3DivCarried d0 (t3Rows E) 0))
        { s with pc := "while.end253.i.i", pre := some t3DivHead },
      1, by omega, rfl, ⟨rfl, ?_, ?_⟩, ?_⟩
    · simp only [stateAt]
      rw [t3DivHeadEnv_e10]
      simp
    · simp only [stateAt]
      rw [t3DivHeadEnv_d201]
      simp
    · intro k
      exact runFuel_jump_prefix
        (t3_divHead_step_zero_entry (calls := calls) (env := s.env) (s := s)
          hpc hpre0 hph hdph hbit) k
  · obtain ⟨hadd, hdiv⟩ := hcpos hc_gt
    have hpre0 : s.pre = some t3DivBody := by
      rw [hpre, ite_eq_right (by omega : ¬ c = 0)]
    refine ⟨stateAt (t3DivHeadEnv s.env
        (BitVec.ofInt 64 (-((((t3Rows E).drop c).sum : Nat) : Int)))
        (t3DivCarried d0 (t3Rows E) c))
        { s with pc := "while.end253.i.i", pre := some t3DivHead },
      1, by omega, rfl, ⟨rfl, ?_, ?_⟩, ?_⟩
    · simp only [stateAt]
      rw [t3DivHeadEnv_e10]
      simp
    · simp only [stateAt]
      rw [t3DivHeadEnv_d201]
      simp
    · intro k
      exact runFuel_jump_prefix
        (t3_divHead_step_zero (calls := calls) (env := s.env) (s := s)
          hpc hpre0 hadd hdiv hbit) k

/-- **The negative loop at the emitted rows.** -/
def t3DivLoop_t3Rows (calls : Calls) (d0 : BitVec 64) (E address : Nat) (hE : E ≤ 342)
    (hpack : ∀ c, c ≤ (t3Rows E).length →
      ∃ k : Code, t3DivCarried d0 (t3Rows E) c = packMag (.fin k) false ∧
        k.IsMag ∧ 0 < k.ticks)
    (hstage : ∀ (env : Env) (s : State) (k : Nat) (d : BitVec 64),
      lookupName env "%e10.2.i.i" = some (.int 64 (BitVec.ofInt 64 (-(k : Int)))) →
      lookupName env "%d201.2.i.i" = some (.float d) →
        lookupName env "@NUMF_EL1_POW10" = some (.ptr address) ∧
        readBytes s.mem (address + min k 22 * 8) 8
          = some (natToBytes (uitofpBits (10 ^ min k 22)).toNat 8)) :
    BoundLoop calls numFastBody :=
  t3DivLoopOf calls d0 (t3Rows E) (t3DivLoop_exit calls d0 E)
    (t3DivLoop_step calls d0 E address hE hpack hstage)

/-- **The negative loop's run at the emitted rows.** -/
theorem t3DivLoop_run_t3Rows (calls : Calls) (d0 : BitVec 64) (E address : Nat)
    (hE : E ≤ 342)
    (hpack : ∀ c, c ≤ (t3Rows E).length →
      ∃ k : Code, t3DivCarried d0 (t3Rows E) c = packMag (.fin k) false ∧
        k.IsMag ∧ 0 < k.ticks)
    (hstage : ∀ (env : Env) (s : State) (k : Nat) (d : BitVec 64),
      lookupName env "%e10.2.i.i" = some (.int 64 (BitVec.ofInt 64 (-(k : Int)))) →
      lookupName env "%d201.2.i.i" = some (.float d) →
        lookupName env "@NUMF_EL1_POW10" = some (.ptr address) ∧
        readBytes s.mem (address + min k 22 * 8) 8
          = some (natToBytes (uitofpBits (10 ^ min k 22)).toNat 8))
    (s : State) (c : Nat) (h : t3DivInv d0 (t3Rows E) (t3Rows E).length s c) (k : Nat)
    {o : Outcome}
    (hcont : ∀ (e : State), e.pc = "while.end253.i.i" → t3DivExitWord e →
      runFuel calls k numFastBody e = some o) :
    runFuel calls (((t3Rows E).length + 1) * 2 + k) numFastBody s = some o :=
  (t3DivLoop_t3Rows calls d0 E address hE hpack hstage).run_at s c h k hcont

/-! ### Axiom footprints -/

#print axioms t3Rows_eq_cons
#print axioms t3Rows_drop_eq
#print axioms t3Rows_drop_sum
#print axioms t3Rows_drop_split
#print axioms t3Rows_getElem_eq_min
#print axioms t3Rows_take_succ_split
#print axioms t3MulCarried_succ
#print axioms t3DivCarried_succ
#print axioms step_icmp_ugt_imm
#print axioms step_bitcastToInt
#print axioms step_ashr_imm
#print axioms step_fcmp_oeq
#print axioms evalICmp_ult_ofNat_imm
#print axioms select_ult_min
#print axioms t3_mulBody_denote
#print axioms t3_mulBody_step
#print axioms evalICmp_sgt_ofNat_zero
#print axioms magTicks_fin_le
#print axioms packMag_fin_false_le
#print axioms evalICmp_ugt_max_fin_zero
#print axioms t3RowHolds_of_pow10
#print axioms fmulBits_pack_fin
#print axioms ofNat_sub_ofNat'
#print axioms t3MulLoop_step
#print axioms evalICmp_sgt_zero
#print axioms t3MulLoop_exit
#print axioms t3MulLoop_t3Rows
#print axioms t3MulLoop_run_t3Rows
#print axioms t3DivIndex
#print axioms t3DivUlt
#print axioms select_ult_min_neg
#print axioms step_select_imm_reg_ite
#print axioms denoteCode_select_imm_reg_ite
#print axioms step_mul_imm
#print axioms denoteCode_mul_imm
#print axioms t3_divBody_find
#print axioms step_fcmp_oeq_imm
#print axioms denoteCode_fcmp_oeq_imm
#print axioms ofNat_add_ofInt_neg
#print axioms evalICmp_slt_ofInt_neg
#print axioms evalICmp_slt_ofInt_neg_zero
#print axioms packMag_fin_false_ne_zero
#print axioms fcmpOeqBits_packMag_fin_false
#print axioms t3_divBody_denote
#print axioms t3_divBody_step
#print axioms t3DivHeadEnv_e10
#print axioms t3DivHeadEnv_d201
#print axioms t3DivBodyEnv_add245
#print axioms t3DivBodyEnv_div
#print axioms t3DivLoop_step
#print axioms t3DivLoop_exit
#print axioms t3DivLoop_t3Rows
#print axioms t3DivLoop_run_t3Rows

end NumFastTier3Rows

end LeanLLVM.Refinement
