/-
`od_gap_recover`'s number unit, as a run of the pinned body.

`JsonStage2HelperIROdGapSteps` pins the body's blocks and proves the instruction
and terminator steps at its widths, and `JsonStage2HelperIROdGapRun` proves the
entry chain and the first scan.  This module proves the unit those leave on the
scan's other side: `if.end`'s number test — the byte `%7` is `'-'` or a decimal
digit, `(uint8)(%7 - 48) < 10` — and its true arm, `if.then19`.

`if.then19` stages the record for `num_fast_el1` and calls it.  What the helper
itself does is not this body's: its outcome is a named hypothesis at the emitted
call, the `CallOutcome` (`ret`, `mem`, `next`) the call environment answers with,
and nothing below reads into the helper's body.  The outcome's return word then
decides the unit's two exits: zero is the refusal, the tag-1 record at `if.then25`
with offset `%10 + %t.0.val`, and non-zero is `if.end67.critedge`'s edge to
`if.end67`.

The blocks and instruction steps are the pinned ones: every step below is `step`
at a `findBlock` pin and a `denoteCode` chain built from the `gap_*` steps of the
Steps module.  The statements are `runFuel` prefixes at the two exit states, with
the record's memory effect spelled at the refusal exit.
-/
import LeanLLVM.Refinement.JsonStage2HelperIROdGapRun

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

/-! ### One control step, from a block's run and terminator -/

/-- One control step from a block's run: `step` at a state whose program counter
finds the block, whose instructions denote to `s'`, and whose terminator is `c`.
The block is named by its three fields so that the terminator's shape reaches
the last hypothesis as a term rather than as a projection. -/
theorem gapNum_step_at_block {calls : Calls} {f : Function}
    {s s' : State} {name : String} {is : List Instr} {term : Term} {c : Ctrl}
    (hfind : f.findBlock s.pc = some ⟨name, is, term⟩)
    (hcode : denoteCode calls is s = some s')
    (hterm : execTerm s' term = c) : step calls f s = c := by
  simp only [step, hfind, hcode, hterm]

/-- A run of one control step that ends in the block's `void` return. -/
theorem gapNum_runFuel_ret_void {calls : Calls} {f : Function} {s : State} {m : Mem}
    (h : step calls f s = .ret none s) (hm : s.mem = m) :
    runFuel calls 1 f s = some (.ret none m) := by
  have h1 : (1 : Nat) = 0 + 1 := rfl
  rw [h1]
  simp only [runFuel, h]
  rw [hm]

/-! ### The number test at `if.end`

The emitted test is `%cmp11 = icmp eq i8 %7, 45`, `%8 = add i8 %7, -48`,
`%or.cond = icmp ult i8 %8, 10` and `%or.cond127 = or i1 %cmp11, %or.cond`.  The
predicate below is that first-byte test at the loaded byte: `'-'` or a decimal
digit. -/

/-- The first-byte number test: the byte is `'-'`, or its `uint8` distance from
`'0'` is below ten. -/
def gapNumberByte (v : BitVec 8) : Prop :=
  evalICmp .eq v (BitVec.ofNat 8 45) = 1#1 ∨
  evalICmp .ult (v + BitVec.ofNat 8 208) (BitVec.ofNat 8 10) = 1#1

/-- A one-bit word is `0` or `1`. -/
theorem gapNum_bv1_cases (x : BitVec 1) : x = 0#1 ∨ x = 1#1 := by
  have hx := x.isLt
  have h' : x.toNat = 0 ∨ x.toNat = 1 := by omega
  rcases h' with h' | h'
  · left
    apply BitVec.eq_of_toNat_eq
    simp [h']
  · right
    apply BitVec.eq_of_toNat_eq
    simp [h']

/-- A disjunction with a true right word is true. -/
theorem gapNum_or_one_right (x : BitVec 1) : (x ||| 1#1) = 1#1 := by
  rcases gapNum_bv1_cases x with h | h <;> subst h <;> rfl

/-- A disjunction with a true left word is true. -/
theorem gapNum_or_one_left (y : BitVec 1) : (1#1 ||| y) = 1#1 := by
  rcases gapNum_bv1_cases y with h | h <;> subst h <;> rfl

/-- The number test's two comparisons, as the `or` the terminator branches on. -/
theorem gapNumberByte_or {v : BitVec 8} (h : gapNumberByte v) :
    (evalICmp .eq v (BitVec.ofNat 8 45) |||
      evalICmp .ult (v + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1#1 := by
  rcases h with h | h
  · rw [h, gapNum_or_one_left]
  · rw [h, gapNum_or_one_right]

/-- `BitVec.ofBool` at a decided false proposition. -/
theorem gapNum_ofBool_decide_false {p : Prop} [Decidable p] (h : ¬p) :
    BitVec.ofBool (decide p) = 0#1 := by
  rw [decide_eq_false_iff_not.mpr h]
  rfl

/-- `BitVec.ofBool` at a decided true proposition. -/
theorem gapNum_ofBool_decide_true {p : Prop} [Decidable p] (h : p) :
    BitVec.ofBool (decide p) = 1#1 := by
  rw [decide_eq_true_iff.mpr h]
  rfl

/-- An equality with a word distinct from zero is false. -/
theorem gapNum_eq_zero_zero {w : Nat} {x : BitVec w} (h : x ≠ 0) :
    evalICmp .eq x (BitVec.ofNat w 0) = 0#1 := by
  change BitVec.ofBool (decide (x = (0 : BitVec w))) = 0#1
  exact gapNum_ofBool_decide_false h

/-- An equality with zero is true at a word that is zero. -/
theorem gapNum_eq_zero_one {w : Nat} {x : BitVec w} (h : x = 0) :
    evalICmp .eq x (BitVec.ofNat w 0) = 1#1 := by
  change BitVec.ofBool (decide (x = (0 : BitVec w))) = 1#1
  exact gapNum_ofBool_decide_true h

/-- A lifetime marker's step: it leaves the state it is called on, so the block's
run passes through it without a cell or a write. -/
theorem gapNum_denote_lifetime (nf : Calls) (env : Env) (s : State)
    (callee : String)
    (h : callee = "llvm.lifetime.start.p0" ∨ callee = "llvm.lifetime.end.p0")
    (o1 o2 : Operand) {v1 v2 : Value}
    (h1 : evalOperand (stateAt env s) o1 = some v1)
    (h2 : evalOperand (stateAt env s) o2 = some v2) (is : List Instr) :
    denoteCode (stage2Calls nf) (.callVoid callee [(Ty.int 64, o1), (Ty.ptr, o2)] :: is)
        (stateAt env s) = denoteCode (stage2Calls nf) is (stateAt env s) := by
  rcases h with rfl | rfl
  · exact gap_denote_callVoid2 (calls := stage2Calls nf) env s "llvm.lifetime.start.p0"
      o1 o2 (r := ⟨.int 1 0, s.mem, s.next⟩) h1 h2 (by rfl) is
  · exact gap_denote_callVoid2 (calls := stage2Calls nf) env s "llvm.lifetime.end.p0"
      o1 o2 (r := ⟨.int 1 0, s.mem, s.next⟩) h1 h2 (by rfl) is

/-! ### The blocks' environments, as named builders -/

/-- `if.end`'s cells: the loaded byte, its two tests and the `or`, and the
addressed byte. -/
def gapNumIfEndEnv (env : Env) (base se : Nat) (v7 : BitVec 8) : Env :=
  cells
    [("%or.cond127", .int 1 (evalICmp .eq v7 (BitVec.ofNat 8 45) |||
        evalICmp .ult (v7 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10))),
     ("%or.cond", .int 1 (evalICmp .ult (v7 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10))),
     ("%8", .int 8 (v7 + BitVec.ofNat 8 208)),
     ("%cmp11", .int 1 (evalICmp .eq v7 (BitVec.ofNat 8 45))),
     ("%7", .int 8 v7),
     ("%arrayidx9", .ptr (base + se))] env

/-- `if.then19`'s cells: the token length, the call's returned word and its test
against zero. -/
def gapNumThen19Env (env : Env) (t ee : BitVec 64) (v32 : BitVec 32) : Env :=
  cells
    [("%tobool24.not.not", .int 1 (evalICmp .eq v32 (BitVec.ofNat 32 0))),
     ("%call23", .int 32 v32),
     ("%sub", .int 64 (ee - t))] env

/-- `if.then25`'s memory: the tag-1 refusal record at the offset `%10 +
%t.0.val`. -/
def gapNumThen25Mem (mem : Mem) (r : Nat) (w t : BitVec 64) : Mem :=
  writeBytes
    (writeBytes (writeBytes mem r (natToBytes 0 4)) (r + 8)
      (natToBytes (w + t).toNat 8))
    (r + 16) (natToBytes 1 8)

/-- `if.then25`'s cells: the record pointer word, the index slot's word, the
summed offset and its three stores. -/
def gapNumThen25Env (env : Env) (cur r : Nat) (w t : BitVec 64) : Env :=
  cells
    [("%msg2.i", .ptr (r + 16)),
     ("%off1.i", .ptr (r + 8)),
     ("%add", .int 64 (w + t)),
     ("%10", .int 64 w),
     ("%9", .ptr r),
     ("%e", .ptr (cur + 1112))] env

/-- A state after a block's terminator: the program counter, its predecessor,
the memory and the allocator cursor.  Named so a step's conclusion can spell it
in argument position. -/
def gapNumJump (s : State) (pc lpc : String) (mem : Mem) (nxt : Nat) : State :=
  { s with pc := pc, pre := some lpc, mem := mem, next := nxt }

/-- The environment the number unit's refusal leaves: the record's cells over the
number test's and the call's. -/
def gapNumberRefusalEnv (env : Env) (base se : Nat) (v7 : BitVec 8)
    (t ee : BitVec 64) (v32 : BitVec 32) (cur r : Nat) (w : BitVec 64) : Env :=
  gapNumThen25Env (gapNumThen19Env (gapNumIfEndEnv env base se v7) t ee v32)
    cur r w t

/-- The state the number unit's refusal leaves: `cleanup82`, carrying the tag-1
record's memory. -/
def gapNumberRefusalState (s : State) (mem' : Mem) (r : Nat) (w t : BitVec 64)
    (next' : Nat) : State :=
  { s with pc := "cleanup82", pre := some "if.then25",
           mem := gapNumThen25Mem mem' r w t, next := next' }

/-- The environment the number unit's accept leaves: the call's cells over the
number test's. -/
def gapNumberAcceptEnv (env : Env) (base se : Nat) (v7 : BitVec 8)
    (t ee : BitVec 64) (v32 : BitVec 32) : Env :=
  gapNumThen19Env (gapNumIfEndEnv env base se v7) t ee v32

/-- The state the number unit's accept leaves: `if.end67`'s entry, memory
unchanged from the helper call. -/
def gapNumberAcceptState (s : State) (mem' : Mem) (next' : Nat) : State :=
  { s with pc := "if.end67", pre := some "if.end67.critedge",
           mem := mem', next := next' }

/-! ### `if.end`: the number test -/

/-- `if.end` on the number test's true arm: the byte at `%arrayidx9`, the minus
test, the digit test and their `or`, with the branch into `if.then19`. -/
theorem gapNum_step_ifEnd_num {calls : Calls} {env : Env} {s : State}
    {base se : Nat} {t : BitVec 64} {v7 : BitVec 8}
    (hpc : s.pc = "if.end")
    (h0 : lookupName env "%0" = some (.ptr base))
    (ht : lookupName env "%t.0.val" = some (.int 64 t))
    (hse : (t.signExtend 64).toNat = se) (hse63 : se < 2 ^ 63)
    (hbyte : readBytes s.mem (base + se) 1 = some (natToBytes v7.toNat 1))
    (hbit : (evalICmp .eq v7 (BitVec.ofNat 8 45) |||
      evalICmp .ult (v7 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1#1) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt (gapNumIfEndEnv env base se v7)
        { s with pc := "if.then19", pre := some "if.end" }) := by
  let env' : Env := gapNumIfEndEnv env base se v7
  have hcode : denoteCode calls odGapRecoverIfEndInstrs (stateAt env s) =
      some (stateAt env' s) := by
    unfold odGapRecoverIfEndInstrs
    refine Eq.trans (denoteCode_gep8_reg calls env s "%arrayidx9" "%0" "%t.0.val"
      h0 ht (by rw [hse]; exact hse63) _) ?_
    rw [hse]
    refine Eq.trans (gap_denote_load8 calls
      (("%arrayidx9", .ptr (base + se)) :: env) s "%7" "%arrayidx9"
      (by block_lk) hbyte _) ?_
    refine Eq.trans (gap_denote_icmp_eq_imm calls
      (("%7", .int 8 v7) :: ("%arrayidx9", .ptr (base + se)) :: env) s
      "%cmp11" "%7" (by block_lk) _) ?_
    refine Eq.trans (gap_denote_add_imm calls
      (("%cmp11", .int 1 (evalICmp .eq v7 (BitVec.ofNat 8 45))) ::
        ("%7", .int 8 v7) :: ("%arrayidx9", .ptr (base + se)) :: env) s
      "%8" "%7" (by block_lk) _) ?_
    refine Eq.trans (gap_denote_icmp_ult_imm calls
      (("%8", .int 8 (v7 + BitVec.ofNat 8 208)) ::
        ("%cmp11", .int 1 (evalICmp .eq v7 (BitVec.ofNat 8 45))) ::
        ("%7", .int 8 v7) :: ("%arrayidx9", .ptr (base + se)) :: env) s
      "%or.cond" "%8" (by block_lk) _) ?_
    refine Eq.trans (gap_denote_or_reg calls
      (("%or.cond", .int 1 (evalICmp .ult (v7 + BitVec.ofNat 8 208)
          (BitVec.ofNat 8 10))) ::
        ("%8", .int 8 (v7 + BitVec.ofNat 8 208)) ::
        ("%cmp11", .int 1 (evalICmp .eq v7 (BitVec.ofNat 8 45))) ::
        ("%7", .int 8 v7) :: ("%arrayidx9", .ptr (base + se)) :: env) s
      "%or.cond127" "%cmp11" "%or.cond" (by block_lk) (by block_lk) []) ?_
    rfl
  refine gapNum_step_at_block (f := odGapRecoverBody) (s := stateAt env s)
    (s' := stateAt env' s) (name := "if.end") (is := odGapRecoverIfEndInstrs)
    (term := Term.condbr (Operand.reg "%or.cond127") "if.then19" "if.else")
    (c := .jump (stateAt env' (gapNumJump s "if.then19" "if.end" s.mem s.next)))
    ?_ ?_ ?_
  · simpa only [stateAt, hpc] using odGapRecover_findBlock_if_end
  · exact hcode
  · rw [gap_execTerm_condbr_one
      (by simp only [env', gapNumIfEndEnv, cells, stateAt, evalOperand, hbit]
          rw [lookupName_cons_self]
          rfl)]
    simp only [stateAt, hpc, gapNumJump]

/-! ### `if.then19`: the record's staging and the helper call -/

/-- `if.then19` with the helper returning zero: the two lifetime markers, the
token length, the `num_fast_el1` call whose `CallOutcome` is the hypothesis
`hcall`, and the branch into `if.then25`. -/
theorem gapNum_step_ifThen19_zero {nf : Calls} {env : Env} {s : State}
    {a9 d ei : Nat} {t ee : BitVec 64} {v32 : BitVec 32}
    {mem' : Mem} {next' : Nat}
    (hpc : s.pc = "if.then19")
    (hd : lookupName env "%d" = some (.ptr d))
    (hei : lookupName env "%ei" = some (.ptr ei))
    (hee : lookupName env "%ee.0.lcssa" = some (.int 64 ee))
    (ht : lookupName env "%t.0.val" = some (.int 64 t))
    (harr : lookupName env "%arrayidx9" = some (.ptr a9))
    (hcall : stage2Calls nf "num_fast_el1"
      [.ptr a9, .int 64 (ee - t), .ptr d, .ptr ei] s.mem s.next =
        some ⟨.int 32 v32, mem', next'⟩)
    (hv32 : v32 = 0#32) :
    step (stage2Calls nf) odGapRecoverBody (stateAt env s) =
      .jump (stateAt (gapNumThen19Env env t ee v32)
        { s with pc := "if.then25", pre := some "if.then19",
                 mem := mem', next := next' }) := by
  let env' : Env := gapNumThen19Env env t ee v32
  have hcode : denoteCode (stage2Calls nf) odGapRecoverIfThen19Instrs
      (stateAt env s) = some (stateAt env' { s with mem := mem', next := next' }) := by
    let s1 : State := { s with mem := mem', next := next' }
    unfold odGapRecoverIfThen19Instrs
    refine Eq.trans (gapNum_denote_lifetime (nf := nf) env s "llvm.lifetime.start.p0"
      (Or.inl rfl) (.imm (.int 64 0x0000000000000008#64)) (.reg "%d")
      rfl (by exact evalOperand_reg_of _ _ _ _ (by block_lk)) _) ?_
    refine Eq.trans (gapNum_denote_lifetime (nf := nf) env s "llvm.lifetime.start.p0"
      (Or.inl rfl) (.imm (.int 64 0x0000000000000008#64)) (.reg "%ei")
      rfl (by exact evalOperand_reg_of _ _ _ _ (by block_lk)) _) ?_
    refine Eq.trans (denoteCode_sub_reg (calls := stage2Calls nf) env s "%sub"
      "%ee.0.lcssa" "%t.0.val" (by block_lk) (by block_lk) _) ?_
    refine Eq.trans (gap_denote_call4 (calls := stage2Calls nf)
      (("%sub", .int 64 (ee - t)) :: env) s "%call23"
      "num_fast_el1" (.reg "%arrayidx9") (.reg "%sub") (.reg "%d") (.reg "%ei")
      (r := ⟨.int 32 v32, mem', next'⟩)
      (by exact evalOperand_reg_of _ _ _ _ (by block_lk))
      (by exact evalOperand_reg_of _ _ _ _ (by block_lk))
      (by exact evalOperand_reg_of _ _ _ _ (by block_lk))
      (by exact evalOperand_reg_of _ _ _ _ (by block_lk)) hcall _) ?_
    refine Eq.trans (gap_denote_icmp_eq_imm (calls := stage2Calls nf)
      (("%call23", .int 32 v32) :: ("%sub", .int 64 (ee - t)) :: env) s1
      "%tobool24.not.not" "%call23" (by block_lk) []) ?_
    rfl
  refine gapNum_step_at_block (f := odGapRecoverBody) (s := stateAt env s)
    (s' := stateAt env' { s with mem := mem', next := next' })
    (name := "if.then19") (is := odGapRecoverIfThen19Instrs)
    (term := Term.condbr (Operand.reg "%tobool24.not.not") "if.then25"
      "if.end67.critedge")
    (c := .jump (stateAt env' (gapNumJump s "if.then25" "if.then19" mem' next')))
    ?_ ?_ ?_
  · simpa only [stateAt, hpc] using odGapRecover_findBlock_if_then19
  · exact hcode
  · rw [gap_execTerm_condbr_one
      (by simp only [env', gapNumThen19Env, cells, stateAt, evalOperand,
            gapNum_eq_zero_one hv32]
          rw [lookupName_cons_self]
          rfl)]
    simp only [stateAt, hpc, gapNumJump]

/-- `if.then19` with the helper returning a non-zero word: the same staging and
the branch into `if.end67.critedge`. -/
theorem gapNum_step_ifThen19_nonzero {nf : Calls} {env : Env} {s : State}
    {a9 d ei : Nat} {t ee : BitVec 64} {v32 : BitVec 32}
    {mem' : Mem} {next' : Nat}
    (hpc : s.pc = "if.then19")
    (hd : lookupName env "%d" = some (.ptr d))
    (hei : lookupName env "%ei" = some (.ptr ei))
    (hee : lookupName env "%ee.0.lcssa" = some (.int 64 ee))
    (ht : lookupName env "%t.0.val" = some (.int 64 t))
    (harr : lookupName env "%arrayidx9" = some (.ptr a9))
    (hcall : stage2Calls nf "num_fast_el1"
      [.ptr a9, .int 64 (ee - t), .ptr d, .ptr ei] s.mem s.next =
        some ⟨.int 32 v32, mem', next'⟩)
    (hv32 : v32 ≠ 0#32) :
    step (stage2Calls nf) odGapRecoverBody (stateAt env s) =
      .jump (stateAt (gapNumThen19Env env t ee v32)
        { s with pc := "if.end67.critedge", pre := some "if.then19",
                 mem := mem', next := next' }) := by
  let env' : Env := gapNumThen19Env env t ee v32
  have hcode : denoteCode (stage2Calls nf) odGapRecoverIfThen19Instrs
      (stateAt env s) = some (stateAt env' { s with mem := mem', next := next' }) := by
    let s1 : State := { s with mem := mem', next := next' }
    unfold odGapRecoverIfThen19Instrs
    refine Eq.trans (gapNum_denote_lifetime (nf := nf) env s "llvm.lifetime.start.p0"
      (Or.inl rfl) (.imm (.int 64 0x0000000000000008#64)) (.reg "%d")
      rfl (by exact evalOperand_reg_of _ _ _ _ (by block_lk)) _) ?_
    refine Eq.trans (gapNum_denote_lifetime (nf := nf) env s "llvm.lifetime.start.p0"
      (Or.inl rfl) (.imm (.int 64 0x0000000000000008#64)) (.reg "%ei")
      rfl (by exact evalOperand_reg_of _ _ _ _ (by block_lk)) _) ?_
    refine Eq.trans (denoteCode_sub_reg (calls := stage2Calls nf) env s "%sub"
      "%ee.0.lcssa" "%t.0.val" (by block_lk) (by block_lk) _) ?_
    refine Eq.trans (gap_denote_call4 (calls := stage2Calls nf)
      (("%sub", .int 64 (ee - t)) :: env) s "%call23"
      "num_fast_el1" (.reg "%arrayidx9") (.reg "%sub") (.reg "%d") (.reg "%ei")
      (r := ⟨.int 32 v32, mem', next'⟩)
      (by exact evalOperand_reg_of _ _ _ _ (by block_lk))
      (by exact evalOperand_reg_of _ _ _ _ (by block_lk))
      (by exact evalOperand_reg_of _ _ _ _ (by block_lk))
      (by exact evalOperand_reg_of _ _ _ _ (by block_lk)) hcall _) ?_
    refine Eq.trans (gap_denote_icmp_eq_imm (calls := stage2Calls nf)
      (("%call23", .int 32 v32) :: ("%sub", .int 64 (ee - t)) :: env) s1
      "%tobool24.not.not" "%call23" (by block_lk) []) ?_
    rfl
  refine gapNum_step_at_block (f := odGapRecoverBody) (s := stateAt env s)
    (s' := stateAt env' { s with mem := mem', next := next' })
    (name := "if.then19") (is := odGapRecoverIfThen19Instrs)
    (term := Term.condbr (Operand.reg "%tobool24.not.not") "if.then25"
      "if.end67.critedge")
    (c := .jump (stateAt env' (gapNumJump s "if.end67.critedge" "if.then19" mem' next')))
    ?_ ?_ ?_
  · simpa only [stateAt, hpc] using odGapRecover_findBlock_if_then19
  · exact hcode
  · rw [gap_execTerm_condbr_zero
      (by simp only [env', gapNumThen19Env, cells, stateAt, evalOperand,
            gapNum_eq_zero_zero hv32]
          rw [lookupName_cons_self]
          rfl)]
    simp only [stateAt, hpc, gapNumJump]

/-! ### The two exits -/

/-- `if.then25`: the refusal record — kind `0`, offset `%10 + %t.0.val`, tag
`1` — then the two lifetime markers and the edge to `cleanup82`. -/
theorem gapNum_step_ifThen25 {nf : Calls} {env : Env} {s : State}
    {cur r ei d : Nat} {w t : BitVec 64}
    (hpc : s.pc = "if.then25")
    (hc : lookupName env "%c" = some (.ptr cur))
    (ht : lookupName env "%t.0.val" = some (.int 64 t))
    (hei : lookupName env "%ei" = some (.ptr ei))
    (hd : lookupName env "%d" = some (.ptr d))
    (hrec : readBytes s.mem (cur + 1112) 8 = some (natToBytes r 8)) (hr64 : r < 2 ^ 64)
    (h10 : readBytes s.mem ei 8 = some (natToBytes w.toNat 8)) :
    step (stage2Calls nf) odGapRecoverBody (stateAt env s) =
      .jump (stateAt (gapNumThen25Env env cur r w t)
        { s with mem := gapNumThen25Mem s.mem r w t,
                 pc := "cleanup82", pre := some "if.then25" }) := by
  let env' : Env := gapNumThen25Env env cur r w t
  have hcode : denoteCode (stage2Calls nf) odGapRecoverIfThen25Instrs
      (stateAt env s) = some (stateAt env' { s with mem := gapNumThen25Mem s.mem r w t }) := by
    let s1 : State := { s with mem := writeBytes s.mem r (natToBytes (0#32).toNat 4) }
    let s2 : State :=
      { s1 with mem := writeBytes s1.mem (r + 8) (natToBytes (w + t).toNat 8) }
    let s3 : State :=
      { s2 with mem := writeBytes s2.mem (r + 16) (natToBytes (1#64).toNat 8) }
    unfold odGapRecoverIfThen25Instrs
    refine Eq.trans (gap_denote_gep8_imm (calls := stage2Calls nf) env s "%e" "%c"
      (0x0000000000000458#64) (by block_lk) (by decide) _) ?_
    have hge : ((0x0000000000000458#64).signExtend 64).toNat = 1112 := by decide
    rw [hge]
    refine Eq.trans (gap_denote_loadPtr (calls := stage2Calls nf)
      (("%e", .ptr (cur + 1112)) :: env) s "%9" "%e" (by block_lk) hrec hr64 _) ?_
    refine Eq.trans (denoteCode_load64 (calls := stage2Calls nf)
      (("%9", .ptr r) :: ("%e", .ptr (cur + 1112)) :: env) s "%10" "%ei"
      (by block_lk) h10 _) ?_
    refine Eq.trans (denoteCode_add_reg (calls := stage2Calls nf)
      (("%10", .int 64 w) :: ("%9", .ptr r) ::
        ("%e", .ptr (cur + 1112)) :: env) s "%add" "%10" "%t.0.val"
      (by block_lk) (by block_lk) _) ?_
    refine Eq.trans (gap_denote_store_imm32 (calls := stage2Calls nf)
      (("%add", .int 64 (w + t)) :: ("%10", .int 64 w) :: ("%9", .ptr r) ::
        ("%e", .ptr (cur + 1112)) :: env) s "%9" (by block_lk) _) ?_
    refine Eq.trans (gap_denote_gep8_imm (calls := stage2Calls nf)
      (("%add", .int 64 (w + t)) :: ("%10", .int 64 w) :: ("%9", .ptr r) ::
        ("%e", .ptr (cur + 1112)) :: env) s1
      "%off1.i" "%9" (0x0000000000000008#64) (by block_lk) (by decide) _) ?_
    rw [gap_se8]
    refine Eq.trans (denoteCode_store64 (calls := stage2Calls nf)
      (("%off1.i", .ptr (r + 8)) :: ("%add", .int 64 (w + t)) ::
        ("%10", .int 64 w) :: ("%9", .ptr r) ::
        ("%e", .ptr (cur + 1112)) :: env) s1 "%add" "%off1.i"
      (by block_lk) (by block_lk) _) ?_
    refine Eq.trans (gap_denote_gep8_imm (calls := stage2Calls nf)
      (("%off1.i", .ptr (r + 8)) :: ("%add", .int 64 (w + t)) ::
        ("%10", .int 64 w) :: ("%9", .ptr r) ::
        ("%e", .ptr (cur + 1112)) :: env) s2
      "%msg2.i" "%9" (0x0000000000000010#64) (by block_lk) (by decide) _) ?_
    rw [gap_se16]
    refine Eq.trans (gap_denote_store_imm64 (calls := stage2Calls nf)
      (("%msg2.i", .ptr (r + 16)) :: ("%off1.i", .ptr (r + 8)) ::
        ("%add", .int 64 (w + t)) :: ("%10", .int 64 w) :: ("%9", .ptr r) ::
        ("%e", .ptr (cur + 1112)) :: env) s2 "%msg2.i" (by block_lk) _) ?_
    refine Eq.trans (gapNum_denote_lifetime (nf := nf)
      (("%msg2.i", .ptr (r + 16)) :: ("%off1.i", .ptr (r + 8)) ::
        ("%add", .int 64 (w + t)) :: ("%10", .int 64 w) :: ("%9", .ptr r) ::
        ("%e", .ptr (cur + 1112)) :: env) s3 "llvm.lifetime.end.p0"
      (Or.inr rfl) (.imm (.int 64 0x0000000000000008#64)) (.reg "%ei")
      rfl (by exact evalOperand_reg_of _ _ _ _ (by block_lk)) _) ?_
    refine Eq.trans (gapNum_denote_lifetime (nf := nf)
      (("%msg2.i", .ptr (r + 16)) :: ("%off1.i", .ptr (r + 8)) ::
        ("%add", .int 64 (w + t)) :: ("%10", .int 64 w) :: ("%9", .ptr r) ::
        ("%e", .ptr (cur + 1112)) :: env) s3 "llvm.lifetime.end.p0"
      (Or.inr rfl) (.imm (.int 64 0x0000000000000008#64)) (.reg "%d")
      rfl (by exact evalOperand_reg_of _ _ _ _ (by block_lk)) []) ?_
    rfl
  refine gapNum_step_at_block (f := odGapRecoverBody) (s := stateAt env s)
    (s' := stateAt env' { s with mem := gapNumThen25Mem s.mem r w t })
    (name := "if.then25") (is := odGapRecoverIfThen25Instrs) (term := Term.br "cleanup82")
    (c := .jump (stateAt env' (gapNumJump s "cleanup82" "if.then25"
      (gapNumThen25Mem s.mem r w t) s.next))) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using odGapRecover_findBlock_if_then25
  · exact hcode
  · rw [gap_execTerm_br]
    simp only [stateAt, hpc, gapNumJump]

/-- `if.end67.critedge`: the two lifetime markers and the edge to `if.end67`. -/
theorem gapNum_step_critedge {nf : Calls} {env : Env} {s : State} {d ei : Nat}
    (hpc : s.pc = "if.end67.critedge")
    (hd : lookupName env "%d" = some (.ptr d))
    (hei : lookupName env "%ei" = some (.ptr ei)) :
    step (stage2Calls nf) odGapRecoverBody (stateAt env s) =
      .jump (stateAt env
        { s with pc := "if.end67", pre := some "if.end67.critedge" }) := by
  have hcode : denoteCode (stage2Calls nf) odGapRecoverIfEnd67CritedgeInstrs
      (stateAt env s) = some (stateAt env s) := by
    unfold odGapRecoverIfEnd67CritedgeInstrs
    refine Eq.trans (gapNum_denote_lifetime (nf := nf) env s "llvm.lifetime.end.p0"
      (Or.inr rfl) (.imm (.int 64 0x0000000000000008#64)) (.reg "%ei")
      rfl (by exact evalOperand_reg_of _ _ _ _ (by block_lk)) _) ?_
    refine Eq.trans (gapNum_denote_lifetime (nf := nf) env s "llvm.lifetime.end.p0"
      (Or.inr rfl) (.imm (.int 64 0x0000000000000008#64)) (.reg "%d")
      rfl (by exact evalOperand_reg_of _ _ _ _ (by block_lk)) []) ?_
    rfl
  refine gapNum_step_at_block (f := odGapRecoverBody) (s := stateAt env s)
    (s' := stateAt env s) (name := "if.end67.critedge")
    (is := odGapRecoverIfEnd67CritedgeInstrs) (term := Term.br "if.end67")
    (c := .jump (stateAt env
      (gapNumJump s "if.end67" "if.end67.critedge" s.mem s.next))) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using odGapRecover_findBlock_if_end67_critedge
  · exact hcode
  · rw [gap_execTerm_br]
    simp only [stateAt, hpc, gapNumJump]

/-! ### The unit's two runs -/

/-- **The number path's refusal run.**  From `if.end` with the number test true
and `num_fast_el1` returning zero, the body reaches `cleanup82` in three control
steps, leaving the tag-1 record at the offset `%10 + %t.0.val`. -/
theorem gap_number_refusal_run {nf : Calls} {env : Env} {s : State}
    {cur base d ei : Nat} {t ee : BitVec 64} {se : Nat} {v7 : BitVec 8}
    {v32 : BitVec 32} {mem' : Mem} {next' : Nat} {r : Nat} {w : BitVec 64}
    (hpc : s.pc = "if.end")
    (h0 : lookupName env "%0" = some (.ptr base))
    (ht : lookupName env "%t.0.val" = some (.int 64 t))
    (hee : lookupName env "%ee.0.lcssa" = some (.int 64 ee))
    (hd : lookupName env "%d" = some (.ptr d))
    (hei : lookupName env "%ei" = some (.ptr ei))
    (hc : lookupName env "%c" = some (.ptr cur))
    (hse : (t.signExtend 64).toNat = se) (hse63 : se < 2 ^ 63)
    (hbyte : readBytes s.mem (base + se) 1 = some (natToBytes v7.toNat 1))
    (hnum : gapNumberByte v7)
    (hcall : stage2Calls nf "num_fast_el1"
      [.ptr (base + se), .int 64 (ee - t), .ptr d, .ptr ei] s.mem s.next =
        some ⟨.int 32 v32, mem', next'⟩)
    (hv32 : v32 = 0#32)
    (hrec : readBytes mem' (cur + 1112) 8 = some (natToBytes r 8)) (hr64 : r < 2 ^ 64)
    (h10 : readBytes mem' ei 8 = some (natToBytes w.toNat 8))
    (k : Nat) :
    runFuel (stage2Calls nf) (3 + k) odGapRecoverBody (stateAt env s) =
      runFuel (stage2Calls nf) k odGapRecoverBody
        (stateAt (gapNumberRefusalEnv env base se v7 t ee v32 cur r w)
          (gapNumberRefusalState s mem' r w t next')) := by
  let env1 : Env := gapNumIfEndEnv env base se v7
  let s1 : State := { s with pc := "if.then19", pre := some "if.end" }
  let env2 : Env := gapNumThen19Env env1 t ee v32
  let s2 : State :=
    { s1 with pc := "if.then25", pre := some "if.then19", mem := mem', next := next' }
  let env3 : Env := gapNumberRefusalEnv env base se v7 t ee v32 cur r w
  let s3 : State := gapNumberRefusalState s mem' r w t next'
  have h1 : step (stage2Calls nf) odGapRecoverBody (stateAt env s) =
      .jump (stateAt env1 s1) :=
    gapNum_step_ifEnd_num (calls := stage2Calls nf) hpc h0 ht hse hse63 hbyte
      (gapNumberByte_or hnum)
  have h2 : step (stage2Calls nf) odGapRecoverBody (stateAt env1 s1) =
      .jump (stateAt env2 s2) := by
    have hd' : lookupName env1 "%d" = some (.ptr d) := by
      simp only [env1, gapNumIfEndEnv]; block_lk
    have hei' : lookupName env1 "%ei" = some (.ptr ei) := by
      simp only [env1, gapNumIfEndEnv]; block_lk
    have hee' : lookupName env1 "%ee.0.lcssa" = some (.int 64 ee) := by
      simp only [env1, gapNumIfEndEnv]; block_lk
    have ht' : lookupName env1 "%t.0.val" = some (.int 64 t) := by
      simp only [env1, gapNumIfEndEnv]; block_lk
    have harr' : lookupName env1 "%arrayidx9" = some (.ptr (base + se)) := by
      simp only [env1, gapNumIfEndEnv]; block_lk
    exact gapNum_step_ifThen19_zero (nf := nf) (s := s1) (by simp only [s1])
      hd' hei' hee' ht' harr' hcall hv32
  have h3 : step (stage2Calls nf) odGapRecoverBody (stateAt env2 s2) =
      .jump (stateAt env3 s3) := by
    have hc' : lookupName env2 "%c" = some (.ptr cur) := by
      simp only [env2, env1, gapNumThen19Env, gapNumIfEndEnv]; block_lk
    have ht' : lookupName env2 "%t.0.val" = some (.int 64 t) := by
      simp only [env2, env1, gapNumThen19Env, gapNumIfEndEnv]; block_lk
    have hei' : lookupName env2 "%ei" = some (.ptr ei) := by
      simp only [env2, env1, gapNumThen19Env, gapNumIfEndEnv]; block_lk
    have hd' : lookupName env2 "%d" = some (.ptr d) := by
      simp only [env2, env1, gapNumThen19Env, gapNumIfEndEnv]; block_lk
    have hrec' : readBytes s2.mem (cur + 1112) 8 = some (natToBytes r 8) := by
      simpa only [s2, s1] using hrec
    have h10' : readBytes s2.mem ei 8 = some (natToBytes w.toNat 8) := by
      simpa only [s2, s1] using h10
    exact gapNum_step_ifThen25 (nf := nf) (s := s2) (by simp only [s2]) hc' ht' hei'
      hd' hrec' hr64 h10'
  rw [show 3 + k = 1 + (1 + (1 + k)) from by omega,
    runFuel_jump_prefix h1 (1 + (1 + k)), runFuel_jump_prefix h2 (1 + k),
    runFuel_jump_prefix h3 k]

/-- **The number path's completion.**  The refusal's `cleanup82` returns `void`,
so the same run is a completed outcome carrying the tag-1 record's memory. -/
theorem gap_number_refusal_outcome {nf : Calls} {env : Env} {s : State}
    {cur base d ei : Nat} {t ee : BitVec 64} {se : Nat} {v7 : BitVec 8}
    {v32 : BitVec 32} {mem' : Mem} {next' : Nat} {r : Nat} {w : BitVec 64}
    (hpc : s.pc = "if.end")
    (h0 : lookupName env "%0" = some (.ptr base))
    (ht : lookupName env "%t.0.val" = some (.int 64 t))
    (hee : lookupName env "%ee.0.lcssa" = some (.int 64 ee))
    (hd : lookupName env "%d" = some (.ptr d))
    (hei : lookupName env "%ei" = some (.ptr ei))
    (hc : lookupName env "%c" = some (.ptr cur))
    (hse : (t.signExtend 64).toNat = se) (hse63 : se < 2 ^ 63)
    (hbyte : readBytes s.mem (base + se) 1 = some (natToBytes v7.toNat 1))
    (hnum : gapNumberByte v7)
    (hcall : stage2Calls nf "num_fast_el1"
      [.ptr (base + se), .int 64 (ee - t), .ptr d, .ptr ei] s.mem s.next =
        some ⟨.int 32 v32, mem', next'⟩)
    (hv32 : v32 = 0#32)
    (hrec : readBytes mem' (cur + 1112) 8 = some (natToBytes r 8)) (hr64 : r < 2 ^ 64)
    (h10 : readBytes mem' ei 8 = some (natToBytes w.toNat 8)) :
    runFuel (stage2Calls nf) (3 + 1) odGapRecoverBody (stateAt env s) =
      some (.ret none (gapNumThen25Mem mem' r w t)) := by
  let ex : State :=
    stateAt (gapNumberRefusalEnv env base se v7 t ee v32 cur r w)
      (gapNumberRefusalState s mem' r w t next')
  have hst : step (stage2Calls nf) odGapRecoverBody ex = .ret none ex :=
    gap_step_cleanup82 (calls := stage2Calls nf)
      (env := gapNumberRefusalEnv env base se v7 t ee v32 cur r w)
      (s := gapNumberRefusalState s mem' r w t next') (by rfl)
  have hstep : runFuel (stage2Calls nf) 1 odGapRecoverBody ex =
      some (.ret none (gapNumThen25Mem mem' r w t)) :=
    gapNum_runFuel_ret_void hst (by rfl)
  have h := gap_number_refusal_run (nf := nf) (env := env) (s := s)
    hpc h0 ht hee hd hei hc hse hse63 hbyte hnum hcall hv32 hrec hr64 h10 (k := 1)
  exact h.trans hstep

/-- **The number path's accept run.**  From `if.end` with the number test true
and `num_fast_el1` returning a non-zero word, the body reaches `if.end67`'s entry
in three control steps, memory unchanged from the call. -/
theorem gap_number_accept_run {nf : Calls} {env : Env} {s : State}
    {base d ei : Nat} {t ee : BitVec 64} {se : Nat} {v7 : BitVec 8}
    {v32 : BitVec 32} {mem' : Mem} {next' : Nat}
    (hpc : s.pc = "if.end")
    (h0 : lookupName env "%0" = some (.ptr base))
    (ht : lookupName env "%t.0.val" = some (.int 64 t))
    (hee : lookupName env "%ee.0.lcssa" = some (.int 64 ee))
    (hd : lookupName env "%d" = some (.ptr d))
    (hei : lookupName env "%ei" = some (.ptr ei))
    (hse : (t.signExtend 64).toNat = se) (hse63 : se < 2 ^ 63)
    (hbyte : readBytes s.mem (base + se) 1 = some (natToBytes v7.toNat 1))
    (hnum : gapNumberByte v7)
    (hcall : stage2Calls nf "num_fast_el1"
      [.ptr (base + se), .int 64 (ee - t), .ptr d, .ptr ei] s.mem s.next =
        some ⟨.int 32 v32, mem', next'⟩)
    (hv32 : v32 ≠ 0#32)
    (k : Nat) :
    runFuel (stage2Calls nf) (3 + k) odGapRecoverBody (stateAt env s) =
      runFuel (stage2Calls nf) k odGapRecoverBody
        (stateAt (gapNumberAcceptEnv env base se v7 t ee v32)
          (gapNumberAcceptState s mem' next')) := by
  let env1 : Env := gapNumIfEndEnv env base se v7
  let s1 : State := { s with pc := "if.then19", pre := some "if.end" }
  let env2 : Env := gapNumberAcceptEnv env base se v7 t ee v32
  let s2 : State :=
    { s1 with pc := "if.end67.critedge", pre := some "if.then19",
              mem := mem', next := next' }
  let s3 : State := gapNumberAcceptState s mem' next'
  have h1 : step (stage2Calls nf) odGapRecoverBody (stateAt env s) =
      .jump (stateAt env1 s1) :=
    gapNum_step_ifEnd_num (calls := stage2Calls nf) hpc h0 ht hse hse63 hbyte
      (gapNumberByte_or hnum)
  have h2 : step (stage2Calls nf) odGapRecoverBody (stateAt env1 s1) =
      .jump (stateAt env2 s2) := by
    have hd' : lookupName env1 "%d" = some (.ptr d) := by
      simp only [env1, gapNumIfEndEnv]; block_lk
    have hei' : lookupName env1 "%ei" = some (.ptr ei) := by
      simp only [env1, gapNumIfEndEnv]; block_lk
    have hee' : lookupName env1 "%ee.0.lcssa" = some (.int 64 ee) := by
      simp only [env1, gapNumIfEndEnv]; block_lk
    have ht' : lookupName env1 "%t.0.val" = some (.int 64 t) := by
      simp only [env1, gapNumIfEndEnv]; block_lk
    have harr' : lookupName env1 "%arrayidx9" = some (.ptr (base + se)) := by
      simp only [env1, gapNumIfEndEnv]; block_lk
    exact gapNum_step_ifThen19_nonzero (nf := nf) (s := s1) (by simp only [s1])
      hd' hei' hee' ht' harr' hcall hv32
  have h3 : step (stage2Calls nf) odGapRecoverBody (stateAt env2 s2) =
      .jump (stateAt env2 s3) := by
    have hd' : lookupName env2 "%d" = some (.ptr d) := by
      simp only [env2, gapNumberAcceptEnv, gapNumThen19Env, gapNumIfEndEnv]
      block_lk
    have hei' : lookupName env2 "%ei" = some (.ptr ei) := by
      simp only [env2, gapNumberAcceptEnv, gapNumThen19Env, gapNumIfEndEnv]
      block_lk
    exact gapNum_step_critedge (nf := nf) (s := s2) (by simp only [s2]) hd' hei'
  rw [show 3 + k = 1 + (1 + (1 + k)) from by omega,
    runFuel_jump_prefix h1 (1 + (1 + k)), runFuel_jump_prefix h2 (1 + k),
    runFuel_jump_prefix h3 k]

/-! ### Axiom footprints

The runs are the pinned `findBlock`s, the Steps module's instruction steps and
the two block terminators; the helper call is the named hypothesis and no step
unfolds its body. -/
#print axioms gap_number_refusal_run
#print axioms gap_number_refusal_outcome
#print axioms gap_number_accept_run

end LeanLLVM.Refinement
