/-
`od_gap_recover`'s **second scan**: the loop the body reaches from `if.end67` when
the token's lexeme has already been accepted.

The C text's second loop is

```
while (s2 < ip && is_ws(b[s2])) s2++;
```

and the emitted body spells it as the head `land.rhs71` (`%s2.020` the carried
counter, `%arrayidx72` and the byte `%15`), the switch `NodeBlock26`/`NodeBlock24`
over that byte, the three leaves (9/10, 13, 32) that send a whitespace byte to
`while.body76` and every other byte to `while.end78`, and `while.body76`'s
`%inc77`/`%exitcond24.not` test against `%cond`.  `while.end78`'s `%s2.0.lcssa`
`phi` is the exit offset, and the block writes the refusal record — kind 0, the
offset, tag 4 — before `cleanup82` returns `void`.

This module proves that run.  It reuses `JsonStage2HelperIROdGapRun`'s routing
(`gapRoute`, `gapRoute_ws`, `gapRoute_nonWs`, which state *which* leaf the switch
selects rather than where the leaf branches), its byte lemma (`gapByte`,
`gap_readOne`) and its sign-extension and word lemmas, and the block pins and
instruction steps of `JsonStage2HelperIROdGapSteps` (`odGapRecover_findBlock_*`,
`gap_denote_*`).  The loop is a `BoundLoop` with bound `ip` and per-iteration cost
five, exactly as the first scan; its invariant carries the whitespace prefix
`gapWsRun (k - ee) (bytes.drop ee) = k - ee`, and the exit offset is the model's
`gapS2`.  The scan itself writes nothing: every state it leaves has the caller's
memory, and the only stores are `while.end78`'s three, which the model spells as
`stage2ErrSetMsg mem e (gapS2 bytes ip ee) gapTagExtra`.

The statement is about the run from `if.end67`'s own state at the staging the
literal and number paths hand it, not a contract over the whole function.
-/
import LeanLLVM.Refinement.JsonStage2HelperIROdGapRun

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval

/-! ### The second scan's vocabulary

`while.end78`'s `phi` names its five predecessors' operands, and `land.rhs71`'s
names its two; both are the emitted lists.  `gapWsLandRhsEnv` is the environment
`land.rhs71` leaves. -/

/-- `(0x458#64).signExtend 64).toNat` is 1112: the cursor's `e` field. -/
theorem gap_se1112 : ((0x0000000000000458#64).signExtend 64).toNat = 1112 := by decide

/-- `land.rhs71`'s `phi`: the incremented counter, or `%ee.0.lcssa`. -/
def gapWsLandRhsIncoming : List (String × Operand) :=
  [("while.body76", Operand.reg "%inc77"), ("if.end67", Operand.reg "%ee.0.lcssa")]

/-- `while.end78`'s `phi`: every predecessor's exit offset. -/
def gapWsScanIncoming : List (String × Operand) :=
  [("if.end67", Operand.reg "%ee.0.lcssa"),
   ("while.body76", Operand.reg "%cond"),
   ("LeafBlock17", Operand.reg "%s2.020"),
   ("LeafBlock20", Operand.reg "%s2.020"),
   ("LeafBlock22", Operand.reg "%s2.020")]

/-- The state `land.rhs71` leaves: the carried counter, its address, and the byte. -/
def gapWsLandRhsEnv (env : Env) (b c : Nat) (byte : UInt8) : Env :=
  ("%15", .int 8 (gapByte byte)) ::
  ("%arrayidx72", .ptr (b + c)) ::
  ("%s2.020", .int 64 (BitVec.ofNat 64 c)) :: env

/-! ### The model's second loop, as arithmetic

`gapS2 bytes ip ee = ee + gapWsRun (ip - ee) (bytes.drop ee)`.  These are the
running-count lemmas the constant-time run reads: the count of a prefix is
additive, a non-whitespace byte stops it, a whitespace byte extends it, and a
prefix through `c` fixes the model's stop at the two exits. -/

/-- A whitespace run that reaches `k` is additive. -/
theorem gapWsRun_add {k m : Nat} {bs : List UInt8}
    (h : gapWsRun k bs = k) :
    gapWsRun (k + m) bs = k + gapWsRun m (bs.drop k) := by
  induction k generalizing bs with
  | zero => simp
  | succ k ih =>
    cases bs with
    | nil => simp [gapWsRun] at h
    | cons b bs =>
      simp only [gapWsRun] at h
      split at h
      · rename_i hws
        have hk : gapWsRun k bs = k := by omega
        rw [show k + 1 + m = k + m + 1 from by omega]
        have hstep : gapWsRun (k + m + 1) (b :: bs) = 1 + gapWsRun (k + m) bs := by
          simp [gapWsRun, hws]
        rw [hstep, List.drop_succ_cons, ih hk]
        omega
      · omega

/-- A run that starts on a non-whitespace byte is zero. -/
theorem gapWsRun_zero_of_nonWs {m : Nat} {bs : List UInt8} (hm : 0 < m)
    (hnws : gapIsWs (bs.getD 0 0) = false) : gapWsRun m bs = 0 := by
  cases m with
  | zero => omega
  | succ m =>
    cases bs with
    | nil => simp [gapWsRun]
    | cons b bs =>
      have hb : gapIsWs b = false := by simpa using hnws
      simp [gapWsRun, hb]

/-- A run continues one byte past a whitespace prefix. -/
theorem gapWsRun_succ {k : Nat} {bs : List UInt8}
    (h : gapWsRun k bs = k) (hk : k < bs.length)
    (hws : gapIsWs (bs.getD k 0) = true) :
    gapWsRun (k + 1) bs = k + 1 := by
  rw [gapWsRun_add h]
  have hone : gapWsRun 1 (bs.drop k) = 1 := by
    have hne : bs.drop k ≠ [] := by
      intro hnil
      have h0 : (bs.drop k).length = 0 := by rw [hnil]; rfl
      rw [List.length_drop] at h0
      omega
    cases hd : bs.drop k with
    | nil => exact absurd hd hne
    | cons b rest =>
      have hb : gapIsWs b = true := by
        have hh := hws
        rw [← gap_getD_drop bs k] at hh
        rw [show (bs.drop k).getD 0 0 = (b :: rest).getD 0 0 from by rw [hd]] at hh
        simpa using hh
      simp [gapWsRun, hb]
  rw [hone]

/-- A whitespace run never passes its bound. -/
theorem gapWsRun_le (k : Nat) (bs : List UInt8) : gapWsRun k bs ≤ k := by
  induction k generalizing bs with
  | zero => simp [gapWsRun]
  | succ k ih =>
    cases bs with
    | nil => simp [gapWsRun]
    | cons b bs =>
      by_cases hws : gapIsWs b = true
      · have hstep : gapWsRun (k + 1) (b :: bs) = 1 + gapWsRun k bs := by
          simp [gapWsRun, hws]
        rw [hstep]
        have := ih bs
        omega
      · have hf : gapIsWs b = false := by
          cases h : gapIsWs b with
          | false => rfl
          | true => exact absurd h hws
        simp [gapWsRun, hf]

/-- The model's second loop is bounded by the window's end. -/
theorem gapWsS2_le {bytes : List UInt8} {ip ee : Nat} (h : ee ≤ ip) :
    gapS2 bytes ip ee ≤ ip := by
  unfold gapS2
  have := gapWsRun_le (ip - ee) (bytes.drop ee)
  omega

/-- **The second scan's non-whitespace exit.**  With the first `k - ee` bytes
whitespace and the byte at `k` not, the model's second loop has stopped at `k`. -/
theorem gapWsS2_of_prefix_nonWs {bytes : List UInt8} {ip ee k : Nat}
    (hee : ee ≤ k) (hlt : k < ip)
    (hpre : gapWsRun (k - ee) (bytes.drop ee) = k - ee)
    (hnws : gapIsWs (bytes.getD k 0) = false) :
    gapS2 bytes ip ee = k := by
  unfold gapS2
  have hadd := gapWsRun_add (m := ip - k) hpre
  rw [show k - ee + (ip - k) = ip - ee from by omega] at hadd
  rw [hadd, gap_drop_drop, show ee + (k - ee) = k from by omega,
    gapWsRun_zero_of_nonWs (m := ip - k) (by omega)
      (by rw [gap_getD_drop]; exact hnws)]
  omega

/-- **The second scan's `ip` exit.**  With the first `k - ee` bytes whitespace,
the byte at `k` a whitespace, and `k + 1 = ip`, the model's second loop has run
the whole window and stopped at `ip`. -/
theorem gapWsS2_of_prefix_all {bytes : List UInt8} {ip ee k : Nat}
    (hblen : bytes.length = ip) (hee : ee ≤ k) (hnext : k + 1 = ip)
    (hpre : gapWsRun (k - ee) (bytes.drop ee) = k - ee)
    (hws : gapIsWs (bytes.getD k 0) = true) :
    gapS2 bytes ip ee = ip := by
  unfold gapS2
  have hone : gapWsRun 1 (bytes.drop k) = 1 :=
    gapWsRun_succ (k := 0) rfl (by rw [List.length_drop, hblen]; omega)
      (by rw [gap_getD_drop]; exact hws)
  have hadd := gapWsRun_add (m := ip - k) hpre
  rw [show k - ee + (ip - k) = ip - ee from by omega] at hadd
  rw [hadd, gap_drop_drop, show ee + (k - ee) = k from by omega,
    show ip - k = 1 from by omega, hone]
  omega

/-! ### The second scan's block steps

Each is one `step`: the block is found by name (the pin from
`JsonStage2HelperIROdGapSteps`), its instructions denote to the state the block
lemma names, and its terminator is executed.  The two `land.rhs71` steps and the
`while.end78` step take the predecessor the `phi` selects by. -/

/-- `if.end67`: `%cmp6919 = %ee.0.lcssa < %cond` selects the head or the exit. -/
theorem gapWs_step_ifEnd67 {calls : Calls} {env : Env} {s : State} {ee ip : Nat}
    (hpc : s.pc = "if.end67")
    (hee : lookupName env "%ee.0.lcssa" = some (.int 64 (BitVec.ofNat 64 ee)))
    (hcond : lookupName env "%cond" = some (.int 64 (BitVec.ofNat 64 ip))) :
    step calls odGapRecoverBody (stateAt env s) =
      (if evalICmp .ult (BitVec.ofNat 64 ee) (BitVec.ofNat 64 ip) = 1#1
       then .jump (stateAt
              (("%cmp6919", .int 1 (evalICmp .ult (BitVec.ofNat 64 ee)
                (BitVec.ofNat 64 ip))) :: env)
              { s with pc := "land.rhs71", pre := some "if.end67" })
       else .jump (stateAt
              (("%cmp6919", .int 1 (evalICmp .ult (BitVec.ofNat 64 ee)
                (BitVec.ofNat 64 ip))) :: env)
              { s with pc := "while.end78", pre := some "if.end67" })) := by
  have hpc' : (stateAt env s).pc = "if.end67" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"if.end67", odGapRecoverIfEnd67Instrs,
        Term.condbr (Operand.reg "%cmp6919") "land.rhs71" "while.end78"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_if_end67
  have hden : denoteCode calls odGapRecoverIfEnd67Instrs (stateAt env s) =
      some (stateAt (("%cmp6919", .int 1 (evalICmp .ult (BitVec.ofNat 64 ee)
        (BitVec.ofNat 64 ip))) :: env) s) := by
    rw [odGapRecoverIfEnd67Instrs]
    refine Eq.trans (gap_denote_icmp_ult_reg calls env s "%cmp6919" "%ee.0.lcssa"
      "%cond" (by block_lk) (by block_lk) []) ?_
    rfl
  by_cases hbit : evalICmp .ult (BitVec.ofNat 64 ee) (BitVec.ofNat 64 ip) = 1#1
  · have hterm : execTerm
        (stateAt (("%cmp6919", .int 1 (evalICmp .ult (BitVec.ofNat 64 ee)
          (BitVec.ofNat 64 ip))) :: env) s)
        (Term.condbr (Operand.reg "%cmp6919") "land.rhs71" "while.end78") =
      .jump (stateAt (("%cmp6919", .int 1 (evalICmp .ult (BitVec.ofNat 64 ee)
          (BitVec.ofNat 64 ip))) :: env)
        { s with pc := "land.rhs71", pre := some "if.end67" }) := by
      rw [gap_execTerm_condbr_one
        (by simp only [evalOperand, stateAt, lookupName_cons_self, hbit]; rfl)]
      simp only [stateAt, hpc]
    simp only [step, hfind, hden, hterm, if_pos hbit]
  · have hz : evalICmp .ult (BitVec.ofNat 64 ee) (BitVec.ofNat 64 ip) = 0#1 := by
      rcases bitVec1_eq_zero_or_one
        (evalICmp .ult (BitVec.ofNat 64 ee) (BitVec.ofNat 64 ip)) with h | h
      · exact h
      · exact absurd h hbit
    have hterm : execTerm
        (stateAt (("%cmp6919", .int 1 (evalICmp .ult (BitVec.ofNat 64 ee)
          (BitVec.ofNat 64 ip))) :: env) s)
        (Term.condbr (Operand.reg "%cmp6919") "land.rhs71" "while.end78") =
      .jump (stateAt (("%cmp6919", .int 1 (evalICmp .ult (BitVec.ofNat 64 ee)
          (BitVec.ofNat 64 ip))) :: env)
        { s with pc := "while.end78", pre := some "if.end67" }) := by
      rw [gap_execTerm_condbr_zero
        (by simp only [evalOperand, stateAt, lookupName_cons_self, hz]; rfl)]
      simp only [stateAt, hpc]
    simp only [step, hfind, hden, hterm, if_neg hbit]

/-- `land.rhs71` entered from `if.end67`: the counter is `%ee.0.lcssa`. -/
theorem gapWs_step_landRhs71_fromIfEnd67 {calls : Calls} {env : Env} {s : State}
    {b c : Nat} {byte : UInt8}
    (hpc : s.pc = "land.rhs71") (hpre : s.pre = some "if.end67")
    (hb : lookupName env "%0" = some (.ptr b))
    (hee : lookupName env "%ee.0.lcssa" = some (.int 64 (BitVec.ofNat 64 c)))
    (hld : readBytes s.mem (b + c) 1 = some (natToBytes (gapByte byte).toNat 1))
    (hc63 : c < 2 ^ 63) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt (gapWsLandRhsEnv env b c byte)
        { s with pc := "NodeBlock26", pre := some "land.rhs71" }) := by
  have hpc' : (stateAt env s).pc = "land.rhs71" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"land.rhs71", odGapRecoverLandRhs71Instrs, Term.br "NodeBlock26"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_land_rhs71
  have hinc : phiIncoming "if.end67" gapWsLandRhsIncoming =
      some (Operand.reg "%ee.0.lcssa") := by decide
  have hop : evalOperand (stateAt env s) (Operand.reg "%ee.0.lcssa") =
      some (.int 64 (BitVec.ofNat 64 c)) := by
    simp only [evalOperand, stateAt]
    rw [hee]
  have hgp : ((BitVec.ofNat 64 c).signExtend 64).toNat < 2 ^ 63 := by
    rw [gap_signExtend_ofNat c (by omega)]
    omega
  have hden : denoteCode calls odGapRecoverLandRhs71Instrs (stateAt env s) =
      some (stateAt (gapWsLandRhsEnv env b c byte) s) := by
    rw [odGapRecoverLandRhs71Instrs]
    refine Eq.trans (denoteCode_phi calls env s "%s2.020" (Ty.int 64)
      gapWsLandRhsIncoming (p := "if.end67") (op := Operand.reg "%ee.0.lcssa")
      (v := .int 64 (BitVec.ofNat 64 c)) hpre hinc hop
      [Instr.gep "%arrayidx72" (Ty.int 8) (Operand.reg "%0") (Operand.reg "%s2.020"),
       Instr.load "%15" (Ty.int 8) (Operand.reg "%arrayidx72")] (by decide)) ?_
    refine Eq.trans (denoteCode_gep8_reg calls
      (("%s2.020", .int 64 (BitVec.ofNat 64 c)) :: env) s
      "%arrayidx72" "%0" "%s2.020" (by block_lk) (by block_lk) hgp
      [Instr.load "%15" (Ty.int 8) (Operand.reg "%arrayidx72")]) ?_
    rw [gap_signExtend_ofNat c (by omega)]
    refine Eq.trans (gap_denote_load8 calls
      (("%arrayidx72", .ptr (b + c)) :: ("%s2.020", .int 64 (BitVec.ofNat 64 c)) :: env) s
      "%15" "%arrayidx72" (by block_lk) hld []) ?_
    rfl
  have hterm : execTerm (stateAt (gapWsLandRhsEnv env b c byte) s) (Term.br "NodeBlock26") =
      .jump (stateAt (gapWsLandRhsEnv env b c byte)
        { s with pc := "NodeBlock26", pre := some "land.rhs71" }) := by
    rw [gap_execTerm_br]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-- `land.rhs71` entered from `while.body76`: the counter is `%inc77`. -/
theorem gapWs_step_landRhs71_fromWhileBody76 {calls : Calls} {env : Env} {s : State}
    {b c : Nat} {byte : UInt8}
    (hpc : s.pc = "land.rhs71") (hpre : s.pre = some "while.body76")
    (hb : lookupName env "%0" = some (.ptr b))
    (hinc : lookupName env "%inc77" = some (.int 64 (BitVec.ofNat 64 c)))
    (hld : readBytes s.mem (b + c) 1 = some (natToBytes (gapByte byte).toNat 1))
    (hc63 : c < 2 ^ 63) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt (gapWsLandRhsEnv env b c byte)
        { s with pc := "NodeBlock26", pre := some "land.rhs71" }) := by
  have hpc' : (stateAt env s).pc = "land.rhs71" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"land.rhs71", odGapRecoverLandRhs71Instrs, Term.br "NodeBlock26"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_land_rhs71
  have hinc' : phiIncoming "while.body76" gapWsLandRhsIncoming =
      some (Operand.reg "%inc77") := by decide
  have hop : evalOperand (stateAt env s) (Operand.reg "%inc77") =
      some (.int 64 (BitVec.ofNat 64 c)) := by
    simp only [evalOperand, stateAt]
    rw [hinc]
  have hgp : ((BitVec.ofNat 64 c).signExtend 64).toNat < 2 ^ 63 := by
    rw [gap_signExtend_ofNat c (by omega)]
    omega
  have hden : denoteCode calls odGapRecoverLandRhs71Instrs (stateAt env s) =
      some (stateAt (gapWsLandRhsEnv env b c byte) s) := by
    rw [odGapRecoverLandRhs71Instrs]
    refine Eq.trans (denoteCode_phi calls env s "%s2.020" (Ty.int 64)
      gapWsLandRhsIncoming (p := "while.body76") (op := Operand.reg "%inc77")
      (v := .int 64 (BitVec.ofNat 64 c)) hpre hinc' hop
      [Instr.gep "%arrayidx72" (Ty.int 8) (Operand.reg "%0") (Operand.reg "%s2.020"),
       Instr.load "%15" (Ty.int 8) (Operand.reg "%arrayidx72")] (by decide)) ?_
    refine Eq.trans (denoteCode_gep8_reg calls
      (("%s2.020", .int 64 (BitVec.ofNat 64 c)) :: env) s
      "%arrayidx72" "%0" "%s2.020" (by block_lk) (by block_lk) hgp
      [Instr.load "%15" (Ty.int 8) (Operand.reg "%arrayidx72")]) ?_
    rw [gap_signExtend_ofNat c (by omega)]
    refine Eq.trans (gap_denote_load8 calls
      (("%arrayidx72", .ptr (b + c)) :: ("%s2.020", .int 64 (BitVec.ofNat 64 c)) :: env) s
      "%15" "%arrayidx72" (by block_lk) hld []) ?_
    rfl
  have hterm : execTerm (stateAt (gapWsLandRhsEnv env b c byte) s) (Term.br "NodeBlock26") =
      .jump (stateAt (gapWsLandRhsEnv env b c byte)
        { s with pc := "NodeBlock26", pre := some "land.rhs71" }) := by
    rw [gap_execTerm_br]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-- `NodeBlock26`: `%15 < 13` selects `LeafBlock17`. -/
theorem gapWs_step_NodeBlock26_toLeaf17 {calls : Calls} {env : Env} {s : State}
    {byte : UInt8}
    (hpc : s.pc = "NodeBlock26") (hpre : s.pre = some "land.rhs71")
    (h15 : lookupName env "%15" = some (.int 8 (gapByte byte)))
    (hbit : evalICmp .slt (gapByte byte) (BitVec.ofNat 8 13) = 1#1) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%Pivot27", .int 1 (evalICmp .slt (gapByte byte) (BitVec.ofNat 8 13))) :: env)
        { s with pc := "LeafBlock17", pre := some "NodeBlock26" }) := by
  have hpc' : (stateAt env s).pc = "NodeBlock26" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"NodeBlock26", odGapRecoverNodeBlock26Instrs,
        Term.condbr (Operand.reg "%Pivot27") "LeafBlock17" "NodeBlock24"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_NodeBlock26
  have hden : denoteCode calls odGapRecoverNodeBlock26Instrs (stateAt env s) =
      some (stateAt (("%Pivot27", .int 1 (evalICmp .slt (gapByte byte)
        (BitVec.ofNat 8 13))) :: env) s) := by
    rw [odGapRecoverNodeBlock26Instrs]
    refine Eq.trans (gap_denote_icmp_slt_imm calls env s "%Pivot27" "%15"
      (by block_lk) []) ?_
    rfl
  have hterm : execTerm (stateAt (("%Pivot27", .int 1 (evalICmp .slt (gapByte byte)
        (BitVec.ofNat 8 13))) :: env) s)
      (Term.condbr (Operand.reg "%Pivot27") "LeafBlock17" "NodeBlock24") =
    .jump (stateAt (("%Pivot27", .int 1 (evalICmp .slt (gapByte byte)
        (BitVec.ofNat 8 13))) :: env)
      { s with pc := "LeafBlock17", pre := some "NodeBlock26" }) := by
    rw [gap_execTerm_condbr_one
      (by simp only [evalOperand, stateAt, lookupName_cons_self, hbit]; rfl)]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-- `NodeBlock26`: `%15 < 13` selects `NodeBlock24`. -/
theorem gapWs_step_NodeBlock26_toNodeBlock24 {calls : Calls} {env : Env} {s : State}
    {byte : UInt8}
    (hpc : s.pc = "NodeBlock26") (hpre : s.pre = some "land.rhs71")
    (h15 : lookupName env "%15" = some (.int 8 (gapByte byte)))
    (hbit : evalICmp .slt (gapByte byte) (BitVec.ofNat 8 13) = 0#1) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%Pivot27", .int 1 (evalICmp .slt (gapByte byte) (BitVec.ofNat 8 13))) :: env)
        { s with pc := "NodeBlock24", pre := some "NodeBlock26" }) := by
  have hpc' : (stateAt env s).pc = "NodeBlock26" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"NodeBlock26", odGapRecoverNodeBlock26Instrs,
        Term.condbr (Operand.reg "%Pivot27") "LeafBlock17" "NodeBlock24"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_NodeBlock26
  have hden : denoteCode calls odGapRecoverNodeBlock26Instrs (stateAt env s) =
      some (stateAt (("%Pivot27", .int 1 (evalICmp .slt (gapByte byte)
        (BitVec.ofNat 8 13))) :: env) s) := by
    rw [odGapRecoverNodeBlock26Instrs]
    refine Eq.trans (gap_denote_icmp_slt_imm calls env s "%Pivot27" "%15"
      (by block_lk) []) ?_
    rfl
  have hterm : execTerm (stateAt (("%Pivot27", .int 1 (evalICmp .slt (gapByte byte)
        (BitVec.ofNat 8 13))) :: env) s)
      (Term.condbr (Operand.reg "%Pivot27") "LeafBlock17" "NodeBlock24") =
    .jump (stateAt (("%Pivot27", .int 1 (evalICmp .slt (gapByte byte)
        (BitVec.ofNat 8 13))) :: env)
      { s with pc := "NodeBlock24", pre := some "NodeBlock26" }) := by
    rw [gap_execTerm_condbr_zero
      (by simp only [evalOperand, stateAt, lookupName_cons_self, hbit]; rfl)]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-- `NodeBlock24`: `%15 < 32` selects `LeafBlock20`. -/
theorem gapWs_step_NodeBlock24_toLeaf20 {calls : Calls} {env : Env} {s : State}
    {byte : UInt8}
    (hpc : s.pc = "NodeBlock24") (hpre : s.pre = some "NodeBlock26")
    (h15 : lookupName env "%15" = some (.int 8 (gapByte byte)))
    (hbit : evalICmp .slt (gapByte byte) (BitVec.ofNat 8 32) = 1#1) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%Pivot25", .int 1 (evalICmp .slt (gapByte byte) (BitVec.ofNat 8 32))) :: env)
        { s with pc := "LeafBlock20", pre := some "NodeBlock24" }) := by
  have hpc' : (stateAt env s).pc = "NodeBlock24" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"NodeBlock24", odGapRecoverNodeBlock24Instrs,
        Term.condbr (Operand.reg "%Pivot25") "LeafBlock20" "LeafBlock22"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_NodeBlock24
  have hden : denoteCode calls odGapRecoverNodeBlock24Instrs (stateAt env s) =
      some (stateAt (("%Pivot25", .int 1 (evalICmp .slt (gapByte byte)
        (BitVec.ofNat 8 32))) :: env) s) := by
    rw [odGapRecoverNodeBlock24Instrs]
    refine Eq.trans (gap_denote_icmp_slt_imm calls env s "%Pivot25" "%15"
      (by block_lk) []) ?_
    rfl
  have hterm : execTerm (stateAt (("%Pivot25", .int 1 (evalICmp .slt (gapByte byte)
        (BitVec.ofNat 8 32))) :: env) s)
      (Term.condbr (Operand.reg "%Pivot25") "LeafBlock20" "LeafBlock22") =
    .jump (stateAt (("%Pivot25", .int 1 (evalICmp .slt (gapByte byte)
        (BitVec.ofNat 8 32))) :: env)
      { s with pc := "LeafBlock20", pre := some "NodeBlock24" }) := by
    rw [gap_execTerm_condbr_one
      (by simp only [evalOperand, stateAt, lookupName_cons_self, hbit]; rfl)]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-- `NodeBlock24`: `%15 < 32` selects `LeafBlock22`. -/
theorem gapWs_step_NodeBlock24_toLeaf22 {calls : Calls} {env : Env} {s : State}
    {byte : UInt8}
    (hpc : s.pc = "NodeBlock24") (hpre : s.pre = some "NodeBlock26")
    (h15 : lookupName env "%15" = some (.int 8 (gapByte byte)))
    (hbit : evalICmp .slt (gapByte byte) (BitVec.ofNat 8 32) = 0#1) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%Pivot25", .int 1 (evalICmp .slt (gapByte byte) (BitVec.ofNat 8 32))) :: env)
        { s with pc := "LeafBlock22", pre := some "NodeBlock24" }) := by
  have hpc' : (stateAt env s).pc = "NodeBlock24" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"NodeBlock24", odGapRecoverNodeBlock24Instrs,
        Term.condbr (Operand.reg "%Pivot25") "LeafBlock20" "LeafBlock22"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_NodeBlock24
  have hden : denoteCode calls odGapRecoverNodeBlock24Instrs (stateAt env s) =
      some (stateAt (("%Pivot25", .int 1 (evalICmp .slt (gapByte byte)
        (BitVec.ofNat 8 32))) :: env) s) := by
    rw [odGapRecoverNodeBlock24Instrs]
    refine Eq.trans (gap_denote_icmp_slt_imm calls env s "%Pivot25" "%15"
      (by block_lk) []) ?_
    rfl
  have hterm : execTerm (stateAt (("%Pivot25", .int 1 (evalICmp .slt (gapByte byte)
        (BitVec.ofNat 8 32))) :: env) s)
      (Term.condbr (Operand.reg "%Pivot25") "LeafBlock20" "LeafBlock22") =
    .jump (stateAt (("%Pivot25", .int 1 (evalICmp .slt (gapByte byte)
        (BitVec.ofNat 8 32))) :: env)
      { s with pc := "LeafBlock22", pre := some "NodeBlock24" }) := by
    rw [gap_execTerm_condbr_zero
      (by simp only [evalOperand, stateAt, lookupName_cons_self, hbit]; rfl)]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-- `LeafBlock22`: `%15 == 32` selects `while.body76`. -/
theorem gapWs_step_LeafBlock22_toWhileBody76 {calls : Calls} {env : Env} {s : State}
    {byte : UInt8}
    (hpc : s.pc = "LeafBlock22") (hpre : s.pre = some "NodeBlock24")
    (h15 : lookupName env "%15" = some (.int 8 (gapByte byte)))
    (hbit : evalICmp .eq (gapByte byte) (BitVec.ofNat 8 32) = 1#1) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%SwitchLeaf23", .int 1 (evalICmp .eq (gapByte byte)
          (BitVec.ofNat 8 32))) :: env)
        { s with pc := "while.body76", pre := some "LeafBlock22" }) := by
  have hpc' : (stateAt env s).pc = "LeafBlock22" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"LeafBlock22", odGapRecoverLeafBlock22Instrs,
        Term.condbr (Operand.reg "%SwitchLeaf23") "while.body76" "while.end78"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_LeafBlock22
  have hden : denoteCode calls odGapRecoverLeafBlock22Instrs (stateAt env s) =
      some (stateAt (("%SwitchLeaf23", .int 1 (evalICmp .eq (gapByte byte)
        (BitVec.ofNat 8 32))) :: env) s) := by
    rw [odGapRecoverLeafBlock22Instrs]
    refine Eq.trans (gap_denote_icmp_eq_imm calls env s "%SwitchLeaf23" "%15"
      (by block_lk) []) ?_
    rfl
  have hterm : execTerm (stateAt (("%SwitchLeaf23", .int 1 (evalICmp .eq (gapByte byte)
        (BitVec.ofNat 8 32))) :: env) s)
      (Term.condbr (Operand.reg "%SwitchLeaf23") "while.body76" "while.end78") =
    .jump (stateAt (("%SwitchLeaf23", .int 1 (evalICmp .eq (gapByte byte)
        (BitVec.ofNat 8 32))) :: env)
      { s with pc := "while.body76", pre := some "LeafBlock22" }) := by
    rw [gap_execTerm_condbr_one
      (by simp only [evalOperand, stateAt, lookupName_cons_self, hbit]; rfl)]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-- `LeafBlock22`: `%15 == 32` selects `while.end78`. -/
theorem gapWs_step_LeafBlock22_toWhileEnd78 {calls : Calls} {env : Env} {s : State}
    {byte : UInt8}
    (hpc : s.pc = "LeafBlock22") (hpre : s.pre = some "NodeBlock24")
    (h15 : lookupName env "%15" = some (.int 8 (gapByte byte)))
    (hbit : evalICmp .eq (gapByte byte) (BitVec.ofNat 8 32) = 0#1) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%SwitchLeaf23", .int 1 (evalICmp .eq (gapByte byte)
          (BitVec.ofNat 8 32))) :: env)
        { s with pc := "while.end78", pre := some "LeafBlock22" }) := by
  have hpc' : (stateAt env s).pc = "LeafBlock22" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"LeafBlock22", odGapRecoverLeafBlock22Instrs,
        Term.condbr (Operand.reg "%SwitchLeaf23") "while.body76" "while.end78"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_LeafBlock22
  have hden : denoteCode calls odGapRecoverLeafBlock22Instrs (stateAt env s) =
      some (stateAt (("%SwitchLeaf23", .int 1 (evalICmp .eq (gapByte byte)
        (BitVec.ofNat 8 32))) :: env) s) := by
    rw [odGapRecoverLeafBlock22Instrs]
    refine Eq.trans (gap_denote_icmp_eq_imm calls env s "%SwitchLeaf23" "%15"
      (by block_lk) []) ?_
    rfl
  have hterm : execTerm (stateAt (("%SwitchLeaf23", .int 1 (evalICmp .eq (gapByte byte)
        (BitVec.ofNat 8 32))) :: env) s)
      (Term.condbr (Operand.reg "%SwitchLeaf23") "while.body76" "while.end78") =
    .jump (stateAt (("%SwitchLeaf23", .int 1 (evalICmp .eq (gapByte byte)
        (BitVec.ofNat 8 32))) :: env)
      { s with pc := "while.end78", pre := some "LeafBlock22" }) := by
    rw [gap_execTerm_condbr_zero
      (by simp only [evalOperand, stateAt, lookupName_cons_self, hbit]; rfl)]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-- `LeafBlock20`: `%15 == 13` selects `while.body76`. -/
theorem gapWs_step_LeafBlock20_toWhileBody76 {calls : Calls} {env : Env} {s : State}
    {byte : UInt8}
    (hpc : s.pc = "LeafBlock20") (hpre : s.pre = some "NodeBlock24")
    (h15 : lookupName env "%15" = some (.int 8 (gapByte byte)))
    (hbit : evalICmp .eq (gapByte byte) (BitVec.ofNat 8 13) = 1#1) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%SwitchLeaf21", .int 1 (evalICmp .eq (gapByte byte)
          (BitVec.ofNat 8 13))) :: env)
        { s with pc := "while.body76", pre := some "LeafBlock20" }) := by
  have hpc' : (stateAt env s).pc = "LeafBlock20" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"LeafBlock20", odGapRecoverLeafBlock20Instrs,
        Term.condbr (Operand.reg "%SwitchLeaf21") "while.body76" "while.end78"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_LeafBlock20
  have hden : denoteCode calls odGapRecoverLeafBlock20Instrs (stateAt env s) =
      some (stateAt (("%SwitchLeaf21", .int 1 (evalICmp .eq (gapByte byte)
        (BitVec.ofNat 8 13))) :: env) s) := by
    rw [odGapRecoverLeafBlock20Instrs]
    refine Eq.trans (gap_denote_icmp_eq_imm calls env s "%SwitchLeaf21" "%15"
      (by block_lk) []) ?_
    rfl
  have hterm : execTerm (stateAt (("%SwitchLeaf21", .int 1 (evalICmp .eq (gapByte byte)
        (BitVec.ofNat 8 13))) :: env) s)
      (Term.condbr (Operand.reg "%SwitchLeaf21") "while.body76" "while.end78") =
    .jump (stateAt (("%SwitchLeaf21", .int 1 (evalICmp .eq (gapByte byte)
        (BitVec.ofNat 8 13))) :: env)
      { s with pc := "while.body76", pre := some "LeafBlock20" }) := by
    rw [gap_execTerm_condbr_one
      (by simp only [evalOperand, stateAt, lookupName_cons_self, hbit]; rfl)]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-- `LeafBlock20`: `%15 == 13` selects `while.end78`. -/
theorem gapWs_step_LeafBlock20_toWhileEnd78 {calls : Calls} {env : Env} {s : State}
    {byte : UInt8}
    (hpc : s.pc = "LeafBlock20") (hpre : s.pre = some "NodeBlock24")
    (h15 : lookupName env "%15" = some (.int 8 (gapByte byte)))
    (hbit : evalICmp .eq (gapByte byte) (BitVec.ofNat 8 13) = 0#1) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%SwitchLeaf21", .int 1 (evalICmp .eq (gapByte byte)
          (BitVec.ofNat 8 13))) :: env)
        { s with pc := "while.end78", pre := some "LeafBlock20" }) := by
  have hpc' : (stateAt env s).pc = "LeafBlock20" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"LeafBlock20", odGapRecoverLeafBlock20Instrs,
        Term.condbr (Operand.reg "%SwitchLeaf21") "while.body76" "while.end78"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_LeafBlock20
  have hden : denoteCode calls odGapRecoverLeafBlock20Instrs (stateAt env s) =
      some (stateAt (("%SwitchLeaf21", .int 1 (evalICmp .eq (gapByte byte)
        (BitVec.ofNat 8 13))) :: env) s) := by
    rw [odGapRecoverLeafBlock20Instrs]
    refine Eq.trans (gap_denote_icmp_eq_imm calls env s "%SwitchLeaf21" "%15"
      (by block_lk) []) ?_
    rfl
  have hterm : execTerm (stateAt (("%SwitchLeaf21", .int 1 (evalICmp .eq (gapByte byte)
        (BitVec.ofNat 8 13))) :: env) s)
      (Term.condbr (Operand.reg "%SwitchLeaf21") "while.body76" "while.end78") =
    .jump (stateAt (("%SwitchLeaf21", .int 1 (evalICmp .eq (gapByte byte)
        (BitVec.ofNat 8 13))) :: env)
      { s with pc := "while.end78", pre := some "LeafBlock20" }) := by
    rw [gap_execTerm_condbr_zero
      (by simp only [evalOperand, stateAt, lookupName_cons_self, hbit]; rfl)]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-- `LeafBlock17`: `%15 - 9 <= 1` selects `while.body76`. -/
theorem gapWs_step_LeafBlock17_toWhileBody76 {calls : Calls} {env : Env} {s : State}
    {byte : UInt8}
    (hpc : s.pc = "LeafBlock17") (hpre : s.pre = some "NodeBlock26")
    (h15 : lookupName env "%15" = some (.int 8 (gapByte byte)))
    (hbit : evalICmp .ule (gapOff (gapByte byte)) (BitVec.ofNat 8 1) = 1#1) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%SwitchLeaf19", .int 1 (evalICmp .ule (gapOff (gapByte byte))
          (BitVec.ofNat 8 1))) :: ("%.off18", .int 8 (gapOff (gapByte byte))) :: env)
        { s with pc := "while.body76", pre := some "LeafBlock17" }) := by
  have hpc' : (stateAt env s).pc = "LeafBlock17" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"LeafBlock17", odGapRecoverLeafBlock17Instrs,
        Term.condbr (Operand.reg "%SwitchLeaf19") "while.body76" "while.end78"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_LeafBlock17
  have hden : denoteCode calls odGapRecoverLeafBlock17Instrs (stateAt env s) =
      some (stateAt (("%SwitchLeaf19", .int 1 (evalICmp .ule (gapOff (gapByte byte))
        (BitVec.ofNat 8 1))) :: ("%.off18", .int 8 (gapOff (gapByte byte))) :: env) s) := by
    rw [odGapRecoverLeafBlock17Instrs]
    refine Eq.trans (gap_denote_add_imm calls env s "%.off18" "%15" (by block_lk) _) ?_
    refine Eq.trans (gap_denote_icmp_ule_imm calls
      (("%.off18", .int 8 (gapOff (gapByte byte))) :: env) s
      "%SwitchLeaf19" "%.off18" (by block_lk) []) ?_
    rfl
  have hterm : execTerm (stateAt (("%SwitchLeaf19", .int 1 (evalICmp .ule (gapOff (gapByte byte))
        (BitVec.ofNat 8 1))) :: ("%.off18", .int 8 (gapOff (gapByte byte))) :: env) s)
      (Term.condbr (Operand.reg "%SwitchLeaf19") "while.body76" "while.end78") =
    .jump (stateAt (("%SwitchLeaf19", .int 1 (evalICmp .ule (gapOff (gapByte byte))
        (BitVec.ofNat 8 1))) :: ("%.off18", .int 8 (gapOff (gapByte byte))) :: env)
      { s with pc := "while.body76", pre := some "LeafBlock17" }) := by
    rw [gap_execTerm_condbr_one
      (by simp only [evalOperand, stateAt, lookupName_cons_self, hbit]; rfl)]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-- `LeafBlock17`: `%15 - 9 <= 1` selects `while.end78`. -/
theorem gapWs_step_LeafBlock17_toWhileEnd78 {calls : Calls} {env : Env} {s : State}
    {byte : UInt8}
    (hpc : s.pc = "LeafBlock17") (hpre : s.pre = some "NodeBlock26")
    (h15 : lookupName env "%15" = some (.int 8 (gapByte byte)))
    (hbit : evalICmp .ule (gapOff (gapByte byte)) (BitVec.ofNat 8 1) = 0#1) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%SwitchLeaf19", .int 1 (evalICmp .ule (gapOff (gapByte byte))
          (BitVec.ofNat 8 1))) :: ("%.off18", .int 8 (gapOff (gapByte byte))) :: env)
        { s with pc := "while.end78", pre := some "LeafBlock17" }) := by
  have hpc' : (stateAt env s).pc = "LeafBlock17" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"LeafBlock17", odGapRecoverLeafBlock17Instrs,
        Term.condbr (Operand.reg "%SwitchLeaf19") "while.body76" "while.end78"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_LeafBlock17
  have hden : denoteCode calls odGapRecoverLeafBlock17Instrs (stateAt env s) =
      some (stateAt (("%SwitchLeaf19", .int 1 (evalICmp .ule (gapOff (gapByte byte))
        (BitVec.ofNat 8 1))) :: ("%.off18", .int 8 (gapOff (gapByte byte))) :: env) s) := by
    rw [odGapRecoverLeafBlock17Instrs]
    refine Eq.trans (gap_denote_add_imm calls env s "%.off18" "%15" (by block_lk) _) ?_
    refine Eq.trans (gap_denote_icmp_ule_imm calls
      (("%.off18", .int 8 (gapOff (gapByte byte))) :: env) s
      "%SwitchLeaf19" "%.off18" (by block_lk) []) ?_
    rfl
  have hterm : execTerm (stateAt (("%SwitchLeaf19", .int 1 (evalICmp .ule (gapOff (gapByte byte))
        (BitVec.ofNat 8 1))) :: ("%.off18", .int 8 (gapOff (gapByte byte))) :: env) s)
      (Term.condbr (Operand.reg "%SwitchLeaf19") "while.body76" "while.end78") =
    .jump (stateAt (("%SwitchLeaf19", .int 1 (evalICmp .ule (gapOff (gapByte byte))
        (BitVec.ofNat 8 1))) :: ("%.off18", .int 8 (gapOff (gapByte byte))) :: env)
      { s with pc := "while.end78", pre := some "LeafBlock17" }) := by
    rw [gap_execTerm_condbr_zero
      (by simp only [evalOperand, stateAt, lookupName_cons_self, hbit]; rfl)]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-- `while.body76`: `%inc77 == %cond` selects `while.end78`. -/
theorem gapWs_step_whileBody76_toWhileEnd78 {calls : Calls} {env : Env} {s : State}
    {c ip : Nat}
    (hpc : s.pc = "while.body76")
    (hcell : lookupName env "%s2.020" = some (.int 64 (BitVec.ofNat 64 c)))
    (hcond : lookupName env "%cond" = some (.int 64 (BitVec.ofNat 64 ip)))
    (hbit : evalICmp .eq (BitVec.ofNat 64 c + 1) (BitVec.ofNat 64 ip) = 1#1) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%exitcond24.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 c + 1)
            (BitVec.ofNat 64 ip))) ::
          ("%inc77", .int 64 (BitVec.ofNat 64 c + 1)) :: env)
        { s with pc := "while.end78", pre := some "while.body76" }) := by
  have hpc' : (stateAt env s).pc = "while.body76" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"while.body76", odGapRecoverWhileBody76Instrs,
        Term.condbr (Operand.reg "%exitcond24.not") "while.end78" "land.rhs71"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_while_body76
  have hden : denoteCode calls odGapRecoverWhileBody76Instrs (stateAt env s) =
      some (stateAt (("%exitcond24.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 c + 1)
        (BitVec.ofNat 64 ip))) :: ("%inc77", .int 64 (BitVec.ofNat 64 c + 1)) :: env) s) := by
    rw [odGapRecoverWhileBody76Instrs]
    refine Eq.trans (gap_denote_add_imm calls env s "%inc77" "%s2.020" (by block_lk) _) ?_
    refine Eq.trans (gap_denote_icmp_eq_reg calls
      (("%inc77", .int 64 (BitVec.ofNat 64 c + 1)) :: env) s
      "%exitcond24.not" "%inc77" "%cond" (by block_lk) (by block_lk) []) ?_
    rfl
  have hterm : execTerm (stateAt (("%exitcond24.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 c + 1)
        (BitVec.ofNat 64 ip))) :: ("%inc77", .int 64 (BitVec.ofNat 64 c + 1)) :: env) s)
      (Term.condbr (Operand.reg "%exitcond24.not") "while.end78" "land.rhs71") =
    .jump (stateAt (("%exitcond24.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 c + 1)
        (BitVec.ofNat 64 ip))) :: ("%inc77", .int 64 (BitVec.ofNat 64 c + 1)) :: env)
      { s with pc := "while.end78", pre := some "while.body76" }) := by
    rw [gap_execTerm_condbr_one
      (by simp only [evalOperand, stateAt, lookupName_cons_self, hbit]; rfl)]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-- `while.body76`: `%inc77 == %cond` selects `land.rhs71`. -/
theorem gapWs_step_whileBody76_toLandRhs71 {calls : Calls} {env : Env} {s : State}
    {c ip : Nat}
    (hpc : s.pc = "while.body76")
    (hcell : lookupName env "%s2.020" = some (.int 64 (BitVec.ofNat 64 c)))
    (hcond : lookupName env "%cond" = some (.int 64 (BitVec.ofNat 64 ip)))
    (hbit : evalICmp .eq (BitVec.ofNat 64 c + 1) (BitVec.ofNat 64 ip) = 0#1) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%exitcond24.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 c + 1)
            (BitVec.ofNat 64 ip))) ::
          ("%inc77", .int 64 (BitVec.ofNat 64 c + 1)) :: env)
        { s with pc := "land.rhs71", pre := some "while.body76" }) := by
  have hpc' : (stateAt env s).pc = "while.body76" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"while.body76", odGapRecoverWhileBody76Instrs,
        Term.condbr (Operand.reg "%exitcond24.not") "while.end78" "land.rhs71"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_while_body76
  have hden : denoteCode calls odGapRecoverWhileBody76Instrs (stateAt env s) =
      some (stateAt (("%exitcond24.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 c + 1)
        (BitVec.ofNat 64 ip))) :: ("%inc77", .int 64 (BitVec.ofNat 64 c + 1)) :: env) s) := by
    rw [odGapRecoverWhileBody76Instrs]
    refine Eq.trans (gap_denote_add_imm calls env s "%inc77" "%s2.020" (by block_lk) _) ?_
    refine Eq.trans (gap_denote_icmp_eq_reg calls
      (("%inc77", .int 64 (BitVec.ofNat 64 c + 1)) :: env) s
      "%exitcond24.not" "%inc77" "%cond" (by block_lk) (by block_lk) []) ?_
    rfl
  have hterm : execTerm (stateAt (("%exitcond24.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 c + 1)
        (BitVec.ofNat 64 ip))) :: ("%inc77", .int 64 (BitVec.ofNat 64 c + 1)) :: env) s)
      (Term.condbr (Operand.reg "%exitcond24.not") "while.end78" "land.rhs71") =
    .jump (stateAt (("%exitcond24.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 c + 1)
        (BitVec.ofNat 64 ip))) :: ("%inc77", .int 64 (BitVec.ofNat 64 c + 1)) :: env)
      { s with pc := "land.rhs71", pre := some "while.body76" }) := by
    rw [gap_execTerm_condbr_zero
      (by simp only [evalOperand, stateAt, lookupName_cons_self, hbit]; rfl)]
    simp only [stateAt, hpc]
  simp only [step, hfind, hden, hterm]

/-- A counter's eight little-endian bytes, as an opaque spelling: the exit block's
memory terms stay small. -/
def gapWsCountBytes (v : Nat) : List UInt8 := natToBytes v 8

/-- `while.end78`: the exit offset `phi`, then the refusal record's three stores
and the jump to `cleanup82`.  The record's address is the cursor's `e` field's
word, and the three stores leave `stage2ErrSetMsg`. -/
theorem gapWs_step_whileEnd78 {calls : Calls} {env : Env} {s : State}
    {p cell : String} {c s2 e : Nat}
    (hpc : s.pc = "while.end78") (hpre : s.pre = some p)
    (hc : lookupName env "%c" = some (.ptr c))
    (hinc : phiIncoming p gapWsScanIncoming = some (Operand.reg cell))
    (hcell : lookupName env cell = some (.int 64 (BitVec.ofNat 64 s2)))
    (he : readBytes s.mem (c + 1112) 8 = some (natToBytes e 8)) (he64 : e < 2 ^ 64)
    (hs2 : s2 < 2 ^ 64) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%msg2.i138", .ptr (e + 16)) :: ("%off1.i137", .ptr (e + 8)) ::
          ("%16", .ptr e) :: ("%e79", .ptr (c + 1112)) ::
          ("%s2.0.lcssa", .int 64 (BitVec.ofNat 64 s2)) :: env)
        { s with pc := "cleanup82", pre := some "while.end78", mem := stage2ErrSetMsg s.mem e s2 4 }) := by
  have hpc' : (stateAt env s).pc = "while.end78" := hpc
  have hfind : odGapRecoverBody.findBlock (stateAt env s).pc =
      some ⟨"while.end78", odGapRecoverWhileEnd78Instrs, Term.br "cleanup82"⟩ := by
    rw [hpc']; exact odGapRecover_findBlock_while_end78
  have hop : evalOperand (stateAt env s) (Operand.reg cell) =
      some (.int 64 (BitVec.ofNat 64 s2)) := by
    simp only [evalOperand, stateAt]
    rw [hcell]
  have hraw : denoteCode calls odGapRecoverWhileEnd78Instrs (stateAt env s) =
      some (stateAt
        (("%msg2.i138", .ptr (e + 16)) :: ("%off1.i137", .ptr (e + 8)) ::
          ("%16", .ptr e) :: ("%e79", .ptr (c + 1112)) ::
          ("%s2.0.lcssa", .int 64 (BitVec.ofNat 64 s2)) :: env)
        { s with mem :=
          writeBytes (writeBytes (writeBytes s.mem e (natToBytes 0 4))
            (e + 8) (gapWsCountBytes s2)) (e + 16) (natToBytes 4 8) }) := by
    rw [odGapRecoverWhileEnd78Instrs]
    refine Eq.trans (denoteCode_phi calls env s "%s2.0.lcssa" (Ty.int 64)
      gapWsScanIncoming (p := p) (op := Operand.reg cell)
      (v := .int 64 (BitVec.ofNat 64 s2)) hpre hinc hop
      [Instr.gep "%e79" (Ty.int 8) (Operand.reg "%c")
         (Operand.imm (Const.int 64 0x0000000000000458#64)),
       Instr.load "%16" Ty.ptr (Operand.reg "%e79"),
       Instr.store (Ty.int 32) (Operand.imm (Const.int 32 0x00000000#32)) (Operand.reg "%16"),
       Instr.gep "%off1.i137" (Ty.int 8) (Operand.reg "%16")
         (Operand.imm (Const.int 64 0x0000000000000008#64)),
       Instr.store (Ty.int 64) (Operand.reg "%s2.0.lcssa") (Operand.reg "%off1.i137"),
       Instr.gep "%msg2.i138" (Ty.int 8) (Operand.reg "%16")
         (Operand.imm (Const.int 64 0x0000000000000010#64)),
       Instr.store (Ty.int 64) (Operand.imm (Const.int 64 0x0000000000000004#64))
         (Operand.reg "%msg2.i138")] (by decide)) ?_
    refine Eq.trans (gap_denote_gep8_imm calls
      (("%s2.0.lcssa", .int 64 (BitVec.ofNat 64 s2)) :: env) s
      "%e79" "%c" (0x0000000000000458#64) (a := c) (by block_lk) (by decide)
      [Instr.load "%16" Ty.ptr (Operand.reg "%e79"),
       Instr.store (Ty.int 32) (Operand.imm (Const.int 32 0x00000000#32)) (Operand.reg "%16"),
       Instr.gep "%off1.i137" (Ty.int 8) (Operand.reg "%16")
         (Operand.imm (Const.int 64 0x0000000000000008#64)),
       Instr.store (Ty.int 64) (Operand.reg "%s2.0.lcssa") (Operand.reg "%off1.i137"),
       Instr.gep "%msg2.i138" (Ty.int 8) (Operand.reg "%16")
         (Operand.imm (Const.int 64 0x0000000000000010#64)),
       Instr.store (Ty.int 64) (Operand.imm (Const.int 64 0x0000000000000004#64))
         (Operand.reg "%msg2.i138")]) ?_
    rw [gap_se1112]
    refine Eq.trans (gap_denote_loadPtr calls
      (("%e79", .ptr (c + 1112)) ::
        ("%s2.0.lcssa", .int 64 (BitVec.ofNat 64 s2)) :: env) s
      "%16" "%e79" (v := e) (by block_lk) he he64
      [Instr.store (Ty.int 32) (Operand.imm (Const.int 32 0x00000000#32)) (Operand.reg "%16"),
       Instr.gep "%off1.i137" (Ty.int 8) (Operand.reg "%16")
         (Operand.imm (Const.int 64 0x0000000000000008#64)),
       Instr.store (Ty.int 64) (Operand.reg "%s2.0.lcssa") (Operand.reg "%off1.i137"),
       Instr.gep "%msg2.i138" (Ty.int 8) (Operand.reg "%16")
         (Operand.imm (Const.int 64 0x0000000000000010#64)),
       Instr.store (Ty.int 64) (Operand.imm (Const.int 64 0x0000000000000004#64))
         (Operand.reg "%msg2.i138")]) ?_
    refine Eq.trans (gap_denote_store_imm32 calls
      (("%16", .ptr e) :: ("%e79", .ptr (c + 1112)) ::
        ("%s2.0.lcssa", .int 64 (BitVec.ofNat 64 s2)) :: env) s
      "%16" (a := e) (by block_lk)
      [Instr.gep "%off1.i137" (Ty.int 8) (Operand.reg "%16")
         (Operand.imm (Const.int 64 0x0000000000000008#64)),
       Instr.store (Ty.int 64) (Operand.reg "%s2.0.lcssa") (Operand.reg "%off1.i137"),
       Instr.gep "%msg2.i138" (Ty.int 8) (Operand.reg "%16")
         (Operand.imm (Const.int 64 0x0000000000000010#64)),
       Instr.store (Ty.int 64) (Operand.imm (Const.int 64 0x0000000000000004#64))
         (Operand.reg "%msg2.i138")]) ?_
    rw [show (0x00000000#32).toNat = 0 from by decide]
    refine Eq.trans (gap_denote_gep8_imm calls
      (("%16", .ptr e) :: ("%e79", .ptr (c + 1112)) ::
        ("%s2.0.lcssa", .int 64 (BitVec.ofNat 64 s2)) :: env)
      { s with mem := writeBytes s.mem e (natToBytes 0 4) }
      "%off1.i137" "%16" (0x0000000000000008#64) (a := e) (by block_lk) (by decide)
      [Instr.store (Ty.int 64) (Operand.reg "%s2.0.lcssa") (Operand.reg "%off1.i137"),
       Instr.gep "%msg2.i138" (Ty.int 8) (Operand.reg "%16")
         (Operand.imm (Const.int 64 0x0000000000000010#64)),
       Instr.store (Ty.int 64) (Operand.imm (Const.int 64 0x0000000000000004#64))
         (Operand.reg "%msg2.i138")]) ?_
    rw [gap_se8]
    refine Eq.trans (denoteCode_store64 calls
      (("%off1.i137", .ptr (e + 8)) :: ("%16", .ptr e) ::
        ("%e79", .ptr (c + 1112)) ::
        ("%s2.0.lcssa", .int 64 (BitVec.ofNat 64 s2)) :: env)
      { s with mem := writeBytes s.mem e (natToBytes 0 4) }
      "%s2.0.lcssa" "%off1.i137" (x := BitVec.ofNat 64 s2) (a := e + 8)
      (by block_lk) (by block_lk)
      [Instr.gep "%msg2.i138" (Ty.int 8) (Operand.reg "%16")
         (Operand.imm (Const.int 64 0x0000000000000010#64)),
       Instr.store (Ty.int 64) (Operand.imm (Const.int 64 0x0000000000000004#64))
         (Operand.reg "%msg2.i138")]) ?_
    rw [gap_word64 hs2, show natToBytes s2 8 = gapWsCountBytes s2 from rfl]
    refine Eq.trans (gap_denote_gep8_imm calls
      (("%off1.i137", .ptr (e + 8)) :: ("%16", .ptr e) ::
        ("%e79", .ptr (c + 1112)) ::
        ("%s2.0.lcssa", .int 64 (BitVec.ofNat 64 s2)) :: env)
      { s with mem :=
          writeBytes (writeBytes s.mem e (natToBytes 0 4)) (e + 8) (gapWsCountBytes s2) }
      "%msg2.i138" "%16" (0x0000000000000010#64) (a := e) (by block_lk) (by decide)
      [Instr.store (Ty.int 64) (Operand.imm (Const.int 64 0x0000000000000004#64))
         (Operand.reg "%msg2.i138")]) ?_
    rw [gap_se16]
    refine Eq.trans (gap_denote_store_imm64 calls
      (("%msg2.i138", .ptr (e + 16)) :: ("%off1.i137", .ptr (e + 8)) ::
        ("%16", .ptr e) :: ("%e79", .ptr (c + 1112)) ::
        ("%s2.0.lcssa", .int 64 (BitVec.ofNat 64 s2)) :: env)
      { s with mem :=
          writeBytes (writeBytes s.mem e (natToBytes 0 4)) (e + 8) (gapWsCountBytes s2) }
      "%msg2.i138" (a := e + 16) (by block_lk) []) ?_
    rw [show (0x0000000000000004#64).toNat = 4 from by decide]
    rfl
  have hden : denoteCode calls odGapRecoverWhileEnd78Instrs (stateAt env s) =
      some (stateAt
        (("%msg2.i138", .ptr (e + 16)) :: ("%off1.i137", .ptr (e + 8)) ::
          ("%16", .ptr e) :: ("%e79", .ptr (c + 1112)) ::
          ("%s2.0.lcssa", .int 64 (BitVec.ofNat 64 s2)) :: env)
        { s with mem := stage2ErrSetMsg s.mem e s2 4 }) := by
    rw [hraw]
    simp only [stage2ErrSetMsg, stage2ErrSet, wordBytes, gapWsCountBytes]
  have hterm : execTerm
      (stateAt
        (("%msg2.i138", .ptr (e + 16)) :: ("%off1.i137", .ptr (e + 8)) ::
          ("%16", .ptr e) :: ("%e79", .ptr (c + 1112)) ::
          ("%s2.0.lcssa", .int 64 (BitVec.ofNat 64 s2)) :: env)
        { s with mem := stage2ErrSetMsg s.mem e s2 4 }) (Term.br "cleanup82") =
      .jump (stateAt
        (("%msg2.i138", .ptr (e + 16)) :: ("%off1.i137", .ptr (e + 8)) ::
          ("%16", .ptr e) :: ("%e79", .ptr (c + 1112)) ::
          ("%s2.0.lcssa", .int 64 (BitVec.ofNat 64 s2)) :: env)
        { s with pc := "cleanup82", pre := some "while.end78", mem := stage2ErrSetMsg s.mem e s2 4 }) := by
    rw [gap_execTerm_br]
    simp only [stateAt, hpc]
  have hstep0 : step calls odGapRecoverBody (stateAt env s) =
      execTerm (stateAt
        (("%msg2.i138", .ptr (e + 16)) :: ("%off1.i137", .ptr (e + 8)) ::
          ("%16", .ptr e) :: ("%e79", .ptr (c + 1112)) ::
          ("%s2.0.lcssa", .int 64 (BitVec.ofNat 64 s2)) :: env)
        { s with mem := stage2ErrSetMsg s.mem e s2 4 }) (Term.br "cleanup82") := by
    simp only [step, hfind, hden]
  exact Eq.trans hstep0 hterm

/-! ### The pins the run reads

The nine blocks the second scan's run visits, at the instruction lists and
terminators `JsonStage2HelperIROdGapSteps` pins. -/

theorem gapWsSecondScan_pins :
    odGapRecoverBody.findBlock "if.end67" =
      some ⟨"if.end67", odGapRecoverIfEnd67Instrs,
        Term.condbr (Operand.reg "%cmp6919") "land.rhs71" "while.end78"⟩ ∧
    odGapRecoverBody.findBlock "land.rhs71" =
      some ⟨"land.rhs71", odGapRecoverLandRhs71Instrs, Term.br "NodeBlock26"⟩ ∧
    odGapRecoverBody.findBlock "NodeBlock26" =
      some ⟨"NodeBlock26", odGapRecoverNodeBlock26Instrs,
        Term.condbr (Operand.reg "%Pivot27") "LeafBlock17" "NodeBlock24"⟩ ∧
    odGapRecoverBody.findBlock "NodeBlock24" =
      some ⟨"NodeBlock24", odGapRecoverNodeBlock24Instrs,
        Term.condbr (Operand.reg "%Pivot25") "LeafBlock20" "LeafBlock22"⟩ ∧
    odGapRecoverBody.findBlock "LeafBlock17" =
      some ⟨"LeafBlock17", odGapRecoverLeafBlock17Instrs,
        Term.condbr (Operand.reg "%SwitchLeaf19") "while.body76" "while.end78"⟩ ∧
    odGapRecoverBody.findBlock "LeafBlock20" =
      some ⟨"LeafBlock20", odGapRecoverLeafBlock20Instrs,
        Term.condbr (Operand.reg "%SwitchLeaf21") "while.body76" "while.end78"⟩ ∧
    odGapRecoverBody.findBlock "LeafBlock22" =
      some ⟨"LeafBlock22", odGapRecoverLeafBlock22Instrs,
        Term.condbr (Operand.reg "%SwitchLeaf23") "while.body76" "while.end78"⟩ ∧
    odGapRecoverBody.findBlock "while.body76" =
      some ⟨"while.body76", odGapRecoverWhileBody76Instrs,
        Term.condbr (Operand.reg "%exitcond24.not") "while.end78" "land.rhs71"⟩ ∧
    odGapRecoverBody.findBlock "while.end78" =
      some ⟨"while.end78", odGapRecoverWhileEnd78Instrs, Term.br "cleanup82"⟩ := by
  exact ⟨odGapRecover_findBlock_if_end67, odGapRecover_findBlock_land_rhs71,
    odGapRecover_findBlock_NodeBlock26, odGapRecover_findBlock_NodeBlock24,
    odGapRecover_findBlock_LeafBlock17, odGapRecover_findBlock_LeafBlock20,
    odGapRecover_findBlock_LeafBlock22, odGapRecover_findBlock_while_body76,
    odGapRecover_findBlock_while_end78⟩

/-! ### The second scan's invariant and exits

The head `land.rhs71` carries the counter `k` in the cell its `phi` selects: the
exit offset `%ee.0.lcssa` on the first visit (`if.end67`) and `%inc77` on every
later one (`while.body76`).  The budget `ip ≤ k + r` is the `BoundLoop` measure,
and `gapWsRun`'s prefix fact is the model's: every byte from `ee` to `k` is
whitespace.  The exit leaves the caller's memory and the `while.end78` `phi`'s
selected cell bound to the model's `gapS2`. -/

/-- The counter the second scan's head's `phi` carries, by predecessor. -/
def gapWsScanCarried (s : State) (c : Nat) : Prop :=
  (s.pre = some "if.end67" ∧
    lookupName s.env "%ee.0.lcssa" = some (.int 64 (BitVec.ofNat 64 c))) ∨
  (s.pre = some "while.body76" ∧
    lookupName s.env "%inc77" = some (.int 64 (BitVec.ofNat 64 c)))

/-- The second scan's invariant at `land.rhs71`: the head's block, the caller's
memory, the cells a step reads besides the counter, the carried counter, the
window's arithmetic (`ee ≤ k < ip < 2 ^ 63`), the budget `ip ≤ k + r`, and the
model's whitespace prefix. -/
def gapWsScanInv (bytes : List UInt8) (ip b ee c : Nat) (mem : Mem)
    (r : Nat) (s : State) (k : Nat) : Prop :=
  s.pc = "land.rhs71" ∧ s.mem = mem ∧
  lookupName s.env "%0" = some (.ptr b) ∧
  lookupName s.env "%c" = some (.ptr c) ∧
  lookupName s.env "%cond" = some (.int 64 (BitVec.ofNat 64 ip)) ∧
  gapWsScanCarried s k ∧
  ee ≤ k ∧ k < ip ∧ ip < 2 ^ 63 ∧ ip ≤ k + r ∧
  gapWsRun (k - ee) (bytes.drop ee) = k - ee

/-- The head's exit test: the byte at the counter is not a whitespace, or the
counter is the window's last position. -/
def gapWsScanAtBound (bytes : List UInt8) (ip : Nat) (_s : State) (k : Nat) : Bool :=
  (!gapIsWs (bytes.getD k 0)) || decide (k + 1 = ip)

/-- The second scan's exit: the state is at `while.end78` with the caller's
memory, and its `phi`'s selected cell carries the model's `gapS2`. -/
def gapWsScanExit (bytes : List UInt8) (ip ee c : Nat) (mem : Mem) (e : State) : Prop :=
  e.pc = "while.end78" ∧ e.mem = mem ∧
  lookupName e.env "%c" = some (.ptr c) ∧
  ∃ (leaf cell : String),
    e.pre = some leaf ∧
    phiIncoming leaf gapWsScanIncoming = some (Operand.reg cell) ∧
    lookupName e.env cell = some (.int 64 (BitVec.ofNat 64 (gapS2 bytes ip ee)))

/-- The invariant at the head's first visit: the exit offset is the counter, and
the budget is the whole bound. -/
theorem gapWsScanInv_seed {bytes : List UInt8} {ip b ee c : Nat} {mem : Mem} {s : State}
    (hlt : ee < ip) (hiplt : ip < 2 ^ 63)
    (hpc : s.pc = "land.rhs71") (hpre : s.pre = some "if.end67") (hmem : s.mem = mem)
    (hb : lookupName s.env "%0" = some (.ptr b))
    (hcur : lookupName s.env "%c" = some (.ptr c))
    (hee : lookupName s.env "%ee.0.lcssa" = some (.int 64 (BitVec.ofNat 64 ee)))
    (hcond : lookupName s.env "%cond" = some (.int 64 (BitVec.ofNat 64 ip))) :
    gapWsScanInv bytes ip b ee c mem ip s ee :=
  ⟨hpc, hmem, hb, hcur, hcond, Or.inl ⟨hpre, hee⟩, le_rfl, hlt, hiplt, by omega,
    by simp [gapWsRun]⟩

/-! ### The second scan's three prefixes

Each is the `∃ j ≤ cost` shape `BoundLoop`'s arms consume.  The routing is the
first scan's, with the leaves' destinations swapped: a whitespace byte takes an
advancing leaf to `while.body76`, any other byte a stopping leaf to
`while.end78`. -/

/-- **The second scan's non-whitespace exit.**  From the head over a
non-whitespace byte, the switch's three stopping routes reach `while.end78` with
the counter the model's `gapS2`, the scan writing nothing. -/
theorem gapWs_scan_exit_nonWs {calls : Calls} {bytes : List UInt8} {ip b ee c : Nat}
    {mem : Mem} {s : State} {r k : Nat}
    (hbytes : gapBytesAt mem bytes b ip)
    (hinv : gapWsScanInv bytes ip b ee c mem r s k)
    (hnws : gapIsWs (bytes.getD k 0) = false) :
    ∃ (e : State) (j : Nat), j ≤ 4 ∧ gapWsScanExit bytes ip ee c mem e ∧
      ∀ m, runFuel calls (j + m) odGapRecoverBody s =
        runFuel calls m odGapRecoverBody e := by
  obtain ⟨hpc, hmem, hb, hcur, hcond, hcarried, hkee, hklt, hiplt, _hbud, hpfx⟩ := hinv
  have hk63 : k < 2 ^ 63 := by omega
  have hbytes' : gapBytesAt s.mem bytes b ip := by rw [hmem]; exact hbytes
  have hread : readBytes s.mem (b + k) 1
      = some (natToBytes (gapByte (bytes.getD k 0)).toNat 1) :=
    gap_readOne hbytes' hklt rfl
  have hgap : gapS2 bytes ip ee = k := gapWsS2_of_prefix_nonWs hkee hklt hpfx hnws
  let s1 : State := stateAt (gapWsLandRhsEnv s.env b k (bytes.getD k 0))
    { s with pc := "NodeBlock26", pre := some "land.rhs71" }
  have h1 : step calls odGapRecoverBody s = .jump s1 := by
    rcases hcarried with ⟨hpre0, hee⟩ | ⟨hpre0, hinc⟩
    · have hh := gapWs_step_landRhs71_fromIfEnd67 (calls := calls) (env := s.env) (s := s)
        (b := b) (c := k) (byte := bytes.getD k 0) hpc hpre0 hb hee hread hk63
      have hst : stateAt s.env s = s := rfl
      simpa only [hst, s1] using hh
    · have hh := gapWs_step_landRhs71_fromWhileBody76 (calls := calls) (env := s.env) (s := s)
        (b := b) (c := k) (byte := bytes.getD k 0) hpc hpre0 hb hinc hread hk63
      have hst : stateAt s.env s = s := rfl
      simpa only [hst, s1] using hh
  have hs1 : lookupName s1.env "%15" = some (.int 8 (gapByte (bytes.getD k 0))) := by
    simp only [s1, stateAt, gapWsLandRhsEnv]
    block_lk
  have hroute := gapRoute_nonWs hnws
  rcases hroute with ⟨hb1, hb2⟩ | ⟨hb1, hb3, hb4⟩ | ⟨hb1, hb3, hb5⟩
  · -- `\t`/`\n`: `NodeBlock26` → `LeafBlock17` → `while.end78`
    let s2 : State := stateAt
      (("%Pivot27", .int 1 (evalICmp .slt (gapByte (bytes.getD k 0))
        (BitVec.ofNat 8 13))) :: s1.env)
      { s1 with pc := "LeafBlock17", pre := some "NodeBlock26" }
    have h2 : step calls odGapRecoverBody s1 = .jump s2 := by
      have hh := gapWs_step_NodeBlock26_toLeaf17 (calls := calls) (env := s1.env) (s := s1)
        (byte := bytes.getD k 0) rfl rfl hs1 hb1
      have hst : stateAt s1.env s1 = s1 := rfl
      simpa only [hst, s2] using hh
    have hs2 : lookupName s2.env "%15" = some (.int 8 (gapByte (bytes.getD k 0))) := by
      simp only [s2, stateAt]
      block_lk
    let s3 : State := stateAt
      (("%SwitchLeaf19", .int 1 (evalICmp .ule (gapOff (gapByte (bytes.getD k 0)))
          (BitVec.ofNat 8 1))) ::
        ("%.off18", .int 8 (gapOff (gapByte (bytes.getD k 0)))) :: s2.env)
      { s2 with pc := "while.end78", pre := some "LeafBlock17" }
    have h3 : step calls odGapRecoverBody s2 = .jump s3 := by
      have hh := gapWs_step_LeafBlock17_toWhileEnd78 (calls := calls) (env := s2.env)
        (s := s2) (byte := bytes.getD k 0) rfl rfl hs2 hb2
      have hst : stateAt s2.env s2 = s2 := rfl
      simpa only [hst, s3] using hh
    refine ⟨s3, 3, by omega, ?_, ?_⟩
    · refine ⟨rfl, ?_, ?_, ?_⟩
      · simp only [s3, s2, s1, stateAt]; exact hmem
      · simp only [s3, s2, s1, stateAt, gapWsLandRhsEnv]; block_lk
      · refine ⟨"LeafBlock17", "%s2.020", rfl, by decide, ?_⟩
        rw [hgap]
        simp only [s3, s2, s1, stateAt, gapWsLandRhsEnv]; block_lk
    · intro m
      rw [show 3 + m = 1 + (1 + (1 + m)) from by omega,
        runFuel_jump_prefix h1 (1 + (1 + m)),
        runFuel_jump_prefix h2 (1 + m), runFuel_jump_prefix h3 m]
  · -- `\r`: `NodeBlock26` → `NodeBlock24` → `LeafBlock20` → `while.end78`
    let s2 : State := stateAt
      (("%Pivot27", .int 1 (evalICmp .slt (gapByte (bytes.getD k 0))
        (BitVec.ofNat 8 13))) :: s1.env)
      { s1 with pc := "NodeBlock24", pre := some "NodeBlock26" }
    have h2 : step calls odGapRecoverBody s1 = .jump s2 := by
      have hh := gapWs_step_NodeBlock26_toNodeBlock24 (calls := calls) (env := s1.env)
        (s := s1) (byte := bytes.getD k 0) rfl rfl hs1 hb1
      have hst : stateAt s1.env s1 = s1 := rfl
      simpa only [hst, s2] using hh
    have hs2 : lookupName s2.env "%15" = some (.int 8 (gapByte (bytes.getD k 0))) := by
      simp only [s2, stateAt]
      block_lk
    let s3 : State := stateAt
      (("%Pivot25", .int 1 (evalICmp .slt (gapByte (bytes.getD k 0))
        (BitVec.ofNat 8 32))) :: s2.env)
      { s2 with pc := "LeafBlock20", pre := some "NodeBlock24" }
    have h3 : step calls odGapRecoverBody s2 = .jump s3 := by
      have hh := gapWs_step_NodeBlock24_toLeaf20 (calls := calls) (env := s2.env) (s := s2)
        (byte := bytes.getD k 0) rfl rfl hs2 hb3
      have hst : stateAt s2.env s2 = s2 := rfl
      simpa only [hst, s3] using hh
    have hs3 : lookupName s3.env "%15" = some (.int 8 (gapByte (bytes.getD k 0))) := by
      simp only [s3, stateAt]
      block_lk
    let s4 : State := stateAt
      (("%SwitchLeaf21", .int 1 (evalICmp .eq (gapByte (bytes.getD k 0))
        (BitVec.ofNat 8 13))) :: s3.env)
      { s3 with pc := "while.end78", pre := some "LeafBlock20" }
    have h4 : step calls odGapRecoverBody s3 = .jump s4 := by
      have hh := gapWs_step_LeafBlock20_toWhileEnd78 (calls := calls) (env := s3.env)
        (s := s3) (byte := bytes.getD k 0) rfl rfl hs3 hb4
      have hst : stateAt s3.env s3 = s3 := rfl
      simpa only [hst, s4] using hh
    refine ⟨s4, 4, by omega, ?_, ?_⟩
    · refine ⟨rfl, ?_, ?_, ?_⟩
      · simp only [s4, s3, s2, s1, stateAt]; exact hmem
      · simp only [s4, s3, s2, s1, stateAt, gapWsLandRhsEnv]; block_lk
      · refine ⟨"LeafBlock20", "%s2.020", rfl, by decide, ?_⟩
        rw [hgap]
        simp only [s4, s3, s2, s1, stateAt, gapWsLandRhsEnv]; block_lk
    · intro m
      rw [show 4 + m = 1 + (1 + (1 + (1 + m))) from by omega,
        runFuel_jump_prefix h1 (1 + (1 + (1 + m))),
        runFuel_jump_prefix h2 (1 + (1 + m)),
        runFuel_jump_prefix h3 (1 + m), runFuel_jump_prefix h4 m]
  · -- `\ `: `NodeBlock26` → `NodeBlock24` → `LeafBlock22` → `while.end78`
    let s2 : State := stateAt
      (("%Pivot27", .int 1 (evalICmp .slt (gapByte (bytes.getD k 0))
        (BitVec.ofNat 8 13))) :: s1.env)
      { s1 with pc := "NodeBlock24", pre := some "NodeBlock26" }
    have h2 : step calls odGapRecoverBody s1 = .jump s2 := by
      have hh := gapWs_step_NodeBlock26_toNodeBlock24 (calls := calls) (env := s1.env)
        (s := s1) (byte := bytes.getD k 0) rfl rfl hs1 hb1
      have hst : stateAt s1.env s1 = s1 := rfl
      simpa only [hst, s2] using hh
    have hs2 : lookupName s2.env "%15" = some (.int 8 (gapByte (bytes.getD k 0))) := by
      simp only [s2, stateAt]
      block_lk
    let s3 : State := stateAt
      (("%Pivot25", .int 1 (evalICmp .slt (gapByte (bytes.getD k 0))
        (BitVec.ofNat 8 32))) :: s2.env)
      { s2 with pc := "LeafBlock22", pre := some "NodeBlock24" }
    have h3 : step calls odGapRecoverBody s2 = .jump s3 := by
      have hh := gapWs_step_NodeBlock24_toLeaf22 (calls := calls) (env := s2.env) (s := s2)
        (byte := bytes.getD k 0) rfl rfl hs2 hb3
      have hst : stateAt s2.env s2 = s2 := rfl
      simpa only [hst, s3] using hh
    have hs3 : lookupName s3.env "%15" = some (.int 8 (gapByte (bytes.getD k 0))) := by
      simp only [s3, stateAt]
      block_lk
    let s4 : State := stateAt
      (("%SwitchLeaf23", .int 1 (evalICmp .eq (gapByte (bytes.getD k 0))
        (BitVec.ofNat 8 32))) :: s3.env)
      { s3 with pc := "while.end78", pre := some "LeafBlock22" }
    have h4 : step calls odGapRecoverBody s3 = .jump s4 := by
      have hh := gapWs_step_LeafBlock22_toWhileEnd78 (calls := calls) (env := s3.env)
        (s := s3) (byte := bytes.getD k 0) rfl rfl hs3 hb5
      have hst : stateAt s3.env s3 = s3 := rfl
      simpa only [hst, s4] using hh
    refine ⟨s4, 4, by omega, ?_, ?_⟩
    · refine ⟨rfl, ?_, ?_, ?_⟩
      · simp only [s4, s3, s2, s1, stateAt]; exact hmem
      · simp only [s4, s3, s2, s1, stateAt, gapWsLandRhsEnv]; block_lk
      · refine ⟨"LeafBlock22", "%s2.020", rfl, by decide, ?_⟩
        rw [hgap]
        simp only [s4, s3, s2, s1, stateAt, gapWsLandRhsEnv]; block_lk
    · intro m
      rw [show 4 + m = 1 + (1 + (1 + (1 + m))) from by omega,
        runFuel_jump_prefix h1 (1 + (1 + (1 + m))),
        runFuel_jump_prefix h2 (1 + (1 + m)),
        runFuel_jump_prefix h3 (1 + m), runFuel_jump_prefix h4 m]

/-- **The second scan's advance head.**  From the head over a whitespace byte's
three advancing routes, the switch reaches `while.body76` with the cells its step
reads still bound. -/
theorem gapWs_scan_toWhileBody {calls : Calls} {bytes : List UInt8} {ip b ee c : Nat}
    {mem : Mem} {s : State} {r k : Nat}
    (hbytes : gapBytesAt mem bytes b ip)
    (hinv : gapWsScanInv bytes ip b ee c mem r s k)
    (hws : gapIsWs (bytes.getD k 0) = true) :
    ∃ (e : State) (j : Nat), j ≤ 4 ∧ e.pc = "while.body76" ∧ e.mem = mem ∧
      lookupName e.env "%s2.020" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName e.env "%cond" = some (.int 64 (BitVec.ofNat 64 ip)) ∧
      lookupName e.env "%0" = some (.ptr b) ∧
      lookupName e.env "%c" = some (.ptr c) ∧
      ∀ m, runFuel calls (j + m) odGapRecoverBody s =
        runFuel calls m odGapRecoverBody e := by
  obtain ⟨hpc, hmem, hb, hcur, hcond, hcarried, _hkee, hklt, _hiplt, _hbud, _hpfx⟩ := hinv
  have hk63 : k < 2 ^ 63 := by omega
  have hbytes' : gapBytesAt s.mem bytes b ip := by rw [hmem]; exact hbytes
  have hread : readBytes s.mem (b + k) 1
      = some (natToBytes (gapByte (bytes.getD k 0)).toNat 1) :=
    gap_readOne hbytes' hklt rfl
  let s1 : State := stateAt (gapWsLandRhsEnv s.env b k (bytes.getD k 0))
    { s with pc := "NodeBlock26", pre := some "land.rhs71" }
  have h1 : step calls odGapRecoverBody s = .jump s1 := by
    rcases hcarried with ⟨hpre0, hee⟩ | ⟨hpre0, hinc⟩
    · have hh := gapWs_step_landRhs71_fromIfEnd67 (calls := calls) (env := s.env) (s := s)
        (b := b) (c := k) (byte := bytes.getD k 0) hpc hpre0 hb hee hread hk63
      have hst : stateAt s.env s = s := rfl
      simpa only [hst, s1] using hh
    · have hh := gapWs_step_landRhs71_fromWhileBody76 (calls := calls) (env := s.env) (s := s)
        (b := b) (c := k) (byte := bytes.getD k 0) hpc hpre0 hb hinc hread hk63
      have hst : stateAt s.env s = s := rfl
      simpa only [hst, s1] using hh
  have hs1 : lookupName s1.env "%15" = some (.int 8 (gapByte (bytes.getD k 0))) := by
    simp only [s1, stateAt, gapWsLandRhsEnv]
    block_lk
  have hroute := gapRoute_ws hws
  rcases hroute with ⟨hb1, hb2⟩ | ⟨hb1, hb3, hb4⟩ | ⟨hb1, hb3, hb5⟩
  · -- `\t`/`\n`: `LeafBlock17` advances
    let s2 : State := stateAt
      (("%Pivot27", .int 1 (evalICmp .slt (gapByte (bytes.getD k 0))
        (BitVec.ofNat 8 13))) :: s1.env)
      { s1 with pc := "LeafBlock17", pre := some "NodeBlock26" }
    have h2 : step calls odGapRecoverBody s1 = .jump s2 := by
      have hh := gapWs_step_NodeBlock26_toLeaf17 (calls := calls) (env := s1.env) (s := s1)
        (byte := bytes.getD k 0) rfl rfl hs1 hb1
      have hst : stateAt s1.env s1 = s1 := rfl
      simpa only [hst, s2] using hh
    have hs2 : lookupName s2.env "%15" = some (.int 8 (gapByte (bytes.getD k 0))) := by
      simp only [s2, stateAt]
      block_lk
    let s3 : State := stateAt
      (("%SwitchLeaf19", .int 1 (evalICmp .ule (gapOff (gapByte (bytes.getD k 0)))
          (BitVec.ofNat 8 1))) ::
        ("%.off18", .int 8 (gapOff (gapByte (bytes.getD k 0)))) :: s2.env)
      { s2 with pc := "while.body76", pre := some "LeafBlock17" }
    have h3 : step calls odGapRecoverBody s2 = .jump s3 := by
      have hh := gapWs_step_LeafBlock17_toWhileBody76 (calls := calls) (env := s2.env)
        (s := s2) (byte := bytes.getD k 0) rfl rfl hs2 hb2
      have hst : stateAt s2.env s2 = s2 := rfl
      simpa only [hst, s3] using hh
    refine ⟨s3, 3, by omega, rfl, hmem, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [s3, s2, s1, stateAt, gapWsLandRhsEnv]; block_lk
    · simp only [s3, s2, s1, stateAt, gapWsLandRhsEnv]; block_lk
    · simp only [s3, s2, s1, stateAt, gapWsLandRhsEnv]; block_lk
    · simp only [s3, s2, s1, stateAt, gapWsLandRhsEnv]; block_lk
    · intro m
      rw [show 3 + m = 1 + (1 + (1 + m)) from by omega,
        runFuel_jump_prefix h1 (1 + (1 + m)),
        runFuel_jump_prefix h2 (1 + m), runFuel_jump_prefix h3 m]
  · -- `\r`: `LeafBlock20` advances
    let s2 : State := stateAt
      (("%Pivot27", .int 1 (evalICmp .slt (gapByte (bytes.getD k 0))
        (BitVec.ofNat 8 13))) :: s1.env)
      { s1 with pc := "NodeBlock24", pre := some "NodeBlock26" }
    have h2 : step calls odGapRecoverBody s1 = .jump s2 := by
      have hh := gapWs_step_NodeBlock26_toNodeBlock24 (calls := calls) (env := s1.env)
        (s := s1) (byte := bytes.getD k 0) rfl rfl hs1 hb1
      have hst : stateAt s1.env s1 = s1 := rfl
      simpa only [hst, s2] using hh
    have hs2 : lookupName s2.env "%15" = some (.int 8 (gapByte (bytes.getD k 0))) := by
      simp only [s2, stateAt]
      block_lk
    let s3 : State := stateAt
      (("%Pivot25", .int 1 (evalICmp .slt (gapByte (bytes.getD k 0))
        (BitVec.ofNat 8 32))) :: s2.env)
      { s2 with pc := "LeafBlock20", pre := some "NodeBlock24" }
    have h3 : step calls odGapRecoverBody s2 = .jump s3 := by
      have hh := gapWs_step_NodeBlock24_toLeaf20 (calls := calls) (env := s2.env) (s := s2)
        (byte := bytes.getD k 0) rfl rfl hs2 hb3
      have hst : stateAt s2.env s2 = s2 := rfl
      simpa only [hst, s3] using hh
    have hs3 : lookupName s3.env "%15" = some (.int 8 (gapByte (bytes.getD k 0))) := by
      simp only [s3, stateAt]
      block_lk
    let s4 : State := stateAt
      (("%SwitchLeaf21", .int 1 (evalICmp .eq (gapByte (bytes.getD k 0))
        (BitVec.ofNat 8 13))) :: s3.env)
      { s3 with pc := "while.body76", pre := some "LeafBlock20" }
    have h4 : step calls odGapRecoverBody s3 = .jump s4 := by
      have hh := gapWs_step_LeafBlock20_toWhileBody76 (calls := calls) (env := s3.env)
        (s := s3) (byte := bytes.getD k 0) rfl rfl hs3 hb4
      have hst : stateAt s3.env s3 = s3 := rfl
      simpa only [hst, s4] using hh
    refine ⟨s4, 4, by omega, rfl, hmem, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [s4, s3, s2, s1, stateAt, gapWsLandRhsEnv]; block_lk
    · simp only [s4, s3, s2, s1, stateAt, gapWsLandRhsEnv]; block_lk
    · simp only [s4, s3, s2, s1, stateAt, gapWsLandRhsEnv]; block_lk
    · simp only [s4, s3, s2, s1, stateAt, gapWsLandRhsEnv]; block_lk
    · intro m
      rw [show 4 + m = 1 + (1 + (1 + (1 + m))) from by omega,
        runFuel_jump_prefix h1 (1 + (1 + (1 + m))),
        runFuel_jump_prefix h2 (1 + (1 + m)),
        runFuel_jump_prefix h3 (1 + m), runFuel_jump_prefix h4 m]
  · -- `\ `: `LeafBlock22` advances
    let s2 : State := stateAt
      (("%Pivot27", .int 1 (evalICmp .slt (gapByte (bytes.getD k 0))
        (BitVec.ofNat 8 13))) :: s1.env)
      { s1 with pc := "NodeBlock24", pre := some "NodeBlock26" }
    have h2 : step calls odGapRecoverBody s1 = .jump s2 := by
      have hh := gapWs_step_NodeBlock26_toNodeBlock24 (calls := calls) (env := s1.env)
        (s := s1) (byte := bytes.getD k 0) rfl rfl hs1 hb1
      have hst : stateAt s1.env s1 = s1 := rfl
      simpa only [hst, s2] using hh
    have hs2 : lookupName s2.env "%15" = some (.int 8 (gapByte (bytes.getD k 0))) := by
      simp only [s2, stateAt]
      block_lk
    let s3 : State := stateAt
      (("%Pivot25", .int 1 (evalICmp .slt (gapByte (bytes.getD k 0))
        (BitVec.ofNat 8 32))) :: s2.env)
      { s2 with pc := "LeafBlock22", pre := some "NodeBlock24" }
    have h3 : step calls odGapRecoverBody s2 = .jump s3 := by
      have hh := gapWs_step_NodeBlock24_toLeaf22 (calls := calls) (env := s2.env) (s := s2)
        (byte := bytes.getD k 0) rfl rfl hs2 hb3
      have hst : stateAt s2.env s2 = s2 := rfl
      simpa only [hst, s3] using hh
    have hs3 : lookupName s3.env "%15" = some (.int 8 (gapByte (bytes.getD k 0))) := by
      simp only [s3, stateAt]
      block_lk
    let s4 : State := stateAt
      (("%SwitchLeaf23", .int 1 (evalICmp .eq (gapByte (bytes.getD k 0))
        (BitVec.ofNat 8 32))) :: s3.env)
      { s3 with pc := "while.body76", pre := some "LeafBlock22" }
    have h4 : step calls odGapRecoverBody s3 = .jump s4 := by
      have hh := gapWs_step_LeafBlock22_toWhileBody76 (calls := calls) (env := s3.env)
        (s := s3) (byte := bytes.getD k 0) rfl rfl hs3 hb5
      have hst : stateAt s3.env s3 = s3 := rfl
      simpa only [hst, s4] using hh
    refine ⟨s4, 4, by omega, rfl, hmem, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [s4, s3, s2, s1, stateAt, gapWsLandRhsEnv]; block_lk
    · simp only [s4, s3, s2, s1, stateAt, gapWsLandRhsEnv]; block_lk
    · simp only [s4, s3, s2, s1, stateAt, gapWsLandRhsEnv]; block_lk
    · simp only [s4, s3, s2, s1, stateAt, gapWsLandRhsEnv]; block_lk
    · intro m
      rw [show 4 + m = 1 + (1 + (1 + (1 + m))) from by omega,
        runFuel_jump_prefix h1 (1 + (1 + (1 + m))),
        runFuel_jump_prefix h2 (1 + (1 + m)),
        runFuel_jump_prefix h3 (1 + m), runFuel_jump_prefix h4 m]

/-- **The second scan's `ip` exit.**  From the head over a whitespace byte whose
successor is the window's end, five control steps reach `while.end78`, and the
model's second loop has run the whole window. -/
theorem gapWs_scan_exit_ip {calls : Calls} {bytes : List UInt8} {ip b ee c : Nat}
    {mem : Mem} {s : State} {r k : Nat}
    (hbytes : gapBytesAt mem bytes b ip) (hblen : bytes.length = ip)
    (hinv : gapWsScanInv bytes ip b ee c mem r s k)
    (hws : gapIsWs (bytes.getD k 0) = true) (hnext : k + 1 = ip) :
    ∃ (e : State) (j : Nat), j ≤ 5 ∧ gapWsScanExit bytes ip ee c mem e ∧
      ∀ m, runFuel calls (j + m) odGapRecoverBody s =
        runFuel calls m odGapRecoverBody e := by
  obtain ⟨e1, j1, hj1, hpc1, hmem1, hcell1, hcond1, _h0cell, hcur1, hrun1⟩ :=
    gapWs_scan_toWhileBody (calls := calls) hbytes hinv hws
  obtain ⟨hpc, hmem, hb, hcur, hcond, hcarried, hkee, hklt, hiplt, _hbud, hpfx⟩ := hinv
  have hip64 : ip < 2 ^ 64 := by omega
  have hee : gapS2 bytes ip ee = ip :=
    gapWsS2_of_prefix_all hblen hkee hnext hpfx hws
  have hbit : evalICmp .eq (BitVec.ofNat 64 k + 1) (BitVec.ofNat 64 ip) = 1#1 :=
    gap_scan_atIp_bit hip64 hnext
  let sE : State := stateAt
    (("%exitcond24.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 k + 1)
        (BitVec.ofNat 64 ip))) ::
      ("%inc77", .int 64 (BitVec.ofNat 64 k + 1)) :: e1.env)
    { e1 with pc := "while.end78", pre := some "while.body76" }
  have hstep : step calls odGapRecoverBody e1 = .jump sE := by
    have hh := gapWs_step_whileBody76_toWhileEnd78 (calls := calls) (env := e1.env)
      (s := e1) (c := k) (ip := ip) hpc1 hcell1 hcond1 hbit
    have hst : stateAt e1.env e1 = e1 := rfl
    simpa only [hst, sE] using hh
  refine ⟨sE, j1 + 1, by omega, ?_, ?_⟩
  · refine ⟨rfl, ?_, ?_, ?_⟩
    · rw [show sE.mem = e1.mem from rfl, hmem1]
    · simp only [sE, stateAt]; block_lk
    · refine ⟨"while.body76", "%cond", rfl, by decide, ?_⟩
      rw [hee]
      simp only [sE, stateAt]; block_lk
  · intro m
    rw [show j1 + 1 + m = j1 + (1 + m) from by omega, hrun1 (1 + m),
      runFuel_jump_prefix hstep m]

/-- **The second scan's advance.**  From the head over a whitespace byte whose
successor is inside the window, five control steps re-enter `land.rhs71` with the
counter advanced and the invariant at one unit of budget less. -/
theorem gapWs_scan_step_loop {calls : Calls} {bytes : List UInt8} {ip b ee c : Nat}
    {mem : Mem} {s : State} {r k : Nat}
    (hbytes : gapBytesAt mem bytes b ip) (hblen : bytes.length = ip)
    (hinv : gapWsScanInv bytes ip b ee c mem (r + 1) s k)
    (hws : gapIsWs (bytes.getD k 0) = true) (hnext : k + 1 ≠ ip) :
    ∃ (e : State) (k' : Nat) (j : Nat), j ≤ 5 ∧ e.pc = "land.rhs71" ∧ k < k' ∧
      gapWsScanInv bytes ip b ee c mem r e k' ∧
      ∀ m, runFuel calls (j + m) odGapRecoverBody s =
        runFuel calls m odGapRecoverBody e := by
  obtain ⟨e1, j1, hj1, hpc1, hmem1, hcell1, hcond1, _h0cell, _hcur1, hrun1⟩ :=
    gapWs_scan_toWhileBody (calls := calls) hbytes hinv hws
  obtain ⟨hpc, hmem, hb, hcur, hcond, hcarried, hkee, hklt, hiplt, hbud, hpfx⟩ := hinv
  have hip64 : ip < 2 ^ 64 := by omega
  have hkp : k - ee < (bytes.drop ee).length := by
    rw [List.length_drop, hblen]; omega
  have hbit : evalICmp .eq (BitVec.ofNat 64 k + 1) (BitVec.ofNat 64 ip) = 0#1 :=
    gap_scan_offIp_bit hklt hip64 hnext
  let sE : State := stateAt
    (("%exitcond24.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 k + 1)
        (BitVec.ofNat 64 ip))) ::
      ("%inc77", .int 64 (BitVec.ofNat 64 k + 1)) :: e1.env)
    { e1 with pc := "land.rhs71", pre := some "while.body76" }
  have hstep : step calls odGapRecoverBody e1 = .jump sE := by
    have hh := gapWs_step_whileBody76_toLandRhs71 (calls := calls) (env := e1.env)
      (s := e1) (c := k) (ip := ip) hpc1 hcell1 hcond1 hbit
    have hst : stateAt e1.env e1 = e1 := rfl
    simpa only [hst, sE] using hh
  have hseed : gapWsRun (k + 1 - ee) (bytes.drop ee) = k + 1 - ee := by
    rw [show k + 1 - ee = (k - ee) + 1 from by omega,
      gapWsRun_succ hpfx hkp
        (by rw [gap_getD_drop_add, show ee + (k - ee) = k from by omega]; exact hws)]
  refine ⟨sE, k + 1, j1 + 1, by omega, rfl, by omega, ?_, ?_⟩
  · refine ⟨rfl, hmem1, ?_, ?_, ?_, Or.inr ⟨rfl, ?_⟩, by omega, by omega, hiplt,
      by omega, hseed⟩
    · simp only [sE, stateAt]; block_lk
    · simp only [sE, stateAt]; block_lk
    · simp only [sE, stateAt]; block_lk
    · simp only [sE, stateAt]
      rw [gap_ofNat64_add_one (c := k) (by omega)]
      block_lk
  · intro m
    rw [show j1 + 1 + m = j1 + (1 + m) from by omega, hrun1 (1 + m),
      runFuel_jump_prefix hstep m]

/-! ### The loop instance

The bound is `ip`, the measure the budget `ip ≤ k + r`, and the per-iteration
control-step bound five.  The exits are the two the head's own test names: the
switch on a non-whitespace byte, and `while.body76`'s equality with `ip` on
whitespace. -/

/-- **The second scan as a `BoundLoop`.**  The budget's zero edge is empty: the
invariant asks for `k < ip` and for `ip ≤ k`, so no head state carries zero
budget. -/
def gapWsScanLoop (calls : Calls) (bytes : List UInt8) (ip b ee c : Nat) (mem : Mem)
    (hbytes : gapBytesAt mem bytes b ip) (hblen : bytes.length = ip) :
    BoundLoop calls odGapRecoverBody where
  head := "land.rhs71"
  exitBlock := "while.end78"
  N := ip
  cost := 5
  Inv := gapWsScanInv bytes ip b ee c mem
  atBound := gapWsScanAtBound bytes ip
  Exit := fun e => e.pc = "while.end78"
  ExitWord := gapWsScanExit bytes ip ee c mem
  step_exit := by
    intro r s k hinv hat
    unfold gapWsScanAtBound at hat
    by_cases hws : gapIsWs (bytes.getD k 0) = true
    · have hns : (!gapIsWs (bytes.getD k 0)) = false := by
        rw [hws]; rfl
      have hid : decide (k + 1 = ip) = true := by
        rcases Bool.or_eq_true_iff.mp hat with h | h
        · rw [hns] at h
          exact absurd h (by decide)
        · exact h
      obtain ⟨e, j, hj, hexit, hrun⟩ :=
        gapWs_scan_exit_ip hbytes hblen hinv hws (of_decide_eq_true hid)
      exact ⟨e, j, hj, hexit.1, hexit, hrun⟩
    · have hfalse : gapIsWs (bytes.getD k 0) = false := by
        cases h : gapIsWs (bytes.getD k 0) with
        | false => rfl
        | true => exact absurd h hws
      obtain ⟨e, j, hj, hexit, hrun⟩ := gapWs_scan_exit_nonWs hbytes hinv hfalse
      exact ⟨e, j, by omega, hexit.1, hexit, hrun⟩
  step_loop := by
    intro r s k hinv hat
    unfold gapWsScanAtBound at hat
    rcases Bool.or_eq_false_iff.mp hat with ⟨hns, hid⟩
    have hws : gapIsWs (bytes.getD k 0) = true := by
      cases h : gapIsWs (bytes.getD k 0) with
      | true => rfl
      | false =>
        rw [h] at hns
        exact absurd hns (by decide)
    exact gapWs_scan_step_loop hbytes hblen hinv hws (of_decide_eq_false hid)
  exit_at_zero := by
    intro s k hinv
    obtain ⟨_, _, _, _, _, _, _, hklt, _, hbud, _⟩ := hinv
    exact absurd hbud (by omega)
  budget := by
    intro r s k hinv
    obtain ⟨_, _, _, _, _, _, hkee, hklt, _, hbud, _⟩ := hinv
    exact ⟨by omega, hbud⟩

/-- **The second scan's run from its head.**  From `land.rhs71` with `r`
iterations of budget, the scan reaches `while.end78` within `(r + 1) * 5` control
steps. -/
theorem gapWsScanLoop_run_from {calls : Calls} {bytes : List UInt8} {ip b ee c : Nat}
    {mem : Mem} (hbytes : gapBytesAt mem bytes b ip) (hblen : bytes.length = ip)
    (r : Nat) (s : State) (k : Nat) (h : gapWsScanInv bytes ip b ee c mem r s k) :
    ∃ (e : State) (j : Nat), j ≤ (r + 1) * 5 ∧ e.pc = "while.end78" ∧
      gapWsScanExit bytes ip ee c mem e ∧
      ∀ m, runFuel calls (j + m) odGapRecoverBody s =
        runFuel calls m odGapRecoverBody e :=
  (gapWsScanLoop calls bytes ip b ee c mem hbytes hblen).run_from r s k h

/-- **The second scan's run.**  At the whole bound as its budget, the scan of the
document `[0, ip)` from the exit offset `ee` reaches `while.end78` within
`(ip + 1) * 5` control steps, and the run continues identically from there. -/
theorem gapWsScanLoop_run {calls : Calls} {bytes : List UInt8} {ip b ee c : Nat}
    {mem : Mem} (hbytes : gapBytesAt mem bytes b ip) (hblen : bytes.length = ip)
    (s : State) (k : Nat) (h : gapWsScanInv bytes ip b ee c mem ip s k) (m : Nat) :
    ∃ (e : State) (j : Nat), j ≤ (ip + 1) * 5 ∧ e.pc = "while.end78" ∧
      gapWsScanExit bytes ip ee c mem e ∧
      runFuel calls (j + m) odGapRecoverBody s =
        runFuel calls m odGapRecoverBody e :=
  (gapWsScanLoop calls bytes ip b ee c mem hbytes hblen).run s k h m

/-! ### The exit, continued

`while.end78`'s `phi` selects the exit offset from the leaf the scan left
through, and the block writes the refusal record: kind 0, the offset, and tag 4
at `%msg2.i138`.  `cleanup82` then returns `void`. -/

/-- **The second scan's exit, continued.**  From `while.end78` the body writes
the record's three words — the model's `stage2ErrSetMsg mem e (gapS2 …) 4` — and
`cleanup82` returns `void`.  The scan itself wrote nothing: the record is the only
memory this continuation touches. -/
theorem gapWs_whileEnd78_continue {calls : Calls} {bytes : List UInt8}
    {ip ee c e : Nat} {mem : Mem} {e0 : State}
    (heele : ee ≤ ip) (hiplt : ip < 2 ^ 63)
    (hexit : gapWsScanExit bytes ip ee c mem e0)
    (he : readBytes mem (c + 1112) 8 = some (natToBytes e 8)) (he64 : e < 2 ^ 64) :
    ∃ (j : Nat), j ≤ 2 ∧
      runFuel calls j odGapRecoverBody e0 =
        some (.ret none (stage2ErrSetMsg mem e (gapS2 bytes ip ee) 4)) := by
  obtain ⟨hpc0, hmem0, hcur0, leaf, cell, hpre0, hinc0, hcell0⟩ := hexit
  have hs2 : gapS2 bytes ip ee < 2 ^ 64 := by
    have hle := gapWsS2_le (bytes := bytes) heele
    omega
  have he' : readBytes e0.mem (c + 1112) 8 = some (natToBytes e 8) := by
    rw [hmem0]; exact he
  let envNew : Env :=
    ("%msg2.i138", .ptr (e + 16)) :: ("%off1.i137", .ptr (e + 8)) ::
      ("%16", .ptr e) :: ("%e79", .ptr (c + 1112)) ::
      ("%s2.0.lcssa", .int 64 (BitVec.ofNat 64 (gapS2 bytes ip ee))) :: e0.env
  let sret : State :=
    { e0 with pc := "cleanup82", pre := some "while.end78", mem := stage2ErrSetMsg e0.mem e (gapS2 bytes ip ee) 4 }
  have hstep : step calls odGapRecoverBody e0 = .jump (stateAt envNew sret) := by
    have hh := gapWs_step_whileEnd78 (calls := calls) (env := e0.env) (s := e0)
      (p := leaf) (cell := cell) (c := c) (s2 := gapS2 bytes ip ee) (e := e)
      hpc0 hpre0 hcur0 hinc0 hcell0 he' he64 hs2
    have hst : stateAt e0.env e0 = e0 := rfl
    rw [hst] at hh
    simpa only [envNew, sret, stage2ErrSetMsg, stage2ErrSet, wordBytes] using hh
  have hcl : step calls odGapRecoverBody (stateAt envNew sret) =
      .ret none (stateAt envNew sret) :=
    gap_step_cleanup82 (calls := calls) (env := envNew) (s := sret) rfl
  have hfin : (stateAt envNew sret).mem = stage2ErrSetMsg mem e (gapS2 bytes ip ee) 4 := by
    simp only [stateAt, sret, hmem0]
  refine ⟨2, by omega, ?_⟩
  rw [show 2 = 1 + 1 from rfl, runFuel_jump_prefix hstep 1,
    show runFuel calls 1 odGapRecoverBody (stateAt envNew sret) =
      some (.ret none (stateAt envNew sret).mem) from by simp only [runFuel, hcl],
    hfin]

/-! ### The run from `if.end67` -/

/-- **The second scan, at the staging `if.end67` hands it.**  From the block the
literal and number paths enter, with the cursor's `e` record and the document's
window, the body either enters `land.rhs71` and scans the whitespace gap or, when
the first loop already reached `ip`, goes straight to `while.end78`.  The run
returns `void` with the record written at the model's `gapS2` and tag 4
(`gapExtraWrite`), and `(ip + 1) * 5 + 3` control steps bound it. -/
theorem gapWs_secondScan_run {calls : Calls} {mem : Mem} {bytes : List UInt8}
    {ip b ee c e : Nat} {s : State}
    (hpc : s.pc = "if.end67") (hmem : s.mem = mem)
    (hb : lookupName s.env "%0" = some (.ptr b))
    (hcur : lookupName s.env "%c" = some (.ptr c))
    (hee : lookupName s.env "%ee.0.lcssa" = some (.int 64 (BitVec.ofNat 64 ee)))
    (hcond : lookupName s.env "%cond" = some (.int 64 (BitVec.ofNat 64 ip)))
    (he : readBytes mem (c + 1112) 8 = some (natToBytes e 8)) (he64 : e < 2 ^ 64)
    (hbytes : gapBytesAt mem bytes b ip) (hblen : bytes.length = ip)
    (heele : ee ≤ ip) (hiplt : ip < 2 ^ 63) :
    ∃ (j : Nat), j ≤ 1 + (ip + 1) * 5 + 2 ∧
      runFuel calls j odGapRecoverBody s =
        some (.ret none (stage2ErrSetMsg mem e (gapS2 bytes ip ee) 4)) ∧
      gapExtraWrite bytes ip ee = GapWrite.err (gapS2 bytes ip ee) gapTagExtra ∧
      readBytes (stage2ErrSetMsg mem e (gapS2 bytes ip ee) 4) (e + 8) 8 =
        some (wordBytes 8 (gapS2 bytes ip ee)) ∧
      readBytes (stage2ErrSetMsg mem e (gapS2 bytes ip ee) 4) (e + 16) 8 =
        some (wordBytes 8 gapTagExtra) := by
  by_cases hlt : ee < ip
  · -- the head is entered
    have hbit : evalICmp .ult (BitVec.ofNat 64 ee) (BitVec.ofNat 64 ip) = 1#1 :=
      gap_ult_one (by omega) (by omega) hlt
    let s1 : State := stateAt
      (("%cmp6919", .int 1 (evalICmp .ult (BitVec.ofNat 64 ee)
        (BitVec.ofNat 64 ip))) :: s.env)
      { s with pc := "land.rhs71", pre := some "if.end67" }
    have hstep1 : step calls odGapRecoverBody s = .jump s1 := by
      have hh := gapWs_step_ifEnd67 (calls := calls) (env := s.env) (s := s)
        (ee := ee) (ip := ip) hpc hee hcond
      rw [if_pos hbit] at hh
      have hst : stateAt s.env s = s := rfl
      simpa only [hst, s1] using hh
    have hseed : gapWsScanInv bytes ip b ee c mem ip s1 ee := by
      refine ⟨rfl, ?_, ?_, ?_, ?_, Or.inl ⟨rfl, ?_⟩, le_rfl, hlt, hiplt, by omega,
        by simp [gapWsRun]⟩
      · simp only [s1, stateAt]; exact hmem
      · simp only [s1, stateAt]; block_lk
      · simp only [s1, stateAt]; block_lk
      · simp only [s1, stateAt]; block_lk
      · simp only [s1, stateAt]; block_lk
    obtain ⟨e0, jl, hjl, hpcE, hexitE, hrunLoop⟩ :=
      gapWsScanLoop_run (calls := calls) hbytes hblen s1 ee hseed 2
    obtain ⟨jc, hjc, hrunCont⟩ :=
      gapWs_whileEnd78_continue heele hiplt hexitE he he64
    have hcont2 : runFuel calls 2 odGapRecoverBody e0 =
        some (.ret none (stage2ErrSetMsg mem e (gapS2 bytes ip ee) 4)) :=
      runFuel_mono_le hjc hrunCont
    refine ⟨1 + jl + 2, by omega, ?_, rfl, ?_, ?_⟩
    · rw [show 1 + jl + 2 = 1 + (jl + 2) from by omega,
        runFuel_jump_prefix hstep1 (jl + 2), hrunLoop]
      exact hcont2
    · exact stage2ErrSetMsg_off_read mem e (gapS2 bytes ip ee) 4
    · exact stage2ErrSetMsg_msg_read mem e (gapS2 bytes ip ee) 4
  · -- the first loop already reached `ip`
    have heq : ee = ip := by omega
    have hbit : evalICmp .ult (BitVec.ofNat 64 ee) (BitVec.ofNat 64 ip) = 0#1 := by
      rw [heq]
      exact gap_ult_self _
    let e0 : State := stateAt
      (("%cmp6919", .int 1 (evalICmp .ult (BitVec.ofNat 64 ee)
        (BitVec.ofNat 64 ip))) :: s.env)
      { s with pc := "while.end78", pre := some "if.end67" }
    have hstep1 : step calls odGapRecoverBody s = .jump e0 := by
      have hh := gapWs_step_ifEnd67 (calls := calls) (env := s.env) (s := s)
        (ee := ee) (ip := ip) hpc hee hcond
      rw [if_neg (by rw [hbit]; decide)] at hh
      have hst : stateAt s.env s = s := rfl
      simpa only [hst, e0] using hh
    have hmem0 : e0.mem = mem := by
      simp only [e0, stateAt]; exact hmem
    have hS2 : gapS2 bytes ip ee = ee := by
      unfold gapS2
      rw [show ip - ee = 0 from by omega]
      simp [gapWsRun]
    have hexit : gapWsScanExit bytes ip ee c mem e0 := by
      refine ⟨rfl, hmem0, ?_, ?_⟩
      · simp only [e0, stateAt]; block_lk
      · refine ⟨"if.end67", "%ee.0.lcssa", rfl, by decide, ?_⟩
        rw [hS2]
        simp only [e0, stateAt]; block_lk
    obtain ⟨jc, hjc, hrunCont⟩ :=
      gapWs_whileEnd78_continue heele hiplt hexit he he64
    refine ⟨1 + jc, by omega, ?_, rfl, ?_, ?_⟩
    · rw [runFuel_jump_prefix hstep1 jc]
      exact hrunCont
    · exact stage2ErrSetMsg_off_read mem e (gapS2 bytes ip ee) 4
    · exact stage2ErrSetMsg_msg_read mem e (gapS2 bytes ip ee) 4

/-! ### Axiom footprints -/

#print axioms gap_se1112
#print axioms gapWsRun_add
#print axioms gapWsRun_succ
#print axioms gapWsS2_of_prefix_nonWs
#print axioms gapWsS2_of_prefix_all
#print axioms gapWs_step_ifEnd67
#print axioms gapWs_step_landRhs71_fromIfEnd67
#print axioms gapWs_step_whileEnd78
#print axioms gapWsSecondScan_pins
#print axioms gapWs_scan_exit_nonWs
#print axioms gapWs_scan_toWhileBody
#print axioms gapWs_scan_exit_ip
#print axioms gapWs_scan_step_loop
#print axioms gapWsScanLoop
#print axioms gapWsScanLoop_run
#print axioms gapWs_whileEnd78_continue
#print axioms gapWs_secondScan_run

end LeanLLVM.Refinement
