import LeanLLVM.Refinement.JsonStage2StringBodyMemory

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)

/-! ### The blocks as control steps

`step` reads a block at `s.pc`, denotes its instruction list, and executes its
terminator; the runs above are the same `denoteCode` at the same block.  The two
are one step (`step_at_block`), and what each step still needs is its terminator's
branch value — the bit the block's own test wrote, which the run's conclusion
names as the environment's cell.  Stating the bit as a hypothesis (rather than
case-splitting inside each step) is what keeps the step at the shape `runFuel`'s
recursion consumes: `runFuel_jump_prefix` turns a `.jump` into one control step,
and `BoundLoop`'s arms are two of these composed.

**The nineteen pins are the block labels the `_at` shapes resolve to.**  Each is
`decide`, so a block whose instruction list moved fails here rather than inside a
step's proof. -/

/-- One control step from a block's run: `step` at a state whose program counter
finds `b`, whose instruction list denotes to `s'`, and whose terminator is `c`. -/
theorem step_at_block {calls : Calls} {f : Function} {s s' : State} {b : Block}
    {c : Ctrl} (hfind : f.findBlock s.pc = some b)
    (hcode : denoteCode calls b.instrs s = some s')
    (hterm : execTerm s' b.term = c) :
    step calls f s = c := by
  simp only [step, hfind, hcode, hterm]

theorem s2StringBody_findBlock_entry_at :
    s2StringBodyBody.findBlock "entry" =
      some ⟨"entry", s2StringBodyEntryInstrs,
        Term.condbr (.reg "%tobool.not") "if.end16" "while.cond.preheader"⟩ := by decide

theorem s2StringBody_findBlock_while_cond_at :
    s2StringBodyBody.findBlock "while.cond.preheader" =
      some ⟨"while.cond.preheader", s2StringBodyWhileCondInstrs,
        Term.condbr (.reg "%cmp3") "land.rhs" "if.then9"⟩ := by decide

theorem s2StringBody_findBlock_land_rhs_at :
    s2StringBodyBody.findBlock "land.rhs" =
      some ⟨"land.rhs", s2StringBodyLandRhsInstrs,
        Term.condbr (.reg "%cmp1") "while.body" "land.lhs.true"⟩ := by decide

theorem s2StringBody_findBlock_while_body_at :
    s2StringBodyBody.findBlock "while.body" =
      some ⟨"while.body", s2StringBodyWhileBodyInstrs,
        Term.condbr (.reg "%exitcond.not") "if.then9" "land.rhs"⟩ := by decide

theorem s2StringBody_findBlock_land_lhs_true_at :
    s2StringBodyBody.findBlock "land.lhs.true" =
      some ⟨"land.lhs.true", s2StringBodyLandLhsTrueInstrs,
        Term.condbr (.reg "%cmp7") "if.end" "if.then9"⟩ := by decide

theorem s2StringBody_findBlock_if_then9_at :
    s2StringBodyBody.findBlock "if.then9" =
      some ⟨"if.then9", s2StringBodyIfThen9Instrs, Term.br "cleanup47"⟩ := by decide

theorem s2StringBody_findBlock_if_end_at :
    s2StringBodyBody.findBlock "if.end" =
      some ⟨"if.end", s2StringBodyIfEndInstrs,
        Term.condbr (.reg "%cmp10") "if.then12" "if.end15"⟩ := by decide

theorem s2StringBody_findBlock_if_then12_at :
    s2StringBodyBody.findBlock "if.then12" =
      some ⟨"if.then12", s2StringBodyIfThen12Instrs, Term.br "cleanup47"⟩ := by decide

theorem s2StringBody_findBlock_if_end15_at :
    s2StringBodyBody.findBlock "if.end15" =
      some ⟨"if.end15", s2StringBodyIfEnd15Instrs, Term.br "cleanup47"⟩ := by decide

theorem s2StringBody_findBlock_if_end16_at :
    s2StringBodyBody.findBlock "if.end16" =
      some ⟨"if.end16", s2StringBodyIfEnd16Instrs,
        Term.condbr (.reg "%cmp18") "if.then20" "if.end21"⟩ := by decide

theorem s2StringBody_findBlock_if_then20_at :
    s2StringBodyBody.findBlock "if.then20" =
      some ⟨"if.then20", s2StringBodyIfThen20Instrs, Term.br "cleanup47"⟩ := by decide

theorem s2StringBody_findBlock_if_end21_at :
    s2StringBodyBody.findBlock "if.end21" =
      some ⟨"if.end21", s2StringBodyIfEnd21Instrs,
        Term.condbr (.reg "%cmp24.not") "if.end29" "if.then26"⟩ := by decide

theorem s2StringBody_findBlock_if_then26_at :
    s2StringBodyBody.findBlock "if.then26" =
      some ⟨"if.then26", s2StringBodyIfThen26Instrs, Term.br "cleanup47"⟩ := by decide

theorem s2StringBody_findBlock_if_end29_at :
    s2StringBodyBody.findBlock "if.end29" =
      some ⟨"if.end29", s2StringBodyIfEnd29Instrs,
        Term.condbr (.reg "%cmp33") "if.then35" "if.end39"⟩ := by decide

theorem s2StringBody_findBlock_if_then35_at :
    s2StringBodyBody.findBlock "if.then35" =
      some ⟨"if.then35", s2StringBodyIfThen35Instrs, Term.br "cleanup47"⟩ := by decide

theorem s2StringBody_findBlock_if_end39_at :
    s2StringBodyBody.findBlock "if.end39" =
      some ⟨"if.end39", s2StringBodyIfEnd39Instrs,
        Term.condbr (.reg "%tobool40.not") "if.end43" "if.then41"⟩ := by decide

theorem s2StringBody_findBlock_if_then41_at :
    s2StringBodyBody.findBlock "if.then41" =
      some ⟨"if.then41", s2StringBodyIfThen41Instrs, Term.br "if.end43"⟩ := by decide

theorem s2StringBody_findBlock_if_end43_at :
    s2StringBodyBody.findBlock "if.end43" =
      some ⟨"if.end43", s2StringBodyIfEnd43Instrs, Term.br "cleanup47"⟩ := by decide

theorem s2StringBody_findBlock_cleanup47_at :
    s2StringBodyBody.findBlock "cleanup47" =
      some ⟨"cleanup47", s2StringBodyCleanup47Instrs,
        Term.ret (Ty.int 32) (some (Operand.reg "%retval.3"))⟩ := by decide

/-! ### The entry and the two arm tests -/

/-- The entry block's environment after its six result-bearing instructions: the
allocator's first cell and the five the block builds over it. -/
def s2StringBodyEntryOut (env : Env) (next : Nat) (base p : Nat)
    (nxp : BitVec 64) : Env :=
  s2StringBodyEnv6 (s2StringBodyEnv5 (s2StringBodyEnv4
    (s2StringBodyEnv3 (s2StringBodyEnv2 (s2StringBodyEnv1 env next) base) p) base)
    p base) nxp

/-- The entry block's step, to the list-free arm: `nxp = 0`. -/
theorem step_entry_ifEnd16 {env : Env} {s : State} {c p base : Nat}
    {nxp : BitVec 64}
    (hpc : s.pc = "entry")
    (hc : lookupName env "%c" = some (.ptr c))
    (hp : lookupName env "%p" = some (.ptr p))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hbase : readBytes s.mem c 8 = some (wordBytes 8 base)) (hb64 : base < 2 ^ 64)
    (hp64 : p < 2 ^ 64)
    (hbit : evalICmp .eq nxp (BitVec.ofNat 64 0) = 1#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (s2StringBodyEntryOut env s.next base p nxp)
        { s with next := s.next + (Ty.int 64).sizeBytes, pc := "if.end16", pre := some s.pc }) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyEntryOut env s.next base p nxp)
      { s with next := s.next + (Ty.int 64).sizeBytes })
    (b := ⟨"entry", s2StringBodyEntryInstrs,
      Term.condbr (.reg "%tobool.not") "if.end16" "while.cond.preheader"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_entry_at
  · simpa only [denoteCode_nil, s2StringBodyEntryOut] using
      s2StringBody_entry_denote hc hp hnxp hbase hb64 hp64
  · exact execTerm_condbr_one _ _ _ _ _ (by s2_lk) hbit

/-- The entry block's step, to the scan arm: `nxp ≠ 0`. -/
theorem step_entry_whileCond {env : Env} {s : State} {c p base : Nat}
    {nxp : BitVec 64}
    (hpc : s.pc = "entry")
    (hc : lookupName env "%c" = some (.ptr c))
    (hp : lookupName env "%p" = some (.ptr p))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hbase : readBytes s.mem c 8 = some (wordBytes 8 base)) (hb64 : base < 2 ^ 64)
    (hp64 : p < 2 ^ 64)
    (hbit : evalICmp .eq nxp (BitVec.ofNat 64 0) = 0#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (s2StringBodyEntryOut env s.next base p nxp)
        { s with next := s.next + (Ty.int 64).sizeBytes, pc := "while.cond.preheader", pre := some s.pc }) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyEntryOut env s.next base p nxp)
      { s with next := s.next + (Ty.int 64).sizeBytes })
    (b := ⟨"entry", s2StringBodyEntryInstrs,
      Term.condbr (.reg "%tobool.not") "if.end16" "while.cond.preheader"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_entry_at
  · simpa only [denoteCode_nil, s2StringBodyEntryOut] using
      s2StringBody_entry_denote hc hp hnxp hbase hb64 hp64
  · exact execTerm_condbr_zero _ _ _ _ _ (by s2_lk) hbit

/-- The scan-head test's step, the cursor word read: one control step to the scan's
head. -/
theorem step_whileCond_landRhs {env : Env} {s : State} {xj : Nat}
    {j0 nxp : BitVec 64}
    (hpc : s.pc = "while.cond.preheader")
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hj0 : readBytes s.mem xj 8 = some (wordBytes 8 j0.toNat))
    (hj64 : j0.toNat < 2 ^ 64)
    (hbit : evalICmp .ult j0 nxp = 1#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (s2StringBodyWhileCondEnv env j0 nxp)
        { s with pc := "land.rhs", pre := some s.pc }) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyWhileCondEnv env j0 nxp) s)
    (b := ⟨"while.cond.preheader", s2StringBodyWhileCondInstrs,
      Term.condbr (.reg "%cmp3") "land.rhs" "if.then9"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_while_cond_at
  · simpa only [denoteCode_nil] using
      s2StringBody_whileCond_denote hxj hnxp hj0 hj64
  · exact execTerm_condbr_one _ _ _ _ _ (by s2_lk) hbit

/-- The scan-head test's step, the body-itself arm: one control step to `if.then9`. -/
theorem step_whileCond_ifThen9 {env : Env} {s : State} {xj : Nat}
    {j0 nxp : BitVec 64}
    (hpc : s.pc = "while.cond.preheader")
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hj0 : readBytes s.mem xj 8 = some (wordBytes 8 j0.toNat))
    (hj64 : j0.toNat < 2 ^ 64)
    (hbit : evalICmp .ult j0 nxp = 0#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (s2StringBodyWhileCondEnv env j0 nxp)
        { s with pc := "if.then9", pre := some s.pc }) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyWhileCondEnv env j0 nxp) s)
    (b := ⟨"while.cond.preheader", s2StringBodyWhileCondInstrs,
      Term.condbr (.reg "%cmp3") "land.rhs" "if.then9"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_while_cond_at
  · simpa only [denoteCode_nil] using
      s2StringBody_whileCond_denote hxj hnxp hj0 hj64
  · exact execTerm_condbr_zero _ _ _ _ _ (by s2_lk) hbit

/-! ### The scan's steps -/

/-- The scan's head, while the lane is still below the body: one control step to
`while.body`. -/
theorem step_landRhs_while {env : Env} {s : State} {p : String} {op : Operand}
    {inc24 : BitVec 64} {xp : Nat} {bs : List UInt8} {sub : BitVec 64}
    (hpc : s.pc = "land.rhs") (hpre : s.pre = some p)
    (hinc : phiIncoming p [("while.body", Operand.reg "%inc"),
      ("while.cond.preheader", Operand.reg "%xj.promoted")] = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 inc24))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hpos : (inc24.signExtend 64).toNat < 2 ^ 63)
    (hlane : readBytes s.mem (xp + (inc24.signExtend 64).toNat * 4) 4 = some bs)
    (hbit : evalICmpNat .ugt 64 sub.toNat
      (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat).toNat = 1#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (s2StringBodyLandRhsEnv env inc24 xp bs sub)
        { s with pc := "while.body", pre := some s.pc }) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyLandRhsEnv env inc24 xp bs sub) s)
    (b := ⟨"land.rhs", s2StringBodyLandRhsInstrs,
      Term.condbr (.reg "%cmp1") "while.body" "land.lhs.true"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_land_rhs_at
  · simpa only [denoteCode_nil] using
      s2StringBody_landRhs_denote hpre hinc hop hxp hsub hpos hlane
  · exact execTerm_condbr_one _ _ _ _ _ (by s2_lk) hbit

/-- The scan's head, the lane inside the body: one control step to
`land.lhs.true`, the loop's first exit. -/
theorem step_landRhs_exit {env : Env} {s : State} {p : String} {op : Operand}
    {inc24 : BitVec 64} {xp : Nat} {bs : List UInt8} {sub : BitVec 64}
    (hpc : s.pc = "land.rhs") (hpre : s.pre = some p)
    (hinc : phiIncoming p [("while.body", Operand.reg "%inc"),
      ("while.cond.preheader", Operand.reg "%xj.promoted")] = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 inc24))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hpos : (inc24.signExtend 64).toNat < 2 ^ 63)
    (hlane : readBytes s.mem (xp + (inc24.signExtend 64).toNat * 4) 4 = some bs)
    (hbit : evalICmpNat .ugt 64 sub.toNat
      (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat).toNat = 0#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (s2StringBodyLandRhsEnv env inc24 xp bs sub)
        { s with pc := "land.lhs.true", pre := some s.pc }) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyLandRhsEnv env inc24 xp bs sub) s)
    (b := ⟨"land.rhs", s2StringBodyLandRhsInstrs,
      Term.condbr (.reg "%cmp1") "while.body" "land.lhs.true"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_land_rhs_at
  · simpa only [denoteCode_nil] using
      s2StringBody_landRhs_denote hpre hinc hop hxp hsub hpos hlane
  · exact execTerm_condbr_zero _ _ _ _ _ (by s2_lk) hbit

/-- The scan's body: the counter's advance written back, one control step to the
scan's head (`cost`'s second step). -/
theorem step_whileBody_back {env : Env} {s : State} {inc24 nxp : BitVec 64}
    {xj : Nat}
    (hpc : s.pc = "while.body")
    (hinc24 : lookupName env "%inc24" = some (.int 64 inc24))
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hbit : evalICmp .eq (inc24 + 1#64) nxp = 0#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt
        (("%exitcond.not", .int 1 (evalICmp .eq (inc24 + 1#64) nxp)) ::
          ("%inc", .int 64 (inc24 + 1#64)) :: env)
        ({ s with mem := writeBytes s.mem xj (natToBytes (inc24 + 1#64).toNat 8), pc := "land.rhs", pre := some s.pc })) := by
  refine step_at_block
    (s' := stateAt
      (("%exitcond.not", .int 1 (evalICmp .eq (inc24 + 1#64) nxp)) ::
        ("%inc", .int 64 (inc24 + 1#64)) :: env)
      { s with mem := writeBytes s.mem xj (natToBytes (inc24 + 1#64).toNat 8) })
    (b := ⟨"while.body", s2StringBodyWhileBodyInstrs,
      Term.condbr (.reg "%exitcond.not") "if.then9" "land.rhs"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_while_body_at
  · simpa only [denoteCode_nil] using s2StringBody_whileBody_denote hinc24 hxj hnxp
  · exact execTerm_condbr_zero _ _ _ _ _ (by s2_lk) hbit

/-- The scan's body, the counter at the count: one control step to `if.then9`, the
loop's second exit. -/
theorem step_whileBody_exit {env : Env} {s : State} {inc24 nxp : BitVec 64}
    {xj : Nat}
    (hpc : s.pc = "while.body")
    (hinc24 : lookupName env "%inc24" = some (.int 64 inc24))
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hbit : evalICmp .eq (inc24 + 1#64) nxp = 1#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt
        (("%exitcond.not", .int 1 (evalICmp .eq (inc24 + 1#64) nxp)) ::
          ("%inc", .int 64 (inc24 + 1#64)) :: env)
        ({ s with mem := writeBytes s.mem xj (natToBytes (inc24 + 1#64).toNat 8), pc := "if.then9", pre := some s.pc })) := by
  refine step_at_block
    (s' := stateAt
      (("%exitcond.not", .int 1 (evalICmp .eq (inc24 + 1#64) nxp)) ::
        ("%inc", .int 64 (inc24 + 1#64)) :: env)
      { s with mem := writeBytes s.mem xj (natToBytes (inc24 + 1#64).toNat 8) })
    (b := ⟨"while.body", s2StringBodyWhileBodyInstrs,
      Term.condbr (.reg "%exitcond.not") "if.then9" "land.rhs"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_while_body_at
  · simpa only [denoteCode_nil] using s2StringBody_whileBody_denote hinc24 hxj hnxp
  · exact execTerm_condbr_one _ _ _ _ _ (by s2_lk) hbit

/-- The inside test, the lane past the body's end: one control step to `if.end`. -/
theorem step_landLhsTrue_ifEnd {env : Env} {s : State} {sub len conv : BitVec 64}
    (hpc : s.pc = "land.lhs.true")
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hlen : lookupName env "%len" = some (.int 64 len))
    (hconv : lookupName env "%conv" = some (.int 64 conv))
    (hbit : evalICmpNat .ugt 64 (sub + len).toNat conv.toNat = 1#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt
        (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
          ("%add", .int 64 (sub + len)) :: env)
        { s with pc := "if.end", pre := some s.pc }) := by
  refine step_at_block
    (s' := stateAt
      (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
        ("%add", .int 64 (sub + len)) :: env) s)
    (b := ⟨"land.lhs.true", s2StringBodyLandLhsTrueInstrs,
      Term.condbr (.reg "%cmp7") "if.end" "if.then9"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_land_lhs_true_at
  · simpa only [denoteCode_nil] using s2StringBody_landLhsTrue_denote hsub hlen hconv
  · exact execTerm_condbr_one _ _ _ _ _ (by s2_lk) hbit

/-- The inside test, the lane inside the body: one control step to `if.then9`. -/
theorem step_landLhsTrue_ifThen9 {env : Env} {s : State} {sub len conv : BitVec 64}
    (hpc : s.pc = "land.lhs.true")
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hlen : lookupName env "%len" = some (.int 64 len))
    (hconv : lookupName env "%conv" = some (.int 64 conv))
    (hbit : evalICmpNat .ugt 64 (sub + len).toNat conv.toNat = 0#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt
        (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
          ("%add", .int 64 (sub + len)) :: env)
        { s with pc := "if.then9", pre := some s.pc }) := by
  refine step_at_block
    (s' := stateAt
      (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
        ("%add", .int 64 (sub + len)) :: env) s)
    (b := ⟨"land.lhs.true", s2StringBodyLandLhsTrueInstrs,
      Term.condbr (.reg "%cmp7") "if.end" "if.then9"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_land_lhs_true_at
  · simpa only [denoteCode_nil] using s2StringBody_landLhsTrue_denote hsub hlen hconv
  · exact execTerm_condbr_zero _ _ _ _ _ (by s2_lk) hbit

/-! ### The list arm's exits -/

/-- The body-itself arm's step: the extent's word at `outn`, then `cleanup47`. -/
theorem step_ifThen9_cleanup47 {env : Env} {s : State} {len : BitVec 64} {outn : Nat}
    (hpc : s.pc = "if.then9")
    (hlen : lookupName env "%len" = some (.int 64 len))
    (houtn : lookupName env "%outn" = some (.ptr outn)) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt env
        ({ s with mem := writeBytes s.mem outn (natToBytes len.toNat 8), pc := "cleanup47", pre := some s.pc })) := by
  refine step_at_block
    (s' := stateAt env { s with mem := writeBytes s.mem outn (natToBytes len.toNat 8) })
    (b := ⟨"if.then9", s2StringBodyIfThen9Instrs, Term.br "cleanup47"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_if_then9_at
  · simpa only [denoteCode_nil] using s2StringBody_ifThen9_denote hlen houtn
  · rfl

/-- The expander's step, its answer all-ones: one control step to the refusal
record. -/
theorem step_ifEnd_ifThen12 {env : Env} {s : State}
    {p dst ei xp xj : Nat} {len nxp sub call : BitVec 64} {m : Mem} {nx : Nat}
    (hpc : s.pc = "if.end")
    (hp : lookupName env "%p" = some (.ptr p))
    (hlen : lookupName env "%len" = some (.int 64 len))
    (hdst : lookupName env "%dst" = some (.ptr dst))
    (hei : lookupName env "%ei" = some (.ptr ei))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hc : s2StringBodyCalls "leanllvm_json_escape_expand"
      [.ptr p, .int 64 len, .ptr dst, .ptr ei, .ptr xp, .ptr xj, .int 64 nxp,
       .int 64 sub] (writeBytes s.mem ei (natToBytes (0#64).toNat 8)) s.next =
      some { ret := .int 64 call, mem := m, next := nx })
    (hbit : evalICmp .eq call 0xffffffffffffffff#64 = 1#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (s2StringBodyIfEndEnv env call)
        ({ s with mem := m, next := nx, pc := "if.then12", pre := some s.pc })) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyIfEndEnv env call) { s with mem := m, next := nx })
    (b := ⟨"if.end", s2StringBodyIfEndInstrs,
      Term.condbr (.reg "%cmp10") "if.then12" "if.end15"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_if_end_at
  · simpa only [denoteCode_nil] using
      s2StringBody_ifEnd_denote hp hlen hdst hei hxp hxj hnxp hsub hc
  · exact execTerm_condbr_one _ _ _ _ _ (by s2_lk) hbit

/-- The expander's step, an answer that is not all-ones: one control step to the
decoded length's write. -/
theorem step_ifEnd_ifEnd15 {env : Env} {s : State}
    {p dst ei xp xj : Nat} {len nxp sub call : BitVec 64} {m : Mem} {nx : Nat}
    (hpc : s.pc = "if.end")
    (hp : lookupName env "%p" = some (.ptr p))
    (hlen : lookupName env "%len" = some (.int 64 len))
    (hdst : lookupName env "%dst" = some (.ptr dst))
    (hei : lookupName env "%ei" = some (.ptr ei))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hc : s2StringBodyCalls "leanllvm_json_escape_expand"
      [.ptr p, .int 64 len, .ptr dst, .ptr ei, .ptr xp, .ptr xj, .int 64 nxp,
       .int 64 sub] (writeBytes s.mem ei (natToBytes (0#64).toNat 8)) s.next =
      some { ret := .int 64 call, mem := m, next := nx })
    (hbit : evalICmp .eq call 0xffffffffffffffff#64 = 0#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (s2StringBodyIfEndEnv env call)
        ({ s with mem := m, next := nx, pc := "if.end15", pre := some s.pc })) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyIfEndEnv env call) { s with mem := m, next := nx })
    (b := ⟨"if.end", s2StringBodyIfEndInstrs,
      Term.condbr (.reg "%cmp10") "if.then12" "if.end15"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_if_end_at
  · simpa only [denoteCode_nil] using
      s2StringBody_ifEnd_denote hp hlen hdst hei hxp hxj hnxp hsub hc
  · exact execTerm_condbr_zero _ _ _ _ _ (by s2_lk) hbit

set_option maxHeartbeats 1000000 in
/-- The refusal record's step: the three fields written, then `cleanup47`. -/
theorem step_ifThen12_cleanup47 {env : Env} {s : State} {c ei e : Nat} {off sub : BitVec 64}
    (hpc : s.pc = "if.then12")
    (hc : lookupName env "%c" = some (.ptr c))
    (hei : lookupName env "%ei" = some (.ptr ei))
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hoff : readBytes s.mem ei 8 = some (natToBytes off.toNat 8))
    (hcval : readBytes s.mem (c + (1112#64).toNat) 8 = some (wordBytes 8 e))
    (he64 : e < 2 ^ 64) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (s2StringBodyIfThen12Env env off sub c e)
        ({ s with mem := s2StringBodyIfThen12Mem s.mem e off sub, pc := "cleanup47", pre := some s.pc })) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyIfThen12Env env off sub c e)
      { s with mem := s2StringBodyIfThen12Mem s.mem e off sub })
    (b := ⟨"if.then12", s2StringBodyIfThen12Instrs, Term.br "cleanup47"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_if_then12_at
  · simpa only [denoteCode_nil] using
      s2StringBody_ifThen12_denote hc hei hsub hoff hcval he64
  · rfl

/-- The decoded length's step at `outn`, then `cleanup47`. -/
theorem step_ifEnd15_cleanup47 {env : Env} {s : State} {call : BitVec 64} {outn : Nat}
    (hpc : s.pc = "if.end15")
    (hcall : lookupName env "%call" = some (.int 64 call))
    (houtn : lookupName env "%outn" = some (.ptr outn)) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt env
        ({ s with mem := writeBytes s.mem outn (natToBytes call.toNat 8), pc := "cleanup47", pre := some s.pc })) := by
  refine step_at_block
    (s' := stateAt env { s with mem := writeBytes s.mem outn (natToBytes call.toNat 8) })
    (b := ⟨"if.end15", s2StringBodyIfEnd15Instrs, Term.br "cleanup47"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_if_end15_at
  · simpa only [denoteCode_nil] using s2StringBody_ifEnd15_denote hcall houtn
  · rfl

/-! ### The list-free arm's exits -/

/-- The scan's answer all-ones: the plain span's word at `outn`. -/
theorem step_ifEnd16_ifThen20 {env : Env} {s : State} {p len : Nat} {call17 : BitVec 64}
    {m : Mem} {nx : Nat}
    (hpc : s.pc = "if.end16")
    (hp : lookupName env "%p" = some (.ptr p))
    (hlen : lookupName env "%len" = some (.int 64 len))
    (hc : s2StringBodyCalls "z_scan" [.ptr p, .int 64 len] s.mem s.next =
      some { ret := .int 64 call17, mem := m, next := nx })
    (hbit : evalICmp .eq call17 0xffffffffffffffff#64 = 1#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (s2StringBodyIfEnd16Env env call17)
        ({ s with mem := m, next := nx, pc := "if.then20", pre := some s.pc })) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyIfEnd16Env env call17) { s with mem := m, next := nx })
    (b := ⟨"if.end16", s2StringBodyIfEnd16Instrs,
      Term.condbr (.reg "%cmp18") "if.then20" "if.end21"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_if_end16_at
  · simpa only [denoteCode_nil] using s2StringBody_ifEnd16_denote hp hlen hc
  · exact execTerm_condbr_one _ _ _ _ _ (by s2_lk) hbit

/-- The scan's answer is a special byte: the byte's test. -/
theorem step_ifEnd16_ifEnd21 {env : Env} {s : State} {p len : Nat} {call17 : BitVec 64}
    {m : Mem} {nx : Nat}
    (hpc : s.pc = "if.end16")
    (hp : lookupName env "%p" = some (.ptr p))
    (hlen : lookupName env "%len" = some (.int 64 len))
    (hc : s2StringBodyCalls "z_scan" [.ptr p, .int 64 len] s.mem s.next =
      some { ret := .int 64 call17, mem := m, next := nx })
    (hbit : evalICmp .eq call17 0xffffffffffffffff#64 = 0#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (s2StringBodyIfEnd16Env env call17)
        ({ s with mem := m, next := nx, pc := "if.end21", pre := some s.pc })) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyIfEnd16Env env call17) { s with mem := m, next := nx })
    (b := ⟨"if.end16", s2StringBodyIfEnd16Instrs,
      Term.condbr (.reg "%cmp18") "if.then20" "if.end21"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_if_end16_at
  · simpa only [denoteCode_nil] using s2StringBody_ifEnd16_denote hp hlen hc
  · exact execTerm_condbr_zero _ _ _ _ _ (by s2_lk) hbit

/-- The plain span's word at `outn`. -/
theorem step_ifThen20_cleanup47 {env : Env} {s : State} {len : BitVec 64} {outn : Nat}
    (hpc : s.pc = "if.then20")
    (hlen : lookupName env "%len" = some (.int 64 len))
    (houtn : lookupName env "%outn" = some (.ptr outn)) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt env
        ({ s with mem := writeBytes s.mem outn (natToBytes len.toNat 8), pc := "cleanup47", pre := some s.pc })) := by
  refine step_at_block
    (s' := stateAt env { s with mem := writeBytes s.mem outn (natToBytes len.toNat 8) })
    (b := ⟨"if.then20", s2StringBodyIfThen20Instrs, Term.br "cleanup47"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_if_then20_at
  · simpa only [denoteCode_nil] using s2StringBody_ifThen20_denote hlen houtn
  · rfl

/-- The byte's test, a backslash: one control step to the suffix's decoding. -/
theorem step_ifEnd21_ifEnd29 {env : Env} {s : State} {p : Nat} {call17 : BitVec 64}
    {bs : List UInt8}
    (hpc : s.pc = "if.end21")
    (hp : lookupName env "%p" = some (.ptr p))
    (hcall17 : lookupName env "%call17" = some (.int 64 call17))
    (hpos : (call17.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (call17.signExtend 64).toNat) 1 = some bs)
    (hbit : evalICmpNat .eq 8 (BitVec.ofNat 8 (bytesToNat bs)).toNat (0x5c#8).toNat = 1#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (s2StringBodyIfEnd21Env env p call17 bs)
        { s with pc := "if.end29", pre := some s.pc }) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyIfEnd21Env env p call17 bs) s)
    (b := ⟨"if.end21", s2StringBodyIfEnd21Instrs,
      Term.condbr (.reg "%cmp24.not") "if.end29" "if.then26"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_if_end21_at
  · simpa only [denoteCode_nil] using s2StringBody_ifEnd21_denote hp hcall17 hpos hb
  · exact execTerm_condbr_one _ _ _ _ _ (by s2_lk) hbit

/-- The byte's test, a control byte: one control step to the refusal record. -/
theorem step_ifEnd21_ifThen26 {env : Env} {s : State} {p : Nat} {call17 : BitVec 64}
    {bs : List UInt8}
    (hpc : s.pc = "if.end21")
    (hp : lookupName env "%p" = some (.ptr p))
    (hcall17 : lookupName env "%call17" = some (.int 64 call17))
    (hpos : (call17.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (call17.signExtend 64).toNat) 1 = some bs)
    (hbit : evalICmpNat .eq 8 (BitVec.ofNat 8 (bytesToNat bs)).toNat (0x5c#8).toNat = 0#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (s2StringBodyIfEnd21Env env p call17 bs)
        { s with pc := "if.then26", pre := some s.pc }) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyIfEnd21Env env p call17 bs) s)
    (b := ⟨"if.end21", s2StringBodyIfEnd21Instrs,
      Term.condbr (.reg "%cmp24.not") "if.end29" "if.then26"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_if_end21_at
  · simpa only [denoteCode_nil] using s2StringBody_ifEnd21_denote hp hcall17 hpos hb
  · exact execTerm_condbr_zero _ _ _ _ _ (by s2_lk) hbit

set_option maxHeartbeats 1000000 in
/-- The control record's step: the three fields written, then `cleanup47`. -/
theorem step_ifThen26_cleanup47 {env : Env} {s : State} {c e : Nat} {off sub : BitVec 64}
    (hpc : s.pc = "if.then26")
    (hc : lookupName env "%c" = some (.ptr c))
    (hcall17 : lookupName env "%call17" = some (.int 64 off))
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hcval : readBytes s.mem (c + (1112#64).toNat) 8 = some (wordBytes 8 e))
    (he64 : e < 2 ^ 64) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (s2StringBodyIfThen26Env env off sub c e)
        ({ s with mem := s2StringBodyIfThen26Mem s.mem e off sub, pc := "cleanup47", pre := some s.pc })) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyIfThen26Env env off sub c e)
      { s with mem := s2StringBodyIfThen26Mem s.mem e off sub })
    (b := ⟨"if.then26", s2StringBodyIfThen26Instrs, Term.br "cleanup47"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_if_then26_at
  · simpa only [denoteCode_nil] using
      s2StringBody_ifThen26_denote hc hcall17 hsub hcval he64
  · rfl

/-- The decoder's step, its answer all-ones: the refusal record. -/
theorem step_ifEnd29_ifThen35 {env : Env} {s : State}
    {dst p ei : Nat} {call17 len call32 : BitVec 64} {m : Mem} {nx : Nat}
    (hpc : s.pc = "if.end29")
    (hlen : lookupName env "%len" = some (.int 64 len))
    (hdst : lookupName env "%dst" = some (.ptr dst))
    (hei : lookupName env "%ei" = some (.ptr ei))
    (hcall17 : lookupName env "%call17" = some (.int 64 call17))
    (harr : lookupName env "%arrayidx22" = some (.ptr (p + (call17.signExtend 64).toNat)))
    (hpos : (call17.signExtend 64).toNat < 2 ^ 63)
    (hc : s2StringBodyCalls "leanllvm_json_escape_decode"
      [.ptr (p + (call17.signExtend 64).toNat), .int 64 (len - call17),
       .ptr (dst + (call17.signExtend 64).toNat), .ptr ei]
      (writeBytes s.mem ei (natToBytes (0#64).toNat 8)) s.next =
      some { ret := .int 64 call32, mem := m, next := nx })
    (hbit : evalICmp .eq call32 0xffffffffffffffff#64 = 1#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (s2StringBodyIfEnd29Env env dst p call17 len call32)
        ({ s with mem := m, next := nx, pc := "if.then35", pre := some s.pc })) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyIfEnd29Env env dst p call17 len call32)
      { s with mem := m, next := nx })
    (b := ⟨"if.end29", s2StringBodyIfEnd29Instrs,
      Term.condbr (.reg "%cmp33") "if.then35" "if.end39"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_if_end29_at
  · simpa only [denoteCode_nil] using
      s2StringBody_ifEnd29_denote hlen hdst hei hcall17 harr hpos hc
  · exact execTerm_condbr_one _ _ _ _ _ (by s2_lk) hbit

/-- The decoder's step, an accepting answer: the zero-prefix test. -/
theorem step_ifEnd29_ifEnd39 {env : Env} {s : State}
    {dst p ei : Nat} {call17 len call32 : BitVec 64} {m : Mem} {nx : Nat}
    (hpc : s.pc = "if.end29")
    (hlen : lookupName env "%len" = some (.int 64 len))
    (hdst : lookupName env "%dst" = some (.ptr dst))
    (hei : lookupName env "%ei" = some (.ptr ei))
    (hcall17 : lookupName env "%call17" = some (.int 64 call17))
    (harr : lookupName env "%arrayidx22" = some (.ptr (p + (call17.signExtend 64).toNat)))
    (hpos : (call17.signExtend 64).toNat < 2 ^ 63)
    (hc : s2StringBodyCalls "leanllvm_json_escape_decode"
      [.ptr (p + (call17.signExtend 64).toNat), .int 64 (len - call17),
       .ptr (dst + (call17.signExtend 64).toNat), .ptr ei]
      (writeBytes s.mem ei (natToBytes (0#64).toNat 8)) s.next =
      some { ret := .int 64 call32, mem := m, next := nx })
    (hbit : evalICmp .eq call32 0xffffffffffffffff#64 = 0#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (s2StringBodyIfEnd29Env env dst p call17 len call32)
        ({ s with mem := m, next := nx, pc := "if.end39", pre := some s.pc })) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyIfEnd29Env env dst p call17 len call32)
      { s with mem := m, next := nx })
    (b := ⟨"if.end29", s2StringBodyIfEnd29Instrs,
      Term.condbr (.reg "%cmp33") "if.then35" "if.end39"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_if_end29_at
  · simpa only [denoteCode_nil] using
      s2StringBody_ifEnd29_denote hlen hdst hei hcall17 harr hpos hc
  · exact execTerm_condbr_zero _ _ _ _ _ (by s2_lk) hbit

set_option maxHeartbeats 1000000 in
/-- The malformed record's step: the combined offset written, then `cleanup47`. -/
theorem step_ifThen35_cleanup47 {env : Env} {s : State} {c ei e : Nat}
    {off sub rel : BitVec 64}
    (hpc : s.pc = "if.then35")
    (hc : lookupName env "%c" = some (.ptr c))
    (hei : lookupName env "%ei" = some (.ptr ei))
    (hcall17 : lookupName env "%call17" = some (.int 64 off))
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hrel : readBytes s.mem ei 8 = some (natToBytes rel.toNat 8))
    (hcval : readBytes s.mem (c + (1112#64).toNat) 8 = some (wordBytes 8 e))
    (he64 : e < 2 ^ 64) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (s2StringBodyIfThen35Env env off sub rel c e)
        ({ s with mem := s2StringBodyIfThen35Mem s.mem e (off + sub + rel), pc := "cleanup47", pre := some s.pc })) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyIfThen35Env env off sub rel c e)
      { s with mem := s2StringBodyIfThen35Mem s.mem e (off + sub + rel) })
    (b := ⟨"if.then35", s2StringBodyIfThen35Instrs, Term.br "cleanup47"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_if_then35_at
  · simpa only [denoteCode_nil] using
      s2StringBody_ifThen35_denote hc hei hcall17 hsub hrel hcval he64
  · rfl

/-- The zero-prefix test, the prefix empty: one control step to `if.end43`. -/
theorem step_ifEnd39_ifEnd43 {env : Env} {s : State} {call17 : BitVec 64}
    (hpc : s.pc = "if.end39")
    (hcall17 : lookupName env "%call17" = some (.int 64 call17))
    (hbit : evalICmp .eq call17 (BitVec.ofNat 64 0) = 1#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (s2StringBodyIfEnd39Env env call17)
        { s with pc := "if.end43", pre := some s.pc }) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyIfEnd39Env env call17) s)
    (b := ⟨"if.end39", s2StringBodyIfEnd39Instrs,
      Term.condbr (.reg "%tobool40.not") "if.end43" "if.then41"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_if_end39_at
  · simpa only [denoteCode_nil] using s2StringBody_ifEnd39_denote hcall17
  · exact execTerm_condbr_one _ _ _ _ _ (by s2_lk) hbit

/-- The zero-prefix test, the prefix nonempty: one control step to the copy. -/
theorem step_ifEnd39_ifThen41 {env : Env} {s : State} {call17 : BitVec 64}
    (hpc : s.pc = "if.end39")
    (hcall17 : lookupName env "%call17" = some (.int 64 call17))
    (hbit : evalICmp .eq call17 (BitVec.ofNat 64 0) = 0#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (s2StringBodyIfEnd39Env env call17)
        { s with pc := "if.then41", pre := some s.pc }) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyIfEnd39Env env call17) s)
    (b := ⟨"if.end39", s2StringBodyIfEnd39Instrs,
      Term.condbr (.reg "%tobool40.not") "if.end43" "if.then41"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_if_end39_at
  · simpa only [denoteCode_nil] using s2StringBody_ifEnd39_denote hcall17
  · exact execTerm_condbr_zero _ _ _ _ _ (by s2_lk) hbit

/-- The exact prefix copy's step, then `if.end43`. -/
theorem step_ifThen41_ifEnd43 {env : Env} {s : State} {dst p : Nat}
    {call17 : BitVec 64} {m : Mem} {nx : Nat}
    (hpc : s.pc = "if.then41")
    (hdst : lookupName env "%dst" = some (.ptr dst))
    (hp : lookupName env "%p" = some (.ptr p))
    (hcall17 : lookupName env "%call17" = some (.int 64 call17))
    (hc : s2StringBodyCalls "llvm.memcpy.p0.p0.i64"
      [.ptr dst, .ptr p, .int 64 call17, .int 1 0] s.mem s.next =
      some { ret := .int 1 0, mem := m, next := nx }) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt env { s with mem := m, next := nx, pc := "if.end43", pre := some s.pc }) := by
  refine step_at_block
    (s' := stateAt env { s with mem := m, next := nx })
    (b := ⟨"if.then41", s2StringBodyIfThen41Instrs, Term.br "if.end43"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_if_then41_at
  · simpa only [denoteCode_nil] using s2StringBody_ifThen41_denote hdst hp hcall17 hc
  · rfl

/-- The decoded length's sum's step at `outn`, then `cleanup47`. -/
theorem step_ifEnd43_cleanup47 {env : Env} {s : State} {call17 call32 : BitVec 64}
    {outn : Nat}
    (hpc : s.pc = "if.end43")
    (hcall32 : lookupName env "%call32" = some (.int 64 call32))
    (hcall17 : lookupName env "%call17" = some (.int 64 call17))
    (houtn : lookupName env "%outn" = some (.ptr outn)) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (("%add44", .int 64 (call32 + call17)) :: env)
        ({ s with mem := writeBytes s.mem outn (natToBytes (call32 + call17).toNat 8), pc := "cleanup47", pre := some s.pc })) := by
  refine step_at_block
    (s' := stateAt (("%add44", .int 64 (call32 + call17)) :: env)
      { s with mem := writeBytes s.mem outn (natToBytes (call32 + call17).toNat 8) })
    (b := ⟨"if.end43", s2StringBodyIfEnd43Instrs, Term.br "cleanup47"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_if_end43_at
  · simpa only [denoteCode_nil] using s2StringBody_ifEnd43_denote hcall32 hcall17 houtn
  · rfl

/-- The merged cleanup's step: the seven-edge `phi` and the end marker, then the
function's answer. -/
theorem step_cleanup47_ret {env : Env} {s : State} {p : String} {op : Operand}
    {form : BitVec 32} {ei : Nat}
    (hpc : s.pc = "cleanup47") (hpre : s.pre = some p)
    (hinc : phiIncoming p
      [("if.then9", Operand.imm (Const.int 32 0x00000001#32)),
       ("if.then12", Operand.imm (Const.int 32 0x00000000#32)),
       ("if.end15", Operand.imm (Const.int 32 0x00000002#32)),
       ("if.then20", Operand.imm (Const.int 32 0x00000001#32)),
       ("if.then26", Operand.imm (Const.int 32 0x00000000#32)),
       ("if.then35", Operand.imm (Const.int 32 0x00000000#32)),
       ("if.end43", Operand.imm (Const.int 32 0x00000002#32))] = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 32 form))
    (hei : lookupName env "%ei" = some (.ptr ei)) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.ret (some (.int 32 form)) (stateAt (("%retval.3", .int 32 form) :: env) s) := by
  refine step_at_block
    (s' := stateAt (("%retval.3", .int 32 form) :: env) s)
    (b := ⟨"cleanup47", s2StringBodyCleanup47Instrs,
      Term.ret (Ty.int 32) (some (Operand.reg "%retval.3"))⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_cleanup47_at
  · simpa only [denoteCode_nil] using s2StringBody_cleanup47_denote hpre hinc hop hei
  · have hv : evalOperand (stateAt (("%retval.3", .int 32 form) :: env) s)
        (.reg "%retval.3") = some (.int 32 form) := by s2_lk
    simp only [execTerm, hv]



/-! ### The scan's loop

The loop's own facts: one iteration is two control steps (the head advances,
`while.body` writes the counter and returns), the head's two exits go to
`land.lhs.true` and `if.then9`, and a `BoundLoop` instance composes them. -/

/-- The scan's cursor word after one iteration: the word written where the cursor's
own word stands replaces it in place, so the head's memory is the caller's with the
cursor at the new counter. -/
theorem s2StringBodyScan_advance (mem0 : Mem) (xj c : Nat) (s : State)
    (hmem : s.mem = writeBytes mem0 xj (wordBytes 8 c))
    (hc64 : c + 1 < 2 ^ 64) :
    writeBytes s.mem xj (natToBytes ((BitVec.ofNat 64 c) + 1#64).toNat 8) =
      writeBytes mem0 xj (wordBytes 8 (c + 1)) := by
  rw [hmem]
  have htoNat : ((BitVec.ofNat 64 c) + 1#64).toNat = c + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  rw [htoNat]
  exact writeBytes_writeBytes_same mem0 xj (wordBytes 8 c) (wordBytes 8 (c + 1))
    (by simp [wordBytes, natToBytes_length])

/-- **The scan's iteration**: two control steps from the head back to the head. -/
theorem s2StringBodyScanIterate {envH : Env} {s : State} {p : String} {op : Operand}
    {inc24 nxp : BitVec 64} {xp xj : Nat} {bs : List UInt8} {sub : BitVec 64}
    (hpc : s.pc = "land.rhs") (hpre : s.pre = some p)
    (hxj : lookupName envH "%xj" = some (.ptr xj))
    (hnxp : lookupName envH "%nxp" = some (.int 64 nxp))
    (hinc : phiIncoming p [("while.body", Operand.reg "%inc"),
      ("while.cond.preheader", Operand.reg "%xj.promoted")] = some op)
    (hop : evalOperand (stateAt envH s) op = some (.int 64 inc24))
    (hxp : lookupName envH "%xp" = some (.ptr xp))
    (hsub : lookupName envH "%sub.ptr.sub" = some (.int 64 sub))
    (hpos : (inc24.signExtend 64).toNat < 2 ^ 63)
    (hlane : readBytes s.mem (xp + (inc24.signExtend 64).toNat * 4) 4 = some bs)
    (hbit1 : evalICmpNat .ugt 64 sub.toNat
      (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat).toNat = 1#1)
    (hbit2 : evalICmp .eq (inc24 + 1#64) nxp = 0#1) :
    ∀ k, runFuel s2StringBodyCalls (2 + k) s2StringBodyBody (stateAt envH s) =
      runFuel s2StringBodyCalls k s2StringBodyBody
        (stateAt
          (("%exitcond.not", .int 1 (evalICmp .eq (inc24 + 1#64) nxp)) ::
            ("%inc", .int 64 (inc24 + 1#64)) ::
            s2StringBodyLandRhsEnv envH inc24 xp bs sub)
          ({ s with mem := writeBytes s.mem xj (natToBytes (inc24 + 1#64).toNat 8), pc := "land.rhs", pre := some "while.body" })) := by
  intro k
  have h1 := step_landRhs_while (env := envH) (s := s) (p := p) (op := op)
    hpc hpre hinc hop hxp hsub hpos hlane hbit1
  have h2 := step_whileBody_back
    (env := s2StringBodyLandRhsEnv envH inc24 xp bs sub)
    (s := { s with pc := "while.body", pre := some s.pc })
    (inc24 := inc24) (nxp := nxp) (xj := xj)
    rfl (by s2_lk) (by s2_lk) (by s2_lk) hbit2
  calc runFuel s2StringBodyCalls (2 + k) s2StringBodyBody (stateAt envH s)
      = runFuel s2StringBodyCalls (1 + (1 + k)) s2StringBodyBody (stateAt envH s) := by
        rw [show 2 + k = 1 + (1 + k) from by omega]
    _ = runFuel s2StringBodyCalls (1 + k) s2StringBodyBody
          (stateAt (s2StringBodyLandRhsEnv envH inc24 xp bs sub)
            { s with pc := "while.body", pre := some s.pc }) :=
        runFuel_jump_prefix h1 (1 + k)
    _ = runFuel s2StringBodyCalls k s2StringBodyBody
          (stateAt
            (("%exitcond.not", .int 1 (evalICmp .eq (inc24 + 1#64) nxp)) ::
              ("%inc", .int 64 (inc24 + 1#64)) ::
              s2StringBodyLandRhsEnv envH inc24 xp bs sub)
            ({ s with mem := writeBytes s.mem xj (natToBytes (inc24 + 1#64).toNat 8), pc := "land.rhs", pre := some "while.body" })) :=
        runFuel_jump_prefix h2 k

/-- **The scan's first exit**: one control step to `land.lhs.true`. -/
theorem s2StringBodyScanExit {envH : Env} {s : State} {p : String} {op : Operand}
    {inc24 : BitVec 64} {xp : Nat} {bs : List UInt8} {sub : BitVec 64}
    (hpc : s.pc = "land.rhs") (hpre : s.pre = some p)
    (hinc : phiIncoming p [("while.body", Operand.reg "%inc"),
      ("while.cond.preheader", Operand.reg "%xj.promoted")] = some op)
    (hop : evalOperand (stateAt envH s) op = some (.int 64 inc24))
    (hxp : lookupName envH "%xp" = some (.ptr xp))
    (hsub : lookupName envH "%sub.ptr.sub" = some (.int 64 sub))
    (hpos : (inc24.signExtend 64).toNat < 2 ^ 63)
    (hlane : readBytes s.mem (xp + (inc24.signExtend 64).toNat * 4) 4 = some bs)
    (hbit : evalICmpNat .ugt 64 sub.toNat
      (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat).toNat = 0#1) :
    ∀ k, runFuel s2StringBodyCalls (1 + k) s2StringBodyBody (stateAt envH s) =
      runFuel s2StringBodyCalls k s2StringBodyBody
        (stateAt (s2StringBodyLandRhsEnv envH inc24 xp bs sub)
          { s with pc := "land.lhs.true", pre := some s.pc }) := by
  intro k
  exact runFuel_jump_prefix
    (step_landRhs_exit hpc hpre hinc hop hxp hsub hpos hlane hbit) k

/-- **The scan's back edge.**  One iteration is two control steps. -/
theorem s2StringBodyScan_step_loop (mem0 : Mem) (xj pos0 xp N : Nat) (ps : List Nat)
    (hps : readLanes32 mem0 xp N = some ps)
    (hdisj : ∀ k, k < N → xp + 4 * k + 4 ≤ xj ∨ xj + 8 ≤ xp + 4 * k)
    (hN : N < 2 ^ 63) (hpos0 : pos0 < 2 ^ 64)
    (r c : Nat) (s : State)
    (hinv : s2StringBodyScanInv mem0 xj pos0 xp N ps (r + 1) s c)
    (hbound : s2StringBodyScanAtBound ps pos0 N s c = false) :
    ∃ (e : State) (c' : Nat) (j : Nat), j ≤ 2 ∧ e.pc = "land.rhs" ∧ c < c' ∧
      s2StringBodyScanInv mem0 xj pos0 xp N ps r e c' ∧
      ∀ k, runFuel s2StringBodyCalls (j + k) s2StringBodyBody s =
        runFuel s2StringBodyCalls k s2StringBodyBody e := by
  obtain ⟨hpc, hmem, hsum, ⟨p, op, hpre, hinc, hop⟩, hxp, hsub, hxj, hnxp,
    ⟨q, bs, hq, hblen, hval, hlane⟩⟩ := hinv
  have hlen : ps.length = N := (readLanes32_lane hps).1
  have hb : s2StringBodyScanAtBound ps pos0 N s c = false := hbound
  rw [s2StringBodyScanAtBound_false] at hbound
  have hcN : c + 1 < N := by
    by_contra h; exact hbound (Or.inl (by omega))
  have hc : c < N := by omega
  have hN64 : N < 2 ^ 64 := by omega
  have hpos : ((BitVec.ofNat 64 c).signExtend 64).toNat < 2 ^ 63 := by
    rw [signExtend_ofNat c (by omega)]; omega
  obtain ⟨hbit1, hbit2⟩ :=
    s2StringBodyScan_bits_of_not_atBound hb hq hval hblen rfl hpos0 rfl rfl hN64
  have hidx : ((BitVec.ofNat 64 c).signExtend 64).toNat * 4 = 4 * c := by
    rw [signExtend_ofNat c (by omega)]
    omega
  have hlane' : readBytes s.mem (xp + ((BitVec.ofNat 64 c).signExtend 64).toNat * 4) 4
      = some bs := by
    rw [hidx]
    exact hlane
  have hrun := s2StringBodyScanIterate (envH := s.env) (s := s) (p := p) (op := op)
    hpc hpre hxj hnxp hinc hop hxp hsub hpos hlane' hbit1 hbit2
  obtain ⟨laneQ, laneBs, hq', hlaneM, hval'⟩ :=
    (readLanes32_lane hps).2 (c + 1) hcN
  have hblen' : laneBs.length = 4 := readBytes_length_some hlaneM
  have hframe : readBytes (writeBytes mem0 xj (wordBytes 8 (c + 1))) (xp + 4 * (c + 1)) 4
      = some laneBs := by
    rcases hdisj (c + 1) hcN with h | h
    · rw [readBytes_writeBytes_below mem0 (wordBytes 8 (c + 1)) 4 (xp + 4 * (c + 1)) xj
        (by omega)]
      exact hlaneM
    · rw [s2StringBodyReadBytes_above mem0 (wordBytes 8 (c + 1)) 4 (xp + 4 * (c + 1)) xj
        (by simp [wordBytes, natToBytes_length]; omega)]
      exact hlaneM
  let e : State := stateAt
      (("%exitcond.not", .int 1 (evalICmp .eq ((BitVec.ofNat 64 c) + 1#64)
          (BitVec.ofNat 64 N))) ::
        ("%inc", .int 64 ((BitVec.ofNat 64 c) + 1#64)) ::
        s2StringBodyLandRhsEnv s.env (BitVec.ofNat 64 c) xp bs (BitVec.ofNat 64 pos0))
      ({ s with mem := writeBytes s.mem xj (natToBytes ((BitVec.ofNat 64 c) + 1#64).toNat 8), pc := "land.rhs", pre := some "while.body" })
  refine ⟨e, c + 1, 2, le_rfl, rfl, by omega, ?_, ?_⟩
  · refine ⟨rfl, ?_, by omega,
      ⟨"while.body", Operand.reg "%inc", rfl, by simp [phiIncoming], ?_⟩,
      ?_, ?_, ?_, ?_, ⟨laneQ, laneBs, hq', hblen', hval', ?_⟩⟩
    · exact s2StringBodyScan_advance mem0 xj c s hmem (by omega)
    · simp [e, stateAt, evalOperand, lookupName, s2StringBodyLandRhsEnv, ofNat_add_one]
    · simp only [e, stateAt, lookupName, s2StringBodyLandRhsEnv]; exact hxp
    · simp only [e, stateAt, lookupName, s2StringBodyLandRhsEnv]; exact hsub
    · simp only [e, stateAt, lookupName, s2StringBodyLandRhsEnv]; exact hxj
    · simp only [e, stateAt, lookupName, s2StringBodyLandRhsEnv]; exact hnxp
    · simp only [e]
      rw [show (writeBytes s.mem xj (natToBytes ((BitVec.ofNat 64 c) + 1#64).toNat 8))
          = writeBytes mem0 xj (wordBytes 8 (c + 1)) from
        s2StringBodyScan_advance mem0 xj c s hmem (by omega)]
      exact hframe
  · exact hrun

/-- **The scan's iteration, leaving**: the counter reached the count. -/
theorem s2StringBodyScanIterateExit {envH : Env} {s : State} {p : String} {op : Operand}
    {inc24 nxp : BitVec 64} {xp xj : Nat} {bs : List UInt8} {sub : BitVec 64}
    (hpc : s.pc = "land.rhs") (hpre : s.pre = some p)
    (hxj : lookupName envH "%xj" = some (.ptr xj))
    (hnxp : lookupName envH "%nxp" = some (.int 64 nxp))
    (hinc : phiIncoming p [("while.body", Operand.reg "%inc"),
      ("while.cond.preheader", Operand.reg "%xj.promoted")] = some op)
    (hop : evalOperand (stateAt envH s) op = some (.int 64 inc24))
    (hxp : lookupName envH "%xp" = some (.ptr xp))
    (hsub : lookupName envH "%sub.ptr.sub" = some (.int 64 sub))
    (hpos : (inc24.signExtend 64).toNat < 2 ^ 63)
    (hlane : readBytes s.mem (xp + (inc24.signExtend 64).toNat * 4) 4 = some bs)
    (hbit1 : evalICmpNat .ugt 64 sub.toNat
      (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat).toNat = 1#1)
    (hbit2 : evalICmp .eq (inc24 + 1#64) nxp = 1#1) :
    ∀ k, runFuel s2StringBodyCalls (2 + k) s2StringBodyBody (stateAt envH s) =
      runFuel s2StringBodyCalls k s2StringBodyBody
        (stateAt
          (("%exitcond.not", .int 1 (evalICmp .eq (inc24 + 1#64) nxp)) ::
            ("%inc", .int 64 (inc24 + 1#64)) ::
            s2StringBodyLandRhsEnv envH inc24 xp bs sub)
          ({ s with mem := writeBytes s.mem xj (natToBytes (inc24 + 1#64).toNat 8), pc := "if.then9", pre := some "while.body" })) := by
  intro k
  have h1 := step_landRhs_while (env := envH) (s := s) (p := p) (op := op)
    hpc hpre hinc hop hxp hsub hpos hlane hbit1
  have h2 := step_whileBody_exit
    (env := s2StringBodyLandRhsEnv envH inc24 xp bs sub)
    (s := { s with pc := "while.body", pre := some s.pc })
    (inc24 := inc24) (nxp := nxp) (xj := xj)
    rfl (by s2_lk) (by s2_lk) (by s2_lk) hbit2
  calc runFuel s2StringBodyCalls (2 + k) s2StringBodyBody (stateAt envH s)
      = runFuel s2StringBodyCalls (1 + (1 + k)) s2StringBodyBody (stateAt envH s) := by
        rw [show 2 + k = 1 + (1 + k) from by omega]
    _ = runFuel s2StringBodyCalls (1 + k) s2StringBodyBody
          (stateAt (s2StringBodyLandRhsEnv envH inc24 xp bs sub)
            { s with pc := "while.body", pre := some s.pc }) :=
        runFuel_jump_prefix h1 (1 + k)
    _ = runFuel s2StringBodyCalls k s2StringBodyBody
          (stateAt
            (("%exitcond.not", .int 1 (evalICmp .eq (inc24 + 1#64) nxp)) ::
              ("%inc", .int 64 (inc24 + 1#64)) ::
              s2StringBodyLandRhsEnv envH inc24 xp bs sub)
            ({ s with mem := writeBytes s.mem xj (natToBytes (inc24 + 1#64).toNat 8), pc := "if.then9", pre := some "while.body" })) :=
        runFuel_jump_prefix h2 k

/-- The blocks the scan may leave for. -/
def s2StringBodyScanExited (e : State) : Prop :=
  e.pc = "land.lhs.true" ∨ e.pc = "if.then9"

/-- What the scan leaves behind: the cursor word at the counter it stopped at, and
that counter being the count or the first lane inside the body. -/
def s2StringBodyScanExitWord (mem0 : Mem) (xj : Nat) (ps : List Nat) (pos0 N : Nat)
    (e : State) : Prop :=
  ∃ c, e.mem = writeBytes mem0 xj (wordBytes 8 c) ∧
    (N ≤ c + 1 ∨ ∃ q, ps[c]? = some q ∧ pos0 ≤ q)

theorem s2StringBodyScan_step_exit (mem0 : Mem) (xj pos0 xp N : Nat)
    (ps : List Nat)
    (hps : readLanes32 mem0 xp N = some ps)
    (hdisj : ∀ k, k < N → xp + 4 * k + 4 ≤ xj ∨ xj + 8 ≤ xp + 4 * k)
    (hN : N < 2 ^ 63) (hpos0 : pos0 < 2 ^ 64)
    (r c : Nat) (s : State)
    (hinv : s2StringBodyScanInv mem0 xj pos0 xp N ps r s c)
    (hbound : s2StringBodyScanAtBound ps pos0 N s c = true) :
    ∃ (e : State) (j : Nat), j ≤ 2 ∧ s2StringBodyScanExited e ∧
      s2StringBodyScanExitWord mem0 xj ps pos0 N e ∧
      ∀ k, runFuel s2StringBodyCalls (j + k) s2StringBodyBody s =
        runFuel s2StringBodyCalls k s2StringBodyBody e := by
  obtain ⟨hpc, hmem, hsum, ⟨p, op, hpre, hinc, hop⟩, hxp, hsub, hxj, hnxp,
    ⟨q, bs, hq, hblen, hval, hlane⟩⟩ := hinv
  have hlen : ps.length = N := (readLanes32_lane hps).1
  have hcN : c < N := by
    have : c < ps.length := by
      by_contra h
      rw [List.getElem?_eq_none (by omega)] at hq
      cases hq
    omega
  have hb : s2StringBodyScanAtBound ps pos0 N s c = true := hbound
  rw [s2StringBodyScanAtBound_eq] at hbound
  have hN64 : N < 2 ^ 64 := by omega
  have hpos : ((BitVec.ofNat 64 c).signExtend 64).toNat < 2 ^ 63 := by
    rw [signExtend_ofNat c (by omega)]; omega
  have hidx : ((BitVec.ofNat 64 c).signExtend 64).toNat * 4 = 4 * c := by
    rw [signExtend_ofNat c (by omega)]; omega
  have hlane' : readBytes s.mem (xp + ((BitVec.ofNat 64 c).signExtend 64).toNat * 4) 4
      = some bs := by
    rw [hidx]; exact hlane
  have hconv : (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat).toNat = q := by
    have h32 := bytesToNat_lt_32 hblen
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h32,
      Nat.mod_eq_of_lt (by omega), hval]
  by_cases hge : pos0 ≤ q
  · have hbit : evalICmpNat .ugt 64 (BitVec.ofNat 64 pos0).toNat
        (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat).toNat = 0#1 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpos0, hconv]
      exact evalICmpNat_ugt_of_ge hpos0 (by have := bytesToNat_lt_32 hblen; omega) hge
    have hrun := s2StringBodyScanExit (envH := s.env) (s := s) (p := p) (op := op)
      hpc hpre hinc hop hxp hsub hpos hlane' hbit
    let e : State := stateAt (s2StringBodyLandRhsEnv s.env (BitVec.ofNat 64 c) xp bs
        (BitVec.ofNat 64 pos0)) { s with pc := "land.lhs.true", pre := some s.pc }
    refine ⟨e, 1, by decide, Or.inl rfl, ?_, hrun⟩
    exact ⟨c, by simp only [e, stateAt]; exact hmem, Or.inr ⟨q, hq, hge⟩⟩
  · have hlt : q < pos0 := by omega
    have hNle : N ≤ c + 1 := by
      rcases hbound with h | ⟨q', hq', hge'⟩
      · exact h
      · rw [hq] at hq'; cases Option.some.inj hq'; exact absurd hge' hge
    have heqc : c + 1 = N := by omega
    have hbit1 : evalICmpNat .ugt 64 (BitVec.ofNat 64 pos0).toNat
        (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat).toNat = 1#1 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpos0, hconv]
      exact evalICmpNat_ugt_one hpos0 (by have := bytesToNat_lt_32 hblen; omega) hlt
    have hbit2 : evalICmp .eq ((BitVec.ofNat 64 c) + 1#64) (BitVec.ofNat 64 N) = 1#1 :=
      evalICmp_eq_of_eq hN64 heqc.symm
    have hrun := s2StringBodyScanIterateExit (envH := s.env) (s := s) (p := p) (op := op)
      hpc hpre hxj hnxp hinc hop hxp hsub hpos hlane' hbit1 hbit2
    let e : State := stateAt
        (("%exitcond.not", .int 1 (evalICmp .eq ((BitVec.ofNat 64 c) + 1#64)
            (BitVec.ofNat 64 N))) ::
          ("%inc", .int 64 ((BitVec.ofNat 64 c) + 1#64)) ::
          s2StringBodyLandRhsEnv s.env (BitVec.ofNat 64 c) xp bs (BitVec.ofNat 64 pos0))
        ({ s with mem := writeBytes s.mem xj (natToBytes ((BitVec.ofNat 64 c) + 1#64).toNat 8), pc := "if.then9", pre := some "while.body" })
    refine ⟨e, 2, le_rfl, Or.inr rfl, ?_, hrun⟩
    refine ⟨c + 1, ?_, Or.inl (by omega)⟩
    simp only [e, stateAt]
    rw [show (writeBytes s.mem xj (natToBytes ((BitVec.ofNat 64 c) + 1#64).toNat 8))
        = writeBytes mem0 xj (wordBytes 8 (c + 1)) from
      s2StringBodyScan_advance mem0 xj c s hmem (by omega)]

/-- **The scan, as a `BoundLoop`**, handing back the lanes it passed. -/
def s2StringBodyScanLoop (mem0 : Mem) (xj pos0 xp N : Nat) (ps : List Nat)
    (hps : readLanes32 mem0 xp N = some ps)
    (hdisj : ∀ k, k < N → xp + 4 * k + 4 ≤ xj ∨ xj + 8 ≤ xp + 4 * k)
    (hN : N < 2 ^ 63) (hpos0 : pos0 < 2 ^ 64) :
    BoundLoop s2StringBodyCalls s2StringBodyBody where
  head := "land.rhs"
  exitBlock := "land.lhs.true"
  N := N
  cost := 2
  Inv := s2StringBodyScanInv mem0 xj pos0 xp N ps
  atBound := s2StringBodyScanAtBound ps pos0 N
  Exit := s2StringBodyScanExited
  ExitWord := s2StringBodyScanExitWord mem0 xj ps pos0 N
  step_exit := fun r s c =>
    s2StringBodyScan_step_exit mem0 xj pos0 xp N ps hps hdisj hN hpos0 r c s
  step_loop := fun r s c =>
    s2StringBodyScan_step_loop mem0 xj pos0 xp N ps hps hdisj hN hpos0 r c s
  exit_at_zero := by
    intro s c h
    obtain ⟨_hpc, _hmem, hsum, _⟩ := h
    rw [s2StringBodyScanAtBound_eq]
    exact Or.inl (by omega)
  budget := by
    intro r s c h
    obtain ⟨_hpc, _hmem, hsum, _⟩ := h
    omega

/-- **The scan's fuel**: `(N + 1) * 2` control steps from the head, and the exit's
continuation at its own fuel. -/
theorem s2StringBodyScan_run (mem0 : Mem) (xj pos0 xp N : Nat) (ps : List Nat)
    (hps : readLanes32 mem0 xp N = some ps)
    (hdisj : ∀ k, k < N → xp + 4 * k + 4 ≤ xj ∨ xj + 8 ≤ xp + 4 * k)
    (hN : N < 2 ^ 63) (hpos0 : pos0 < 2 ^ 64)
    (s : State) (c : Nat) (k : Nat)
    (hinv : s2StringBodyScanInv mem0 xj pos0 xp N ps N s c) {o : Outcome}
    (hcont : ∀ (e : State), s2StringBodyScanExited e →
      s2StringBodyScanExitWord mem0 xj ps pos0 N e →
      runFuel s2StringBodyCalls k s2StringBodyBody e = some o) :
    runFuel s2StringBodyCalls ((N + 1) * 2 + k) s2StringBodyBody s = some o :=
  (s2StringBodyScanBoundLoop mem0 xj pos0 xp N ps 2
    s2StringBodyScanExited (s2StringBodyScanExitWord mem0 xj ps pos0 N)
    (s2StringBodyScan_step_exit mem0 xj pos0 xp N ps hps hdisj hN hpos0)
    (s2StringBodyScan_step_loop mem0 xj pos0 xp N ps hps hdisj hN hpos0)).run_at
    s c hinv k hcont

/-! ### The entry's prefixes -/

theorem ofNat_sub (p base : Nat) (hb : base ≤ p) (hp : p < 2 ^ 64) :
    (BitVec.ofNat 64 p) - (BitVec.ofNat 64 base) = BitVec.ofNat 64 (p - base) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- **The entry's step to the list-free arm, as a prefix.** -/
theorem s2StringBodyEntry_prefix_ifEnd16 {env : Env} {s : State}
    {c p base : Nat} {nxp : BitVec 64}
    (hpc : s.pc = "entry")
    (hc : lookupName env "%c" = some (.ptr c))
    (hp : lookupName env "%p" = some (.ptr p))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hbase : readBytes s.mem c 8 = some (wordBytes 8 base)) (hb64 : base < 2 ^ 64)
    (hp64 : p < 2 ^ 64)
    (hbit : evalICmp .eq nxp (BitVec.ofNat 64 0) = 1#1) :
    ∀ k, runFuel s2StringBodyCalls (1 + k) s2StringBodyBody (stateAt env s) =
      runFuel s2StringBodyCalls k s2StringBodyBody
        (stateAt (s2StringBodyEntryOut env s.next base p nxp)
          ({ s with next := s.next + (Ty.int 64).sizeBytes, pc := "if.end16", pre := some s.pc })) := by
  intro k
  exact runFuel_jump_prefix
    (step_entry_ifEnd16 hpc hc hp hnxp hbase hb64 hp64 hbit) k

/-- **The entry's step to the scan arm, as a prefix.** -/
theorem s2StringBodyEntry_prefix_whileCond {env : Env} {s : State}
    {c p base : Nat} {nxp : BitVec 64}
    (hpc : s.pc = "entry")
    (hc : lookupName env "%c" = some (.ptr c))
    (hp : lookupName env "%p" = some (.ptr p))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hbase : readBytes s.mem c 8 = some (wordBytes 8 base)) (hb64 : base < 2 ^ 64)
    (hp64 : p < 2 ^ 64)
    (hbit : evalICmp .eq nxp (BitVec.ofNat 64 0) = 0#1) :
    ∀ k, runFuel s2StringBodyCalls (1 + k) s2StringBodyBody (stateAt env s) =
      runFuel s2StringBodyCalls k s2StringBodyBody
        (stateAt (s2StringBodyEntryOut env s.next base p nxp)
          ({ s with next := s.next + (Ty.int 64).sizeBytes, pc := "while.cond.preheader", pre := some s.pc })) := by
  intro k
  exact runFuel_jump_prefix
    (step_entry_whileCond hpc hc hp hnxp hbase hb64 hp64 hbit) k

/-- **The scan head's test, as a prefix**, the scan's head leaving for the loop. -/
theorem s2StringBodyWhileCond_prefix_landRhs {env : Env} {s : State} {xj : Nat}
    {j0 nxp : BitVec 64}
    (hpc : s.pc = "while.cond.preheader")
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hj0 : readBytes s.mem xj 8 = some (wordBytes 8 j0.toNat))
    (hj64 : j0.toNat < 2 ^ 64)
    (hbit : evalICmp .ult j0 nxp = 1#1) :
    ∀ k, runFuel s2StringBodyCalls (1 + k) s2StringBodyBody (stateAt env s) =
      runFuel s2StringBodyCalls k s2StringBodyBody
        (stateAt (s2StringBodyWhileCondEnv env j0 nxp)
          { s with pc := "land.rhs", pre := some s.pc }) := by
  intro k
  exact runFuel_jump_prefix
    (step_whileCond_landRhs hpc hxj hnxp hj0 hj64 hbit) k

/-- **The scan head's test, as a prefix**, the body-itself arm. -/
theorem s2StringBodyWhileCond_prefix_ifThen9 {env : Env} {s : State} {xj : Nat}
    {j0 nxp : BitVec 64}
    (hpc : s.pc = "while.cond.preheader")
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hj0 : readBytes s.mem xj 8 = some (wordBytes 8 j0.toNat))
    (hj64 : j0.toNat < 2 ^ 64)
    (hbit : evalICmp .ult j0 nxp = 0#1) :
    ∀ k, runFuel s2StringBodyCalls (1 + k) s2StringBodyBody (stateAt env s) =
      runFuel s2StringBodyCalls k s2StringBodyBody
        (stateAt (s2StringBodyWhileCondEnv env j0 nxp)
          { s with pc := "if.then9", pre := some s.pc }) := by
  intro k
  exact runFuel_jump_prefix
    (step_whileCond_ifThen9 hpc hxj hnxp hj0 hj64 hbit) k

/-- **Seating the scan's invariant at the head the entry's test left.** -/
theorem s2StringBodyScanInv_seat (env : Env) (s : State) (base p xj xp j0 : Nat)
    (ps : List Nat) (nxp : BitVec 64)
    (hbase : base ≤ p) (hp64 : p < 2 ^ 64)
    (hword : stage2ReadWord s.mem xj 8 = some j0)
    (hps : readLanes32 s.mem xp nxp.toNat = some ps)
    (hj0 : j0 < nxp.toNat)
    (hxpc : lookupName env "%xp" = some (.ptr xp))
    (hxjc : lookupName env "%xj" = some (.ptr xj))
    (hnxpc : lookupName env "%nxp" = some (.int 64 nxp)) :
    s2StringBodyScanInv s.mem xj (p - base) xp nxp.toNat ps (nxp.toNat - j0)
      (stateAt
        (s2StringBodyWhileCondEnv (s2StringBodyEntryOut env s.next base p nxp)
          (BitVec.ofNat 64 j0) nxp)
        { s with next := s.next + (Ty.int 64).sizeBytes, pc := "land.rhs", pre := some "while.cond.preheader" })
      j0 := by
  obtain ⟨q, bs, hq, hlaneM, hval⟩ := (readLanes32_lane hps).2 j0 hj0
  have hblen : bs.length = 4 := readBytes_length_some hlaneM
  have hpres := stage2ReadWord_writeBytes_self s.mem xj 8 j0 hword
  have hnxp : BitVec.ofNat 64 nxp.toNat = nxp := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt nxp.isLt]
  refine ⟨rfl, ?_, by omega, ?_, ?_, ?_, ?_, ?_, ⟨q, bs, hq, hblen, hval, ?_⟩⟩
  · simpa only [stateAt] using hpres.symm
  · refine ⟨"while.cond.preheader", Operand.reg "%xj.promoted", ?_,
      by simp [phiIncoming], ?_⟩
    · simp only [stateAt]
    · simp [stateAt, evalOperand, lookupName, s2StringBodyWhileCondEnv,
        s2StringBodyEntryOut, s2StringBodyEnv6, s2StringBodyEnv5, s2StringBodyEnv4,
        s2StringBodyEnv3, s2StringBodyEnv2, s2StringBodyEnv1]
  · simp [stateAt, lookupName, s2StringBodyWhileCondEnv, s2StringBodyEntryOut,
      s2StringBodyEnv6, s2StringBodyEnv5, s2StringBodyEnv4, s2StringBodyEnv3,
      s2StringBodyEnv2, s2StringBodyEnv1, hxpc]
  · simp [stateAt, lookupName, s2StringBodyWhileCondEnv, s2StringBodyEntryOut,
      s2StringBodyEnv6, s2StringBodyEnv5, s2StringBodyEnv4, s2StringBodyEnv3,
      s2StringBodyEnv2, s2StringBodyEnv1, ofNat_sub p base hbase hp64]
  · simp [stateAt, lookupName, s2StringBodyWhileCondEnv, s2StringBodyEntryOut,
      s2StringBodyEnv6, s2StringBodyEnv5, s2StringBodyEnv4, s2StringBodyEnv3,
      s2StringBodyEnv2, s2StringBodyEnv1, hxjc]
  · simp [stateAt, lookupName, s2StringBodyWhileCondEnv, s2StringBodyEntryOut,
      s2StringBodyEnv6, s2StringBodyEnv5, s2StringBodyEnv4, s2StringBodyEnv3,
      s2StringBodyEnv2, s2StringBodyEnv1, hnxp, hnxpc]
  · simp only [stateAt]
    exact hlaneM

/-! ### The terminal runs

Every path's last link: the merged cleanup returns the form the edge selected, and
the arm's last block writes the memory before it. -/

/-- A `ret` step completes the run: the outcome carries the returned word and the
memory the block left. -/
theorem runFuel_ret_mem {calls : Calls} {f : Function} {s s' : State} {v : Value}
    (h : step calls f s = .ret (some v) s') (k : Nat) :
    runFuel calls (1 + k) f s = some (.ret (some v) s'.mem) := by
  rw [show 1 + k = k + 1 from by omega]
  simp only [runFuel, h]

/-- **`cleanup47` finishes**: the `phi`'s form and the function's answer, one
control step. -/
theorem s2StringBodyCleanup47_finishes {env : Env} {s : State} {p : String}
    {op : Operand} {form : BitVec 32} {ei : Nat}
    (hpc : s.pc = "cleanup47") (hpre : s.pre = some p)
    (hinc : phiIncoming p
      [("if.then9", Operand.imm (Const.int 32 0x00000001#32)),
       ("if.then12", Operand.imm (Const.int 32 0x00000000#32)),
       ("if.end15", Operand.imm (Const.int 32 0x00000002#32)),
       ("if.then20", Operand.imm (Const.int 32 0x00000001#32)),
       ("if.then26", Operand.imm (Const.int 32 0x00000000#32)),
       ("if.then35", Operand.imm (Const.int 32 0x00000000#32)),
       ("if.end43", Operand.imm (Const.int 32 0x00000002#32))] = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 32 form))
    (hei : lookupName env "%ei" = some (.ptr ei)) :
    runFuel s2StringBodyCalls 1 s2StringBodyBody (stateAt env s) =
      some (.ret (some (.int 32 form))
        (stateAt (("%retval.3", .int 32 form) :: env) s).mem) :=
  runFuel_ret_mem (step_cleanup47_ret hpc hpre hinc hop hei) 0

/-- **The body-itself arm's end**: `if.then9` writes the extent's word at `outn`,
`cleanup47` returns `1`, two control steps. -/
theorem s2StringBodyIfThen9_finishes {env : Env} {s : State} {len : BitVec 64}
    {outn ei : Nat}
    (hpc : s.pc = "if.then9")
    (hlen : lookupName env "%len" = some (.int 64 len))
    (houtn : lookupName env "%outn" = some (.ptr outn))
    (hei : lookupName env "%ei" = some (.ptr ei)) :
    runFuel s2StringBodyCalls 2 s2StringBodyBody (stateAt env s) =
      some (.ret (some (.int 32 0x00000001#32))
        (writeBytes s.mem outn (natToBytes len.toNat 8))) := by
  have h1 := step_ifThen9_cleanup47 hpc hlen houtn
  have hpre : ∀ k, runFuel s2StringBodyCalls (1 + k) s2StringBodyBody (stateAt env s) =
      runFuel s2StringBodyCalls k s2StringBodyBody
        (stateAt env { s with mem := writeBytes s.mem outn (natToBytes len.toNat 8), pc := "cleanup47", pre := some s.pc }) :=
    fun k => runFuel_jump_prefix h1 k
  have hfin : runFuel s2StringBodyCalls 1 s2StringBodyBody
      (stateAt env { s with mem := writeBytes s.mem outn (natToBytes len.toNat 8), pc := "cleanup47", pre := some s.pc }) =
      some (.ret (some (.int 32 0x00000001#32))
        (writeBytes s.mem outn (natToBytes len.toNat 8))) :=
    s2StringBodyCleanup47_finishes (env := env)
      (s := { s with mem := writeBytes s.mem outn (natToBytes len.toNat 8), pc := "cleanup47", pre := some s.pc })
      (p := "if.then9") (op := .imm (Const.int 32 0x00000001#32)) (form := 0x00000001#32)
      rfl (by rw [hpc]) (by simp [phiIncoming]) rfl hei
  simpa only [stateAt] using runFuel_prefix_some hpre hfin

/-- **The decoded length's end**: `if.end15` writes the word at `outn`,
`cleanup47` returns `2`, two control steps. -/
theorem s2StringBodyIfEnd15_finishes {env : Env} {s : State} {call : BitVec 64}
    {outn ei : Nat}
    (hpc : s.pc = "if.end15")
    (hcall : lookupName env "%call" = some (.int 64 call))
    (houtn : lookupName env "%outn" = some (.ptr outn))
    (hei : lookupName env "%ei" = some (.ptr ei)) :
    runFuel s2StringBodyCalls 2 s2StringBodyBody (stateAt env s) =
      some (.ret (some (.int 32 0x00000002#32))
        (writeBytes s.mem outn (natToBytes call.toNat 8))) := by
  have h1 := step_ifEnd15_cleanup47 hpc hcall houtn
  have hpre : ∀ k, runFuel s2StringBodyCalls (1 + k) s2StringBodyBody (stateAt env s) =
      runFuel s2StringBodyCalls k s2StringBodyBody
        (stateAt env { s with mem := writeBytes s.mem outn (natToBytes call.toNat 8), pc := "cleanup47", pre := some s.pc }) :=
    fun k => runFuel_jump_prefix h1 k
  have hfin : runFuel s2StringBodyCalls 1 s2StringBodyBody
      (stateAt env { s with mem := writeBytes s.mem outn (natToBytes call.toNat 8), pc := "cleanup47", pre := some s.pc }) =
      some (.ret (some (.int 32 0x00000002#32))
        (writeBytes s.mem outn (natToBytes call.toNat 8))) :=
    s2StringBodyCleanup47_finishes (env := env)
      (s := { s with mem := writeBytes s.mem outn (natToBytes call.toNat 8), pc := "cleanup47", pre := some s.pc })
      (p := "if.end15") (op := .imm (Const.int 32 0x00000002#32)) (form := 0x00000002#32)
      rfl (by rw [hpc]) (by simp [phiIncoming]) rfl hei
  simpa only [stateAt] using runFuel_prefix_some hpre hfin

set_option maxHeartbeats 4000000 in
/-- **The refusal record's end**: `if.then12` writes the record, `cleanup47`
returns `0`, two control steps. -/
theorem s2StringBodyIfThen12_finishes {env : Env} {s : State} {c ei e : Nat}
    {off sub : BitVec 64}
    (hpc : s.pc = "if.then12")
    (hc : lookupName env "%c" = some (.ptr c))
    (hei : lookupName env "%ei" = some (.ptr ei))
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hoff : readBytes s.mem ei 8 = some (natToBytes off.toNat 8))
    (hcval : readBytes s.mem (c + (1112#64).toNat) 8 = some (wordBytes 8 e))
    (he64 : e < 2 ^ 64)
    (hslot : lookupName (s2StringBodyIfThen12Env env off sub c e) "%ei"
      = some (.ptr ei)) :
    runFuel s2StringBodyCalls 2 s2StringBodyBody (stateAt env s) =
      some (.ret (some (.int 32 0x00000000#32))
        (s2StringBodyIfThen12Mem s.mem e off sub)) := by
  have h1 := step_ifThen12_cleanup47 hpc hc hei hsub hoff hcval he64
  have hpre : ∀ k, runFuel s2StringBodyCalls (1 + k) s2StringBodyBody (stateAt env s) =
      runFuel s2StringBodyCalls k s2StringBodyBody
        (stateAt (s2StringBodyIfThen12Env env off sub c e)
          { s with mem := s2StringBodyIfThen12Mem s.mem e off sub, pc := "cleanup47", pre := some s.pc }) :=
    fun k => runFuel_jump_prefix h1 k
  have hfin : runFuel s2StringBodyCalls 1 s2StringBodyBody
      (stateAt (s2StringBodyIfThen12Env env off sub c e)
        { s with mem := s2StringBodyIfThen12Mem s.mem e off sub, pc := "cleanup47", pre := some s.pc }) =
      some (.ret (some (.int 32 0x00000000#32))
        (s2StringBodyIfThen12Mem s.mem e off sub)) :=
    s2StringBodyCleanup47_finishes (env := s2StringBodyIfThen12Env env off sub c e)
      (s := { s with mem := s2StringBodyIfThen12Mem s.mem e off sub, pc := "cleanup47", pre := some s.pc })
      (p := "if.then12") (op := .imm (Const.int 32 0x00000000#32)) (form := 0x00000000#32)
      rfl (by rw [hpc]) (by simp [phiIncoming]) rfl hslot
  simpa using runFuel_prefix_some hpre hfin

/-- **The inside test at the body-itself arm**: `land.lhs.true`, `if.then9`,
`cleanup47` — three control steps, form `1`. -/
theorem s2StringBodyLandLhsTrue_toIfThen9_finishes {env : Env} {s : State}
    {sub len conv : BitVec 64} {outn ei : Nat}
    (hpc : s.pc = "land.lhs.true")
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hlen : lookupName env "%len" = some (.int 64 len))
    (hconv : lookupName env "%conv" = some (.int 64 conv))
    (hbit : evalICmpNat .ugt 64 (sub + len).toNat conv.toNat = 0#1)
    (houtn : lookupName env "%outn" = some (.ptr outn))
    (hei : lookupName env "%ei" = some (.ptr ei)) :
    runFuel s2StringBodyCalls 3 s2StringBodyBody (stateAt env s) =
      some (.ret (some (.int 32 0x00000001#32))
        (writeBytes s.mem outn (natToBytes len.toNat 8))) := by
  have hstep := step_landLhsTrue_ifThen9 hpc hsub hlen hconv hbit
  have hfin : runFuel s2StringBodyCalls 2 s2StringBodyBody
      (stateAt (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
        ("%add", .int 64 (sub + len)) :: env)
        { s with pc := "if.then9", pre := some s.pc }) =
      some (.ret (some (.int 32 0x00000001#32))
        (writeBytes s.mem outn (natToBytes len.toNat 8))) :=
    s2StringBodyIfThen9_finishes (env := ("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
        ("%add", .int 64 (sub + len)) :: env)
      (s := { s with pc := "if.then9", pre := some s.pc }) rfl (by s2_lk) (by s2_lk) (by s2_lk)
  have := runFuel_prefix_some (fun k => runFuel_jump_prefix hstep k) hfin
  simpa using this

/-- **The inside test's refusal path**: `land.lhs.true`, `if.end`, `if.then12`,
`cleanup47` — four control steps, form `0`. -/
theorem s2StringBodyLandLhsTrue_refused_finishes {env : Env} {s : State}
    {sub len conv off : BitVec 64} {p dst ei xp xj c e : Nat} {nxp : BitVec 64}
    {extra : Mem} {nx : Nat} {call : BitVec 64}
    (hpc : s.pc = "land.lhs.true")
    (hc : lookupName env "%c" = some (.ptr c))
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hlen : lookupName env "%len" = some (.int 64 len))
    (hconv : lookupName env "%conv" = some (.int 64 conv))
    (hbit7 : evalICmpNat .ugt 64 (sub + len).toNat conv.toNat = 1#1)
    (hp : lookupName env "%p" = some (.ptr p))
    (hdst : lookupName env "%dst" = some (.ptr dst))
    (hei : lookupName env "%ei" = some (.ptr ei))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hexp : s2StringBodyCalls "leanllvm_json_escape_expand"
      [.ptr p, .int 64 len, .ptr dst, .ptr ei, .ptr xp, .ptr xj, .int 64 nxp,
       .int 64 sub] (writeBytes s.mem ei (natToBytes (0#64).toNat 8)) s.next =
      some { ret := .int 64 call, mem := extra, next := nx })
    (hbit10 : evalICmp .eq call 0xffffffffffffffff#64 = 1#1)
    (hoff : readBytes extra ei 8 = some (natToBytes off.toNat 8))
    (hcval : readBytes extra (c + (1112#64).toNat) 8 = some (wordBytes 8 e))
    (he64 : e < 2 ^ 64) :
    runFuel s2StringBodyCalls 4 s2StringBodyBody (stateAt env s) =
      some (.ret (some (.int 32 0x00000000#32))
        (s2StringBodyIfThen12Mem extra e off sub)) := by
  have h1 := step_landLhsTrue_ifEnd hpc hsub hlen hconv hbit7
  have h2 : step s2StringBodyCalls s2StringBodyBody
      (stateAt
        (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
          ("%add", .int 64 (sub + len)) :: env)
        { s with pc := "if.end", pre := some s.pc }) =
      .jump (stateAt (s2StringBodyIfEndEnv
        (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
          ("%add", .int 64 (sub + len)) :: env) call)
        { s with mem := extra, next := nx, pc := "if.then12", pre := some "if.end" }) := by
    refine step_ifEnd_ifThen12 (env := ("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
        ("%add", .int 64 (sub + len)) :: env)
      (s := { s with pc := "if.end", pre := some s.pc }) rfl
      (by s2_lk) (by s2_lk) (by s2_lk) (by s2_lk) (by s2_lk) (by s2_lk) (by s2_lk) (by s2_lk)
      ?_ hbit10
    simpa only [stateAt] using hexp
  have hpre : ∀ k, runFuel s2StringBodyCalls (2 + k) s2StringBodyBody (stateAt env s) =
      runFuel s2StringBodyCalls k s2StringBodyBody
        (stateAt (s2StringBodyIfEndEnv
          (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
            ("%add", .int 64 (sub + len)) :: env) call)
          { s with mem := extra, next := nx, pc := "if.then12", pre := some "if.end" }) := by
    have h12 := runFuel_prefix_trans (fun j => runFuel_jump_prefix h1 j)
      (fun j => runFuel_jump_prefix h2 j)
    intro k
    simpa [show 2 + k = 1 + (1 + k) from by omega] using h12 k
  have hfin := s2StringBodyIfThen12_finishes (env := s2StringBodyIfEndEnv
      (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
        ("%add", .int 64 (sub + len)) :: env) call)
    (s := { s with mem := extra, next := nx, pc := "if.then12", pre := some "if.end" })
    (c := c) (ei := ei) (e := e) (off := off) (sub := sub)
    rfl (by s2_lk) (by s2_lk) (by s2_lk) (by simpa only [stateAt] using hoff)
    (by simpa only [stateAt] using hcval) he64 (by s2_lk)
  have := runFuel_prefix_some hpre hfin
  simpa using this

/-- **The inside test's decoded path**: `land.lhs.true`, `if.end`, `if.end15`,
`cleanup47` — four control steps, form `2`. -/
theorem s2StringBodyLandLhsTrue_decoded_finishes {env : Env} {s : State}
    {sub len conv : BitVec 64} {p dst ei outn xp xj : Nat} {nxp : BitVec 64}
    {extra : Mem} {nx : Nat} {call : BitVec 64}
    (hpc : s.pc = "land.lhs.true")
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hlen : lookupName env "%len" = some (.int 64 len))
    (hconv : lookupName env "%conv" = some (.int 64 conv))
    (hbit7 : evalICmpNat .ugt 64 (sub + len).toNat conv.toNat = 1#1)
    (hp : lookupName env "%p" = some (.ptr p))
    (hdst : lookupName env "%dst" = some (.ptr dst))
    (hei : lookupName env "%ei" = some (.ptr ei))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hexp : s2StringBodyCalls "leanllvm_json_escape_expand"
      [.ptr p, .int 64 len, .ptr dst, .ptr ei, .ptr xp, .ptr xj, .int 64 nxp,
       .int 64 sub] (writeBytes s.mem ei (natToBytes (0#64).toNat 8)) s.next =
      some { ret := .int 64 call, mem := extra, next := nx })
    (hbit10 : evalICmp .eq call 0xffffffffffffffff#64 = 0#1)
    (houtn : lookupName env "%outn" = some (.ptr outn)) :
    runFuel s2StringBodyCalls 4 s2StringBodyBody (stateAt env s) =
      some (.ret (some (.int 32 0x00000002#32))
        (writeBytes extra outn (natToBytes call.toNat 8))) := by
  have h1 := step_landLhsTrue_ifEnd hpc hsub hlen hconv hbit7
  have h2 : step s2StringBodyCalls s2StringBodyBody
      (stateAt
        (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
          ("%add", .int 64 (sub + len)) :: env)
        { s with pc := "if.end", pre := some s.pc }) =
      .jump (stateAt (s2StringBodyIfEndEnv
        (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
          ("%add", .int 64 (sub + len)) :: env) call)
        { s with mem := extra, next := nx, pc := "if.end15", pre := some "if.end" }) := by
    refine step_ifEnd_ifEnd15 (env := ("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
        ("%add", .int 64 (sub + len)) :: env)
      (s := { s with pc := "if.end", pre := some s.pc }) rfl
      (by s2_lk) (by s2_lk) (by s2_lk) (by s2_lk) (by s2_lk) (by s2_lk) (by s2_lk) (by s2_lk)
      ?_ hbit10
    simpa only [stateAt] using hexp
  have hpre : ∀ k, runFuel s2StringBodyCalls (2 + k) s2StringBodyBody (stateAt env s) =
      runFuel s2StringBodyCalls k s2StringBodyBody
        (stateAt (s2StringBodyIfEndEnv
          (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
            ("%add", .int 64 (sub + len)) :: env) call)
          { s with mem := extra, next := nx, pc := "if.end15", pre := some "if.end" }) := by
    have h12 := runFuel_prefix_trans (fun j => runFuel_jump_prefix h1 j)
      (fun j => runFuel_jump_prefix h2 j)
    intro k
    simpa [show 2 + k = 1 + (1 + k) from by omega] using h12 k
  have hfin := s2StringBodyIfEnd15_finishes (env := s2StringBodyIfEndEnv
      (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
        ("%add", .int 64 (sub + len)) :: env) call)
    (s := { s with mem := extra, next := nx, pc := "if.end15", pre := some "if.end" })
    (call := call) (outn := outn) (ei := ei)
    rfl (by s2_lk) (by s2_lk) (by s2_lk)
  have := runFuel_prefix_some hpre hfin
  simpa using this

/-! ### The list-free arm's terminal runs -/

/-- **The plain span's end**: `if.then20`, `cleanup47` — two control steps, form `1`. -/
theorem s2StringBodyIfThen20_finishes {env : Env} {s : State} {len : BitVec 64}
    {outn ei : Nat}
    (hpc : s.pc = "if.then20")
    (hlen : lookupName env "%len" = some (.int 64 len))
    (houtn : lookupName env "%outn" = some (.ptr outn))
    (hei : lookupName env "%ei" = some (.ptr ei)) :
    runFuel s2StringBodyCalls 2 s2StringBodyBody (stateAt env s) =
      some (.ret (some (.int 32 0x00000001#32))
        (writeBytes s.mem outn (natToBytes len.toNat 8))) := by
  have h1 := step_ifThen20_cleanup47 hpc hlen houtn
  have hpre : ∀ k, runFuel s2StringBodyCalls (1 + k) s2StringBodyBody (stateAt env s) =
      runFuel s2StringBodyCalls k s2StringBodyBody
        (stateAt env { s with mem := writeBytes s.mem outn (natToBytes len.toNat 8), pc := "cleanup47", pre := some s.pc }) :=
    fun k => runFuel_jump_prefix h1 k
  have hfin : runFuel s2StringBodyCalls 1 s2StringBodyBody
      (stateAt env { s with mem := writeBytes s.mem outn (natToBytes len.toNat 8), pc := "cleanup47", pre := some s.pc }) =
      some (.ret (some (.int 32 0x00000001#32))
        (writeBytes s.mem outn (natToBytes len.toNat 8))) :=
    s2StringBodyCleanup47_finishes (env := env)
      (s := { s with mem := writeBytes s.mem outn (natToBytes len.toNat 8), pc := "cleanup47", pre := some s.pc })
      (p := "if.then20") (op := .imm (Const.int 32 0x00000001#32)) (form := 0x00000001#32)
      rfl (by rw [hpc]) (by simp [phiIncoming]) rfl hei
  simpa only [stateAt] using runFuel_prefix_some hpre hfin

set_option maxHeartbeats 4000000 in
/-- **The control record's end**: `if.then26`, `cleanup47` — two control steps,
form `0`. -/
theorem s2StringBodyIfThen26_finishes' {env : Env} {s : State} {c e ei : Nat}
    {off sub : BitVec 64}
    (hpc : s.pc = "if.then26")
    (hc : lookupName env "%c" = some (.ptr c))
    (hcall17 : lookupName env "%call17" = some (.int 64 off))
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hcval : readBytes s.mem (c + (1112#64).toNat) 8 = some (wordBytes 8 e))
    (he64 : e < 2 ^ 64)
    (hslot : lookupName (s2StringBodyIfThen26Env env off sub c e) "%ei"
      = some (.ptr ei)) :
    runFuel s2StringBodyCalls 2 s2StringBodyBody (stateAt env s) =
      some (.ret (some (.int 32 0x00000000#32))
        (s2StringBodyIfThen26Mem s.mem e off sub)) := by
  have h1 := step_ifThen26_cleanup47 hpc hc hcall17 hsub hcval he64
  have hpre : ∀ k, runFuel s2StringBodyCalls (1 + k) s2StringBodyBody (stateAt env s) =
      runFuel s2StringBodyCalls k s2StringBodyBody
        (stateAt (s2StringBodyIfThen26Env env off sub c e)
          { s with mem := s2StringBodyIfThen26Mem s.mem e off sub, pc := "cleanup47", pre := some s.pc }) :=
    fun k => runFuel_jump_prefix h1 k
  have hfin : runFuel s2StringBodyCalls 1 s2StringBodyBody
      (stateAt (s2StringBodyIfThen26Env env off sub c e)
        { s with mem := s2StringBodyIfThen26Mem s.mem e off sub, pc := "cleanup47", pre := some s.pc }) =
      some (.ret (some (.int 32 0x00000000#32))
        (s2StringBodyIfThen26Mem s.mem e off sub)) :=
    s2StringBodyCleanup47_finishes (env := s2StringBodyIfThen26Env env off sub c e)
      (s := { s with mem := s2StringBodyIfThen26Mem s.mem e off sub, pc := "cleanup47", pre := some s.pc })
      (p := "if.then26") (op := .imm (Const.int 32 0x00000000#32)) (form := 0x00000000#32)
      rfl (by rw [hpc]) (by simp [phiIncoming]) rfl hslot
  simpa using runFuel_prefix_some hpre hfin

set_option maxHeartbeats 4000000 in
/-- **The malformed record's end**: `if.then35`, `cleanup47` — two control steps,
form `0`. -/
theorem s2StringBodyIfThen35_finishes {env : Env} {s : State} {c ei e : Nat}
    {off sub rel : BitVec 64}
    (hpc : s.pc = "if.then35")
    (hc : lookupName env "%c" = some (.ptr c))
    (hei : lookupName env "%ei" = some (.ptr ei))
    (hcall17 : lookupName env "%call17" = some (.int 64 off))
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hrel : readBytes s.mem ei 8 = some (natToBytes rel.toNat 8))
    (hcval : readBytes s.mem (c + (1112#64).toNat) 8 = some (wordBytes 8 e))
    (he64 : e < 2 ^ 64)
    (hslot : lookupName (s2StringBodyIfThen35Env env off sub rel c e) "%ei"
      = some (.ptr ei)) :
    runFuel s2StringBodyCalls 2 s2StringBodyBody (stateAt env s) =
      some (.ret (some (.int 32 0x00000000#32))
        (s2StringBodyIfThen35Mem s.mem e (off + sub + rel))) := by
  have h1 := step_ifThen35_cleanup47 hpc hc hei hcall17 hsub hrel hcval he64
  have hpre : ∀ k, runFuel s2StringBodyCalls (1 + k) s2StringBodyBody (stateAt env s) =
      runFuel s2StringBodyCalls k s2StringBodyBody
        (stateAt (s2StringBodyIfThen35Env env off sub rel c e)
          { s with mem := s2StringBodyIfThen35Mem s.mem e (off + sub + rel), pc := "cleanup47", pre := some s.pc }) :=
    fun k => runFuel_jump_prefix h1 k
  have hfin : runFuel s2StringBodyCalls 1 s2StringBodyBody
      (stateAt (s2StringBodyIfThen35Env env off sub rel c e)
        { s with mem := s2StringBodyIfThen35Mem s.mem e (off + sub + rel), pc := "cleanup47", pre := some s.pc }) =
      some (.ret (some (.int 32 0x00000000#32))
        (s2StringBodyIfThen35Mem s.mem e (off + sub + rel))) :=
    s2StringBodyCleanup47_finishes (env := s2StringBodyIfThen35Env env off sub rel c e)
      (s := { s with mem := s2StringBodyIfThen35Mem s.mem e (off + sub + rel), pc := "cleanup47", pre := some s.pc })
      (p := "if.then35") (op := .imm (Const.int 32 0x00000000#32)) (form := 0x00000000#32)
      rfl (by rw [hpc]) (by simp [phiIncoming]) rfl hslot
  simpa using runFuel_prefix_some hpre hfin

/-- **The decoded length's end**: `if.end43`, `cleanup47` — two control steps,
form `2`. -/
theorem s2StringBodyIfEnd43_finishes {env : Env} {s : State} {call17 call32 : BitVec 64}
    {outn ei : Nat}
    (hpc : s.pc = "if.end43")
    (hcall32 : lookupName env "%call32" = some (.int 64 call32))
    (hcall17 : lookupName env "%call17" = some (.int 64 call17))
    (houtn : lookupName env "%outn" = some (.ptr outn))
    (hei : lookupName env "%ei" = some (.ptr ei)) :
    runFuel s2StringBodyCalls 2 s2StringBodyBody (stateAt env s) =
      some (.ret (some (.int 32 0x00000002#32))
        (writeBytes s.mem outn (natToBytes (call32 + call17).toNat 8))) := by
  have h1 := step_ifEnd43_cleanup47 hpc hcall32 hcall17 houtn
  have hpre : ∀ k, runFuel s2StringBodyCalls (1 + k) s2StringBodyBody (stateAt env s) =
      runFuel s2StringBodyCalls k s2StringBodyBody
        (stateAt (("%add44", .int 64 (call32 + call17)) :: env)
          { s with mem := writeBytes s.mem outn (natToBytes (call32 + call17).toNat 8), pc := "cleanup47", pre := some s.pc }) :=
    fun k => runFuel_jump_prefix h1 k
  have hfin : runFuel s2StringBodyCalls 1 s2StringBodyBody
      (stateAt (("%add44", .int 64 (call32 + call17)) :: env)
        { s with mem := writeBytes s.mem outn (natToBytes (call32 + call17).toNat 8), pc := "cleanup47", pre := some s.pc }) =
      some (.ret (some (.int 32 0x00000002#32))
        (writeBytes s.mem outn (natToBytes (call32 + call17).toNat 8))) :=
    s2StringBodyCleanup47_finishes (env := ("%add44", .int 64 (call32 + call17)) :: env)
      (s := { s with mem := writeBytes s.mem outn (natToBytes (call32 + call17).toNat 8), pc := "cleanup47", pre := some s.pc })
      (p := "if.end43") (op := .imm (Const.int 32 0x00000002#32)) (form := 0x00000002#32)
      rfl (by rw [hpc]) (by simp [phiIncoming]) rfl (by s2_lk)
  simpa using runFuel_prefix_some hpre hfin

end LeanLLVM.Refinement
