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

**The nine pin theorems are the block labels the `_at` shapes resolve to.**  Each
is `decide`, so a block whose instruction list moved fails here rather than inside
a step's proof. -/

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
        Term.condbr (.reg "%cmp3") "land.rhs" "if.then"⟩ := by decide

theorem s2StringBody_findBlock_land_rhs_at :
    s2StringBodyBody.findBlock "land.rhs" =
      some ⟨"land.rhs", s2StringBodyLandRhsInstrs,
        Term.condbr (.reg "%cmp1") "while.body" "land.lhs.true"⟩ := by decide

theorem s2StringBody_findBlock_while_body_at :
    s2StringBodyBody.findBlock "while.body" =
      some ⟨"while.body", s2StringBodyWhileBodyInstrs,
        Term.condbr (.reg "%exitcond.not") "if.then" "land.rhs"⟩ := by decide

theorem s2StringBody_findBlock_land_lhs_true_at :
    s2StringBodyBody.findBlock "land.lhs.true" =
      some ⟨"land.lhs.true", s2StringBodyLandLhsTrueInstrs,
        Term.condbr (.reg "%cmp7") "if.end" "if.then"⟩ := by decide

theorem s2StringBody_findBlock_if_then_at :
    s2StringBodyBody.findBlock "if.then" =
      some ⟨"if.then",
        [Instr.store (Ty.int 64) (Operand.reg "%len") (Operand.reg "%outn")],
        Term.br "cleanup16"⟩ := by decide

theorem s2StringBody_findBlock_if_end_at :
    s2StringBodyBody.findBlock "if.end" =
      some ⟨"if.end", s2StringBodyIfEndInstrs,
        Term.condbr (.reg "%cmp9") "if.then11" "if.end14"⟩ := by decide

theorem s2StringBody_findBlock_if_then11_at :
    s2StringBodyBody.findBlock "if.then11" =
      some ⟨"if.then11", s2StringBodyIfThen11Instrs, Term.br "cleanup"⟩ := by decide

theorem s2StringBody_findBlock_if_end14_at :
    s2StringBodyBody.findBlock "if.end14" =
      some ⟨"if.end14",
        [Instr.store (Ty.int 64) (Operand.reg "%call") (Operand.reg "%outn")],
        Term.br "cleanup"⟩ := by decide

theorem s2StringBody_findBlock_cleanup_at :
    s2StringBodyBody.findBlock "cleanup" =
      some ⟨"cleanup", s2StringBodyCleanupInstrs, Term.br "cleanup16"⟩ := by decide

theorem s2StringBody_findBlock_cleanup16_at :
    s2StringBodyBody.findBlock "cleanup16" =
      some ⟨"cleanup16", s2StringBodyCleanup16Instrs,
        Term.ret (Ty.int 32) (some (Operand.reg "%retval.1"))⟩ := by decide

/-- The entry block's environment after its seven instructions, named: the
allocator's first cell and the six the block builds over it. -/
def s2StringBodyEntryOut (env : Env) (next : Nat) (base p j0 : Nat)
    (nxp : BitVec 64) : Env :=
  s2StringBodyEnv7 (s2StringBodyEnv6 (s2StringBodyEnv5 (s2StringBodyEnv4
    (s2StringBodyEnv3 (s2StringBodyEnv2 (s2StringBodyEnv1 env next) base) p) base)
    p base) j0) j0 nxp

/-- The entry block's step, to the scan's head: the test holds. -/
theorem step_entry_landRhs {env : Env} {s : State} {c p xj base j0 : Nat}
    {nxp : BitVec 64}
    (hpc : s.pc = "entry")
    (hc : lookupName env "%c" = some (.ptr c))
    (hp : lookupName env "%p" = some (.ptr p))
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hbase : readBytes s.mem c 8 = some (wordBytes 8 base)) (hb64 : base < 2 ^ 64)
    (hp64 : p < 2 ^ 64)
    (hj0 : readBytes s.mem xj 8 = some (wordBytes 8 j0)) (hj64 : j0 < 2 ^ 64)
    (hbit : evalICmp .ult (BitVec.ofNat 64 j0) nxp = 1#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (s2StringBodyEntryOut env s.next base p j0 nxp)
        { s with next := s.next + (Ty.int 64).sizeBytes, pc := "land.rhs", pre := some s.pc }) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyEntryOut env s.next base p j0 nxp)
      { s with next := s.next + (Ty.int 64).sizeBytes })
    (b := ⟨"entry", s2StringBodyEntryInstrs,
      Term.condbr (.reg "%cmp3") "land.rhs" "if.then"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_entry_at
  · simpa only [denoteCode_nil, s2StringBodyEntryOut] using
      s2StringBody_entry_denote hc hp hxj hnxp hbase hb64 hp64 hj0 hj64
  · exact execTerm_condbr_one _ _ _ _ _ (by s2_lk) hbit

/-- The entry block's step, to the body-itself arm: the test fails. -/
theorem step_entry_ifThen {env : Env} {s : State} {c p xj base j0 : Nat}
    {nxp : BitVec 64}
    (hpc : s.pc = "entry")
    (hc : lookupName env "%c" = some (.ptr c))
    (hp : lookupName env "%p" = some (.ptr p))
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hbase : readBytes s.mem c 8 = some (wordBytes 8 base)) (hb64 : base < 2 ^ 64)
    (hp64 : p < 2 ^ 64)
    (hj0 : readBytes s.mem xj 8 = some (wordBytes 8 j0)) (hj64 : j0 < 2 ^ 64)
    (hbit : evalICmp .ult (BitVec.ofNat 64 j0) nxp = 0#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (s2StringBodyEntryOut env s.next base p j0 nxp)
        { s with next := s.next + (Ty.int 64).sizeBytes, pc := "if.then", pre := some s.pc }) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyEntryOut env s.next base p j0 nxp)
      { s with next := s.next + (Ty.int 64).sizeBytes })
    (b := ⟨"entry", s2StringBodyEntryInstrs,
      Term.condbr (.reg "%cmp3") "land.rhs" "if.then"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_entry_at
  · simpa only [denoteCode_nil, s2StringBodyEntryOut] using
      s2StringBody_entry_denote hc hp hxj hnxp hbase hb64 hp64 hj0 hj64
  · exact execTerm_condbr_zero _ _ _ _ _ (by s2_lk) hbit

/-- The scan's head, while the lane is still below the body: one control step to
`while.body`. -/
theorem step_landRhs_while {env : Env} {s : State} {p : String} {op : Operand}
    {inc24 : BitVec 64} {xp : Nat} {bs : List UInt8} {sub : BitVec 64}
    (hpc : s.pc = "land.rhs") (hpre : s.pre = some p)
    (hinc : phiIncoming p [("while.body", Operand.reg "%inc"),
      ("entry", Operand.reg "%xj.promoted")] = some op)
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
      ("entry", Operand.reg "%xj.promoted")] = some op)
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
      Term.condbr (.reg "%exitcond.not") "if.then" "land.rhs"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_while_body_at
  · simpa only [denoteCode_nil] using s2StringBody_whileBody_denote hinc24 hxj hnxp
  · exact execTerm_condbr_zero _ _ _ _ _ (by s2_lk) hbit

/-- The scan's body, the counter at the count: one control step to `if.then`, the
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
        ({ s with mem := writeBytes s.mem xj (natToBytes (inc24 + 1#64).toNat 8), pc := "if.then", pre := some s.pc })) := by
  refine step_at_block
    (s' := stateAt
      (("%exitcond.not", .int 1 (evalICmp .eq (inc24 + 1#64) nxp)) ::
        ("%inc", .int 64 (inc24 + 1#64)) :: env)
      { s with mem := writeBytes s.mem xj (natToBytes (inc24 + 1#64).toNat 8) })
    (b := ⟨"while.body", s2StringBodyWhileBodyInstrs,
      Term.condbr (.reg "%exitcond.not") "if.then" "land.rhs"⟩) ?_ ?_ ?_
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
      Term.condbr (.reg "%cmp7") "if.end" "if.then"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_land_lhs_true_at
  · simpa only [denoteCode_nil] using s2StringBody_landLhsTrue_denote hsub hlen hconv
  · exact execTerm_condbr_one _ _ _ _ _ (by s2_lk) hbit

/-- The inside test, the lane inside the body: one control step to `if.then`. -/
theorem step_landLhsTrue_ifThen {env : Env} {s : State} {sub len conv : BitVec 64}
    (hpc : s.pc = "land.lhs.true")
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hlen : lookupName env "%len" = some (.int 64 len))
    (hconv : lookupName env "%conv" = some (.int 64 conv))
    (hbit : evalICmpNat .ugt 64 (sub + len).toNat conv.toNat = 0#1) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt
        (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
          ("%add", .int 64 (sub + len)) :: env)
        { s with pc := "if.then", pre := some s.pc }) := by
  refine step_at_block
    (s' := stateAt
      (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
        ("%add", .int 64 (sub + len)) :: env) s)
    (b := ⟨"land.lhs.true", s2StringBodyLandLhsTrueInstrs,
      Term.condbr (.reg "%cmp7") "if.end" "if.then"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_land_lhs_true_at
  · simpa only [denoteCode_nil] using s2StringBody_landLhsTrue_denote hsub hlen hconv
  · exact execTerm_condbr_zero _ _ _ _ _ (by s2_lk) hbit

/-- The body-itself arm's step: the extent's word at `outn`, then `cleanup16`. -/
theorem step_ifThen_cleanup16 {env : Env} {s : State} {len : BitVec 64} {outn : Nat}
    (hpc : s.pc = "if.then")
    (hlen : lookupName env "%len" = some (.int 64 len))
    (houtn : lookupName env "%outn" = some (.ptr outn)) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt env
        ({ s with mem := writeBytes s.mem outn (natToBytes len.toNat 8), pc := "cleanup16", pre := some s.pc })) := by
  refine step_at_block
    (s' := stateAt env { s with mem := writeBytes s.mem outn (natToBytes len.toNat 8) })
    (b := ⟨"if.then",
      [Instr.store (Ty.int 64) (Operand.reg "%len") (Operand.reg "%outn")],
      Term.br "cleanup16"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_if_then_at
  · simpa only [denoteCode_nil] using s2StringBody_ifThen_denote hlen houtn
  · rfl

/-- The expander's step, its answer all-ones: one control step to the refusal
record. -/
theorem step_ifEnd_ifThen11 {env : Env} {s : State}
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
        ({ s with mem := m, next := nx, pc := "if.then11", pre := some s.pc })) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyIfEndEnv env call) { s with mem := m, next := nx })
    (b := ⟨"if.end", s2StringBodyIfEndInstrs,
      Term.condbr (.reg "%cmp9") "if.then11" "if.end14"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_if_end_at
  · simpa only [denoteCode_nil] using
      s2StringBody_ifEnd_denote hp hlen hdst hei hxp hxj hnxp hsub hc
  · exact execTerm_condbr_one _ _ _ _ _ (by s2_lk) hbit

/-- The expander's step, an answer that is not all-ones: one control step to the
decoded length's write. -/
theorem step_ifEnd_ifEnd14 {env : Env} {s : State}
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
        ({ s with mem := m, next := nx, pc := "if.end14", pre := some s.pc })) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyIfEndEnv env call) { s with mem := m, next := nx })
    (b := ⟨"if.end", s2StringBodyIfEndInstrs,
      Term.condbr (.reg "%cmp9") "if.then11" "if.end14"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_if_end_at
  · simpa only [denoteCode_nil] using
      s2StringBody_ifEnd_denote hp hlen hdst hei hxp hxj hnxp hsub hc
  · exact execTerm_condbr_zero _ _ _ _ _ (by s2_lk) hbit

set_option maxHeartbeats 1000000 in
/-- The refusal record's step: the three fields written, then `cleanup`. -/
theorem step_ifThen11_cleanup {env : Env} {s : State} {c ei e : Nat} {off sub : BitVec 64}
    (hpc : s.pc = "if.then11")
    (hc : lookupName env "%c" = some (.ptr c))
    (hei : lookupName env "%ei" = some (.ptr ei))
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hoff : readBytes s.mem ei 8 = some (natToBytes off.toNat 8))
    (hcval : readBytes s.mem (c + (1112#64).toNat) 8 = some (wordBytes 8 e))
    (he64 : e < 2 ^ 64) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (s2StringBodyIfThen11Env env off sub c e)
        ({ s with mem := s2StringBodyIfThen11Mem s.mem e off sub, pc := "cleanup", pre := some s.pc })) := by
  refine step_at_block
    (s' := stateAt (s2StringBodyIfThen11Env env off sub c e)
      { s with mem := s2StringBodyIfThen11Mem s.mem e off sub })
    (b := ⟨"if.then11", s2StringBodyIfThen11Instrs, Term.br "cleanup"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_if_then11_at
  · simpa only [denoteCode_nil] using
      s2StringBody_ifThen11_denote hc hei hsub hoff hcval he64
  · rfl

/-- The decoded length's step at `outn`, then `cleanup`. -/
theorem step_ifEnd14_cleanup {env : Env} {s : State} {call : BitVec 64} {outn : Nat}
    (hpc : s.pc = "if.end14")
    (hcall : lookupName env "%call" = some (.int 64 call))
    (houtn : lookupName env "%outn" = some (.ptr outn)) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt env
        ({ s with mem := writeBytes s.mem outn (natToBytes call.toNat 8), pc := "cleanup", pre := some s.pc })) := by
  refine step_at_block
    (s' := stateAt env { s with mem := writeBytes s.mem outn (natToBytes call.toNat 8) })
    (b := ⟨"if.end14",
      [Instr.store (Ty.int 64) (Operand.reg "%call") (Operand.reg "%outn")],
      Term.br "cleanup"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_if_end14_at
  · simpa only [denoteCode_nil] using s2StringBody_ifEnd14_denote hcall houtn
  · rfl

/-- The first cleanup block's step: the form's `phi`, then `cleanup16`. -/
theorem step_cleanup_cleanup16 {env : Env} {s : State} {p : String} {op : Operand}
    {form : BitVec 32} {ei : Nat}
    (hpc : s.pc = "cleanup") (hpre : s.pre = some p)
    (hinc : phiIncoming p [("if.then11", Operand.imm (Const.int 32 0x00000000#32)),
      ("if.end14", Operand.imm (Const.int 32 0x00000002#32))] = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 32 form))
    (hei : lookupName env "%ei" = some (.ptr ei)) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.jump (stateAt (("%retval.0", .int 32 form) :: env)
        { s with pc := "cleanup16", pre := some s.pc }) := by
  refine step_at_block
    (s' := stateAt (("%retval.0", .int 32 form) :: env) s)
    (b := ⟨"cleanup", s2StringBodyCleanupInstrs, Term.br "cleanup16"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_cleanup_at
  · simpa only [denoteCode_nil] using s2StringBody_cleanup_denote hpre hinc hop hei
  · rfl

/-- The second cleanup block's step: the returned form, and the function's
answer.  The `i32` the `phi` selects is what `execTerm` reads, so the terminator is
a `ret` of that word, not of the register. -/
theorem step_cleanup16_ret {env : Env} {s : State} {p : String} {op : Operand}
    {form : BitVec 32}
    (hpc : s.pc = "cleanup16") (hpre : s.pre = some p)
    (hinc : phiIncoming p [("cleanup", Operand.reg "%retval.0"),
      ("if.then", Operand.imm (Const.int 32 0x00000001#32))] = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 32 form)) :
    step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      Ctrl.ret (some (.int 32 form)) (stateAt (("%retval.1", .int 32 form) :: env) s) := by
  refine step_at_block
    (s' := stateAt (("%retval.1", .int 32 form) :: env) s)
    (b := ⟨"cleanup16", s2StringBodyCleanup16Instrs,
      Term.ret (Ty.int 32) (some (Operand.reg "%retval.1"))⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using s2StringBody_findBlock_cleanup16_at
  · simpa only [denoteCode_nil] using s2StringBody_cleanup16_denote hpre hinc hop
  · have hv : evalOperand (stateAt (("%retval.1", .int 32 form) :: env) s)
        (.reg "%retval.1") = some (.int 32 form) := by s2_lk
    simp only [execTerm, hv]


/-- The scan's cursor word after one iteration: the word written where the cursor's
own word stands replaces it in place, so the head's memory is the caller's with the
cursor at the new counter.  This is `writeBytes_writeBytes_same` at `(xj, 8)`, and
`hc64` is what makes the counter's increment not wrap. -/
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

/-- **The scan's iteration**: two control steps from the head back to the head, the
counter's word written where it stands.  The two steps are the block steps composed
through `runFuel_jump_prefix`, so the cost this loop's instance names is `2` and the
state it returns is the next head, at `(r, c + 1)` in the invariant's terms. -/
theorem s2StringBodyScanIterate {envH : Env} {s : State} {p : String} {op : Operand}
    {inc24 nxp : BitVec 64} {xp xj : Nat} {bs : List UInt8} {sub : BitVec 64}
    (hpc : s.pc = "land.rhs") (hpre : s.pre = some p)
    (hxj : lookupName envH "%xj" = some (.ptr xj))
    (hnxp : lookupName envH "%nxp" = some (.int 64 nxp))
    (hinc : phiIncoming p [("while.body", Operand.reg "%inc"),
      ("entry", Operand.reg "%xj.promoted")] = some op)
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

/-- **The scan's first exit**: one control step to `land.lhs.true`, the lane already
inside the body, the memory as the head left it. -/
theorem s2StringBodyScanExit {envH : Env} {s : State} {p : String} {op : Operand}
    {inc24 : BitVec 64} {xp : Nat} {bs : List UInt8} {sub : BitVec 64}
    (hpc : s.pc = "land.rhs") (hpre : s.pre = some p)
    (hinc : phiIncoming p [("while.body", Operand.reg "%inc"),
      ("entry", Operand.reg "%xj.promoted")] = some op)
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

/-- **The scan's back edge.**  One iteration is two control steps (`cost = 2`):
the head's step advances, `while.body` writes the counter and returns to the head.
Every clause of the invariant is re-established — the `phi`'s edge is `while.body`
and its operand `%inc` now reads `c + 1`, the four registers are still the outer
cells, the cursor word is the new counter (`s2StringBodyScan_advance`, which is
where the write order matters), and the lane at `c + 1` is the model's entry there
(`readLanes32_lane`), read past the cursor's write by the region's disjointness. -/
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


/-- **The scan's iteration, leaving.**  The same two control steps as
`s2StringBodyScanIterate`, but the counter has reached the count, so `while.body`'s
test holds and the scan leaves for `if.then`. -/
theorem s2StringBodyScanIterateExit {envH : Env} {s : State} {p : String} {op : Operand}
    {inc24 nxp : BitVec 64} {xp xj : Nat} {bs : List UInt8} {sub : BitVec 64}
    (hpc : s.pc = "land.rhs") (hpre : s.pre = some p)
    (hxj : lookupName envH "%xj" = some (.ptr xj))
    (hnxp : lookupName envH "%nxp" = some (.int 64 nxp))
    (hinc : phiIncoming p [("while.body", Operand.reg "%inc"),
      ("entry", Operand.reg "%xj.promoted")] = some op)
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
          ({ s with mem := writeBytes s.mem xj (natToBytes (inc24 + 1#64).toNat 8), pc := "if.then", pre := some "while.body" })) := by
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
            ({ s with mem := writeBytes s.mem xj (natToBytes (inc24 + 1#64).toNat 8), pc := "if.then", pre := some "while.body" })) :=
        runFuel_jump_prefix h2 k

/-- The blocks the scan may leave for. -/
def s2StringBodyScanExited (e : State) : Prop :=
  e.pc = "land.lhs.true" ∨ e.pc = "if.then"

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
  · -- the lane is already inside the body: the head's exit, one step
    have hbit : evalICmpNat .ugt 64 (BitVec.ofNat 64 pos0).toNat
        (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat).toNat = 0#1 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpos0, hconv]
      exact evalICmpNat_ugt_of_ge hpos0 (by have := bytesToNat_lt_32 hblen; omega) hge
    have hrun := s2StringBodyScanExit (envH := s.env) (s := s) (p := p) (op := op)
      hpc hpre hinc hop hxp hsub hpos hlane' hbit
    let e : State := stateAt (s2StringBodyLandRhsEnv s.env (BitVec.ofNat 64 c) xp bs
        (BitVec.ofNat 64 pos0)) { s with pc := "land.lhs.true", pre := some s.pc }
    refine ⟨e, 1, by decide, Or.inl rfl, ?_, hrun⟩
    exact ⟨c, by simp only [e, stateAt]; exact hmem, Or.inr ⟨q, hq, hge⟩⟩
  · -- the lane is below the body's start, so only the count can have stopped it
    have hlt : q < pos0 := by omega
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
        ({ s with mem := writeBytes s.mem xj (natToBytes ((BitVec.ofNat 64 c) + 1#64).toNat 8), pc := "if.then", pre := some "while.body" })
    refine ⟨e, 2, le_rfl, Or.inr rfl, ?_, hrun⟩
    refine ⟨c + 1, ?_, Or.inl (by omega)⟩
    simp only [e, stateAt]
    rw [show (writeBytes s.mem xj (natToBytes ((BitVec.ofNat 64 c) + 1#64).toNat 8))
        = writeBytes mem0 xj (wordBytes 8 (c + 1)) from
      s2StringBodyScan_advance mem0 xj c s hmem (by omega)]


/-- **The scan, as a `BoundLoop`.**  The two arms are proved, so the value carries no
hypothesis beyond the staging's: the lane list, the region disjointness the frame
needs, and the two bounds.  The exits are `land.lhs.true` and `if.then`, and the
exit word is the cursor at the counter the scan stopped at. -/
def s2StringBodyScanLoop (mem0 : Mem) (xj pos0 xp N : Nat) (ps : List Nat)
    (hps : readLanes32 mem0 xp N = some ps)
    (hdisj : ∀ k, k < N → xp + 4 * k + 4 ≤ xj ∨ xj + 8 ≤ xp + 4 * k)
    (hN : N < 2 ^ 63) (hpos0 : pos0 < 2 ^ 64) :
    BoundLoop s2StringBodyCalls s2StringBodyBody :=
  s2StringBodyScanBoundLoop mem0 xj pos0 xp N ps 2
    s2StringBodyScanExited (s2StringBodyScanExitWord mem0 xj ps pos0 N)
    (s2StringBodyScan_step_exit mem0 xj pos0 xp N ps hps hdisj hN hpos0)
    (s2StringBodyScan_step_loop mem0 xj pos0 xp N ps hps hdisj hN hpos0)

/-- **The scan's fuel, read off its instance**: `(N + 1) * 2` control steps from the
head, and the exit's continuation at its own fuel. -/
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
  (s2StringBodyScanLoop mem0 xj pos0 xp N ps hps hdisj hN hpos0).run_at s c hinv k hcont


/-! ### The entry's prefix

The body's run starts here: the entry block's step, stated as the `runFuel` prefix
the closing composes with (`s2StringBodyScan_run` for the scan, and the exit
continuations for the rest).  The *seating* — reading `s2StringBodyScanInv` off the
staging at the head the entry leaves — is not stated here, and its first clause is
why: the invariant wants `s.mem = writeBytes s.mem xj (wordBytes 8 j0)`, which is
the self-write form of a region already present.  That is the presence clause
`s2StringBodyPre` still owes (obligation 3), so the seating belongs with it rather
than ahead of it. -/

/-- `ofNat` at `i64` is a homomorphism for subtraction when the operands do not
borrow: `(p - base)` as the model's `Nat` is the bit-vector difference. -/
theorem ofNat_sub (p base : Nat) (hb : base ≤ p) (hp : p < 2 ^ 64) :
    (BitVec.ofNat 64 p) - (BitVec.ofNat 64 base) = BitVec.ofNat 64 (p - base) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- **The entry's step to the scan's head, as a prefix**: one control step, and the
run continues from the head at `land.rhs`. -/
theorem s2StringBodyEntry_prefix_landRhs {env : Env} {s : State}
    {c p xj base j0 : Nat} {nxp : BitVec 64}
    (hpc : s.pc = "entry")
    (hc : lookupName env "%c" = some (.ptr c))
    (hp : lookupName env "%p" = some (.ptr p))
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hbase : readBytes s.mem c 8 = some (wordBytes 8 base)) (hb64 : base < 2 ^ 64)
    (hp64 : p < 2 ^ 64)
    (hj0 : readBytes s.mem xj 8 = some (wordBytes 8 j0)) (hj64 : j0 < 2 ^ 64)
    (hbit : evalICmp .ult (BitVec.ofNat 64 j0) nxp = 1#1) :
    ∀ k, runFuel s2StringBodyCalls (1 + k) s2StringBodyBody (stateAt env s) =
      runFuel s2StringBodyCalls k s2StringBodyBody
        (stateAt (s2StringBodyEntryOut env s.next base p j0 nxp)
          ({ s with next := s.next + (Ty.int 64).sizeBytes, pc := "land.rhs", pre := some s.pc })) := by
  intro k
  exact runFuel_jump_prefix
    (step_entry_landRhs hpc hc hp hxj hnxp hbase hb64 hp64 hj0 hj64 hbit) k

/-- **The entry's step to the body-itself arm, as a prefix.** -/
theorem s2StringBodyEntry_prefix_ifThen {env : Env} {s : State}
    {c p xj base j0 : Nat} {nxp : BitVec 64}
    (hpc : s.pc = "entry")
    (hc : lookupName env "%c" = some (.ptr c))
    (hp : lookupName env "%p" = some (.ptr p))
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hbase : readBytes s.mem c 8 = some (wordBytes 8 base)) (hb64 : base < 2 ^ 64)
    (hp64 : p < 2 ^ 64)
    (hj0 : readBytes s.mem xj 8 = some (wordBytes 8 j0)) (hj64 : j0 < 2 ^ 64)
    (hbit : evalICmp .ult (BitVec.ofNat 64 j0) nxp = 0#1) :
    ∀ k, runFuel s2StringBodyCalls (1 + k) s2StringBodyBody (stateAt env s) =
      runFuel s2StringBodyCalls k s2StringBodyBody
        (stateAt (s2StringBodyEntryOut env s.next base p j0 nxp)
          ({ s with next := s.next + (Ty.int 64).sizeBytes, pc := "if.then", pre := some s.pc })) := by
  intro k
  exact runFuel_jump_prefix
    (step_entry_ifThen hpc hc hp hxj hnxp hbase hb64 hp64 hj0 hj64 hbit) k



/-- **Seating the scan's invariant at the head the entry left.**  Every clause is
read off the staging: the entry writes nothing, so its memory is the caller's and
the cursor word's presence (`stage2ReadWord_writeBytes_self`) is the invariant's
memory clause; the `phi`'s edge is `entry` selecting `%xj.promoted`, which the entry
has just bound to `j0`; `%xp`, `%xj` and `%nxp` are the caller's registers, falling
through the entry's seven cells; `%sub.ptr.sub` is `p - base` (`ofNat_sub`); and the
lane at `j0` is the model's, because the head's memory is the caller's. -/
theorem s2StringBodyScanInv_seat (env : Env) (s : State) (base p xj xp j0 : Nat)
    (ps : List Nat) (nxp : BitVec 64)
    (hpc : s.pc = "entry")
    (hbase : base ≤ p) (hp64 : p < 2 ^ 64)
    (hword : stage2ReadWord s.mem xj 8 = some j0)
    (hps : readLanes32 s.mem xp nxp.toNat = some ps)
    (hj0 : j0 < nxp.toNat)
    (hxpc : lookupName env "%xp" = some (.ptr xp))
    (hxjc : lookupName env "%xj" = some (.ptr xj))
    (hnxpc : lookupName env "%nxp" = some (.int 64 nxp)) :
    s2StringBodyScanInv s.mem xj (p - base) xp nxp.toNat ps (nxp.toNat - j0)
      (stateAt (s2StringBodyEntryOut env s.next base p j0 nxp)
        { s with next := s.next + (Ty.int 64).sizeBytes, pc := "land.rhs", pre := some s.pc })
      j0 := by
  obtain ⟨q, bs, hq, hlaneM, hval⟩ := (readLanes32_lane hps).2 j0 hj0
  have hblen : bs.length = 4 := readBytes_length_some hlaneM
  have hpres := stage2ReadWord_writeBytes_self s.mem xj 8 j0 hword
  have hnxp : BitVec.ofNat 64 nxp.toNat = nxp := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt nxp.isLt]
  refine ⟨rfl, ?_, by omega, ?_, ?_, ?_, ?_, ?_, ⟨q, bs, hq, hblen, hval, ?_⟩⟩
  · simpa only [stateAt] using hpres.symm
  · refine ⟨"entry", Operand.reg "%xj.promoted", ?_, by simp [phiIncoming], ?_⟩
    · simp only [stateAt, hpc]
    · simp [stateAt, evalOperand, lookupName, s2StringBodyEntryOut,
        s2StringBodyEnv7, s2StringBodyEnv6]
  · simp [stateAt, lookupName, s2StringBodyEntryOut, s2StringBodyEnv7,
      s2StringBodyEnv6, s2StringBodyEnv5, s2StringBodyEnv4, s2StringBodyEnv3,
      s2StringBodyEnv2, s2StringBodyEnv1, hxpc]
  · simp [stateAt, lookupName, s2StringBodyEntryOut, s2StringBodyEnv7,
      s2StringBodyEnv6, s2StringBodyEnv5, s2StringBodyEnv4, s2StringBodyEnv3,
      s2StringBodyEnv2, s2StringBodyEnv1, ofNat_sub p base hbase hp64]
  · simp [stateAt, lookupName, s2StringBodyEntryOut, s2StringBodyEnv7,
      s2StringBodyEnv6, s2StringBodyEnv5, s2StringBodyEnv4, s2StringBodyEnv3,
      s2StringBodyEnv2, s2StringBodyEnv1, hxjc]
  · simp [stateAt, lookupName, s2StringBodyEntryOut, s2StringBodyEnv7,
      s2StringBodyEnv6, s2StringBodyEnv5, s2StringBodyEnv4, s2StringBodyEnv3,
      s2StringBodyEnv2, s2StringBodyEnv1, hnxp, hnxpc]
  · simp only [stateAt]
    exact hlaneM


/-! ### The end of the run

Two blocks finish the body — `cleanup16` returns the form, and `if.then` writes the
extent's word before it — and both are `ret`s rather than jumps, so the run ends at
them (`runFuel` maps a `ret` step to the outcome, dropping the state).  These are
the continuations' last link: every path reaches `cleanup16` at some form, and the
form is the `phi`'s answer from whichever cleanup block preceded it. -/

/-- A `ret` step completes the run: the outcome carries the returned word and the
memory the block left. -/
theorem runFuel_ret_mem {calls : Calls} {f : Function} {s s' : State} {v : Value}
    (h : step calls f s = .ret (some v) s') (k : Nat) :
    runFuel calls (1 + k) f s = some (.ret (some v) s'.mem) := by
  rw [show 1 + k = k + 1 from by omega]
  simp only [runFuel, h]

/-- **`cleanup16` finishes the body**: the returned form's `phi` and the function's
answer at that word, one control step. -/
theorem s2StringBodyCleanup16_finishes {env : Env} {s : State} {p : String}
    {op : Operand} {form : BitVec 32}
    (hpc : s.pc = "cleanup16") (hpre : s.pre = some p)
    (hinc : phiIncoming p [("cleanup", Operand.reg "%retval.0"),
      ("if.then", Operand.imm (Const.int 32 0x00000001#32))] = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 32 form)) :
    runFuel s2StringBodyCalls 1 s2StringBodyBody (stateAt env s) =
      some (.ret (some (.int 32 form))
        (stateAt (("%retval.1", .int 32 form) :: env) s).mem) :=
  runFuel_ret_mem (step_cleanup16_ret hpc hpre hinc hop) 0

/-- **The body-itself arm's end**: `if.then` writes the extent's word at `outn`,
`cleanup16` returns `1`, and the run is over in two control steps. -/
theorem s2StringBodyIfThen_finishes {env : Env} {s : State} {len : BitVec 64}
    {outn : Nat}
    (hpc : s.pc = "if.then")
    (hlen : lookupName env "%len" = some (.int 64 len))
    (houtn : lookupName env "%outn" = some (.ptr outn)) :
    runFuel s2StringBodyCalls 2 s2StringBodyBody (stateAt env s) =
      some (.ret (some (.int 32 0x00000001#32))
        (writeBytes s.mem outn (natToBytes len.toNat 8))) := by
  have h1 := step_ifThen_cleanup16 hpc hlen houtn
  have h2 : step s2StringBodyCalls s2StringBodyBody
      (stateAt env { s with mem := writeBytes s.mem outn (natToBytes len.toNat 8), pc := "cleanup16", pre := some s.pc }) =
      .ret (some (.int 32 0x00000001#32))
        (stateAt (("%retval.1", .int 32 0x00000001#32) :: env)
          { s with mem := writeBytes s.mem outn (natToBytes len.toNat 8), pc := "cleanup16", pre := some s.pc }) := by
    refine step_cleanup16_ret (p := "if.then")
      (op := .imm (Const.int 32 0x00000001#32)) rfl ?_ ?_ rfl
    · rw [hpc]
    · simp [phiIncoming]
  have hpre : ∀ k, runFuel s2StringBodyCalls (1 + k) s2StringBodyBody (stateAt env s) =
      runFuel s2StringBodyCalls k s2StringBodyBody
        (stateAt env { s with mem := writeBytes s.mem outn (natToBytes len.toNat 8), pc := "cleanup16", pre := some s.pc }) :=
    fun k => runFuel_jump_prefix h1 k
  have hcont : runFuel s2StringBodyCalls 1 s2StringBodyBody
      (stateAt env { s with mem := writeBytes s.mem outn (natToBytes len.toNat 8), pc := "cleanup16", pre := some s.pc }) =
      some (.ret (some (.int 32 0x00000001#32))
        (stateAt (("%retval.1", .int 32 0x00000001#32) :: env)
          { s with mem := writeBytes s.mem outn (natToBytes len.toNat 8), pc := "cleanup16", pre := some s.pc }).mem) :=
    runFuel_ret_mem h2 0
  simpa only [stateAt] using runFuel_prefix_some hpre hcont


/-- **`cleanup` finishes, having come from the refusal**: its `phi` selects `0`,
`cleanup16` returns `%retval.0`, and the run is over in two control steps. -/
theorem s2StringBodyCleanup_fromRefused_finishes {env : Env} {s : State} {ei : Nat}
    (hpc : s.pc = "cleanup") (hpre : s.pre = some "if.then11")
    (hei : lookupName env "%ei" = some (.ptr ei)) :
    runFuel s2StringBodyCalls 2 s2StringBodyBody (stateAt env s) =
      some (.ret (some (.int 32 0x00000000#32)) s.mem) := by
  have hstep : step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      .jump (stateAt (("%retval.0", .int 32 0x00000000#32) :: env)
        { s with pc := "cleanup16", pre := some s.pc }) :=
    step_cleanup_cleanup16 (env := env) (s := s) (p := "if.then11")
      (op := .imm (Const.int 32 0x00000000#32)) hpc hpre (by simp [phiIncoming]) rfl hei
  have hfin : runFuel s2StringBodyCalls 1 s2StringBodyBody
      (stateAt (("%retval.0", .int 32 0x00000000#32) :: env)
        { s with pc := "cleanup16", pre := some s.pc }) =
      some (.ret (some (.int 32 0x00000000#32)) s.mem) := by
    have h := s2StringBodyCleanup16_finishes (env := ("%retval.0", .int 32 0x00000000#32) :: env)
      (s := { s with pc := "cleanup16", pre := some s.pc }) (p := "cleanup")
      (op := .reg "%retval.0") (form := 0x00000000#32) rfl (by rw [hpc])
      (by simp [phiIncoming]) (by s2_lk)
    simpa only [stateAt] using h
  exact runFuel_prefix_some (fun k => runFuel_jump_prefix hstep k) hfin

/-- **`cleanup` finishes, having come from the decoded arm**: its `phi` selects `2`. -/
theorem s2StringBodyCleanup_fromDecoded_finishes {env : Env} {s : State} {ei : Nat}
    (hpc : s.pc = "cleanup") (hpre : s.pre = some "if.end14")
    (hei : lookupName env "%ei" = some (.ptr ei)) :
    runFuel s2StringBodyCalls 2 s2StringBodyBody (stateAt env s) =
      some (.ret (some (.int 32 0x00000002#32)) s.mem) := by
  have hstep : step s2StringBodyCalls s2StringBodyBody (stateAt env s) =
      .jump (stateAt (("%retval.0", .int 32 0x00000002#32) :: env)
        { s with pc := "cleanup16", pre := some s.pc }) :=
    step_cleanup_cleanup16 (env := env) (s := s) (p := "if.end14")
      (op := .imm (Const.int 32 0x00000002#32)) hpc hpre (by simp [phiIncoming]) rfl hei
  have hfin : runFuel s2StringBodyCalls 1 s2StringBodyBody
      (stateAt (("%retval.0", .int 32 0x00000002#32) :: env)
        { s with pc := "cleanup16", pre := some s.pc }) =
      some (.ret (some (.int 32 0x00000002#32)) s.mem) := by
    have h := s2StringBodyCleanup16_finishes (env := ("%retval.0", .int 32 0x00000002#32) :: env)
      (s := { s with pc := "cleanup16", pre := some s.pc }) (p := "cleanup")
      (op := .reg "%retval.0") (form := 0x00000002#32) rfl (by rw [hpc])
      (by simp [phiIncoming]) (by s2_lk)
    simpa only [stateAt] using h
  exact runFuel_prefix_some (fun k => runFuel_jump_prefix hstep k) hfin


/-- **The decoded length's path finishes**: the word at `outn`, `cleanup`'s decoded
form, and the run is over in three control steps. -/
theorem s2StringBodyIfEnd14_finishes {env : Env} {s : State} {call : BitVec 64}
    {outn ei : Nat}
    (hpc : s.pc = "if.end14")
    (hcall : lookupName env "%call" = some (.int 64 call))
    (houtn : lookupName env "%outn" = some (.ptr outn))
    (hei : lookupName env "%ei" = some (.ptr ei)) :
    runFuel s2StringBodyCalls 3 s2StringBodyBody (stateAt env s) =
      some (.ret (some (.int 32 0x00000002#32))
        (writeBytes s.mem outn (natToBytes call.toNat 8))) := by
  have hstep := step_ifEnd14_cleanup hpc hcall houtn
  have hfin : runFuel s2StringBodyCalls 2 s2StringBodyBody
      (stateAt env { s with mem := writeBytes s.mem outn (natToBytes call.toNat 8), pc := "cleanup", pre := some s.pc }) =
      some (.ret (some (.int 32 0x00000002#32))
        (writeBytes s.mem outn (natToBytes call.toNat 8))) :=
    s2StringBodyCleanup_fromDecoded_finishes (env := env)
      (s := { s with mem := writeBytes s.mem outn (natToBytes call.toNat 8), pc := "cleanup", pre := some s.pc })
      rfl (by rw [hpc]) hei
  have := runFuel_prefix_some (fun k => runFuel_jump_prefix hstep k) hfin
  simpa using this

/-- **The inside test finishing at the body-itself arm**: one step to `if.then`,
then the arm's two — three control steps, form `1`. -/
theorem s2StringBodyLandLhsTrue_toIfThen_finishes {env : Env} {s : State}
    {sub len conv : BitVec 64} {outn : Nat}
    (hpc : s.pc = "land.lhs.true")
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hlen : lookupName env "%len" = some (.int 64 len))
    (hconv : lookupName env "%conv" = some (.int 64 conv))
    (hbit : evalICmpNat .ugt 64 (sub + len).toNat conv.toNat = 0#1)
    (houtn : lookupName env "%outn" = some (.ptr outn)) :
    runFuel s2StringBodyCalls 3 s2StringBodyBody (stateAt env s) =
      some (.ret (some (.int 32 0x00000001#32))
        (writeBytes s.mem outn (natToBytes len.toNat 8))) := by
  have hstep := step_landLhsTrue_ifThen hpc hsub hlen hconv hbit
  have hfin : runFuel s2StringBodyCalls 2 s2StringBodyBody
      (stateAt (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
        ("%add", .int 64 (sub + len)) :: env)
        { s with pc := "if.then", pre := some s.pc }) =
      some (.ret (some (.int 32 0x00000001#32))
        (writeBytes s.mem outn (natToBytes len.toNat 8))) :=
    s2StringBodyIfThen_finishes (env := ("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
        ("%add", .int 64 (sub + len)) :: env)
      (s := { s with pc := "if.then", pre := some s.pc }) rfl (by s2_lk) (by s2_lk)
  have := runFuel_prefix_some (fun k => runFuel_jump_prefix hstep k) hfin
  simpa using this


/-- The refusal record's output state, named: the record's three fields written over
the caller's memory, at `cleanup`.  Rule four's failure mode is why this exists:
stated inline, the nine-cell environment is a `whnf` liability the elaborator pays
at every unification, and the proof dies in `whnf` — *not* in logic — at the
default budget and again at a million heartbeats.  Naming the state is necessary
but was measured **not** sufficient for the refusal path: the cost that remains is
the instantiation of a completion lemma at this environment, so a path stated here
still wants its completion proved over a state variable (no `s2StringBodyIfThen11Mem`
in the type) rather than at this term. -/
def s2StringBodyIfThen11Out (env : Env) (s : State) (off sub : BitVec 64) (c e : Nat) :
    State :=
  stateAt (s2StringBodyIfThen11Env env off sub c e)
    { s with mem := s2StringBodyIfThen11Mem s.mem e off sub, pc := "cleanup", pre := some s.pc }

set_option maxHeartbeats 4000000 in
/-- **The refusal record's path finishes**, with the record's facts and the slot
lookup supplied by the caller: the heavy environment appears once, in the
composition's state, and the completion is the generic one.

**The budget is scoped to this theorem, and it is a cost exception, not a proof
trick.**  The composition's elaboration exceeds the default 200 000 heartbeats —
measured again after naming the state and after taking the slot lookup from the
caller, so neither of those is the cause — and completes at 4 000 000 in about a
minute.  The cause is inherent to a nine-cell record state crossing a lemma whose
conclusion mentions the state's memory; the general fix is a completion whose
outcome carries the memory as a *variable*, which is a change to the closing's
shape rather than to this path. -/
theorem s2StringBodyIfThen11_finishes {env : Env} {s : State} {c ei e : Nat}
    {off sub : BitVec 64}
    (hpc : s.pc = "if.then11")
    (hc : lookupName env "%c" = some (.ptr c))
    (hei : lookupName env "%ei" = some (.ptr ei))
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hoff : readBytes s.mem ei 8 = some (natToBytes off.toNat 8))
    (hcval : readBytes s.mem (c + (1112#64).toNat) 8 = some (wordBytes 8 e))
    (he64 : e < 2 ^ 64)
    (hslot : lookupName (s2StringBodyIfThen11Env env off sub c e) "%ei"
      = some (.ptr ei)) :
    runFuel s2StringBodyCalls 3 s2StringBodyBody (stateAt env s) =
      some (.ret (some (.int 32 0x00000000#32))
        (s2StringBodyIfThen11Mem s.mem e off sub)) := by
  have hstep := step_ifThen11_cleanup hpc hc hei hsub hoff hcval he64
  have hfin : runFuel s2StringBodyCalls 2 s2StringBodyBody
      (stateAt (s2StringBodyIfThen11Env env off sub c e)
        { s with mem := s2StringBodyIfThen11Mem s.mem e off sub, pc := "cleanup", pre := some s.pc }) =
      some (.ret (some (.int 32 0x00000000#32))
        (s2StringBodyIfThen11Mem s.mem e off sub)) :=
    s2StringBodyCleanup_fromRefused_finishes
      (env := s2StringBodyIfThen11Env env off sub c e)
      (s := { s with mem := s2StringBodyIfThen11Mem s.mem e off sub, pc := "cleanup", pre := some s.pc })
      rfl (by rw [hpc]) hslot
  have := runFuel_prefix_some (fun k => runFuel_jump_prefix hstep k) hfin
  simpa using this


/-- **The inside test's refusal path, end to end**: `land.lhs.true`, `if.end`, the
record's three fields, `cleanup`'s refusal form — five control steps, answer `0`.

Stated as one theorem because its terminal state spells the caller's values (the
callee's memory `extra` and cursor `nx`, its returned word `call`, and the record's
`c`, `ei`, `e`, `off`): the prefix split works only where a terminal's input state
is describable by the prefix's own hypotheses, and here it is not.  It needs **no
budget** — a lemma's proof is not re-elaborated at its call site — which is the
composition-side half of the cost model: the price is paid where the terminal is
proved, not where it is used. -/
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
    (hbit9 : evalICmp .eq call 0xffffffffffffffff#64 = 1#1)
    (hoff : readBytes extra ei 8 = some (natToBytes off.toNat 8))
    (hcval : readBytes extra (c + (1112#64).toNat) 8 = some (wordBytes 8 e))
    (he64 : e < 2 ^ 64) :
    runFuel s2StringBodyCalls 5 s2StringBodyBody (stateAt env s) =
      some (.ret (some (.int 32 0x00000000#32))
        (s2StringBodyIfThen11Mem extra e off sub)) := by
  have h1 := step_landLhsTrue_ifEnd hpc hsub hlen hconv hbit7
  have h2 : step s2StringBodyCalls s2StringBodyBody
      (stateAt
        (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
          ("%add", .int 64 (sub + len)) :: env)
        { s with pc := "if.end", pre := some s.pc }) =
      .jump (stateAt (s2StringBodyIfEndEnv
        (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
          ("%add", .int 64 (sub + len)) :: env) call)
        { s with mem := extra, next := nx, pc := "if.then11", pre := some "if.end" }) := by
    refine step_ifEnd_ifThen11 (env := ("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
        ("%add", .int 64 (sub + len)) :: env)
      (s := { s with pc := "if.end", pre := some s.pc }) rfl
      (by s2_lk) (by s2_lk) (by s2_lk) (by s2_lk) (by s2_lk) (by s2_lk) (by s2_lk) (by s2_lk)
      ?_ hbit9
    simpa only [stateAt] using hexp
  have hpre : ∀ k, runFuel s2StringBodyCalls (2 + k) s2StringBodyBody (stateAt env s) =
      runFuel s2StringBodyCalls k s2StringBodyBody
        (stateAt (s2StringBodyIfEndEnv
          (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
            ("%add", .int 64 (sub + len)) :: env) call)
          { s with mem := extra, next := nx, pc := "if.then11", pre := some "if.end" }) := by
    have h12 := runFuel_prefix_trans (fun j => runFuel_jump_prefix h1 j)
      (fun j => runFuel_jump_prefix h2 j)
    intro k
    simpa [show 2 + k = 1 + (1 + k) from by omega] using h12 k
  have hfin := s2StringBodyIfThen11_finishes (env := s2StringBodyIfEndEnv
      (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
        ("%add", .int 64 (sub + len)) :: env) call)
    (s := { s with mem := extra, next := nx, pc := "if.then11", pre := some "if.end" })
    (c := c) (ei := ei) (e := e) (off := off) (sub := sub)
    rfl (by s2_lk) (by s2_lk) (by s2_lk) (by simpa only [stateAt] using hoff)
    (by simpa only [stateAt] using hcval) he64 (by s2_lk)
  have := runFuel_prefix_some hpre hfin
  simpa using this


/-- **The inside test's decoded path, end to end**: `land.lhs.true`, `if.end`, the
decoded length's word at `outn` — five control steps, answer `2`.  The terminal
spells no caller value, so this composition is the cheapest of the four. -/
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
    (hbit9 : evalICmp .eq call 0xffffffffffffffff#64 = 0#1)
    (houtn : lookupName env "%outn" = some (.ptr outn)) :
    runFuel s2StringBodyCalls 5 s2StringBodyBody (stateAt env s) =
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
        { s with mem := extra, next := nx, pc := "if.end14", pre := some "if.end" }) := by
    refine step_ifEnd_ifEnd14 (env := ("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
        ("%add", .int 64 (sub + len)) :: env)
      (s := { s with pc := "if.end", pre := some s.pc }) rfl
      (by s2_lk) (by s2_lk) (by s2_lk) (by s2_lk) (by s2_lk) (by s2_lk) (by s2_lk) (by s2_lk)
      ?_ hbit9
    simpa only [stateAt] using hexp
  have hpre : ∀ k, runFuel s2StringBodyCalls (2 + k) s2StringBodyBody (stateAt env s) =
      runFuel s2StringBodyCalls k s2StringBodyBody
        (stateAt (s2StringBodyIfEndEnv
          (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
            ("%add", .int 64 (sub + len)) :: env) call)
          { s with mem := extra, next := nx, pc := "if.end14", pre := some "if.end" }) := by
    have h12 := runFuel_prefix_trans (fun j => runFuel_jump_prefix h1 j)
      (fun j => runFuel_jump_prefix h2 j)
    intro k
    simpa [show 2 + k = 1 + (1 + k) from by omega] using h12 k
  have hfin := s2StringBodyIfEnd14_finishes (env := s2StringBodyIfEndEnv
      (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
        ("%add", .int 64 (sub + len)) :: env) call)
    (s := { s with mem := extra, next := nx, pc := "if.end14", pre := some "if.end" })
    (call := call) (outn := outn)
    rfl (by s2_lk) (by s2_lk) (by s2_lk)
  have := runFuel_prefix_some hpre hfin
  simpa using this


end LeanLLVM.Refinement
