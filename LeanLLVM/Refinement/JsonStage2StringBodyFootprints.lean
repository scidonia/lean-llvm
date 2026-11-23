import LeanLLVM.Refinement.JsonStage2StringBodyAST

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)

/-! ### Axiom footprints

The clause and the two arm lemmas print their footprints with `#guard_msgs`, so
the build checks them rather than printing them.  The instrument's
discriminating control is the one §7.6 records: a throwaway declaration proved
with `sorry` prints `sorryAx` under the same command.  No `sorry` is in this
module. -/
/-- info: 'LeanLLVM.Refinement.escapeExpand8_decoded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapeExpand8_decoded

/-- info: 'LeanLLVM.Refinement.escapeExpand8_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapeExpand8_refused

/-- info: 'LeanLLVM.Refinement.s2StringBodyCalls_expand_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms s2StringBodyCalls_expand_eq

/-! ### One instruction, one step

The shapes this body has that `BlockEval`'s vocabulary does not: an `i8` load and
its comparison, the two- and four-argument call forms, and the store of a literal.
Each is the `evalInstr` equation at the environment builder, in the shape its
chain step consumes. -/

/-- `store i32 <c>, ptr %p`: the refusal record's first field. -/
theorem sb_step_store32_imm (calls : Calls) (env : Env) (s : State) (p : String)
    {x : BitVec 32} {a : Nat} (hp : lookupName env p = some (.ptr a)) :
    evalInstr calls (stateAt env s) (.store (Ty.int 32) (.imm (.int 32 x)) (.reg p)) =
      some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) }) := by
  have h1 : evalOperand (stateAt env s) (.imm (.int 32 x)) = some (.int 32 x) := rfl
  have h2 := BlockEval.evalOperand_reg_of env s p (.ptr a) hp
  unfold evalInstr
  dsimp only
  rw [h1, h2]
  simp [State.bind, stateAt, storeValue]

/-- `load i8, ptr %p`: the body's own span byte at the scan's answer. -/
theorem sb_step_load8 (calls : Calls) (env : Env) (s : State) (d p : String)
    {a : Nat} {bs : List UInt8} (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 1 = some bs) :
    evalInstr calls (stateAt env s) (.load d (Ty.int 8) (.reg p)) =
      some (stateAt ((d, .int 8 (BitVec.ofNat 8 (bytesToNat bs))) :: env) s) := by
  have h1 := BlockEval.evalOperand_reg_of env s p (.ptr a) hp
  have hv' : loadValue (stateAt env s).mem (.int 8) a =
      some (.int 8 (BitVec.ofNat 8 (bytesToNat bs))) := by
    change loadValue s.mem (.int 8) a =
      some (.int 8 (BitVec.ofNat 8 (bytesToNat bs)))
    simp only [loadValue, hv, show (8 + 7) / 8 = 1 from rfl]
    rw [ite_eq_right (by decide : ¬ ((8 : Nat) = 0))]
  unfold evalInstr
  dsimp only
  rw [h1]
  dsimp only
  rw [hv']
  rfl

/-- `icmp eq i8 %a, <c>`: the scan's answer tested against the backslash. -/
theorem sb_step_icmp8_eq_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 8} (ha : lookupName env a = some (.int 8 x)) :
    evalInstr calls (stateAt env s) (.icmp d .eq 8 (.reg a) (.imm (.int 8 c))) =
      some (stateAt ((d, .int 1 (evalICmpNat .eq 8 x.toNat c.toNat)) :: env) s) := by
  have h1 := BlockEval.evalOperand_reg_of env s a (.int 8 x) ha
  have h2 : evalOperand (stateAt env s) (.imm (.int 8 c)) = some (.int 8 c) := rfl
  unfold evalInstr
  dsimp only
  rw [h1, h2]
  simp [State.bind, stateAt, Value.intToNat]

theorem denoteCode_icmp8_eq_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 8} (ha : lookupName env a = some (.int 8 x)) (is : List Instr) :
    denoteCode calls (.icmp d .eq 8 (.reg a) (.imm (.int 8 c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmpNat .eq 8 x.toNat c.toNat)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (sb_step_icmp8_eq_imm calls env s d a ha)]

/-- A void call at four arguments: the exact prefix copy's emitted form. -/
theorem sb_step_callVoid4 (calls : Calls) (env : Env) (s : State) (callee : String)
    (o1 o2 o3 o4 : Operand) {v1 v2 v3 v4 : Value} {r : CallOutcome}
    (h1 : evalOperand (stateAt env s) o1 = some v1)
    (h2 : evalOperand (stateAt env s) o2 = some v2)
    (h3 : evalOperand (stateAt env s) o3 = some v3)
    (h4 : evalOperand (stateAt env s) o4 = some v4)
    (hc : calls callee [v1, v2, v3, v4] s.mem s.next = some r) :
    evalInstr calls (stateAt env s)
        (.callVoid callee [(Ty.ptr, o1), (Ty.ptr, o2), (Ty.int 64, o3), (Ty.int 1, o4)]) =
      some (stateAt env { s with mem := r.mem, next := r.next }) := by
  have hargs : evalOperands (stateAt env s)
      [(Ty.ptr, o1), (Ty.ptr, o2), (Ty.int 64, o3), (Ty.int 1, o4)] =
      some [v1, v2, v3, v4] := by
    simp only [evalOperands, h1, h2, h3, h4]
  have hc' : calls callee [v1, v2, v3, v4] (stateAt env s).mem (stateAt env s).next =
      some r := hc
  simp only [evalInstr, hargs, hc']
  rfl

/-- A two-argument call binding its `i64` result: `z_scan`'s emitted form. -/
theorem sb_step_call2 (calls : Calls) (env : Env) (s : State) (d callee : String)
    (o1 o2 : Operand) {v1 v2 : Value} {r : CallOutcome}
    (h1 : evalOperand (stateAt env s) o1 = some v1)
    (h2 : evalOperand (stateAt env s) o2 = some v2)
    (hc : calls callee [v1, v2] s.mem s.next = some r) :
    evalInstr calls (stateAt env s)
        (.call d (Ty.int 64) callee [(Ty.ptr, o1), (Ty.int 64, o2)]) =
      some (stateAt ((d, r.ret) :: env) { s with mem := r.mem, next := r.next }) := by
  have hargs : evalOperands (stateAt env s)
      [(Ty.ptr, o1), (Ty.int 64, o2)] = some [v1, v2] := by
    simp only [evalOperands, h1, h2]
  have hc' : calls callee [v1, v2] (stateAt env s).mem (stateAt env s).next = some r := hc
  simp only [evalInstr, hargs, hc']
  rfl

/-- A call at eight arguments binding its `i64` result: the expander's emitted
form.  Its outcome is the clause's (`escapeExpand8_decoded`/`_refused`). -/
theorem sb_step_call8 (calls : Calls) (env : Env) (s : State) (d callee : String)
    (o1 o2 o3 o4 o5 o6 o7 o8 : Operand)
    {v1 v2 v3 v4 v5 v6 v7 v8 : Value} {r : CallOutcome}
    (h1 : evalOperand (stateAt env s) o1 = some v1)
    (h2 : evalOperand (stateAt env s) o2 = some v2)
    (h3 : evalOperand (stateAt env s) o3 = some v3)
    (h4 : evalOperand (stateAt env s) o4 = some v4)
    (h5 : evalOperand (stateAt env s) o5 = some v5)
    (h6 : evalOperand (stateAt env s) o6 = some v6)
    (h7 : evalOperand (stateAt env s) o7 = some v7)
    (h8 : evalOperand (stateAt env s) o8 = some v8)
    (hc : calls callee [v1, v2, v3, v4, v5, v6, v7, v8] s.mem s.next = some r) :
    evalInstr calls (stateAt env s) (.call d (Ty.int 64) callee
        [(Ty.ptr, o1), (Ty.int 64, o2), (Ty.ptr, o3), (Ty.ptr, o4), (Ty.ptr, o5),
         (Ty.ptr, o6), (Ty.int 64, o7), (Ty.int 64, o8)]) =
      some (stateAt ((d, r.ret) :: env) { s with mem := r.mem, next := r.next }) := by
  have hargs : evalOperands (stateAt env s)
      [(Ty.ptr, o1), (Ty.int 64, o2), (Ty.ptr, o3), (Ty.ptr, o4), (Ty.ptr, o5),
       (Ty.ptr, o6), (Ty.int 64, o7), (Ty.int 64, o8)] =
      some [v1, v2, v3, v4, v5, v6, v7, v8] := by
    simp only [evalOperands, h1, h2, h3, h4, h5, h6, h7, h8]
  have hc' : calls callee [v1, v2, v3, v4, v5, v6, v7, v8]
      (stateAt env s).mem (stateAt env s).next = some r := hc
  simp only [evalInstr, hargs, hc']
  rfl

/-- A four-argument call binding its `i64` result: the list-free decoder's form. -/
theorem sb_step_call4 (calls : Calls) (env : Env) (s : State) (d callee : String)
    (o1 o2 o3 o4 : Operand) {v1 v2 v3 v4 : Value} {r : CallOutcome}
    (h1 : evalOperand (stateAt env s) o1 = some v1)
    (h2 : evalOperand (stateAt env s) o2 = some v2)
    (h3 : evalOperand (stateAt env s) o3 = some v3)
    (h4 : evalOperand (stateAt env s) o4 = some v4)
    (hc : calls callee [v1, v2, v3, v4] s.mem s.next = some r) :
    evalInstr calls (stateAt env s) (.call d (Ty.int 64) callee
        [(Ty.ptr, o1), (Ty.int 64, o2), (Ty.ptr, o3), (Ty.ptr, o4)]) =
      some (stateAt ((d, r.ret) :: env) { s with mem := r.mem, next := r.next }) := by
  have hargs : evalOperands (stateAt env s)
      [(Ty.ptr, o1), (Ty.int 64, o2), (Ty.ptr, o3), (Ty.ptr, o4)] =
      some [v1, v2, v3, v4] := by
    simp only [evalOperands, h1, h2, h3, h4]
  have hc' : calls callee [v1, v2, v3, v4] (stateAt env s).mem (stateAt env s).next =
      some r := hc
  simp only [evalInstr, hargs, hc']
  rfl

-- The marker's step: `stage2Calls` selects it by callee name, so it writes
-- nothing and allocates nothing.  The step's conclusion is the state unchanged.
theorem sb_step_lifetime (env : Env) (s : State) (ei : Nat) (callee : String)
    (hname : callee = "llvm.lifetime.start.p0" ∨ callee = "llvm.lifetime.end.p0")
    (hei : lookupName env "%ei" = some (.ptr ei)) :
    evalInstr s2StringBodyCalls (stateAt env s)
        (.callVoid callee [(Ty.int 64, .imm (.int 64 (8#64))), (Ty.ptr, .reg "%ei")]) =
      some (stateAt env s) := by
  have hargs : evalOperands (stateAt env s)
      [(Ty.int 64, .imm (.int 64 (8#64))), (Ty.ptr, .reg "%ei")] =
      some [.int 64 (8#64), .ptr ei] := by
    simp only [evalOperands, evalOperand, Const.toValue, stateAt, hei]
  rcases hname with rfl | rfl <;>
    simp only [evalInstr, hargs, s2StringBodyCalls, JsonStage2IR.stage2Calls]

/-! ### The entry block

The entry converts the two addresses, takes the slot's lifetime marker, and tests
`nxp` against zero: the branch that picks the scan arm and the list-free arm. -/

/-- **The entry block's run.**  The seven instructions, each applied at the **cons**
environment the previous step built, with the allocator cell carried as
`(Ty.int 64).sizeBytes` and each one-cell-deep lookup peeled by `s2_lk`. -/
theorem s2StringBody_entry_denote {env : Env} {s : State}
    {c p base : Nat} {nxp : BitVec 64}
    (hc : lookupName env "%c" = some (.ptr c))
    (hp : lookupName env "%p" = some (.ptr p))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hbase : readBytes s.mem c 8 = some (wordBytes 8 base)) (hb64 : base < 2 ^ 64)
    (hp64 : p < 2 ^ 64) :
    denoteCode s2StringBodyCalls s2StringBodyEntryInstrs (stateAt env s) =
      denoteCode s2StringBodyCalls []
        (stateAt (s2StringBodyEnv6 (s2StringBodyEnv5 (s2StringBodyEnv4
          (s2StringBodyEnv3 (s2StringBodyEnv2 (s2StringBodyEnv1 env s.next) base) p) base)
          p base) nxp)
          { s with next := s.next + (Ty.int 64).sizeBytes }) := by
  dsimp only [s2StringBodyEntryInstrs]
  rw [denoteCode_cons_of _ _ _ _ _ (sb_step_alloca s2StringBodyCalls env s "%ei" (Ty.int 64) 0)]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_loadPtr s2StringBodyCalls (("%ei", .ptr s.next) :: env)
      { s with next := s.next + (Ty.int 64).sizeBytes }
      "%0" "%c" (by s2_lk) hbase hb64)]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_ptrtoint s2StringBodyCalls (("%0", .ptr base) :: ("%ei", .ptr s.next) :: env)
      { s with next := s.next + (Ty.int 64).sizeBytes }
      "%sub.ptr.lhs.cast" "%p" (by s2_lk) hp64)]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_ptrtoint s2StringBodyCalls
      (("%sub.ptr.lhs.cast", .int 64 (BitVec.ofNat 64 p)) :: ("%0", .ptr base) ::
        ("%ei", .ptr s.next) :: env)
      { s with next := s.next + (Ty.int 64).sizeBytes }
      "%sub.ptr.rhs.cast" "%0" (by s2_lk) hb64)]
  rw [denoteCode_sub_reg s2StringBodyCalls
    (("%sub.ptr.rhs.cast", .int 64 (BitVec.ofNat 64 base)) ::
      ("%sub.ptr.lhs.cast", .int 64 (BitVec.ofNat 64 p)) :: ("%0", .ptr base) ::
      ("%ei", .ptr s.next) :: env) { s with next := s.next + (Ty.int 64).sizeBytes }
    "%sub.ptr.sub" "%sub.ptr.lhs.cast" "%sub.ptr.rhs.cast" (by s2_lk) (by s2_lk) _]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_lifetime
      (("%sub.ptr.sub", .int 64 (BitVec.ofNat 64 p - BitVec.ofNat 64 base)) ::
        ("%sub.ptr.rhs.cast", .int 64 (BitVec.ofNat 64 base)) ::
        ("%sub.ptr.lhs.cast", .int 64 (BitVec.ofNat 64 p)) :: ("%0", .ptr base) ::
        ("%ei", .ptr s.next) :: env)
      { s with next := s.next + (Ty.int 64).sizeBytes } s.next
      "llvm.lifetime.start.p0" (Or.inl rfl) (by s2_lk))]
  rw [denoteCode_icmp_eq_imm s2StringBodyCalls
    (("%sub.ptr.sub", .int 64 (BitVec.ofNat 64 p - BitVec.ofNat 64 base)) ::
      ("%sub.ptr.rhs.cast", .int 64 (BitVec.ofNat 64 base)) ::
      ("%sub.ptr.lhs.cast", .int 64 (BitVec.ofNat 64 p)) :: ("%0", .ptr base) ::
      ("%ei", .ptr s.next) :: env)
    { s with next := s.next + (Ty.int 64).sizeBytes }
    "%tobool.not" "%nxp" (by s2_lk) []]
  simp only [denoteCode_nil, s2StringBodyEnv1, s2StringBodyEnv2, s2StringBodyEnv3,
    s2StringBodyEnv4, s2StringBodyEnv5, s2StringBodyEnv6]

/-! ### `while.cond.preheader`: the cursor word and the head's first test -/

/-- The `while.cond.preheader` block's environment: the cursor word and the test
of it against the count. -/
def s2StringBodyWhileCondEnv (env : Env) (j0 nxp : BitVec 64) : Env :=
  ("%cmp3", .int 1 (evalICmp .ult j0 nxp)) :: ("%xj.promoted", .int 64 j0) :: env

/-- The `while.cond.preheader` block's instruction list. -/
def s2StringBodyWhileCondInstrs : List Instr :=
  [Instr.load "%xj.promoted" (Ty.int 64) (Operand.reg "%xj"),
   Instr.icmp "%cmp3" (IPred.ult) 64 (Operand.reg "%xj.promoted") (Operand.reg "%nxp")]

theorem s2StringBodyWhileCondInstrs_eq :
    (s2StringBodyBody.findBlock "while.cond.preheader").map (·.instrs) =
      some s2StringBodyWhileCondInstrs := by decide

/-- **The `while.cond.preheader` block's run**: the cursor word, and the head's
test of it against the count. -/
theorem s2StringBody_whileCond_denote {calls : Calls} {env : Env} {s : State}
    {xj : Nat} {j0 nxp : BitVec 64}
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp))
    (hj0 : readBytes s.mem xj 8 = some (wordBytes 8 j0.toNat))
    (hj64 : j0.toNat < 2 ^ 64) :
    denoteCode calls s2StringBodyWhileCondInstrs (stateAt env s) =
      denoteCode calls [] (stateAt (s2StringBodyWhileCondEnv env j0 nxp) s) := by
  dsimp only [s2StringBodyWhileCondInstrs]
  rw [denoteCode_load64 (v := j0) calls env s "%xj.promoted" "%xj" hxj
    (by rw [hj0]; rfl) _]
  rw [denoteCode_icmp_ult_reg calls (("%xj.promoted", .int 64 j0) :: env) s "%cmp3"
    "%xj.promoted" "%nxp" (by s2_lk) hnxp []]
  simp only [denoteCode_nil, s2StringBodyWhileCondEnv]

/-! ### The scan's head and body, and the inside test -/

/-- The `land.rhs` block's instruction list: the counter's `phi`, the lane's
address, the lane, its zero-extension, and the test over the body's extent. -/
def s2StringBodyLandRhsInstrs : List Instr :=
  [Instr.phi "%inc24" (Ty.int 64)
     [("while.body", Operand.reg "%inc"),
      ("while.cond.preheader", Operand.reg "%xj.promoted")],
   Instr.gep "%arrayidx" (Ty.int 32) (Operand.reg "%xp") (Operand.reg "%inc24"),
   Instr.load "%1" (Ty.int 32) (Operand.reg "%arrayidx"),
   Instr.zext "%conv" 32 64 (Operand.reg "%1"),
   Instr.icmp "%cmp1" (IPred.ugt) 64 (Operand.reg "%sub.ptr.sub")
     (Operand.reg "%conv")]

theorem s2StringBodyLandRhsInstrs_eq :
    (s2StringBodyBody.findBlock "land.rhs").map (·.instrs) =
      some s2StringBodyLandRhsInstrs := by decide

/-- The `land.rhs` block's environment: the counter, the lane's address, the lane
and its zero-extension, and the test over the body's extent — each in the form
its step produced. -/
def s2StringBodyLandRhsEnv (env : Env) (inc24 : BitVec 64) (xp : Nat)
    (bs : List UInt8) (sub : BitVec 64) : Env :=
  ("%cmp1", .int 1 (evalICmpNat .ugt 64 sub.toNat
      (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat).toNat)) ::
    ("%conv", .int 64 (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat)) ::
    ("%1", .int 32 (BitVec.ofNat 32 (bytesToNat bs))) ::
    ("%arrayidx", .ptr (xp + (inc24.signExtend 64).toNat * 4)) ::
    ("%inc24", .int 64 inc24) :: env

/-- **The `land.rhs` block's run**, at the predecessor the edge delivered: the
counter's `phi`, the lane at the position, its zero-extension and the test. -/
theorem s2StringBody_landRhs_denote {calls : Calls} {env : Env} {s : State}
    {p : String} {op : Operand} {inc24 : BitVec 64} {xp : Nat} {bs : List UInt8}
    {sub : BitVec 64}
    (hpre : s.pre = some p)
    (hinc : phiIncoming p [("while.body", Operand.reg "%inc"),
      ("while.cond.preheader", Operand.reg "%xj.promoted")] = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 inc24))
    (hxp : lookupName env "%xp" = some (.ptr xp))
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hpos : (inc24.signExtend 64).toNat < 2 ^ 63)
    (hlane : readBytes s.mem (xp + (inc24.signExtend 64).toNat * 4) 4 = some bs) :
    denoteCode calls s2StringBodyLandRhsInstrs (stateAt env s) =
      denoteCode calls [] (stateAt (s2StringBodyLandRhsEnv env inc24 xp bs sub) s) := by
  dsimp only [s2StringBodyLandRhsInstrs]
  rw [denoteCode_phi calls env s "%inc24" (Ty.int 64) _ hpre hinc hop _ (by decide)]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_gep32 calls (("%inc24", .int 64 inc24) :: env) s "%arrayidx" "%xp"
      "%inc24" (by s2_lk) (by s2_lk) hpos)]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_load32 calls
      (("%arrayidx", .ptr (xp + (inc24.signExtend 64).toNat * 4)) ::
        ("%inc24", .int 64 inc24) :: env) s "%1" "%arrayidx" (by s2_lk) hlane)]
  rw [denoteCode_zext calls
    (("%1", .int 32 (BitVec.ofNat 32 (bytesToNat bs))) ::
      ("%arrayidx", .ptr (xp + (inc24.signExtend 64).toNat * 4)) ::
      ("%inc24", .int 64 inc24) :: env) s "%conv" "%1" 32 64 (by s2_lk) _]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_icmp_rr calls
      (("%conv", .int 64 (BitVec.ofNat 64 (BitVec.ofNat 32 (bytesToNat bs)).toNat)) ::
        ("%1", .int 32 (BitVec.ofNat 32 (bytesToNat bs))) ::
        ("%arrayidx", .ptr (xp + (inc24.signExtend 64).toNat * 4)) ::
        ("%inc24", .int 64 inc24) :: env) s "%cmp1" "%sub.ptr.sub" "%conv" .ugt
      (by s2_lk) (by s2_lk))]
  simp only [denoteCode_nil, s2StringBodyLandRhsEnv]

/-- The `while.body` block's instruction list. -/
def s2StringBodyWhileBodyInstrs : List Instr :=
  [Instr.binop "%inc" (BinOp.add) 64 (Operand.reg "%inc24")
     (Operand.imm (Const.int 64 0x0000000000000001#64)),
   Instr.store (Ty.int 64) (Operand.reg "%inc") (Operand.reg "%xj"),
   Instr.icmp "%exitcond.not" (IPred.eq) 64 (Operand.reg "%inc")
     (Operand.reg "%nxp")]

theorem s2StringBodyWhileBodyInstrs_eq :
    (s2StringBodyBody.findBlock "while.body").map (·.instrs) =
      some s2StringBodyWhileBodyInstrs := by decide

/-- **The `while.body` block's run**: the counter advances by one, the cursor
word takes it, and the exit test compares it with the count. -/
theorem s2StringBody_whileBody_denote {calls : Calls} {env : Env} {s : State}
    {inc24 nxp : BitVec 64} {xj : Nat}
    (hinc24 : lookupName env "%inc24" = some (.int 64 inc24))
    (hxj : lookupName env "%xj" = some (.ptr xj))
    (hnxp : lookupName env "%nxp" = some (.int 64 nxp)) :
    denoteCode calls s2StringBodyWhileBodyInstrs (stateAt env s) =
      denoteCode calls []
        (stateAt
          (("%exitcond.not", .int 1 (evalICmp .eq (inc24 + 1#64) nxp)) ::
            ("%inc", .int 64 (inc24 + 1#64)) :: env)
          { s with mem := writeBytes s.mem xj (natToBytes (inc24 + 1#64).toNat 8) }) := by
  dsimp only [s2StringBodyWhileBodyInstrs]
  rw [denoteCode_add_imm calls env s "%inc" "%inc24" hinc24 _]
  rw [denoteCode_store64 calls (("%inc", .int 64 (inc24 + 1#64)) :: env) s "%inc" "%xj"
    (by s2_lk) (by s2_lk) _]
  rw [denoteCode_icmp_eq_reg calls (("%inc", .int 64 (inc24 + 1#64)) :: env)
    { s with mem := writeBytes s.mem xj (natToBytes (inc24 + 1#64).toNat 8) }
    "%exitcond.not" "%inc" "%nxp" (by s2_lk) (by s2_lk) []]

/-- The `land.lhs.true` block's instruction list: the extent's end and the test
of the lane against it. -/
def s2StringBodyLandLhsTrueInstrs : List Instr :=
  [Instr.binop "%add" (BinOp.add) 64 (Operand.reg "%sub.ptr.sub")
     (Operand.reg "%len"),
   Instr.icmp "%cmp7" (IPred.ugt) 64 (Operand.reg "%add") (Operand.reg "%conv")]

theorem s2StringBodyLandLhsTrueInstrs_eq :
    (s2StringBodyBody.findBlock "land.lhs.true").map (·.instrs) =
      some s2StringBodyLandLhsTrueInstrs := by decide

/-- **The `land.lhs.true` block's run**: the body's extent as an end address, and
the lane tested against it. -/
theorem s2StringBody_landLhsTrue_denote {calls : Calls} {env : Env} {s : State}
    {sub len conv : BitVec 64}
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hlen : lookupName env "%len" = some (.int 64 len))
    (hconv : lookupName env "%conv" = some (.int 64 conv)) :
    denoteCode calls s2StringBodyLandLhsTrueInstrs (stateAt env s) =
      denoteCode calls []
        (stateAt
          (("%cmp7", .int 1 (evalICmpNat .ugt 64 (sub + len).toNat conv.toNat)) ::
            ("%add", .int 64 (sub + len)) :: env) s) := by
  dsimp only [s2StringBodyLandLhsTrueInstrs]
  rw [denoteCode_add_reg calls env s "%add" "%sub.ptr.sub" "%len" hsub hlen _]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_icmp_rr calls (("%add", .int 64 (sub + len)) :: env) s "%cmp7"
      "%add" "%conv" .ugt (by s2_lk) hconv)]

/-! ### The list arm's exits and the expander -/

/-- The `if.then9` block's instruction list: the body-itself form's length word. -/
def s2StringBodyIfThen9Instrs : List Instr :=
  [Instr.store (Ty.int 64) (Operand.reg "%len") (Operand.reg "%outn")]

theorem s2StringBodyIfThen9Instrs_eq :
    (s2StringBodyBody.findBlock "if.then9").map (·.instrs) =
      some s2StringBodyIfThen9Instrs := by decide

/-- **The `if.then9` arm's run**: `outn` takes the body's extent. -/
theorem s2StringBody_ifThen9_denote {calls : Calls} {env : Env} {s : State}
    {len : BitVec 64} {outn : Nat}
    (hlen : lookupName env "%len" = some (.int 64 len))
    (houtn : lookupName env "%outn" = some (.ptr outn)) :
    denoteCode calls s2StringBodyIfThen9Instrs (stateAt env s) =
      denoteCode calls []
        (stateAt env { s with mem := writeBytes s.mem outn (natToBytes len.toNat 8) }) := by
  dsimp only [s2StringBodyIfThen9Instrs]
  rw [denoteCode_store64 calls env s "%len" "%outn" hlen houtn []]

/-- The `if.end` block's environment: the expander's returned word and the branch
test over it. -/
def s2StringBodyIfEndEnv (env : Env) (call : BitVec 64) : Env :=
  ("%cmp10", .int 1 (evalICmp .eq call 0xffffffffffffffff#64)) ::
    ("%call", .int 64 call) :: env

/-- The `if.end` block's instruction list: the slot's clear, the expander at eight
arguments, and the test of its answer. -/
def s2StringBodyIfEndInstrs : List Instr :=
  [Instr.store (Ty.int 64) (Operand.imm (Const.int 64 0x0000000000000000#64))
     (Operand.reg "%ei"),
   Instr.call "%call" (Ty.int 64) "leanllvm_json_escape_expand"
     [(Ty.ptr, Operand.reg "%p"), (Ty.int 64, Operand.reg "%len"),
      (Ty.ptr, Operand.reg "%dst"), (Ty.ptr, Operand.reg "%ei"),
      (Ty.ptr, Operand.reg "%xp"), (Ty.ptr, Operand.reg "%xj"),
      (Ty.int 64, Operand.reg "%nxp"), (Ty.int 64, Operand.reg "%sub.ptr.sub")],
   Instr.icmp "%cmp10" (IPred.eq) 64 (Operand.reg "%call")
     (Operand.imm (Const.int 64 0xffffffffffffffff#64))]

theorem s2StringBodyIfEndInstrs_eq :
    (s2StringBodyBody.findBlock "if.end").map (·.instrs) =
      some s2StringBodyIfEndInstrs := by decide

/-- **The `if.end` block's run**: the slot's clear, the expander at the eight
registers the scan left, and the test of the returned word against all-ones. -/
theorem s2StringBody_ifEnd_denote {env : Env} {s : State}
    {p dst ei xp xj : Nat} {len nxp sub call : BitVec 64} {m : Mem} {nx : Nat}
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
      some { ret := .int 64 call, mem := m, next := nx }) :
    denoteCode s2StringBodyCalls s2StringBodyIfEndInstrs (stateAt env s) =
      denoteCode s2StringBodyCalls []
        (stateAt (s2StringBodyIfEndEnv env call) { s with mem := m, next := nx }) := by
  dsimp only [s2StringBodyIfEndInstrs]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_store64_imm s2StringBodyCalls env s "%ei" (x := 0#64) hei)]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_call8 s2StringBodyCalls env _ "%call" "leanllvm_json_escape_expand"
      (.reg "%p") (.reg "%len") (.reg "%dst") (.reg "%ei") (.reg "%xp")
      (.reg "%xj") (.reg "%nxp") (.reg "%sub.ptr.sub")
      (BlockEval.evalOperand_reg_of env _ "%p" (.ptr p) hp)
      (BlockEval.evalOperand_reg_of env _ "%len" (.int 64 len) hlen)
      (BlockEval.evalOperand_reg_of env _ "%dst" (.ptr dst) hdst)
      (BlockEval.evalOperand_reg_of env _ "%ei" (.ptr ei) hei)
      (BlockEval.evalOperand_reg_of env _ "%xp" (.ptr xp) hxp)
      (BlockEval.evalOperand_reg_of env _ "%xj" (.ptr xj) hxj)
      (BlockEval.evalOperand_reg_of env _ "%nxp" (.int 64 nxp) hnxp)
      (BlockEval.evalOperand_reg_of env _ "%sub.ptr.sub" (.int 64 sub) hsub)
      hc)]
  rw [denoteCode_icmp_eq_imm s2StringBodyCalls _ _ "%cmp10" "%call" (by s2_lk) []]
  simp only [denoteCode_nil, s2StringBodyIfEndEnv]

/-- The `if.then12` block's environment: the record's pointer, its three fields,
and the offset word the expander returned. -/
def s2StringBodyIfThen12Env (env : Env) (off sub : BitVec 64) (c e : Nat) : Env :=
  ("%msg2.i.i", .ptr (e + (16#64).toNat)) ::
    ("%off1.i.i", .ptr (e + (8#64).toNat)) ::
    ("%c.val95", .ptr e) :: ("%3", .ptr (c + (1112#64).toNat)) ::
    ("%add13", .int 64 (off + sub)) :: ("%2", .int 64 off) :: env

def s2StringBodyIfThen12Mem (mem : Mem) (e : Nat) (off sub : BitVec 64) : Mem :=
  writeBytes
    (writeBytes (writeBytes mem e (natToBytes (0#32).toNat 4))
      (e + (8#64).toNat) (natToBytes (off + sub).toNat 8))
    (e + (16#64).toNat) (natToBytes 0 8)

/-- The `if.then12` block's instruction list: the expander's offset word, the
record's pointer, and the record's three fields. -/
def s2StringBodyIfThen12Instrs : List Instr :=
  [Instr.load "%2" (Ty.int 64) (Operand.reg "%ei"),
   Instr.binop "%add13" (BinOp.add) 64 (Operand.reg "%2") (Operand.reg "%sub.ptr.sub"),
   Instr.gep "%3" (Ty.int 8) (Operand.reg "%c")
     (Operand.imm (Const.int 64 0x0000000000000458#64)),
   Instr.load "%c.val95" (Ty.ptr) (Operand.reg "%3"),
   Instr.store (Ty.int 32) (Operand.imm (Const.int 32 0x0000000000000000#32))
     (Operand.reg "%c.val95"),
   Instr.gep "%off1.i.i" (Ty.int 8) (Operand.reg "%c.val95")
     (Operand.imm (Const.int 64 0x0000000000000008#64)),
   Instr.store (Ty.int 64) (Operand.reg "%add13") (Operand.reg "%off1.i.i"),
   Instr.gep "%msg2.i.i" (Ty.int 8) (Operand.reg "%c.val95")
     (Operand.imm (Const.int 64 0x0000000000000010#64)),
   Instr.store (Ty.ptr) (Operand.imm (Const.null)) (Operand.reg "%msg2.i.i")]

theorem s2StringBodyIfThen12Instrs_eq :
    (s2StringBodyBody.findBlock "if.then12").map (·.instrs) =
      some s2StringBodyIfThen12Instrs := by decide

theorem s2StringBody_ifThen12_denote {calls : Calls} {env : Env} {s : State}
    {c ei e : Nat} {off sub : BitVec 64}
    (hc : lookupName env "%c" = some (.ptr c))
    (hei : lookupName env "%ei" = some (.ptr ei))
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hoff : readBytes s.mem ei 8 = some (natToBytes off.toNat 8))
    (hcval : readBytes s.mem (c + (1112#64).toNat) 8 = some (wordBytes 8 e))
    (he64 : e < 2 ^ 64) :
    denoteCode calls s2StringBodyIfThen12Instrs (stateAt env s) =
      denoteCode calls []
        (stateAt (s2StringBodyIfThen12Env env off sub c e)
          { s with mem := s2StringBodyIfThen12Mem s.mem e off sub }) := by
  dsimp only [s2StringBodyIfThen12Instrs]
  rw [denoteCode_load64 (v := off) calls env s "%2" "%ei"
    (by simpa [lookupName] using hei) hoff _]
  rw [denoteCode_add_reg calls (("%2", .int 64 off) :: env) s "%add13" "%2"
    "%sub.ptr.sub" (by s2_lk) (by s2_lk) _]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_gep8_lit calls
      (("%add13", .int 64 (off + sub)) :: ("%2", .int 64 off) :: env) s "%3" "%c"
      (1112#64) (by s2_lk) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_loadPtr calls
      (("%3", .ptr (c + (1112#64).toNat)) ::
        ("%add13", .int 64 (off + sub)) :: ("%2", .int 64 off) :: env) s
      "%c.val95" "%3" (by s2_lk) hcval he64)]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_store32_imm calls
      (("%c.val95", .ptr e) :: ("%3", .ptr (c + (1112#64).toNat)) ::
        ("%add13", .int 64 (off + sub)) :: ("%2", .int 64 off) :: env) s
      "%c.val95" (by s2_lk))]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_gep8_lit calls
      (("%c.val95", .ptr e) :: ("%3", .ptr (c + (1112#64).toNat)) ::
        ("%add13", .int 64 (off + sub)) :: ("%2", .int 64 off) :: env)
      { s with mem := writeBytes s.mem e (natToBytes (0#32).toNat 4) }
      "%off1.i.i" "%c.val95" (8#64) (by s2_lk) (by decide))]
  rw [denoteCode_store64 calls
    (("%off1.i.i", .ptr (e + (8#64).toNat)) ::
      ("%c.val95", .ptr e) :: ("%3", .ptr (c + (1112#64).toNat)) ::
      ("%add13", .int 64 (off + sub)) :: ("%2", .int 64 off) :: env)
    { s with mem := writeBytes s.mem e (natToBytes (0#32).toNat 4) }
    "%add13" "%off1.i.i" (by s2_lk) (by s2_lk) _]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_gep8_lit calls
      (("%off1.i.i", .ptr (e + (8#64).toNat)) ::
        ("%c.val95", .ptr e) :: ("%3", .ptr (c + (1112#64).toNat)) ::
        ("%add13", .int 64 (off + sub)) :: ("%2", .int 64 off) :: env)
      { s with mem := (writeBytes (writeBytes s.mem e (natToBytes (0#32).toNat 4))
          (e + (8#64).toNat) (natToBytes (off + sub).toNat 8)) }
      "%msg2.i.i" "%c.val95" (16#64) (by s2_lk) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_storePtr_null calls
      (("%msg2.i.i", .ptr (e + (16#64).toNat)) ::
        ("%off1.i.i", .ptr (e + (8#64).toNat)) ::
        ("%c.val95", .ptr e) :: ("%3", .ptr (c + (1112#64).toNat)) ::
        ("%add13", .int 64 (off + sub)) :: ("%2", .int 64 off) :: env)
      { s with mem := (writeBytes (writeBytes s.mem e (natToBytes (0#32).toNat 4))
          (e + (8#64).toNat) (natToBytes (off + sub).toNat 8)) }
      "%msg2.i.i" (by s2_lk))]
  simp only [denoteCode_nil, s2StringBodyIfThen12Env, s2StringBodyIfThen12Mem]

/-- The `if.end15` block's instruction list: the decoded length at `outn`. -/
def s2StringBodyIfEnd15Instrs : List Instr :=
  [Instr.store (Ty.int 64) (Operand.reg "%call") (Operand.reg "%outn")]

theorem s2StringBodyIfEnd15Instrs_eq :
    (s2StringBodyBody.findBlock "if.end15").map (·.instrs) =
      some s2StringBodyIfEnd15Instrs := by decide

/-- **The `if.end15` arm's run**: the expander's returned word at `outn`. -/
theorem s2StringBody_ifEnd15_denote {calls : Calls} {env : Env} {s : State}
    {call : BitVec 64} {outn : Nat}
    (hcall : lookupName env "%call" = some (.int 64 call))
    (houtn : lookupName env "%outn" = some (.ptr outn)) :
    denoteCode calls s2StringBodyIfEnd15Instrs (stateAt env s) =
      denoteCode calls []
        (stateAt env { s with mem := writeBytes s.mem outn (natToBytes call.toNat 8) }) := by
  dsimp only [s2StringBodyIfEnd15Instrs]
  rw [denoteCode_store64 calls env s "%call" "%outn" hcall houtn []]

/-! ### The list-free arm

With no list, the body scans its own span (`z_scan`), refuses a control byte,
copies the clean prefix exactly once the decode has accepted, and decodes the
suffix.  Each block's run is below; the block's terminator picks the next. -/

/-- The `if.end16` block's environment: `z_scan`'s answer and its test. -/
def s2StringBodyIfEnd16Env (env : Env) (call17 : BitVec 64) : Env :=
  ("%cmp18", .int 1 (evalICmp .eq call17 0xffffffffffffffff#64)) ::
    ("%call17", .int 64 call17) :: env

/-- The `if.end16` block's instruction list: the scan and the test of its answer. -/
def s2StringBodyIfEnd16Instrs : List Instr :=
  [Instr.call "%call17" (Ty.int 64) "z_scan"
     [(Ty.ptr, Operand.reg "%p"), (Ty.int 64, Operand.reg "%len")],
   Instr.icmp "%cmp18" (IPred.eq) 64 (Operand.reg "%call17")
     (Operand.imm (Const.int 64 0xffffffffffffffff#64))]

theorem s2StringBodyIfEnd16Instrs_eq :
    (s2StringBodyBody.findBlock "if.end16").map (·.instrs) =
      some s2StringBodyIfEnd16Instrs := by decide

/-- **The `if.end16` block's run**: the scan at the body's own span, and the test
of its answer against all-ones. -/
theorem s2StringBody_ifEnd16_denote {env : Env} {s : State}
    {p len : Nat} {call17 : BitVec 64} {m : Mem} {nx : Nat}
    (hp : lookupName env "%p" = some (.ptr p))
    (hlen : lookupName env "%len" = some (.int 64 len))
    (hc : s2StringBodyCalls "z_scan" [.ptr p, .int 64 len] s.mem s.next =
      some { ret := .int 64 call17, mem := m, next := nx }) :
    denoteCode s2StringBodyCalls s2StringBodyIfEnd16Instrs (stateAt env s) =
      denoteCode s2StringBodyCalls []
        (stateAt (s2StringBodyIfEnd16Env env call17) { s with mem := m, next := nx }) := by
  dsimp only [s2StringBodyIfEnd16Instrs]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_call2 s2StringBodyCalls env s "%call17" "z_scan" (.reg "%p") (.reg "%len")
      (BlockEval.evalOperand_reg_of env _ "%p" (.ptr p) hp)
      (BlockEval.evalOperand_reg_of env _ "%len" (.int 64 len) hlen) hc)]
  rw [denoteCode_icmp_eq_imm s2StringBodyCalls _ _ "%cmp18" "%call17" (by s2_lk) []]
  simp only [denoteCode_nil, s2StringBodyIfEnd16Env]

/-- The `if.then20` block's instruction list: the plain span's length word. -/
def s2StringBodyIfThen20Instrs : List Instr :=
  [Instr.store (Ty.int 64) (Operand.reg "%len") (Operand.reg "%outn")]

theorem s2StringBodyIfThen20Instrs_eq :
    (s2StringBodyBody.findBlock "if.then20").map (·.instrs) =
      some s2StringBodyIfThen20Instrs := by decide

/-- **The `if.then20` arm's run**: a plain span is its own materialisation, so
`outn` takes its extent. -/
theorem s2StringBody_ifThen20_denote {calls : Calls} {env : Env} {s : State}
    {len : BitVec 64} {outn : Nat}
    (hlen : lookupName env "%len" = some (.int 64 len))
    (houtn : lookupName env "%outn" = some (.ptr outn)) :
    denoteCode calls s2StringBodyIfThen20Instrs (stateAt env s) =
      denoteCode calls []
        (stateAt env { s with mem := writeBytes s.mem outn (natToBytes len.toNat 8) }) := by
  dsimp only [s2StringBodyIfThen20Instrs]
  rw [denoteCode_store64 calls env s "%len" "%outn" hlen houtn []]

/-- The `if.end21` block's environment: the special byte's address, the byte, and
its test against the backslash. -/
def s2StringBodyIfEnd21Env (env : Env) (p : Nat) (call17 : BitVec 64)
    (bs : List UInt8) : Env :=
  ("%cmp24.not", .int 1 (evalICmpNat .eq 8
    (BitVec.ofNat 8 (bytesToNat bs)).toNat (0x5c#8).toNat)) ::
    ("%4", .int 8 (BitVec.ofNat 8 (bytesToNat bs))) ::
    ("%arrayidx22", .ptr (p + (call17.signExtend 64).toNat)) :: env

/-- The `if.end21` block's instruction list: the special byte's address, the byte,
and the test against the backslash. -/
def s2StringBodyIfEnd21Instrs : List Instr :=
  [Instr.gep "%arrayidx22" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%call17"),
   Instr.load "%4" (Ty.int 8) (Operand.reg "%arrayidx22"),
   Instr.icmp "%cmp24.not" (IPred.eq) 8 (Operand.reg "%4")
     (Operand.imm (Const.int 8 0x000000000000005c#8))]

theorem s2StringBodyIfEnd21Instrs_eq :
    (s2StringBodyBody.findBlock "if.end21").map (·.instrs) =
      some s2StringBodyIfEnd21Instrs := by decide

/-- **The `if.end21` block's run**: the special byte at the scan's offset, and the
test that tells a control byte from a backslash. -/
theorem s2StringBody_ifEnd21_denote {calls : Calls} {env : Env} {s : State}
    {p : Nat} {call17 : BitVec 64} {bs : List UInt8}
    (hp : lookupName env "%p" = some (.ptr p))
    (hcall17 : lookupName env "%call17" = some (.int 64 call17))
    (hpos : (call17.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (p + (call17.signExtend 64).toNat) 1 = some bs) :
    denoteCode calls s2StringBodyIfEnd21Instrs (stateAt env s) =
      denoteCode calls [] (stateAt (s2StringBodyIfEnd21Env env p call17 bs) s) := by
  dsimp only [s2StringBodyIfEnd21Instrs]
  rw [denoteCode_gep8_reg calls env s "%arrayidx22" "%p" "%call17" hp hcall17 hpos _]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_load8 calls
      (("%arrayidx22", .ptr (p + (call17.signExtend 64).toNat)) :: env) s
      "%4" "%arrayidx22" (by s2_lk) hb)]
  rw [denoteCode_icmp8_eq_imm calls
    (("%4", .int 8 (BitVec.ofNat 8 (bytesToNat bs))) ::
      ("%arrayidx22", .ptr (p + (call17.signExtend 64).toNat)) :: env) s
    "%cmp24.not" "%4" (by s2_lk) []]
  simp only [denoteCode_nil, s2StringBodyIfEnd21Env]

/-- The `if.then26` block's environment: the record's pointer, its three fields,
and the body-relative offset of the control byte. -/
def s2StringBodyIfThen26Env (env : Env) (off sub : BitVec 64) (c e : Nat) : Env :=
  ("%msg2.i.i97", .ptr (e + (16#64).toNat)) ::
    ("%off1.i.i96", .ptr (e + (8#64).toNat)) ::
    ("%c.val94", .ptr e) :: ("%5", .ptr (c + (1112#64).toNat)) ::
    ("%add27", .int 64 (off + sub)) :: env

def s2StringBodyIfThen26Mem (mem : Mem) (e : Nat) (off sub : BitVec 64) : Mem :=
  s2StringBodyIfThen12Mem mem e off sub

/-- The `if.then26` block's instruction list: the control byte's offset, the
record's pointer, and the record's three fields. -/
def s2StringBodyIfThen26Instrs : List Instr :=
  [Instr.binop "%add27" (BinOp.add) 64 (Operand.reg "%call17") (Operand.reg "%sub.ptr.sub"),
   Instr.gep "%5" (Ty.int 8) (Operand.reg "%c")
     (Operand.imm (Const.int 64 0x0000000000000458#64)),
   Instr.load "%c.val94" (Ty.ptr) (Operand.reg "%5"),
   Instr.store (Ty.int 32) (Operand.imm (Const.int 32 0x0000000000000000#32))
     (Operand.reg "%c.val94"),
   Instr.gep "%off1.i.i96" (Ty.int 8) (Operand.reg "%c.val94")
     (Operand.imm (Const.int 64 0x0000000000000008#64)),
   Instr.store (Ty.int 64) (Operand.reg "%add27") (Operand.reg "%off1.i.i96"),
   Instr.gep "%msg2.i.i97" (Ty.int 8) (Operand.reg "%c.val94")
     (Operand.imm (Const.int 64 0x0000000000000010#64)),
   Instr.store (Ty.ptr) (Operand.imm (Const.null)) (Operand.reg "%msg2.i.i97")]

theorem s2StringBodyIfThen26Instrs_eq :
    (s2StringBodyBody.findBlock "if.then26").map (·.instrs) =
      some s2StringBodyIfThen26Instrs := by decide

theorem s2StringBody_ifThen26_denote {calls : Calls} {env : Env} {s : State}
    {c e : Nat} {off sub : BitVec 64}
    (hc : lookupName env "%c" = some (.ptr c))
    (hcall17 : lookupName env "%call17" = some (.int 64 off))
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hcval : readBytes s.mem (c + (1112#64).toNat) 8 = some (wordBytes 8 e))
    (he64 : e < 2 ^ 64) :
    denoteCode calls s2StringBodyIfThen26Instrs (stateAt env s) =
      denoteCode calls []
        (stateAt (s2StringBodyIfThen26Env env off sub c e)
          { s with mem := s2StringBodyIfThen26Mem s.mem e off sub }) := by
  dsimp only [s2StringBodyIfThen26Instrs]
  rw [denoteCode_add_reg calls env s "%add27" "%call17" "%sub.ptr.sub" hcall17 hsub _]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_gep8_lit calls
      (("%add27", .int 64 (off + sub)) :: env) s "%5" "%c"
      (1112#64) (by s2_lk) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_loadPtr calls
      (("%5", .ptr (c + (1112#64).toNat)) ::
        ("%add27", .int 64 (off + sub)) :: env) s
      "%c.val94" "%5" (by s2_lk) hcval he64)]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_store32_imm calls
      (("%c.val94", .ptr e) :: ("%5", .ptr (c + (1112#64).toNat)) ::
        ("%add27", .int 64 (off + sub)) :: env) s
      "%c.val94" (by s2_lk))]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_gep8_lit calls
      (("%c.val94", .ptr e) :: ("%5", .ptr (c + (1112#64).toNat)) ::
        ("%add27", .int 64 (off + sub)) :: env)
      { s with mem := writeBytes s.mem e (natToBytes (0#32).toNat 4) }
      "%off1.i.i96" "%c.val94" (8#64) (by s2_lk) (by decide))]
  rw [denoteCode_store64 calls
    (("%off1.i.i96", .ptr (e + (8#64).toNat)) ::
      ("%c.val94", .ptr e) :: ("%5", .ptr (c + (1112#64).toNat)) ::
      ("%add27", .int 64 (off + sub)) :: env)
    { s with mem := writeBytes s.mem e (natToBytes (0#32).toNat 4) }
    "%add27" "%off1.i.i96" (by s2_lk) (by s2_lk) _]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_gep8_lit calls
      (("%off1.i.i96", .ptr (e + (8#64).toNat)) ::
        ("%c.val94", .ptr e) :: ("%5", .ptr (c + (1112#64).toNat)) ::
        ("%add27", .int 64 (off + sub)) :: env)
      { s with mem := (writeBytes (writeBytes s.mem e (natToBytes (0#32).toNat 4))
          (e + (8#64).toNat) (natToBytes (off + sub).toNat 8)) }
      "%msg2.i.i97" "%c.val94" (16#64) (by s2_lk) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_storePtr_null calls
      (("%msg2.i.i97", .ptr (e + (16#64).toNat)) ::
        ("%off1.i.i96", .ptr (e + (8#64).toNat)) ::
        ("%c.val94", .ptr e) :: ("%5", .ptr (c + (1112#64).toNat)) ::
        ("%add27", .int 64 (off + sub)) :: env)
      { s with mem := (writeBytes (writeBytes s.mem e (natToBytes (0#32).toNat 4))
          (e + (8#64).toNat) (natToBytes (off + sub).toNat 8)) }
      "%msg2.i.i97" (by s2_lk))]
  simp only [denoteCode_nil, s2StringBodyIfThen26Env, s2StringBodyIfThen26Mem,
    s2StringBodyIfThen12Mem]

/-- The `if.end29` block's environment: the slot, the suffix's length and address,
the decoder's answer, and its test. -/
def s2StringBodyIfEnd29Env (env : Env) (dst p : Nat) (call17 len call32 : BitVec 64) : Env :=
  ("%cmp33", .int 1 (evalICmp .eq call32 0xffffffffffffffff#64)) ::
    ("%call32", .int 64 call32) ::
    ("%add.ptr31", .ptr (dst + (call17.signExtend 64).toNat)) ::
    ("%sub", .int 64 (len - call17)) :: env

/-- The `if.end29` block's instruction list: the slot's clear, the suffix's extent
and address, the list-free decoder at four arguments, and its test. -/
def s2StringBodyIfEnd29Instrs : List Instr :=
  [Instr.store (Ty.int 64) (Operand.imm (Const.int 64 0x0000000000000000#64))
     (Operand.reg "%ei"),
   Instr.binop "%sub" (BinOp.sub) 64 (Operand.reg "%len") (Operand.reg "%call17"),
   Instr.gep "%add.ptr31" (Ty.int 8) (Operand.reg "%dst") (Operand.reg "%call17"),
   Instr.call "%call32" (Ty.int 64) "leanllvm_json_escape_decode"
     [(Ty.ptr, Operand.reg "%arrayidx22"), (Ty.int 64, Operand.reg "%sub"),
      (Ty.ptr, Operand.reg "%add.ptr31"), (Ty.ptr, Operand.reg "%ei")],
   Instr.icmp "%cmp33" (IPred.eq) 64 (Operand.reg "%call32")
     (Operand.imm (Const.int 64 0xffffffffffffffff#64))]

theorem s2StringBodyIfEnd29Instrs_eq :
    (s2StringBodyBody.findBlock "if.end29").map (·.instrs) =
      some s2StringBodyIfEnd29Instrs := by decide

/-- **The `if.end29` block's run**: the slot's clear, the suffix's length and
address, the list-free decoder, and the test of its answer. -/
theorem s2StringBody_ifEnd29_denote {env : Env} {s : State}
    {dst p ei : Nat} {call17 len call32 : BitVec 64} {m : Mem} {nx : Nat}
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
      some { ret := .int 64 call32, mem := m, next := nx }) :
    denoteCode s2StringBodyCalls s2StringBodyIfEnd29Instrs (stateAt env s) =
      denoteCode s2StringBodyCalls []
        (stateAt (s2StringBodyIfEnd29Env env dst p call17 len call32)
          { s with mem := m, next := nx }) := by
  dsimp only [s2StringBodyIfEnd29Instrs]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_store64_imm s2StringBodyCalls env s "%ei" (x := 0#64) hei)]
  rw [denoteCode_sub_reg s2StringBodyCalls env
    { s with mem := writeBytes s.mem ei (natToBytes (0#64).toNat 8) }
    "%sub" "%len" "%call17" hlen hcall17 _]
  rw [denoteCode_gep8_reg s2StringBodyCalls
    (("%sub", .int 64 (len - call17)) :: env)
    { s with mem := writeBytes s.mem ei (natToBytes (0#64).toNat 8) }
    "%add.ptr31" "%dst" "%call17" (by s2_lk) (by s2_lk) hpos _]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_call4 s2StringBodyCalls
      (("%add.ptr31", .ptr (dst + (call17.signExtend 64).toNat)) ::
        ("%sub", .int 64 (len - call17)) :: env)
      { s with mem := writeBytes s.mem ei (natToBytes (0#64).toNat 8) }
      "%call32" "leanllvm_json_escape_decode"
      (.reg "%arrayidx22") (.reg "%sub") (.reg "%add.ptr31") (.reg "%ei")
      (BlockEval.evalOperand_reg_of _ _ "%arrayidx22" (.ptr (p + (call17.signExtend 64).toNat)) harr)
      (BlockEval.evalOperand_reg_of _ _ "%sub" (.int 64 (len - call17)) (by s2_lk))
      (BlockEval.evalOperand_reg_of _ _ "%add.ptr31" (.ptr (dst + (call17.signExtend 64).toNat)) (by s2_lk))
      (BlockEval.evalOperand_reg_of _ _ "%ei" (.ptr ei) (by s2_lk))
      hc)]
  rw [denoteCode_icmp_eq_imm s2StringBodyCalls _ _ "%cmp33" "%call32" (by s2_lk) []]
  simp only [denoteCode_nil, s2StringBodyIfEnd29Env]

/-- The `if.then35` block's environment: the record's pointer, its three fields,
and the combined refusal offset (`pos0 + the scan's answer + the decoder's`). -/
def s2StringBodyIfThen35Env (env : Env) (off sub rel : BitVec 64) (c e : Nat) : Env :=
  ("%msg2.i.i99", .ptr (e + (16#64).toNat)) ::
    ("%off1.i.i98", .ptr (e + (8#64).toNat)) ::
    ("%c.val", .ptr e) :: ("%7", .ptr (c + (1112#64).toNat)) ::
    ("%add37", .int 64 (off + sub + rel)) ::
    ("%6", .int 64 rel) :: ("%add36", .int 64 (off + sub)) :: env

def s2StringBodyIfThen35Mem (mem : Mem) (e : Nat) (v : BitVec 64) : Mem :=
  writeBytes
    (writeBytes (writeBytes mem e (natToBytes (0#32).toNat 4))
      (e + (8#64).toNat) (natToBytes v.toNat 8))
    (e + (16#64).toNat) (natToBytes 0 8)

/-- The `if.then35` block's instruction list: the combined offset, the record's
pointer, and the record's three fields. -/
def s2StringBodyIfThen35Instrs : List Instr :=
  [Instr.binop "%add36" (BinOp.add) 64 (Operand.reg "%call17") (Operand.reg "%sub.ptr.sub"),
   Instr.load "%6" (Ty.int 64) (Operand.reg "%ei"),
   Instr.binop "%add37" (BinOp.add) 64 (Operand.reg "%add36") (Operand.reg "%6"),
   Instr.gep "%7" (Ty.int 8) (Operand.reg "%c")
     (Operand.imm (Const.int 64 0x0000000000000458#64)),
   Instr.load "%c.val" (Ty.ptr) (Operand.reg "%7"),
   Instr.store (Ty.int 32) (Operand.imm (Const.int 32 0x0000000000000000#32))
     (Operand.reg "%c.val"),
   Instr.gep "%off1.i.i98" (Ty.int 8) (Operand.reg "%c.val")
     (Operand.imm (Const.int 64 0x0000000000000008#64)),
   Instr.store (Ty.int 64) (Operand.reg "%add37") (Operand.reg "%off1.i.i98"),
   Instr.gep "%msg2.i.i99" (Ty.int 8) (Operand.reg "%c.val")
     (Operand.imm (Const.int 64 0x0000000000000010#64)),
   Instr.store (Ty.ptr) (Operand.imm (Const.null)) (Operand.reg "%msg2.i.i99")]

theorem s2StringBodyIfThen35Instrs_eq :
    (s2StringBodyBody.findBlock "if.then35").map (·.instrs) =
      some s2StringBodyIfThen35Instrs := by decide

theorem s2StringBody_ifThen35_denote {calls : Calls} {env : Env} {s : State}
    {c ei e : Nat} {off sub rel : BitVec 64}
    (hc : lookupName env "%c" = some (.ptr c))
    (hei : lookupName env "%ei" = some (.ptr ei))
    (hcall17 : lookupName env "%call17" = some (.int 64 off))
    (hsub : lookupName env "%sub.ptr.sub" = some (.int 64 sub))
    (hrel : readBytes s.mem ei 8 = some (natToBytes rel.toNat 8))
    (hcval : readBytes s.mem (c + (1112#64).toNat) 8 = some (wordBytes 8 e))
    (he64 : e < 2 ^ 64) :
    denoteCode calls s2StringBodyIfThen35Instrs (stateAt env s) =
      denoteCode calls []
        (stateAt (s2StringBodyIfThen35Env env off sub rel c e)
          { s with mem := s2StringBodyIfThen35Mem s.mem e (off + sub + rel) }) := by
  dsimp only [s2StringBodyIfThen35Instrs]
  rw [denoteCode_add_reg calls env s "%add36" "%call17" "%sub.ptr.sub" hcall17 hsub _]
  rw [denoteCode_load64 (v := rel) calls (("%add36", .int 64 (off + sub)) :: env) s
    "%6" "%ei" (by simpa [lookupName] using hei) hrel _]
  rw [denoteCode_add_reg calls
    (("%6", .int 64 rel) :: ("%add36", .int 64 (off + sub)) :: env) s
    "%add37" "%add36" "%6" (by s2_lk) (by s2_lk) _]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_gep8_lit calls
      (("%add37", .int 64 (off + sub + rel)) ::
        ("%6", .int 64 rel) :: ("%add36", .int 64 (off + sub)) :: env) s "%7" "%c"
      (1112#64) (by s2_lk) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_loadPtr calls
      (("%7", .ptr (c + (1112#64).toNat)) ::
        ("%add37", .int 64 (off + sub + rel)) ::
        ("%6", .int 64 rel) :: ("%add36", .int 64 (off + sub)) :: env) s
      "%c.val" "%7" (by s2_lk) hcval he64)]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_store32_imm calls
      (("%c.val", .ptr e) :: ("%7", .ptr (c + (1112#64).toNat)) ::
        ("%add37", .int 64 (off + sub + rel)) ::
        ("%6", .int 64 rel) :: ("%add36", .int 64 (off + sub)) :: env) s
      "%c.val" (by s2_lk))]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_gep8_lit calls
      (("%c.val", .ptr e) :: ("%7", .ptr (c + (1112#64).toNat)) ::
        ("%add37", .int 64 (off + sub + rel)) ::
        ("%6", .int 64 rel) :: ("%add36", .int 64 (off + sub)) :: env)
      { s with mem := writeBytes s.mem e (natToBytes (0#32).toNat 4) }
      "%off1.i.i98" "%c.val" (8#64) (by s2_lk) (by decide))]
  rw [denoteCode_store64 calls
    (("%off1.i.i98", .ptr (e + (8#64).toNat)) ::
      ("%c.val", .ptr e) :: ("%7", .ptr (c + (1112#64).toNat)) ::
      ("%add37", .int 64 (off + sub + rel)) ::
      ("%6", .int 64 rel) :: ("%add36", .int 64 (off + sub)) :: env)
    { s with mem := writeBytes s.mem e (natToBytes (0#32).toNat 4) }
    "%add37" "%off1.i.i98" (by s2_lk) (by s2_lk) _]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_gep8_lit calls
      (("%off1.i.i98", .ptr (e + (8#64).toNat)) ::
        ("%c.val", .ptr e) :: ("%7", .ptr (c + (1112#64).toNat)) ::
        ("%add37", .int 64 (off + sub + rel)) ::
        ("%6", .int 64 rel) :: ("%add36", .int 64 (off + sub)) :: env)
      { s with mem := (writeBytes (writeBytes s.mem e (natToBytes (0#32).toNat 4))
          (e + (8#64).toNat) (natToBytes (off + sub + rel).toNat 8)) }
      "%msg2.i.i99" "%c.val" (16#64) (by s2_lk) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_storePtr_null calls
      (("%msg2.i.i99", .ptr (e + (16#64).toNat)) ::
        ("%off1.i.i98", .ptr (e + (8#64).toNat)) ::
        ("%c.val", .ptr e) :: ("%7", .ptr (c + (1112#64).toNat)) ::
        ("%add37", .int 64 (off + sub + rel)) ::
        ("%6", .int 64 rel) :: ("%add36", .int 64 (off + sub)) :: env)
      { s with mem := (writeBytes (writeBytes s.mem e (natToBytes (0#32).toNat 4))
          (e + (8#64).toNat) (natToBytes (off + sub + rel).toNat 8)) }
      "%msg2.i.i99" (by s2_lk))]
  simp only [denoteCode_nil, s2StringBodyIfThen35Env, s2StringBodyIfThen35Mem]

/-- The `if.end39` block's environment: the test that picks the exact prefix copy. -/
def s2StringBodyIfEnd39Env (env : Env) (call17 : BitVec 64) : Env :=
  ("%tobool40.not", .int 1 (evalICmp .eq call17 (BitVec.ofNat 64 0))) :: env

/-- The `if.end39` block's instruction list: the zero-prefix test. -/
def s2StringBodyIfEnd39Instrs : List Instr :=
  [Instr.icmp "%tobool40.not" (IPred.eq) 64 (Operand.reg "%call17")
     (Operand.imm (Const.int 64 0x0000000000000000#64))]

theorem s2StringBodyIfEnd39Instrs_eq :
    (s2StringBodyBody.findBlock "if.end39").map (·.instrs) =
      some s2StringBodyIfEnd39Instrs := by decide

/-- **The `if.end39` block's run**: the zero-prefix test. -/
theorem s2StringBody_ifEnd39_denote {calls : Calls} {env : Env} {s : State}
    {call17 : BitVec 64}
    (hcall17 : lookupName env "%call17" = some (.int 64 call17)) :
    denoteCode calls s2StringBodyIfEnd39Instrs (stateAt env s) =
      denoteCode calls [] (stateAt (s2StringBodyIfEnd39Env env call17) s) := by
  dsimp only [s2StringBodyIfEnd39Instrs]
  rw [denoteCode_icmp_eq_imm calls env s "%tobool40.not" "%call17" hcall17 []]
  simp only [denoteCode_nil, s2StringBodyIfEnd39Env]

/-- The `if.then41` block's instruction list: the exact prefix copy. -/
def s2StringBodyIfThen41Instrs : List Instr :=
  [Instr.callVoid "llvm.memcpy.p0.p0.i64"
     [(Ty.ptr, Operand.reg "%dst"), (Ty.ptr, Operand.reg "%p"),
      (Ty.int 64, Operand.reg "%call17"), (Ty.int 1, Operand.imm (Const.int 1 0x0#1))]]

theorem s2StringBodyIfThen41Instrs_eq :
    (s2StringBodyBody.findBlock "if.then41").map (·.instrs) =
      some s2StringBodyIfThen41Instrs := by decide

/-- **The `if.then41` block's run**: the exact prefix copy, `call17` bytes from
the body's start to the destination's start. -/
theorem s2StringBody_ifThen41_denote {env : Env} {s : State}
    {dst p : Nat} {call17 : BitVec 64} {m : Mem} {nx : Nat}
    (hdst : lookupName env "%dst" = some (.ptr dst))
    (hp : lookupName env "%p" = some (.ptr p))
    (hcall17 : lookupName env "%call17" = some (.int 64 call17))
    (hc : s2StringBodyCalls "llvm.memcpy.p0.p0.i64"
      [.ptr dst, .ptr p, .int 64 call17, .int 1 0] s.mem s.next =
      some { ret := .int 1 0, mem := m, next := nx }) :
    denoteCode s2StringBodyCalls s2StringBodyIfThen41Instrs (stateAt env s) =
      denoteCode s2StringBodyCalls []
        (stateAt env { s with mem := m, next := nx }) := by
  dsimp only [s2StringBodyIfThen41Instrs]
  refine (denoteCode_cons_of _ _ _ _ _
    (sb_step_callVoid4 s2StringBodyCalls env s "llvm.memcpy.p0.p0.i64"
      (.reg "%dst") (.reg "%p") (.reg "%call17") (.imm (.int 1 0))
      (BlockEval.evalOperand_reg_of env s "%dst" (.ptr dst) hdst)
      (BlockEval.evalOperand_reg_of env s "%p" (.ptr p) hp)
      (BlockEval.evalOperand_reg_of env s "%call17" (.int 64 call17) hcall17)
      (by simp only [evalOperand, Const.toValue]) hc)).trans ?_
  simp only [denoteCode_nil]

/-- The `if.end43` block's instruction list: the decoded length's sum and its
write to `outn`. -/
def s2StringBodyIfEnd43Instrs : List Instr :=
  [Instr.binop "%add44" (BinOp.add) 64 (Operand.reg "%call32") (Operand.reg "%call17"),
   Instr.store (Ty.int 64) (Operand.reg "%add44") (Operand.reg "%outn")]

theorem s2StringBodyIfEnd43Instrs_eq :
    (s2StringBodyBody.findBlock "if.end43").map (·.instrs) =
      some s2StringBodyIfEnd43Instrs := by decide

/-- **The `if.end43` block's run**: the decoded length is the prefix plus the
suffix's decoded extent, written at `outn`. -/
theorem s2StringBody_ifEnd43_denote {calls : Calls} {env : Env} {s : State}
    {call17 call32 : BitVec 64} {outn : Nat}
    (hcall32 : lookupName env "%call32" = some (.int 64 call32))
    (hcall17 : lookupName env "%call17" = some (.int 64 call17))
    (houtn : lookupName env "%outn" = some (.ptr outn)) :
    denoteCode calls s2StringBodyIfEnd43Instrs (stateAt env s) =
      denoteCode calls []
        (stateAt
          (("%add44", .int 64 (call32 + call17)) :: env)
          { s with mem := writeBytes s.mem outn (natToBytes (call32 + call17).toNat 8) }) := by
  dsimp only [s2StringBodyIfEnd43Instrs]
  rw [denoteCode_add_reg calls env s "%add44" "%call32" "%call17" hcall32 hcall17 _]
  rw [denoteCode_store64 calls (("%add44", .int 64 (call32 + call17)) :: env) s
    "%add44" "%outn" (by s2_lk) houtn []]

/-! ### The merged cleanup

`cleanup47` is the two-arm body's single exit: a seven-edge `phi` selecting the
returned form, and the slot's end marker. -/

/-- The `cleanup47` block's instruction list: the seven-edge `phi` and the end
marker. -/
def s2StringBodyCleanup47Instrs : List Instr :=
  [Instr.phi "%retval.3" (Ty.int 32)
     [("if.then9", Operand.imm (Const.int 32 0x0000000000000001#32)),
      ("if.then12", Operand.imm (Const.int 32 0x0000000000000000#32)),
      ("if.end15", Operand.imm (Const.int 32 0x0000000000000002#32)),
      ("if.then20", Operand.imm (Const.int 32 0x0000000000000001#32)),
      ("if.then26", Operand.imm (Const.int 32 0x0000000000000000#32)),
      ("if.then35", Operand.imm (Const.int 32 0x0000000000000000#32)),
      ("if.end43", Operand.imm (Const.int 32 0x0000000000000002#32))],
   Instr.callVoid "llvm.lifetime.end.p0"
     [(Ty.int 64, Operand.imm (Const.int 64 0x0000000000000008#64)),
      (Ty.ptr, Operand.reg "%ei")]]

theorem s2StringBodyCleanup47Instrs_eq :
    (s2StringBodyBody.findBlock "cleanup47").map (·.instrs) =
      some s2StringBodyCleanup47Instrs := by decide

/-- **The `cleanup47` block's run**: the form's `phi`, and the marker — an identity
step at this environment, so the block's memory and cursor are the edge's. -/
theorem s2StringBody_cleanup47_denote {env : Env} {s : State}
    {p : String} {op : Operand} {form : BitVec 32} {ei : Nat}
    (hpre : s.pre = some p)
    (hinc : phiIncoming p
      [("if.then9", Operand.imm (Const.int 32 0x0000000000000001#32)),
       ("if.then12", Operand.imm (Const.int 32 0x0000000000000000#32)),
       ("if.end15", Operand.imm (Const.int 32 0x0000000000000002#32)),
       ("if.then20", Operand.imm (Const.int 32 0x0000000000000001#32)),
       ("if.then26", Operand.imm (Const.int 32 0x0000000000000000#32)),
       ("if.then35", Operand.imm (Const.int 32 0x0000000000000000#32)),
       ("if.end43", Operand.imm (Const.int 32 0x0000000000000002#32))] = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 32 form))
    (hei : lookupName env "%ei" = some (.ptr ei)) :
    denoteCode s2StringBodyCalls s2StringBodyCleanup47Instrs (stateAt env s) =
      denoteCode s2StringBodyCalls []
        (stateAt (("%retval.3", .int 32 form) :: env) s) := by
  dsimp only [s2StringBodyCleanup47Instrs]
  rw [denoteCode_phi s2StringBodyCalls env s "%retval.3" (Ty.int 32) _ hpre hinc hop _
    (by decide)]
  rw [denoteCode_cons_of _ _ _ _ _
    (sb_step_lifetime (("%retval.3", .int 32 form) :: env) s ei
      "llvm.lifetime.end.p0" (Or.inr rfl) (by s2_lk))]

end LeanLLVM.Refinement
