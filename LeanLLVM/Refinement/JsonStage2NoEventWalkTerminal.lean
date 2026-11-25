/-
The no-event walk's terminal arms: the refusal block, the acceptance, and the
empty-stream flush.

`JsonStage2NoEventWalkInv` states the walk's invariant, its one separation surface
and its seed.  This module proves the run each terminal exit makes from the state
the loop leaves at it, and the record's post at the memory those stores produce:

* **the refusal** (`if.then527`): the block's leading `%ei520.0.ph` `phi` selects
  an operand at the predecessor the literal chain left — an immediate for the
  differing-byte and shorter-token sites, or `%sub524`/`%ln.0` for the token that
  overruns the literal — and that operand's word is the offset's low part.  Then
  `%add529 = ei + %idxprom.lcssa`, the store at `%off`, the `od_gap_recover` call
  at `stage2GapRecover`, the three zero stores, the `%off` load and the `%err`
  store.
* **the acceptance** (`accept`): the three stores, with the count in both word
  slots and the arena's running sum added to the terms.
* **the flush** (`if.then`): the empty stream's three zero stores and the
  document's length at `%err`.

The composition is the tree's, not one block-wide `denoteCode` term: each step is
a lemma concluding at a **named state** (`stage2NoEventRefusalS1`…`S6`), composed
by `denoteCode`/`step` transitivity in the `WalkLink` idiom, and a step covers at
most three instructions.  The register facts the steps read are the state's own,
through `Stage2NoEventWalkParams`, `Stage2NoEventWalkLocals` and — for the
acceptance — `Stage2NoEventWalkAcc`; no arm carries a separation fact, because
`Stage2NoEventWalkInv.sep` is the one surface.

Each arm ends at `cleanup580`'s `phi` (zero for the refusal and the flush, one for
the acceptance), the four lifetime markers' `end`s, and the `ret`.  The markers
write nothing and allocate nothing, so the returned memory is the arm's own
stores.  The post is `stage2NoEventBoundary` at the arm's verdict and memory.

**What this module does not do.**  It does not prove the loop: the acceptance
carries the parse relation `Stage2NoEvent bs arena obs toks` and its fold facts as
premises, which the loop's completion is to supply, and the refusal carries the
gap call's footprint — the helper's write is inside `%e`'s record, which the
cursor record's own contents fix.  The continuing loop is the next sub-milestone
and the premise tier the one after it.

**The refusal's `%off` word.**  The helper may write the record's offset, and the
last write at `%e + 8` is what `%74` reads.  The arm therefore takes the observed
word `eoff` with its read-back and its bound: when the rule answers `.unchanged`
the word is the block's own `ei + idx`, and when it answers `.wrote _ off _` it is
the helper's `off`, which the rule's own site bound places inside the document.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkInv
import LeanLLVM.Refinement.JsonStage2NoEventLiteral

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

/-! ### The terminal blocks, pinned -/

/-- `cleanup580`'s `%retval.14` incoming list, in the fixture's order.  Every
predecessor binds the arm's literal verdict: one for `accept`, zero for the three
refusal copies and the rest. -/
def cleanup580Incoming : List (String × Operand) :=
  [("if.then", Operand.imm (.int 64 (BitVec.ofNat 64 0))),
   ("if.then12", Operand.imm (.int 64 (BitVec.ofNat 64 0))),
   ("if.then68", Operand.imm (.int 64 (BitVec.ofNat 64 0))),
   ("if.then360", Operand.imm (.int 64 (BitVec.ofNat 64 0))),
   ("accept", Operand.imm (.int 64 (BitVec.ofNat 64 1))),
   ("if.then372", Operand.imm (.int 64 (BitVec.ofNat 64 0))),
   ("if.then402", Operand.imm (.int 64 (BitVec.ofNat 64 0))),
   ("if.then105", Operand.imm (.int 64 (BitVec.ofNat 64 0))),
   ("if.then118", Operand.imm (.int 64 (BitVec.ofNat 64 0))),
   ("if.then297", Operand.imm (.int 64 (BitVec.ofNat 64 0))),
   ("if.then311", Operand.imm (.int 64 (BitVec.ofNat 64 0))),
   ("if.then428", Operand.imm (.int 64 (BitVec.ofNat 64 0))),
   ("if.then94", Operand.imm (.int 64 (BitVec.ofNat 64 0))),
   ("if.then38", Operand.imm (.int 64 (BitVec.ofNat 64 0))),
   ("if.then321", Operand.imm (.int 64 (BitVec.ofNat 64 0))),
   ("cleanup.thread", Operand.imm (.int 64 (BitVec.ofNat 64 0))),
   ("cleanup287.thread", Operand.imm (.int 64 (BitVec.ofNat 64 0))),
   ("if.then562", Operand.imm (.int 64 (BitVec.ofNat 64 0))),
   ("cleanup491.thread", Operand.imm (.int 64 (BitVec.ofNat 64 0))),
   ("if.else510", Operand.imm (.int 64 (BitVec.ofNat 64 0))),
   ("if.then527", Operand.imm (.int 64 (BitVec.ofNat 64 0)))]

/-- `if.then527`'s instructions after its `%ei520.0.ph` `phi`, up to and
including the three zero stores.  The split is the load's: it reads the refusal
word after the stores, so its own step runs at the stores' named memory. -/
def refusalPrefixInstrs : List Instr :=
  [ Instr.binop "%add529" BinOp.add 64 (Operand.reg "%ei520.0.ph")
      (Operand.reg "%idxprom.lcssa"),
    Instr.store (Ty.int 64) (Operand.reg "%add529") (Operand.reg "%off"),
    Instr.callVoid "od_gap_recover"
      [((Ty.ptr), (Operand.reg "%c")), ((Ty.int 64), (Operand.reg "%idxprom.lcssa"))],
    Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
      (Operand.reg "%tokens_out"),
    Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
      (Operand.reg "%values_out"),
    Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
      (Operand.reg "%sum_out")]

/-- The `%off` load and the `%err` store, after the three zero stores. -/
def refusalTailInstrs : List Instr :=
  [ Instr.load "%74" (Ty.int 64) (Operand.reg "%off"),
    Instr.store (Ty.int 64) (Operand.reg "%74") (Operand.reg "%err")]

/-- `if.then527`'s instructions after its `%ei520.0.ph` `phi`. -/
def refusalRestInstrs : List Instr :=
  refusalPrefixInstrs ++ refusalTailInstrs

/-- `if.then527`: the `%ei520.0.ph` `phi`, the offset, the helper call and the
refusal stores. -/
def refusalInstrs : List Instr :=
  Instr.phi "%ei520.0.ph" (Ty.int 64) ifThen527EiIncoming :: refusalRestInstrs

/-- `if.then527`, pinned. -/
def refusalBlock : Block :=
  { name := "if.then527", instrs := refusalInstrs, term := Term.br "cleanup580" }

theorem refusalBlock_find : stage2NoEventBody.findBlock "if.then527" = some refusalBlock := by
  decide

/-- `cleanup580`: the verdict `phi`, the four lifetime markers' ends and the
return. -/
def cleanup580Instrs : List Instr :=
  [ Instr.phi "%retval.14" (Ty.int 64) cleanup580Incoming,
    Instr.callVoid "llvm.lifetime.end.p0"
      [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 1192)))),
        (Ty.ptr, (Operand.reg "%c"))],
    Instr.callVoid "llvm.lifetime.end.p0"
      [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 24)))),
        (Ty.ptr, (Operand.reg "%e"))],
    Instr.callVoid "llvm.lifetime.end.p0"
      [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 520)))),
        (Ty.ptr, (Operand.reg "%stk"))],
    Instr.callVoid "llvm.lifetime.end.p0"
      [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))),
        (Ty.ptr, (Operand.reg "%xj"))]]

/-- `cleanup580`, pinned. -/
def cleanup580Block : Block :=
  { name := "cleanup580", instrs := cleanup580Instrs,
    term := Term.ret (Ty.int 64) (some (Operand.reg "%retval.14")) }

theorem cleanup580Block_find : stage2NoEventBody.findBlock "cleanup580" = some cleanup580Block := by
  decide

/-- `accept`'s three stores, in the fixture's order (the sum's add sits between
the second and third). -/
def acceptInstrs : List Instr :=
  [ Instr.store (Ty.int 64) (Operand.reg "%tokens.8") (Operand.reg "%tokens_out"),
    Instr.store (Ty.int 64) (Operand.reg "%tokens.8") (Operand.reg "%values_out"),
    Instr.binop "%add579" BinOp.add 64 (Operand.reg "%terms.8")
      (Operand.reg "%arena.10"),
    Instr.store (Ty.int 64) (Operand.reg "%add579") (Operand.reg "%sum_out")]

/-- `accept`, pinned. -/
def acceptBlock : Block :=
  { name := "accept", instrs := acceptInstrs, term := Term.br "cleanup580" }

theorem acceptBlock_find : stage2NoEventBody.findBlock "accept" = some acceptBlock := by
  decide

/-- `if.then`'s empty-stream stores: the three zeroes and the document's length
at `%err`. -/
def flushInstrs : List Instr :=
  [ Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
      (Operand.reg "%tokens_out"),
    Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
      (Operand.reg "%values_out"),
    Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
      (Operand.reg "%sum_out"),
    Instr.store (Ty.int 64) (Operand.reg "%n") (Operand.reg "%err")]

/-- `if.then`, pinned. -/
def flushBlock : Block :=
  { name := "if.then", instrs := flushInstrs, term := Term.br "cleanup580" }

theorem flushBlock_find : stage2NoEventBody.findBlock "if.then" = some flushBlock := by
  decide

-- The pins are of the parsed body, not of a transcription: each name resolves,
-- and `cleanup580`'s phi is the pinned list at both terminals' selectors.
#guard decide (stage2NoEventBody.findBlock "if.then527" ≠ none)
#guard decide (stage2NoEventBody.findBlock "accept" ≠ none)
#guard decide (stage2NoEventBody.findBlock "if.then" ≠ none)
#guard decide
  (litPhiIncoming ((stage2NoEventBody.findBlock "cleanup580").getD
      ⟨"", [], .unreachable⟩) "%retval.14" = some cleanup580Incoming)
#guard decide
  (litPhiIncoming ((stage2NoEventBody.findBlock "if.then527").getD
      ⟨"", [], .unreachable⟩) "%ei520.0.ph" = some ifThen527EiIncoming)

/-! ### The arms' memories, named

A literal four-deep `writeBytes` in a theorem's type is re-elaborated at every
use; the names are what keep the arm statements and their read-backs readable. -/

/-- A state with the caller's registers, block and predecessor, and a new memory
and allocator cursor; the shape every straight-line step here leaves. -/
def stage2NoEventStepState (s : State) (m : Mem) (n : Nat) : State :=
  { env := s.env, mem := m, next := n, pc := s.pc, pre := s.pre }

/-- A step's state with the block and predecessor its terminator delivers. -/
def stage2NoEventJumpState (s : State) (m : Mem) (n : Nat) (pc pre : String) : State :=
  { env := s.env, mem := m, next := n, pc := pc, pre := some pre }

/-- The three zero stores at the caller's output slots. -/
def stage2NoEventZeroMem (m : Mem) (tokensOut valuesOut sumOut : Nat) : Mem :=
  writeBytes (writeBytes (writeBytes m tokensOut (wordBytes 8 0)) valuesOut
    (wordBytes 8 0)) sumOut (wordBytes 8 0)

/-- Three zero stores and one word at `%err`: the refusal's memory (the word is
the observed `%off`) and the flush's (the word is the document's length). -/
def stage2NoEventErrMem (m : Mem) (tokensOut valuesOut sumOut err : Nat)
    (v : BitVec 64) : Mem :=
  writeBytes (stage2NoEventZeroMem m tokensOut valuesOut sumOut) err
    (natToBytes v.toNat 8)

/-- The acceptance's three stores: the count in both word slots and the sum. -/
def stage2NoEventAcceptMem (m : Mem) (tokensOut valuesOut sumOut : Nat)
    (tok sum : BitVec 64) : Mem :=
  writeBytes (writeBytes (writeBytes m tokensOut (wordBytes 8 tok.toNat)) valuesOut
    (wordBytes 8 tok.toNat)) sumOut (wordBytes 8 sum.toNat)

/-! ### The refusal's named states

Each is a top-level state the block's run reaches: the `phi`, the offset and its
store, the helper call, the three zero stores, the load, and the error store.  A
step lemma's conclusion is one of these, and the composition is `Eq.trans` along
the block's own instruction list. -/

/-- The environment after the `%ei520.0.ph` `phi`. -/
def stage2NoEventRefusalEnv1 (env : Env) (ei : BitVec 64) : Env :=
  ("%ei520.0.ph", .int 64 ei) :: env

/-- The environment after `%add529 = ei + idx`. -/
def stage2NoEventRefusalEnv2 (env : Env) (ei idx : BitVec 64) : Env :=
  ("%add529", .int 64 (ei + idx)) :: stage2NoEventRefusalEnv1 env ei

/-- The environment after the `%74` load. -/
def stage2NoEventRefusalEnv3 (env : Env) (ei idx eoff : BitVec 64) : Env :=
  ("%74", .int 64 eoff) :: stage2NoEventRefusalEnv2 env ei idx

/-- After the `%ei520.0.ph` `phi`. -/
def stage2NoEventRefusalS1 (env : Env) (s : State) (ei : BitVec 64) : State :=
  stateAt (stage2NoEventRefusalEnv1 env ei) s

/-- After `%add529` and the store at `%off`. -/
def stage2NoEventRefusalS2 (env : Env) (s : State) (ei idx : BitVec 64) (q : Nat) :
    State :=
  stateAt (stage2NoEventRefusalEnv2 env ei idx)
    (stage2NoEventStepState s
      (writeBytes s.mem q (natToBytes (ei + idx).toNat 8)) s.next)

/-- After the helper call. -/
def stage2NoEventRefusalS3 (env : Env) (s : State) (ei idx : BitVec 64)
    (rc : CallOutcome) : State :=
  stateAt (stage2NoEventRefusalEnv2 env ei idx)
    (stage2NoEventStepState s rc.mem rc.next)

/-- After the three zero stores. -/
def stage2NoEventRefusalS4 (env : Env) (s : State) (ei idx : BitVec 64)
    (rc : CallOutcome) (tokensOut valuesOut sumOut : Nat) : State :=
  stateAt (stage2NoEventRefusalEnv2 env ei idx)
    (stage2NoEventStepState s
      (stage2NoEventZeroMem rc.mem tokensOut valuesOut sumOut) rc.next)

/-- After the `%74` load. -/
def stage2NoEventRefusalS5 (env : Env) (s : State) (ei idx : BitVec 64)
    (rc : CallOutcome) (tokensOut valuesOut sumOut : Nat) (eoff : BitVec 64) : State :=
  stateAt (stage2NoEventRefusalEnv3 env ei idx eoff)
    (stage2NoEventStepState s
      (stage2NoEventZeroMem rc.mem tokensOut valuesOut sumOut) rc.next)

/-- After the `%err` store: the block's last instruction. -/
def stage2NoEventRefusalS6 (env : Env) (s : State) (ei idx : BitVec 64)
    (rc : CallOutcome) (tokensOut valuesOut sumOut err : Nat) (eoff : BitVec 64) : State :=
  stateAt (stage2NoEventRefusalEnv3 env ei idx eoff)
    (stage2NoEventStepState s
      (stage2NoEventErrMem rc.mem tokensOut valuesOut sumOut err eoff) rc.next)

/-- **The state the refusal's branch delivers to `cleanup580`.** -/
def stage2NoEventRefusalTarget (env : Env) (s : State) (ei idx : BitVec 64)
    (rc : CallOutcome) (tokensOut valuesOut sumOut err : Nat) (eoff : BitVec 64) : State :=
  stateAt (stage2NoEventRefusalEnv3 env ei idx eoff)
    (stage2NoEventJumpState s
      (stage2NoEventErrMem rc.mem tokensOut valuesOut sumOut err eoff) rc.next
      "cleanup580" "if.then527")

/-- A name the refusal's `phi` and offset steps did not bind reads through the
block's entry environment: one lemma per register the return block needs. -/
theorem lookupName_refusalEnv3_c (env : Env) (ei idx eoff : BitVec 64) :
    lookupName (stage2NoEventRefusalEnv3 env ei idx eoff) "%c" = lookupName env "%c" := by
  simp only [stage2NoEventRefusalEnv3, stage2NoEventRefusalEnv2,
    stage2NoEventRefusalEnv1]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

theorem lookupName_refusalEnv3_e (env : Env) (ei idx eoff : BitVec 64) :
    lookupName (stage2NoEventRefusalEnv3 env ei idx eoff) "%e" = lookupName env "%e" := by
  simp only [stage2NoEventRefusalEnv3, stage2NoEventRefusalEnv2,
    stage2NoEventRefusalEnv1]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

theorem lookupName_refusalEnv3_stk (env : Env) (ei idx eoff : BitVec 64) :
    lookupName (stage2NoEventRefusalEnv3 env ei idx eoff) "%stk" = lookupName env "%stk" := by
  simp only [stage2NoEventRefusalEnv3, stage2NoEventRefusalEnv2,
    stage2NoEventRefusalEnv1]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

theorem lookupName_refusalEnv3_xj (env : Env) (ei idx eoff : BitVec 64) :
    lookupName (stage2NoEventRefusalEnv3 env ei idx eoff) "%xj" = lookupName env "%xj" := by
  simp only [stage2NoEventRefusalEnv3, stage2NoEventRefusalEnv2,
    stage2NoEventRefusalEnv1]
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-! ### One step at a block, and the instruction steps -/

/-- One control step from a block's run: `step` at a state whose program counter
finds `b`, whose instructions denote to `s'`, and whose terminator is `c`. -/
theorem stage2NoEventWalk_step_at_block {calls : Calls} {f : Function}
    {s s' : State} {b : Block} {c : Ctrl} (hfind : f.findBlock s.pc = some b)
    (hcode : denoteCode calls b.instrs s = some s')
    (hterm : execTerm s' b.term = c) : step calls f s = c := by
  simp only [step, hfind, hcode, hterm]

/-- A store of a 64-bit immediate, as a chain step. -/
theorem stage2NoEventWalk_denote_store64_imm (calls : Calls) (env : Env) (s : State)
    (x : BitVec 64) (p : String) {a : Nat}
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store (.int 64) (.imm (.int 64 x)) (.reg p) :: is)
        (stateAt env s) =
      denoteCode calls is
        (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 8) }) := by
  have hstep : evalInstr calls (stateAt env s)
      (.store (.int 64) (.imm (.int 64 x)) (.reg p)) =
      some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 8) }) := by
    have h1 : evalOperand (stateAt env s) (.imm (.int 64 x)) = some (.int 64 x) := rfl
    have h2 : evalOperand (stateAt env s) (.reg p) = some (.ptr a) :=
      evalOperand_reg_of env s p (.ptr a) hp
    unfold evalInstr
    dsimp only
    rw [h1, h2]
    simp [State.bind, stateAt, storeValue]
  rw [denoteCode_cons_of _ _ _ _ _ hstep]

/-- `%add529 = ei + idx` and the store at `%off`, as one named step: the offset
address is the caller's `q`, which the invariant's `%off` binding fixes at
`%e + 8`. -/
theorem stage2NoEventWalk_denote_add_store (calls : Calls) (env : Env) (s : State)
    {ei idx : BitVec 64} {q : Nat}
    (heip : lookupName env "%ei520.0.ph" = some (.int 64 ei))
    (hidx : lookupName env "%idxprom.lcssa" = some (.int 64 idx))
    (hoff : lookupName env "%off" = some (.ptr q))
    (is : List Instr) :
    denoteCode calls (Instr.binop "%add529" BinOp.add 64 (Operand.reg "%ei520.0.ph")
        (Operand.reg "%idxprom.lcssa") ::
      Instr.store (Ty.int 64) (Operand.reg "%add529") (Operand.reg "%off") :: is)
      (stateAt env s) =
      denoteCode calls is
        (stateAt (("%add529", .int 64 (ei + idx)) :: env)
          (stage2NoEventStepState s
            (writeBytes s.mem q (natToBytes (ei + idx).toNat 8)) s.next)) := by
  rw [denoteCode_add_reg (calls := calls) (env := env) (s := s) "%add529"
    "%ei520.0.ph" "%idxprom.lcssa" heip hidx
    (Instr.store (Ty.int 64) (Operand.reg "%add529") (Operand.reg "%off") :: is)]
  rw [denoteCode_store64 (calls := calls)
    (env := ("%add529", .int 64 (ei + idx)) :: env) (s := s) (v := "%add529")
    (p := "%off") (x := ei + idx) (a := q)
    (by simp only [lookupName_cons_self])
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact hoff) is]
  rfl

/-- A void two-argument call the environment answers, at either argument order. -/
theorem stage2NoEventWalk_denote_callVoid2 (calls : Calls) (env : Env) (s : State)
    (callee : String) (t1 : Ty) (o1 : Operand) (t2 : Ty) (o2 : Operand)
    {v1 v2 : Value} {r : CallOutcome}
    (h1 : evalOperand (stateAt env s) o1 = some v1)
    (h2 : evalOperand (stateAt env s) o2 = some v2)
    (hc : calls callee [v1, v2] s.mem s.next = some r) (is : List Instr) :
    denoteCode calls (.callVoid callee [(t1, o1), (t2, o2)] :: is) (stateAt env s) =
      denoteCode calls is (stateAt env { s with mem := r.mem, next := r.next }) := by
  have hargs : evalOperands (stateAt env s) [(t1, o1), (t2, o2)] = some [v1, v2] := by
    simp only [evalOperands, h1, h2]
  have hstep : evalInstr calls (stateAt env s) (.callVoid callee [(t1, o1), (t2, o2)]) =
      some (stateAt env (stage2NoEventStepState s r.mem r.next)) := by
    simp only [evalInstr, hargs, hc, stateAt_mem, stateAt_next]
    rfl
  rw [denoteCode_cons_of _ _ _ _ _ hstep]
  rfl

/-- The selection answers a lifetime marker at any argument list with the
caller's memory and allocator: no value read, no byte written, no allocation. -/
theorem stage2NoEventCalls_lifetime_args {gap : Calls} {sym : String}
    {args : List Value} {mem : Mem} {next : Nat}
    (h : sym = "llvm.lifetime.start.p0" ∨ sym = "llvm.lifetime.end.p0") :
    ∃ out, stage2NoEventCalls gap sym args mem next = some out ∧ out.mem = mem ∧
      out.next = next := by
  have hne : sym ≠ "od_gap_recover" := by
    rcases h with rfl | rfl <;> decide
  have hsel : stage2NoEventCalls gap sym args mem next =
      stage2Calls stage2SubCalls sym args mem next := by
    simp only [stage2NoEventCalls]
    rw [ite_eq_right hne]
  rcases h with rfl | rfl
  · refine ⟨{ ret := .int 1 0, mem := mem, next := next }, ?_, rfl, rfl⟩
    rw [hsel]; rfl
  · refine ⟨{ ret := .int 1 0, mem := mem, next := next }, ?_, rfl, rfl⟩
    rw [hsel]; rfl

/-- A lifetime `end` marker writes nothing and allocates nothing: the chain goes
on at the caller's state. -/
theorem stage2NoEventWalk_denote_lifetimeEnd {gap : Calls} (env : Env) (s : State)
    (p : String) {sz a : Nat}
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode (stage2NoEventCalls gap)
        (.callVoid "llvm.lifetime.end.p0"
          [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 sz)))),
            (Ty.ptr, (Operand.reg p))] :: is) (stateAt env s) =
      denoteCode (stage2NoEventCalls gap) is (stateAt env s) := by
  obtain ⟨out, hout, hm, hn⟩ := stage2NoEventCalls_lifetime_args (gap := gap)
    (sym := "llvm.lifetime.end.p0") (args := [.int 64 (BitVec.ofNat 64 sz), .ptr a])
    (mem := s.mem) (next := s.next) (Or.inr rfl)
  have h1 : evalOperand (stateAt env s) (.imm (.int 64 (BitVec.ofNat 64 sz))) =
      some (.int 64 (BitVec.ofNat 64 sz)) := rfl
  have h2 : evalOperand (stateAt env s) (.reg p) = some (.ptr a) :=
    evalOperand_reg_of env s p (.ptr a) hp
  have hargs : evalOperands (stateAt env s)
      [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 sz)))),
        (Ty.ptr, (Operand.reg p))] =
      some [.int 64 (BitVec.ofNat 64 sz), .ptr a] := by
    simp only [evalOperands, h1, h2]
  have hstep : evalInstr (stage2NoEventCalls gap) (stateAt env s)
      (.callVoid "llvm.lifetime.end.p0"
        [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 sz)))),
          (Ty.ptr, (Operand.reg p))]) = some (stateAt env s) := by
    simp only [evalInstr, hargs, hout, hm, hn]
    rfl
  rw [denoteCode_cons_of _ _ _ _ _ hstep]

/-! ### The refusal block's run -/

/-- The refusal block's run: the `phi` (at whichever operand the chain selected),
the offset and its store, the helper call, the three zero stores, the load and the
error store, composed through the named states. -/
theorem stage2NoEventRefusal_denote {gap : Calls} (env : Env) (s : State) (p : String)
    {ei idx : BitVec 64} {c e tokensOut valuesOut sumOut err eoff : Nat}
    {rc : CallOutcome} {op : Operand}
    (hpre : s.pre = some p)
    (hinc : phiIncoming p ifThen527EiIncoming = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 ei))
    (hidx : lookupName env "%idxprom.lcssa" = some (.int 64 idx))
    (hoff : lookupName env "%off" = some (.ptr (e + 8)))
    (hc : lookupName env "%c" = some (.ptr c))
    (htok : lookupName env "%tokens_out" = some (.ptr tokensOut))
    (hval : lookupName env "%values_out" = some (.ptr valuesOut))
    (hsum : lookupName env "%sum_out" = some (.ptr sumOut))
    (herr : lookupName env "%err" = some (.ptr err))
    (hrc : stage2NoEventCalls gap "od_gap_recover" [.ptr c, .int 64 idx]
      (writeBytes s.mem (e + 8) (natToBytes (ei + idx).toNat 8)) s.next = some rc)
    (hv4 : readBytes (stage2NoEventZeroMem rc.mem tokensOut valuesOut sumOut) (e + 8) 8
      = some (natToBytes (BitVec.ofNat 64 eoff).toNat 8)) :
    denoteCode (stage2NoEventCalls gap) refusalInstrs (stateAt env s) =
      some (stage2NoEventRefusalS6 env s ei idx rc tokensOut valuesOut sumOut err
        (BitVec.ofNat 64 eoff)) := by
  unfold refusalInstrs refusalRestInstrs refusalPrefixInstrs refusalTailInstrs
  simp only [List.cons_append, List.nil_append]
  rw [denoteCode_phi (calls := stage2NoEventCalls gap) (env := env) (s := s)
    "%ei520.0.ph" (Ty.int 64) ifThen527EiIncoming (p := p) (op := op)
    (v := .int 64 ei) hpre hinc hop _ (by rfl)]
  rw [stage2NoEventWalk_denote_add_store (calls := stage2NoEventCalls gap)
    (env := ("%ei520.0.ph", .int 64 ei) :: env) (s := s) (ei := ei) (idx := idx)
    (by simp only [lookupName_cons_self])
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact hidx)
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact hoff)]
  rw [stage2NoEventWalk_denote_callVoid2 (calls := stage2NoEventCalls gap)
    (env := ("%add529", .int 64 (ei + idx)) :: ("%ei520.0.ph", .int 64 ei) :: env)
    (s := _)
    "od_gap_recover"
    Ty.ptr (Operand.reg "%c") (Ty.int 64) (Operand.reg "%idxprom.lcssa")
    (evalOperand_reg_of _ _ _ _ (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact hc))
    (evalOperand_reg_of _ _ _ _ (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact hidx)) hrc]
  generalize hR2 : { stage2NoEventStepState s (writeBytes s.mem (e + 8) (natToBytes (ei + idx).toNat 8)) s.next with mem := rc.mem, next := rc.next } = R2
  rw [stage2NoEventWalk_denote_store64_imm (calls := stage2NoEventCalls gap)
    (env := ("%add529", .int 64 (ei + idx)) :: ("%ei520.0.ph", .int 64 ei) :: env)
    (x := (BitVec.ofNat 64 0)) (p := "%tokens_out")
    (hp := (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact htok))]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod]
  generalize hR3 : { R2 with mem := writeBytes R2.mem tokensOut (natToBytes 0 8) } = R3
  rw [stage2NoEventWalk_denote_store64_imm (calls := stage2NoEventCalls gap)
    (env := ("%add529", .int 64 (ei + idx)) :: ("%ei520.0.ph", .int 64 ei) :: env)
    (x := (BitVec.ofNat 64 0)) (p := "%values_out")
    (hp := (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact hval))]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod]
  generalize hR4 : { R3 with mem := writeBytes R3.mem valuesOut (natToBytes 0 8) } = R4
  rw [stage2NoEventWalk_denote_store64_imm (calls := stage2NoEventCalls gap)
    (env := ("%add529", .int 64 (ei + idx)) :: ("%ei520.0.ph", .int 64 ei) :: env)
    (x := (BitVec.ofNat 64 0)) (p := "%sum_out")
    (hp := (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact hsum))]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod]
  generalize hR5 : { R4 with mem := writeBytes R4.mem sumOut (natToBytes 0 8) } = R5
  have hR5mem : R5.mem = stage2NoEventZeroMem rc.mem tokensOut valuesOut sumOut := by
    rw [← hR5, ← hR4, ← hR3, ← hR2]
    simp only [stage2NoEventStepState, stage2NoEventZeroMem, wordBytes]
  have hv4' : readBytes R5.mem (e + 8) 8 =
      some (natToBytes (BitVec.ofNat 64 eoff).toNat 8) := by
    rw [hR5mem]
    exact hv4
  rw [denoteCode_load64 (calls := stage2NoEventCalls gap)
    (env := ("%add529", .int 64 (ei + idx)) :: ("%ei520.0.ph", .int 64 ei) :: env)
    (s := R5) (d := "%74") (p := "%off") (v := BitVec.ofNat 64 eoff)
    (hp := (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact hoff)) (hv := hv4')]
  rw [denoteCode_store64 (calls := stage2NoEventCalls gap)
    (env := ("%74", .int 64 (BitVec.ofNat 64 eoff)) ::
      ("%add529", .int 64 (ei + idx)) :: ("%ei520.0.ph", .int 64 ei) :: env)
    (v := "%74") (p := "%err") (x := BitVec.ofNat 64 eoff)
    (hv := (by simp only [lookupName_cons_self]))
    (hp := (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact herr))]
  generalize hR6 : { R5 with mem := writeBytes R5.mem err (natToBytes (BitVec.ofNat 64 eoff).toNat 8) } = R6
  simp only [denoteCode_nil]
  rw [← hR6, ← hR5, ← hR4, ← hR3, ← hR2]
  simp only [stateAt, stage2NoEventRefusalS6, stage2NoEventRefusalEnv3,
    stage2NoEventRefusalEnv2, stage2NoEventRefusalEnv1, stage2NoEventStepState,
    stage2NoEventErrMem, stage2NoEventZeroMem, wordBytes]

/-- **The refusal block's control step.**  The selected `%ei520.0.ph` word and the
block's run, ending at `cleanup580` with `if.then527` as its predecessor. -/
theorem stage2NoEventRefusal_step {gap : Calls} (env : Env) (s : State) (p : String)
    {ei idx : BitVec 64} {c e tokensOut valuesOut sumOut err eoff : Nat}
    {rc : CallOutcome} {op : Operand}
    (hpc : s.pc = "if.then527") (hpre : s.pre = some p)
    (hinc : phiIncoming p ifThen527EiIncoming = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 ei))
    (hidx : lookupName env "%idxprom.lcssa" = some (.int 64 idx))
    (hoff : lookupName env "%off" = some (.ptr (e + 8)))
    (hc : lookupName env "%c" = some (.ptr c))
    (htok : lookupName env "%tokens_out" = some (.ptr tokensOut))
    (hval : lookupName env "%values_out" = some (.ptr valuesOut))
    (hsum : lookupName env "%sum_out" = some (.ptr sumOut))
    (herr : lookupName env "%err" = some (.ptr err))
    (hrc : stage2NoEventCalls gap "od_gap_recover" [.ptr c, .int 64 idx]
      (writeBytes s.mem (e + 8) (natToBytes (ei + idx).toNat 8)) s.next = some rc)
    (hv4 : readBytes (stage2NoEventZeroMem rc.mem tokensOut valuesOut sumOut) (e + 8) 8
      = some (natToBytes (BitVec.ofNat 64 eoff).toNat 8)) :
    step (stage2NoEventCalls gap) stage2NoEventBody (stateAt env s) =
      .jump (stage2NoEventRefusalTarget env s ei idx rc tokensOut valuesOut sumOut err
        (BitVec.ofNat 64 eoff)) := by
  refine stage2NoEventWalk_step_at_block (s := stateAt env s)
    (s' := stage2NoEventRefusalS6 env s ei idx rc tokensOut valuesOut sumOut err
      (BitVec.ofNat 64 eoff)) (b := refusalBlock) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using refusalBlock_find
  · exact stage2NoEventRefusal_denote env s p hpre hinc hop hidx hoff hc htok hval
      hsum herr hrc hv4
  · simp only [refusalBlock, execTerm, stage2NoEventRefusalTarget,
      stage2NoEventRefusalS6, stage2NoEventJumpState, stage2NoEventStepState,
      stage2NoEventRefusalEnv3, stage2NoEventRefusalEnv2, stage2NoEventRefusalEnv1,
      stateAt, hpc]

/-! ### The return block -/

/-- **The return block's run.**  The `%retval.14` `phi` selects the arm's verdict
from its predecessor, the four lifetime markers write nothing and allocate
nothing, and the `ret` hands the verdict back. -/
theorem stage2NoEventCleanup_denote {gap : Calls} (env : Env) (s : State)
    (pcName : String) {w : BitVec 64} {c e stk xj : Nat}
    (hpre : s.pre = some pcName)
    (hinc : phiIncoming pcName cleanup580Incoming = some (.imm (.int 64 w)))
    (hc : lookupName env "%c" = some (.ptr c))
    (he : lookupName env "%e" = some (.ptr e))
    (hstk : lookupName env "%stk" = some (.ptr stk))
    (hxj : lookupName env "%xj" = some (.ptr xj)) :
    denoteCode (stage2NoEventCalls gap) cleanup580Instrs (stateAt env s) =
      some (stateAt (("%retval.14", .int 64 w) :: env) s) := by
  unfold cleanup580Instrs
  rw [denoteCode_phi (calls := stage2NoEventCalls gap) (env := env) (s := s)
    "%retval.14" (Ty.int 64) cleanup580Incoming (p := pcName)
    (op := .imm (.int 64 w)) (v := .int 64 w) hpre hinc
    (evalOperand_lit_of _ 64 w) _ (by rfl)]
  rw [stage2NoEventWalk_denote_lifetimeEnd (gap := gap)
    (env := ("%retval.14", .int 64 w) :: env) (s := s) "%c" (sz := 1192) (a := c)
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact hc)]
  rw [stage2NoEventWalk_denote_lifetimeEnd (gap := gap)
    (env := ("%retval.14", .int 64 w) :: env) (s := s) "%e" (sz := 24) (a := e)
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact he)]
  rw [stage2NoEventWalk_denote_lifetimeEnd (gap := gap)
    (env := ("%retval.14", .int 64 w) :: env) (s := s) "%stk" (sz := 520) (a := stk)
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact hstk)]
  rw [stage2NoEventWalk_denote_lifetimeEnd (gap := gap)
    (env := ("%retval.14", .int 64 w) :: env) (s := s) "%xj" (sz := 8) (a := xj)
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact hxj)]
  rfl

/-- **The return block's control step**: from `cleanup580`, the run rets the
verdict its `phi` selects. -/
theorem stage2NoEventCleanup_step {gap : Calls} (env : Env) (s : State)
    (pcName : String) {w : BitVec 64} {c e stk xj : Nat}
    (hpc : s.pc = "cleanup580")
    (hpre : s.pre = some pcName)
    (hinc : phiIncoming pcName cleanup580Incoming = some (.imm (.int 64 w)))
    (hc : lookupName env "%c" = some (.ptr c))
    (he : lookupName env "%e" = some (.ptr e))
    (hstk : lookupName env "%stk" = some (.ptr stk))
    (hxj : lookupName env "%xj" = some (.ptr xj)) :
    step (stage2NoEventCalls gap) stage2NoEventBody (stateAt env s) =
      .ret (some (.int 64 w)) (stateAt (("%retval.14", .int 64 w) :: env) s) := by
  refine stage2NoEventWalk_step_at_block (s := stateAt env s)
    (s' := stateAt (("%retval.14", .int 64 w) :: env) s) (b := cleanup580Block) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using cleanup580Block_find
  · exact stage2NoEventCleanup_denote env s pcName hpre hinc hc he hstk hxj
  · simp only [cleanup580Block, execTerm, stateAt, evalOperand, lookupName_cons_self]

/-! ### The flush (empty-stream) arm -/

/-- **`if.then`'s run.**  The three zero stores and the document's length at
`%err`; the block branches to `cleanup580`. -/
theorem stage2NoEventFlush_denote {gap : Calls} (env : Env) (s : State)
    {nv : BitVec 64} {tokensOut valuesOut sumOut err : Nat}
    (hnv : lookupName env "%n" = some (.int 64 nv))
    (htok : lookupName env "%tokens_out" = some (.ptr tokensOut))
    (hval : lookupName env "%values_out" = some (.ptr valuesOut))
    (hsum : lookupName env "%sum_out" = some (.ptr sumOut))
    (herr : lookupName env "%err" = some (.ptr err)) :
    denoteCode (stage2NoEventCalls gap) flushInstrs (stateAt env s) =
      some (stateAt env
        (stage2NoEventStepState s
          (stage2NoEventErrMem s.mem tokensOut valuesOut sumOut err nv) s.next)) := by
  unfold flushInstrs
  rw [stage2NoEventWalk_denote_store64_imm (calls := stage2NoEventCalls gap)
    (env := env) (s := s) (x := (BitVec.ofNat 64 0)) (p := "%tokens_out")
    (hp := htok)]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod]
  generalize hS1 : { s with mem := writeBytes s.mem tokensOut (natToBytes 0 8) } = S1
  rw [stage2NoEventWalk_denote_store64_imm (calls := stage2NoEventCalls gap)
    (env := env) (x := (BitVec.ofNat 64 0)) (p := "%values_out") (hp := hval)]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod]
  generalize hS2 : { S1 with mem := writeBytes S1.mem valuesOut (natToBytes 0 8) } = S2
  rw [stage2NoEventWalk_denote_store64_imm (calls := stage2NoEventCalls gap)
    (env := env) (x := (BitVec.ofNat 64 0)) (p := "%sum_out") (hp := hsum)]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod]
  generalize hS3 : { S2 with mem := writeBytes S2.mem sumOut (natToBytes 0 8) } = S3
  rw [denoteCode_store64 (calls := stage2NoEventCalls gap) (env := env)
    (v := "%n") (p := "%err") (x := nv) (hv := hnv) (hp := herr)]
  generalize hS4 : { S3 with mem := writeBytes S3.mem err (natToBytes nv.toNat 8) } = S4
  simp only [denoteCode_nil]
  rw [← hS4, ← hS3, ← hS2, ← hS1]
  simp only [stateAt, stage2NoEventStepState, stage2NoEventErrMem,
    stage2NoEventZeroMem, wordBytes]

/-- **The flush arm's control step**: from `if.then`, the stores and the branch
to `cleanup580`. -/
theorem stage2NoEventFlush_step {gap : Calls} (env : Env) (s : State)
    {nv : BitVec 64} {tokensOut valuesOut sumOut err : Nat}
    (hpc : s.pc = "if.then")
    (hnv : lookupName env "%n" = some (.int 64 nv))
    (htok : lookupName env "%tokens_out" = some (.ptr tokensOut))
    (hval : lookupName env "%values_out" = some (.ptr valuesOut))
    (hsum : lookupName env "%sum_out" = some (.ptr sumOut))
    (herr : lookupName env "%err" = some (.ptr err)) :
    step (stage2NoEventCalls gap) stage2NoEventBody (stateAt env s) =
      .jump (stateAt env
        (stage2NoEventJumpState s
          (stage2NoEventErrMem s.mem tokensOut valuesOut sumOut err nv) s.next
          "cleanup580" "if.then")) := by
  refine stage2NoEventWalk_step_at_block (s := stateAt env s)
    (s' := stateAt env
      (stage2NoEventStepState s
        (stage2NoEventErrMem s.mem tokensOut valuesOut sumOut err nv) s.next))
    (b := flushBlock) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using flushBlock_find
  · exact stage2NoEventFlush_denote env s hnv htok hval hsum herr
  · simp only [flushBlock, execTerm, stage2NoEventJumpState, stage2NoEventStepState,
      stateAt, evalOperand, lookupName_cons_self, hpc]

/-! ### The acceptance arm -/

/-- **`accept`'s run.**  The count in both word slots and the arena's running sum
added to the terms. -/
theorem stage2NoEventAccept_denote {gap : Calls} (env : Env) (s : State)
    {tok terms arenaWord tokensOut valuesOut sumOut : Nat}
    (htokR : lookupName env "%tokens.8" = some (.int 64 (BitVec.ofNat 64 tok)))
    (htermsR : lookupName env "%terms.8" = some (.int 64 (BitVec.ofNat 64 terms)))
    (harenaR : lookupName env "%arena.10" = some (.int 64 (BitVec.ofNat 64 arenaWord)))
    (htok : lookupName env "%tokens_out" = some (.ptr tokensOut))
    (hval : lookupName env "%values_out" = some (.ptr valuesOut))
    (hsum : lookupName env "%sum_out" = some (.ptr sumOut)) :
    denoteCode (stage2NoEventCalls gap) acceptInstrs (stateAt env s) =
      some (stateAt
        (("%add579", .int 64 (BitVec.ofNat 64 terms + BitVec.ofNat 64 arenaWord))
          :: env)
        (stage2NoEventStepState s
          (stage2NoEventAcceptMem s.mem tokensOut valuesOut sumOut
            (BitVec.ofNat 64 tok)
            (BitVec.ofNat 64 terms + BitVec.ofNat 64 arenaWord)) s.next)) := by
  unfold acceptInstrs
  rw [denoteCode_store64 (calls := stage2NoEventCalls gap) (env := env) (s := s)
    (x := BitVec.ofNat 64 tok) "%tokens.8" "%tokens_out" htokR htok]
  generalize hG1 : { s with mem := writeBytes s.mem tokensOut (natToBytes (BitVec.ofNat 64 tok).toNat 8) } = G1
  rw [denoteCode_store64 (calls := stage2NoEventCalls gap) (env := env) (s := _)
    (x := BitVec.ofNat 64 tok) "%tokens.8" "%values_out" htokR hval]
  generalize hG2 : { G1 with mem := writeBytes G1.mem valuesOut (natToBytes (BitVec.ofNat 64 tok).toNat 8) } = G2
  rw [denoteCode_add_reg (calls := stage2NoEventCalls gap) (env := env) (s := _)
    "%add579" "%terms.8" "%arena.10" htermsR harenaR]
  rw [denoteCode_store64 (calls := stage2NoEventCalls gap)
    (env := ("%add579", .int 64 (BitVec.ofNat 64 terms + BitVec.ofNat 64 arenaWord))
      :: env) (s := _) (x := BitVec.ofNat 64 terms + BitVec.ofNat 64 arenaWord)
    "%add579" "%sum_out" (by simp only [lookupName_cons_self])
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact hsum)]
  generalize hG3 : { G2 with mem := writeBytes G2.mem sumOut (natToBytes (BitVec.ofNat 64 terms + BitVec.ofNat 64 arenaWord).toNat 8) } = G3
  simp only [denoteCode_nil]
  rw [← hG3, ← hG2, ← hG1]
  simp only [stateAt, stage2NoEventStepState, stage2NoEventAcceptMem, wordBytes]

/-- **The acceptance arm's control step**: from `accept`, the stores and the
branch to `cleanup580`. -/
theorem stage2NoEventAccept_step {gap : Calls} (env : Env) (s : State)
    {tok terms arenaWord tokensOut valuesOut sumOut : Nat}
    (hpc : s.pc = "accept")
    (htokR : lookupName env "%tokens.8" = some (.int 64 (BitVec.ofNat 64 tok)))
    (htermsR : lookupName env "%terms.8" = some (.int 64 (BitVec.ofNat 64 terms)))
    (harenaR : lookupName env "%arena.10" = some (.int 64 (BitVec.ofNat 64 arenaWord)))
    (htok : lookupName env "%tokens_out" = some (.ptr tokensOut))
    (hval : lookupName env "%values_out" = some (.ptr valuesOut))
    (hsum : lookupName env "%sum_out" = some (.ptr sumOut)) :
    step (stage2NoEventCalls gap) stage2NoEventBody (stateAt env s) =
      .jump (stateAt
        (("%add579", .int 64 (BitVec.ofNat 64 terms + BitVec.ofNat 64 arenaWord))
          :: env)
        (stage2NoEventJumpState s
          (stage2NoEventAcceptMem s.mem tokensOut valuesOut sumOut
            (BitVec.ofNat 64 tok)
            (BitVec.ofNat 64 terms + BitVec.ofNat 64 arenaWord)) s.next
          "cleanup580" "accept")) := by
  refine stage2NoEventWalk_step_at_block (s := stateAt env s)
    (s' := stateAt
      (("%add579", .int 64 (BitVec.ofNat 64 terms + BitVec.ofNat 64 arenaWord))
        :: env)
      (stage2NoEventStepState s
        (stage2NoEventAcceptMem s.mem tokensOut valuesOut sumOut
          (BitVec.ofNat 64 tok)
          (BitVec.ofNat 64 terms + BitVec.ofNat 64 arenaWord)) s.next))
    (b := acceptBlock) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using acceptBlock_find
  · exact stage2NoEventAccept_denote env s htokR htermsR harenaR htok hval hsum
  · simp only [acceptBlock, execTerm, stage2NoEventJumpState, stage2NoEventStepState,
      stateAt, evalOperand, lookupName_cons_self, hpc]

/-! ### The store read-backs -/

/-- A word store reads back at its own address. -/
theorem stage2NoEventRead_own {mem : Mem} {a v : Nat} :
    readBytes (writeBytes mem a (wordBytes 8 v)) a 8 = some (wordBytes 8 v) := by
  have h := readBytes_writeBytes_same mem (wordBytes 8 v) (addr := a)
  rwa [show (wordBytes 8 v).length = 8 from natToBytes_length v 8] at h

/-- **The refusal word is separate from the three output words**, from the one
surface: the record's `(e, 24)` entry is a staged object, the three words are ABI
regions, and the cross half of the `Pairwise` gives each pair. -/
theorem stage2NoEventWalkSep_off_slots {b n ep nep xp nxp scratch scratchcap
    tokensOut valuesOut sumOut err stk e c d : Nat}
    (h : Stage2NoEventWalkSep b n ep nep xp nxp scratch scratchcap tokensOut
      valuesOut sumOut err stk e c d) :
    ((e + 8) + 8 ≤ tokensOut ∨ tokensOut + 8 ≤ e + 8) ∧
      ((e + 8) + 8 ≤ valuesOut ∨ valuesOut + 8 ≤ e + 8) ∧
      ((e + 8) + 8 ≤ sumOut ∨ sumOut + 8 ≤ e + 8) := by
  have hrec : (e, stage2NoEventErrorExtent) ∈ stage2NoEventStagedRegions stk e c d := by
    simp [stage2NoEventStagedRegions]
  have hcross (a : Nat)
      (ha : (a, 8) ∈ stage2NoEventRegions b n ep nep xp nxp scratch scratchcap
        tokensOut valuesOut sumOut err) :
      (e + 8) + 8 ≤ a ∨ a + 8 ≤ e + 8 := by
    have := disjointRegions_against (rs := stage2NoEventRegions b n ep nep xp nxp
        scratch scratchcap tokensOut valuesOut sumOut err)
      (ss := stage2NoEventStagedRegions stk e c d) (a := a) (n := 8) h ha
      (e, stage2NoEventErrorExtent) hrec
    simp only [stage2NoEventErrorExtent] at this
    omega
  exact ⟨
    hcross tokensOut (by simp [stage2NoEventRegions, stage2NoEventWrites]),
    hcross valuesOut (by simp [stage2NoEventRegions, stage2NoEventWrites]),
    hcross sumOut (by simp [stage2NoEventRegions, stage2NoEventWrites])⟩

/-! ### The terminal post at the arms' memories -/

/-- **The four words are present** at the stores' own read-backs. -/
theorem stage2NoEventPresent_writes {m : Mem} {tokensOut valuesOut sumOut err eoff : Nat}
    (hTok : readBytes m tokensOut 8 = some (wordBytes 8 0))
    (hVal : readBytes m valuesOut 8 = some (wordBytes 8 0))
    (hSum : readBytes m sumOut 8 = some (wordBytes 8 0))
    (hErr : readBytes m err 8 = some (wordBytes 8 eoff)) :
    ∀ a, inRegions (stage2NoEventWrites tokensOut valuesOut sumOut err) a → present m a := by
  intro a ha
  obtain ⟨r, hr, hlo, hhi⟩ := ha
  simp only [stage2NoEventWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · have hp := readBytes_some_present m tokensOut 8 _ hTok (a - tokensOut) (by omega)
    rwa [Nat.add_sub_of_le hlo] at hp
  · have hp := readBytes_some_present m valuesOut 8 _ hVal (a - valuesOut) (by omega)
    rwa [Nat.add_sub_of_le hlo] at hp
  · have hp := readBytes_some_present m sumOut 8 _ hSum (a - sumOut) (by omega)
    rwa [Nat.add_sub_of_le hlo] at hp
  · have hp := readBytes_some_present m err 8 _ hErr (a - err) (by omega)
    rwa [Nat.add_sub_of_le hlo] at hp

/-- The boundary's witnesses at a carry: the verdict, the events and the parser's
tokens are the arm's. -/
def stage2NoEventWitness (K : Stage2NoEventWalkCarry) (verdict : BitVec 64)
    (obs : List ConsumerEvent) (toks : List Token) : Stage2NoEventWitness :=
  { b := K.b, n := K.n, ep := K.ep, nep := K.nep, xp := K.xp, nxp := K.nxp,
    scratch := K.scratch, scratchcap := K.scratchcap, tokensOut := K.tokensOut,
    valuesOut := K.valuesOut, sumOut := K.sumOut, err := K.err, verdict := verdict,
    tok := K.tok, terms := K.terms, bs := K.bs, arena := K.arena, obs := obs,
    toks := toks, stk := K.stk, e := K.e, c := K.c, d := K.d, nextEnd := K.nextEnd }

/-- **The refusal boundary from the stores.**  The three zero words, the refusal
slot and the frame the run's regions have kept. -/
theorem stage2NoEventBoundary_refusal {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} (h : Stage2NoEventWalkInv K mem s) {m : Mem} {eoff : Nat}
    (hTok : readBytes m K.tokensOut 8 = some (wordBytes 8 0))
    (hVal : readBytes m K.valuesOut 8 = some (wordBytes 8 0))
    (hSum : readBytes m K.sumOut 8 = some (wordBytes 8 0))
    (hErr : readBytes m K.err 8 = some (wordBytes 8 eoff))
    (hOffLe : eoff ≤ K.n)
    (hFrame : UnchangedOutside mem m
      (stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err ++
        (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
          [(K.next0, K.nextEnd - K.next0)]))) :
    stage2NoEventBoundary K.a12 mem K.next0 m (.int 64 0) := by
  refine stage2NoEventBoundary_of_witness
    (w := stage2NoEventWitness K 0 [] []) ?_
  exact ⟨h.args_eq, rfl, Or.inl rfl, h.doc,
    fun hv => absurd hv (by simp [stage2NoEventWitness]), fun hv => absurd hv (by simp [stage2NoEventWitness]),
    fun hv => absurd hv (by simp [stage2NoEventWitness]), fun hv => absurd hv (by simp [stage2NoEventWitness]),
    fun hv => absurd hv (by simp [stage2NoEventWitness]), fun hv => absurd hv (by simp [stage2NoEventWitness]),
    fun hv => absurd hv (by simp [stage2NoEventWitness]), fun hv => absurd hv (by simp [stage2NoEventWitness]),
    fun _ => hTok, fun _ => hVal, fun _ => hSum,
    fun _ => ⟨eoff, hOffLe, hErr⟩, fun hv => absurd hv (by simp [stage2NoEventWitness]),
    stage2NoEventPresent_writes hTok hVal hSum hErr,
    by simp only [stage2NoEventWitness]; have := h.nextEnd_static; omega,
    hFrame⟩

/-- The four output words are present, with the refusal slot left at the
caller's staged bytes on acceptance. -/
theorem stage2NoEventPresent_writes_accept {m mem : Mem} {tokensOut valuesOut sumOut
    err tok sumWord : Nat}
    (hTok : readBytes m tokensOut 8 = some (wordBytes 8 tok))
    (hVal : readBytes m valuesOut 8 = some (wordBytes 8 tok))
    (hSum : readBytes m sumOut 8 = some (wordBytes 8 sumWord))
    (hErr : readBytes m err 8 = readBytes mem err 8)
    (hErrBytes : HasBytes mem err 8) :
    ∀ a, inRegions (stage2NoEventWrites tokensOut valuesOut sumOut err) a → present m a := by
  intro a ha
  obtain ⟨r, hr, hlo, hhi⟩ := ha
  simp only [stage2NoEventWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · have hp := readBytes_some_present m tokensOut 8 _ hTok (a - tokensOut) (by omega)
    rwa [Nat.add_sub_of_le hlo] at hp
  · have hp := readBytes_some_present m valuesOut 8 _ hVal (a - valuesOut) (by omega)
    rwa [Nat.add_sub_of_le hlo] at hp
  · have hp := readBytes_some_present m sumOut 8 _ hSum (a - sumOut) (by omega)
    rwa [Nat.add_sub_of_le hlo] at hp
  · obtain ⟨vs, hvs⟩ := hErrBytes
    have hm : readBytes m err 8 = some vs := by rw [hErr]; exact hvs
    have hp := readBytes_some_present m err 8 vs hm (a - err) (by omega)
    rwa [Nat.add_sub_of_le hlo] at hp

/-- **The acceptance boundary from the stores and the parse relation.** -/
theorem stage2NoEventBoundary_accept {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} (h : Stage2NoEventWalkInv K mem s) {m : Mem}
    {obs : List ConsumerEvent} {toks : List Token}
    (hTok : readBytes m K.tokensOut 8 = some (wordBytes 8 K.tok))
    (hVal : readBytes m K.valuesOut 8 = some (wordBytes 8 K.tok))
    (hSum : readBytes m K.sumOut 8 =
      some (wordBytes 8 ((byteSum K.arena + K.terms) % 2 ^ 64)))
    (hErr : readBytes m K.err 8 = readBytes mem K.err 8)
    (hRel : Stage2NoEvent K.bs K.arena obs toks)
    (hObsLen : obs.length = K.tok)
    (hTerms : K.terms = (obs.map ConsumerEvent.terms).sum)
    (hFrame : UnchangedOutside mem m
      (stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err ++
        (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
          [(K.next0, K.nextEnd - K.next0)]))) :
    stage2NoEventBoundary K.a12 mem K.next0 m (.int 64 1) := by
  refine stage2NoEventBoundary_of_witness
    (w := stage2NoEventWitness K 1 obs toks) ?_
  exact ⟨h.args_eq, rfl, Or.inr rfl, h.doc,
    fun _ => hTok, fun _ => hVal, fun _ => hSum, fun _ => h.tokLe,
    fun _ => Nat.lt_of_le_of_lt h.tokLe h.nLt, fun _ => hRel,
    fun _ => hObsLen, fun _ => hTerms,
    fun hv => absurd hv (by simp [stage2NoEventWitness]), fun hv => absurd hv (by simp [stage2NoEventWitness]),
    fun hv => absurd hv (by simp [stage2NoEventWitness]), fun hv => absurd hv (by simp [stage2NoEventWitness]),
    fun _ => hErr,
    stage2NoEventPresent_writes_accept hTok hVal hSum hErr h.errBytes,
    by simp only [stage2NoEventWitness]; have := h.nextEnd_static; omega,
    hFrame⟩

/-! ### The flush arm's run -/

/-- **The flush arm.**  The empty entry stream: the three zero stores and the
document's length at `%err`, then the return with verdict zero.  The count is zero
and nothing is claimed about the events, so the arm needs no premise beyond the
walk's own frame. -/
theorem stage2NoEventFlush_run {K : Stage2NoEventWalkCarry} {mem : Mem} {s : State}
    (h : Stage2NoEventWalkInv K mem s)
    (hregs : Stage2NoEventWalkParams K s)
    (hloc : Stage2NoEventWalkLocals K s)
    (hpc : s.pc = "if.then") :
    ∃ m, runFuel (stage2NoEventCalls (gap := stage2GapRecover)) 2 stage2NoEventBody
        (stateAt s.env s) = some (.ret (some (.int 64 0)) m) ∧
      stage2NoEventBoundary K.a12 mem K.next0 m (.int 64 0) := by
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩ :=
    stage2NoEventWrites_slots (stage2NoEventRegions_writes h.separate)
  have hNV : (BitVec.ofNat 64 K.n).toNat = K.n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.nLt]
  have hstep1 := stage2NoEventFlush_step (gap := stage2GapRecover) s.env s hpc
    hregs.n hregs.tokensOut hregs.valuesOut hregs.sumOut hregs.err
  have hinc0 : phiIncoming "if.then" cleanup580Incoming =
      some (.imm (.int 64 (0 : BitVec 64))) := by decide
  have hcleanup := stage2NoEventCleanup_step (gap := stage2GapRecover) s.env
    (stage2NoEventJumpState s
      (stage2NoEventErrMem s.mem K.tokensOut K.valuesOut K.sumOut K.err
        (BitVec.ofNat 64 K.n)) s.next "cleanup580" "if.then")
    "if.then" rfl rfl hinc0 hregs.c hregs.e hregs.stk hloc.xj
  refine ⟨stage2NoEventErrMem s.mem K.tokensOut K.valuesOut K.sumOut K.err
    (BitVec.ofNat 64 K.n), ?_, ?_⟩
  · simp only [runFuel, hstep1, hcleanup]
    simp only [stateAt_mem, stage2NoEventJumpState]
  · have hErrW : natToBytes (BitVec.ofNat 64 K.n).toNat 8 = wordBytes 8 K.n := by
      rw [hNV]; rfl
    have hTok : readBytes (stage2NoEventErrMem s.mem K.tokensOut K.valuesOut K.sumOut
        K.err (BitVec.ofNat 64 K.n)) K.tokensOut 8 = some (wordBytes 8 0) := by
      simp only [stage2NoEventErrMem, stage2NoEventZeroMem, hErrW]
      rw [readBytes_wordBytes_frame (addr := K.err) (v := K.n) (p := K.tokensOut)
        (n := 8) (by omega)]
      rw [readBytes_wordBytes_frame (addr := K.sumOut) (v := 0) (p := K.tokensOut)
        (n := 8) (by omega)]
      rw [readBytes_wordBytes_frame (addr := K.valuesOut) (v := 0) (p := K.tokensOut)
        (n := 8) (by omega)]
      exact stage2NoEventRead_own
    have hVal : readBytes (stage2NoEventErrMem s.mem K.tokensOut K.valuesOut K.sumOut
        K.err (BitVec.ofNat 64 K.n)) K.valuesOut 8 = some (wordBytes 8 0) := by
      simp only [stage2NoEventErrMem, stage2NoEventZeroMem, hErrW]
      rw [readBytes_wordBytes_frame (addr := K.err) (v := K.n) (p := K.valuesOut)
        (n := 8) (by omega)]
      rw [readBytes_wordBytes_frame (addr := K.sumOut) (v := 0) (p := K.valuesOut)
        (n := 8) (by omega)]
      exact stage2NoEventRead_own
    have hSum : readBytes (stage2NoEventErrMem s.mem K.tokensOut K.valuesOut K.sumOut
        K.err (BitVec.ofNat 64 K.n)) K.sumOut 8 = some (wordBytes 8 0) := by
      simp only [stage2NoEventErrMem, stage2NoEventZeroMem, hErrW]
      rw [readBytes_wordBytes_frame (addr := K.err) (v := K.n) (p := K.sumOut)
        (n := 8) (by omega)]
      exact stage2NoEventRead_own
    have hErr : readBytes (stage2NoEventErrMem s.mem K.tokensOut K.valuesOut K.sumOut
        K.err (BitVec.ofNat 64 K.n)) K.err 8 = some (wordBytes 8 K.n) := by
      simp only [stage2NoEventErrMem, stage2NoEventZeroMem, hErrW]
      exact stage2NoEventRead_own
    have hbase : UnchangedOutside mem
        (stage2NoEventErrMem s.mem K.tokensOut K.valuesOut K.sumOut K.err
          (BitVec.ofNat 64 K.n))
        (stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err ++
          (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
            [(K.next0, K.nextEnd - K.next0)])) := by
      have h0 : UnchangedOutside mem s.mem
          (stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err ++
            (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
              [(K.next0, K.nextEnd - K.next0)])) :=
        h.walkFrame.of_covered (fun r hr =>
          ⟨r, List.mem_append_right _ hr, le_rfl, le_rfl⟩)
      have hmem (a : Nat) (ha : (a, 8) ∈ stage2NoEventWrites K.tokensOut
          K.valuesOut K.sumOut K.err) :
          ∃ q ∈ stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err ++
            (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
              [(K.next0, K.nextEnd - K.next0)]), q.1 ≤ a ∧ a + 8 ≤ q.1 + q.2 :=
        ⟨(a, 8), List.mem_append_left _ ha, le_rfl, le_rfl⟩
      simp only [stage2NoEventErrMem, stage2NoEventZeroMem, hErrW]
      exact (((h0.write_le (hmem K.tokensOut (by simp [stage2NoEventWrites]))
        (by simp [wordBytes, natToBytes_length])).write_le
        (hmem K.valuesOut (by simp [stage2NoEventWrites]))
        (by simp [wordBytes, natToBytes_length])).write_le
        (hmem K.sumOut (by simp [stage2NoEventWrites]))
        (by simp [wordBytes, natToBytes_length])).write_le
        (hmem K.err (by simp [stage2NoEventWrites]))
        (by simp [wordBytes, natToBytes_length])
    exact stage2NoEventBoundary_refusal h hTok hVal hSum hErr
      (Nat.le_refl K.n) hbase

/-! ### The acceptance arm's run -/

/-- The arena's register word and the terms add to the post's modular sum. -/
theorem stage2NoEventSumWord {arena : List UInt8} {terms arenaWord : Nat}
    (h : byteSum arena % 2 ^ 64 = arenaWord) :
    (BitVec.ofNat 64 terms + BitVec.ofNat 64 arenaWord).toNat =
      (byteSum arena + terms) % 2 ^ 64 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, ← h, Nat.mod_mod,
    ← Nat.add_mod, Nat.add_comm]

/-- **The acceptance arm.**  The three stores, the return with verdict one, and
the record's boundary at the parse relation the walk's trace supplies.  The
state's reading is the three-word `Stage2NoEventWalkAcceptAcc` (the stores' own
cells), and the relation, its length and its sum are the trace's, so no argument
beside the trace is needed. -/
theorem stage2NoEventAccept_run_traced {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State}
    (h : Stage2NoEventWalkInv K mem s)
    (hregs : Stage2NoEventWalkParams K s)
    (hloc : Stage2NoEventWalkLocals K s)
    (hacc : Stage2NoEventWalkAcceptAcc K s)
    (hpc : s.pc = "accept")
    (htrace : Stage2NoEventWalkTrace K) :
    ∃ m, runFuel (stage2NoEventCalls (gap := stage2GapRecover)) 2 stage2NoEventBody
        (stateAt s.env s) = some (.ret (some (.int 64 1)) m) ∧
      stage2NoEventBoundary K.a12 mem K.next0 m (.int 64 1) := by
  obtain ⟨obs, toks, hRel, hObsLen, hTermsEq, -⟩ := htrace
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩ :=
    stage2NoEventWrites_slots (stage2NoEventRegions_writes h.separate)
  have hTokLt : K.tok < 2 ^ 64 := Nat.lt_of_le_of_lt h.tokLe h.nLt
  have hTokW : (BitVec.ofNat 64 K.tok).toNat = K.tok := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hTokLt]
  have hSumW : (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 K.arenaWord).toNat =
      (byteSum K.arena + K.terms) % 2 ^ 64 :=
    stage2NoEventSumWord h.arenaEq
  have hstep1 := stage2NoEventAccept_step (gap := stage2GapRecover) s.env s hpc
    hacc.tokens hacc.terms hacc.arena hregs.tokensOut hregs.valuesOut hregs.sumOut
  have hinc1 : phiIncoming "accept" cleanup580Incoming =
      some (.imm (.int 64 (1 : BitVec 64))) := by decide
  have hcleanup := stage2NoEventCleanup_step (gap := stage2GapRecover)
    (("%add579", .int 64 (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 K.arenaWord))
      :: s.env)
    (stage2NoEventJumpState s
      (stage2NoEventAcceptMem s.mem K.tokensOut K.valuesOut K.sumOut
        (BitVec.ofNat 64 K.tok)
        (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 K.arenaWord)) s.next
      "cleanup580" "accept")
    "accept" rfl rfl hinc1
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact hregs.c)
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact hregs.e)
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact hregs.stk)
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact hloc.xj)
  refine ⟨stage2NoEventAcceptMem s.mem K.tokensOut K.valuesOut K.sumOut
    (BitVec.ofNat 64 K.tok)
    (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 K.arenaWord), ?_, ?_⟩
  · simp only [runFuel, hstep1, hcleanup]
    simp only [stateAt_mem, stage2NoEventJumpState]
  · have hTok : readBytes (stage2NoEventAcceptMem s.mem K.tokensOut K.valuesOut
        K.sumOut (BitVec.ofNat 64 K.tok)
        (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 K.arenaWord)) K.tokensOut 8 =
        some (wordBytes 8 K.tok) := by
      simp only [stage2NoEventAcceptMem, hTokW, hSumW]
      rw [readBytes_wordBytes_frame
        (addr := K.sumOut) (v := (byteSum K.arena + K.terms) % 2 ^ 64)
        (p := K.tokensOut) (n := 8) (by omega)]
      rw [readBytes_wordBytes_frame (addr := K.valuesOut) (v := K.tok)
        (p := K.tokensOut) (n := 8) (by omega)]
      exact stage2NoEventRead_own
    have hVal : readBytes (stage2NoEventAcceptMem s.mem K.tokensOut K.valuesOut
        K.sumOut (BitVec.ofNat 64 K.tok)
        (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 K.arenaWord)) K.valuesOut 8 =
        some (wordBytes 8 K.tok) := by
      simp only [stage2NoEventAcceptMem, hTokW, hSumW]
      rw [readBytes_wordBytes_frame
        (addr := K.sumOut) (v := (byteSum K.arena + K.terms) % 2 ^ 64)
        (p := K.valuesOut) (n := 8) (by omega)]
      exact stage2NoEventRead_own
    have hSum : readBytes (stage2NoEventAcceptMem s.mem K.tokensOut K.valuesOut
        K.sumOut (BitVec.ofNat 64 K.tok)
        (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 K.arenaWord)) K.sumOut 8 =
        some (wordBytes 8 ((byteSum K.arena + K.terms) % 2 ^ 64)) := by
      simp only [stage2NoEventAcceptMem, hTokW, hSumW]
      exact stage2NoEventRead_own
    have hErr : readBytes (stage2NoEventAcceptMem s.mem K.tokensOut K.valuesOut
        K.sumOut (BitVec.ofNat 64 K.tok)
        (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 K.arenaWord)) K.err 8 =
        readBytes mem K.err 8 := by
      simp only [stage2NoEventAcceptMem, hTokW, hSumW]
      rw [readBytes_wordBytes_frame
        (addr := K.sumOut) (v := (byteSum K.arena + K.terms) % 2 ^ 64)
        (p := K.err) (n := 8) (by omega)]
      rw [readBytes_wordBytes_frame (addr := K.valuesOut) (v := K.tok)
        (p := K.err) (n := 8) (by omega)]
      rw [readBytes_wordBytes_frame (addr := K.tokensOut) (v := K.tok)
        (p := K.err) (n := 8) (by omega)]
      exact readBytes_eq_of_UnchangedOn
        (unchangedOutside_iff_inRegions.mp h.walkFrame) (a := K.err) (n := 8) (by
          intro k hk
          rintro ⟨r, hr, hlo, hhi⟩
          rcases List.mem_append.mp hr with hr | hr
          · have := stage2NoEventRunRegions_err_outside h.separate h.sep r hr
            omega
          · rcases List.mem_cons.mp hr with rfl | hnil
            · have := h.watermark (K.err, 8) (by
                simp [stage2NoEventRegions, stage2NoEventWrites])
              omega
            · simp at hnil)
    have hbase : UnchangedOutside mem
        (stage2NoEventAcceptMem s.mem K.tokensOut K.valuesOut K.sumOut
          (BitVec.ofNat 64 K.tok)
          (BitVec.ofNat 64 K.terms + BitVec.ofNat 64 K.arenaWord))
        (stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err ++
          (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
            [(K.next0, K.nextEnd - K.next0)])) := by
      have h0 : UnchangedOutside mem s.mem
          (stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err ++
            (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
              [(K.next0, K.nextEnd - K.next0)])) :=
        h.walkFrame.of_covered (fun r hr =>
          ⟨r, List.mem_append_right _ hr, le_rfl, le_rfl⟩)
      have hmem (a : Nat) (ha : (a, 8) ∈ stage2NoEventWrites K.tokensOut
          K.valuesOut K.sumOut K.err) :
          ∃ q ∈ stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err ++
            (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
              [(K.next0, K.nextEnd - K.next0)]), q.1 ≤ a ∧ a + 8 ≤ q.1 + q.2 :=
        ⟨(a, 8), List.mem_append_left _ ha, le_rfl, le_rfl⟩
      simp only [stage2NoEventAcceptMem, hTokW, hSumW]
      exact ((h0.write_le (hmem K.tokensOut (by simp [stage2NoEventWrites]))
        (by simp [wordBytes, natToBytes_length])).write_le
        (hmem K.valuesOut (by simp [stage2NoEventWrites]))
        (by simp [wordBytes, natToBytes_length])).write_le
        (hmem K.sumOut (by simp [stage2NoEventWrites]))
        (by simp [wordBytes, natToBytes_length])
    exact stage2NoEventBoundary_accept h hTok hVal hSum hErr hRel hObsLen hTermsEq
      hbase

/-! ### The refusal arm's run -/

/-- **The refusal arm.**  From `if.then527`'s entry state with the selected
offset word, the run reaches the `ret` at `cleanup580` with verdict zero, and the
record's boundary holds at the memory the stores produced. -/
theorem stage2NoEventRefusal_run {K : Stage2NoEventWalkCarry} {mem : Mem} {s : State}
    (h : Stage2NoEventWalkInv K mem s)
    (hregs : Stage2NoEventWalkParams K s)
    (hloc : Stage2NoEventWalkLocals K s)
    {p : String} {ei idx : BitVec 64} {rc : CallOutcome} {eoff : Nat} {op : Operand}
    (hpc : s.pc = "if.then527") (hpre : s.pre = some p)
    (hinc : phiIncoming p ifThen527EiIncoming = some op)
    (hop : evalOperand (stateAt s.env s) op = some (.int 64 ei))
    (hidx : lookupName s.env "%idxprom.lcssa" = some (.int 64 idx))
    (hrc : stage2NoEventCalls (gap := stage2GapRecover) "od_gap_recover"
      [.ptr K.c, .int 64 idx]
      (writeBytes s.mem (K.e + 8) (natToBytes (ei + idx).toNat 8)) s.next = some rc)
    (hv : readBytes rc.mem (K.e + 8) 8 = some (wordBytes 8 eoff))
    (hOffLe : eoff ≤ K.n) (hOffLt : eoff < 2 ^ 64)
    (hGapFrame : UnchangedOutside s.mem rc.mem
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)])) :
    ∃ m, runFuel (stage2NoEventCalls (gap := stage2GapRecover)) 2 stage2NoEventBody
        (stateAt s.env s) = some (.ret (some (.int 64 0)) m) ∧
      stage2NoEventBoundary K.a12 mem K.next0 m (.int 64 0) := by
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩ :=
    stage2NoEventWrites_slots (stage2NoEventRegions_writes h.separate)
  obtain ⟨hso1, hso2, hso3⟩ := stage2NoEventWalkSep_off_slots h.sep
  have hOffW : natToBytes (BitVec.ofNat 64 eoff).toNat 8 = wordBytes 8 eoff := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hOffLt]; rfl
  have hv4 : readBytes (stage2NoEventZeroMem rc.mem K.tokensOut K.valuesOut K.sumOut)
      (K.e + 8) 8 = some (natToBytes (BitVec.ofNat 64 eoff).toNat 8) := by
    simp only [stage2NoEventZeroMem]
    rw [readBytes_wordBytes_frame (addr := K.sumOut) (v := 0) (p := K.e + 8)
      (n := 8) (by omega)]
    rw [readBytes_wordBytes_frame (addr := K.valuesOut) (v := 0) (p := K.e + 8)
      (n := 8) (by omega)]
    rw [readBytes_wordBytes_frame (addr := K.tokensOut) (v := 0) (p := K.e + 8)
      (n := 8) (by omega)]
    rw [hOffW]
    exact hv
  have hstep1 := stage2NoEventRefusal_step (gap := stage2GapRecover) s.env s p hpc
    hpre hinc hop hidx hloc.off hregs.c hregs.tokensOut hregs.valuesOut hregs.sumOut
    hregs.err hrc hv4
  have hinc0 : phiIncoming "if.then527" cleanup580Incoming =
      some (.imm (.int 64 (0 : BitVec 64))) := by decide
  have hcE : lookupName (stage2NoEventRefusalEnv3 s.env ei idx (BitVec.ofNat 64 eoff))
      "%c" = some (.ptr K.c) := by
    rw [lookupName_refusalEnv3_c]; exact hregs.c
  have heE : lookupName (stage2NoEventRefusalEnv3 s.env ei idx (BitVec.ofNat 64 eoff))
      "%e" = some (.ptr K.e) := by
    rw [lookupName_refusalEnv3_e]; exact hregs.e
  have hstkE : lookupName (stage2NoEventRefusalEnv3 s.env ei idx (BitVec.ofNat 64 eoff))
      "%stk" = some (.ptr K.stk) := by
    rw [lookupName_refusalEnv3_stk]; exact hregs.stk
  have hxjE : lookupName (stage2NoEventRefusalEnv3 s.env ei idx (BitVec.ofNat 64 eoff))
      "%xj" = some (.ptr K.xj) := by
    rw [lookupName_refusalEnv3_xj]; exact hloc.xj
  have hcleanup := stage2NoEventCleanup_step (gap := stage2GapRecover)
    (stage2NoEventRefusalEnv3 s.env ei idx (BitVec.ofNat 64 eoff))
    (stage2NoEventJumpState s
      (stage2NoEventErrMem rc.mem K.tokensOut K.valuesOut K.sumOut K.err
        (BitVec.ofNat 64 eoff)) rc.next "cleanup580" "if.then527")
    "if.then527" rfl rfl hinc0 hcE heE hstkE hxjE
  refine ⟨stage2NoEventErrMem rc.mem K.tokensOut K.valuesOut K.sumOut K.err
    (BitVec.ofNat 64 eoff), ?_, ?_⟩
  · simp only [runFuel, hstep1, hcleanup, stage2NoEventRefusalTarget]
    simp only [stateAt_mem, stage2NoEventJumpState]
  · have hTok : readBytes (stage2NoEventErrMem rc.mem K.tokensOut K.valuesOut
        K.sumOut K.err (BitVec.ofNat 64 eoff)) K.tokensOut 8 =
        some (wordBytes 8 0) := by
      simp only [stage2NoEventErrMem, stage2NoEventZeroMem, hOffW]
      rw [readBytes_wordBytes_frame (addr := K.err) (v := eoff) (p := K.tokensOut)
        (n := 8) (by omega)]
      rw [readBytes_wordBytes_frame (addr := K.sumOut) (v := 0) (p := K.tokensOut)
        (n := 8) (by omega)]
      rw [readBytes_wordBytes_frame (addr := K.valuesOut) (v := 0) (p := K.tokensOut)
        (n := 8) (by omega)]
      exact stage2NoEventRead_own
    have hVal : readBytes (stage2NoEventErrMem rc.mem K.tokensOut K.valuesOut
        K.sumOut K.err (BitVec.ofNat 64 eoff)) K.valuesOut 8 =
        some (wordBytes 8 0) := by
      simp only [stage2NoEventErrMem, stage2NoEventZeroMem, hOffW]
      rw [readBytes_wordBytes_frame (addr := K.err) (v := eoff) (p := K.valuesOut)
        (n := 8) (by omega)]
      rw [readBytes_wordBytes_frame (addr := K.sumOut) (v := 0) (p := K.valuesOut)
        (n := 8) (by omega)]
      exact stage2NoEventRead_own
    have hSum : readBytes (stage2NoEventErrMem rc.mem K.tokensOut K.valuesOut
        K.sumOut K.err (BitVec.ofNat 64 eoff)) K.sumOut 8 = some (wordBytes 8 0) := by
      simp only [stage2NoEventErrMem, stage2NoEventZeroMem, hOffW]
      rw [readBytes_wordBytes_frame (addr := K.err) (v := eoff) (p := K.sumOut)
        (n := 8) (by omega)]
      exact stage2NoEventRead_own
    have hErr : readBytes (stage2NoEventErrMem rc.mem K.tokensOut K.valuesOut
        K.sumOut K.err (BitVec.ofNat 64 eoff)) K.err 8 = some (wordBytes 8 eoff) := by
      simp only [stage2NoEventErrMem, stage2NoEventZeroMem, hOffW]
      exact stage2NoEventRead_own
    have hbase : UnchangedOutside mem
        (stage2NoEventErrMem rc.mem K.tokensOut K.valuesOut K.sumOut K.err
          (BitVec.ofNat 64 eoff))
        (stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err ++
          (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
            [(K.next0, K.nextEnd - K.next0)])) := by
      have h0 : UnchangedOutside mem rc.mem
          (stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err ++
            (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
              [(K.next0, K.nextEnd - K.next0)])) :=
        ((h.walkFrame.trans hGapFrame).of_covered (fun r hr =>
          ⟨r, List.mem_append_right _ hr, le_rfl, le_rfl⟩))
      have hmem (a : Nat) (ha : (a, 8) ∈ stage2NoEventWrites K.tokensOut
          K.valuesOut K.sumOut K.err) :
          ∃ q ∈ stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err ++
            (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
              [(K.next0, K.nextEnd - K.next0)]), q.1 ≤ a ∧ a + 8 ≤ q.1 + q.2 :=
        ⟨(a, 8), List.mem_append_left _ ha, le_rfl, le_rfl⟩
      simp only [stage2NoEventErrMem, stage2NoEventZeroMem, hOffW]
      exact (((h0.write_le (hmem K.tokensOut (by simp [stage2NoEventWrites]))
        (by simp [wordBytes, natToBytes_length])).write_le
        (hmem K.valuesOut (by simp [stage2NoEventWrites]))
        (by simp [wordBytes, natToBytes_length])).write_le
        (hmem K.sumOut (by simp [stage2NoEventWrites]))
        (by simp [wordBytes, natToBytes_length])).write_le
        (hmem K.err (by simp [stage2NoEventWrites]))
        (by simp [wordBytes, natToBytes_length])
    exact stage2NoEventBoundary_refusal h hTok hVal hSum hErr hOffLe hbase

/-! ### The entry block's bootstrap

The invariant is stated at the loop head, so the entry prefix that binds `%xj`
and `%off` is a run of its own: four allocations advance the cursor by `32`, the
markers leave the state alone, and the only writes are the two zeros and the
cursor record's header.  The parameter facts hold at the entry state; the two
locals hold after the prefix. -/

/-- The entry prefix that binds `%xj` and `%off`, in the fixture's order. -/
def entryBootstrapInstrs : List Instr :=
  [ Instr.alloca "%xj" (Ty.int 64) 0,
    Instr.alloca "%outn" (Ty.int 64) 0,
    Instr.alloca "%outn205" (Ty.int 64) 0,
    Instr.alloca "%ei" (Ty.int 64) 0,
    Instr.callVoid "llvm.lifetime.start.p0"
      [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))),
        (Ty.ptr, (Operand.reg "%xj"))],
    Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
      (Operand.reg "%xj"),
    Instr.callVoid "llvm.lifetime.start.p0"
      [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 520)))),
        (Ty.ptr, (Operand.reg "%stk"))],
    Instr.callVoid "llvm.lifetime.start.p0"
      [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 24)))),
        (Ty.ptr, (Operand.reg "%e"))],
    Instr.callVoid "llvm.lifetime.start.p0"
      [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 1192)))),
        (Ty.ptr, (Operand.reg "%c"))],
    Instr.store (Ty.int 32) (Operand.imm (.int 32 (BitVec.ofNat 32 1)))
      (Operand.reg "%e"),
    Instr.gep "%off" (Ty.int 8) (Operand.reg "%e")
      (Operand.imm (.int 64 (BitVec.ofNat 64 8))),
    Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
      (Operand.reg "%off") ]

-- The prefix is the pinned block's own first twelve instructions.
#guard decide
  ((stage2NoEventBody.findBlock "entry").map (fun b => b.instrs.take 12)
    = some entryBootstrapInstrs)

/-- One `alloca`, as a chain step; the allocated extent is the hypothesis. -/
theorem stage2NoEventWalk_denote_alloca (calls : Calls) (env : Env) (s : State)
    (d : String) (ty : Ty) (al n : Nat) (hsz : ty.sizeBytes = n) (is : List Instr) :
    denoteCode calls (.alloca d ty al :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .ptr s.next) :: env)
        (stage2NoEventStepState s s.mem (s.next + n))) := by
  rw [denoteCode_cons_of calls (.alloca d ty al) is (stateAt env s)
    (stateAt ((d, .ptr s.next) :: env) { s with next := s.next + ty.sizeBytes })
    (by simp [evalInstr, stateAt])]
  rw [hsz]
  rfl

/-- A `lifetime.start` marker leaves the state alone. -/
theorem stage2NoEventWalk_denote_lifetimeStart {gap : Calls} (env : Env) (s : State)
    (p : String) {sz a : Nat}
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode (stage2NoEventCalls gap)
        (.callVoid "llvm.lifetime.start.p0"
          [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 sz)))),
            (Ty.ptr, (Operand.reg p))] :: is) (stateAt env s) =
      denoteCode (stage2NoEventCalls gap) is (stateAt env s) := by
  obtain ⟨out, hout, hm, hn⟩ := stage2NoEventCalls_lifetime_args (gap := gap)
    (sym := "llvm.lifetime.start.p0")
    (args := [.int 64 (BitVec.ofNat 64 sz), .ptr a])
    (mem := s.mem) (next := s.next) (Or.inl rfl)
  have h1 : evalOperand (stateAt env s) (.imm (.int 64 (BitVec.ofNat 64 sz))) =
      some (.int 64 (BitVec.ofNat 64 sz)) := rfl
  have h2 : evalOperand (stateAt env s) (.reg p) = some (.ptr a) :=
    evalOperand_reg_of env s p (.ptr a) hp
  have hargs : evalOperands (stateAt env s)
      [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 sz)))),
        (Ty.ptr, (Operand.reg p))] =
      some [.int 64 (BitVec.ofNat 64 sz), .ptr a] := by
    simp only [evalOperands, h1, h2]
  have hstep : evalInstr (stage2NoEventCalls gap) (stateAt env s)
      (.callVoid "llvm.lifetime.start.p0"
        [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 sz)))),
          (Ty.ptr, (Operand.reg p))]) = some (stateAt env s) := by
    simp only [evalInstr, hargs, hout, hm, hn]
    rfl
  rw [denoteCode_cons_of _ _ _ _ _ hstep]

/-- A 32-bit integer store, as a chain step. -/
theorem stage2NoEventWalk_denote_store32_imm (calls : Calls) (env : Env) (s : State)
    (x : BitVec 32) (p : String) {a : Nat}
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store (.int 32) (.imm (.int 32 x)) (.reg p) :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt env
        (stage2NoEventStepState s (writeBytes s.mem a (natToBytes x.toNat 4)) s.next)) := by
  have hstep : evalInstr calls (stateAt env s)
      (.store (.int 32) (.imm (.int 32 x)) (.reg p)) =
      some (stateAt env
        (stage2NoEventStepState s (writeBytes s.mem a (natToBytes x.toNat 4)) s.next)) := by
    have h1 : evalOperand (stateAt env s) (.imm (.int 32 x)) = some (.int 32 x) := rfl
    have h2 : evalOperand (stateAt env s) (.reg p) = some (.ptr a) :=
      evalOperand_reg_of env s p (.ptr a) hp
    simp only [evalInstr, h1, h2, storeValue]
    rfl
  rw [denoteCode_cons_of _ _ _ _ _ hstep]

/-- An eight-byte `gep` at a literal offset, as a chain step. -/
theorem stage2NoEventWalk_denote_gep8_imm (calls : Calls) (env : Env) (s : State)
    (d base : String) (off : BitVec 64) {a bytes : Nat}
    (hb : lookupName env base = some (.ptr a))
    (hbytes : (off.signExtend 64).toNat * (Ty.int 8).sizeBytes = bytes)
    (hlt : (off.signExtend 64).toNat < 2 ^ 63) (is : List Instr) :
    denoteCode calls (.gep d (.int 8) (.reg base) (.imm (.int 64 off)) :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt ((d, .ptr (a + bytes)) :: env) s) := by
  have hb' : evalOperand (stateAt env s) (.reg base) = some (.ptr a) :=
    evalOperand_reg_of env s base (.ptr a) hb
  have hoff : evalOperand (stateAt env s) (.imm (.int 64 off)) = some (.int 64 off) :=
    evalOperand_lit_of (stateAt env s) 64 off
  have hstep : evalInstr calls (stateAt env s)
      (.gep d (.int 8) (.reg base) (.imm (.int 64 off))) =
      some (stateAt ((d, .ptr (a + bytes)) :: env) s) := by
    simp only [evalInstr, hb', hoff, hlt, if_true, hbytes, State.bind]
    rfl
  rw [denoteCode_cons_of _ _ _ _ _ hstep]

/-- The entry state at the record's staging. -/
def stage2NoEventEntryState (K : Stage2NoEventWalkCarry) (mem : Mem) (next : Nat) :
    State :=
  EntryState stage2NoEventBody (stage2NoEventArgs K.a12 K.stk K.e K.c K.d) mem next

/-- The entry state binds every parameter. -/
theorem stage2NoEventEntry_params {K : Stage2NoEventWalkCarry} {mem : Mem} {next : Nat}
    (hargs : K.a12 = [.ptr K.b, .int 64 (BitVec.ofNat 64 K.n), .ptr K.ep,
      .int 64 (BitVec.ofNat 64 K.nep), .ptr K.xp, .int 64 (BitVec.ofNat 64 K.nxp),
      .ptr K.scratch, .int 64 (BitVec.ofNat 64 K.scratchcap), .ptr K.tokensOut,
      .ptr K.valuesOut, .ptr K.sumOut, .ptr K.err]) :
    Stage2NoEventWalkParams K (stage2NoEventEntryState K mem next) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [stage2NoEventEntryState, EntryState, stage2NoEventBody,
      stage2NoEventArgs, stage2NoEventStagingArgs, hargs, lookupName]

/-- The four allocations' environment keeps `%xj` at the entry cursor. -/
theorem lookupName_entryEnv_xj (env : Env) (ei o₂ o₁ xa : Nat) :
    lookupName (("%ei", .ptr ei) :: ("%outn205", .ptr o₂) ::
      ("%outn", .ptr o₁) :: ("%xj", .ptr xa) :: env) "%xj" = some (.ptr xa) := by
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  rw [lookupName_cons_self]

theorem lookupName_entryEnv_stk (env : Env) (ei o₂ o₁ xa a : Nat)
    (h : lookupName env "%stk" = some (.ptr a)) :
    lookupName (("%ei", .ptr ei) :: ("%outn205", .ptr o₂) ::
      ("%outn", .ptr o₁) :: ("%xj", .ptr xa) :: env) "%stk" = some (.ptr a) := by
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

theorem lookupName_entryEnv_e (env : Env) (ei o₂ o₁ xa a : Nat)
    (h : lookupName env "%e" = some (.ptr a)) :
    lookupName (("%ei", .ptr ei) :: ("%outn205", .ptr o₂) ::
      ("%outn", .ptr o₁) :: ("%xj", .ptr xa) :: env) "%e" = some (.ptr a) := by
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

theorem lookupName_entryEnv_c (env : Env) (ei o₂ o₁ xa a : Nat)
    (h : lookupName env "%c" = some (.ptr a)) :
    lookupName (("%ei", .ptr ei) :: ("%outn205", .ptr o₂) ::
      ("%outn", .ptr o₁) :: ("%xj", .ptr xa) :: env) "%c" = some (.ptr a) := by
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- **The entry block's bootstrap.**  From a state carrying the parameters and
entered at the record's cursor, the prefix binds `%xj` and `%off` and reaches a
state where both local facts hold. -/
theorem stage2NoEventEntry_bootstrap {gap : Calls} {K : Stage2NoEventWalkCarry}
    {s : State} (hpar : Stage2NoEventWalkParams K s) (hxj : K.xj = s.next) :
    ∃ s', denoteCode (stage2NoEventCalls gap) entryBootstrapInstrs (stateAt s.env s) =
        some (stateAt s'.env s') ∧ Stage2NoEventWalkLocals K s' := by
  unfold entryBootstrapInstrs
  rw [stage2NoEventWalk_denote_alloca (calls := stage2NoEventCalls gap)
    (env := s.env) (s := s) "%xj" (Ty.int 64) 0 8 (by decide)]
  generalize hS1 : stage2NoEventStepState s s.mem (s.next + 8) = S1
  rw [stage2NoEventWalk_denote_alloca (calls := stage2NoEventCalls gap)
    (env := ("%xj", .ptr s.next) :: s.env) (s := S1) "%outn" (Ty.int 64) 0 8
    (by decide)]
  generalize hS2 : stage2NoEventStepState S1 S1.mem (S1.next + 8) = S2
  rw [stage2NoEventWalk_denote_alloca (calls := stage2NoEventCalls gap)
    (env := ("%outn", .ptr S1.next) :: ("%xj", .ptr s.next) :: s.env) (s := S2)
    "%outn205" (Ty.int 64) 0 8 (by decide)]
  generalize hS3 : stage2NoEventStepState S2 S2.mem (S2.next + 8) = S3
  rw [stage2NoEventWalk_denote_alloca (calls := stage2NoEventCalls gap)
    (env := ("%outn205", .ptr S2.next) :: ("%outn", .ptr S1.next) ::
      ("%xj", .ptr s.next) :: s.env) (s := S3) "%ei" (Ty.int 64) 0 8
    (by decide)]
  generalize hS4 : stage2NoEventStepState S3 S3.mem (S3.next + 8) = S4
  rw [stage2NoEventWalk_denote_lifetimeStart (gap := gap)
    (env := ("%ei", .ptr S3.next) :: ("%outn205", .ptr S2.next) ::
      ("%outn", .ptr S1.next) :: ("%xj", .ptr s.next) :: s.env) (s := S4)
    "%xj" (sz := 8) (a := s.next)
    (lookupName_entryEnv_xj s.env S3.next S2.next S1.next s.next)]
  rw [stage2NoEventWalk_denote_store64_imm (calls := stage2NoEventCalls gap)
    (env := ("%ei", .ptr S3.next) :: ("%outn205", .ptr S2.next) ::
      ("%outn", .ptr S1.next) :: ("%xj", .ptr s.next) :: s.env) (s := S4)
    (x := (BitVec.ofNat 64 0)) (p := "%xj")
    (hp := lookupName_entryEnv_xj s.env S3.next S2.next S1.next s.next)]
  generalize hS5 : ({ env := S4.env, mem := writeBytes S4.mem s.next (natToBytes (BitVec.ofNat 64 0).toNat 8), next := S4.next, pc := S4.pc, pre := S4.pre } : State) = S5
  rw [stage2NoEventWalk_denote_lifetimeStart (gap := gap)
    (env := ("%ei", .ptr S3.next) :: ("%outn205", .ptr S2.next) ::
      ("%outn", .ptr S1.next) :: ("%xj", .ptr s.next) :: s.env) (s := S5)
    "%stk" (sz := 520) (a := K.stk)
    (lookupName_entryEnv_stk s.env S3.next S2.next S1.next s.next K.stk hpar.stk)]
  rw [stage2NoEventWalk_denote_lifetimeStart (gap := gap)
    (env := ("%ei", .ptr S3.next) :: ("%outn205", .ptr S2.next) ::
      ("%outn", .ptr S1.next) :: ("%xj", .ptr s.next) :: s.env) (s := S5)
    "%e" (sz := 24) (a := K.e)
    (lookupName_entryEnv_e s.env S3.next S2.next S1.next s.next K.e hpar.e)]
  rw [stage2NoEventWalk_denote_lifetimeStart (gap := gap)
    (env := ("%ei", .ptr S3.next) :: ("%outn205", .ptr S2.next) ::
      ("%outn", .ptr S1.next) :: ("%xj", .ptr s.next) :: s.env) (s := S5)
    "%c" (sz := 1192) (a := K.c)
    (lookupName_entryEnv_c s.env S3.next S2.next S1.next s.next K.c hpar.c)]
  rw [stage2NoEventWalk_denote_store32_imm (calls := stage2NoEventCalls gap)
    (env := ("%ei", .ptr S3.next) :: ("%outn205", .ptr S2.next) ::
      ("%outn", .ptr S1.next) :: ("%xj", .ptr s.next) :: s.env) (s := S5)
    (x := (BitVec.ofNat 32 1)) (p := "%e")
    (hp := lookupName_entryEnv_e s.env S3.next S2.next S1.next s.next K.e hpar.e)]
  generalize hS6 : stage2NoEventStepState S5 (writeBytes S5.mem K.e (natToBytes (BitVec.ofNat 32 1).toNat 4)) S5.next = S6
  rw [stage2NoEventWalk_denote_gep8_imm (calls := stage2NoEventCalls gap)
    (env := ("%ei", .ptr S3.next) :: ("%outn205", .ptr S2.next) ::
      ("%outn", .ptr S1.next) :: ("%xj", .ptr s.next) :: s.env) (s := S6)
    "%off" "%e" (BitVec.ofNat 64 8) (a := K.e) (bytes := 8)
    (lookupName_entryEnv_e s.env S3.next S2.next S1.next s.next K.e hpar.e)
    (by decide) (by decide)]
  rw [stage2NoEventWalk_denote_store64_imm (calls := stage2NoEventCalls gap)
    (env := ("%off", .ptr (K.e + 8)) ::
      ("%ei", .ptr S3.next) :: ("%outn205", .ptr S2.next) ::
      ("%outn", .ptr S1.next) :: ("%xj", .ptr s.next) :: s.env) (s := S6)
    (x := (BitVec.ofNat 64 0)) (p := "%off") (a := K.e + 8)
    (hp := by simp only [lookupName_cons_self])]
  generalize hS7 : ({ env := S6.env, mem := writeBytes S6.mem (K.e + 8) (natToBytes (BitVec.ofNat 64 0).toNat 8), next := S6.next, pc := S6.pc, pre := S6.pre } : State) = S7
  refine ⟨stateAt
    (("%off", .ptr (K.e + 8)) :: ("%ei", .ptr S3.next) :: ("%outn205", .ptr S2.next) ::
      ("%outn", .ptr S1.next) :: ("%xj", .ptr s.next) :: s.env) S7, ?_, ?_⟩
  · simp only [denoteCode_nil, stateAt]
  · refine ⟨?_, ?_⟩
    · show lookupName (stateAt
        (("%off", .ptr (K.e + 8)) :: ("%ei", .ptr S3.next) ::
          ("%outn205", .ptr S2.next) :: ("%outn", .ptr S1.next) ::
          ("%xj", .ptr s.next) :: s.env) S7).env "%xj" = some (.ptr K.xj)
      simp only [stateAt]
      rw [lookupName_cons_ne _ _ (by decide)]
      rw [lookupName_entryEnv_xj]
      rw [hxj]
    · show lookupName (stateAt
        (("%off", .ptr (K.e + 8)) :: ("%ei", .ptr S3.next) ::
          ("%outn205", .ptr S2.next) :: ("%outn", .ptr S1.next) ::
          ("%xj", .ptr s.next) :: s.env) S7).env "%off" = some (.ptr (K.e + 8))
      simp only [stateAt]
      rw [lookupName_cons_self]

/-! ### Axiom footprints -/

#print axioms stage2NoEventRefusal_denote
#print axioms stage2NoEventRefusal_step
#print axioms stage2NoEventCleanup_denote
#print axioms stage2NoEventFlush_step
#print axioms stage2NoEventAccept_step
#print axioms stage2NoEventWalkSep_off_slots
#print axioms stage2NoEventBoundary_refusal
#print axioms stage2NoEventBoundary_accept
#print axioms stage2NoEventFlush_run
#print axioms stage2NoEventAccept_run_traced
#print axioms stage2NoEventRefusal_run
#print axioms stage2NoEventWalk_denote_alloca
#print axioms stage2NoEventWalk_denote_lifetimeStart
#print axioms stage2NoEventWalk_denote_store32_imm
#print axioms stage2NoEventWalk_denote_gep8_imm
#print axioms stage2NoEventEntry_params
#print axioms stage2NoEventEntry_bootstrap

end LeanLLVM.Refinement
