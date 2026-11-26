/-
The no-event walk's value remainder, closed: `if.else510`'s denotation and the
`gapElse` evidence.

`JsonStage2NoEventWalkValueRemainder` proves the value class's `.ws`/`.other`
bytes leave the loop by the literal dispatch and reach `if.else510`'s entry, and
states the refusal row from the route's tail
(`Stage2NoEventWalkValueRemainderTail`) — but with the block's own step
(`step510`) and the `gapElse` evidence (`evidence`) as *fields*, because the tree
pinned the block (`stage2NoEventIfElse510Block_find`) without deriving either.
This module supplies both, and the tail is then built from the route's data.

The block, in the fixture's order: `store i64 %idxprom.lcssa, ptr %off`; the
`od_gap_recover(ptr %c, i64 %idxprom.lcssa)` call; three zero stores; `%63 = load
i64, ptr %off`; `store i64 %63, ptr %err`; `br label %cleanup580`.  Nothing binds
a register but the load's `%63`, so the environment is the entry's with that one
cell consed on; the memory is the call's outcome with the four output words on
it.  The `%off` store is `%idxprom.lcssa` itself — the addend-free shape the
`gapElse` constructor names (`eoff = idx`), unlike `if.then527`'s `ei + idx`.

The read of `%off` at the load and the read the evidence claims at the call's
memory are the two observed words: the helper may rewrite the record's offset, so
neither is a function of the entry state.  They are premises of this module's
producer, exactly as `if.then527`'s (`stage2NoEventRefusal_denote`'s `hv4` and
`stage2NoEventGapLiteral_exit`'s `hv`) — the helper's write is fixed at the
deployment boundary, not by the body.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkValueRemainder
import LeanLLVM.Refinement.JsonStage2NoEventWalkTerminal

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.BlockEval

/-! ### The block's states

The run has seven instructions and no `phi`: the store at `%off` leaves the
environment alone, the call leaves it alone, the three zero stores leave it
alone, the load binds `%63`, and the `%err` store leaves it alone again.  The
states below are the two public ones — the block's last instruction's exit and
the branch's target — named so the statements stay readable. -/

/-- **`if.else510`'s post-instruction state**: the entry environment with `%63`
bound to the word the load read, the call's outcome's memory with the four output
words written on it, and the call's allocator cursor. -/
def stage2NoEventIfElse510Post (env : Env) (s : State) (rc : CallOutcome)
    (tokensOut valuesOut sumOut err : Nat) (eoff : BitVec 64) : State :=
  stateAt (("%63", .int 64 eoff) :: env)
    (stage2NoEventStepState s
      (stage2NoEventErrMem rc.mem tokensOut valuesOut sumOut err eoff) rc.next)

/-- **The state `if.else510`'s branch delivers to `cleanup580`**: the post-state
at the branch's target, with the block's own name as the `phi`'s predecessor. -/
def stage2NoEventIfElse510Target (env : Env) (s : State) (rc : CallOutcome)
    (tokensOut valuesOut sumOut err : Nat) (eoff : BitVec 64) : State :=
  stateAt (("%63", .int 64 eoff) :: env)
    (stage2NoEventJumpState s
      (stage2NoEventErrMem rc.mem tokensOut valuesOut sumOut err eoff) rc.next
      "cleanup580" "if.else510")

/-- **The `%63` cell is the only one the block binds**, so the entry's registers
read through to the target. -/
theorem stage2NoEventIfElse510Target_env (env : Env) (s : State) (rc : CallOutcome)
    (tokensOut valuesOut sumOut err : Nat) (eoff : BitVec 64) :
    (stage2NoEventIfElse510Target env s rc tokensOut valuesOut sumOut err eoff).env =
      ("%63", .int 64 eoff) :: env := by
  simp only [stage2NoEventIfElse510Target, stage2NoEventJumpState, stateAt]

/-- **The target's memory is the four output words on the call's outcome.** -/
theorem stage2NoEventIfElse510Target_mem (env : Env) (s : State) (rc : CallOutcome)
    (tokensOut valuesOut sumOut err : Nat) (eoff : BitVec 64) :
    (stage2NoEventIfElse510Target env s rc tokensOut valuesOut sumOut err eoff).mem =
      stage2NoEventErrMem rc.mem tokensOut valuesOut sumOut err eoff := by
  simp only [stage2NoEventIfElse510Target, stage2NoEventJumpState, stateAt]

/-! ### The block's denotation

The seven instructions are one `denoteCode` chain, each instruction's step a
committed lemma: the store at `%off` (`denoteCode_store64`), the helper call
(`stage2NoEventWalk_denote_callVoid2`), the three zero stores
(`stage2NoEventWalk_denote_store64_imm`), the load (`denoteCode_load64`) and the
`%err` store (`denoteCode_store64`). -/

/-- **`if.else510`'s run**, from the entry environment and the `%off`/index
registers: `%idxprom.lcssa` is stored at `%off`, the helper is called at the
stored word, the three output words are zeroed, the load reads `%off` and the
`%err` store writes the loaded word.  The two reads of the helper's memory are
the observed words (`hload` at the load, immediately after the three zero stores;
nothing else writes `%off`'s slot). -/
theorem stage2NoEventIfElse510_denote {gap : Calls} (env : Env) (s : State)
    {idx eoff : BitVec 64} {c tokensOut valuesOut sumOut err offAddr : Nat}
    {rc : CallOutcome}
    (hidx : lookupName env "%idxprom.lcssa" = some (.int 64 idx))
    (hoff : lookupName env "%off" = some (.ptr offAddr))
    (hc : lookupName env "%c" = some (.ptr c))
    (htok : lookupName env "%tokens_out" = some (.ptr tokensOut))
    (hval : lookupName env "%values_out" = some (.ptr valuesOut))
    (hsum : lookupName env "%sum_out" = some (.ptr sumOut))
    (herr : lookupName env "%err" = some (.ptr err))
    (hrc : stage2NoEventCalls gap "od_gap_recover" [.ptr c, .int 64 idx]
      (writeBytes s.mem offAddr (natToBytes idx.toNat 8)) s.next = some rc)
    (hload : readBytes
      (stage2NoEventZeroMem rc.mem tokensOut valuesOut sumOut) offAddr 8 =
        some (natToBytes eoff.toNat 8)) :
    denoteCode (stage2NoEventCalls gap) stage2NoEventIfElse510Block.instrs
        (stateAt env s) =
      some (stage2NoEventIfElse510Post env s rc tokensOut valuesOut sumOut err eoff) := by
  unfold stage2NoEventIfElse510Block
  rw [denoteCode_store64 (calls := stage2NoEventCalls gap) (env := env) (s := s)
    (v := "%idxprom.lcssa") (p := "%off") (x := idx) (a := offAddr) hidx hoff]
  generalize hR1 : { s with mem := writeBytes s.mem offAddr (natToBytes idx.toNat 8) } = R1
  rw [stage2NoEventWalk_denote_callVoid2 (calls := stage2NoEventCalls gap)
    (env := env) (s := R1)
    "od_gap_recover" Ty.ptr (Operand.reg "%c") (Ty.int 64) (Operand.reg "%idxprom.lcssa")
    (evalOperand_reg_of env R1 "%c" (.ptr c) hc)
    (evalOperand_reg_of env R1 "%idxprom.lcssa" (.int 64 idx) hidx)
    (by rw [← hR1]; exact hrc)]
  generalize hR2 : { R1 with mem := rc.mem, next := rc.next } = R2
  rw [stage2NoEventWalk_denote_store64_imm (calls := stage2NoEventCalls gap)
    (env := env) (s := R2) (x := (BitVec.ofNat 64 0)) (p := "%tokens_out") (hp := htok)]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod]
  generalize hR3 : { R2 with mem := writeBytes R2.mem tokensOut (natToBytes 0 8) } = R3
  rw [stage2NoEventWalk_denote_store64_imm (calls := stage2NoEventCalls gap)
    (env := env) (s := R3) (x := (BitVec.ofNat 64 0)) (p := "%values_out") (hp := hval)]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod]
  generalize hR4 : { R3 with mem := writeBytes R3.mem valuesOut (natToBytes 0 8) } = R4
  rw [stage2NoEventWalk_denote_store64_imm (calls := stage2NoEventCalls gap)
    (env := env) (s := R4) (x := (BitVec.ofNat 64 0)) (p := "%sum_out") (hp := hsum)]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod]
  generalize hR5 : { R4 with mem := writeBytes R4.mem sumOut (natToBytes 0 8) } = R5
  have hR5mem : R5.mem = stage2NoEventZeroMem rc.mem tokensOut valuesOut sumOut := by
    rw [← hR5, ← hR4, ← hR3, ← hR2]
    simp only [stage2NoEventZeroMem, wordBytes]
  have hload' : readBytes R5.mem offAddr 8 = some (natToBytes eoff.toNat 8) := by
    rw [hR5mem]; exact hload
  rw [denoteCode_load64 (calls := stage2NoEventCalls gap) (env := env) (s := R5)
    (d := "%63") (p := "%off") (v := eoff) hoff hload']
  rw [denoteCode_store64 (calls := stage2NoEventCalls gap)
    (env := ("%63", .int 64 eoff) :: env) (s := R5)
    (v := "%63") (p := "%err") (x := eoff)
    (hv := (by simp only [lookupName_cons_self]))
    (hp := (by rw [lookupName_cons_ne _ _ (by decide)]; exact herr))]
  generalize hR6 : { R5 with mem := writeBytes R5.mem err (natToBytes eoff.toNat 8) } = R6
  simp only [denoteCode_nil]
  rw [← hR6, ← hR5, ← hR4, ← hR3, ← hR2, ← hR1]
  simp only [stage2NoEventIfElse510Post, stateAt, stage2NoEventStepState,
    stage2NoEventErrMem, stage2NoEventZeroMem, wordBytes]

/-- **`if.else510`'s control step**: from its entry, the block's run ends at
`cleanup580` with `if.else510` as the predecessor. -/
theorem stage2NoEventIfElse510_step {gap : Calls} (env : Env) (s : State)
    {idx eoff : BitVec 64} {c tokensOut valuesOut sumOut err offAddr : Nat}
    {rc : CallOutcome}
    (hpc : s.pc = "if.else510")
    (hidx : lookupName env "%idxprom.lcssa" = some (.int 64 idx))
    (hoff : lookupName env "%off" = some (.ptr offAddr))
    (hc : lookupName env "%c" = some (.ptr c))
    (htok : lookupName env "%tokens_out" = some (.ptr tokensOut))
    (hval : lookupName env "%values_out" = some (.ptr valuesOut))
    (hsum : lookupName env "%sum_out" = some (.ptr sumOut))
    (herr : lookupName env "%err" = some (.ptr err))
    (hrc : stage2NoEventCalls gap "od_gap_recover" [.ptr c, .int 64 idx]
      (writeBytes s.mem offAddr (natToBytes idx.toNat 8)) s.next = some rc)
    (hload : readBytes
      (stage2NoEventZeroMem rc.mem tokensOut valuesOut sumOut) offAddr 8 =
        some (natToBytes eoff.toNat 8)) :
    step (stage2NoEventCalls gap) stage2NoEventBody (stateAt env s) =
      .jump (stage2NoEventIfElse510Target env s rc tokensOut valuesOut sumOut err eoff) := by
  refine stage2NoEventWalk_step_at_block (s := stateAt env s)
    (s' := stage2NoEventIfElse510Post env s rc tokensOut valuesOut sumOut err eoff)
    (b := stage2NoEventIfElse510Block) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using stage2NoEventIfElse510Block_find
  · exact stage2NoEventIfElse510_denote env s hidx hoff hc htok hval hsum herr hrc hload
  · simp only [stage2NoEventIfElse510Block, execTerm, stage2NoEventIfElse510Target,
      stage2NoEventIfElse510Post, stage2NoEventJumpState, stage2NoEventStepState,
      stateAt, hpc]

/-! ### The tail and the row

The remainder's tail has `step510` and `evidence` as fields.  This section builds
it from the route's data — the route to the entry, the entry's register facts,
the helper's outcome, and the two observed words — so the value refusal row has
no block-shaped premise left.  The evidence's frame is
`stage2NoEventErrMem_writes_frame` widened to the `gapElse` constructor's list:
the post-block memory differs from the helper's only at the four output words,
and the five pointer cells and the index cell read through the load's `%63`. -/

/-- **The remainder arm's tail, instantiated.**  Every field of
`Stage2NoEventWalkValueRemainderTail` except the two this module proves: the
block's step is `stage2NoEventIfElse510_step`, and `cleanup580`'s return and the
`gapElse` evidence are derived at the step's target.  The caller supplies the
route to `if.else510`, the entry's parameters and locals, the index cell, the
helper's outcome, the two observed words and the reference-side data — the same
shape `if.then527`'s refusal exit takes. -/
noncomputable def Stage2NoEventWalkValueRemainderTail.ofIfElse510 {gap : Calls}
    {mem : Mem} {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s sE : State}
    {j idx eoff : Nat} {rc : CallOutcome}
    (hj : ∀ n, runFuel (stage2NoEventCalls gap) (j + n) stage2NoEventBody s =
      runFuel (stage2NoEventCalls gap) n stage2NoEventBody sE)
    (hpc : sE.pc = "if.else510")
    (hcost : j + 1 ≤ stage2NoEventWalkPotential K k + F)
    (hpar : Stage2NoEventWalkParams K sE)
    (hloc : Stage2NoEventWalkLocals K sE)
    (hidx : lookupName sE.env "%idxprom.lcssa" =
      some (.int 64 (BitVec.ofNat 64 idx)))
    (hrc : stage2NoEventCalls gap "od_gap_recover"
      [.ptr K.c, .int 64 (BitVec.ofNat 64 idx)]
      (writeBytes sE.mem (K.e + 8) (natToBytes (BitVec.ofNat 64 idx).toNat 8))
      sE.next = some rc)
    (hload : readBytes
      (stage2NoEventZeroMem rc.mem K.tokensOut K.valuesOut K.sumOut) (K.e + 8) 8 =
        some (natToBytes (BitVec.ofNat 64 eoff).toNat 8))
    (hv : readBytes rc.mem (K.e + 8) 8 = some (wordBytes 8 eoff))
    (heoffEq : eoff = idx)
    (hOffLe : eoff ≤ K.n) (hLt : eoff < 2 ^ 64)
    (hreport : Stage2NoEventRun K.a12 mem
      (stage2NoEventErrMem rc.mem K.tokensOut K.valuesOut K.sumOut K.err
        (BitVec.ofNat 64 eoff)))
    (htrace : Stage2NoEventWalkTrace K)
    (hdata : Stage2NoEventWalkReferenceRefuse K)
    (hbound : stage2NoEventBoundary K.a12 mem K.next0
      (stage2NoEventErrMem rc.mem K.tokensOut K.valuesOut K.sumOut K.err
        (BitVec.ofNat 64 eoff)) (.int 64 0)) :
    Stage2NoEventWalkValueRemainderTail gap mem F K k s := by
  let sT : State :=
    stage2NoEventIfElse510Target sE.env sE rc K.tokensOut K.valuesOut K.sumOut K.err
      (BitVec.ofNat 64 eoff)
  let m : Mem :=
    stage2NoEventErrMem rc.mem K.tokensOut K.valuesOut K.sumOut K.err
      (BitVec.ofNat 64 eoff)
  let sR : State :=
    stateAt (("%retval.14", .int 64 0) ::
        ("%63", .int 64 (BitVec.ofNat 64 eoff)) :: sE.env)
      (stage2NoEventJumpState sE m rc.next "cleanup580" "if.else510")
  have hsTenv : sT.env = ("%63", .int 64 (BitVec.ofNat 64 eoff)) :: sE.env :=
    stage2NoEventIfElse510Target_env _ _ _ _ _ _ _ _
  have hsTmem : sT.mem = m :=
    stage2NoEventIfElse510Target_mem _ _ _ _ _ _ _ _
  have hstep : step (stage2NoEventCalls gap) stage2NoEventBody sE = .jump sT :=
    stage2NoEventIfElse510_step sE.env sE (idx := BitVec.ofNat 64 idx)
      (eoff := BitVec.ofNat 64 eoff) (offAddr := K.e + 8) hpc hidx hloc.off
      hpar.c hpar.tokensOut hpar.valuesOut hpar.sumOut hpar.err hrc hload
  have hinc0 : phiIncoming "if.else510" cleanup580Incoming =
      some (.imm (.int 64 0)) := by decide
  have hclean : step (stage2NoEventCalls gap) stage2NoEventBody sT =
      .ret (some (.int 64 0)) sR :=
    stage2NoEventCleanup_step (gap := gap)
      (("%63", .int 64 (BitVec.ofNat 64 eoff)) :: sE.env)
      (stage2NoEventJumpState sE m rc.next "cleanup580" "if.else510")
      "if.else510" rfl rfl hinc0
      (c := K.c) (e := K.e) (stk := K.stk) (xj := K.xj)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact hpar.c)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact hpar.e)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact hpar.stk)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact hloc.xj)
  have hsym : UnchangedOutside m rc.mem
      (stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err) :=
    fun a ha =>
      (stage2NoEventErrMem_writes_frame (m := rc.mem) (t := K.tokensOut)
        (v := K.valuesOut) (su := K.sumOut) (e := K.err)
        (x := BitVec.ofNat 64 eoff) a ha).symm
  have hTframe : UnchangedOutside sT.mem rc.mem
      (stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err ++
        (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
          [(K.next0, K.nextEnd - K.next0)])) := by
    rw [hsTmem]
    exact hsym.of_covered (fun r hr =>
      ⟨r, List.mem_append_left _ hr, le_rfl, le_rfl⟩)
  have hev : Stage2NoEventWalkRefusalEvidence K sT :=
    .gapElse rc eoff idx
      (by rw [hsTenv, lookupName_cons_ne _ _ (by decide)]; exact hpar.tokensOut)
      (by rw [hsTenv, lookupName_cons_ne _ _ (by decide)]; exact hpar.valuesOut)
      (by rw [hsTenv, lookupName_cons_ne _ _ (by decide)]; exact hpar.sumOut)
      (by rw [hsTenv, lookupName_cons_ne _ _ (by decide)]; exact hpar.err)
      (by rw [hsTenv, lookupName_cons_ne _ _ (by decide)]; exact hloc.off)
      (by rw [hsTenv, lookupName_cons_ne _ _ (by decide)]; exact hidx)
      hv hTframe heoffEq hOffLe hLt
  exact Stage2NoEventWalkValueRemainderTail.mk j sE sT sR m hpc hj hcost hstep
    hclean hsTmem hev hreport htrace hdata hbound

/-- **The value remainder's refusal row, unconditional in `if.else510`.**  The
tail above, and the row is its `.terminal` constructor: the value class's
`.ws`/`.other` dispatch refuses, and no part of the block's denotation remains a
premise. -/
noncomputable def stage2NoEventWalkValueRemainderRow {gap : Calls} {mem : Mem}
    {F : Nat} {K : Stage2NoEventWalkCarry} {k : Nat} {s sE : State}
    {j idx eoff : Nat} {rc : CallOutcome}
    (hj : ∀ n, runFuel (stage2NoEventCalls gap) (j + n) stage2NoEventBody s =
      runFuel (stage2NoEventCalls gap) n stage2NoEventBody sE)
    (hpc : sE.pc = "if.else510")
    (hcost : j + 1 ≤ stage2NoEventWalkPotential K k + F)
    (hpar : Stage2NoEventWalkParams K sE)
    (hloc : Stage2NoEventWalkLocals K sE)
    (hidx : lookupName sE.env "%idxprom.lcssa" =
      some (.int 64 (BitVec.ofNat 64 idx)))
    (hrc : stage2NoEventCalls gap "od_gap_recover"
      [.ptr K.c, .int 64 (BitVec.ofNat 64 idx)]
      (writeBytes sE.mem (K.e + 8) (natToBytes (BitVec.ofNat 64 idx).toNat 8))
      sE.next = some rc)
    (hload : readBytes
      (stage2NoEventZeroMem rc.mem K.tokensOut K.valuesOut K.sumOut) (K.e + 8) 8 =
        some (natToBytes (BitVec.ofNat 64 eoff).toNat 8))
    (hv : readBytes rc.mem (K.e + 8) 8 = some (wordBytes 8 eoff))
    (heoffEq : eoff = idx)
    (hOffLe : eoff ≤ K.n) (hLt : eoff < 2 ^ 64)
    (hreport : Stage2NoEventRun K.a12 mem
      (stage2NoEventErrMem rc.mem K.tokensOut K.valuesOut K.sumOut K.err
        (BitVec.ofNat 64 eoff)))
    (htrace : Stage2NoEventWalkTrace K)
    (hdata : Stage2NoEventWalkReferenceRefuse K)
    (hbound : stage2NoEventBoundary K.a12 mem K.next0
      (stage2NoEventErrMem rc.mem K.tokensOut K.valuesOut K.sumOut K.err
        (BitVec.ofNat 64 eoff)) (.int 64 0)) :
    Stage2NoEventWalkRow (stage2NoEventCalls gap) mem F K k s :=
  (Stage2NoEventWalkValueRemainderTail.ofIfElse510 hj hpc hcost hpar hloc hidx
    hrc hload hv heoffEq hOffLe hLt hreport htrace hdata hbound).row

/-! ### Axiom footprints -/

#print axioms stage2NoEventIfElse510Target_env
#print axioms stage2NoEventIfElse510Target_mem
#print axioms stage2NoEventIfElse510_denote
#print axioms stage2NoEventIfElse510_step
#print axioms Stage2NoEventWalkValueRemainderTail.ofIfElse510
#print axioms stage2NoEventWalkValueRemainderRow

end LeanLLVM.Refinement
