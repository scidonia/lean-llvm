/-
The no-event walk's terminal class.

A head reaches the dispatch with the document's byte in `%3`; the count classes
close a cycle, and the terminal ones leave the loop for `cleanup580`.  The exit a
terminal route produces is `Stage2NoEventWalkExit` (`JsonStage2NoEventWalkPremises`),
stated at the route's **post-block endpoint** `sT`: the terminal block's stores are
visible there, its in-block `phi` cells remain in the environment, and the
remaining run is `cleanup580`'s one step to the `ret`.  Its `route` field is the
run equality from the head to `sT`, its `run` the two-step return from `sT`, and
its evidence is the route's own registers — the acceptance's three words, or one
of the five refusal shapes (`zeroStore`, `errStore`, `gapElse`, `gapNumber`,
`gapLiteral`).

This module produces those exits and the rows that carry them:

* the **route composition**: a route from the head to a terminal block's entry,
  and the block's own control step, give the route to the block's target
  (`Stage2NoEventWalkRunTo.extend`), and the target's `cleanup580` step gives the
  `Exit`'s returning run at the route's count plus one
  (`Stage2NoEventWalkRunTo.run_of_cleanup`);
* the **terminal entries**: every block whose terminator is `cleanup580`'s — the
  fifteen zero-store entries, the two `errStore` cleanups, the two gap routes,
  `if.then527` and `accept` — pinned against the parsed body; the census below
  checks the entry set against the `phi`'s own incoming list in both directions;
* the **refusal shapes' inhabitants**: `zeroStore` at the fifteen zero-store
  entries (the generic producer over `stage2NoEventZeroStoreInstrs` for the
  thirteen entries whose body is the four stores, and `if.then38`'s `phi`-prefixed
  and `if.then360`'s `%ep` index-read bodies with their own prefixes), `errStore`
  at `cleanup.thread` and `cleanup287.thread` (each with its own offset `phi` and
  `lifetime.end` operand), and `gapLiteral` from its evidence at `if.then527`.
  `gapElse` (`if.else510`) and `gapNumber` (`cleanup491.thread`) are pinned and
  their exit is the shared refusal seam — `stage2NoEventRefuse_exit` from the
  shape's evidence and the record's boundary — but this module does not derive
  their `denoteCode` chains, so their evidence is the route's to supply;
* the **acceptance**: `stage2NoEventAccept_exit`, from the three stores' reading at
  the target, the carried delta and the record's boundary.  `accept`'s own run is
  `JsonStage2NoEventWalkTerminal`'s (`acceptBlock_find`, `stage2NoEventAccept_step`),
  so this module states the exit and the seam, not a second route.

Each refusal producer takes the walk's frame at the head (`Stage2NoEventWalkInv`),
the route to the block's entry, the block's entry registers
(`Stage2NoEventWalkParams`, `Stage2NoEventWalkLocals`), the route's own
word/`CallOutcome` facts, the trace the walk has consumed, the price
(`j + 1 ≤ Φ K k + F`) and the record's report at the returned memory.  The
boundary is **derived** wherever the block's own stores are the witness
(`zeroStore`, `gapLiteral`: the four words read back, the frame composed from the
walk's, the route's and the call's); the two seams `stage2NoEventRefuse_exit` and
`stage2NoEventAccept_exit` take it as an argument — `zeroStore`/`errStore`-at-a-
route's-zeros establish it there.  The report is the walk's residue
(`Stage2NoEventRun`); nothing in the terminal class reads it, and the obligation
reads the boundary.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkPremises

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

/-! ### Reaching a terminal block's target

A terminal block is entered by its predecessor's branch; the route the dispatch
proves ends at that entry.  The exit is stated one step further on — at the
block's target, where `cleanup580` has yet to run — so the two compositions the
producers open with are these. -/

/-- **One jump step, in fuel.**  From a state whose step jumps, one unit of fuel
is the target's run. -/
theorem stage2NoEventRunFuel_step_jump {calls : Calls} {f : Function} {s s' : State}
    (h : step calls f s = .jump s') (n : Nat) :
    runFuel calls (n + 1) f s = runFuel calls n f s' := by
  cases n with
  | zero => simp only [runFuel, h]
  | succ n => simp only [runFuel, h]

/-- **A route extended by one block.**  The route to a terminal block's entry and
the block's own control step give the route to its target. -/
theorem Stage2NoEventWalkRunTo.extend {calls : Calls} {s sE sT : State}
    (h : Stage2NoEventWalkRunTo calls s sE)
    (hstep : step calls stage2NoEventBody sE = .jump sT) :
    Stage2NoEventWalkRunTo calls s sT := by
  obtain ⟨j, hj⟩ := h
  refine ⟨j + 1, fun n => ?_⟩
  rw [show j + 1 + n = j + (n + 1) from by omega, hj (n + 1),
    stage2NoEventRunFuel_step_jump hstep n]

/-- **The returning run of a route.**  The route's count plus one — the count to
the terminal block's entry and the block's own step — and the target's
`cleanup580` step reach the `ret` at the target's memory.  The `Exit`'s `run`
names this fuel as `q + 2` at `q = j + 1`. -/
theorem Stage2NoEventWalkRunTo.run_of_cleanup {calls : Calls} {f : Function}
    {s sE sT s' : State} {j : Nat} {v : BitVec 64} {m : Mem}
    (hj : ∀ n, runFuel calls (j + n) f s = runFuel calls n f sE)
    (hstep : step calls f sE = .jump sT)
    (hret : step calls f sT = .ret (some (.int 64 v)) s')
    (hms : s'.mem = m) :
    runFuel calls (j + 1 + 2) f s = some (.ret (some (.int 64 v)) m) := by
  have h3 : runFuel calls 3 f sE = some (.ret (some (.int 64 v)) m) := by
    simp only [runFuel, hstep]
    simp only [hret, hms]
  rw [show j + 1 + 2 = j + 3 from by omega, hj 3]
  exact h3

/-! ### The zero-store family

Fifteen entries store three zeroes and one word at `%err` and branch to
`cleanup580`: the literal refusals' zero rule, at the entry's own index or `n`.
The block binds nothing but the word it stores (one entry's `phi`, one entry's
`%conv362`), so the environment carries the four output pointers and the return
block's registers unmoved. -/

/-- The zero-store entries' instructions, at the register whose word lands at
`%err`. -/
def stage2NoEventZeroStoreInstrs (w : String) : List Instr :=
  [ Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
      (Operand.reg "%tokens_out"),
    Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
      (Operand.reg "%values_out"),
    Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
      (Operand.reg "%sum_out"),
    Instr.store (Ty.int 64) (Operand.reg w) (Operand.reg "%err")]

/-- **A zero-store entry's body**, from the four pointers and the word's own
register. -/
theorem stage2NoEventZeroStore_denote {calls : Calls} (env : Env) (s : State)
    (w : String) {tokensOut valuesOut sumOut err : Nat} {x : BitVec 64}
    (htok : lookupName env "%tokens_out" = some (.ptr tokensOut))
    (hval : lookupName env "%values_out" = some (.ptr valuesOut))
    (hsum : lookupName env "%sum_out" = some (.ptr sumOut))
    (herr : lookupName env "%err" = some (.ptr err))
    (hw : lookupName env w = some (.int 64 x)) :
    denoteCode calls (stage2NoEventZeroStoreInstrs w) (stateAt env s) =
      some (stateAt env
        (stage2NoEventStepState s
          (stage2NoEventErrMem s.mem tokensOut valuesOut sumOut err x) s.next)) := by
  unfold stage2NoEventZeroStoreInstrs
  rw [stage2NoEventWalk_denote_store64_imm (calls := calls) (env := env) (s := s)
    (x := (BitVec.ofNat 64 0)) (p := "%tokens_out") (hp := htok)]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod]
  generalize hS1 : { s with mem := writeBytes s.mem tokensOut (natToBytes 0 8) } = S1
  rw [stage2NoEventWalk_denote_store64_imm (calls := calls) (env := env) (s := S1)
    (x := (BitVec.ofNat 64 0)) (p := "%values_out") (hp := hval)]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod]
  generalize hS2 : { S1 with mem := writeBytes S1.mem valuesOut (natToBytes 0 8) } = S2
  rw [stage2NoEventWalk_denote_store64_imm (calls := calls) (env := env) (s := S2)
    (x := (BitVec.ofNat 64 0)) (p := "%sum_out") (hp := hsum)]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod]
  generalize hS3 : { S2 with mem := writeBytes S2.mem sumOut (natToBytes 0 8) } = S3
  rw [denoteCode_store64 (calls := calls) (env := env) (s := S3)
    (v := w) (p := "%err") (x := x) (hv := hw) (hp := herr)]
  simp only [denoteCode_nil]
  rw [← hS3, ← hS2, ← hS1]
  simp only [stage2NoEventErrMem, stage2NoEventZeroMem, wordBytes, stateAt,
    stage2NoEventStepState]

/-- **The zero-store entry's target**: `cleanup580` with the three zeros and the
word at `%err` written, the entry's environment carried and the entry's name as
the `phi`'s predecessor. -/
def stage2NoEventZeroTarget (env : Env) (s : State) (tokensOut valuesOut sumOut err : Nat)
    (x : BitVec 64) (blk : String) : State :=
  stateAt env
    (stage2NoEventJumpState s (stage2NoEventErrMem s.mem tokensOut valuesOut sumOut err x)
      s.next "cleanup580" blk)

/-- **A zero-store entry's control step**, from its `pc` and its four pointers. -/
theorem stage2NoEventZero_step {calls : Calls} (env : Env) (s : State)
    (blk w : String) {b : Block} {tokensOut valuesOut sumOut err : Nat} {x : BitVec 64}
    (hpc : s.pc = blk) (hfind : stage2NoEventBody.findBlock blk = some b)
    (hbody : b.instrs = stage2NoEventZeroStoreInstrs w)
    (hterm : b.term = Term.br "cleanup580")
    (htok : lookupName env "%tokens_out" = some (.ptr tokensOut))
    (hval : lookupName env "%values_out" = some (.ptr valuesOut))
    (hsum : lookupName env "%sum_out" = some (.ptr sumOut))
    (herr : lookupName env "%err" = some (.ptr err))
    (hw : lookupName env w = some (.int 64 x)) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stage2NoEventZeroTarget env s tokensOut valuesOut sumOut err x blk) := by
  have hcode : denoteCode calls b.instrs (stateAt env s) =
      some (stateAt env
        (stage2NoEventStepState s
          (stage2NoEventErrMem s.mem tokensOut valuesOut sumOut err x) s.next)) := by
    rw [hbody]
    exact stage2NoEventZeroStore_denote env s w htok hval hsum herr hw
  refine stage2NoEventWalk_step_at_block (s := stateAt env s)
    (s' := stateAt env
      (stage2NoEventStepState s
        (stage2NoEventErrMem s.mem tokensOut valuesOut sumOut err x) s.next))
    (b := b) (c := .jump (stage2NoEventZeroTarget env s tokensOut valuesOut sumOut err x blk))
    ?_ hcode ?_
  · simpa only [stateAt, hpc] using hfind
  · rw [hterm]
    simp only [execTerm, stage2NoEventZeroTarget, stage2NoEventJumpState,
      stage2NoEventStepState, stateAt, hpc]

/-! ### The refusal word's four reads

The refusal record's memory is the three zero words and one word at `%err`; the
boundary reads all four back.  The four slots are pairwise separate at the
record's own separation, so each store leaves the others' words. -/

/-- **The three zero words and the word at `%err`, read back.** -/
theorem stage2NoEventErrMem_reads {m : Mem} {tokensOut valuesOut sumOut err : Nat}
    {x : BitVec 64} (hsep : DisjointRegions
      (stage2NoEventWrites tokensOut valuesOut sumOut err)) :
    readBytes (stage2NoEventErrMem m tokensOut valuesOut sumOut err x) tokensOut 8 =
      some (wordBytes 8 0) ∧
    readBytes (stage2NoEventErrMem m tokensOut valuesOut sumOut err x) valuesOut 8 =
      some (wordBytes 8 0) ∧
    readBytes (stage2NoEventErrMem m tokensOut valuesOut sumOut err x) sumOut 8 =
      some (wordBytes 8 0) ∧
    readBytes (stage2NoEventErrMem m tokensOut valuesOut sumOut err x) err 8 =
      some (wordBytes 8 x.toNat) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := stage2NoEventWrites_slots hsep
  have hx : natToBytes x.toNat 8 = wordBytes 8 x.toNat := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [stage2NoEventErrMem, stage2NoEventZeroMem, hx]
    rw [readBytes_wordBytes_frame (addr := err) (v := x.toNat) (p := tokensOut)
      (n := 8) (by omega)]
    rw [readBytes_wordBytes_frame (addr := sumOut) (v := 0) (p := tokensOut)
      (n := 8) (by omega)]
    rw [readBytes_wordBytes_frame (addr := valuesOut) (v := 0) (p := tokensOut)
      (n := 8) (by omega)]
    exact stage2NoEventRead_own
  · simp only [stage2NoEventErrMem, stage2NoEventZeroMem, hx]
    rw [readBytes_wordBytes_frame (addr := err) (v := x.toNat) (p := valuesOut)
      (n := 8) (by omega)]
    rw [readBytes_wordBytes_frame (addr := sumOut) (v := 0) (p := valuesOut)
      (n := 8) (by omega)]
    exact stage2NoEventRead_own
  · simp only [stage2NoEventErrMem, stage2NoEventZeroMem, hx]
    rw [readBytes_wordBytes_frame (addr := err) (v := x.toNat) (p := sumOut)
      (n := 8) (by omega)]
    exact stage2NoEventRead_own
  · simp only [stage2NoEventErrMem, stage2NoEventZeroMem, hx]
    exact stage2NoEventRead_own

/-- **The refusal memory's writes lie inside the three zeros and the word.**  The
four stores are the output words, so the caller's memory and the refusal's agree
outside them. -/
theorem stage2NoEventErrMem_writes_frame {m : Mem} {t v su e : Nat} {x : BitVec 64} :
    UnchangedOutside m (stage2NoEventErrMem m t v su e x)
      (stage2NoEventWrites t v su e) := by
  have hmemW (a : Nat) (ha : (a, 8) ∈ stage2NoEventWrites t v su e) :
      ∃ q ∈ stage2NoEventWrites t v su e, q.1 ≤ a ∧ a + 8 ≤ q.1 + q.2 :=
    ⟨(a, 8), ha, le_rfl, le_rfl⟩
  exact ((((UnchangedOutside.refl' m _).write_le (bs := natToBytes 0 8)
    (hmemW t (by simp [stage2NoEventWrites]))
    (by simp [natToBytes_length])).write_le (bs := natToBytes 0 8)
    (hmemW v (by simp [stage2NoEventWrites]))
    (by simp [natToBytes_length])).write_le (bs := natToBytes 0 8)
    (hmemW su (by simp [stage2NoEventWrites]))
    (by simp [natToBytes_length])).write_le (bs := natToBytes x.toNat 8)
    (hmemW e (by simp [stage2NoEventWrites]))
    (by simp [natToBytes_length])

/-- **A zero-store refusal's evidence**, at a state that carries the four
read-backs and the pointers. -/
theorem stage2NoEventZero_evidence {K : Stage2NoEventWalkCarry} {sT : State} {eoff : Nat}
    (htok : lookupName sT.env "%tokens_out" = some (.ptr K.tokensOut))
    (hval : lookupName sT.env "%values_out" = some (.ptr K.valuesOut))
    (hsum : lookupName sT.env "%sum_out" = some (.ptr K.sumOut))
    (herr : lookupName sT.env "%err" = some (.ptr K.err))
    (hread : readBytes sT.mem K.err 8 = some (wordBytes 8 eoff))
    (hle : eoff ≤ K.n) (hlt : eoff < 2 ^ 64) :
    Stage2NoEventWalkRefusalEvidence K sT :=
  .zeroStore eoff htok hval hsum herr hread hle hlt

/-! ### The shared exit plumbing

Every refusal route has the same shape at the end: a route to the block's entry,
the block's control step, `cleanup580`'s returning step, the evidence at the
block's target and the record's boundary at the returned memory.  These two
producers name that shape once; each route below derives its evidence and its
boundary and calls one of them. -/

/-- **A refusal's exit from its evidence and boundary.** -/
theorem stage2NoEventRefuse_exit {gap : Calls} {mem : Mem} {F k : Nat}
    {K : Stage2NoEventWalkCarry} {s sE sT sR : State} {j : Nat} {m : Mem}
    (hj : ∀ n, runFuel (stage2NoEventCalls gap) (j + n) stage2NoEventBody s =
      runFuel (stage2NoEventCalls gap) n stage2NoEventBody sE)
    (hstep : step (stage2NoEventCalls gap) stage2NoEventBody sE = .jump sT)
    (hclean : step (stage2NoEventCalls gap) stage2NoEventBody sT =
      .ret (some (.int 64 0)) sR)
    (hmR : sR.mem = m)
    (hcost : j + 1 ≤ stage2NoEventWalkPotential K k + F)
    (hreport : Stage2NoEventRun K.a12 mem m)
    (htrace : Stage2NoEventWalkTrace K sE)
    (hev : Stage2NoEventWalkRefusalEvidence K sT)
    (hbound : stage2NoEventBoundary K.a12 mem K.next0 m (.int 64 0)) :
    Stage2NoEventWalkExit (stage2NoEventCalls gap) mem F K k s := by
  obtain ⟨obs, toks, hrel, hobsLen, htermsEq, -⟩ := htrace
  exact .refuse (j + 1) m sT (Stage2NoEventWalkRunTo.extend ⟨j, hj⟩ hstep) hcost
    (Stage2NoEventWalkRunTo.run_of_cleanup (f := stage2NoEventBody) (j := j) (v := 0)
      (m := m) hj hstep hclean hmR)
    hev obs toks hrel hobsLen htermsEq hreport hbound

/-- **An acceptance's exit from its reading and boundary.**  The acceptance's
carry delta is the constructor's own: the target carry `K'` has strictly more
tokens than the head's — `K.tok < K'.tok`, since a scalar route consumes one and
the pair classes (`{}`, `[]`, `["x"]`) two — and keeps the argument list and the
caller's cursor.  The exact count is `K'`'s: `AcceptAcc K' sT` binds the three
stored words and `obs.length = K'.tok` binds the trace's length, so the
inequality alone is not read as a count. -/
theorem stage2NoEventAccept_exit {gap : Calls} {mem : Mem} {F k : Nat}
    {K K' : Stage2NoEventWalkCarry} {s sE sT sR : State} {j : Nat} {m : Mem}
    {obs : List ConsumerEvent} {toks : List Token}
    (hj : ∀ n, runFuel (stage2NoEventCalls gap) (j + n) stage2NoEventBody s =
      runFuel (stage2NoEventCalls gap) n stage2NoEventBody sE)
    (hstep : step (stage2NoEventCalls gap) stage2NoEventBody sE = .jump sT)
    (hclean : step (stage2NoEventCalls gap) stage2NoEventBody sT =
      .ret (some (.int 64 1)) sR)
    (hmR : sR.mem = m)
    (hcost : j + 1 ≤ stage2NoEventWalkPotential K k + F)
    (htokK : K.tok < K'.tok) (ha12 : K'.a12 = K.a12) (hn0 : K'.next0 = K.next0)
    (hacc : Stage2NoEventWalkAcceptAcc K' sT)
    (hrel : Stage2NoEvent K.bs K'.arena obs toks)
    (hobsLen : obs.length = K'.tok)
    (htermsEq : K'.terms = (obs.map ConsumerEvent.terms).sum)
    (hreport : Stage2NoEventRun K'.a12 mem m)
    (hbound : stage2NoEventBoundary K'.a12 mem K'.next0 m (.int 64 1)) :
    Stage2NoEventWalkExit (stage2NoEventCalls gap) mem F K k s :=
  .accept K' (j + 1) m sT (Stage2NoEventWalkRunTo.extend ⟨j, hj⟩ hstep) hcost
    (Stage2NoEventWalkRunTo.run_of_cleanup (f := stage2NoEventBody) (j := j) (v := 1)
      (m := m) hj hstep hclean hmR)
    htokK ha12 hn0 hacc obs toks hrel hobsLen htermsEq hreport hbound

/-- **The terminal row from its exit.** -/
def stage2NoEventWalkTerminalRow {calls : Calls} {mem : Mem} {F : Nat}
    {K : Stage2NoEventWalkCarry} {k : Nat} {s : State}
    (exit : Stage2NoEventWalkExit calls mem F K k s) :
    Stage2NoEventWalkRow calls mem F K k s :=
  .terminal exit

/-! ### The frame the boundary reads

The record's boundary needs the returned memory to agree with the caller's
outside the output words and the run's own regions.  The head's frame and the
route's compose, the route's call frame extends that, and each block's writes lie
inside the output words, so the four steps compose to one frame per route. -/

/-- **The frames compose to the boundary's.**  The walk's frame at the head, the
route's, the call's, and the entry's stores: from the caller's memory to the
target's, outside the output words and the run's regions. -/
theorem stage2NoEventBoundaryFrame {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s sE : State} (h : Stage2NoEventWalkInv K mem s)
    {sM m : Mem}
    (hroute : UnchangedOutside s.mem sE.mem
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]))
    (hcall : UnchangedOutside sE.mem sM
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]))
    (hstores : UnchangedOutside sM m
      (stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err)) :
    UnchangedOutside mem m
      (stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err ++
        (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
          [(K.next0, K.nextEnd - K.next0)])) := by
  have h0 : UnchangedOutside mem sE.mem
      (stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err ++
        (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
          [(K.next0, K.nextEnd - K.next0)])) :=
    ((h.walkFrame.trans hroute).of_covered (fun r hr =>
      ⟨r, List.mem_append_right _ hr, le_rfl, le_rfl⟩))
  have h1 : UnchangedOutside mem sM
      (stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err ++
        (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
          [(K.next0, K.nextEnd - K.next0)])) :=
    h0.trans (hcall.of_covered (fun r hr =>
      ⟨r, List.mem_append_right _ hr, le_rfl, le_rfl⟩))
  exact h1.trans (hstores.of_covered (fun r hr =>
    ⟨r, List.mem_append_left _ hr, le_rfl, le_rfl⟩))

/-- **A zero-store entry's refusal exit.**  The blocks' own run is the caller's
(the pin's `denoteCode` and control step); what this producer adds is the target's
`cleanup580` step, the evidence read back at the target, the returning run, and the
record's boundary from the walk's frame and the route's. -/
theorem stage2NoEventZero_exit {gap : Calls} {mem : Mem} {F k : Nat}
    {K : Stage2NoEventWalkCarry} {s sE sT sR : State} {j : Nat} {x : BitVec 64} {m : Mem}
    (hj : ∀ n, runFuel (stage2NoEventCalls gap) (j + n) stage2NoEventBody s =
      runFuel (stage2NoEventCalls gap) n stage2NoEventBody sE)
    (hstep : step (stage2NoEventCalls gap) stage2NoEventBody sE = .jump sT)
    (hclean : step (stage2NoEventCalls gap) stage2NoEventBody sT =
      .ret (some (.int 64 0)) sR)
    (hmR : sR.mem = m)
    (hm : m = stage2NoEventErrMem sE.mem K.tokensOut K.valuesOut K.sumOut K.err x)
    (hmS : sT.mem = m)
    (htok : lookupName sT.env "%tokens_out" = some (.ptr K.tokensOut))
    (hval : lookupName sT.env "%values_out" = some (.ptr K.valuesOut))
    (hsum : lookupName sT.env "%sum_out" = some (.ptr K.sumOut))
    (herr : lookupName sT.env "%err" = some (.ptr K.err))
    (hle : x.toNat ≤ K.n)
    (hcost : j + 1 ≤ stage2NoEventWalkPotential K k + F)
    (hreport : Stage2NoEventRun K.a12 mem m)
    (htrace : Stage2NoEventWalkTrace K sE)
    (hrouteFrame : UnchangedOutside s.mem sE.mem
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]))
    (h : Stage2NoEventWalkInv K mem s) :
    Stage2NoEventWalkExit (stage2NoEventCalls gap) mem F K k s := by
  obtain ⟨hTok, hVal, hSum, hErr⟩ :=
    stage2NoEventErrMem_reads (m := sE.mem) (x := x)
      (stage2NoEventRegions_writes h.separate)
  refine stage2NoEventRefuse_exit hj hstep hclean hmR hcost hreport htrace
    (stage2NoEventZero_evidence htok hval hsum herr (by rw [hmS, hm]; exact hErr)
      hle x.isLt) ?_
  refine stage2NoEventBoundary_refusal h (by rw [hm]; exact hTok) (by rw [hm]; exact hVal)
    (by rw [hm]; exact hSum) (by rw [hm]; exact hErr) hle ?_
  have hw : UnchangedOutside sE.mem m
      (stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err) := by
    rw [hm]
    have hmemW (a : Nat) (ha : (a, 8) ∈ stage2NoEventWrites K.tokensOut
        K.valuesOut K.sumOut K.err) :
        ∃ q ∈ stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err,
          q.1 ≤ a ∧ a + 8 ≤ q.1 + q.2 :=
      ⟨(a, 8), ha, le_rfl, le_rfl⟩
    exact ((((UnchangedOutside.refl' sE.mem _).write_le
      (hmemW K.tokensOut (by simp [stage2NoEventWrites]))
      (by simp [wordBytes, natToBytes_length])).write_le
      (hmemW K.valuesOut (by simp [stage2NoEventWrites]))
      (by simp [wordBytes, natToBytes_length])).write_le
      (hmemW K.sumOut (by simp [stage2NoEventWrites]))
      (by simp [wordBytes, natToBytes_length])).write_le
      (hmemW K.err (by simp [stage2NoEventWrites]))
      (by simp [natToBytes_length])
  exact stage2NoEventBoundaryFrame h hrouteFrame (UnchangedOutside.refl' _ _) hw

/-- **A zero-store entry's exit**, from the pin. -/
theorem stage2NoEventZeroBlock_exit {gap : Calls} {mem : Mem} {F k : Nat}
    {K : Stage2NoEventWalkCarry} {s sE : State} {j : Nat} {blk w : String} {b : Block}
    {x : BitVec 64}
    (hj : ∀ n, runFuel (stage2NoEventCalls gap) (j + n) stage2NoEventBody s =
      runFuel (stage2NoEventCalls gap) n stage2NoEventBody sE)
    (hpc : sE.pc = blk) (hfind : stage2NoEventBody.findBlock blk = some b)
    (hbody : b.instrs = stage2NoEventZeroStoreInstrs w)
    (hterm : b.term = Term.br "cleanup580")
    (hinc : phiIncoming blk cleanup580Incoming = some (.imm (.int 64 0)))
    (hpar : Stage2NoEventWalkParams K sE)
    (hloc : Stage2NoEventWalkLocals K sE)
    (hw : lookupName sE.env w = some (.int 64 x))
    (hle : x.toNat ≤ K.n)
    (hcost : j + 1 ≤ stage2NoEventWalkPotential K k + F)
    (hreport : Stage2NoEventRun K.a12 mem
      (stage2NoEventErrMem sE.mem K.tokensOut K.valuesOut K.sumOut K.err x))
    (htrace : Stage2NoEventWalkTrace K sE)
    (hrouteFrame : UnchangedOutside s.mem sE.mem
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]))
    (h : Stage2NoEventWalkInv K mem s) :
    Stage2NoEventWalkExit (stage2NoEventCalls gap) mem F K k s := by
  have hstep : step (stage2NoEventCalls gap) stage2NoEventBody sE =
      .jump (stage2NoEventZeroTarget sE.env sE K.tokensOut K.valuesOut K.sumOut K.err x
        blk) :=
    stage2NoEventZero_step sE.env sE blk w hpc hfind hbody hterm
      hpar.tokensOut hpar.valuesOut hpar.sumOut hpar.err hw
  have hclean : step (stage2NoEventCalls gap) stage2NoEventBody
      (stage2NoEventZeroTarget sE.env sE K.tokensOut K.valuesOut K.sumOut K.err x blk) =
      .ret (some (.int 64 0))
        (stateAt (("%retval.14", .int 64 0) :: sE.env)
          (stage2NoEventJumpState sE
            (stage2NoEventErrMem sE.mem K.tokensOut K.valuesOut K.sumOut K.err x)
            sE.next "cleanup580" blk)) :=
    stage2NoEventCleanup_step (gap := gap) sE.env
      (stage2NoEventJumpState sE
        (stage2NoEventErrMem sE.mem K.tokensOut K.valuesOut K.sumOut K.err x)
        sE.next "cleanup580" blk) blk rfl rfl hinc hpar.c hpar.e hpar.stk hloc.xj
  have henvT : (stage2NoEventZeroTarget sE.env sE K.tokensOut K.valuesOut K.sumOut K.err x
      blk).env = sE.env := by
    simp only [stage2NoEventZeroTarget, stage2NoEventJumpState, stateAt]
  have hmemT : (stage2NoEventZeroTarget sE.env sE K.tokensOut K.valuesOut K.sumOut K.err x
      blk).mem =
      stage2NoEventErrMem sE.mem K.tokensOut K.valuesOut K.sumOut K.err x := by
    simp only [stage2NoEventZeroTarget, stage2NoEventJumpState, stateAt]
  exact stage2NoEventZero_exit
    (m := stage2NoEventErrMem sE.mem K.tokensOut K.valuesOut K.sumOut K.err x)
    hj hstep hclean (by simp only [stateAt, stage2NoEventJumpState]) rfl hmemT
    (by rw [henvT]; exact hpar.tokensOut)
    (by rw [henvT]; exact hpar.valuesOut)
    (by rw [henvT]; exact hpar.sumOut)
    (by rw [henvT]; exact hpar.err)
    hle hcost hreport htrace hrouteFrame h

/-- **A zero-store entry's row**, from the pin: the terminal row at the exit. -/
def stage2NoEventZeroBlock_row {gap : Calls} {mem : Mem} {F k : Nat}
    {K : Stage2NoEventWalkCarry} {s sE : State} {j : Nat} {blk w : String} {b : Block}
    {x : BitVec 64}
    (h : Stage2NoEventWalkHead K mem k s)
    (hj : ∀ n, runFuel (stage2NoEventCalls gap) (j + n) stage2NoEventBody s =
      runFuel (stage2NoEventCalls gap) n stage2NoEventBody sE)
    (hpc : sE.pc = blk) (hfind : stage2NoEventBody.findBlock blk = some b)
    (hbody : b.instrs = stage2NoEventZeroStoreInstrs w)
    (hterm : b.term = Term.br "cleanup580")
    (hinc : phiIncoming blk cleanup580Incoming = some (.imm (.int 64 0)))
    (hpar : Stage2NoEventWalkParams K sE)
    (hloc : Stage2NoEventWalkLocals K sE)
    (hw : lookupName sE.env w = some (.int 64 x))
    (hle : x.toNat ≤ K.n)
    (hcost : j + 1 ≤ stage2NoEventWalkPotential K k + F)
    (hreport : Stage2NoEventRun K.a12 mem
      (stage2NoEventErrMem sE.mem K.tokensOut K.valuesOut K.sumOut K.err x))
    (htrace : Stage2NoEventWalkTrace K sE)
    (hrouteFrame : UnchangedOutside s.mem sE.mem
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)])) :
    Stage2NoEventWalkRow (stage2NoEventCalls gap) mem F K k s :=
  stage2NoEventWalkTerminalRow
    (stage2NoEventZeroBlock_exit hj hpc hfind hbody hterm hinc hpar hloc hw hle
      hcost hreport htrace hrouteFrame h.inv)

/-! ### The terminal entries' pins

The entries whose terminator is `cleanup580`'s, each pinned against the parsed
body: the block's instruction list and the `findBlock` equation.  A pin is a
`decide` on the parse, so a re-capture that moves an entry fails the build here.
The zero-store entries' instruction lists are `stage2NoEventZeroStoreInstrs` at the
register whose word lands at `%err`; the two prefixed entries (`if.then38`'s
offset `phi`, `if.then360`'s documented index read) are pinned literally. -/

/-- `if.then` — the empty stream's flush — is `JsonStage2NoEventWalkTerminal`'s
`flushBlock`; this is its zero-rule form, so the flush is one of the family's
entries without a second pin of the same block. -/
theorem stage2NoEventFlushBlock_instrs :
    flushBlock.instrs = stage2NoEventZeroStoreInstrs "%n" := by
  simp only [flushBlock, flushInstrs, stage2NoEventZeroStoreInstrs]

/-- `if.then12`: the zero rule's entry at `%idxprom.lcssa1108`. -/
def stage2NoEventIfThen12Block : Block :=
  { name := "if.then12",
    instrs :=
      [ Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%tokens_out"),
        Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%values_out"),
        Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%sum_out"),
        Instr.store (Ty.int 64) (Operand.reg "%idxprom.lcssa1108") (Operand.reg "%err") ],
    term := Term.br "cleanup580" }

theorem stage2NoEventIfThen12Block_find :
    stage2NoEventBody.findBlock "if.then12" = some stage2NoEventIfThen12Block := by decide

theorem stage2NoEventIfThen12Block_instrs :
    stage2NoEventIfThen12Block.instrs = stage2NoEventZeroStoreInstrs "%idxprom.lcssa1108" := by
  simp only [stage2NoEventIfThen12Block, stage2NoEventZeroStoreInstrs]

/-- `if.then68`: the zero rule's entry at `%n`. -/
def stage2NoEventIfThen68Block : Block :=
  { name := "if.then68",
    instrs :=
      [ Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%tokens_out"),
        Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%values_out"),
        Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%sum_out"),
        Instr.store (Ty.int 64) (Operand.reg "%n") (Operand.reg "%err") ],
    term := Term.br "cleanup580" }

theorem stage2NoEventIfThen68Block_find :
    stage2NoEventBody.findBlock "if.then68" = some stage2NoEventIfThen68Block := by decide

theorem stage2NoEventIfThen68Block_instrs :
    stage2NoEventIfThen68Block.instrs = stage2NoEventZeroStoreInstrs "%n" := by
  simp only [stage2NoEventIfThen68Block, stage2NoEventZeroStoreInstrs]

/-- `if.then94`: the zero rule's entry at `%idxprom76`. -/
def stage2NoEventIfThen94Block : Block :=
  { name := "if.then94",
    instrs :=
      [ Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%tokens_out"),
        Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%values_out"),
        Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%sum_out"),
        Instr.store (Ty.int 64) (Operand.reg "%idxprom76") (Operand.reg "%err") ],
    term := Term.br "cleanup580" }

theorem stage2NoEventIfThen94Block_find :
    stage2NoEventBody.findBlock "if.then94" = some stage2NoEventIfThen94Block := by decide

theorem stage2NoEventIfThen94Block_instrs :
    stage2NoEventIfThen94Block.instrs = stage2NoEventZeroStoreInstrs "%idxprom76" := by
  simp only [stage2NoEventIfThen94Block, stage2NoEventZeroStoreInstrs]

/-- `if.then105`: the zero rule's entry at `%n`. -/
def stage2NoEventIfThen105Block : Block :=
  { name := "if.then105",
    instrs :=
      [ Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%tokens_out"),
        Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%values_out"),
        Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%sum_out"),
        Instr.store (Ty.int 64) (Operand.reg "%n") (Operand.reg "%err") ],
    term := Term.br "cleanup580" }

theorem stage2NoEventIfThen105Block_find :
    stage2NoEventBody.findBlock "if.then105" = some stage2NoEventIfThen105Block := by decide

theorem stage2NoEventIfThen105Block_instrs :
    stage2NoEventIfThen105Block.instrs = stage2NoEventZeroStoreInstrs "%n" := by
  simp only [stage2NoEventIfThen105Block, stage2NoEventZeroStoreInstrs]

/-- `if.then118`: the zero rule's entry at `%idxprom113`. -/
def stage2NoEventIfThen118Block : Block :=
  { name := "if.then118",
    instrs :=
      [ Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%tokens_out"),
        Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%values_out"),
        Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%sum_out"),
        Instr.store (Ty.int 64) (Operand.reg "%idxprom113") (Operand.reg "%err") ],
    term := Term.br "cleanup580" }

theorem stage2NoEventIfThen118Block_find :
    stage2NoEventBody.findBlock "if.then118" = some stage2NoEventIfThen118Block := by decide

theorem stage2NoEventIfThen118Block_instrs :
    stage2NoEventIfThen118Block.instrs = stage2NoEventZeroStoreInstrs "%idxprom113" := by
  simp only [stage2NoEventIfThen118Block, stage2NoEventZeroStoreInstrs]

/-- `if.then297`: the zero rule's entry at `%n`. -/
def stage2NoEventIfThen297Block : Block :=
  { name := "if.then297",
    instrs :=
      [ Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%tokens_out"),
        Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%values_out"),
        Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%sum_out"),
        Instr.store (Ty.int 64) (Operand.reg "%n") (Operand.reg "%err") ],
    term := Term.br "cleanup580" }

theorem stage2NoEventIfThen297Block_find :
    stage2NoEventBody.findBlock "if.then297" = some stage2NoEventIfThen297Block := by decide

theorem stage2NoEventIfThen297Block_instrs :
    stage2NoEventIfThen297Block.instrs = stage2NoEventZeroStoreInstrs "%n" := by
  simp only [stage2NoEventIfThen297Block, stage2NoEventZeroStoreInstrs]

/-- `if.then311`: the zero rule's entry at `%idxprom306`. -/
def stage2NoEventIfThen311Block : Block :=
  { name := "if.then311",
    instrs :=
      [ Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%tokens_out"),
        Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%values_out"),
        Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%sum_out"),
        Instr.store (Ty.int 64) (Operand.reg "%idxprom306") (Operand.reg "%err") ],
    term := Term.br "cleanup580" }

theorem stage2NoEventIfThen311Block_find :
    stage2NoEventBody.findBlock "if.then311" = some stage2NoEventIfThen311Block := by decide

theorem stage2NoEventIfThen311Block_instrs :
    stage2NoEventIfThen311Block.instrs = stage2NoEventZeroStoreInstrs "%idxprom306" := by
  simp only [stage2NoEventIfThen311Block, stage2NoEventZeroStoreInstrs]

/-- `if.then321`: the zero rule's entry at `%n`. -/
def stage2NoEventIfThen321Block : Block :=
  { name := "if.then321",
    instrs :=
      [ Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%tokens_out"),
        Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%values_out"),
        Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%sum_out"),
        Instr.store (Ty.int 64) (Operand.reg "%n") (Operand.reg "%err") ],
    term := Term.br "cleanup580" }

theorem stage2NoEventIfThen321Block_find :
    stage2NoEventBody.findBlock "if.then321" = some stage2NoEventIfThen321Block := by decide

theorem stage2NoEventIfThen321Block_instrs :
    stage2NoEventIfThen321Block.instrs = stage2NoEventZeroStoreInstrs "%n" := by
  simp only [stage2NoEventIfThen321Block, stage2NoEventZeroStoreInstrs]

/-- `if.then372`: the zero rule's entry at `%n`. -/
def stage2NoEventIfThen372Block : Block :=
  { name := "if.then372",
    instrs :=
      [ Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%tokens_out"),
        Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%values_out"),
        Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%sum_out"),
        Instr.store (Ty.int 64) (Operand.reg "%n") (Operand.reg "%err") ],
    term := Term.br "cleanup580" }

theorem stage2NoEventIfThen372Block_find :
    stage2NoEventBody.findBlock "if.then372" = some stage2NoEventIfThen372Block := by decide

theorem stage2NoEventIfThen372Block_instrs :
    stage2NoEventIfThen372Block.instrs = stage2NoEventZeroStoreInstrs "%n" := by
  simp only [stage2NoEventIfThen372Block, stage2NoEventZeroStoreInstrs]

/-- `if.then402`: the zero rule's entry at `%idxprom385`. -/
def stage2NoEventIfThen402Block : Block :=
  { name := "if.then402",
    instrs :=
      [ Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%tokens_out"),
        Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%values_out"),
        Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%sum_out"),
        Instr.store (Ty.int 64) (Operand.reg "%idxprom385") (Operand.reg "%err") ],
    term := Term.br "cleanup580" }

theorem stage2NoEventIfThen402Block_find :
    stage2NoEventBody.findBlock "if.then402" = some stage2NoEventIfThen402Block := by decide

theorem stage2NoEventIfThen402Block_instrs :
    stage2NoEventIfThen402Block.instrs = stage2NoEventZeroStoreInstrs "%idxprom385" := by
  simp only [stage2NoEventIfThen402Block, stage2NoEventZeroStoreInstrs]

/-- `if.then428`: the zero rule's entry at `%idxprom385`. -/
def stage2NoEventIfThen428Block : Block :=
  { name := "if.then428",
    instrs :=
      [ Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%tokens_out"),
        Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%values_out"),
        Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%sum_out"),
        Instr.store (Ty.int 64) (Operand.reg "%idxprom385") (Operand.reg "%err") ],
    term := Term.br "cleanup580" }

theorem stage2NoEventIfThen428Block_find :
    stage2NoEventBody.findBlock "if.then428" = some stage2NoEventIfThen428Block := by decide

theorem stage2NoEventIfThen428Block_instrs :
    stage2NoEventIfThen428Block.instrs = stage2NoEventZeroStoreInstrs "%idxprom385" := by
  simp only [stage2NoEventIfThen428Block, stage2NoEventZeroStoreInstrs]

/-- `if.then562`: the zero rule's entry at `%q.01062`. -/
def stage2NoEventIfThen562Block : Block :=
  { name := "if.then562",
    instrs :=
      [ Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%tokens_out"),
        Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%values_out"),
        Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%sum_out"),
        Instr.store (Ty.int 64) (Operand.reg "%q.01062") (Operand.reg "%err") ],
    term := Term.br "cleanup580" }

theorem stage2NoEventIfThen562Block_find :
    stage2NoEventBody.findBlock "if.then562" = some stage2NoEventIfThen562Block := by decide

theorem stage2NoEventIfThen562Block_instrs :
    stage2NoEventIfThen562Block.instrs = stage2NoEventZeroStoreInstrs "%q.01062" := by
  simp only [stage2NoEventIfThen562Block, stage2NoEventZeroStoreInstrs]

/-! ### The `errStore` family

`cleanup.thread` and `cleanup287.thread` store their offset `phi`'s word at `%err`
and pass the `lifetime.end` marker the alloca the offset came from.  The three
output words are the *predecessors*' zeros, so the route carries them; the block
writes only the refusal word. -/

/-- The `errStore` family's body: the offset `phi`, its store at `%err`, and the
`lifetime.end` marker on the alloca. -/
def stage2NoEventErrStoreInstrs (d outn : String)
    (inc : List (String × Operand)) : List Instr :=
  [ Instr.phi d (Ty.int 64) inc,
    Instr.store (Ty.int 64) (Operand.reg d) (Operand.reg "%err"),
    Instr.callVoid "llvm.lifetime.end.p0"
      [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))),
        (Ty.ptr, (Operand.reg outn))] ]

/-- `cleanup.thread`'s offset `phi` incoming list. -/
def stage2NoEventCleanupThreadIncoming : List (String × Operand) :=
  [("if.then129", (Operand.reg "%conv130")), ("if.then143", (Operand.reg "%conv152")),
   ("do.body164", (Operand.reg "%18"))]

/-- `cleanup287.thread`'s offset `phi` incoming list. -/
def stage2NoEventCleanup287Incoming : List (String × Operand) :=
  [("if.then209", (Operand.reg "%idxprom.lcssa1109")),
   ("if.then223", (Operand.reg "%idxprom.lcssa1109")),
   ("do.body246", (Operand.reg "%33"))]

/-- `cleanup.thread`, pinned. -/
def stage2NoEventCleanupThreadBlock : Block :=
  { name := "cleanup.thread",
    instrs := stage2NoEventErrStoreInstrs "%conv130.sink" "%outn"
      stage2NoEventCleanupThreadIncoming,
    term := Term.br "cleanup580" }

/-- `cleanup287.thread`, pinned. -/
def stage2NoEventCleanup287Block : Block :=
  { name := "cleanup287.thread",
    instrs := stage2NoEventErrStoreInstrs "%idxprom.lcssa1109.lcssa.sink" "%outn205"
      stage2NoEventCleanup287Incoming,
    term := Term.br "cleanup580" }

theorem stage2NoEventCleanupThreadBlock_find :
    stage2NoEventBody.findBlock "cleanup.thread" =
      some stage2NoEventCleanupThreadBlock := by decide

theorem stage2NoEventCleanup287Block_find :
    stage2NoEventBody.findBlock "cleanup287.thread" =
      some stage2NoEventCleanup287Block := by decide

/-- **An `errStore` entry's body**, from the selected offset word and the two
pointers. -/
theorem stage2NoEventErrStore_denote {gap : Calls} (env : Env) (s : State)
    (d outn : String) (inc : List (String × Operand)) {p : String} {op : Operand}
    {w : BitVec 64} {err a : Nat}
    (hpre : s.pre = some p) (hinc : phiIncoming p inc = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 w))
    (hdErr : d ≠ "%err") (hdOutn : d ≠ outn)
    (herr : lookupName env "%err" = some (.ptr err))
    (houtn : lookupName env outn = some (.ptr a)) :
    denoteCode (stage2NoEventCalls gap) (stage2NoEventErrStoreInstrs d outn inc)
        (stateAt env s) =
      some (stateAt ((d, .int 64 w) :: env)
        (stage2NoEventStepState s (writeBytes s.mem err (wordBytes 8 w.toNat))
          s.next)) := by
  unfold stage2NoEventErrStoreInstrs
  rw [denoteCode_phi (calls := stage2NoEventCalls gap) (env := env) (s := s)
    d (Ty.int 64) inc (p := p) (op := op) (v := .int 64 w) hpre hinc hop _
    (by rfl)]
  rw [denoteCode_store64 (calls := stage2NoEventCalls gap)
    (env := (d, .int 64 w) :: env) (s := s) (v := d) (p := "%err") (x := w)
    (by simp only [lookupName_cons_self])
    (by rw [lookupName_cons_ne _ _ hdErr]; exact herr)]
  rw [stage2NoEventWalk_denote_lifetimeEnd (gap := gap)
    (env := (d, .int 64 w) :: env) (s := _) outn (sz := 8) (a := a)
    (by rw [lookupName_cons_ne _ _ hdOutn]; exact houtn)]
  simp only [denoteCode_nil, stateAt, stage2NoEventStepState, wordBytes]

/-- **An `errStore` entry's target**: the offset word at `%err`, the `phi` cell in
the environment, and `cleanup580` next. -/
def stage2NoEventErrStoreTarget (env : Env) (s : State) (d : String) (w : BitVec 64)
    (err : Nat) (blk : String) : State :=
  stateAt ((d, .int 64 w) :: env)
    (stage2NoEventJumpState s (writeBytes s.mem err (wordBytes 8 w.toNat)) s.next
      "cleanup580" blk)

/-- **An `errStore` entry's control step.** -/
theorem stage2NoEventErrStore_step {gap : Calls} (env : Env) (s : State)
    (blk d outn : String) (inc : List (String × Operand)) {b : Block} {p : String}
    {op : Operand} {w : BitVec 64} {err a : Nat}
    (hpc : s.pc = blk) (hfind : stage2NoEventBody.findBlock blk = some b)
    (hbody : b.instrs = stage2NoEventErrStoreInstrs d outn inc)
    (hterm : b.term = Term.br "cleanup580")
    (hpre : s.pre = some p) (hinc : phiIncoming p inc = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 w))
    (hdErr : d ≠ "%err") (hdOutn : d ≠ outn)
    (herr : lookupName env "%err" = some (.ptr err))
    (houtn : lookupName env outn = some (.ptr a)) :
    step (stage2NoEventCalls gap) stage2NoEventBody (stateAt env s) =
      .jump (stage2NoEventErrStoreTarget env s d w err blk) := by
  have hcode : denoteCode (stage2NoEventCalls gap) b.instrs (stateAt env s) =
      some (stateAt ((d, .int 64 w) :: env)
        (stage2NoEventStepState s (writeBytes s.mem err (wordBytes 8 w.toNat))
          s.next)) := by
    rw [hbody]
    exact stage2NoEventErrStore_denote env s d outn inc hpre hinc hop hdErr hdOutn
      herr houtn
  refine stage2NoEventWalk_step_at_block (s := stateAt env s)
    (s' := stateAt ((d, .int 64 w) :: env)
      (stage2NoEventStepState s (writeBytes s.mem err (wordBytes 8 w.toNat)) s.next))
    (b := b) ?_ hcode ?_
  · show stage2NoEventBody.findBlock s.pc = some b
    rw [hpc]; exact hfind
  · rw [hterm]
    simp only [execTerm, stage2NoEventErrStoreTarget, stage2NoEventJumpState,
      stage2NoEventStepState, stateAt, hpc]

/-- **The `errStore` target binds the offset cell**, and reads it back. -/
theorem stage2NoEventErrStoreTarget_operand (env : Env) (s : State) (d : String)
    (w : BitVec 64) (err : Nat) (blk : String) :
    evalOperand (stage2NoEventErrStoreTarget env s d w err blk) (Operand.reg d) =
      some (.int 64 w) := by
  simp only [stage2NoEventErrStoreTarget, stage2NoEventJumpState, stateAt, evalOperand,
    lookupName_cons_self]

theorem stage2NoEventErrStoreTarget_env (env : Env) (s : State) (d : String)
    (w : BitVec 64) (err : Nat) (blk : String) :
    (stage2NoEventErrStoreTarget env s d w err blk).env = (d, .int 64 w) :: env := by
  simp only [stage2NoEventErrStoreTarget, stage2NoEventJumpState, stateAt]

/-- **An `errStore` entry's refusal exit.**  The evidence is the `phi` cell (the
operand the step read and the shape's `src` register), the `lifetime.end` operand
and `%err`; the three zero words and the refusal word are the route's memory. -/
theorem stage2NoEventErrStore_exit {gap : Calls} {mem : Mem} {F k : Nat}
    {K : Stage2NoEventWalkCarry} {s sE sT sR : State} {j : Nat} {m : Mem}
    {src : String} {w : Nat} {p : Nat}
    (hj : ∀ n, runFuel (stage2NoEventCalls gap) (j + n) stage2NoEventBody s =
      runFuel (stage2NoEventCalls gap) n stage2NoEventBody sE)
    (hstep : step (stage2NoEventCalls gap) stage2NoEventBody sE = .jump sT)
    (hclean : step (stage2NoEventCalls gap) stage2NoEventBody sT =
      .ret (some (.int 64 0)) sR)
    (hmR : sR.mem = m)
    (hop : evalOperand sT (Operand.reg src) = some (.int 64 (BitVec.ofNat 64 w)))
    (hsrc : src = "%conv130.sink" ∨ src = "%idxprom.lcssa1109.lcssa.sink")
    (hlook : lookupName sT.env src = some (.int 64 (BitVec.ofNat 64 w)))
    (hout : lookupName sT.env "%outn" = some (.ptr p) ∨
      lookupName sT.env "%outn205" = some (.ptr p))
    (herr : lookupName sT.env "%err" = some (.ptr K.err))
    (hwlt : w < 2 ^ 64)
    (hcost : j + 1 ≤ stage2NoEventWalkPotential K k + F)
    (hreport : Stage2NoEventRun K.a12 mem m)
    (htrace : Stage2NoEventWalkTrace K sE)
    (hTokZ : readBytes m K.tokensOut 8 = some (wordBytes 8 0))
    (hValZ : readBytes m K.valuesOut 8 = some (wordBytes 8 0))
    (hSumZ : readBytes m K.sumOut 8 = some (wordBytes 8 0))
    (hErrW : readBytes m K.err 8 = some (wordBytes 8 w))
    (hOffLe : w ≤ K.n)
    (hframe : UnchangedOutside mem m
      (stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err ++
        (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
          [(K.next0, K.nextEnd - K.next0)])))
    (h : Stage2NoEventWalkInv K mem s) :
    Stage2NoEventWalkExit (stage2NoEventCalls gap) mem F K k s :=
  stage2NoEventRefuse_exit hj hstep hclean hmR hcost hreport htrace
    (.errStore w (Operand.reg src) p src hop hwlt hsrc hlook hout herr)
    (stage2NoEventBoundary_refusal h hTokZ hValZ hSumZ hErrW hOffLe hframe)

/-- **A `cleanup.thread` exit**, from its pin: the offset `phi`'s cell, the
`lifetime.end` operand, and the route's four words. -/
theorem stage2NoEventCleanupThread_exit {gap : Calls} {mem : Mem} {F k : Nat}
    {K : Stage2NoEventWalkCarry} {s sE : State} {j : Nat}
    {w : BitVec 64} {p : String} {op : Operand} {outn : Nat}
    (hj : ∀ n, runFuel (stage2NoEventCalls gap) (j + n) stage2NoEventBody s =
      runFuel (stage2NoEventCalls gap) n stage2NoEventBody sE)
    (hpc : sE.pc = "cleanup.thread") (hp : sE.pre = some p)
    (hinc : phiIncoming p stage2NoEventCleanupThreadIncoming = some op)
    (hop : evalOperand (stateAt sE.env sE) op = some (.int 64 w))
    (houtn : lookupName sE.env "%outn" = some (.ptr outn))
    (hinc0 : phiIncoming "cleanup.thread" cleanup580Incoming = some (.imm (.int 64 0)))
    (hpar : Stage2NoEventWalkParams K sE)
    (hloc : Stage2NoEventWalkLocals K sE)
    (hcost : j + 1 ≤ stage2NoEventWalkPotential K k + F)
    (hreport : Stage2NoEventRun K.a12 mem (writeBytes sE.mem K.err (wordBytes 8 w.toNat)))
    (htrace : Stage2NoEventWalkTrace K sE)
    (hTokZ : readBytes (writeBytes sE.mem K.err (wordBytes 8 w.toNat)) K.tokensOut 8 =
      some (wordBytes 8 0))
    (hValZ : readBytes (writeBytes sE.mem K.err (wordBytes 8 w.toNat)) K.valuesOut 8 =
      some (wordBytes 8 0))
    (hSumZ : readBytes (writeBytes sE.mem K.err (wordBytes 8 w.toNat)) K.sumOut 8 =
      some (wordBytes 8 0))
    (hOffLe : w.toNat ≤ K.n)
    (hrouteFrame : UnchangedOutside s.mem sE.mem
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]))
    (h : Stage2NoEventWalkInv K mem s) :
    Stage2NoEventWalkExit (stage2NoEventCalls gap) mem F K k s := by
  have hstep : step (stage2NoEventCalls gap) stage2NoEventBody sE =
      .jump (stage2NoEventErrStoreTarget sE.env sE "%conv130.sink" w K.err
        "cleanup.thread") :=
    stage2NoEventErrStore_step (gap := gap) (b := stage2NoEventCleanupThreadBlock)
      sE.env sE "cleanup.thread" "%conv130.sink" "%outn"
      stage2NoEventCleanupThreadIncoming hpc stage2NoEventCleanupThreadBlock_find
      (by simp only [stage2NoEventCleanupThreadBlock, stage2NoEventErrStoreInstrs])
      rfl hp hinc hop (by decide) (by decide) hpar.err houtn
  have hclean : step (stage2NoEventCalls gap) stage2NoEventBody
      (stage2NoEventErrStoreTarget sE.env sE "%conv130.sink" w K.err "cleanup.thread") =
      .ret (some (.int 64 0))
        (stateAt (("%retval.14", .int 64 0) :: ("%conv130.sink", .int 64 w) :: sE.env)
          (stage2NoEventJumpState sE (writeBytes sE.mem K.err (wordBytes 8 w.toNat))
            sE.next "cleanup580" "cleanup.thread")) :=
    stage2NoEventCleanup_step (gap := gap) (("%conv130.sink", .int 64 w) :: sE.env)
      (stage2NoEventJumpState sE (writeBytes sE.mem K.err (wordBytes 8 w.toNat))
        sE.next "cleanup580" "cleanup.thread") "cleanup.thread" rfl rfl hinc0
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact hpar.c)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact hpar.e)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact hpar.stk)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact hloc.xj)
  have henvT : (stage2NoEventErrStoreTarget sE.env sE "%conv130.sink" w K.err
      "cleanup.thread").env = ("%conv130.sink", .int 64 w) :: sE.env := by
    simp only [stage2NoEventErrStoreTarget, stage2NoEventJumpState, stateAt]
  have hErrW : readBytes (writeBytes sE.mem K.err (wordBytes 8 w.toNat)) K.err 8 =
      some (wordBytes 8 w.toNat) := stage2NoEventRead_own
  have hframe : UnchangedOutside mem
      (writeBytes sE.mem K.err (wordBytes 8 w.toNat))
      (stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err ++
        (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
          [(K.next0, K.nextEnd - K.next0)])) :=
    stage2NoEventBoundaryFrame h hrouteFrame (UnchangedOutside.refl' _ _)
      (by
        have hmemErr : (K.err, 8) ∈
            stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err := by
          simp [stage2NoEventWrites]
        refine (UnchangedOutside.refl' sE.mem _).write_le (w := 8) ?_ ?_
        · exact ⟨(K.err, 8), List.mem_append_left _ hmemErr, le_rfl, le_rfl⟩
        · simp [wordBytes, natToBytes_length])
  have hopT : evalOperand (stage2NoEventErrStoreTarget sE.env sE "%conv130.sink" w K.err
      "cleanup.thread") (Operand.reg "%conv130.sink") =
      some (.int 64 (BitVec.ofNat 64 w.toNat)) := by
    rw [stage2NoEventErrStoreTarget_operand]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hlookT : lookupName (stage2NoEventErrStoreTarget sE.env sE "%conv130.sink" w K.err
      "cleanup.thread").env "%conv130.sink" =
      some (.int 64 (BitVec.ofNat 64 w.toNat)) := by
    rw [stage2NoEventErrStoreTarget_env, lookupName_cons_self]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have houtT : lookupName (stage2NoEventErrStoreTarget sE.env sE "%conv130.sink" w K.err
      "cleanup.thread").env "%outn" = some (.ptr outn) := by
    rw [stage2NoEventErrStoreTarget_env]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact houtn
  have herrT : lookupName (stage2NoEventErrStoreTarget sE.env sE "%conv130.sink" w K.err
      "cleanup.thread").env "%err" = some (.ptr K.err) := by
    rw [stage2NoEventErrStoreTarget_env]
    rw [lookupName_cons_ne _ _ (by decide)]
    exact hpar.err
  have hwlt : w.toNat < 2 ^ 64 := w.isLt
  exact stage2NoEventErrStore_exit (p := outn) (src := "%conv130.sink")
    (w := w.toNat) hj hstep hclean
    (by simp only [stateAt, stage2NoEventJumpState]) hopT (Or.inl rfl) hlookT
    (Or.inl houtT) herrT hwlt hcost hreport htrace hTokZ hValZ hSumZ hErrW hOffLe
    hframe h

/-- **A `cleanup287.thread` exit**, from its pin: the string path's offset `phi`
and its own `%outn205` operand. -/
theorem stage2NoEventCleanup287_exit {gap : Calls} {mem : Mem} {F k : Nat}
    {K : Stage2NoEventWalkCarry} {s sE : State} {j : Nat}
    {w : BitVec 64} {p : String} {op : Operand} {outn : Nat}
    (hj : ∀ n, runFuel (stage2NoEventCalls gap) (j + n) stage2NoEventBody s =
      runFuel (stage2NoEventCalls gap) n stage2NoEventBody sE)
    (hpc : sE.pc = "cleanup287.thread") (hp : sE.pre = some p)
    (hinc : phiIncoming p stage2NoEventCleanup287Incoming = some op)
    (hop : evalOperand (stateAt sE.env sE) op = some (.int 64 w))
    (houtn : lookupName sE.env "%outn205" = some (.ptr outn))
    (hinc0 : phiIncoming "cleanup287.thread" cleanup580Incoming = some (.imm (.int 64 0)))
    (hpar : Stage2NoEventWalkParams K sE)
    (hloc : Stage2NoEventWalkLocals K sE)
    (hcost : j + 1 ≤ stage2NoEventWalkPotential K k + F)
    (hreport : Stage2NoEventRun K.a12 mem (writeBytes sE.mem K.err (wordBytes 8 w.toNat)))
    (htrace : Stage2NoEventWalkTrace K sE)
    (hTokZ : readBytes (writeBytes sE.mem K.err (wordBytes 8 w.toNat)) K.tokensOut 8 =
      some (wordBytes 8 0))
    (hValZ : readBytes (writeBytes sE.mem K.err (wordBytes 8 w.toNat)) K.valuesOut 8 =
      some (wordBytes 8 0))
    (hSumZ : readBytes (writeBytes sE.mem K.err (wordBytes 8 w.toNat)) K.sumOut 8 =
      some (wordBytes 8 0))
    (hOffLe : w.toNat ≤ K.n)
    (hrouteFrame : UnchangedOutside s.mem sE.mem
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]))
    (h : Stage2NoEventWalkInv K mem s) :
    Stage2NoEventWalkExit (stage2NoEventCalls gap) mem F K k s := by
  have hstep : step (stage2NoEventCalls gap) stage2NoEventBody sE =
      .jump (stage2NoEventErrStoreTarget sE.env sE "%idxprom.lcssa1109.lcssa.sink" w
        K.err "cleanup287.thread") :=
    stage2NoEventErrStore_step (gap := gap) (b := stage2NoEventCleanup287Block)
      sE.env sE "cleanup287.thread" "%idxprom.lcssa1109.lcssa.sink" "%outn205"
      stage2NoEventCleanup287Incoming hpc stage2NoEventCleanup287Block_find
      (by simp only [stage2NoEventCleanup287Block, stage2NoEventErrStoreInstrs])
      rfl hp hinc hop (by decide) (by decide) hpar.err houtn
  have hclean : step (stage2NoEventCalls gap) stage2NoEventBody
      (stage2NoEventErrStoreTarget sE.env sE "%idxprom.lcssa1109.lcssa.sink" w
        K.err "cleanup287.thread") =
      .ret (some (.int 64 0))
        (stateAt (("%retval.14", .int 64 0) ::
            ("%idxprom.lcssa1109.lcssa.sink", .int 64 w) :: sE.env)
          (stage2NoEventJumpState sE (writeBytes sE.mem K.err (wordBytes 8 w.toNat))
            sE.next "cleanup580" "cleanup287.thread")) :=
    stage2NoEventCleanup_step (gap := gap)
      (("%idxprom.lcssa1109.lcssa.sink", .int 64 w) :: sE.env)
      (stage2NoEventJumpState sE (writeBytes sE.mem K.err (wordBytes 8 w.toNat))
        sE.next "cleanup580" "cleanup287.thread") "cleanup287.thread" rfl rfl hinc0
      (c := K.c) (e := K.e) (stk := K.stk) (xj := K.xj)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact hpar.c)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact hpar.e)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact hpar.stk)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact hloc.xj)
  have henvT : (stage2NoEventErrStoreTarget sE.env sE
      "%idxprom.lcssa1109.lcssa.sink" w K.err "cleanup287.thread").env =
      ("%idxprom.lcssa1109.lcssa.sink", .int 64 w) :: sE.env :=
    stage2NoEventErrStoreTarget_env _ _ _ _ _ _
  have hopT : evalOperand (stage2NoEventErrStoreTarget sE.env sE
      "%idxprom.lcssa1109.lcssa.sink" w K.err "cleanup287.thread")
      (Operand.reg "%idxprom.lcssa1109.lcssa.sink") =
      some (.int 64 (BitVec.ofNat 64 w.toNat)) := by
    rw [stage2NoEventErrStoreTarget_operand]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hlookT : lookupName (stage2NoEventErrStoreTarget sE.env sE
      "%idxprom.lcssa1109.lcssa.sink" w K.err "cleanup287.thread").env
      "%idxprom.lcssa1109.lcssa.sink" =
      some (.int 64 (BitVec.ofNat 64 w.toNat)) := by
    rw [henvT, lookupName_cons_self]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have houtT : lookupName (stage2NoEventErrStoreTarget sE.env sE
      "%idxprom.lcssa1109.lcssa.sink" w K.err "cleanup287.thread").env "%outn205" =
      some (.ptr outn) := by
    rw [henvT, lookupName_cons_ne _ _ (by decide)]
    exact houtn
  have herrT : lookupName (stage2NoEventErrStoreTarget sE.env sE
      "%idxprom.lcssa1109.lcssa.sink" w K.err "cleanup287.thread").env "%err" =
      some (.ptr K.err) := by
    rw [henvT, lookupName_cons_ne _ _ (by decide)]
    exact hpar.err
  have hErrW : readBytes (writeBytes sE.mem K.err (wordBytes 8 w.toNat)) K.err 8 =
      some (wordBytes 8 w.toNat) := stage2NoEventRead_own
  have hframe : UnchangedOutside mem (writeBytes sE.mem K.err (wordBytes 8 w.toNat))
      (stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err ++
        (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
          [(K.next0, K.nextEnd - K.next0)])) :=
    stage2NoEventBoundaryFrame h hrouteFrame (UnchangedOutside.refl' _ _)
      (by
        have hmemErr : (K.err, 8) ∈
            stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err := by
          simp [stage2NoEventWrites]
        exact (UnchangedOutside.refl' sE.mem _).write_le (w := 8)
          ⟨(K.err, 8), List.mem_append_left _ hmemErr, le_rfl, le_rfl⟩
          (by simp [wordBytes, natToBytes_length]))
  exact stage2NoEventErrStore_exit (p := outn)
    (src := "%idxprom.lcssa1109.lcssa.sink") (w := w.toNat) hj hstep hclean
    (by simp only [stateAt, stage2NoEventJumpState]) hopT
    (Or.inr rfl) hlookT (Or.inr houtT) herrT w.isLt hcost hreport htrace hTokZ hValZ
    hSumZ hErrW hOffLe hframe h

/-! ### The gap family's literal shape

`if.then527`'s run is the terminal module's (`stage2NoEventRefusal_step`); what the
exit adds is the evidence at its target — the `%ei520.0.ph` cell, the offset
`%off`, the `%74` read-back — and the boundary from the walk's frame, the route's
and the call's. -/

/-- **The refusal word's slot against the error word**, from the one separation
surface: the record's `(e, 24)` entry is a staged object, the error word an ABI
region. -/
theorem stage2NoEventWalkSep_off_err {b n ep nep xp nxp scratch scratchcap
    tokensOut valuesOut sumOut err stk e c d : Nat}
    (h : Stage2NoEventWalkSep b n ep nep xp nxp scratch scratchcap tokensOut
      valuesOut sumOut err stk e c d) :
    (e + 8) + 8 ≤ err ∨ err + 8 ≤ e + 8 := by
  have hrec : (e, stage2NoEventErrorExtent) ∈ stage2NoEventStagedRegions stk e c d := by
    simp [stage2NoEventStagedRegions]
  have := disjointRegions_against (rs := stage2NoEventRegions b n ep nep xp nxp
      scratch scratchcap tokensOut valuesOut sumOut err)
    (ss := stage2NoEventStagedRegions stk e c d) (a := err) (n := 8) h
    (by simp [stage2NoEventRegions, stage2NoEventWrites])
    (e, stage2NoEventErrorExtent) hrec
  simp only [stage2NoEventErrorExtent] at this
  omega

/-- **The refusal word's slot is untouched by the four output stores.** -/
theorem stage2NoEventErrMem_off_read {m : Mem} {t v su err : Nat} {x : BitVec 64}
    {off : Nat}
    (h1 : off + 8 ≤ t ∨ t + 8 ≤ off) (h2 : off + 8 ≤ v ∨ v + 8 ≤ off)
    (h3 : off + 8 ≤ su ∨ su + 8 ≤ off) (h4 : off + 8 ≤ err ∨ err + 8 ≤ off) :
    readBytes (stage2NoEventErrMem m t v su err x) off 8 = readBytes m off 8 := by
  have hx : natToBytes x.toNat 8 = wordBytes 8 x.toNat := rfl
  simp only [stage2NoEventErrMem, stage2NoEventZeroMem, hx]
  rw [readBytes_wordBytes_frame (addr := err) (v := x.toNat) (p := off) (n := 8) h4]
  rw [readBytes_wordBytes_frame (addr := su) (v := 0) (p := off) (n := 8) h3]
  rw [readBytes_wordBytes_frame (addr := v) (v := 0) (p := off) (n := 8) h2]
  rw [readBytes_wordBytes_frame (addr := t) (v := 0) (p := off) (n := 8) h1]


/-- **The gap family's literal shape**, from the route's word and its provenance.
The evidence names the `%ei520.0.ph` cell, the offset slot, the `%74` read at the
call's memory and the phi's incoming value; the boundary reads the stores back. -/
theorem stage2NoEventGapLiteral_exit {gap : Calls} {mem : Mem} {F k : Nat}
    {K : Stage2NoEventWalkCarry} {s sE sT sR : State} {j : Nat} {m : Mem}
    {rc : CallOutcome} {ei520 idxNat eoffN : Nat}
    {src : Stage2NoEventWalkEi520Incoming}
    (hj : ∀ n, runFuel (stage2NoEventCalls gap) (j + n) stage2NoEventBody s =
      runFuel (stage2NoEventCalls gap) n stage2NoEventBody sE)
    (hstep : step (stage2NoEventCalls gap) stage2NoEventBody sE = .jump sT)
    (hclean : step (stage2NoEventCalls gap) stage2NoEventBody sT =
      .ret (some (.int 64 0)) sR)
    (hmR : sR.mem = m)
    (hm : m = stage2NoEventErrMem rc.mem K.tokensOut K.valuesOut K.sumOut K.err
      (BitVec.ofNat 64 eoffN))
    (hmS : sT.mem = m)
    (htok : lookupName sT.env "%tokens_out" = some (.ptr K.tokensOut))
    (hval : lookupName sT.env "%values_out" = some (.ptr K.valuesOut))
    (hsum : lookupName sT.env "%sum_out" = some (.ptr K.sumOut))
    (herr : lookupName sT.env "%err" = some (.ptr K.err))
    (hoff : lookupName sT.env "%off" = some (.ptr (K.e + 8)))
    (hidx : lookupName sT.env "%idxprom.lcssa" =
      some (.int 64 (BitVec.ofNat 64 idxNat)))
    (hei : lookupName sT.env "%ei520.0.ph" = some (.int 64 (BitVec.ofNat 64 ei520)))
    (hsrcValue : src.value = ei520)
    (hv : readBytes rc.mem (K.e + 8) 8 = some (wordBytes 8 eoffN))
    (heoffEq : eoffN = ei520 + idxNat)
    (hOffLe : eoffN ≤ K.n) (hLt : eoffN < 2 ^ 64)
    (hcost : j + 1 ≤ stage2NoEventWalkPotential K k + F)
    (hreport : Stage2NoEventRun K.a12 mem m)
    (htrace : Stage2NoEventWalkTrace K sE)
    (hrouteFrame : UnchangedOutside s.mem sE.mem
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]))
    (hcallFrame : UnchangedOutside sE.mem rc.mem
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]))
    (h : Stage2NoEventWalkInv K mem s) :
    Stage2NoEventWalkExit (stage2NoEventCalls gap) mem F K k s := by
  obtain ⟨hTok, hVal, hSum, hErr⟩ :=
    stage2NoEventErrMem_reads (m := rc.mem) (x := BitVec.ofNat 64 eoffN)
      (stage2NoEventRegions_writes h.separate)
  have hsym : UnchangedOutside
      (stage2NoEventErrMem rc.mem K.tokensOut K.valuesOut K.sumOut K.err
        (BitVec.ofNat 64 eoffN)) rc.mem
      (stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err) :=
    fun a ha => (stage2NoEventErrMem_writes_frame (m := rc.mem)
      (t := K.tokensOut) (v := K.valuesOut) (su := K.sumOut) (e := K.err)
      (x := BitVec.ofNat 64 eoffN) a ha).symm
  have hTframe : UnchangedOutside sT.mem rc.mem
      (stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err ++
        (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
          [(K.next0, K.nextEnd - K.next0)])) := by
    rw [hmS, hm]
    exact hsym.of_covered (fun r hr =>
      ⟨r, List.mem_append_left _ hr, le_rfl, le_rfl⟩)
  refine stage2NoEventRefuse_exit hj hstep hclean hmR hcost hreport htrace
    (.gapLiteral rc eoffN idxNat ei520 src htok hval hsum herr hoff hidx hei
      hsrcValue hv hTframe heoffEq hOffLe hLt) ?_
  refine stage2NoEventBoundary_refusal (eoff := eoffN) h (by rw [hm]; exact hTok)
    (by rw [hm]; exact hVal) (by rw [hm]; exact hSum)
    (by
      rw [hm]
      rw [show (BitVec.ofNat 64 eoffN).toNat = eoffN from by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hLt]] at hErr
      exact hErr)
    hOffLe ?_
  have hstores : UnchangedOutside rc.mem m
      (stage2NoEventWrites K.tokensOut K.valuesOut K.sumOut K.err) := by
    rw [hm]
    exact stage2NoEventErrMem_writes_frame (m := rc.mem) (t := K.tokensOut)
      (v := K.valuesOut) (su := K.sumOut) (e := K.err)
      (x := BitVec.ofNat 64 eoffN)
  exact stage2NoEventBoundaryFrame h hrouteFrame hcallFrame hstores

/-- `if.then38`'s offset `phi` incoming list. -/
def stage2NoEventIfThen38Incoming : List (String × Operand) :=
  [("if.then38.loopexit", (Operand.reg "%idxprom.le")),
   ("if.then35.peel", (Operand.reg "%idxprom.peel"))]

/-- `if.then38`: the offset `phi` and the zero rule's stores. -/
def stage2NoEventIfThen38Block : Block :=
  { name := "if.then38",
    instrs :=
      Instr.phi "%idxprom.lcssa1110" (Ty.int 64) stage2NoEventIfThen38Incoming ::
        stage2NoEventZeroStoreInstrs "%idxprom.lcssa1110",
    term := Term.br "cleanup580" }

theorem stage2NoEventIfThen38Block_find :
    stage2NoEventBody.findBlock "if.then38" = some stage2NoEventIfThen38Block := by
  decide

/-! ### The two entries that bind their own offset first

`if.then38` conses an offset `phi` before the zero rule's stores, and `if.then360`
reads the entry's index (`gep` at `%ep`, a 32-bit load, the zero extension) before
them.  Their words are bound by their own blocks, so the four-store producer
cannot read them; each gets its prefix's run here, and then the same target,
evidence and boundary as the family. -/

/-- **A `gep` at a four-byte element type**, indexed by a register, as a chain
step: `if.then360`'s index read is `getelementptr i32, ptr %ep, i64 %k.6`. -/
theorem stage2NoEventWalk_step_gep32_reg (calls : Calls) (env : Env) (s : State)
    (d base off : String) {a : Nat} {w : Nat} {idx : BitVec w}
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int w idx))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63) :
    evalInstr calls (stateAt env s) (.gep d (.int 32) (.reg base) (.reg off)) =
      some (stateAt ((d, .ptr (a + (idx.signExtend 64).toNat * 4)) :: env) s) := by
  have hb' : evalOperand (stateAt env s) (.reg base) = some (.ptr a) :=
    evalOperand_reg_of env s base (.ptr a) hb
  have ho' : evalOperand (stateAt env s) (.reg off) = some (.int w idx) :=
    evalOperand_reg_of env s off (.int w idx) ho
  simp only [evalInstr, hb', ho', hpos, ite_true, Ty.sizeBytes, State.bind]
  rfl

/-- **A `load i32`**, as a chain step. -/
theorem stage2NoEventWalk_step_load32 (calls : Calls) (env : Env) (s : State)
    (d p : String) {a : Nat} {x : BitVec 32}
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 4 = some (natToBytes x.toNat 4)) :
    evalInstr calls (stateAt env s) (.load d (.int 32) (.reg p)) =
      some (stateAt ((d, .int 32 x) :: env) s) := by
  have hp' : evalOperand (stateAt env s) (.reg p) = some (.ptr a) :=
    evalOperand_reg_of env s p (.ptr a) hp
  have hload : loadValue (stateAt env s).mem (.int 32) a = some (.int 32 x) := by
    have h32 : ¬ ((32 : Nat) = 0) := by decide
    simp only [loadValue, h32, ite_false, stateAt_mem,
      show (32 + 7) / 8 = 4 from by decide]
    rw [hv]
    simp only [natToBytes_toNat, show 256 ^ 4 = 2 ^ 32 from by decide,
      Nat.mod_eq_of_lt x.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simp only [evalInstr, hp', hload, State.bind]
  rfl

/-- **A `phi`-prefixed zero-store entry's target**: the offset cell, the three
zeros and the word at `%err`. -/
def stage2NoEventPhiZeroTarget (env : Env) (s : State) (d : String) (w : BitVec 64)
    (t v su e : Nat) (blk : String) : State :=
  stateAt ((d, .int 64 w) :: env)
    (stage2NoEventJumpState s (stage2NoEventErrMem s.mem t v su e w) s.next
      "cleanup580" blk)

theorem stage2NoEventPhiZeroTarget_env (env : Env) (s : State) (d : String) (w : BitVec 64)
    (t v su e : Nat) (blk : String) :
    (stage2NoEventPhiZeroTarget env s d w t v su e blk).env =
      (d, .int 64 w) :: env := by
  simp only [stage2NoEventPhiZeroTarget, stage2NoEventJumpState, stateAt]

theorem stage2NoEventPhiZeroTarget_mem (env : Env) (s : State) (d : String) (w : BitVec 64)
    (t v su e : Nat) (blk : String) :
    (stage2NoEventPhiZeroTarget env s d w t v su e blk).mem =
      stage2NoEventErrMem s.mem t v su e w := by
  simp only [stage2NoEventPhiZeroTarget, stage2NoEventJumpState, stateAt]

/-- **A `phi`-prefixed zero-store entry's body**, from the selected offset word. -/
theorem stage2NoEventPhiZeroStore_denote {calls : Calls} (env : Env) (s : State)
    (d : String) (inc : List (String × Operand)) {p : String} {op : Operand}
    {t v su e : Nat} {x : BitVec 64}
    (hpre : s.pre = some p) (hinc : phiIncoming p inc = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 x))
    (hd1 : d ≠ "%tokens_out") (hd2 : d ≠ "%values_out") (hd3 : d ≠ "%sum_out")
    (hd4 : d ≠ "%err")
    (htok : lookupName env "%tokens_out" = some (.ptr t))
    (hval : lookupName env "%values_out" = some (.ptr v))
    (hsum : lookupName env "%sum_out" = some (.ptr su))
    (herr : lookupName env "%err" = some (.ptr e)) :
    denoteCode calls (Instr.phi d (Ty.int 64) inc :: stage2NoEventZeroStoreInstrs d)
        (stateAt env s) =
      some (stateAt ((d, .int 64 x) :: env)
        (stage2NoEventStepState s (stage2NoEventErrMem s.mem t v su e x) s.next)) := by
  rw [denoteCode_phi (calls := calls) (env := env) (s := s) d (Ty.int 64) inc
    (p := p) (op := op) (v := .int 64 x) hpre hinc hop _ (by rfl)]
  exact stage2NoEventZeroStore_denote ((d, .int 64 x) :: env) s d
    (by rw [lookupName_cons_ne _ _ hd1]; exact htok)
    (by rw [lookupName_cons_ne _ _ hd2]; exact hval)
    (by rw [lookupName_cons_ne _ _ hd3]; exact hsum)
    (by rw [lookupName_cons_ne _ _ hd4]; exact herr)
    (by simp only [lookupName_cons_self])

/-- **`if.then38`'s exit**: its `phi`'s word, the family's stores, and the
`cleanup580` seam. -/
theorem stage2NoEventIfThen38_exit {gap : Calls} {mem : Mem} {F k : Nat}
    {K : Stage2NoEventWalkCarry} {s sE : State} {j : Nat}
    {p : String} {op : Operand} {x : BitVec 64}
    (hj : ∀ n, runFuel (stage2NoEventCalls gap) (j + n) stage2NoEventBody s =
      runFuel (stage2NoEventCalls gap) n stage2NoEventBody sE)
    (hpc : sE.pc = "if.then38") (hp : sE.pre = some p)
    (hinc : phiIncoming p stage2NoEventIfThen38Incoming = some op)
    (hop : evalOperand (stateAt sE.env sE) op = some (.int 64 x))
    (hinc0 : phiIncoming "if.then38" cleanup580Incoming = some (.imm (.int 64 0)))
    (hpar : Stage2NoEventWalkParams K sE)
    (hloc : Stage2NoEventWalkLocals K sE)
    (hle : x.toNat ≤ K.n)
    (hcost : j + 1 ≤ stage2NoEventWalkPotential K k + F)
    (hreport : Stage2NoEventRun K.a12 mem
      (stage2NoEventErrMem sE.mem K.tokensOut K.valuesOut K.sumOut K.err x))
    (htrace : Stage2NoEventWalkTrace K sE)
    (hrouteFrame : UnchangedOutside s.mem sE.mem
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]))
    (h : Stage2NoEventWalkInv K mem s) :
    Stage2NoEventWalkExit (stage2NoEventCalls gap) mem F K k s := by
  have hcode : denoteCode (stage2NoEventCalls gap) stage2NoEventIfThen38Block.instrs
      (stateAt sE.env sE) =
      some (stateAt (("%idxprom.lcssa1110", .int 64 x) :: sE.env)
        (stage2NoEventStepState sE
          (stage2NoEventErrMem sE.mem K.tokensOut K.valuesOut K.sumOut K.err x)
          sE.next)) :=
    stage2NoEventPhiZeroStore_denote sE.env sE "%idxprom.lcssa1110"
      stage2NoEventIfThen38Incoming hp hinc hop (by decide) (by decide) (by decide)
      (by decide) hpar.tokensOut hpar.valuesOut hpar.sumOut hpar.err
  have hstep : step (stage2NoEventCalls gap) stage2NoEventBody sE =
      .jump (stage2NoEventPhiZeroTarget sE.env sE "%idxprom.lcssa1110" x
        K.tokensOut K.valuesOut K.sumOut K.err "if.then38") := by
    refine stage2NoEventWalk_step_at_block (s := stateAt sE.env sE)
      (s' := stateAt (("%idxprom.lcssa1110", .int 64 x) :: sE.env)
        (stage2NoEventStepState sE
          (stage2NoEventErrMem sE.mem K.tokensOut K.valuesOut K.sumOut K.err x)
          sE.next))
      (b := stage2NoEventIfThen38Block) ?_ ?_ ?_
    · show stage2NoEventBody.findBlock sE.pc = some stage2NoEventIfThen38Block
      rw [hpc]; exact stage2NoEventIfThen38Block_find
    · exact hcode
    · simp only [stage2NoEventIfThen38Block, execTerm, stage2NoEventPhiZeroTarget,
        stage2NoEventJumpState, stage2NoEventStepState, stateAt, hpc]
  have hclean : step (stage2NoEventCalls gap) stage2NoEventBody
      (stage2NoEventPhiZeroTarget sE.env sE "%idxprom.lcssa1110" x K.tokensOut
        K.valuesOut K.sumOut K.err "if.then38") =
      .ret (some (.int 64 0))
        (stateAt (("%retval.14", .int 64 0) ::
            ("%idxprom.lcssa1110", .int 64 x) :: sE.env)
          (stage2NoEventJumpState sE
            (stage2NoEventErrMem sE.mem K.tokensOut K.valuesOut K.sumOut K.err x)
            sE.next "cleanup580" "if.then38")) :=
    stage2NoEventCleanup_step (gap := gap)
      (("%idxprom.lcssa1110", .int 64 x) :: sE.env)
      (stage2NoEventJumpState sE
        (stage2NoEventErrMem sE.mem K.tokensOut K.valuesOut K.sumOut K.err x)
        sE.next "cleanup580" "if.then38") "if.then38" rfl rfl hinc0
      (c := K.c) (e := K.e) (stk := K.stk) (xj := K.xj)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact hpar.c)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact hpar.e)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact hpar.stk)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact hloc.xj)
  have henvT := stage2NoEventPhiZeroTarget_env sE.env sE "%idxprom.lcssa1110" x
    K.tokensOut K.valuesOut K.sumOut K.err "if.then38"
  refine stage2NoEventZero_exit (x := x)
    (m := stage2NoEventErrMem sE.mem K.tokensOut K.valuesOut K.sumOut K.err x)
    hj hstep hclean (by simp only [stateAt, stage2NoEventJumpState]) rfl
    ?_ ?_ ?_ ?_ ?_ hle hcost hreport htrace hrouteFrame h
  · rw [stage2NoEventPhiZeroTarget_mem]
  · rw [henvT]; exact lookupName_cons_ne _ _ (by decide) |>.trans hpar.tokensOut
  · rw [henvT]; exact lookupName_cons_ne _ _ (by decide) |>.trans hpar.valuesOut
  · rw [henvT]; exact lookupName_cons_ne _ _ (by decide) |>.trans hpar.sumOut
  · rw [henvT]; exact lookupName_cons_ne _ _ (by decide) |>.trans hpar.err

/-- `if.then360`: the index read and the zero rule's stores. -/
def stage2NoEventIfThen360Block : Block :=
  { name := "if.then360",
    instrs :=
      [ Instr.gep "%arrayidx361" (Ty.int 32) (Operand.reg "%ep") (Operand.reg "%k.6"),
        Instr.load "%51" (Ty.int 32) (Operand.reg "%arrayidx361"),
        Instr.zext "%conv362" 32 64 (Operand.reg "%51") ] ++
        stage2NoEventZeroStoreInstrs "%conv362",
    term := Term.br "cleanup580" }

theorem stage2NoEventIfThen360Block_find :
    stage2NoEventBody.findBlock "if.then360" = some stage2NoEventIfThen360Block := by
  decide

/-- **`if.then360`'s target**: the index read's three cells and the zero rule's
stores. -/
def stage2NoEventIfThen360Target (env : Env) (s : State) (base : Nat) {w : Nat}
    (idx6 : BitVec w) (x32 : BitVec 32) (x64 : BitVec 64) (t v su e : Nat) : State :=
  stateAt (("%conv362", .int 64 x64) :: ("%51", .int 32 x32) ::
      ("%arrayidx361", .ptr (base + (idx6.signExtend 64).toNat * 4)) :: env)
    (stage2NoEventJumpState s (stage2NoEventErrMem s.mem t v su e x64) s.next
      "cleanup580" "if.then360")

theorem stage2NoEventIfThen360Target_env (env : Env) (s : State) (base : Nat) {w : Nat}
    (idx6 : BitVec w) (x32 : BitVec 32) (x64 : BitVec 64) (t v su e : Nat) :
    (stage2NoEventIfThen360Target env s base idx6 x32 x64 t v su e).env =
      ("%conv362", .int 64 x64) :: ("%51", .int 32 x32) ::
        ("%arrayidx361", .ptr (base + (idx6.signExtend 64).toNat * 4)) :: env := by
  simp only [stage2NoEventIfThen360Target, stage2NoEventJumpState, stateAt]

theorem stage2NoEventIfThen360Target_mem (env : Env) (s : State) (base : Nat) {w : Nat}
    (idx6 : BitVec w) (x32 : BitVec 32) (x64 : BitVec 64) (t v su e : Nat) :
    (stage2NoEventIfThen360Target env s base idx6 x32 x64 t v su e).mem =
      stage2NoEventErrMem s.mem t v su e x64 := by
  simp only [stage2NoEventIfThen360Target, stage2NoEventJumpState, stateAt]

/-- **`if.then360`'s exit**: the entry's index read binds `%arrayidx361`, `%51` and
`%conv362`, and the zero rule's stores follow. -/
theorem stage2NoEventIfThen360_exit {gap : Calls} {mem : Mem} {F k : Nat}
    {K : Stage2NoEventWalkCarry} {s sE : State} {j : Nat}
    {w : Nat} {idx6 : BitVec w} {x32 : BitVec 32} {x64 : BitVec 64}
    (hj : ∀ n, runFuel (stage2NoEventCalls gap) (j + n) stage2NoEventBody s =
      runFuel (stage2NoEventCalls gap) n stage2NoEventBody sE)
    (hpc : sE.pc = "if.then360")
    (hxp : lookupName sE.env "%ep" = some (.ptr K.ep))
    (hk6 : lookupName sE.env "%k.6" = some (.int w idx6))
    (hpos : (idx6.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes sE.mem (K.ep + (idx6.signExtend 64).toNat * 4) 4 =
      some (natToBytes x32.toNat 4))
    (hconv : x64 = BitVec.ofNat 64 x32.toNat)
    (hinc0 : phiIncoming "if.then360" cleanup580Incoming = some (.imm (.int 64 0)))
    (hpar : Stage2NoEventWalkParams K sE)
    (hloc : Stage2NoEventWalkLocals K sE)
    (hle : x64.toNat ≤ K.n)
    (hcost : j + 1 ≤ stage2NoEventWalkPotential K k + F)
    (hreport : Stage2NoEventRun K.a12 mem
      (stage2NoEventErrMem sE.mem K.tokensOut K.valuesOut K.sumOut K.err x64))
    (htrace : Stage2NoEventWalkTrace K sE)
    (hrouteFrame : UnchangedOutside s.mem sE.mem
      (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
        [(K.next0, K.nextEnd - K.next0)]))
    (h : Stage2NoEventWalkInv K mem s) :
    Stage2NoEventWalkExit (stage2NoEventCalls gap) mem F K k s := by
  have hcode : denoteCode (stage2NoEventCalls gap)
      stage2NoEventIfThen360Block.instrs (stateAt sE.env sE) =
      some (stateAt (("%conv362", .int 64 x64) :: ("%51", .int 32 x32) ::
          ("%arrayidx361", .ptr (K.ep + (idx6.signExtend 64).toNat * 4)) :: sE.env)
        (stage2NoEventStepState sE
          (stage2NoEventErrMem sE.mem K.tokensOut K.valuesOut K.sumOut K.err x64)
          sE.next)) := by
    simp only [stage2NoEventIfThen360Block, List.cons_append, List.nil_append]
    rw [denoteCode_cons_of _ _ _ _ _
      (stage2NoEventWalk_step_gep32_reg (stage2NoEventCalls gap) sE.env sE
        "%arrayidx361" "%ep" "%k.6" hxp hk6 hpos)]
    rw [denoteCode_cons_of _ _ _ _ _
      (stage2NoEventWalk_step_load32 (stage2NoEventCalls gap)
        (("%arrayidx361", .ptr (K.ep + (idx6.signExtend 64).toNat * 4)) :: sE.env) sE
        "%51" "%arrayidx361" (x := x32) (by simp only [lookupName_cons_self]) hread)]
    rw [denoteCode_zext (calls := stage2NoEventCalls gap)
      (env := ("%51", .int 32 x32) ::
        ("%arrayidx361", .ptr (K.ep + (idx6.signExtend 64).toNat * 4)) :: sE.env)
      (s := sE) "%conv362" "%51" 32 64 (x := x32)
      (by simp only [lookupName_cons_self])]
    rw [hconv]
    rw [stage2NoEventZeroStore_denote
      (env := ("%conv362", .int 64 (BitVec.ofNat 64 x32.toNat)) ::
        ("%51", .int 32 x32) ::
        ("%arrayidx361", .ptr (K.ep + (idx6.signExtend 64).toNat * 4)) :: sE.env)
      (s := sE) (x := BitVec.ofNat 64 x32.toNat) "%conv362"
      (by
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
          lookupName_cons_ne _ _ (by decide)]
        exact hpar.tokensOut)
      (by
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
          lookupName_cons_ne _ _ (by decide)]
        exact hpar.valuesOut)
      (by
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
          lookupName_cons_ne _ _ (by decide)]
        exact hpar.sumOut)
      (by
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
          lookupName_cons_ne _ _ (by decide)]
        exact hpar.err)
      (by simp only [lookupName_cons_self])]
  have hstep : step (stage2NoEventCalls gap) stage2NoEventBody sE =
      .jump (stage2NoEventIfThen360Target sE.env sE K.ep idx6 x32 x64
        K.tokensOut K.valuesOut K.sumOut K.err) := by
    refine stage2NoEventWalk_step_at_block (s := stateAt sE.env sE)
      (s' := stateAt (("%conv362", .int 64 x64) :: ("%51", .int 32 x32) ::
        ("%arrayidx361", .ptr (K.ep + (idx6.signExtend 64).toNat * 4)) :: sE.env)
        (stage2NoEventStepState sE
          (stage2NoEventErrMem sE.mem K.tokensOut K.valuesOut K.sumOut K.err x64)
          sE.next))
      (b := stage2NoEventIfThen360Block) ?_ ?_ ?_
    · show stage2NoEventBody.findBlock sE.pc = some stage2NoEventIfThen360Block
      rw [hpc]; exact stage2NoEventIfThen360Block_find
    · exact hcode
    · simp only [stage2NoEventIfThen360Block, execTerm, stage2NoEventIfThen360Target,
        stage2NoEventJumpState, stage2NoEventStepState, stateAt, hpc]
  have hclean : step (stage2NoEventCalls gap) stage2NoEventBody
      (stage2NoEventIfThen360Target sE.env sE K.ep idx6 x32 x64
        K.tokensOut K.valuesOut K.sumOut K.err) =
      .ret (some (.int 64 0))
        (stateAt (("%retval.14", .int 64 0) ::
            ("%conv362", .int 64 x64) :: ("%51", .int 32 x32) ::
            ("%arrayidx361", .ptr (K.ep + (idx6.signExtend 64).toNat * 4)) :: sE.env)
          (stage2NoEventJumpState sE
            (stage2NoEventErrMem sE.mem K.tokensOut K.valuesOut K.sumOut K.err x64)
            sE.next "cleanup580" "if.then360")) :=
    stage2NoEventCleanup_step (gap := gap)
      (("%conv362", .int 64 x64) :: ("%51", .int 32 x32) ::
        ("%arrayidx361", .ptr (K.ep + (idx6.signExtend 64).toNat * 4)) :: sE.env)
      (stage2NoEventJumpState sE
        (stage2NoEventErrMem sE.mem K.tokensOut K.valuesOut K.sumOut K.err x64)
        sE.next "cleanup580" "if.then360") "if.then360" rfl rfl hinc0
      (c := K.c) (e := K.e) (stk := K.stk) (xj := K.xj)
      (by
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
          lookupName_cons_ne _ _ (by decide)]
        exact hpar.c)
      (by
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
          lookupName_cons_ne _ _ (by decide)]
        exact hpar.e)
      (by
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
          lookupName_cons_ne _ _ (by decide)]
        exact hpar.stk)
      (by
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
          lookupName_cons_ne _ _ (by decide)]
        exact hloc.xj)
  have henvT := stage2NoEventIfThen360Target_env sE.env sE K.ep idx6 x32 x64
    K.tokensOut K.valuesOut K.sumOut K.err
  refine stage2NoEventZero_exit (x := x64)
    (m := stage2NoEventErrMem sE.mem K.tokensOut K.valuesOut K.sumOut K.err x64)
    hj hstep hclean (by simp only [stateAt, stage2NoEventJumpState]) rfl
    ?_ ?_ ?_ ?_ ?_ hle hcost hreport htrace hrouteFrame h
  · rw [stage2NoEventIfThen360Target_mem]
  · rw [henvT]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hpar.tokensOut
  · rw [henvT]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hpar.valuesOut
  · rw [henvT]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hpar.sumOut
  · rw [henvT]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hpar.err

/-! ### The remaining entries' pins

The two gap entries and the two prefixed zero-store entries, pinned against the
parsed body so a re-capture that moves them fails the build.  `if.then527` and
`accept` are pinned in `JsonStage2NoEventWalkTerminal` (`refusalBlock_find`,
`acceptBlock_find`). -/

/-- `if.else510`, pinned. -/
def stage2NoEventIfElse510Block : Block :=
  { name := "if.else510",
    instrs :=
      [ Instr.store (Ty.int 64) (Operand.reg "%idxprom.lcssa") (Operand.reg "%off"),
        Instr.callVoid "od_gap_recover"
          [(Ty.ptr, (Operand.reg "%c")), ((Ty.int 64), (Operand.reg "%idxprom.lcssa"))],
        Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%tokens_out"),
        Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%values_out"),
        Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%sum_out"),
        Instr.load "%63" (Ty.int 64) (Operand.reg "%off"),
        Instr.store (Ty.int 64) (Operand.reg "%63") (Operand.reg "%err") ],
    term := Term.br "cleanup580" }

theorem stage2NoEventIfElse510Block_find :
    stage2NoEventBody.findBlock "if.else510" = some stage2NoEventIfElse510Block := by
  decide

/-- `cleanup491.thread`, pinned. -/
def stage2NoEventCleanup491Block : Block :=
  { name := "cleanup491.thread",
    instrs :=
      [ Instr.load "%60" (Ty.int 64) (Operand.reg "%ei"),
        Instr.binop "%add480" BinOp.add 64 (Operand.reg "%60")
          (Operand.reg "%idxprom.lcssa"),
        Instr.store (Ty.int 64) (Operand.reg "%add480") (Operand.reg "%off"),
        Instr.callVoid "od_gap_recover"
          [(Ty.ptr, (Operand.reg "%c")), ((Ty.int 64), (Operand.reg "%idxprom.lcssa"))],
        Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%tokens_out"),
        Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%values_out"),
        Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0)))
          (Operand.reg "%sum_out"),
        Instr.load "%61" (Ty.int 64) (Operand.reg "%off"),
        Instr.store (Ty.int 64) (Operand.reg "%61") (Operand.reg "%err"),
        Instr.callVoid "llvm.lifetime.end.p0"
          [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))),
            (Ty.ptr, (Operand.reg "%ei"))],
        Instr.callVoid "llvm.lifetime.end.p0"
          [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))),
            (Ty.ptr, (Operand.reg "%d"))] ],
    term := Term.br "cleanup580" }

theorem stage2NoEventCleanup491Block_find :
    stage2NoEventBody.findBlock "cleanup491.thread" = some stage2NoEventCleanup491Block := by
  decide

/-! ### The entries' census

The terminal class's entry set: every `cleanup580` predecessor, with the refusal
family it invokes.  The census is a name list, not the contract — the routes are
the producers above — and the guard checks it against the parsed `phi`'s incoming
list, so an entry added to the body and not to this list fails the build.  The
family column names the shape the entry's route produces; the two gap entries
whose `denoteCode` chains this module does not derive (`gapElse`, `gapNumber`)
are pinned and their evidence is the route's, which the header records. -/

/-- **The terminal entries**, with the family each invokes. -/
def stage2NoEventTerminalEntries : List (String × String) :=
  [("if.then", "zeroStore"), ("if.then12", "zeroStore"), ("if.then38", "zeroStore"),
   ("if.then68", "zeroStore"), ("if.then94", "zeroStore"), ("if.then105", "zeroStore"),
   ("if.then118", "zeroStore"), ("if.then297", "zeroStore"), ("if.then311", "zeroStore"),
   ("if.then321", "zeroStore"), ("if.then360", "zeroStore"), ("if.then372", "zeroStore"),
   ("if.then402", "zeroStore"), ("if.then428", "zeroStore"), ("if.then562", "zeroStore"),
   ("cleanup.thread", "errStore"), ("cleanup287.thread", "errStore"),
   ("cleanup491.thread", "gapNumber"), ("if.else510", "gapElse"),
   ("if.then527", "gapLiteral"), ("accept", "accept")]

/-- **Every entry is a `cleanup580` predecessor.** -/
def stage2NoEventTerminalCensus : Bool :=
  stage2NoEventTerminalEntries.all fun e =>
    decide (e.1 ∈ cleanup580Incoming.map (·.1))

/-- **Every `cleanup580` predecessor is an entry.** -/
def stage2NoEventTerminalCensusCover : Bool :=
  cleanup580Incoming.all fun e => decide (e.1 ∈ stage2NoEventTerminalEntries.map (·.1))

#guard stage2NoEventTerminalEntries.length = 21
#guard stage2NoEventTerminalCensus
#guard stage2NoEventTerminalCensusCover
#guard decide (stage2NoEventBody.findBlock "if.else510" ≠ none)
#guard decide (stage2NoEventBody.findBlock "cleanup491.thread" ≠ none)
#guard decide (stage2NoEventBody.findBlock "cleanup287.thread" ≠ none)
#guard stage2NoEventIfThen38Incoming.length = 2

/-! ### Axiom footprints -/

#print axioms Stage2NoEventWalkRunTo.extend
#print axioms Stage2NoEventWalkRunTo.run_of_cleanup
#print axioms stage2NoEventZeroStore_denote
#print axioms stage2NoEventZero_step
#print axioms stage2NoEventErrMem_reads
#print axioms stage2NoEventZero_evidence
#print axioms stage2NoEventZero_exit
#print axioms stage2NoEventZeroBlock_exit
#print axioms stage2NoEventZeroBlock_row
#print axioms stage2NoEventRefuse_exit
#print axioms stage2NoEventAccept_exit
#print axioms stage2NoEventPhiZeroStore_denote
#print axioms stage2NoEventIfThen38_exit
#print axioms stage2NoEventIfThen360_exit
#print axioms stage2NoEventWalk_step_gep32_reg
#print axioms stage2NoEventWalk_step_load32
#print axioms stage2NoEventBoundaryFrame
#print axioms stage2NoEventErrStore_denote
#print axioms stage2NoEventErrStore_step
#print axioms stage2NoEventErrStore_exit
#print axioms stage2NoEventCleanupThread_exit
#print axioms stage2NoEventCleanup287_exit
#print axioms stage2NoEventWalkSep_off_err
#print axioms stage2NoEventErrMem_off_read
#print axioms stage2NoEventGapLiteral_exit
#print axioms stage2NoEventErrMem_writes_frame
#print axioms stage2NoEventIfThen38Block_find
#print axioms stage2NoEventIfThen360Block_find
#print axioms stage2NoEventIfElse510Block_find
#print axioms stage2NoEventCleanup491Block_find
