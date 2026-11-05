import LeanLLVM
import LeanLLVM.Vellum.JsonScanABI
import LeanLLVM.Vellum.JsonScanModel
import LeanLLVM.Vellum.JsonScanIR
import LeanLLVM.Vellum.JsonScanLane
import LeanLLVM.Vellum.JsonScanSpec
import LeanLLVM.Vellum.Pclmul

open LeanLLVM.Vellum

-- The local obligation: the candidate refines the baseline.
example : commaContract ⊢ byteLoop ⊑ swar := byteLoop_refines_swar

-- Correctness transfers along refinement.
example : Correct commaContract byteLoop := byteLoop_correct

-- Contextual replacement preserves a two-call caller.
example (x : BitVec 64) :
    twoCallContext.run byteLoop x = twoCallContext.run swar x :=
  twoCallContext_preserved x

-- The same statement at the C ABI type.
example (x : UInt64) : seamCandidate x = seamBaseline x := seam_refines x

-- Concrete values, including the borrow counterexample lane.
#guard spec 0x2D2C = 0x80
#guard byteLoop 0x2D2C = 0x80
#guard swar 0x2D2C = 0x80
#guard swar 0x2C2C2C2C2C2C2C2C = 0x8080808080808080

-- The two 64-bit identities are kernel-checked by the byte-lane argument in
-- `CommaMaskKernel.lean`; no native bit-blast axioms survive.  The pins record
-- the remaining standard footprint.

/--
info: 'LeanLLVM.Vellum.swar_eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.swar_eq_spec

/--
info: 'LeanLLVM.Vellum.byteLoop_eq_spec' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.byteLoop_eq_spec

/--
info: 'LeanLLVM.Vellum.byteLoop_refines_swar' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.byteLoop_refines_swar

/--
info: 'LeanLLVM.Vellum.twoCallContext_preserved' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.twoCallContext_preserved

-- The probe's `Baseline.lean` body is definitionally the proved function.
def probeBaselineBody (x : UInt64) : UInt64 :=
  let m := x ^^^ 0x2C2C2C2C2C2C2C2C
  ~~~(((m &&& 0x7F7F7F7F7F7F7F7F) + 0x7F7F7F7F7F7F7F7F) ||| m) &&& 0x8080808080808080

example : probeBaselineBody = seamBaseline := by
  funext x
  rfl

-- The emitted-IR bridge: the two probe fixtures parse to the checked ASTs, and
-- the parsed candidate refines the parsed baseline.  The pins record that the
-- bridge adds no axiom beyond the standard footprint.
open LeanLLVM.Vellum.CommaMaskIR

example : ∀ calls, LeanLLVM.Refines calls candidateFunction baselineFunction :=
  IR_refines

/--
info: 'LeanLLVM.Vellum.CommaMaskIR.baseOut_eq_swar' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.CommaMaskIR.baseOut_eq_swar

/--
info: 'LeanLLVM.Vellum.CommaMaskIR.candOut_eq_byteLoop' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.CommaMaskIR.candOut_eq_byteLoop

/--
info: 'LeanLLVM.Vellum.CommaMaskIR.IR_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.CommaMaskIR.IR_refines

-- The contextual replacement theorem: a caller in the semantics calls the seam
-- and the result comes from the call environment, not from an inlined body.
open LeanLLVM.Vellum.SeamContext

example (x : BitVec 64) (o : LeanLLVM.Outcome) :
    LeanLLVM.Beh (envFor byteLoop) callerFunction [LeanLLVM.Value.int 64 x] o ↔
      LeanLLVM.Beh (envFor swar) callerFunction [LeanLLVM.Value.int 64 x] o :=
  caller_seam_replacement x o

/--
info: 'LeanLLVM.Vellum.SeamContext.caller_beh' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.SeamContext.caller_beh

/--
info: 'LeanLLVM.Vellum.SeamContext.caller_seam_replacement' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.SeamContext.caller_seam_replacement

-- The directional rule: `none` is `ub`, so a deterministic environment still
-- has a non-trivial refinement order.
example (x : BitVec 64) (o : LeanLLVM.Outcome) :
    LeanLLVM.Beh (envFor byteLoop) callerFunction [LeanLLVM.Value.int 64 x] o →
      LeanLLVM.Beh (envFor swar) callerFunction [LeanLLVM.Value.int 64 x] o :=
  caller_refines_under_seam x o

-- `h` can fail: an environment that leaves the seam undefined where the
-- baseline defines it is not a refinement of it.  That is the environment
-- direction on its own; the module-level negative control below shows the
-- replacement conclusion fails with it.
example : ¬ LeanLLVM.CallRefines (fun _ _ _ _ => none) (envFor swar) seamSymbol :=
  undefined_env_not_refines

/--
info: 'LeanLLVM.Beh_refines' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Beh_refines

/--
info: 'LeanLLVM.Vellum.SeamContext.caller_refines_under_seam' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.SeamContext.caller_refines_under_seam

-- The memory-backed loop, executed by the semantics, returns the same mask as
-- the unrolled candidate on the lane examples.
open LeanLLVM.Vellum.CommaMaskLoop

#guard
  match LeanLLVM.run LeanLLVM.noCalls loopFunction
      [LeanLLVM.Value.int 64 0x2D2C] with
  | some (.ret (some v) _) => v == LeanLLVM.Value.int 64 0x80
  | _ => false

#guard
  match LeanLLVM.run LeanLLVM.noCalls loopFunction
      [LeanLLVM.Value.int 64 0x2C2C2C2C2C2C2C2C] with
  | some (.ret (some v) _) => v == LeanLLVM.Value.int 64 0x8080808080808080
  | _ => false

-- The loop leaves bytes only in the band its two allocations cover, and at
-- least one: the accumulator and the counter are both written.
#guard
  match LeanLLVM.run LeanLLVM.noCalls loopFunction
      [LeanLLVM.Value.int 64 0x2D2C] with
  | some (.ret _ m) => !m.isEmpty && m.all (fun (a, _) => decide (1 ≤ a ∧ a < 17))
  | _ => false

-- The loop's footprint is read off the allocator: two eight-byte locals from
-- the reserved address one.  It is not the universal predicate, so agreement
-- outside it says something about the returned memory.
example (x : BitVec 64) : loopFrame x = LeanLLVM.Band 1 17 := loopFrame_eq x

-- The two addresses the loop stores to are the locals its `alloca`s handed out,
-- and both are inside the band.
example (x : BitVec 64) : loopFrame x 1 ∧ loopFrame x 9 :=
  loop_store_addresses_in_band x

example (x : BitVec 64) : ¬ (∀ a, loopFrame x a) := by
  intro h
  have h0 : loopFrame x 0 := h 0
  rw [loopFrame_eq] at h0
  simp [LeanLLVM.Band] at h0

-- The framed relation, applied to the loop and the unrolled comparator: the
-- same returned value and byte agreement outside the loop's allocation band.
example (x : BitVec 64) (o : LeanLLVM.Outcome) :
    LeanLLVM.Beh LeanLLVM.noCalls loopFunction [LeanLLVM.Value.int 64 x] o →
      ∃ o', LeanLLVM.Beh LeanLLVM.noCalls candidateFunction
          [LeanLLVM.Value.int 64 x] o' ∧ o.AgreesOutside (loopFrame x) o' :=
  loop_refines_candidate_within x o

example (x : BitVec 64) :
    ∃ memL,
      LeanLLVM.Beh LeanLLVM.noCalls loopFunction [LeanLLVM.Value.int 64 x]
        (.ret (some (LeanLLVM.Value.int 64 (spec x))) memL) ∧
      LeanLLVM.Beh LeanLLVM.noCalls candidateFunction [LeanLLVM.Value.int 64 x]
        (.ret (some (LeanLLVM.Value.int 64 (spec x))) []) ∧
      (LeanLLVM.Outcome.ret (some (LeanLLVM.Value.int 64 (spec x))) memL).AgreesOutside
        (loopFrame x)
        (LeanLLVM.Outcome.ret (some (LeanLLVM.Value.int 64 (spec x))) []) :=
  loop_and_candidate_framed x

-- Exact refinement yields framed refinement, so the existing theorems keep
-- their meaning and the framed relation is the weaker statement beside them.
example : ∀ calls, LeanLLVM.RefinesWithin calls candidateFunction baselineFunction
    (fun a => 1 ≤ a ∧ a < 17) :=
  fun calls => LeanLLVM.refinesWithin_of_refines (IR_refines calls)

-- A unit that writes one byte through the null pointer — address `0`, outside
-- the loop's band `[1, 17)` — and returns zero.  Its returned value matches the
-- unit below; only the memory differs, which is what the framed relation must
-- refuse to forget.  The model has no null check, so the store is defined and
-- the byte is observable.
def vandalFunction : LeanLLVM.Function :=
  { name := "vandal", retTy := .int 64, params := [],
    blocks := [
      { name := "entry",
        instrs := [.store (.int 8) (.imm (.int 8 1)) (.imm .null)],
        term := .ret (.int 64) (some (.imm (.int 64 0))) }] }

/-- The same returned value, no memory. -/
def quietFunction : LeanLLVM.Function :=
  { name := "quiet", retTy := .int 64, params := [],
    blocks := [
      { name := "entry", instrs := [],
        term := .ret (.int 64) (some (.imm (.int 64 0))) }] }

theorem vandal_beh :
    LeanLLVM.Beh LeanLLVM.noCalls vandalFunction []
      (.ret (some (.int 64 0))
        (LeanLLVM.writeBytes [] 0 (LeanLLVM.natToBytes 1 1))) := by
  refine Or.inr ⟨1, ?_⟩
  simp [LeanLLVM.runFuel, LeanLLVM.step, vandalFunction, LeanLLVM.Function.findBlock,
    LeanLLVM.findBlockList, LeanLLVM.denoteCode, LeanLLVM.evalInstr,
    LeanLLVM.evalOperand, LeanLLVM.Const.toValue, LeanLLVM.storeValue,
    LeanLLVM.execTerm, LeanLLVM.initState, LeanLLVM.Function.entry?]

theorem quiet_run (n : Nat) (s : LeanLLVM.State) (hpc : s.pc = "entry") :
    LeanLLVM.runFuel LeanLLVM.noCalls (n + 1) quietFunction s =
      some (.ret (some (.int 64 0)) s.mem) := by
  cases n <;>
    simp [LeanLLVM.runFuel, LeanLLVM.step, quietFunction, LeanLLVM.Function.findBlock,
      LeanLLVM.findBlockList, LeanLLVM.denoteCode, LeanLLVM.execTerm,
      LeanLLVM.evalOperand, LeanLLVM.Const.toValue, hpc]

theorem quiet_beh (o : LeanLLVM.Outcome)
    (h : LeanLLVM.Beh LeanLLVM.noCalls quietFunction [] o) :
    o = .ret (some (.int 64 0)) [] := by
  rcases h with ⟨n, hu⟩ | ⟨n, hr⟩
  · cases n with
    | zero => simp [LeanLLVM.runFuel] at hu
    | succ n =>
        rw [quiet_run n (LeanLLVM.initState quietFunction []) rfl] at hu
        cases hu
  · cases n with
    | zero => simp [LeanLLVM.runFuel] at hr
    | succ n =>
        rw [quiet_run n (LeanLLVM.initState quietFunction []) rfl] at hr
        have := (Option.some.inj hr).symm
        simpa [LeanLLVM.initState] using this

-- The frame is load-bearing: an equal return value and a byte written outside
-- the frame is not a framed refinement.  This is the memory content of the
-- framed relation, here under `noCalls`; it is not evidence for the value-level
-- module theorem below, whose frame is inert for its own hypothesis, because
-- `CallRefines` demands complete agreement of the value, the memory and the
-- allocator state of the two outcomes.
theorem vandal_not_refinesWithin :
    ¬ LeanLLVM.RefinesWithin LeanLLVM.noCalls vandalFunction quietFunction
      (fun a => 1 ≤ a ∧ a < 17) := by
  intro h
  obtain ⟨o', hbeh, hag⟩ := h [] _ vandal_beh
  have ho' := quiet_beh o' hbeh
  subst ho'
  obtain ⟨-, hmem⟩ := hag
  have h0 : LeanLLVM.readByte (LeanLLVM.writeBytes [] 0 (LeanLLVM.natToBytes 1 1)) 0 =
      LeanLLVM.readByte [] 0 := hmem 0 (by decide)
  exact absurd h0 (by decide)

/-! ### The module-level replacement

`replaceFunction_sound` composes the directional environment relation into the
framed refinement of one caller under two selections, and `memCaller` is a
caller with a footprint of its own.  The two pins record the environment
composition; the negative control at the end is the test of the conclusion.
-/

-- The instance: the memory-backed loop's selection (`spec`) against the
-- unrolled candidate's (`byteLoop`), for a caller whose `alloca` gives it a
-- local of its own.
example : LeanLLVM.Vellum.RefinesWithinAcross (envFor spec) (envFor byteLoop)
    memCaller memCaller callerFrame :=
  memCaller_replaces_loop

/-- info: 'LeanLLVM.Vellum.replaceFunction_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.replaceFunction_sound

/-- info: 'LeanLLVM.Vellum.memCaller_replaces_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.memCaller_replaces_loop

-- With no environment entry the caller's call is unresolved, which the
-- semantics turns into `ub` at the first step.
theorem callerInstrs_none (s : LeanLLVM.State) :
    LeanLLVM.denoteCode (fun _ _ _ _ => none) callerInstrs s = none := by
  have hcall : LeanLLVM.evalInstr (fun _ _ _ _ => none) s
      (.call "%r" (.int 64) seamSymbol [(.int 64, .reg "%arg")]) = none := by
    cases h : LeanLLVM.evalOperands s [(.int 64, .reg "%arg")] with
    | none => simp [LeanLLVM.evalInstr, h]
    | some vs => simp [LeanLLVM.evalInstr, h]
  simp [callerInstrs, LeanLLVM.denoteCode, hcall]

theorem caller_step_none :
    LeanLLVM.step (fun _ _ _ _ => none) callerFunction
      (LeanLLVM.initState callerFunction [LeanLLVM.Value.int 64 0]) = .ub := by
  have hfind : callerFunction.findBlock
      (LeanLLVM.initState callerFunction [LeanLLVM.Value.int 64 0]).pc =
        some callerBody := caller_findBlock (x := (0 : BitVec 64))
  rw [LeanLLVM.step, hfind]
  simp [callerBody, callerInstrs_none]

-- The conclusion is not vacuous: the same caller under the undefined
-- environment reaches `ub`, while under `envFor swar` its only behaviour is the
-- defined return, and `ub` is matched by a defined source only by a `ub`
-- source.  Had the relation dropped `calls'`, the hypothesis would be trivial
-- and this negation unprovable.
theorem caller_not_refined_by_undefined_env :
    ¬ LeanLLVM.Vellum.RefinesWithinAcross (fun _ _ _ _ => none) (envFor swar)
        callerFunction callerFunction (LeanLLVM.Band 1 9) := by
  intro h
  obtain ⟨o', hsrc, hag⟩ :=
    h [LeanLLVM.Value.int 64 0] LeanLLVM.Outcome.ub
      (Or.inl ⟨1, by rw [LeanLLVM.runFuel, caller_step_none]⟩)
  have ho' : o' = .ret (some (.int 64 (swar 0))) [] := (caller_beh swar 0 o').1 hsrc
  rw [ho'] at hag
  cases hag

/-- info: 'LeanLLVM.Vellum.CommaMaskLoop.loop_run_fuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.CommaMaskLoop.loop_run_fuel

/-- info: 'LeanLLVM.Vellum.CommaMaskLoop.loop_returns_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.CommaMaskLoop.loop_returns_spec

/-- info: 'LeanLLVM.Vellum.CommaMaskLoop.loop_returns_spec_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.CommaMaskLoop.loop_returns_spec_frame

/-- info: 'LeanLLVM.Vellum.CommaMaskLoop.loop_beh_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.CommaMaskLoop.loop_beh_ret

/-- info: 'LeanLLVM.Vellum.CommaMaskLoop.loop_refines_candidate_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.CommaMaskLoop.loop_refines_candidate_within

/-- info: 'LeanLLVM.Vellum.CommaMaskLoop.loop_and_candidate_framed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.CommaMaskLoop.loop_and_candidate_framed

/-- info: 'LeanLLVM.AgreesOutsideMem.of_private' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.AgreesOutsideMem.of_private

/-- info: 'LeanLLVM.refinesWithin_of_refines' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.refinesWithin_of_refines

/-- info: 'LeanLLVM.runFuel_outcome_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.runFuel_outcome_unique


/-! ### The directed tree relation

The relation compares **bare handled trees**: `handle` folds a source tree's
memory into it, so there is no memory index and no frame parameter left in
`simtt`.  The checks below assert the handler's own equations first, then the
relation on the trees it produces.  The same detector is used for each
affirmative and its refusals, and the `#print axioms` pins record the kernel
footprint.
-/

open LeanLLVM
open LeanLLVM.ITree

/-- A fixed argument, so every check below uses one frame. -/
abbrev checkX : BitVec 64 := 0x0123456789ABCDEF

abbrev checkFrame : Nat → Prop := loopFrame checkX

abbrev checkPost : Outcome → Outcome → Prop := LeanLLVM.Outcome.AgreesOutside (loopFrame checkX)

abbrev checkPostTrue : Outcome → Outcome → Prop := fun _ _ => True

abbrev checkPostFalse : Outcome → Outcome → Prop := fun _ _ => False

/-! #### The handler's equations

`handle` is proof-facing and noncomputable, because the frame is an arbitrary
proposition-valued predicate.  These are its equations at a defined private
load, an undefined private load, an out-of-frame store and a call. -/

/-- A byte at address `1` is in the loop's band. -/
theorem band_one : InFrame checkFrame 1 (.int 8) := by
  intro k hk
  rw [checkFrame, loopFrame_eq]
  simp only [Ty.sizeBytes] at hk
  exact ⟨by omega, by omega⟩

/-- Address `0` is outside the loop's band. -/
theorem band_zero_out : ¬ InFrame checkFrame 0 (.int 8) := by
  intro hf
  have h := hf 0 (by decide)
  rw [checkFrame, loopFrame_eq] at h
  simp [Band] at h

/-- The continuation of the load checks: one returned value and a stale empty
memory, so a handler-produced leaf memory is visibly not the source's. -/
abbrev staleK (v : Option Value) : ITree.Tree Ev Outcome :=
  ITree.ret (Outcome.ret v [])

abbrev loadK : Option Value → ITree.Tree Ev Outcome := fun _ => staleK (some (.int 8 1))

abbrev unitK : Unit → ITree.Tree Ev Outcome := fun _ => staleK (some (.int 8 1))

theorem load_value_defined : loadValue [(1, 5)] (.int 8) 1 = some (.int 8 5) := by decide

theorem load_value_none_in : loadValue ([] : Mem) (.int 8) 1 = none := by decide

/-- A defined in-frame load is silent: the handler inserts a `tau` and leaves
its memory alone, because a load writes nothing. -/
example : handle checkFrame [(1, 5)] (ITree.vis (Ev.load 1 (.int 8)) loadK) =
    ITree.tau (handle checkFrame [(1, 5)] (loadK (some (.int 8 5)))) :=
  handle_load_private band_one load_value_defined

/-- An undefined in-frame load stays visible, annotated `none`, and the
continuation receives `none`: nothing is discarded. -/
example : handle checkFrame [] (ITree.vis (Ev.load 1 (.int 8)) loadK) =
    ITree.vis (ObsEv.load 1 (.int 8) none) (fun () => handle checkFrame [] (loadK none)) :=
  handle_load_none load_value_none_in

theorem store_mem_out : storeMem ([] : Mem) (.int 8) (.int 8 7) 0 = [(0, 7)] := by decide

/-- An out-of-frame store emits its own address, type and value, and its
continuation is the handler at the memory the store wrote — not the stale leaf's
memory. -/
example : handle checkFrame [] (ITree.vis (Ev.store 0 (.int 8) (.int 8 7)) unitK) =
    ITree.vis (ObsEv.store 0 (.int 8) (.int 8 7))
      (fun () => handle checkFrame (storeMem [] (.int 8) (.int 8 7) 0) (unitK ())) :=
  handle_store_visible band_zero_out

/-- Applying that continuation returns this side's `storeMem`, and the write is
real: the handler's state is not the source leaf's empty memory. -/
theorem store_continuation_mem :
    handle checkFrame (storeMem [] (.int 8) (.int 8 7) 0) (unitK ()) =
      ITree.ret (Outcome.ret (some (.int 8 1)) (storeMem [] (.int 8) (.int 8 7) 0)) := by
  rw [show unitK () = staleK (some (.int 8 1)) from rfl, staleK, handle_ret]
  rfl

theorem store_mem_ne_stale : storeMem ([] : Mem) (.int 8) (.int 8 7) 0 ≠ [] := by
  rw [store_mem_out]
  decide

/-- A call is re-emitted with its own callee and arguments, the memory is
untouched, and every response is passed to the source continuation unchanged. -/
example (callee : String) (args : List Value) (m : Mem)
    (k : Option Value → ITree.Tree Ev Outcome) :
    handle checkFrame m (ITree.vis (Ev.call callee args) k) =
      ITree.vis (ObsEv.call callee args) (fun r => handle checkFrame m (k r)) :=
  handle_call

/-! #### Silent terminals, divergence and the UB class

The empty-response nodes are the relation's own: `ObsEv.ub` is a completed
undefined behaviour, `ObsEv.timeout` an exhausted budget. -/

abbrev ubNode : OTree := ITree.vis ObsEv.ub Empty.elim

abbrev timeoutNode : OTree := ITree.vis ObsEv.timeout Empty.elim

abbrev retNode : OTree := ITree.ret (Outcome.ret (some (.int 64 0)) [])

/-- The affirmative control: a budget timeout matches itself. -/
example : simtt checkPost timeoutNode timeoutNode :=
  simtt_timeout_timeout checkPost Empty.elim Empty.elim

/-- A timeout is not a right undefined behaviour. -/
example : ¬ simtt checkPost timeoutNode ubNode :=
  not_simtt_timeout_ub checkPost Empty.elim Empty.elim

/-- Nor is a left undefined behaviour a timeout. -/
example : ¬ simtt checkPost ubNode timeoutNode :=
  not_simtt_ub_timeout checkPost Empty.elim Empty.elim

/-- A timeout is not a return. -/
example : ¬ simtt checkPost timeoutNode retNode :=
  not_simtt_timeout_ret checkPost _ Empty.elim

/-- Nor is a return a timeout. -/
example : ¬ simtt checkPost retNode timeoutNode :=
  not_simtt_ret_timeout checkPost _ Empty.elim

/-- A right `ub` admits a completed left return. -/
example : simtt checkPost retNode ubNode :=
  simtt_ret_ub checkPost _

/-- A left `ub` node is not matched by a defined return. -/
example : ¬ simtt checkPost ubNode retNode :=
  not_simtt_ub_ret checkPost _ [] Empty.elim

/-- Left silent divergence is the bottom against a return. -/
example : simtt checkPost ITree.infTau retNode :=
  simtt_diverges_ret checkPost _

/-- Right silent divergence is not admitted by a return. -/
example : ¬ simtt checkPost retNode ITree.infTau :=
  not_simtt_ret_diverges checkPost _

/-- Both sides diverge silently, so the negative just above is not the whole
story: the same detector admits two silent divergences. -/
example : simtt checkPost ITree.infTau ITree.infTau :=
  simtt_diverges_diverges checkPost

/-- Left silent divergence is related to a right `ub`. -/
example : simtt checkPost ITree.infTau ubNode :=
  simtt_diverges_ub checkPost Empty.elim

/-- Two UB terminals are related whatever their shape and regardless of
`post`; the two shapes are one class. -/
example : simtt checkPostFalse (ITree.ret Outcome.ub) (ITree.ret Outcome.ub) :=
  simtt_ub_terminal checkPostFalse UbTerminal.retLeaf UbTerminal.retLeaf

/-- `ret .ub` on the left against a `vis ObsEv.ub` node on the right. -/
example : simtt checkPostFalse (ITree.ret Outcome.ub) ubNode :=
  simtt_ub_terminal checkPostFalse UbTerminal.retLeaf (UbTerminal.ubNode Empty.elim)

/-- And a `vis ObsEv.ub` node against itself. -/
example : simtt checkPostFalse ubNode ubNode :=
  simtt_ub_ub checkPostFalse Empty.elim Empty.elim

/-- The affirmative control for the UB refusals: two defined returns related by
`post` under the same permissive post. -/
example : simtt checkPostTrue retNode retNode :=
  (simtt_ret_ret_iff checkPostTrue _ _ _ _).mpr trivial

/-- A left `ret` leaf carrying `Outcome.ub` is not related to a defined return,
even when `post` holds of every pair. -/
example : ¬ simtt checkPostTrue (ITree.ret Outcome.ub) retNode :=
  not_simtt_ret_ub_ret checkPostTrue _ [] 

/-- A `vis ObsEv.ub` node is absent from the same check, so the two shapes
behave alike on the left. -/
example : ¬ simtt checkPostTrue ubNode retNode :=
  not_simtt_ub_ret checkPostTrue _ [] Empty.elim

/-- A right `ret` leaf carrying `Outcome.ub` admits a completed left return even
when `post` holds of no pair, which is what makes the admission
`post`-independent. -/
example : simtt checkPostFalse retNode (ITree.ret Outcome.ub) :=
  simtt_ret_ub_terminal checkPostFalse _ UbTerminal.retLeaf

/-! #### Visible loads: the handler's annotation is what matches

The load clause relates two visible loads only when their handler-computed
annotations agree.  Two memories defining the same byte are related, two
undefined loads are related, and a defined answer against an undefined load is
refused — all under one detector, one event and one continuation. -/

theorem load_defined_both : loadValue [(0, 1)] (.int 8) 0 = loadValue [(0, 1), (5, 9)] (.int 8) 0 := by
  decide

theorem load_undefined_both : loadValue ([] : Mem) (.int 8) 0 = loadValue [(5, 9)] (.int 8) 0 := by
  decide

theorem load_defined_vs_undefined :
    loadValue [(0, 1)] (.int 8) 0 ≠ loadValue ([] : Mem) (.int 8) 0 := by
  decide

/-- Equal defined responses: the same visible load matches at two different
handler memories. -/
example : simtt checkPost
    (ITree.vis (ObsEv.load 0 (.int 8) (some (.int 8 1))) (fun () => retNode))
    (ITree.vis (ObsEv.load 0 (.int 8) (some (.int 8 1))) (fun () => retNode)) := by
  refine (simtt_iff _ _ _).mpr ?_
  exact SimttF.vis_load 0 (.int 8) (some (.int 8 1)) _ _
    (SilentHead.refl _) (SilentHead.refl _)
    ((simtt_ret_ret_iff _ _ _ _ _).mpr (Outcome.agreesOutside_refl _ checkFrame))

/-- Two undefined loads are admitted as well: the affirmative control for the
negative below. -/
example : simtt checkPost
    (ITree.vis (ObsEv.load 0 (.int 8) none) (fun () => retNode))
    (ITree.vis (ObsEv.load 0 (.int 8) none) (fun () => retNode)) := by
  refine (simtt_iff _ _ _).mpr ?_
  exact SimttF.vis_load 0 (.int 8) none _ _
    (SilentHead.refl _) (SilentHead.refl _)
    ((simtt_ret_ret_iff _ _ _ _ _).mpr (Outcome.agreesOutside_refl _ checkFrame))

/-- A same-shape out-of-frame load whose handler-computed responses differ is
refused by the same detector that accepts the equal pair: the annotation is part
of the visible event. -/
example : ¬ simtt checkPost
    (ITree.vis (ObsEv.load 0 (.int 8) (some (.int 8 1))) (fun () => retNode))
    (ITree.vis (ObsEv.load 0 (.int 8) none) (fun () => retNode)) :=
  not_simtt_load_ne checkPost (by decide) _ _

/-! #### Visible stores: matching, and three field-only refusals

The affirmative and the refusals below share one detector, one event and one
pair of continuations, and differ only in the store's address, type or value.
The continuations report a deliberately stale leaf memory that is not their
own handler's store result. -/

abbrev staleMemL : Mem := []

abbrev storeMemL : Mem := [(1, 1)]

abbrev storeMemR : Mem := [(1, 2)]

/-- The nonvacuous post: each side's returned memory is that side's own store
result. -/
abbrev bothStores : Outcome → Outcome → Prop := fun left right =>
  left = Outcome.ret (some (.int 8 1)) (storeMem storeMemL (.int 8) (.int 8 7) 0) ∧
    right = Outcome.ret (some (.int 8 1)) (storeMem storeMemR (.int 8) (.int 8 7) 0)

abbrev storeKLeft : Unit → OTree :=
  fun () => ITree.ret (Outcome.ret (some (.int 8 1)) (storeMem storeMemL (.int 8) (.int 8 7) 0))

abbrev storeKRight : Unit → OTree :=
  fun () => ITree.ret (Outcome.ret (some (.int 8 1)) (storeMem storeMemR (.int 8) (.int 8 7) 0))

/-- Equal visible stores simulate, with each final memory bound to its own side's
store result. -/
example : simtt bothStores
    (ITree.vis (ObsEv.store 0 (.int 8) (.int 8 7)) storeKLeft)
    (ITree.vis (ObsEv.store 0 (.int 8) (.int 8 7)) storeKRight) := by
  refine (simtt_iff _ _ _).mpr ?_
  exact SimttF.vis_store 0 (.int 8) (.int 8 7) _ _
    (SilentHead.refl _) (SilentHead.refl _)
    ((simtt_ret_ret_iff _ _ _ _ _).mpr ⟨rfl, rfl⟩)

/-- The affirmative control under the permissive detector that the three
refusals below use: the equal case is accepted. -/
example : simtt checkPostTrue
    (ITree.vis (ObsEv.store 0 (.int 8) (.int 8 7)) storeKLeft)
    (ITree.vis (ObsEv.store 0 (.int 8) (.int 8 7)) storeKRight) := by
  refine (simtt_iff _ _ _).mpr ?_
  exact SimttF.vis_store 0 (.int 8) (.int 8 7) _ _
    (SilentHead.refl _) (SilentHead.refl _)
    ((simtt_ret_ret_iff _ _ _ _ _).mpr trivial)

/-- Only the address differs: refused under the same detector. -/
example : ¬ simtt checkPostTrue
    (ITree.vis (ObsEv.store 0 (.int 8) (.int 8 7)) storeKLeft)
    (ITree.vis (ObsEv.store 1 (.int 8) (.int 8 7)) storeKRight) :=
  not_simtt_store_ne checkPostTrue (by decide) _ _

/-- Only the type differs: refused. -/
example : ¬ simtt checkPostTrue
    (ITree.vis (ObsEv.store 0 (.int 8) (.int 8 7)) storeKLeft)
    (ITree.vis (ObsEv.store 0 (.int 16) (.int 8 7)) storeKRight) :=
  not_simtt_store_ne checkPostTrue (by decide) _ _

/-- Only the value differs: refused. -/
example : ¬ simtt checkPostTrue
    (ITree.vis (ObsEv.store 0 (.int 8) (.int 8 7)) storeKLeft)
    (ITree.vis (ObsEv.store 0 (.int 8) (.int 8 8)) storeKRight) :=
  not_simtt_store_ne checkPostTrue (by decide) _ _

/-! #### Independent returned memories

Two raw source trees whose leaves record a stale memory are handled from
*distinct* initial memories.  Each handled return carries its own handler's final
state — not the source leaf's stale memory and not the other side's — and the
same postcondition relates them.  The store is in-frame here, so the handler is
silent and the handled tree's own leaf is the one the handler wrote; the visible
store above is the out-of-frame case. -/

/-- The stale leaf: a memory that is neither handler's store result. -/
abbrev staleMem : Mem := []

/-- A raw source tree: one in-frame store at address `1` whose continuation
returns the value with a stale leaf memory. -/
abbrev storeSource : ITree.Tree Ev Outcome :=
  ITree.vis (Ev.store 1 (.int 8) (.int 8 7))
    (fun () => ITree.ret (Outcome.ret (some (.int 8 1)) staleMem))

/-- The two initial memories differ at an address the store does not touch, so
the two handler results are distinguishable. -/
abbrev storeInitL : Mem := [(3, 9)]

abbrev storeInitR : Mem := [(4, 9)]

/-- The left handler's final memory is the store it performed, from its own
initial memory. -/
theorem handled_store_mem_left :
    handle checkFrame storeInitL storeSource =
      ITree.tau (ITree.ret (Outcome.ret (some (.int 8 1))
        (storeMem storeInitL (.int 8) (.int 8 7) 1))) := by
  rw [storeSource, handle_store_private band_one, handle_ret]
  rfl

/-- The right handler's final memory is the store it performed, from its own
initial memory. -/
theorem handled_store_mem_right :
    handle checkFrame storeInitR storeSource =
      ITree.tau (ITree.ret (Outcome.ret (some (.int 8 1))
        (storeMem storeInitR (.int 8) (.int 8 7) 1))) := by
  rw [storeSource, handle_store_private band_one, handle_ret]
  rfl

/-- The nonvacuous post: each side's returned memory is that side's own store
result, and the two results are not interchangeable. -/
abbrev memPost : Outcome → Outcome → Prop := fun left right =>
  left = Outcome.ret (some (.int 8 1)) (storeMem storeInitL (.int 8) (.int 8 7) 1) ∧
    right = Outcome.ret (some (.int 8 1)) (storeMem storeInitR (.int 8) (.int 8 7) 1)

theorem store_mem_left_not_stale : storeMem storeInitL (.int 8) (.int 8 7) 1 ≠ staleMem := by
  decide

theorem store_mem_right_not_stale : storeMem storeInitR (.int 8) (.int 8 7) 1 ≠ staleMem := by
  decide

/-- Neither side's result is the other side's: the binding above is not
satisfied by swapping them. -/
theorem store_mem_left_ne_right :
    storeMem storeInitL (.int 8) (.int 8 7) 1 ≠ storeMem storeInitR (.int 8) (.int 8 7) 1 := by
  decide

theorem memPost_not_swapped :
    ¬ memPost (Outcome.ret (some (.int 8 1)) (storeMem storeInitR (.int 8) (.int 8 7) 1))
        (Outcome.ret (some (.int 8 1)) (storeMem storeInitL (.int 8) (.int 8 7) 1)) := by
  decide

/-- The two handled trees are related under that post: each side's final memory
is its own handler's, and a swapped binding is refused. -/
example : simtt memPost (handle checkFrame storeInitL storeSource)
    (handle checkFrame storeInitR storeSource) := by
  rw [handled_store_mem_left, handled_store_mem_right]
  refine (simtt_iff _ _ _).mpr ?_
  exact SimttF.ret_ret
    (v₁ := some (.int 8 1)) (mem₁ := storeMem storeInitL (.int 8) (.int 8 7) 1)
    (v₂ := some (.int 8 1)) (mem₂ := storeMem storeInitR (.int 8) (.int 8 7) 1)
    (SilentHead.step (SilentStep.step _) (SilentHead.refl _))
    (SilentHead.step (SilentStep.step _) (SilentHead.refl _))
    ⟨rfl, rfl⟩

/-! #### Visible calls: matching for every response, and callee/argument refusals

A call carries its response type through the relation, so the affirmative
quantifies over every `Option Value` response and the refusals change only the
callee or only the arguments. -/

abbrev callK : Option Value → OTree := fun _ => retNode

/-- The matching call: the same event, and every response's continuations
related. -/
example : simtt Eq
    (ITree.vis (ObsEv.call "sin" [.int 64 1]) callK)
    (ITree.vis (ObsEv.call "sin" [.int 64 1]) callK) := by
  refine (simtt_iff _ _ _).mpr ?_
  exact SimttF.vis_call "sin" [.int 64 1] callK callK
    (SilentHead.refl _) (SilentHead.refl _) (fun r => (simtt_ret_ret_iff _ _ _ _ _).mpr rfl)

/-- Only the callee differs: refused under the same detector. -/
example : ¬ simtt Eq
    (ITree.vis (ObsEv.call "sin" [.int 64 1]) callK)
    (ITree.vis (ObsEv.call "cos" [.int 64 1]) callK) :=
  not_simtt_call_ne Eq (Or.inl (by decide)) _ _

/-- Only the arguments differ: refused. -/
example : ¬ simtt Eq
    (ITree.vis (ObsEv.call "sin" [.int 64 1]) callK)
    (ITree.vis (ObsEv.call "sin" [.int 64 2]) callK) :=
  not_simtt_call_ne Eq (Or.inr (by decide)) _ _

/-! #### The loop instance and its transport

Under the new relation the fixture is two **handled** trees, and the loop's own
finite derivation is transported through the handler. -/

/-- The loop instance: the parsed loop's handled tree as target, the unrolled
candidate's handled tree as source, at the allocator-derived frame. -/
example (x : BitVec 64) : simtt (Outcome.AgreesOutside (loopFrame x))
    (runHandled noCalls (loopFrame x) 19 loopFunction (initState loopFunction [.int 64 x]))
    (runHandled noCalls (loopFrame x) 10000 candidateFunction
      (initState candidateFunction [.int 64 x])) :=
  loop_candidate_simtt x

/-- The bridge applied at the loop's own 19/10000 budgets: the loop's completed
return is answered by the candidate, and the postcondition is stated of the two
matched outcomes. -/
example (x : BitVec 64) (mem : Mem)
    (h19 : runFuel noCalls 19 loopFunction (initState loopFunction [.int 64 x]) =
      some (.ret (some (.int 64 (spec x))) mem)) :
    runFuel noCalls 10000 candidateFunction (initState candidateFunction [.int 64 x]) =
        some .ub ∨
      ∃ vT vS memT memS,
        Outcome.ret (some (.int 64 (spec x))) mem = .ret vT memT ∧
        runFuel noCalls 10000 candidateFunction (initState candidateFunction [.int 64 x]) =
          some (.ret vS memS) ∧
        (Outcome.ret vT memT).AgreesOutside (loopFrame x) (Outcome.ret vS memS) :=
  simtt_runFuel_some noCalls noCalls_pureEnv (loopFrame x)
    (Outcome.AgreesOutside (loopFrame x))
    loopFunction candidateFunction [.int 64 x] 19 10000
    (Outcome.ret (some (.int 64 (spec x))) mem) (loop_candidate_simtt x) h19

/-- The postcondition is not bypassed: with a post that holds of no pair, two
defined returns are not related. -/
example : ¬ simtt checkPostFalse retNode retNode := by
  intro h
  exact (simtt_ret_ret_iff checkPostFalse _ _ _ _).mp h

/-- The same postcondition rejects a return whose memory differs at address
zero, outside the frame. -/
example (x : BitVec 64) (v : Option Value) :
    ¬ (Outcome.ret v [(0, 1)]).AgreesOutside (loopFrame x) (Outcome.ret v []) :=
  outcome_address_zero_rejected x v

/-! #### The general loop rule and its first instance

`simtt_loop` is the framed, postcondition-indexed rule, and the tick tree is its
first instance: a visibly recurring call whose backedge is only reachable through
the rule's continuation position.  `simtt_post_mono` is the weakening that
recovers the loop fixture's original postcondition, and `handle_tau_guard` is the
handler's own positive jump delay. -/

/-- The rule's exact statement: the same invariant and delay relation in the
premise and in the coinduction seed. -/
example {σ τ : Type} (frame : Nat → Prop) (post : Outcome → Outcome → Prop)
    (left : σ → OTree) (right : τ → OTree) (Inv : σ → τ → Prop)
    (hstep : ∀ s t, Inv s t →
      TauSimttF (fun oT oS => post oT oS ∧ oT.AgreesOutside frame oS)
        (fun p q => ∃ s' t', Inv s' t' ∧ TauHead p (left s') ∧ TauHead q (right t'))
        (left s) (right t)) :
    ∀ s t, Inv s t →
      simtt (fun oT oS => post oT oS ∧ oT.AgreesOutside frame oS) (left s) (right t) :=
  simtt_loop frame post left right Inv hstep

/-- The rule's first instance: the visibly recurring tree at the rule's framed
`True` postcondition, for an arbitrary frame. -/
example (frame : Nat → Prop) :
    simtt (fun oT oS => True ∧ oT.AgreesOutside frame oS)
      (ITree.mfix tickStep ()) (ITree.mfix tickStep ()) :=
  tick_loop_simtt frame

/-- The same instance at the loop fixture's allocator-derived frame. -/
example (x : BitVec 64) :
    simtt (fun oT oS => True ∧ oT.AgreesOutside (loopFrame x) oS)
      (ITree.mfix tickStep ()) (ITree.mfix tickStep ()) :=
  tick_loop_simtt (loopFrame x)

/-- The recurring tree's backedge is guarded at the concrete step: the
continuation after the visible event is a positive finite delay of the next
step's tree, with its flattened form the continuation itself. -/
example :
    ∃ d : ITree.TauClosure OTree,
      ITree.TauClosure.FiniteLater d
        (ITree.bindStep tickStep (tickStep ())) ∧
        ITree.TauClosure.flatten d =
          ITree.bindStep tickStep (ITree.ret (.recur ())) :=
  ITree.mfix_bindStep_recur_guard tickStep ()

/-- The same detector refuses a differing callee at that boundary: the tick
loop's own call is `tick`, and its handled tree is not related to a `tock` node.
The `tau` in front is the loop's own initial step, stripped by the existing
left-`tau` transport. -/
example (frame : Nat → Prop) :
    ¬ simtt (fun oT oS => True ∧ oT.AgreesOutside frame oS)
      (ITree.tau (ITree.vis (ObsEv.call "tick" [])
        (fun _ => ITree.bindStep tickStep (ITree.ret (.recur ())))))
      (ITree.vis (ObsEv.call "tock" [])
        (fun _ => ITree.ret (Outcome.ret (some (.int 64 0)) []))) := by
  intro h
  exact not_simtt_call_ne _ (Or.inl (by decide)) _ _ (simtt_tau_left h)

/-- The refusal stated of the loop's tree itself: `mfix tickStep ()` is one `tau`
in front of its visible node, so the refusal applies to it unchanged. -/
example (frame : Nat → Prop) :
    ¬ simtt (fun oT oS => True ∧ oT.AgreesOutside frame oS)
      (ITree.mfix tickStep ())
      (ITree.vis (ObsEv.call "tock" [])
        (fun _ => ITree.ret (Outcome.ret (some (.int 64 0)) []))) := by
  have hmfix : ITree.mfix tickStep () =
      ITree.tau (ITree.vis (ObsEv.call "tick" [])
        (fun _ => ITree.bindStep tickStep (ITree.ret (.recur ())))) := by
    simp only [ITree.mfix_unfold, tickStep, ITree.bindStep_vis]
  rw [hmfix]
  intro h
  exact not_simtt_call_ne _ (Or.inl (by decide)) _ _ (simtt_tau_left h)

/-- Postcondition weakening recovers the fixture's original framed postcondition
from the rule's `True ∧ _` return relation. -/
example (frame : Nat → Prop) {p q : OTree}
    (h : simtt (fun oT oS => True ∧ oT.AgreesOutside frame oS) p q) :
    simtt (Outcome.AgreesOutside frame) p q :=
  simtt_post_mono (fun _ _ hh => hh.2) h

/-- A handled `tau` is one positive finite delay of the handled continuation,
flattening to the handled `tau`. -/
example (frame : Nat → Prop) (m : Mem) (t : ITree.Tree Ev Outcome) :
    ITree.TauClosure.FiniteLater
        (ITree.TauClosure.later (ITree.TauClosure.now (handle frame m t)))
        (handle frame m t) ∧
      ITree.TauClosure.flatten
        (ITree.TauClosure.later (ITree.TauClosure.now (handle frame m t))) =
        handle frame m (ITree.tau t) :=
  handle_tau_guard frame m t

/-- The exported decreasing-measure lemma at its stated signature. -/
example {frame : Nat → Prop} {σ : Type}
    (toRaw : σ → RawTS) (Inv : σ → Prop) (μ : σ → Nat) (P : RawTS → Prop)
    (hstep : ∀ s, Inv s → 0 < μ s →
      ∃ s', Inv s' ∧ μ s' < μ s ∧ RawSilentHead frame (toRaw s) (toRaw s'))
    (hexit : ∀ s, Inv s → μ s = 0 →
      ∃ terminal, P terminal ∧ RawSilentHead frame (toRaw s) terminal)
    {s₀ : σ} (h₀ : Inv s₀) :
    ∃ terminal, P terminal ∧ RawSilentHead frame (toRaw s₀) terminal :=
  rawSilentHead_of_measure toRaw Inv μ P hstep hexit h₀

/-- The loop fixture's condition seed reaches the return with the whole lane
prefix, through the measure lemma. -/
example (x : BitVec 64) (p : LoopSeed) (h : p.atCond x) :
    ∃ mem, MemConfined 1 17 mem ∧
      RawSilentHead (loopFrame x) p.toRaw
        (ITree.ret
          (Outcome.ret (some (.int 64 (maskPrefix (x ^^^ c 3182967604875373612) 8)))
            mem), mem) :=
  cond_run_silent x p h

/-- Every seed of the loop's family reaches the return silently, at the value the
candidate produces — the obligation the rule's return clause is discharged by. -/
example (x : BitVec 64) (p : LoopSeed) (h : LoopSeed.inv x p) :
    ∃ mem, MemPrivate (loopFrame x) mem ∧
      TauHead (LoopSeed.tree x p)
        (ITree.ret (Outcome.ret (some (.int 64 (spec x))) mem)) :=
  loopSeed_head x p h

/-- The rule at the loop's seed family, before the postcondition is weakened. -/
example (x : BitVec 64) :
    simtt (fun oT oS => True ∧ oT.AgreesOutside (loopFrame x) oS)
      (runHandled noCalls (loopFrame x) 19 loopFunction (initState loopFunction [.int 64 x]))
      (candidateHandled x) :=
  loop_seed_simtt x

/-! #### The correspondence and the axiom footprint -/

/-- The handled correspondence: the handler's memory is the semantics' memory,
so the canonical resolution of a `runHandled` tree is exactly `runFuel`. -/
example (frame : Nat → Prop) (n : Nat) (f : LeanLLVM.Function) (s : LeanLLVM.State) :
    HandledExec noCalls (runHandled noCalls frame n f s) (runFuel noCalls n f s) :=
  handled_runFuel noCalls noCalls_pureEnv frame n f s

/-- info: 'LeanLLVM.ITree.handled_runFuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.handled_runFuel

/-- info: 'LeanLLVM.ITree.handle_load_private' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.handle_load_private

/-- info: 'LeanLLVM.ITree.handle_store_visible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.handle_store_visible

/-- info: 'LeanLLVM.ITree.handle_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.handle_call

/-- info: 'handled_store_mem_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms handled_store_mem_left

/-- info: 'LeanLLVM.ITree.simtt_exec_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.simtt_exec_some

/-- info: 'LeanLLVM.ITree.simtt_runFuel_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.simtt_runFuel_some

/-- info: 'LeanLLVM.ITree.simtt_beh_inclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.simtt_beh_inclusion

/-- info: 'LeanLLVM.ITree.refinesWithin_of_simtt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.refinesWithin_of_simtt

/-- info: 'LeanLLVM.ITree.refines_of_simtt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.refines_of_simtt

/-- info: 'LeanLLVM.ITree.not_simtt_load_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.not_simtt_load_ne

/-- info: 'LeanLLVM.ITree.not_simtt_store_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.not_simtt_store_ne

/-- info: 'LeanLLVM.ITree.not_simtt_call_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.not_simtt_call_ne

/-- info: 'LeanLLVM.ITree.loop_candidate_simtt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.loop_candidate_simtt

/-- info: 'LeanLLVM.ITree.loop_candidate_beh_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.loop_candidate_beh_bridge

/-- info: 'LeanLLVM.ITree.simtt_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.simtt_loop

/-- info: 'LeanLLVM.ITree.simtt_post_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.simtt_post_mono

/-- info: 'LeanLLVM.ITree.tauSimttF_post_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauSimttF_post_mono

/-- info: 'LeanLLVM.ITree.handle_tau_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.handle_tau_guard

/-- info: 'LeanLLVM.ITree.rawSilentHead_of_measure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.rawSilentHead_of_measure

/-- info: 'LeanLLVM.ITree.tickStep_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tickStep_head

/-- info: 'LeanLLVM.ITree.tickStep_cont' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tickStep_cont

/-- info: 'LeanLLVM.ITree.tick_loop_simtt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tick_loop_simtt

/-- info: 'LeanLLVM.ITree.candidateTree_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.candidateTree_head

/-- info: 'LeanLLVM.ITree.loopTree_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.loopTree_head

/-- info: 'LeanLLVM.ITree.loopSeed_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.loopSeed_head

/-- info: 'LeanLLVM.ITree.memPrivate_of_confined' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.memPrivate_of_confined

/-- info: 'LeanLLVM.ITree.entryCondSeed_atCond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.entryCondSeed_atCond

/-- info: 'LeanLLVM.ITree.cond_run_silent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.cond_run_silent

/-- info: 'LeanLLVM.ITree.loopTree_silent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.loopTree_silent

/-- info: 'LeanLLVM.ITree.loop_seed_simtt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.loop_seed_simtt

/-- info: 'LeanLLVM.ITree.outcome_address_zero_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.outcome_address_zero_rejected

/-- info: 'LeanLLVM.ITree.simtt_ret_ret_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.simtt_ret_ret_iff

/-- info: 'LeanLLVM.ITree.SimttF_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.SimttF_monotone

/-- info: 'LeanLLVM.ITree.simtt_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.simtt_unfold

/-- info: 'LeanLLVM.ITree.infTau_diverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.infTau_diverges

/-- info: 'LeanLLVM.ITree.not_silentDiverges_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.not_silentDiverges_ret

/-- info: 'LeanLLVM.ITree.exec_runT' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.exec_runT

/-! ### The delay closure at the host relation

`TauClosure` indexes the same silent closures, and the checks below state the
equivalence in both directions on bound trees, the nine-clause equivalence of the
one-step functional, and the fixed-point identity — with the existing detector's
affirmatives and refusals observed through the delay-indexed unfolding.
-/

/-! #### The finite fragment -/

/-- Same trees, same finite silent closure, witnessed by a delay. -/
example (p q : OTree) : TauHead p q → SilentHead p q := fun h => tauHead_iff_silentHead.mp h

example (p q : OTree) : SilentHead p q → TauHead p q := fun h => tauHead_iff_silentHead.mpr h

/-- One `tau` is a finite delay; `infTau` is not a finite head of a return. -/
example : TauHead (ITree.tau retNode) retNode :=
  tauHead_of_silentHead (SilentHead.step (SilentStep.step _) (SilentHead.refl _))

example : ¬ TauHead ITree.infTau retNode := by
  intro h
  have he := SilentHead_infTau_self (tauHead_iff_silentHead.mp h)
  rw [ITree.infTau_eq] at he
  exact ITree.ret_ne_tau he

/-! #### The infinite fragment -/

/-- Same tree, same divergence. -/
example (p : OTree) : TauDiverges p ↔ SilentDiverges p := tauDiverges_iff_silentDiverges

/-- `infTau` diverges under the delay predicate; a return does not. -/
example : TauDiverges ITree.infTau :=
  tauDiverges_of_silentDiverges ITree.infTau_diverges

example : ¬ TauDiverges retNode := fun h => not_silentDiverges_ret (silentDiverges_of_tauDiverges h)

/-! #### Terminal reachability -/

example (p : OTree) : TauReachesUb p ↔ ReachesUb p := tauReachesUb_iff

example (p : OTree) : TauTimeoutReachable p ↔ TimeoutReachable p := tauTimeoutReachable_iff

/-- Positive and negative terminal controls under the delay predicate. -/
example : TauReachesUb ubNode := tauReachesUb_iff.mpr (reachesUb_of_terminal (UbTerminal.ubNode _))

example : ¬ TauReachesUb timeoutNode := fun h => not_reachesUb_timeout (tauReachesUb_iff.mp h)

example : TauTimeoutReachable timeoutNode :=
  tauTimeoutReachable_iff.mpr ⟨_, SilentHead.refl _, _, rfl⟩

example : ¬ TauTimeoutReachable ubNode := fun h => not_timeoutReachable_ub (tauTimeoutReachable_iff.mp h)

/-! #### The one-step functional, clause by clause -/

/-- The delay-indexed functional is the existing one on the same four operands. -/
example (post : Outcome → Outcome → Prop) (sim : OTree → OTree → Prop) (p q : OTree) :
    TauSimttF post sim p q ↔ SimttF post sim p q :=
  tauSimttF_iff post sim p q

/-- The existing relation is the greatest fixed point of the delay-indexed
functional, with its unfolding and coinduction. -/
example (post : Outcome → Outcome → Prop) :
    simtt post = plfp (TauSimttF post) (hm := TauSimttF_monotone_order post)
      (Lean.Order.top : OTree → OTree → Prop) :=
  simtt_eq_tau_plfp post

example (post : Outcome → Outcome → Prop) (p q : OTree) :
    simtt post p q ↔ TauSimttF post (simtt post) p q :=
  simtt_iff_tau post p q

#check @tauSimtt_coind

/-! #### The preserved classes, through the delay unfolding -/

/-- A right UB terminal still admits a completed left return, and the timeout/
UB and UB/timeout classes are still refused. -/
example : TauSimttF checkPostTrue (simtt checkPostTrue) retNode ubNode :=
  (simtt_iff_tau checkPostTrue retNode ubNode).mp (simtt_ret_ub checkPostTrue _)

example : ¬ TauSimttF checkPostTrue (simtt checkPostTrue) ubNode timeoutNode := by
  intro h
  exact not_simtt_ub_timeout checkPostTrue _ _
    ((simtt_iff_tau checkPostTrue ubNode timeoutNode).mpr h)

example : ¬ TauSimttF checkPostTrue (simtt checkPostTrue) timeoutNode ubNode := by
  intro h
  exact not_simtt_timeout_ub checkPostTrue _ _
    ((simtt_iff_tau checkPostTrue timeoutNode ubNode).mpr h)

/-- A left return is still not matched by a right timeout. -/
example : ¬ TauSimttF checkPostTrue (simtt checkPostTrue) retNode timeoutNode := by
  intro h
  exact not_simtt_ret_timeout checkPostTrue _ _
    ((simtt_iff_tau checkPostTrue retNode timeoutNode).mpr h)

/-- A visible load still matches only its own annotation. -/
example : ¬ TauSimttF checkPostTrue (simtt checkPostTrue)
    (ITree.vis (ObsEv.load 0 (.int 8) none) (fun () => retNode))
    (ITree.vis (ObsEv.load 0 (.int 8) (some (.int 8 1))) (fun () => retNode)) := by
  intro h
  exact not_simtt_load_ne checkPostTrue (by decide) _ _
    ((simtt_iff_tau checkPostTrue _ _).mpr h)

/-- A left divergence is related to a right return before binding. -/
example (o : Outcome) : simtt checkPostTrue ITree.infTau (ITree.ret o) :=
  simtt_diverges_ret checkPostTrue o

/-- The same positive under the delay unfolding. -/
example (o : Outcome) :
    TauSimttF checkPostTrue (simtt checkPostTrue) ITree.infTau (ITree.ret o) :=
  (simtt_iff_tau checkPostTrue ITree.infTau (ITree.ret o)).mp
    (simtt_diverges_ret checkPostTrue o)

/-- The bound pair is refused: the left divergence is preserved, but the right
return's continuation reaches a timeout, so the left-divergence clause's
`¬ TimeoutReachable` premise fails. -/
private theorem not_simtt_diverges_bind_timeout (o : Outcome) :
    ¬ simtt checkPostTrue
      (ITree.bind ITree.infTau (fun (_ : Outcome) => timeoutNode))
      (ITree.bind (ITree.ret o) (fun _ => timeoutNode)) := by
  rw [ITree.bind_ret]
  have hdiv : SilentDiverges (ITree.bind ITree.infTau (fun (_ : Outcome) => timeoutNode)) :=
    silentDiverges_of_tauDiverges
      (tauDiverges_bind (tauDiverges_of_silentDiverges ITree.infTau_diverges) _)
  rw [eq_infTau_of_silentDiverges hdiv]
  intro h
  have hF := (simtt_iff checkPostTrue _ _).mp h
  cases hF with
  | ret_ret h1 _ _ =>
      have e := SilentHead_infTau_self h1
      rw [ITree.infTau_eq] at e
      exact ITree.ret_ne_tau e
  | right_ub_ret h1 _ =>
      have e := SilentHead_infTau_self h1
      rw [ITree.infTau_eq] at e
      exact ITree.ret_ne_tau e
  | ub h1 _ => exact not_reachesUb_infTau h1
  | timeout k1 _ h1 _ =>
      have e := SilentHead_infTau_self h1
      rw [ITree.infTau_eq] at e
      exact (ITree.tau_ne_vis ObsEv.timeout k1).symm e
  | left_diverges _ hnt => exact hnt ⟨_, SilentHead.refl _, _, rfl⟩
  | right_diverges hdiv2 _ => exact not_silentDiverges_timeout hdiv2
  | vis_load addr ty r k1 _ h1 _ _ =>
      have e := SilentHead_infTau_self h1
      rw [ITree.infTau_eq] at e
      exact (ITree.tau_ne_vis (ObsEv.load addr ty r) k1).symm e
  | vis_store addr ty v k1 _ h1 _ _ =>
      have e := SilentHead_infTau_self h1
      rw [ITree.infTau_eq] at e
      exact (ITree.tau_ne_vis (ObsEv.store addr ty v) k1).symm e
  | vis_call callee args k1 _ h1 _ _ =>
      have e := SilentHead_infTau_self h1
      rw [ITree.infTau_eq] at e
      exact (ITree.tau_ne_vis (ObsEv.call callee args) k1).symm e

/-- The same pair after binding: the same `simtt` detector refuses the bound
pair. -/
example (o : Outcome) :
    ¬ simtt checkPostTrue
      (ITree.bind ITree.infTau (fun (_ : Outcome) => timeoutNode))
      (ITree.bind (ITree.ret o) (fun _ => timeoutNode)) :=
  not_simtt_diverges_bind_timeout o

/-- The same bound pair through the delay unfolding: the left divergence and the
right timeout are unchanged, so the left-divergence clause's premise fails there
too. -/
example (o : Outcome) :
    ¬ TauSimttF checkPostTrue (simtt checkPostTrue)
      (ITree.bind ITree.infTau (fun (_ : Outcome) => timeoutNode))
      (ITree.bind (ITree.ret o) (fun _ => timeoutNode)) := by
  intro h
  exact not_simtt_diverges_bind_timeout o
    ((simtt_iff_tau checkPostTrue _ _).mpr h)

/-- The right operand of that refused pair reaches a timeout: the return's
continuation applied at the bound outcome is a timeout node, which is the
premise the left-divergence clause requires to fail. -/
example (o : Outcome) :
    TimeoutReachable (ITree.bind (ITree.ret o) (fun _ => timeoutNode)) := by
  rw [ITree.bind_ret]
  exact ⟨_, SilentHead.refl _, _, rfl⟩

/-- The visible load triple under the delay unfolding: the equal annotation is
accepted on the same continuations, and the annotated-response change is
refused. -/
example : TauSimttF checkPostTrue (simtt checkPostTrue)
    (ITree.vis (ObsEv.load 0 (.int 8) none) (fun () => retNode))
    (ITree.vis (ObsEv.load 0 (.int 8) none) (fun () => retNode)) :=
  (simtt_iff_tau checkPostTrue _ _).mp (by
    refine (simtt_iff _ _ _).mpr ?_
    exact SimttF.vis_load 0 (.int 8) none _ _
      (SilentHead.refl _) (SilentHead.refl _) ((simtt_ret_ret_iff _ _ _ _ _).mpr trivial))

example : ¬ TauSimttF checkPostTrue (simtt checkPostTrue)
    (ITree.vis (ObsEv.load 0 (.int 8) none) (fun () => retNode))
    (ITree.vis (ObsEv.load 0 (.int 8) (some (.int 8 1))) (fun () => retNode)) := by
  intro h
  exact not_simtt_load_ne checkPostTrue (by decide) _ _
    ((simtt_iff_tau checkPostTrue _ _).mpr h)

/-- The visible store triple under the delay unfolding, on the same two
continuations the existing affirmative uses: the equal store is accepted, and the
address-only and value-only changes are refused. -/
example : TauSimttF checkPostTrue (simtt checkPostTrue)
    (ITree.vis (ObsEv.store 0 (.int 8) (.int 8 7)) storeKLeft)
    (ITree.vis (ObsEv.store 0 (.int 8) (.int 8 7)) storeKRight) :=
  (simtt_iff_tau checkPostTrue _ _).mp (by
    refine (simtt_iff _ _ _).mpr ?_
    exact SimttF.vis_store 0 (.int 8) (.int 8 7) _ _
      (SilentHead.refl _) (SilentHead.refl _) ((simtt_ret_ret_iff _ _ _ _ _).mpr trivial))

example : ¬ TauSimttF checkPostTrue (simtt checkPostTrue)
    (ITree.vis (ObsEv.store 0 (.int 8) (.int 8 7)) storeKLeft)
    (ITree.vis (ObsEv.store 1 (.int 8) (.int 8 7)) storeKRight) := by
  intro h
  exact not_simtt_store_ne checkPostTrue (by decide) _ _
    ((simtt_iff_tau checkPostTrue _ _).mpr h)

example : ¬ TauSimttF checkPostTrue (simtt checkPostTrue)
    (ITree.vis (ObsEv.store 0 (.int 8) (.int 8 7)) storeKLeft)
    (ITree.vis (ObsEv.store 0 (.int 8) (.int 8 8)) storeKRight) := by
  intro h
  exact not_simtt_store_ne checkPostTrue (by decide) _ _
    ((simtt_iff_tau checkPostTrue _ _).mpr h)

/-- The visible call triple under the delay unfolding on the same tree: the
matching call is accepted, and the callee-only and argument-only changes are
refused. -/
example : TauSimttF Eq (simtt Eq)
    (ITree.vis (ObsEv.call "sin" [.int 64 1]) callK)
    (ITree.vis (ObsEv.call "sin" [.int 64 1]) callK) :=
  (simtt_iff_tau Eq _ _).mp (by
    refine (simtt_iff _ _ _).mpr ?_
    exact SimttF.vis_call "sin" [.int 64 1] callK callK
      (SilentHead.refl _) (SilentHead.refl _)
      (fun r => (simtt_ret_ret_iff _ _ _ _ _).mpr rfl))

example : ¬ TauSimttF Eq (simtt Eq)
    (ITree.vis (ObsEv.call "sin" [.int 64 1]) callK)
    (ITree.vis (ObsEv.call "cos" [.int 64 1]) callK) := by
  intro h
  exact not_simtt_call_ne Eq (Or.inl (by decide)) _ _ ((simtt_iff_tau Eq _ _).mpr h)

example : ¬ TauSimttF Eq (simtt Eq)
    (ITree.vis (ObsEv.call "sin" [.int 64 1]) callK)
    (ITree.vis (ObsEv.call "sin" [.int 64 2]) callK) := by
  intro h
  exact not_simtt_call_ne Eq (Or.inr (by decide)) _ _ ((simtt_iff_tau Eq _ _).mpr h)

/-- The framed-return pair under the delay unfolding: the same two returns are
accepted at the permissive post and refused at the post that holds of no pair,
so the refusal is the postcondition, not the detector. -/
example : TauSimttF checkPostTrue (simtt checkPostTrue) retNode retNode :=
  (simtt_iff_tau checkPostTrue _ _).mp ((simtt_ret_ret_iff checkPostTrue _ _ _ _).mpr trivial)

example : ¬ TauSimttF checkPostFalse (simtt checkPostFalse) retNode retNode := by
  intro h
  exact (simtt_ret_ret_iff checkPostFalse _ _ _ _).mp
    ((simtt_iff_tau checkPostFalse _ _).mpr h)

/-! ### Congruence under `bind`

The positive theorem with its compatibility hypotheses, and two refusals whose
source pair *is* related.  Binding `simtt checkPostTrue (ret o) ubNode` with a
left continuation that reaches a timeout leaves the right side the bound
`ubNode`, so the result is a timeout against a UB terminal; binding
`simtt checkPostTrue (ret o) (ret o)` with a right continuation that reaches a
timeout gives a return against a timeout.  The same `simtt` detector refuses
each, and each refusal is paired with the witness that its timeout operand
reaches a timeout.
-/

/-- A continuation that reaches UB at `.ub` and returns otherwise. -/
def bindCont : Outcome → OTree
  | .ret v m => ITree.ret (Outcome.ret v m)
  | .ub => ubNode

/-- The positive congruence: `post`-related returns, a left continuation that
silently completes, both `.ub` continuations reaching UB, and no right
continuation reaching a timeout. -/
example :
    simtt (fun _ _ => True)
      (ITree.bind retNode bindCont) (ITree.bind retNode bindCont) := by
  apply simtt_bind
      (post := fun _ _ => True) (post' := fun _ _ => True)
      (f := bindCont) (g := bindCont)
      (p := retNode) (q := retNode)
  · exact (simtt_ret_ret_iff _ _ _ _ _).mpr (by trivial)
  · intro v mem v' mem' _
    exact (simtt_ret_ret_iff _ _ _ _ _).mpr (by trivial)
  · intro o
    cases o with
    | ret v m => exact Or.inl ⟨_, SilentHead.refl _⟩
    | ub => exact Or.inr (reachesUb_of_terminal (UbTerminal.ubNode _))
  · exact reachesUb_of_terminal (UbTerminal.ubNode _)
  · exact reachesUb_of_terminal (UbTerminal.ubNode _)
  · intro v mem
    exact not_timeoutReachable_ret

/-- The refusal hypothesis (iv) prevents: with the **right** continuation
reaching a timeout and the left continuation completing at a return, the bound
pair is a left return against a timeout node, which the same detector refuses. -/
example (o : Outcome) :
    ¬ simtt checkPostTrue
      (ITree.bind (ITree.ret o) (fun _ => ITree.ret (Outcome.ret (some (.int 64 0)) [])))
      (ITree.bind (ITree.ret o) (fun _ => timeoutNode)) := by
  rw [ITree.bind_ret, ITree.bind_ret]
  exact not_simtt_ret_timeout checkPostTrue _ _

/-- The right operand of that refused pair reaches a timeout, which is exactly
hypothesis (iv) of the positive theorem. -/
example (o : Outcome) :
    TimeoutReachable (ITree.bind (ITree.ret o) (fun _ => timeoutNode)) := by
  rw [ITree.bind_ret]
  exact ⟨_, SilentHead.refl _, _, rfl⟩

/-- The pair bound on the right by the UB node is related before binding: a
completed left return against a right UB terminal. -/
example (o : Outcome) : simtt checkPostTrue (ITree.ret o) ubNode :=
  simtt_ret_ub checkPostTrue o

/-- Binding that pair with a left continuation that reaches a timeout leaves the
right side the bound `ubNode`, so the result is a timeout against a UB terminal
and the same detector refuses it. -/
example (o : Outcome) :
    ¬ simtt checkPostTrue
      (ITree.bind (ITree.ret o) (fun _ => timeoutNode))
      (ITree.bind ubNode bindCont) := by
  rw [ITree.bind_ret, ITree.bind_vis]
  exact not_simtt_timeout_ub checkPostTrue Empty.elim _

/-- The left operand of that refused pair reaches a timeout: the continuation
applied at the bound return is a timeout node, which is the operand that turns
the bound pair into a timeout against UB. -/
example (o : Outcome) :
    TimeoutReachable ((fun _ => timeoutNode) o) :=
  ⟨_, SilentHead.refl _, _, rfl⟩

/-! ### Congruence under a re-emitting interpreter -/

/-- The identity-trigger handler: it re-emits every event unchanged, with no
delay. -/
def reemitHandler : ITree.EffectAlgebra.Handler ObsEv ObsEv :=
  fun {_} e => ITree.trigger e

theorem reemitHandler_reemits : Reemits reemitHandler :=
  fun _ => ⟨0, rfl⟩

/-- A same-signature handler that maps the UB terminal to a budget timeout and
otherwise re-emits the event. -/
def badHandler : ITree.EffectAlgebra.Handler ObsEv ObsEv :=
  fun {_} e =>
    match e with
    | .ub => ITree.vis ObsEv.timeout Empty.elim
    | .load addr ty r => ITree.trigger (ObsEv.load addr ty r)
    | .store addr ty v => ITree.trigger (ObsEv.store addr ty v)
    | .call callee args => ITree.trigger (ObsEv.call callee args)
    | .timeout => ITree.trigger ObsEv.timeout

/-- A defined return is related to a right UB terminal. -/
example (o : Outcome) : simtt Eq (ITree.ret o) ubNode :=
  simtt_ret_ub Eq o

/-- The re-emitting interpreter preserves that pair. -/
example (o : Outcome) :
    simtt Eq (ITree.EffectAlgebra.interp reemitHandler (ITree.ret o))
      (ITree.EffectAlgebra.interp reemitHandler ubNode) :=
  simtt_interp reemitHandler_reemits (simtt_ret_ub Eq o)

/-- A handler that re-emits the identical event behind one silent step is still
positive: the nonzero delay is allowed by the premise. -/
def delayedHandler : ITree.EffectAlgebra.Handler ObsEv ObsEv :=
  fun {_} e => ITree.tauN 1 (ITree.trigger e)

theorem delayedHandler_reemits : Reemits delayedHandler := fun _ => ⟨1, rfl⟩

example (o : Outcome) :
    simtt Eq (ITree.EffectAlgebra.interp delayedHandler (ITree.ret o))
      (ITree.EffectAlgebra.interp delayedHandler ubNode) :=
  simtt_interp delayedHandler_reemits (simtt_ret_ub Eq o)

/-- The non-preserving handler does not: the left side stays a return and the
right side is a visible timeout, which the same detector refuses. -/
example (o : Outcome) :
    ¬ simtt Eq (ITree.EffectAlgebra.interp badHandler (ITree.ret o))
      (ITree.EffectAlgebra.interp badHandler ubNode) := by
  rw [ITree.EffectAlgebra.interp_ret]
  rw [ITree.EffectAlgebra.interp_vis,
    show badHandler ObsEv.ub = ITree.vis ObsEv.timeout Empty.elim from rfl,
    ITree.bind_vis]
  exact not_simtt_ret_timeout Eq o _

/-! #### The new host theorems' axiom footprint

Each is pinned at the footprint it was observed to have: the same three axioms
`Simtt.lean`'s own theorems carry.  That `Classical.choice` has **two** sources,
and the pin does not distinguish them: the generic tree carrier inherits it from
mathlib's `PFunctor.M` destructor (present before any host proof), while the host
handler adds its own `Classical.propDecidable` decision on the arbitrary-`Prop`
frame.  The ceiling is the carrier's floor plus the frame decision; it is not
evidence that a host proof decided a proposition. -/

/-- info: 'LeanLLVM.ITree.tauHead_iff_silentHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauHead_iff_silentHead

/-- info: 'LeanLLVM.ITree.tauDiverges_iff_silentDiverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauDiverges_iff_silentDiverges

/-- info: 'LeanLLVM.ITree.tauReachesUb_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauReachesUb_iff

/-- info: 'LeanLLVM.ITree.tauTimeoutReachable_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauTimeoutReachable_iff

/-- info: 'LeanLLVM.ITree.tauSimttF_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauSimttF_iff

/-- info: 'LeanLLVM.ITree.simtt_eq_tau_plfp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.simtt_eq_tau_plfp

/-- info: 'LeanLLVM.ITree.simtt_iff_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.simtt_iff_tau

/-- info: 'LeanLLVM.ITree.tauSimtt_coind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauSimtt_coind

/-- info: 'LeanLLVM.ITree.simtt_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.simtt_bind

/-- info: 'LeanLLVM.ITree.simtt_interp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.simtt_interp

/-- info: 'LeanLLVM.ITree.simtt_ieq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.simtt_ieq

/-- info: 'LeanLLVM.ITree.simtt_tau_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.simtt_tau_tau

/-! #### The delay transports behind the two congruences

Each transport is pinned at its own observed footprint, which is the carrier's
floor: composing, binding, interpreting or inverting a finite or infinite delay
introduces no decision of its own, and the `Classical.choice` visible here is
the one mathlib's `PFunctor.M` destructor already carries. -/

/-- info: 'LeanLLVM.ITree.tauHead_refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauHead_refl

/-- info: 'LeanLLVM.ITree.tauHead_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauHead_step

/-- info: 'LeanLLVM.ITree.tauHead_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauHead_trans

/-- info: 'LeanLLVM.ITree.tauHead_tauN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauHead_tauN

/-- info: 'LeanLLVM.ITree.tauHead_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauHead_bind

/-- info: 'LeanLLVM.ITree.tauDiverges_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauDiverges_bind

/-- info: 'LeanLLVM.ITree.tauDiverges_of_tauHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauDiverges_of_tauHead

/-- info: 'LeanLLVM.ITree.tauReachesUb_of_tauHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauReachesUb_of_tauHead

/-- info: 'LeanLLVM.ITree.tauTimeoutReachable_of_tauHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauTimeoutReachable_of_tauHead

/-- info: 'LeanLLVM.ITree.not_tauTimeoutReachable_of_tauHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.not_tauTimeoutReachable_of_tauHead

/-- info: 'LeanLLVM.ITree.tauHead_bind_of_tauN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauHead_bind_of_tauN

/-- info: 'LeanLLVM.ITree.tauHead_bind_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauHead_bind_inv

/-- info: 'LeanLLVM.ITree.tauTimeoutReachable_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauTimeoutReachable_bind

/-- info: 'LeanLLVM.ITree.tauReachesUb_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauReachesUb_bind

/-- info: 'LeanLLVM.ITree.tauSimttF_of_tauHead_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauSimttF_of_tauHead_left

/-- info: 'LeanLLVM.ITree.tauSimttF_of_tauHead_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauSimttF_of_tauHead_right

/-- info: 'LeanLLVM.ITree.tauSimttF_ret_ret_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauSimttF_ret_ret_bind

/-- info: 'LeanLLVM.ITree.tauSimttF_right_ub_ret_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauSimttF_right_ub_ret_bind

/-- info: 'LeanLLVM.ITree.tauSimttF_bind_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauSimttF_bind_lift

/-- info: 'LeanLLVM.ITree.interp_tauN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.interp_tauN

/-- info: 'LeanLLVM.ITree.interp_infTau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.interp_infTau

/-- info: 'LeanLLVM.ITree.tauHead_interp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauHead_interp

/-- info: 'LeanLLVM.ITree.tauReachesUb_interp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauReachesUb_interp

/-- info: 'LeanLLVM.ITree.tauTimeoutReachable_interp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauTimeoutReachable_interp

/-- info: 'LeanLLVM.ITree.tauDiverges_interp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauDiverges_interp

/-- info: 'LeanLLVM.ITree.tauTimeoutReachable_interp_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauTimeoutReachable_interp_reflect

/-! #### The host delay normal form and its terminal bridge

The delay normal form is pinned at its observed footprint.  The three
constructor-level lemmas that never destruct a tree — `tauN_tau`,
`silentHead_tauN` and `exists_tauN_of_silentHead` — carry `propext` only, as
the generic delay lemmas do; the rest carry the carrier's floor plus the host
handler's frame decision. -/

/-- info: 'LeanLLVM.ITree.tauN_tau' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauN_tau

/-- info: 'LeanLLVM.ITree.silentHead_tauN' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.silentHead_tauN

/-- info: 'LeanLLVM.ITree.exists_tauN_of_silentHead' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.exists_tauN_of_silentHead

/-- info: 'LeanLLVM.ITree.silentHead_of_tauHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.silentHead_of_tauHead

/-- info: 'LeanLLVM.ITree.tauHead_of_silentHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauHead_of_silentHead

/-- info: 'LeanLLVM.ITree.eq_infTau_of_silentDiverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.eq_infTau_of_silentDiverges

/-- info: 'LeanLLVM.ITree.silentDiverges_of_tauDiverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.silentDiverges_of_tauDiverges

/-- info: 'LeanLLVM.ITree.tauDiverges_of_silentDiverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauDiverges_of_silentDiverges

/-- info: 'LeanLLVM.ITree.TauSimttF_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.TauSimttF_monotone

/-- info: 'LeanLLVM.ITree.TauSimttF_monotone_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.TauSimttF_monotone_order

/-- info: 'LeanLLVM.ITree.tauSimttF_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauSimttF_eq

/-! #### The terminal exclusion and the interpreter-point helpers

The two terminal-class proofs and the reflection helpers behind the interpreter
congruence, each pinned at its observed footprint. -/

/-- info: 'LeanLLVM.ITree.tauN_terminal_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.tauN_terminal_inj

/-- info: 'LeanLLVM.ITree.not_reachesUb_of_timeoutReachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.not_reachesUb_of_timeoutReachable

/-- info: 'LeanLLVM.ITree.bind_tauN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.bind_tauN

/-- info: 'LeanLLVM.ITree.interp_vis_tauN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.interp_vis_tauN

/-- info: 'LeanLLVM.ITree.interpStep_interpPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.interpStep_interpPoint

/-- info: 'LeanLLVM.ITree.interpDelayStep_interpPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.interpDelayStep_interpPoint

/-- info: 'LeanLLVM.ITree.interpPoint_of_silentHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.interpPoint_of_silentHead

/-- info: 'LeanLLVM.ITree.interp_vis_timeout_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.interp_vis_timeout_shape

/-- info: 'LeanLLVM.ITree.timeoutReachable_interp_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.timeoutReachable_interp_reflect

/-! ### The JSON seam

`LeanLLVM/Vellum/JsonSeam.lean`: the reference selection, the installed
candidate's selection, the staging caller, and the contextual replacement.  The
headline theorems are restated as statement pins, so weakening one fails to
elaborate even when its footprint is unchanged, and the observed axiom footprint
is pinned beside it.  The negative control's footprint is a pin: the refusal is
a theorem, not a scenario.

`Classical.choice` in the four seam theorems' footprints is inherited, not
entailed: `zip_replicate_right` → `classify32_block` → `classify32_step` carries
it from core's `Nat.right_eq_add`, whose `by omega` proof applies
`Classical.propDecidable` to `b = a + b` and `a = 0` — both `Nat.decEq`-decidable.
It is a core tactic artefact, not an arbitrary-`Prop` frame, and not
`bv_decide`. -/

/-- info: 'LeanLLVM.Vellum.JsonSeam.classifySeam_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonSeam.classifySeam_refines

/-- info: 'LeanLLVM.Vellum.JsonSeam.replaceScanner_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonSeam.replaceScanner_sound

/-- info: 'LeanLLVM.Vellum.JsonSeam.replaceScanner_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonSeam.replaceScanner_ret

/-- info: 'LeanLLVM.Vellum.JsonSeam.wrongMask_not_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonSeam.wrongMask_not_refines

/-- info: 'LeanLLVM.Vellum.JsonSeam.envForBodySym_comma' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonSeam.envForBodySym_comma

open LeanLLVM.Vellum.JsonSeam in
example : ∀ sym, LeanLLVM.CallRefinesWithin
    (envForBodySym jsonSeamSymbol 10000 0 LeanLLVM.Vellum.JsonClassifyIR.classify32Function)
    envForMask sym (LeanLLVM.ReserveFrame 0) :=
  classifySeam_refines

open LeanLLVM.Vellum.JsonSeam in
example : LeanLLVM.Vellum.RefinesWithinAcross
    (envForBodySym jsonSeamSymbol 10000 0 LeanLLVM.Vellum.JsonClassifyIR.classify32Function)
    envForMask scanCaller scanCaller (fun _ => False) :=
  replaceScanner_sound

open LeanLLVM.Vellum.JsonSeam in
example (w0 w1 w2 w3 : BitVec 64) :
    ∀ o, LeanLLVM.Beh
        (envForBodySym jsonSeamSymbol 10000 0 LeanLLVM.Vellum.JsonClassifyIR.classify32Function)
        scanCaller [.int 64 w0, .int 64 w1, .int 64 w2, .int 64 w3] o ↔
      o = .ret (some (.int 32 (LeanLLVM.JSON.maskOfList (blockOf w0 w1 w2 w3))))
        (stagedMem w0 w1 w2 w3) :=
  replaceScanner_ret w0 w1 w2 w3

open LeanLLVM.Vellum.JsonSeam in
example : ¬ LeanLLVM.CallRefinesWithin
    (envForBodySym jsonSeamSymbol 10000 0 LeanLLVM.Vellum.JsonClassifyIR.wrongMaskFunction)
    envForMask jsonSeamSymbol (LeanLLVM.ReserveFrame 0) :=
  wrongMask_not_refines

open LeanLLVM.Vellum.JsonSeam in
example (fuel reserve : Nat) (f : LeanLLVM.Function) :
    envForBodySym LeanLLVM.Vellum.SeamContext.seamSymbol fuel reserve f =
      LeanLLVM.Vellum.SeamContext.envForBody fuel reserve f :=
  envForBodySym_comma fuel reserve f

/-! ### The scanner window's ABI

`LeanLLVM/Vellum/JsonScanABI.lean`: the state slot and status word encodings,
the two round trips, the five-bit lane field's collision, the ABI's symbol, and
`docs/contract.md` §5 as a record with the window's instance.  Each theorem is
restated beside its pin, and every contract field is read by name so a field
removed from the record fails elaboration here rather than passing silently. -/

/-- info: 'LeanLLVM.Vellum.JsonScanABI.encodeFlags_inside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanABI.encodeFlags_inside

open LeanLLVM.Vellum.JsonScanABI in
example (st : LeanLLVM.JSON.BodyState) : (encodeFlags st).getLsbD 0 = st.inside :=
  encodeFlags_inside st

/-- info: 'LeanLLVM.Vellum.JsonScanABI.encodeFlags_oddRun' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanABI.encodeFlags_oddRun

open LeanLLVM.Vellum.JsonScanABI in
example (st : LeanLLVM.JSON.BodyState) : (encodeFlags st).getLsbD 1 = st.oddRun :=
  encodeFlags_oddRun st

/-- info: 'LeanLLVM.Vellum.JsonScanABI.byteOf_ofNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanABI.byteOf_ofNat

open LeanLLVM.Vellum.JsonScanABI in
example (b : UInt8) : byteOf (BitVec.ofNat 32 b.toNat) = b :=
  byteOf_ofNat b

/-- info: 'LeanLLVM.Vellum.JsonScanABI.decodeState_encodeState' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanABI.decodeState_encodeState

open LeanLLVM.Vellum.JsonScanABI in
example {st : LeanLLVM.JSON.BodyState} (h : st.WellFormed) :
    decodeState (encodeState st) = st :=
  decodeState_encodeState h

/-- info: 'LeanLLVM.Vellum.JsonScanABI.reasonOfCode_reasonCode' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanABI.reasonOfCode_reasonCode

open LeanLLVM.Vellum.JsonScanABI in
example (s : LeanLLVM.JSON.BodyStop) : reasonOfCode (reasonCode s) = s :=
  reasonOfCode_reasonCode s

/-- info: 'LeanLLVM.Vellum.JsonScanABI.reasonCode_reasonOfCode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanABI.reasonCode_reasonOfCode

open LeanLLVM.Vellum.JsonScanABI in
example {r : Nat} (h0 : 0 < r) (h3 : r < 4) : reasonCode (reasonOfCode r) = r :=
  reasonCode_reasonOfCode h0 h3

/-- info: 'LeanLLVM.Vellum.JsonScanABI.encodeStatusNat_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanABI.encodeStatusNat_lt

open LeanLLVM.Vellum.JsonScanABI in
example {s : Status} (h : s.LanesInWindow) : encodeStatusNat s < 2 ^ 32 :=
  encodeStatusNat_lt h

/-- info: 'LeanLLVM.Vellum.JsonScanABI.ofNat32_toNat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanABI.ofNat32_toNat

open LeanLLVM.Vellum.JsonScanABI in
example {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n :=
  ofNat32_toNat h

/-- info: 'LeanLLVM.Vellum.JsonScanABI.decodeStatusNat_encodeStatusNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanABI.decodeStatusNat_encodeStatusNat

open LeanLLVM.Vellum.JsonScanABI in
example (s : Status) (h : s.LanesInWindow) :
    decodeStatusNat (encodeStatusNat s) = s :=
  decodeStatusNat_encodeStatusNat s h

/-- info: 'LeanLLVM.Vellum.JsonScanABI.decodeStatus_encodeStatus' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanABI.decodeStatus_encodeStatus

open LeanLLVM.Vellum.JsonScanABI in
example (s : Status) (h : s.LanesInWindow) : decodeStatus (encodeStatus s) = s :=
  decodeStatus_encodeStatus s h

/-- info: 'LeanLLVM.Vellum.JsonScanABI.encodeStatusNat_decodeStatusNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanABI.encodeStatusNat_decodeStatusNat

open LeanLLVM.Vellum.JsonScanABI in
example (n : Nat) (h : Status.InImage n) :
    encodeStatusNat (decodeStatusNat n) = n :=
  encodeStatusNat_decodeStatusNat n h

/-- info: 'LeanLLVM.Vellum.JsonScanABI.decodeStatusNat_lanesInWindow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanABI.decodeStatusNat_lanesInWindow

open LeanLLVM.Vellum.JsonScanABI in
example {n : Nat} (h : Status.InImage n) : (decodeStatusNat n).LanesInWindow :=
  decodeStatusNat_lanesInWindow h

/-- info: 'LeanLLVM.Vellum.JsonScanABI.encodeStatusNat_inImage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanABI.encodeStatusNat_inImage

open LeanLLVM.Vellum.JsonScanABI in
example {s : Status} (h : s.LanesInWindow) : Status.InImage (encodeStatusNat s) :=
  encodeStatusNat_inImage h

/-- info: 'LeanLLVM.Vellum.JsonScanABI.status_inImage_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanABI.status_inImage_iff

open LeanLLVM.Vellum.JsonScanABI in
example (n : Nat) :
    Status.InImage n ↔ ∃ s : Status, s.LanesInWindow ∧ encodeStatusNat s = n :=
  status_inImage_iff n

/-- info: 'LeanLLVM.Vellum.JsonScanABI.encodeStatus_decodeStatus' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanABI.encodeStatus_decodeStatus

open LeanLLVM.Vellum.JsonScanABI in
example (w : BitVec 32) (h : Status.InImage w.toNat) :
    encodeStatus (decodeStatus w) = w :=
  encodeStatus_decodeStatus w h

/-- info: 'LeanLLVM.Vellum.JsonScanABI.laneFieldFive_lane31_collides' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanABI.laneFieldFive_lane31_collides

open LeanLLVM.Vellum.JsonScanABI in
example : laneFieldFive (some 31) = laneFieldFive none :=
  laneFieldFive_lane31_collides

/-- info: 'LeanLLVM.Vellum.JsonScanABI.lane31_fiveBit_wraps' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanABI.lane31_fiveBit_wraps

open LeanLLVM.Vellum.JsonScanABI in
example : (31 + 1) % 32 = 0 ∧ laneFieldSix (some 31) ≠ laneFieldSix none :=
  lane31_fiveBit_wraps

/-- info: 'LeanLLVM.Vellum.JsonScanABI.closeAt31_stop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanABI.closeAt31_stop

open LeanLLVM.Vellum.JsonScanABI LeanLLVM.JSON in
example : (windowOf closeAt31 BodyState.body).stop = some (.close 31) :=
  closeAt31_stop

/-- info: 'LeanLLVM.Vellum.JsonScanABI.controlAt31_stop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanABI.controlAt31_stop

open LeanLLVM.Vellum.JsonScanABI LeanLLVM.JSON in
example :
    (windowOf controlAt31 BodyState.body).stop = some (.refuse 31 .control) :=
  controlAt31_stop

/-- info: 'LeanLLVM.Vellum.JsonScanABI.close31_roundTrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanABI.close31_roundTrip

open LeanLLVM.Vellum.JsonScanABI LeanLLVM.JSON in
example :
    decodeStatus (encodeStatus (.ok ((windowOf closeAt31 BodyState.body).stop))) =
      .ok ((windowOf closeAt31 BodyState.body).stop) :=
  close31_roundTrip

/-- info: 'LeanLLVM.Vellum.JsonScanABI.refuse31_roundTrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanABI.refuse31_roundTrip

open LeanLLVM.Vellum.JsonScanABI LeanLLVM.JSON in
example :
    decodeStatus (encodeStatus (.ok ((windowOf controlAt31 BodyState.body).stop))) =
      .ok ((windowOf controlAt31 BodyState.body).stop) :=
  refuse31_roundTrip

-- The ABI's sizes and symbol.
open LeanLLVM.Vellum.JsonScanABI in
example : stateBytes = 16 := rfl

open LeanLLVM.Vellum.JsonScanABI in
example : outBytes = 4 := rfl

open LeanLLVM.Vellum.JsonScanABI in
example : readExtent = 32 := rfl

open LeanLLVM.Vellum.JsonScanABI in
example : scanSymbol = "leanllvm_json_scan_window" := rfl

-- `jsonScanContract`'s §5 fields, each read by name: a field removed from the
-- record fails to elaborate here rather than passing silently.
open LeanLLVM.Vellum.JsonScanABI in
example : jsonScanContract.readBytes_ = 32 := rfl

open LeanLLVM.Vellum.JsonScanABI in
example : jsonScanContract.outBytes = 4 := rfl

open LeanLLVM.Vellum.JsonScanABI in
example : jsonScanContract.stateBytes = 16 := rfl

open LeanLLVM.Vellum.JsonScanABI in
example (m m' : LeanLLVM.Mem) (in_ out state valid : Nat) :
    jsonScanContract.footprint m m' in_ out state valid ↔
      scanFootprint m m' in_ out state valid :=
  Iff.rfl

open LeanLLVM.Vellum.JsonScanABI in
example (in_ out state valid : Nat) :
    jsonScanContract.slotDisjoint in_ out state valid ↔
      scanSlotDisjoint in_ out state valid :=
  Iff.rfl

open LeanLLVM.Vellum.JsonScanABI in
example : jsonScanContract.ownedByCaller := trivial

open LeanLLVM.Vellum.JsonScanABI in
example (in_ out state : Nat) :
    jsonScanContract.lifetimes in_ out state ↔ scanLifetimes in_ out state :=
  Iff.rfl

open LeanLLVM.Vellum.JsonScanABI in
example : jsonScanContract.alignmentFree := trivial

open LeanLLVM.Vellum.JsonScanABI in
example : jsonScanContract.noIndexArithmetic := trivial

open LeanLLVM.Vellum.JsonScanABI in
example : ¬ jsonScanContract.capacityExhausted := by
  intro h
  exact h

/-! ### The model-side selection (P3)

The slot's readback, the selection's statement with its stopped cases, and the
whole-scan post-memory.  Each theorem is pinned with its footprint and restated
beside it. -/

/-- info: 'LeanLLVM.Vellum.JsonScanModel.slotAt_writeSlot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanModel.slotAt_writeSlot

open LeanLLVM.Vellum.JsonScanModel LeanLLVM.Vellum.JsonScanABI LeanLLVM.JSON LeanLLVM in
example (m : Mem) (p : Nat) {st : BodyState} (h : st.WellFormed) :
    slotAt (writeSlot m p (encodeState st)) p = some st :=
  slotAt_writeSlot m p h

/-- info: 'LeanLLVM.Vellum.JsonScanModel.slotAt_writeMask' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanModel.slotAt_writeMask

open LeanLLVM.Vellum.JsonScanModel LeanLLVM in
example (m : Mem) (pOut pState : Nat) (w : BitVec 32) (h : pOut + 4 ≤ pState) :
    slotAt (writeMask m pOut w) pState = slotAt m pState :=
  slotAt_writeMask m pOut pState w h

/-- info: 'LeanLLVM.Vellum.JsonScanModel.envForScanWindow_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanModel.envForScanWindow_spec

open LeanLLVM.Vellum.JsonScanModel LeanLLVM.Vellum.JsonScanABI LeanLLVM.JSON LeanLLVM in
example (st : BodyState) (bs : List UInt8) (mem : Mem) (pIn pOut pState valid : Nat)
    (hvalid : valid ≤ 32) (hread : readBytes mem pIn valid = some bs)
    (hslot : slotAt mem pState = some st) (next : Nat) :
    envForScanWindow scanSymbol
        [.ptr pIn, .ptr pOut, .ptr pState, .int 32 (BitVec.ofNat 32 valid)] mem next =
      some { ret := .int 32 (encodeStatus (Status.ok (stopOf bs st))),
             mem := writeSlot (writeMask mem pOut (maskOfList bs)) pState
                      (encodeState (carryAt bs st (stopLaneOrLength bs st))),
             next := next } :=
  envForScanWindow_spec st bs mem pIn pOut pState valid hvalid hread hslot next

/-- info: 'LeanLLVM.Vellum.JsonScanModel.envForScanWindow_spec_close' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanModel.envForScanWindow_spec_close

open LeanLLVM.Vellum.JsonScanModel LeanLLVM.Vellum.JsonScanABI LeanLLVM.JSON LeanLLVM in
example (st : BodyState) (bs : List UInt8) (mem : Mem) (pIn pOut pState valid k : Nat)
    (hvalid : valid ≤ 32) (hread : readBytes mem pIn valid = some bs)
    (hslot : slotAt mem pState = some st) (hstop : stopOf bs st = some (.close k))
    (next : Nat) :
    envForScanWindow scanSymbol
        [.ptr pIn, .ptr pOut, .ptr pState, .int 32 (BitVec.ofNat 32 valid)] mem next =
      some { ret := .int 32 (encodeStatus (Status.ok (some (.close k)))),
             mem := writeSlot (writeMask mem pOut (maskOfList bs)) pState
                      (encodeState (carryAt bs st k)),
             next := next } :=
  envForScanWindow_spec_close st bs mem pIn pOut pState valid k hvalid hread hslot
    hstop next

/-- info: 'LeanLLVM.Vellum.JsonScanModel.envForScanWindow_spec_refuse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanModel.envForScanWindow_spec_refuse

open LeanLLVM.Vellum.JsonScanModel LeanLLVM.Vellum.JsonScanABI LeanLLVM.JSON LeanLLVM in
example (st : BodyState) (bs : List UInt8) (mem : Mem) (pIn pOut pState valid k : Nat)
    (reason : BodyStop) (hvalid : valid ≤ 32)
    (hread : readBytes mem pIn valid = some bs) (hslot : slotAt mem pState = some st)
    (hstop : stopOf bs st = some (.refuse k reason)) (next : Nat) :
    envForScanWindow scanSymbol
        [.ptr pIn, .ptr pOut, .ptr pState, .int 32 (BitVec.ofNat 32 valid)] mem next =
      some { ret := .int 32 (encodeStatus (Status.ok (some (.refuse k reason)))),
             mem := writeSlot (writeMask mem pOut (maskOfList bs)) pState
                      (encodeState (carryAt bs st k)),
             next := next } :=
  envForScanWindow_spec_refuse st bs mem pIn pOut pState valid k reason hvalid hread
    hslot hstop next

/-- info: 'LeanLLVM.Vellum.JsonScanModel.envForScanWindow_spec_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanModel.envForScanWindow_spec_full

open LeanLLVM.Vellum.JsonScanModel LeanLLVM.Vellum.JsonScanABI LeanLLVM.JSON LeanLLVM in
example (st : BodyState) (bs : List UInt8) (mem : Mem) (pIn pOut pState valid : Nat)
    (hvalid : valid ≤ 32) (hread : readBytes mem pIn valid = some bs)
    (hslot : slotAt mem pState = some st) (hstop : stopOf bs st = none)
    (hlen : bs.length = 32) (next : Nat) :
    envForScanWindow scanSymbol
        [.ptr pIn, .ptr pOut, .ptr pState, .int 32 (BitVec.ofNat 32 valid)] mem next =
      some { ret := .int 32 (encodeStatus (Status.ok none)),
             mem := writeSlot (writeMask mem pOut (maskOfList bs)) pState
                      (encodeState ((windowOf bs st).carry)),
             next := next } :=
  envForScanWindow_spec_full st bs mem pIn pOut pState valid hvalid hread hslot hstop
    hlen next

/-- info: 'LeanLLVM.Vellum.JsonScanModel.envForScanWindow_refuses_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanModel.envForScanWindow_refuses_valid

open LeanLLVM.Vellum.JsonScanModel LeanLLVM.Vellum.JsonScanABI LeanLLVM.JSON LeanLLVM in
example (mem : Mem) (pIn pOut pState : Nat) (v : BitVec 32) (next : Nat)
    (hlarge : readExtent < v.toNat) :
    envForScanWindow scanSymbol
        [.ptr pIn, .ptr pOut, .ptr pState, .int 32 v] mem next = none :=
  envForScanWindow_refuses_valid mem pIn pOut pState v next hlarge

-- The out-of-domain witness, discriminating: the buffer really holds the forty
-- bytes (35 `a`, the closing quote, four more `a`), so a `valid = 40` read would
-- succeed and the extent guard is the only reason the call does not resolve.
-- The same memory with `valid = 32` does resolve and reports no stop, because the
-- first thirty-two bytes contain no quote.
def witnessRange : List UInt8 := List.replicate 35 0x61 ++ [0x22] ++ List.replicate 4 0x61

def witnessMem : LeanLLVM.Mem :=
  LeanLLVM.Vellum.JsonScanModel.writeSlot
    (LeanLLVM.writeBytes [] 0 witnessRange) 64
    (LeanLLVM.Vellum.JsonScanABI.encodeState LeanLLVM.JSON.BodyState.body)

set_option maxRecDepth 10000 in
open LeanLLVM.Vellum.JsonScanModel LeanLLVM.Vellum.JsonScanABI LeanLLVM.JSON LeanLLVM in
example :
    readBytes witnessMem 0 40 = some witnessRange ∧
    envForScanWindow scanSymbol [.ptr 0, .ptr 100, .ptr 64, .int 32 40] witnessMem 1 = none ∧
    envForScanWindow scanSymbol
        [.ptr 0, .ptr 100, .ptr 64, .int 32 (BitVec.ofNat 32 32)] witnessMem 1 =
      some { ret := .int 32 0,
             mem := writeSlot (writeMask witnessMem 100 0) 64
                      (encodeState BodyState.body),
             next := 1 } := by
  refine ⟨by decide,
    envForScanWindow_refuses_valid witnessMem 0 100 64 40 1 (by decide), ?_⟩
  rw [envForScanWindow_spec BodyState.body (List.replicate 32 0x61) witnessMem 0 100 64 32
    (by decide) (by decide) (by
      simp only [witnessMem]
      exact slotAt_writeSlot (writeBytes [] 0 witnessRange) 64 BodyState.body_wellFormed) 1]
  have hstopF : stopOf (List.replicate 32 0x61) BodyState.body = none := by decide
  have hmaskF : maskOfList (List.replicate 32 0x61) = (0 : BitVec 32) := by decide
  have hcarryF : carryAt (List.replicate 32 0x61) BodyState.body
      (stopLaneOrLength (List.replicate 32 0x61) BodyState.body) = BodyState.body := by
    decide
  have hstatus : encodeStatus (Status.ok none) = (0 : BitVec 32) := by decide
  rw [hstopF, hmaskF, hcarryF, hstatus]

/-- info: 'LeanLLVM.Vellum.JsonScanModel.stoppedWindow_stop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanModel.stoppedWindow_stop

open LeanLLVM.Vellum.JsonScanModel LeanLLVM.JSON in
example : stopOf stoppedWindow BodyState.body = some (.close 0) :=
  stoppedWindow_stop

/-- info: 'LeanLLVM.Vellum.JsonScanModel.stoppedWindow_prefix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanModel.stoppedWindow_prefix

open LeanLLVM.Vellum.JsonScanModel LeanLLVM.JSON in
example : carryAt stoppedWindow BodyState.body 0 = BodyState.body :=
  stoppedWindow_prefix

/-- info: 'LeanLLVM.Vellum.JsonScanModel.stoppedWindow_carry_diverges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanModel.stoppedWindow_carry_diverges

open LeanLLVM.Vellum.JsonScanModel LeanLLVM.JSON in
example :
    (windowOf stoppedWindow BodyState.body).carry ≠
      carryAt stoppedWindow BodyState.body 0 :=
  stoppedWindow_carry_diverges

/-- info: 'LeanLLVM.Vellum.JsonScanModel.stoppedWindow_fold_carry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanModel.stoppedWindow_fold_carry

open LeanLLVM.Vellum.JsonScanModel LeanLLVM.JSON in
example :
    (windowOf stoppedWindow BodyState.body).carry = ⟨true, true, Utf8Need.none⟩ :=
  stoppedWindow_fold_carry

-- The stopped window read through the selection, on a real memory: the window's
-- two bytes at `%in = 0`, the slot seeded with the body's state at `%state = 64`.
-- The returned status closes at lane 0 and the slot receives the prefix carry
-- `carryAt stoppedWindow BodyState.body 0`, which is the body's state.
def stoppedWindowMem : LeanLLVM.Mem :=
  LeanLLVM.Vellum.JsonScanModel.writeSlot
    (LeanLLVM.writeBytes [] 0 LeanLLVM.Vellum.JsonScanModel.stoppedWindow) 64
    (LeanLLVM.Vellum.JsonScanABI.encodeState LeanLLVM.JSON.BodyState.body)

open LeanLLVM.Vellum.JsonScanModel LeanLLVM.Vellum.JsonScanABI LeanLLVM.JSON LeanLLVM in
example :
    envForScanWindow scanSymbol [.ptr 0, .ptr 32, .ptr 64, .int 32 (BitVec.ofNat 32 2)]
        stoppedWindowMem 0 =
      some { ret := .int 32 (encodeStatus (Status.ok (some (.close 0)))),
             mem := writeSlot (writeMask stoppedWindowMem 32 (maskOfList stoppedWindow)) 64
                      (encodeState (carryAt stoppedWindow BodyState.body 0)),
             next := 0 } := by
  apply envForScanWindow_spec_close BodyState.body stoppedWindow stoppedWindowMem 0 32 64 2 0
    (by decide) (by decide) ?_ stoppedWindow_stop 0
  simp only [stoppedWindowMem]
  exact slotAt_writeSlot (writeBytes [] 0 stoppedWindow) 64 BodyState.body_wellFormed

/-- info: 'LeanLLVM.Vellum.JsonScanModel.carryAt_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanModel.carryAt_succ

open LeanLLVM.Vellum.JsonScanModel LeanLLVM.JSON LeanLLVM in
example (bs : List UInt8) (st : BodyState) (k : Nat) :
    carryAt bs st (k + 1) =
      (match bs[k]? with
       | some b =>
           (match bodyStep (carryAt bs st k) b with
            | .cont st' => st'
            | _ => carryAt bs st k)
       | none => carryAt bs st k) :=
  carryAt_succ bs st k

/-- info: 'LeanLLVM.Vellum.JsonScanModel.carryAt_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanModel.carryAt_wellFormed

open LeanLLVM.Vellum.JsonScanModel LeanLLVM.JSON in
example {bs : List UInt8} {st : BodyState} (h : st.WellFormed) (k : Nat) :
    (carryAt bs st k).WellFormed :=
  carryAt_wellFormed h k

/-- info: 'LeanLLVM.Vellum.JsonScanModel.carryAt_of_length_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanModel.carryAt_of_length_le

open LeanLLVM.Vellum.JsonScanModel LeanLLVM.JSON in
example {bs : List UInt8} {st : BodyState} {k : Nat} (h : bs.length ≤ k) :
    carryAt bs st k = carryAt bs st bs.length :=
  carryAt_of_length_le h

/-- info: 'LeanLLVM.Vellum.JsonScanModel.windowOf_carry_of_short' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanModel.windowOf_carry_of_short

open LeanLLVM.Vellum.JsonScanModel LeanLLVM.JSON in
example {bs : List UInt8} {st : BodyState} (hlen : bs.length < 32) :
    (windowOf bs st).carry = carryAt bs st bs.length :=
  windowOf_carry_of_short hlen

/-- info: 'LeanLLVM.Vellum.JsonScanModel.carryAt_stopLaneOrLength_eq_carry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanModel.carryAt_stopLaneOrLength_eq_carry

open LeanLLVM.Vellum.JsonScanModel LeanLLVM.JSON in
example {bs : List UInt8} {st : BodyState} (hlen : bs.length ≤ 32)
    (hstop : stopOf bs st = none) :
    carryAt bs st (stopLaneOrLength bs st) = (windowOf bs st).carry :=
  carryAt_stopLaneOrLength_eq_carry hlen hstop

/-- info: 'LeanLLVM.Vellum.JsonScanModel.windowBytes_length_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanModel.windowBytes_length_le

open LeanLLVM.Vellum.JsonScanModel LeanLLVM.JSON LeanLLVM in
example (bs : Bytes) (i : Nat) : (windowBytes bs i).length ≤ 32 :=
  windowBytes_length_le bs i

/-- info: 'LeanLLVM.Vellum.JsonScanModel.memModelCarry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanModel.memModelCarry

open LeanLLVM.Vellum.JsonScanModel LeanLLVM.JSON LeanLLVM in
example (bs : Bytes) (i : Nat) (st : BodyState) : memModelCarry bs 0 i st = st := rfl

/-- info: 'LeanLLVM.Vellum.JsonScanModel.memModelSteps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanModel.memModelSteps

open LeanLLVM.Vellum.JsonScanModel LeanLLVM.JSON LeanLLVM in
example (bs : Bytes) (i : Nat) (st : BodyState) : memModelSteps bs 0 i st = 0 := rfl

-- The count is one mask per visited window: one for a one-byte body plus its
-- quote, two for forty body bytes plus the quote (a full window and the tail).
set_option maxRecDepth 10000 in
open LeanLLVM.Vellum.JsonScanModel LeanLLVM.JSON LeanLLVM in
example : memModelSteps (ByteString.literal [0x22, 0x61, 0x22]) 4 1 BodyState.body = 1 := by
  decide

set_option maxRecDepth 10000 in
open LeanLLVM.Vellum.JsonScanModel LeanLLVM.JSON LeanLLVM in
example :
    memModelSteps (ByteString.literal ([0x22] ++ List.replicate 40 0x61 ++ [0x22])) 42 1
      BodyState.body = 2 := by
  decide

/-- info: 'LeanLLVM.Vellum.JsonScanModel.memModelGo_slot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanModel.memModelGo_slot

open LeanLLVM.Vellum.JsonScanModel LeanLLVM.JSON LeanLLVM in
example (bs : Bytes) (pOut pState : Nat) :
    ∀ (fuel i k : Nat) (st : BodyState) (mem : Mem),
      st.WellFormed →
      pOut + 4 * (k + memModelSteps bs fuel i st) ≤ pState →
      slotAt mem pState = some st →
      slotAt (memModelGo bs pOut pState fuel i k st mem) pState =
        some (memModelCarry bs fuel i st) :=
  memModelGo_slot bs pOut pState

/-- info: 'LeanLLVM.Vellum.JsonScanModel.memModel_slot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanModel.memModel_slot

open LeanLLVM.Vellum.JsonScanModel LeanLLVM.JSON LeanLLVM in
example (bs : Bytes) (q : Nat) (mem : Mem) (pOut pState : Nat)
    (hbound : pOut + 4 * memModelSteps bs (bs.size + 1) (q + 1) BodyState.body ≤ pState)
    (hslot : slotAt mem pState = some BodyState.body) :
    slotAt (memModel bs q mem pOut pState) pState =
      some (memModelCarry bs (bs.size + 1) (q + 1) BodyState.body) :=
  memModel_slot bs q mem pOut pState hbound hslot

-- The final slot on a concrete scan: a one-byte body plus its quote is one
-- window, and the slot ends holding the prefix carry's encoding.
open LeanLLVM.Vellum.JsonScanModel LeanLLVM.Vellum.JsonScanABI LeanLLVM.JSON LeanLLVM in
example :
    slotAt (memModel (ByteString.literal [0x22, 0x61, 0x22]) 0
        (writeSlot [] 64 (encodeState BodyState.body)) 32 64) 64 =
      some BodyState.body := by
  decide

-- The same scan through the invariant, with both hypotheses discharged rather
-- than assumed: the mask store at 32 ends below the slot at 64, and the seeded
-- slot reads back as the body's state.
open LeanLLVM.Vellum.JsonScanModel LeanLLVM.Vellum.JsonScanABI LeanLLVM.JSON LeanLLVM in
example :
    slotAt (memModel (ByteString.literal [0x22, 0x61, 0x22]) 0
        (writeSlot [] 64 (encodeState BodyState.body)) 32 64) 64 =
      some (memModelCarry (ByteString.literal [0x22, 0x61, 0x22]) 4 1 BodyState.body) :=
  memModel_slot _ 0 _ 32 64 (by decide)
    (slotAt_writeSlot [] 64 BodyState.body_wellFormed)

/-- info: 'LeanLLVM.Vellum.JsonScanModel.memModel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanModel.memModel

/-- info: 'LeanLLVM.Vellum.JsonScanModel.memModel_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanModel.memModel_eq

open LeanLLVM.Vellum.JsonScanModel LeanLLVM.JSON LeanLLVM in
example (bs : Bytes) (q : Nat) (mem : Mem) (pOut pState : Nat) :
    memModel bs q mem pOut pState =
      memModelGo bs pOut pState (bs.size + 1) (q + 1) 0 BodyState.body mem :=
  memModel_eq bs q mem pOut pState

-- A body with no bytes at all leaves memory untouched.
open LeanLLVM.Vellum.JsonScanModel LeanLLVM.JSON LeanLLVM in
example : memModel (ByteString.literal [0x22]) 0 [] 100 200 = [] := rfl

-- A one-byte body followed by its closing quote is one window that stops at
-- lane 1: the mask is the window's, and the slot holds the prefix carry before
-- the quote — the body's own state.
open LeanLLVM.Vellum.JsonScanModel LeanLLVM.Vellum.JsonScanABI LeanLLVM.JSON LeanLLVM in
example :
    memModel (ByteString.literal [0x22, 0x61, 0x22]) 0 [] 100 200 =
      writeSlot (writeMask [] 100 (maskOfList [0x61, 0x22])) 200
        (encodeState BodyState.body) := by
  decide

-- Forty body bytes and the closing quote: a full no-stop window at `%out`, then
-- the nine-byte tail at `%out + 4`, which stops at lane 8.  A 32-lane fold is
-- deeper than `decide`'s default recursion depth, so the limit is raised here
-- and only here.
set_option maxRecDepth 10000 in
open LeanLLVM.Vellum.JsonScanModel LeanLLVM.Vellum.JsonScanABI LeanLLVM.JSON LeanLLVM in
example :
    memModel (ByteString.literal ([0x22] ++ List.replicate 40 0x61 ++ [0x22])) 0
        [] 100 200 =
      writeSlot
        (writeMask
          (writeSlot (writeMask [] 100 (maskOfList (List.replicate 32 0x61))) 200
            (encodeState BodyState.body))
          104 (maskOfList (List.replicate 8 0x61 ++ [0x22])))
        200 (encodeState BodyState.body) := by
  decide

/-! ### The JSON window scanner's authored body

`LeanLLVM/Vellum/JsonScanIR.lean` pins `probes/install/ir/json-scan-body.ll` to
`LeanLLVM.Vellum.JsonScanBody.scanWindowBody` with a `#guard`, so the fixture and
the AST are one object at build time.  The module proves the prefix facts the
refinement statement rests on — the mask, the stop and the carry at a window's
first `k` lanes — and the statements below are those theorems, restated and
pinned.  Every theorem in that module is pinned here.  The refinement theorem
itself is outstanding and is recorded as such in that module's header, so
nothing here pins it.
-/

/--
info: 'LeanLLVM.Vellum.JsonScanIR.maskPref_eq_maskOfList' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanIR.maskPref_eq_maskOfList

/--
info: 'LeanLLVM.Vellum.JsonScanIR.firstStop_eq_stopOf' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanIR.firstStop_eq_stopOf

/--
info: 'LeanLLVM.Vellum.JsonScanIR.carriedAt_eq_carryAt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanIR.carriedAt_eq_carryAt

/--
info: 'LeanLLVM.Vellum.JsonScanIR.carriedAt_succ_cont' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanIR.carriedAt_succ_cont

/--
info: 'LeanLLVM.Vellum.JsonScanIR.carriedAt_succ_stop' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanIR.carriedAt_succ_stop

-- The prefix internals the identifications above are proved from, pinned for
-- the same reason as the conclusions: a nonstandard axiom here reaches the
-- mask, the stop and the carry statements by way of their proofs.

/--
info: 'LeanLLVM.Vellum.JsonScanIR.zipIdx_take_getElem?' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanIR.zipIdx_take_getElem?

/--
info: 'LeanLLVM.Vellum.JsonScanIR.ofNat_one_shiftLeft' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanIR.ofNat_one_shiftLeft

/--
info: 'LeanLLVM.Vellum.JsonScanIR.maskPref_succ' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanIR.maskPref_succ

/--
info: 'LeanLLVM.Vellum.JsonScanIR.maskPref_eq_laneFold' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanIR.maskPref_eq_laneFold

/--
info: 'LeanLLVM.Vellum.JsonScanIR.firstStop_succ' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanIR.firstStop_succ

/--
info: 'LeanLLVM.Vellum.JsonScanIR.firstStop_eq_none' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanIR.firstStop_eq_none

/--
info: 'LeanLLVM.Vellum.JsonScanIR.firstStop_eq_some' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanIR.firstStop_eq_some

-- The mask the accumulator holds at the end of a full window is the classifier's
-- own `maskOfList`, which is what the unit writes at `%out`.
open LeanLLVM.JSON in
example (bs : List UInt8) (h : bs.length ≤ 32) :
    LeanLLVM.Vellum.JsonScanIR.maskPref bs bs.length = maskOfList bs :=
  LeanLLVM.Vellum.JsonScanIR.maskPref_eq_maskOfList bs h

-- The stop word the body leaves is the window fold's first stop.
example (bs : List UInt8) (st : LeanLLVM.JSON.BodyState) (h : bs.length ≤ 32) :
    LeanLLVM.Vellum.JsonScanIR.firstStop bs st bs.length =
      LeanLLVM.Vellum.JsonScanModel.stopOf bs st :=
  LeanLLVM.Vellum.JsonScanIR.firstStop_eq_stopOf h

-- The carry the slot holds is the model's prefix carry at the stop's lane, or at
-- the window's length when nothing stopped.
example (bs : List UInt8) (st : LeanLLVM.JSON.BodyState) (h : bs.length ≤ 32) :
    LeanLLVM.Vellum.JsonScanIR.carriedAt bs st bs.length =
      LeanLLVM.JSON.carryAt bs st (LeanLLVM.Vellum.JsonScanModel.stopLaneOrLength bs st) :=
  LeanLLVM.Vellum.JsonScanIR.carriedAt_eq_carryAt h

-- A lane that continues advances the carry, and one that stops holds it.
example (bs : List UInt8) (st st' : LeanLLVM.JSON.BodyState) (k : Nat) (b : UInt8)
    (hstop : LeanLLVM.Vellum.JsonScanIR.firstStop bs st k = none)
    (hb : bs[k]? = some b)
    (hstep : LeanLLVM.JSON.bodyStep (LeanLLVM.JSON.carryAt bs st k) b = .cont st') :
    LeanLLVM.Vellum.JsonScanIR.carriedAt bs st (k + 1) = st' :=
  LeanLLVM.Vellum.JsonScanIR.carriedAt_succ_cont hstop hb hstep

example (bs : List UInt8) (st : LeanLLVM.JSON.BodyState) (k : Nat) (b : UInt8)
    (hstop : LeanLLVM.Vellum.JsonScanIR.firstStop bs st k = none)
    (hb : bs[k]? = some b)
    (hne : ∀ st', LeanLLVM.JSON.bodyStep (LeanLLVM.JSON.carryAt bs st k) b ≠ .cont st') :
    LeanLLVM.Vellum.JsonScanIR.carriedAt bs st (k + 1) =
      LeanLLVM.Vellum.JsonScanIR.carriedAt bs st k :=
  LeanLLVM.Vellum.JsonScanIR.carriedAt_succ_stop hstop hb hne

-- The prefix fold is split at its last lane: the lane the fold's list has at
-- `k` is the byte and its own index, for `k` inside a window.
example (bs : List UInt8) {k : Nat} (hk : k < 32) :
    (bs.zipIdx.take 32)[k]? = (bs[k]?).map (fun b => (b, k)) :=
  LeanLLVM.Vellum.JsonScanIR.zipIdx_take_getElem? bs hk

-- The emitted one read back as a word: a shift of the lane index is a shift of
-- `BitVec 32`'s own one, for a lane inside the window.
example (k : Nat) (hk : k < 32) :
    BitVec.ofNat 32 (1 <<< k) = ((1 : BitVec 32) <<< k) :=
  LeanLLVM.Vellum.JsonScanIR.ofNat_one_shiftLeft k hk

-- One lane of the prefix mask, as the recursion's own equation.
open LeanLLVM.JSON in
example (bs : List UInt8) (k : Nat) :
    LeanLLVM.Vellum.JsonScanIR.maskPref bs (k + 1) =
      (match bs[k]? with
       | some b =>
           if IsStructOrSpaceB b then
             LeanLLVM.Vellum.JsonScanIR.maskPref bs k ||| ((1 : BitVec 32) <<< k)
           else LeanLLVM.Vellum.JsonScanIR.maskPref bs k
       | none => LeanLLVM.Vellum.JsonScanIR.maskPref bs k) :=
  LeanLLVM.Vellum.JsonScanIR.maskPref_succ bs k

-- The prefix mask is the model's `Nat` fold over the window list, truncated at
-- the prefix.
example (bs : List UInt8) (k : Nat) (hk : k ≤ 32) :
    LeanLLVM.Vellum.JsonScanIR.maskPref bs k =
      BitVec.ofNat 32 (LeanLLVM.Vellum.JsonScanIR.laneFold bs k) :=
  LeanLLVM.Vellum.JsonScanIR.maskPref_eq_laneFold bs k hk

-- One lane of the stop prefix, as the recursion's own equation.
example (bs : List UInt8) (st : LeanLLVM.JSON.BodyState) (k : Nat) :
    LeanLLVM.Vellum.JsonScanIR.firstStop bs st (k + 1) =
      (match LeanLLVM.Vellum.JsonScanIR.firstStop bs st k with
       | some s => some s
       | none => LeanLLVM.Vellum.JsonScanIR.laneStop bs st k) :=
  LeanLLVM.Vellum.JsonScanIR.firstStop_succ bs st k

-- No lane before `k` raises a stop, so the prefix records none.
open LeanLLVM.JSON in
example (bs : List UInt8) (st : BodyState) (k : Nat)
    (h : ∀ j, j < k → ∀ (b : UInt8), bs[j]? = some b →
      ∃ st', bodyStep (carryAt bs st j) b = .cont st') :
    LeanLLVM.Vellum.JsonScanIR.firstStop bs st k = none :=
  LeanLLVM.Vellum.JsonScanIR.firstStop_eq_none (bs := bs) (st := st) (k := k) h

-- A lane that raises a stop fixes the prefix's answer from there on.
open LeanLLVM.JSON in
example (bs : List UInt8) (st : BodyState) (k : Nat)
    (hcont : ∀ j, j < k → ∀ (b : UInt8), bs[j]? = some b →
      ∃ st', bodyStep (carryAt bs st j) b = .cont st')
    (stop : Stop) (hlane : LeanLLVM.Vellum.JsonScanIR.laneStop bs st k = some stop)
    (n : Nat) (hn : k < n) :
    LeanLLVM.Vellum.JsonScanIR.firstStop bs st n = some stop :=
  LeanLLVM.Vellum.JsonScanIR.firstStop_eq_some (bs := bs) (st := st) (k := k)
    hcont (stop := stop) hlane (n := n) hn

/-! ### The JSON window scanner's lane machinery

`LeanLLVM/Vellum/JsonScanLane.lean` holds the lane machinery's first two facts.
`structBit` runs the body's own nine table instructions through the semantics,
and `structBit_correct` says the bit they leave is `IsStructOrSpaceB` on every
byte — the table's correctness is a theorem, where nothing in the kernel had
connected its arithmetic to the predicate.  `maskStep` then accumulates that
bit: one lane's `shl`/`or` leaves the model's `maskPref` fold.  The rest of the
instruction chain, `laneStep`, the loop induction and `scanWindowLLVM_refines`
are outstanding; that module's header records the measured per-lane count and
the generator the chain is to come from.
-/

-- The table prefix is the body's own nine instructions, named here so that a
-- change to `ruleInstrs`'s head fails this pin rather than silently shifting
-- what `structBit_correct` is about.
open LeanLLVM.Vellum.JsonScanBody in
example :
    LeanLLVM.Vellum.JsonScanLane.structBitCode =
      [ .zext "%b64" 8 64 (.reg "%b"),
        .binop "%bt" .and 64 (.reg "%b64") (lit64 63),
        .icmp "%g64" .ult 8 (.reg "%b") (lit8 64),
        .icmp "%g128" .ult 8 (.reg "%b") (lit8 128),
        .select "%t0" (LeanLLVM.Ty.int 64) (.reg "%g128") (lit64 structHi) (lit64 0),
        .select "%t1" (LeanLLVM.Ty.int 64) (.reg "%g64") (lit64 structLo) (.reg "%t0"),
        .binop "%sh" .lshr 64 (.reg "%t1") (.reg "%bt"),
        .binop "%sb1" .and 64 (.reg "%sh") (lit64 1),
        .icmp "%stb" .ne 64 (.reg "%sb1") (lit64 0)] := rfl

/--
info: 'LeanLLVM.Vellum.JsonScanLane.structBit_correct' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanLane.structBit_correct

-- The table's answer on a byte is the model's predicate on that byte: the bridge
-- the mask accumulator consumes, and the one an instruction-level lane proof
-- reaches for instead of restating the table's arithmetic.
open LeanLLVM.JSON in
example (b : UInt8) : LeanLLVM.Vellum.JsonScanLane.structBit b = IsStructOrSpaceB b :=
  LeanLLVM.Vellum.JsonScanLane.structBit_correct b

/--
info: 'LeanLLVM.Vellum.JsonScanLane.maskStep' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanLane.maskStep

-- One lane's accumulated `or` is the model's prefix fold — the clause the ruling
-- asks the body to satisfy.  The lane's bit is the table chain's answer, and the
-- equality with `IsStructOrSpaceB` is supplied by `structBit_correct`, not
-- assumed by the caller.
open LeanLLVM.JSON in
example (bs : List UInt8) (m : BitVec 32) (k : Nat) (b : UInt8)
    (hk : k < 32) (hb : bs[k]? = some b)
    (hm : m = LeanLLVM.Vellum.JsonScanIR.maskPref bs k) :
    (if LeanLLVM.Vellum.JsonScanLane.structBit b = true then
        m ||| ((1 : BitVec 32) <<< k) else m) =
      LeanLLVM.Vellum.JsonScanIR.maskPref bs (k + 1) :=
  LeanLLVM.Vellum.JsonScanLane.maskStep bs m k b hk hb hm

/-! ### The JSON classifier's specification

`LeanLLVM/Vellum/JsonScanSpec.lean` writes down the classifier's interface — the
quote, escaped-quote, delimiter, backslash, in-string and candidate masks over a
window, the packing to words, and the sixty-four-lane form the kernel stores —
in the model's own vocabulary, and proves the bridges to `ScanBlock.lean`'s fold,
its predicates and `ScanBody.bodyStep`'s `inside` field.  Its docstring records
the specification decision — the candidate mask's quote component counts
**unescaped** quotes only — and records what is still owed: the identification
with `windowOf`/`carryAt` and the relation to the emitted kernel's registers.

Each theorem's axiom footprint is pinned here, and each is restated as an
`example` over the public interface.
-/

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Vellum.JsonScanSpec

-- The model's structural set is the classifier's three components.
example (b : UInt8) :
    IsStructuralB b = (IsDelimB b || IsQuoteB b || IsBackslashB b) :=
  isStructuralB_eq b

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.isStructuralB_eq' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.isStructuralB_eq

-- The scalar transition's set is those three plus whitespace.
example (b : UInt8) :
    IsStructOrSpaceB b = (IsDelimB b || IsQuoteB b || IsBackslashB b || IsSpaceB b) :=
  isStructOrSpaceB_eq b

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.isStructOrSpaceB_eq' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.isStructOrSpaceB_eq

-- The packed word is `maskOfListWith` at the block's lanes, definitionally.
example (f : UInt8 → Bool) (blk : Block32) :
    pack32 f blk = maskOfListWith f (List.ofFn blk) :=
  pack32_eq_maskOfListWith f blk

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.pack32_eq_maskOfListWith' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.pack32_eq_maskOfListWith

-- The block layer's `maskOf` is the packing at the scalar transition.
example (blk : Block32) : pack32 IsStructOrSpaceB blk = maskOf blk :=
  pack32_eq_maskOf blk

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.pack32_eq_maskOf' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.pack32_eq_maskOf

-- Bit `k` of a packed word is the decision on lane `k`.
example (f : UInt8 → Bool) (blk : Block32) (k : Fin 32) :
    (pack32 f blk).getLsbD k.val = f (blk k) :=
  pack32_getLsbD f blk k

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.pack32_getLsbD' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.pack32_getLsbD

-- The packed word is the bitcast of the lane vector.
example (f : UInt8 → Bool) (blk : Block32) :
    pack32 f blk =
      BitVec.ofNat 32
        (lanesToNat (List.ofFn (fun k : Fin 32 => BitVec.ofBool (f (blk k))))) :=
  pack32_eq_bitcast f blk

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.pack32_eq_bitcast' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.pack32_eq_bitcast

-- The join's low word is the low lane's word.
example (lo hi : BitVec 32) {k : Nat} (hk : k < 32) :
    (mask64 lo hi).getLsbD k = lo.getLsbD k :=
  mask64_getLsbD_lo lo hi hk

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.mask64_getLsbD_lo' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.mask64_getLsbD_lo

-- The join's high word is the high lane's word.
example (lo hi : BitVec 32) {k : Nat} (hk : k < 32) :
    (mask64 lo hi).getLsbD (k + 32) = hi.getLsbD k :=
  mask64_getLsbD_hi lo hi hk

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.mask64_getLsbD_hi' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.mask64_getLsbD_hi

-- The sixty-four-lane mask's low half.
example (f : UInt8 → Bool) (lo hi : Block32) {k : Nat} (hk : k < 32) :
    (specMask64 f lo hi).getLsbD k = f (lo ⟨k, hk⟩) :=
  specMask64_getLsbD_lo f lo hi hk

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.specMask64_getLsbD_lo' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.specMask64_getLsbD_lo

-- The sixty-four-lane mask's high half.
example (f : UInt8 → Bool) (lo hi : Block32) {k : Nat} (hk : k < 32) :
    (specMask64 f lo hi).getLsbD (k + 32) = f (hi ⟨k, hk⟩) :=
  specMask64_getLsbD_hi f lo hi hk

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.specMask64_getLsbD_hi' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.specMask64_getLsbD_hi

-- The carry advances one lane at a time.
example (bs : List UInt8) (st : ClassState) (k : Nat) :
    classCarryAt bs st (k + 1) =
      (match bs[k]? with
       | some b => classStep (classCarryAt bs st k) b
       | none => classCarryAt bs st k) :=
  classCarryAt_succ bs st k

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.classCarryAt_succ' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.classCarryAt_succ

-- Bit `k` of the unescaped-quote mask.
example {bs : List UInt8} {st : ClassState} {k : Nat} {b : UInt8}
    (hk : k < 32) (hb : bs[k]? = some b) :
    (quoteMask bs st).getLsbD k = isUnescapedQuote (classCarryAt bs st k) b :=
  quoteMask_getLsbD hk hb

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.quoteMask_getLsbD' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.quoteMask_getLsbD

-- Bit `k` of the escaped-quote mask.
example {bs : List UInt8} {st : ClassState} {k : Nat} {b : UInt8}
    (hk : k < 32) (hb : bs[k]? = some b) :
    (escapedQuoteMask bs st).getLsbD k = isEscapedQuote (classCarryAt bs st k) b :=
  escapedQuoteMask_getLsbD hk hb

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.escapedQuoteMask_getLsbD' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.escapedQuoteMask_getLsbD

-- Bit `k` of the delimiter mask.
example {bs : List UInt8} {st : ClassState} {k : Nat} {b : UInt8}
    (hk : k < 32) (hb : bs[k]? = some b) :
    (delimiterMask bs st).getLsbD k = IsDelimB b :=
  delimiterMask_getLsbD hk hb

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.delimiterMask_getLsbD' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.delimiterMask_getLsbD

-- Bit `k` of the backslash mask.
example {bs : List UInt8} {st : ClassState} {k : Nat} {b : UInt8}
    (hk : k < 32) (hb : bs[k]? = some b) :
    (backslashMask bs st).getLsbD k = IsBackslashB b :=
  backslashMask_getLsbD hk hb

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.backslashMask_getLsbD' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.backslashMask_getLsbD

-- Bit `k` of the in-string mask is the string state after byte `k`.
example {bs : List UInt8} {st : ClassState} {k : Nat} {b : UInt8}
    (hk : k < 32) (hb : bs[k]? = some b) :
    (inStringMask bs st).getLsbD k = inStringAfter (classCarryAt bs st k) b :=
  inStringMask_getLsbD hk hb

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.inStringMask_getLsbD' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.inStringMask_getLsbD

-- Bit `k` of the candidate mask.
example {bs : List UInt8} {st : ClassState} {k : Nat} {b : UInt8}
    (hk : k < 32) (hb : bs[k]? = some b) :
    (candidateMask bs st).getLsbD k = isCandidateLane (classCarryAt bs st k) b :=
  candidateMask_getLsbD hk hb

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.candidateMask_getLsbD' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.candidateMask_getLsbD

-- The fold leaves the carry the window's bytes leave.
example (bs : List UInt8) (st : ClassState) :
    (classWindow bs st).carry = classCarryAt bs st 32 :=
  classWindow_carry bs st

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.classWindow_carry' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.classWindow_carry

-- A quote lane is exactly one of unescaped and escaped.
example (st : ClassState) (b : UInt8) :
    (isUnescapedQuote st b || isEscapedQuote st b) = IsQuoteB b :=
  quote_or_escaped st b

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.quote_or_escaped' does not depend on any axioms
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.quote_or_escaped

-- The byte rule's inside field is the classifier's in-string decision.
example (st : ClassState) (b : UInt8) :
    (∀ st', bodyStep (ClassState.toBody st) b = .cont st' →
        st'.inside = inStringAfter st b) ∧
    (bodyStep (ClassState.toBody st) b = .closed → inStringAfter st b = false) :=
  bodyStep_inside st b

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.bodyStep_inside' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.bodyStep_inside

-- The delimiter mask is the block layer's fold at `IsDelimB`.
example (bs : List UInt8) (st : ClassState) (hlen : 32 ≤ bs.length) :
    delimiterMask bs st = maskOfListWith IsDelimB bs :=
  delimiterMask_eq_maskOfListWith bs st hlen

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.delimiterMask_eq_maskOfListWith' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.delimiterMask_eq_maskOfListWith

-- The backslash mask is the block layer's fold at `IsBackslashB`.
example (bs : List UInt8) (st : ClassState) (hlen : 32 ≤ bs.length) :
    backslashMask bs st = maskOfListWith IsBackslashB bs :=
  backslashMask_eq_maskOfListWith bs st hlen

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.backslashMask_eq_maskOfListWith' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.backslashMask_eq_maskOfListWith

-- The two quote masks together are the block layer's raw quote mask.
example (bs : List UInt8) (st : ClassState) (hlen : 32 ≤ bs.length) :
    quoteMask bs st ||| escapedQuoteMask bs st = maskOfListWith IsQuoteB bs :=
  quoteMask_or_escaped_eq bs st hlen

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.quoteMask_or_escaped_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.quoteMask_or_escaped_eq

-- The scalar transition's mask is the classifier's components.
example (bs : List UInt8) (st : ClassState) (hlen : 32 ≤ bs.length) :
    maskOfList bs =
      delimiterMask bs st ||| quoteMask bs st ||| escapedQuoteMask bs st |||
        backslashMask bs st ||| maskOfListWith IsSpaceB bs :=
  maskOfList_decompose bs st hlen

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.maskOfList_decompose' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.maskOfList_decompose

-- The candidate mask is `q | (s & ~im)` at one window.
example (bs : List UInt8) (st : ClassState) (hlen : 32 ≤ bs.length) :
    candidateMask bs st =
      quoteMask bs st ||| (delimiterMask bs st &&& ~~~inStringMask bs st) :=
  candidateMask_eq bs st hlen

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.candidateMask_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.candidateMask_eq

-- The join's low half, read at a lane.
example (f : List UInt8 → ClassState → BitVec 32) (lo hi : Block32) (st : ClassState)
    {k : Nat} (hk : k < 32) :
    (classMask64 f lo hi st).getLsbD k = (f (List.ofFn lo) st).getLsbD k :=
  classMask64_getLsbD_lo f lo hi st hk

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.classMask64_getLsbD_lo' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.classMask64_getLsbD_lo

-- The join's high half, read at a lane, entered with the low half's carry.
example (f : List UInt8 → ClassState → BitVec 32) (lo hi : Block32) (st : ClassState)
    {k : Nat} (hk : k < 32) :
    (classMask64 f lo hi st).getLsbD (k + 32) =
      (f (List.ofFn hi) ((classWindow (List.ofFn lo) st).carry)).getLsbD k :=
  classMask64_getLsbD_hi f lo hi st hk

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.classMask64_getLsbD_hi' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.classMask64_getLsbD_hi

-- The join commutes with disjunction.
example (a b c d : BitVec 32) :
    mask64 a b ||| mask64 c d = mask64 (a ||| c) (b ||| d) :=
  mask64_or a b c d

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.mask64_or' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.mask64_or

-- The join commutes with conjunction.
example (a b c d : BitVec 32) :
    mask64 a b &&& mask64 c d = mask64 (a &&& c) (b &&& d) :=
  mask64_and a b c d

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.mask64_and' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.mask64_and

-- The join commutes with complement.
example (a b : BitVec 32) : ~~~(mask64 a b) = mask64 (~~~a) (~~~b) :=
  mask64_not a b

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.mask64_not' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.mask64_not

-- The kernel's sixty-four-lane candidate mask is `q | (s & ~im)`.
example (lo hi : Block32) (st : ClassState) :
    specCandidate64 lo hi st =
      specQuote64 lo hi st |||
        (specDelimiter64 lo hi st &&& ~~~specInString64 lo hi st) :=
  candidateMask64_eq lo hi st

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.candidateMask64_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.candidateMask64_eq

-- The decision, executed: `"\""` (four bytes) from outside a string.  The escaped quote is a
-- quote lane and not a candidate, so the candidate mask has lanes 0 and 3 while
-- the raw quote mask also has lane 2.
example :
    candidateMask [0x22, 0x5C, 0x22, 0x22] ⟨false, false⟩ = 0b1001 ∧
    quoteMask [0x22, 0x5C, 0x22, 0x22] ⟨false, false⟩ = 0b1001 ∧
    escapedQuoteMask [0x22, 0x5C, 0x22, 0x22] ⟨false, false⟩ = 0b100 ∧
    inStringMask [0x22, 0x5C, 0x22, 0x22] ⟨false, false⟩ = 0b0111 ∧
    (quoteMask [0x22, 0x5C, 0x22, 0x22] ⟨false, false⟩ |||
      escapedQuoteMask [0x22, 0x5C, 0x22, 0x22] ⟨false, false⟩) = 0b1101 :=
  escaped_quote_witness

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.escaped_quote_witness' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.escaped_quote_witness

-- The classifier's projection of the model's carry is the identity on `toBody`.
example (st : ClassState) : BodyState.classPart st.toBody = st :=
  ClassState.classPart_toBody st

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.ClassState.classPart_toBody' does not depend on any axioms
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.ClassState.classPart_toBody

-- One byte of agreement between the byte rule and the classifier's step.
example (st : BodyState) (b : UInt8) {st' : BodyState}
    (hstep : bodyStep st b = .cont st')
    (hodd : st.oddRun = true → st.utf8 = Utf8Need.none)
    (habove : Utf8Need.AboveAscii st.utf8)
    (hins : IsBackslashB b = true → st.inside = true) :
    BodyState.classPart st' = classStep (BodyState.classPart st) b :=
  classPart_classStep_of_cont st b hstep hodd habove hins

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.classPart_classStep_of_cont' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.classPart_classStep_of_cont

-- The rule's closing decision carries its own premises.
example {st : BodyState} {b : UInt8} (h : bodyStep st b = .closed) :
    st.inside = true ∧ st.oddRun = false ∧ IsQuoteB b = true :=
  bodyStep_closed_facts h

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.bodyStep_closed_facts' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.bodyStep_closed_facts

-- The two carries agree before lane `k`, under the two named conditions.
example (bs : List UInt8) (st : ClassState) {k : Nat}
    (hcont : ContinuesBefore bs st.toBody k)
    (hdom : NoBackslashOutside bs st.toBody k) :
    classCarryAt bs st k = BodyState.classPart (carryAt bs st.toBody k) :=
  classCarryAt_eq_classPart bs st hcont hdom

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.classCarryAt_eq_classPart' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.classCarryAt_eq_classPart

-- A window read from inside a body needs no condition on its bytes.
example (bs : List UInt8) (st : ClassState) (hin : st.inside = true) {k : Nat}
    (hcont : ContinuesBefore bs st.toBody k) :
    classCarryAt bs st k = BodyState.classPart (carryAt bs st.toBody k) :=
  classCarryAt_eq_classPart_of_inside bs st hin hcont

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.classCarryAt_eq_classPart_of_inside' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.classCarryAt_eq_classPart_of_inside

-- The no-stop hypothesis alone is not enough: a backslash outside a body fails
-- `NoBackslashOutside` and the carries differ.
example :
    (windowOf [0x5C] (⟨false, false⟩ : ClassState).toBody).stop = none ∧
      ¬ NoBackslashOutside [0x5C] (⟨false, false⟩ : ClassState).toBody 1 ∧
      classCarryAt [0x5C] (⟨false, false⟩ : ClassState) 1 ≠
        BodyState.classPart
          (carryAt [0x5C] (⟨false, false⟩ : ClassState).toBody 1) :=
  no_stop_does_not_identify_carries

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.no_stop_does_not_identify_carries' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.no_stop_does_not_identify_carries

-- The no-stop hypothesis is necessary: a closing stop at lane 0 fails
-- `ContinuesBefore` and the carries differ.
example :
    (windowOf [0x22] (⟨true, false⟩ : ClassState).toBody).stop = some (.close 0) ∧
      ¬ ContinuesBefore [0x22] (⟨true, false⟩ : ClassState).toBody 1 ∧
      classCarryAt [0x22] (⟨true, false⟩ : ClassState) 1 = ⟨false, false⟩ ∧
      carryAt [0x22] (⟨true, false⟩ : ClassState).toBody 1 = BodyState.body :=
  close_stop_carry_diverges

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.close_stop_carry_diverges' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.close_stop_carry_diverges

-- The model's quote mask is the classifier's two quote masks.
example (bs : List UInt8) (st : ClassState) (hlen : 32 ≤ bs.length)
    (hstop : (windowOf bs st.toBody).stop = none) :
    (windowOf bs st.toBody).quote = quoteMask bs st ||| escapedQuoteMask bs st :=
  windowOf_quote_eq bs st hlen hstop

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.windowOf_quote_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.windowOf_quote_eq

-- The model's backslash mask is the classifier's.
example (bs : List UInt8) (st : ClassState) (hlen : 32 ≤ bs.length)
    (hstop : (windowOf bs st.toBody).stop = none) :
    (windowOf bs st.toBody).backslash = backslashMask bs st :=
  windowOf_backslash_eq bs st hlen hstop

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.windowOf_backslash_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.windowOf_backslash_eq

-- The model's structural mask in the classifier's component vocabulary.
example (bs : List UInt8) (st : ClassState) (hlen : 32 ≤ bs.length) :
    (windowOf bs st.toBody).structural =
      delimiterMask bs st ||| quoteMask bs st ||| escapedQuoteMask bs st |||
        backslashMask bs st ||| maskOfListWith IsSpaceB bs :=
  windowOf_structural_eq bs st hlen

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.windowOf_structural_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.windowOf_structural_eq

-- With no stop the closing lane is empty on both sides.
example (bs : List UInt8) (st : ClassState) (hlen : 32 ≤ bs.length)
    (hstop : (windowOf bs st.toBody).stop = none) :
    (windowOf bs st.toBody).delim = 0 ∧
      quoteMask bs st &&& ~~~inStringMask bs st = 0 :=
  windowOf_delim_eq_zero_of_stop_none bs st hlen hstop

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.windowOf_delim_eq_zero_of_stop_none' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.windowOf_delim_eq_zero_of_stop_none

-- At a closing stop's lane the model's closing lane and the classifier's are the same
-- bit, under the no-backslash condition the stop's readback does not supply.
example (bs : List UInt8) (st : ClassState) {k : Nat}
    (hstop : (windowOf bs st.toBody).stop = some (.close k))
    (hdom : NoBackslashOutside bs st.toBody k) :
    (windowOf bs st.toBody).delim.getLsbD k =
      (quoteMask bs st &&& ~~~inStringMask bs st).getLsbD k :=
  windowOf_delim_eq_of_close_stop bs st hstop hdom

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.windowOf_delim_eq_of_close_stop' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.windowOf_delim_eq_of_close_stop

-- The no-backslash condition is necessary for that identification.
example :
    (windowOf [0x5C, 0x22, 0x22] (⟨false, false⟩ : ClassState).toBody).stop =
        some (.close 2) ∧
      (windowOf [0x5C, 0x22, 0x22] (⟨false, false⟩ : ClassState).toBody).delim.getLsbD 2 =
        true ∧
      (quoteMask [0x5C, 0x22, 0x22] ⟨false, false⟩ &&&
        ~~~inStringMask [0x5C, 0x22, 0x22] ⟨false, false⟩).getLsbD 2 = false ∧
      ContinuesBefore [0x5C, 0x22, 0x22] (⟨false, false⟩ : ClassState).toBody 2 ∧
      ¬ NoBackslashOutside [0x5C, 0x22, 0x22] (⟨false, false⟩ : ClassState).toBody 2 :=
  delim_eq_fails_outside

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.delim_eq_fails_outside' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.delim_eq_fails_outside

-- The continuation is necessary for that identification.
example :
    (windowOf [0x22, 0x22] (⟨true, false⟩ : ClassState).toBody).stop = some (.close 0) ∧
      (windowOf [0x22, 0x22] (⟨true, false⟩ : ClassState).toBody).delim.getLsbD 1 = true ∧
      (quoteMask [0x22, 0x22] ⟨true, false⟩ &&&
        ~~~inStringMask [0x22, 0x22] ⟨true, false⟩).getLsbD 1 = false ∧
      NoBackslashOutside [0x22, 0x22] (⟨true, false⟩ : ClassState).toBody 1 ∧
      ¬ ContinuesBefore [0x22, 0x22] (⟨true, false⟩ : ClassState).toBody 1 :=
  delim_eq_fails_past_stop

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.delim_eq_fails_past_stop' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.delim_eq_fails_past_stop

-- Past a stop the classifier steps and the model holds.
example (bs : List UInt8) (st : ClassState) {s : Nat} {b : UInt8}
    (hb : bs[s]? = some b)
    (hcarry : classCarryAt bs st s = BodyState.classPart (carryAt bs st.toBody s))
    (hstop : ∀ st', bodyStep (carryAt bs st.toBody s) b ≠ .cont st') :
    carryAt bs st.toBody (s + 1) = carryAt bs st.toBody s ∧
      classCarryAt bs st (s + 1) =
        classStep (BodyState.classPart (carryAt bs st.toBody s)) b :=
  classCarryAt_succ_of_stop bs st hb hcarry hstop

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.classCarryAt_succ_of_stop' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.classCarryAt_succ_of_stop

-- At a closing stop the classifier's flag is the complement of the model's.
example (bs : List UInt8) (st : ClassState) {s : Nat} {b : UInt8}
    (hb : bs[s]? = some b)
    (hcont : ContinuesBefore bs st.toBody s)
    (hdom : NoBackslashOutside bs st.toBody s)
    (hclosed : bodyStep (carryAt bs st.toBody s) b = .closed) :
    classCarryAt bs st (s + 1) = ⟨false, false⟩ ∧
      carryAt bs st.toBody (s + 1) = carryAt bs st.toBody s ∧
      (carryAt bs st.toBody s).inside = true :=
  classCarryAt_succ_closed bs st hb hcont hdom hclosed

/--
info: 'LeanLLVM.Vellum.JsonScanSpec.classCarryAt_succ_closed' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.classCarryAt_succ_closed

/-! ### The stage-1 depth counter

`LeanLLVM/Vellum/DepthCountRefine.lean` proves the emitted kernel `@depth_count`
against the depth fold: the run returns the fold's running depth, writes the
depth and the running-depth sum to the statistics pair, and changes no other
byte.  The fixture pin is restated here through the module's public `src`, and
the axiom footprint of the theorem and of the two internal lemmas its proof rests
on is pinned.

The negative control for the fixture pin is a mutation, not a shipped guard:
editing `tests/v16/depth_count.ll` at `%more` from `ult` to `ule` parses to an
AST that is not the transcription, so applying the `#guard` below to that text
yields `false`.  The mutation is not committed.
-/

open LeanLLVM.Vellum.DepthCountRefine

-- The committed text parses to the transcription the module proves against.
-- `src` is the string the imported module baked in through `include_str`, so
-- this reads the fixture as of that module's elaboration: after editing
-- `tests/v16/depth_count.ll`, re-elaborate `DepthCountRefine` before reading a
-- green run here.
#guard
  match LeanLLVM.parseModule src with
  | .ok m => m = { decls := [], functions := [depthFunction] }
  | .error _ => false

-- The conclusion, at the public statement: from a memory holding the index array
-- and the bytes it points at, the kernel returns and stores the depth fold over
-- the token sequence, and leaves memory otherwise unchanged.
example (calls : LeanLLVM.Calls) (pbuf pidx pstats : Nat) (m0 : LeanLLVM.Mem)
    (tokens : List UInt8) (idxs : Nat → Nat) (n : Nat)
    (hn : n < 2^63) (hlen : tokens.length = n)
    (hidx : ∀ (k : Nat), k < n →
      LeanLLVM.readBytes m0 (pidx + k * 4) 4 = some (LeanLLVM.natToBytes (idxs k) 4))
    (hfit : ∀ (k : Nat), k < n → idxs k < 2^32)
    (hbuf : ∀ (k : Nat) (hk : k < n),
      LeanLLVM.readBytes m0 (pbuf + idxs k) 1 =
        some [tokens.get ⟨k, by rw [hlen]; exact hk⟩]) :
    LeanLLVM.runFuel calls (n + 2) depthFunction
        (start m0 pbuf pidx pstats (BitVec.ofNat 64 n)) =
      LeanLLVM.Vellum.DepthCountRefine.Result calls m0 pstats tokens :=
  depth_count_refines calls pbuf pidx pstats m0 tokens idxs n hn hlen hidx hfit hbuf

/--
info: 'LeanLLVM.Vellum.DepthCountRefine.depth_count_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.DepthCountRefine.depth_count_refines

-- The installation boundary, restated: the same hypothesis set and conclusion,
-- with `depthContract_holds` as the inhabitant.  The theorem is the contract's
-- own proof, so a hypothesis added to `depthContract` and not to
-- `depth_count_refines` (or the reverse) makes this fail rather than letting a
-- certificate name a boundary nothing proved.
example (calls : LeanLLVM.Calls) (pbuf pidx pstats : Nat) (m0 : LeanLLVM.Mem)
    (tokens : List UInt8) (idxs : Nat → Nat) (n : Nat)
    (hn : n < 2^63) (hlen : tokens.length = n)
    (hidx : ∀ (k : Nat), k < n →
      LeanLLVM.readBytes m0 (pidx + k * 4) 4 = some (LeanLLVM.natToBytes (idxs k) 4))
    (hfit : ∀ (k : Nat), k < n → idxs k < 2^32)
    (hbuf : ∀ (k : Nat) (hk : k < n),
      LeanLLVM.readBytes m0 (pbuf + idxs k) 1 =
        some [tokens.get ⟨k, by rw [hlen]; exact hk⟩]) :
    LeanLLVM.runFuel calls (n + 2) depthFunction
        (start m0 pbuf pidx pstats (BitVec.ofNat 64 n)) =
      LeanLLVM.Vellum.DepthCountRefine.Result calls m0 pstats tokens := by
  have h : depthContract := depthContract_holds
  unfold depthContract at h
  exact h calls pbuf pidx pstats m0 tokens idxs n hn hlen hidx hfit hbuf

/--
info: 'LeanLLVM.Vellum.DepthCountRefine.depthContract_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.DepthCountRefine.depthContract_holds

/--
info: 'LeanLLVM.Vellum.DepthCountRefine.loop_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.DepthCountRefine.loop_run

/--
info: 'LeanLLVM.Vellum.DepthCountRefine.loop_body' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.DepthCountRefine.loop_body

/-! ### The carry-less product and the mask identity

`LeanLLVM/Vellum/Pclmul.lean` states the classifier's arithmetic: `clmul` — the
truncated GF(2) polynomial product as a fold of shifted XORs — the all-ones
instance as the prefix parity (`clmul_allOnes_self`), its uniqueness
(`clmul_allOnes_unique`), and the two mask identities that put
`JsonScanSpec`'s in-string mask in that arithmetic, with the outgoing carry as
the block's top lane.

Its docstring records what is **not** proved: the kernel's `specQuote64`
derivation through `pext`/`pdep` lane moves, and any relation to the emitted IR.
Nothing here restates those as facts.

Each theorem's axiom footprint is pinned below, and each is restated as an
`example` over the public interface.  Every pin is at `[propext, Quot.sound]` or
below: the module proves its own all-ones lane lemma rather than using
`BitVec.getLsbD_allOnes`, whose proof carries `Classical.choice`, so no theorem
here depends on a choice principle.
-/

open LeanLLVM.Vellum.Pclmul

-- The XOR normal forms the folds are written with.
example {w : Nat} (a b c : BitVec w) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) :=
  xor_left_comm a b c

example {w : Nat} (a b : BitVec w) : (a ^^^ b) ^^^ b = a :=
  xor_self_right a b

-- Cancelling an addend in the Bool XOR group.
example (x y z : Bool) : ((x ^^ y) = z) ↔ (x = (z ^^ y)) :=
  xor_eq_iff

/--
info: 'LeanLLVM.Vellum.Pclmul.xor_left_comm' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.xor_left_comm

/--
info: 'LeanLLVM.Vellum.Pclmul.xor_self_right' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.xor_self_right

/--
info: 'LeanLLVM.Vellum.Pclmul.xor_eq_iff' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.xor_eq_iff

-- The all-ones multiplier selects every shifted copy of `a`.
example {w : Nat} (a : BitVec w) :
    clmul a (BitVec.allOnes w) =
      (List.range w).foldl (fun acc j => acc ^^^ (a <<< j)) 0#w :=
  clmul_allOnes_eq_fold a

/-- **The prefix-parity identity**: the all-ones product is the prefix XOR of its
input, so it is the `1 + x` inverse of its own shift. -/
example {w : Nat} (a : BitVec w) :
    clmul a (BitVec.allOnes w) ^^^ (clmul a (BitVec.allOnes w) <<< 1) = a :=
  clmul_allOnes_self a

/-- **The uniqueness**: any word with that difference *is* the all-ones product —
prefix parity is pinned by its difference and its lane zero, not merely
exhibited. -/
example {w : Nat} {p q : BitVec w} (h : p ^^^ (p <<< 1) = q) :
    p = clmul q (BitVec.allOnes w) :=
  clmul_allOnes_unique h

/--
info: 'LeanLLVM.Vellum.Pclmul.clmul_allOnes_eq_fold' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.clmul_allOnes_eq_fold

/--
info: 'LeanLLVM.Vellum.Pclmul.clmul_allOnes_self' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.clmul_allOnes_self

/--
info: 'LeanLLVM.Vellum.Pclmul.clmul_allOnes_unique' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.clmul_allOnes_unique

-- The carry word's lanes are the carry bit.
example {w : Nat} {seed : Bool} {k : Nat} (hk : k < w) :
    (seedVec w seed).getLsbD k = seed :=
  seedVec_getLsbD hk

-- The lane recurrence read off the identity: lane zero, and the step.
example {w : Nat} (a : BitVec w) :
    (clmul a (BitVec.allOnes w)).getLsbD 0 = a.getLsbD 0 :=
  clmul_allOnes_getLsbD_zero a

example {w : Nat} {a : BitVec w} {k : Nat} (hk : k + 1 < w) :
    (clmul a (BitVec.allOnes w)).getLsbD (k + 1)
      = (a.getLsbD (k + 1) ^^ (clmul a (BitVec.allOnes w)).getLsbD k) :=
  clmul_allOnes_getLsbD_succ hk

/-- Two lane sequences with the same difference and the same seed agree. -/
example {w : Nat} (a c m : BitVec w) (seed : Bool)
    (hc0 : c.getLsbD 0 = a.getLsbD 0)
    (hc : ∀ k, k + 1 < w → c.getLsbD (k + 1) = (a.getLsbD (k + 1) ^^ c.getLsbD k))
    (hm0 : m.getLsbD 0 = (a.getLsbD 0 ^^ seed))
    (hm : ∀ k, k + 1 < w → m.getLsbD (k + 1) = (a.getLsbD (k + 1) ^^ m.getLsbD k)) :
    m = c ^^^ seedVec w seed :=
  eq_clmul_of_recur a c m seed hc0 hc hm0 hm

/--
info: 'LeanLLVM.Vellum.Pclmul.seedVec_getLsbD' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.seedVec_getLsbD

/--
info: 'LeanLLVM.Vellum.Pclmul.clmul_allOnes_getLsbD_zero' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.clmul_allOnes_getLsbD_zero

/--
info: 'LeanLLVM.Vellum.Pclmul.clmul_allOnes_getLsbD_succ' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.clmul_allOnes_getLsbD_succ

/--
info: 'LeanLLVM.Vellum.Pclmul.eq_clmul_of_recur' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.eq_clmul_of_recur

-- The window recurrence, read one lane at a time against `classStep`.
example (s : ClassState) (b : UInt8) :
    inStringAfter s b = (s.inside ^^ isUnescapedQuote s b) :=
  inStringAfter_apply s b

example (s : ClassState) (b b' : UInt8) :
    inStringAfter (classStep s b) b'
      = (inStringAfter s b ^^ isUnescapedQuote (classStep s b) b') :=
  inStringAfter_classStep s b b'

example (bs : List UInt8) (st : ClassState) : classCarryAt bs st 0 = st :=
  classCarryAt_zero bs st

example {bs : List UInt8} {st : ClassState} {b : UInt8} (hb : bs[0]? = some b) :
    (inStringMask bs st).getLsbD 0 = ((quoteMask bs st).getLsbD 0 ^^ st.inside) :=
  inStringMask_zero hb

example {bs : List UInt8} {st : ClassState} {i : Nat} {b b' : UInt8}
    (hi : i + 1 < 32) (hbi : bs[i]? = some b) (hbi1 : bs[i + 1]? = some b') :
    (inStringMask bs st).getLsbD (i + 1)
      = ((quoteMask bs st).getLsbD (i + 1) ^^ (inStringMask bs st).getLsbD i) :=
  inStringMask_recur hi hbi hbi1

/-- **The window identity**: the in-string mask is the all-ones product of the
unescaped-quote mask, XOR the carry word. -/
example (bs : List UInt8) (st : ClassState) (hlen : 32 ≤ bs.length) :
    inStringMask bs st =
      clmul (quoteMask bs st) (BitVec.allOnes 32) ^^^ seedVec 32 st.inside :=
  inStringMask_eq_clmul bs st hlen

/--
info: 'LeanLLVM.Vellum.Pclmul.inStringAfter_apply' does not depend on any axioms
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.inStringAfter_apply

/--
info: 'LeanLLVM.Vellum.Pclmul.inStringAfter_classStep' does not depend on any axioms
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.inStringAfter_classStep

/--
info: 'LeanLLVM.Vellum.Pclmul.classCarryAt_zero' does not depend on any axioms
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.classCarryAt_zero

/--
info: 'LeanLLVM.Vellum.Pclmul.inStringMask_zero' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.inStringMask_zero

/--
info: 'LeanLLVM.Vellum.Pclmul.inStringMask_recur' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.inStringMask_recur

/--
info: 'LeanLLVM.Vellum.Pclmul.inStringMask_eq_clmul' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.inStringMask_eq_clmul

-- Lane lookups in a halved block.
example {lo : Block32} {k : Nat} (hk : k < 32) :
    (List.ofFn lo)[k]? = some (lo ⟨k, hk⟩) :=
  ofFn_getElem? hk

example {lo hi : Block32} {st : ClassState} {k : Nat} (hk : k < 32) :
    (specInString64 lo hi st).getLsbD k = (inStringMask (List.ofFn lo) st).getLsbD k :=
  specInString64_bit_lo hk

example {lo hi : Block32} {st : ClassState} {m : Nat} (hm : m < 32) :
    (specInString64 lo hi st).getLsbD (m + 32) =
      (inStringMask (List.ofFn hi) ((classWindow (List.ofFn lo) st).carry)).getLsbD m :=
  specInString64_bit_hi hm

example {lo hi : Block32} {st : ClassState} {j : Nat} (h32 : 32 ≤ j) (hj : j < 64) :
    (specInString64 lo hi st).getLsbD j =
      (inStringMask (List.ofFn hi) ((classWindow (List.ofFn lo) st).carry)).getLsbD (j - 32) :=
  specInString64_bit_hi' h32 hj

example {lo hi : Block32} {st : ClassState} {k : Nat} (hk : k < 32) :
    (specQuote64 lo hi st).getLsbD k = (quoteMask (List.ofFn lo) st).getLsbD k :=
  specQuote64_bit_lo hk

example {lo hi : Block32} {st : ClassState} {m : Nat} (hm : m < 32) :
    (specQuote64 lo hi st).getLsbD (m + 32) =
      (quoteMask (List.ofFn hi) ((classWindow (List.ofFn lo) st).carry)).getLsbD m :=
  specQuote64_bit_hi hm

example {lo hi : Block32} {st : ClassState} {j : Nat} (h32 : 32 ≤ j) (hj : j < 64) :
    (specQuote64 lo hi st).getLsbD j =
      (quoteMask (List.ofFn hi) ((classWindow (List.ofFn lo) st).carry)).getLsbD (j - 32) :=
  specQuote64_bit_hi' h32 hj

example {lo hi : Block32} {st : ClassState} :
    (specInString64 lo hi st).getLsbD 32 =
      (inStringMask (List.ofFn hi) ((classWindow (List.ofFn lo) st).carry)).getLsbD 0 :=
  specInString64_bit_32

example {lo hi : Block32} {st : ClassState} :
    (specQuote64 lo hi st).getLsbD 32 =
      (quoteMask (List.ofFn hi) ((classWindow (List.ofFn lo) st).carry)).getLsbD 0 :=
  specQuote64_bit_32

/-- The carry crosses the halfway point as the low half's top lane. -/
example (bs : List UInt8) (st : ClassState) (hlen : 32 ≤ bs.length) :
    (classWindow bs st).carry.inside = (inStringMask bs st).getLsbD 31 :=
  classWindow_carry_inside bs st hlen

example {lo hi : Block32} {st : ClassState} :
    (specInString64 lo hi st).getLsbD 32
      = ((specQuote64 lo hi st).getLsbD 32 ^^ (specInString64 lo hi st).getLsbD 31) :=
  specInString64_step_32

example {lo hi : Block32} {st : ClassState} {k : Nat}
    (hk : 33 ≤ k + 1) (hk64 : k + 1 < 64) :
    (specInString64 lo hi st).getLsbD (k + 1)
      = ((specQuote64 lo hi st).getLsbD (k + 1) ^^ (specInString64 lo hi st).getLsbD k) :=
  specInString64_step_hi hk hk64

/-- **The block identity**: the kernel's in-string mask over a sixty-four-byte
block is the all-ones product of its unescaped-quote mask, XOR the carry. -/
example (lo hi : Block32) (st : ClassState) :
    specInString64 lo hi st =
      clmul (specQuote64 lo hi st) (BitVec.allOnes 64) ^^^ seedVec 64 st.inside :=
  specInString64_eq_clmul lo hi st

/-- **The outgoing carry**: the way out of a block is its mask's bit 63. -/
example (lo hi : Block32) (st : ClassState) :
    (classWindow (List.ofFn hi) ((classWindow (List.ofFn lo) st).carry)).carry.inside
      = (specInString64 lo hi st).getLsbD 63 :=
  specInString64_outgoing_carry lo hi st

example (lo hi : Block32) (st : ClassState) :
    (classWindow (List.ofFn hi) ((classWindow (List.ofFn lo) st).carry)).carry.inside
      = ((clmul (specQuote64 lo hi st) (BitVec.allOnes 64)
          ^^^ seedVec 64 st.inside)).getLsbD 63 :=
  specInString64_outgoing_carry_pclmul lo hi st

/--
info: 'LeanLLVM.Vellum.Pclmul.ofFn_getElem?' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.ofFn_getElem?

/--
info: 'LeanLLVM.Vellum.Pclmul.specInString64_bit_lo' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.specInString64_bit_lo

/--
info: 'LeanLLVM.Vellum.Pclmul.specInString64_bit_hi' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.specInString64_bit_hi

/--
info: 'LeanLLVM.Vellum.Pclmul.specInString64_bit_hi'' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.specInString64_bit_hi'

/--
info: 'LeanLLVM.Vellum.Pclmul.specQuote64_bit_lo' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.specQuote64_bit_lo

/--
info: 'LeanLLVM.Vellum.Pclmul.specQuote64_bit_hi' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.specQuote64_bit_hi

/--
info: 'LeanLLVM.Vellum.Pclmul.specQuote64_bit_hi'' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.specQuote64_bit_hi'

/--
info: 'LeanLLVM.Vellum.Pclmul.specInString64_bit_32' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.specInString64_bit_32

/--
info: 'LeanLLVM.Vellum.Pclmul.specQuote64_bit_32' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.specQuote64_bit_32

/--
info: 'LeanLLVM.Vellum.Pclmul.classWindow_carry_inside' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.classWindow_carry_inside

/--
info: 'LeanLLVM.Vellum.Pclmul.specInString64_step_32' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.specInString64_step_32

/--
info: 'LeanLLVM.Vellum.Pclmul.specInString64_step_hi' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.specInString64_step_hi

/--
info: 'LeanLLVM.Vellum.Pclmul.specInString64_eq_clmul' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.specInString64_eq_clmul

/--
info: 'LeanLLVM.Vellum.Pclmul.specInString64_outgoing_carry' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.specInString64_outgoing_carry

/--
info: 'LeanLLVM.Vellum.Pclmul.specInString64_outgoing_carry_pclmul' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Pclmul.specInString64_outgoing_carry_pclmul

/-! #### Executed witnesses

`clmul` is a fold, so the four-lane instance reduces: the specification module's
own example has the unescaped-quote mask of `"\""` at `0b1001` and its all-ones
product at the inclusive prefix XOR `0b0111`, and the identity's two sides agree
on the specification's window. -/

#guard clmul (0b1001 : BitVec 4) (0b1111 : BitVec 4) = 0b0111
#guard clmul (0b1001 : BitVec 4) (BitVec.allOnes 4) ^^^ seedVec 4 true = 0b1000

example :
    inStringMask (0x22 :: List.replicate 31 0x20) ⟨false, false⟩
      = clmul (quoteMask (0x22 :: List.replicate 31 0x20) ⟨false, false⟩)
          (BitVec.allOnes 32) ^^^ seedVec 32 false :=
  inStringMask_eq_clmul _ _ (by simp)

/-! ### The bit intrinsics and the kernel's quote-mask derivation

`LeanLLVM/Vellum/BitLanes.lean` models the three instructions the index kernel
calls besides `pclmulqdq` — `pext`, `pdep` and `ctlz` — in lane vocabulary, with
the rank machinery that pairs a mask's set lanes with their positions:
`rank_setLanes_getElem` (the `j`-th set lane's rank is `j`),
`setLanes_getElem?_rank` (a set lane's rank indexes it), the population bound
`setLanes_length_le` and the monotonicity `rank_mono`.  The Galois connection is
two statements: `pdep_pext` — `pdep (pext a m) m = a &&& m`, for every `a`, since
scattering a gather puts back exactly the lanes `m` selects — and the round trip
`pext_pdep`, `pext (pdep a m) m = a &&& lowLanes w (setLanes m).length`, whose
lanes above the population count are zero whatever was scattered there.  `ctlz` is
the leading-zero count and `trailingRun` the maximal suffix of set lanes;
`ctlz (~~~m) = trailingRun m` is `ctlz_not_eq_trailingRun`.

`LeanLLVM/Vellum/QuoteDerive.lean` proves the kernel's escape arithmetic against
`JsonScanSpec`'s own masks.  `kernelEscape_eq` says the kernel's scatter is the
parity mask on the lanes that are not backslashes — the kernel's mask leaves a
run's interior lanes clear, and the identity says exactly that — and `kernelQuote64`
is the derivation itself: `%qmc2 = %qrawc2 & ~%escc2` over a sixty-four-lane block
*is* the specification's `specQuote64`.  Both carry the hypothesis
`st.oddRun = (runOpen && ppar)`: the kernel carries the run-open bit beside the
parity, `ClassState` does not name it, and the two agree under that invariant,
which the kernel maintains because `%ppnc2` implies `%topc2`.  `ppn64` is the same
for the outgoing parity: the kernel's `ctlz(~~~bs) & 1`, corrected when the block
is all backslashes and the run continues, is the `oddRun` the specification's
`classStep` fold leaves.

Every public theorem is pinned below at `[propext, Quot.sound]` or narrower; the three
`private` numeral lemmas of `BitLanes` cannot be named from another file and are not
pinned.  The `BitVec`
and `List` lane lemmas whose proof terms carry `Classical.choice`
(`BitVec.getLsbD_allOnes`, `BitVec.getLsbD_not`, `List.filter_eq_nil_iff`, and
`JsonScanSpec.mask64_not`, which follows from the second) are not used: each is
replaced by a local proof, so no theorem here needs a choice principle.
-/

open LeanLLVM.Vellum.BitLanes LeanLLVM.Vellum.QuoteDerive

-- A packed lane reads back as the function's value.
example (f : Fin 8 → Bool) : (ofLanes f).getLsbD 3 = f ⟨3, by decide⟩ :=
  ofLanes_getLsbD f (by decide)

-- A mask has at most `w` set lanes, and the rank counts them without exceeding
-- that bound and without decreasing as the lane rises.
example (m : BitVec 8) : (setLanes m).length ≤ 8 := setLanes_length_le m

example (m : BitVec 8) {i j : Nat} (h : i ≤ j) : rank m i ≤ rank m j := rank_mono m h

-- The two alignment facts.
example (m : BitVec 8) {j : Nat} (hj : j < (setLanes m).length) :
    rank m (setLanes m)[j] = j :=
  rank_setLanes_getElem m hj

example (m : BitVec 8) {i : Nat} (hi : i < 8) (hm : m.getLsbD i = true) :
    (setLanes m)[rank m i]? = some i :=
  setLanes_getElem?_rank m hi hm

-- The Galois connection: scattering a gather puts back exactly `m`'s lanes.
example {w : Nat} (a m : BitVec w) : pdep (pext a m) m = a &&& m := pdep_pext a m

-- The round trip clears the lanes above the population count: `0b0110` has two set
-- lanes, so gathering its scatter keeps `a`'s lanes 0 and 1 and clears lanes 2 and 3,
-- even though `a` sets lane 3.
example : pext (pdep (0b1011 : BitVec 4) (0b0110 : BitVec 4)) (0b0110 : BitVec 4)
    = 0b0011 := by decide

-- `ctlz` of the complement is the trailing run.
example (m : BitVec 8) : ctlz (~~~m) = trailingRun m := ctlz_not_eq_trailingRun m

-- The run-start and run-end lanes do not read the run-open bit, and a run starts at
-- lane zero exactly when lane zero is a backslash.
example (bs : BitVec 8) (o : Bool) : (runStarts bs o).getLsbD 0 = bs.getLsbD 0 := by
  rw [runStarts_getLsbD bs o (by decide), startLane]
  cases bs.getLsbD 0 <;> cases o <;> rfl

example (bs : BitVec 8) : (runEnds bs).getLsbD 7 = bs.getLsbD 7 := by
  rw [runEnds_getLsbD bs (by decide), endLane]
  rw [BitVec.getLsbD_of_ge bs 8 (by decide)]
  rw [Bool.not_false, Bool.and_true]

-- The count invariant: a backslash lane has been entered and not yet left.
example (bs : BitVec 8) (o : Bool) {k : Nat} (hk : k < 8) :
    startsBelow bs o (k + 1) = endsBelow bs k + (if bs.getLsbD k then 1 else 0) :=
  startsUpTo_end bs o k hk

-- The escape mask is the parity mask on the lanes that are not backslashes.
example (bs : BitVec 8) (o p : Bool) :
    kernelEscape bs o p = escapeLanes bs o p &&& ~~~bs :=
  kernelEscape_eq bs o p

-- The derivation, over the specification's own masks.
example (lo hi : Block32) (st : ClassState) (o p : Bool) (hst : st.oddRun = (o && p)) :
    kernelQuote (specMask64 IsQuoteB lo hi) (specMask64 IsBackslashB lo hi) o p
      = specQuote64 lo hi st :=
  kernelQuote64 lo hi st o p hst

-- The same, stated against the specification's fold: the low half's `oddRun` is the
-- lane recursion the kernel's escape arithmetic runs on.
example (lo hi : Block32) (st : ClassState) (o p : Bool) (hst : st.oddRun = (o && p)) :
    (classCarryAt (List.ofFn lo) st 16).oddRun
      = runParityBefore (specMask64 IsBackslashB lo hi) o p 16 :=
  oddRun_lo hst 16 (by decide)

example (lo hi : Block32) (st : ClassState) (o p : Bool) (hst : st.oddRun = (o && p)) :
    (classCarryAt (List.ofFn hi) (classWindow (List.ofFn lo) st).carry 16).oddRun
      = runParityBefore (specMask64 IsBackslashB lo hi) o p 48 :=
  oddRun_hi hst 16 (by decide)

-- The run parity at a lane is the trailing run's parity.
example (bs : BitVec 8) (o p : Bool) :
    runParityBefore bs o p 8
      = (decide (suffixRun bs 8 % 2 = 1) ^^ (decide (suffixRun bs 8 = 8) && (o && p))) :=
  runParityBefore_eq bs o p 8 (by decide)

-- `%lzpc2` is that parity, and `%ppnc2` is the fold's `oddRun`.
example (bs : BitVec 8) :
    decide (ctlz (~~~bs) % 2 = 1) = decide (suffixRun bs 8 % 2 = 1) :=
  lzParity_eq_suffixRun bs

example (bs : BitVec 8) (o p : Bool) (h : 0 < 8) :
    nextParity bs o p = oneLane 8 (runParityBefore bs o p 8) :=
  nextParity_eq bs o p h

example (lo hi : Block32) (st : ClassState) (o p : Bool) (hst : st.oddRun = (o && p)) :
    nextParity (specMask64 IsBackslashB lo hi) o p
      = oneLane 64
          (classWindow (List.ofFn hi) (classWindow (List.ofFn lo) st).carry).carry.oddRun :=
  ppn64 lo hi st o p hst

-- The derivation's hypothesis is not a restriction.  The kernel's parity word lives
-- on the block's top lane, so a nonzero outgoing parity means an open run…
example (bs : BitVec 8) (o p : Bool) : nextParity bs o p &&& ~~~(bs >>> 7) = 0#8 :=
  nextParity_and_not_top bs o p

example (bs : BitVec 8) (o p : Bool) : (bs >>> 7 = 0#8) ↔ bs.getLsbD 7 = false :=
  topWord_eq_zero_iff bs (by decide)

example (bs : BitVec 8) (o p : Bool) :
    nextParity bs o p ≠ 0#8 → bs.getLsbD 7 = true :=
  nextParity_ne_zero_imp_open bs o p (by decide)

-- …and the specification's parity is its own run-open bit, in every state the fold
-- reaches and in the degenerate instance any `ClassState` satisfies.
example (st : ClassState) (b : UInt8) :
    (classStep st b).oddRun = (IsBackslashB b && (classStep st b).oddRun) :=
  classStep_oddRun_gated st b

example (bs : List UInt8) (inside : Bool) (k : Nat) (hk : k ≤ bs.length) :
    (classCarryAt bs ⟨inside, false⟩ k).oddRun
      = (byteOpen bs k && (classCarryAt bs ⟨inside, false⟩ k).oddRun) :=
  specCarry_hypothesis bs inside k hk

example (st : ClassState) : st.oddRun = (st.oddRun && st.oddRun) :=
  classState_self_open st

-- Every public theorem's footprint, in declaration order, `BitLanes` first.  The three
-- `private` numeral lemmas of `BitLanes` cannot be named from another file and so are
-- not pinned; every named theorem here is.
/--
info: 'LeanLLVM.Vellum.BitLanes.ofLanes_getLsbD' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.ofLanes_getLsbD

/--
info: 'LeanLLVM.Vellum.BitLanes.ofLanes_congr' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.ofLanes_congr

/--
info: 'LeanLLVM.Vellum.BitLanes.ofLanes_false' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.ofLanes_false

/--
info: 'LeanLLVM.Vellum.BitLanes.lowLanes_getLsbD' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.lowLanes_getLsbD

/--
info: 'LeanLLVM.Vellum.BitLanes.allOnes_getLsbD_of_lt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.allOnes_getLsbD_of_lt

/--
info: 'LeanLLVM.Vellum.BitLanes.getLsbD_not_of_lt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.getLsbD_not_of_lt

/--
info: 'LeanLLVM.Vellum.BitLanes.mem_setLanes' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.mem_setLanes

/--
info: 'LeanLLVM.Vellum.BitLanes.range_pairwise' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.range_pairwise

/--
info: 'LeanLLVM.Vellum.BitLanes.setLanes_pairwise' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.setLanes_pairwise

/--
info: 'LeanLLVM.Vellum.BitLanes.setLanes_length_le' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.setLanes_length_le

/--
info: 'LeanLLVM.Vellum.BitLanes.setLanes_getElem_true' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.setLanes_getElem_true

/--
info: 'LeanLLVM.Vellum.BitLanes.setLanes_getElem_lt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.setLanes_getElem_lt

/--
info: 'LeanLLVM.Vellum.BitLanes.setLanes_getElem?_eq' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.setLanes_getElem?_eq

/--
info: 'LeanLLVM.Vellum.BitLanes.rank_le' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.rank_le

/--
info: 'LeanLLVM.Vellum.BitLanes.filter_implies_filter' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.filter_implies_filter

/--
info: 'LeanLLVM.Vellum.BitLanes.rank_mono' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.rank_mono

/--
info: 'LeanLLVM.Vellum.BitLanes.filter_eq_nil_of_all_false' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.filter_eq_nil_of_all_false

/--
info: 'LeanLLVM.Vellum.BitLanes.filter_lt_getElem_eq_take' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.filter_lt_getElem_eq_take

/--
info: 'LeanLLVM.Vellum.BitLanes.filter_lt_getElem_eq_take_length' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.filter_lt_getElem_eq_take_length

/--
info: 'LeanLLVM.Vellum.BitLanes.filter_lt_getElem?_mem' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.filter_lt_getElem?_mem

/--
info: 'LeanLLVM.Vellum.BitLanes.rank_setLanes_getElem' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.rank_setLanes_getElem

/--
info: 'LeanLLVM.Vellum.BitLanes.setLanes_getElem?_rank' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.setLanes_getElem?_rank

/--
info: 'LeanLLVM.Vellum.BitLanes.pext_getLsbD' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.pext_getLsbD

/--
info: 'LeanLLVM.Vellum.BitLanes.pext_getLsbD_of_lt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.pext_getLsbD_of_lt

/--
info: 'LeanLLVM.Vellum.BitLanes.pext_getLsbD_of_ge' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.pext_getLsbD_of_ge

/--
info: 'LeanLLVM.Vellum.BitLanes.pdep_getLsbD' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.pdep_getLsbD

/--
info: 'LeanLLVM.Vellum.BitLanes.pdep_pext' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.pdep_pext

/--
info: 'LeanLLVM.Vellum.BitLanes.pext_pdep' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.pext_pdep

/--
info: 'LeanLLVM.Vellum.BitLanes.pext_pdep_of_clear' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.pext_pdep_of_clear

/--
info: 'LeanLLVM.Vellum.BitLanes.suffixRun_le' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.suffixRun_le

/--
info: 'LeanLLVM.Vellum.BitLanes.trailingRun_le' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.trailingRun_le

/--
info: 'LeanLLVM.Vellum.BitLanes.ite_not_add' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.ite_not_add

/--
info: 'LeanLLVM.Vellum.BitLanes.ctlz_not_eq_trailingRun' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.ctlz_not_eq_trailingRun

/--
info: 'LeanLLVM.Vellum.BitLanes.ctlz_zero' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.ctlz_zero

/--
info: 'LeanLLVM.Vellum.QuoteDerive.oneLane_getLsbD' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.oneLane_getLsbD

/--
info: 'LeanLLVM.Vellum.QuoteDerive.evenLanes_getLsbD' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.evenLanes_getLsbD

/--
info: 'LeanLLVM.Vellum.QuoteDerive.escapeLanes_getLsbD' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.escapeLanes_getLsbD

/--
info: 'LeanLLVM.Vellum.QuoteDerive.runStarts_getLsbD' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.runStarts_getLsbD

/--
info: 'LeanLLVM.Vellum.QuoteDerive.runEnds_getLsbD' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.runEnds_getLsbD

/--
info: 'LeanLLVM.Vellum.QuoteDerive.afterRuns_getLsbD' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.afterRuns_getLsbD

/--
info: 'LeanLLVM.Vellum.QuoteDerive.countBelow_succ' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.countBelow_succ

/--
info: 'LeanLLVM.Vellum.QuoteDerive.countBelow_mono' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.countBelow_mono

/--
info: 'LeanLLVM.Vellum.QuoteDerive.filter_singleton_length' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.filter_singleton_length

/--
info: 'LeanLLVM.Vellum.QuoteDerive.filter_true_eq' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.filter_true_eq

/--
info: 'LeanLLVM.Vellum.QuoteDerive.range_filter_lt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.range_filter_lt

/--
info: 'LeanLLVM.Vellum.QuoteDerive.range_filter_and_lt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.range_filter_and_lt

/--
info: 'LeanLLVM.Vellum.QuoteDerive.countBelow_eq_rank' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.countBelow_eq_rank

/--
info: 'LeanLLVM.Vellum.QuoteDerive.filter_map_eq' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.filter_map_eq

/--
info: 'LeanLLVM.Vellum.QuoteDerive.countBelow_shift' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.countBelow_shift

/--
info: 'LeanLLVM.Vellum.QuoteDerive.startsBelow_succ' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.startsBelow_succ

/--
info: 'LeanLLVM.Vellum.QuoteDerive.endsBelow_succ' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.endsBelow_succ

/--
info: 'LeanLLVM.Vellum.QuoteDerive.startsUpTo_end' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.startsUpTo_end

/--
info: 'LeanLLVM.Vellum.QuoteDerive.startsBelow_top' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.startsBelow_top

/--
info: 'LeanLLVM.Vellum.QuoteDerive.rank_runStarts' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.rank_runStarts

/--
info: 'LeanLLVM.Vellum.QuoteDerive.rank_runEnds' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.rank_runEnds

/--
info: 'LeanLLVM.Vellum.QuoteDerive.rank_afterRuns' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.rank_afterRuns

/--
info: 'LeanLLVM.Vellum.QuoteDerive.mod_two_eq_zero_or_one' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.mod_two_eq_zero_or_one

/--
info: 'LeanLLVM.Vellum.QuoteDerive.mod_two_succ_eq_one' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.mod_two_succ_eq_one

/--
info: 'LeanLLVM.Vellum.QuoteDerive.mod_two_succ_eq_zero' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.mod_two_succ_eq_zero

/--
info: 'LeanLLVM.Vellum.QuoteDerive.xor_not_right' does not depend on any axioms
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.xor_not_right

/--
info: 'LeanLLVM.Vellum.QuoteDerive.evenXor_add' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.evenXor_add

/--
info: 'LeanLLVM.Vellum.QuoteDerive.altLanes_getLsbD' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.altLanes_getLsbD

/--
info: 'LeanLLVM.Vellum.QuoteDerive.startPara_getLsbD' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.startPara_getLsbD

/--
info: 'LeanLLVM.Vellum.QuoteDerive.endPara_getLsbD' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.endPara_getLsbD

/--
info: 'LeanLLVM.Vellum.QuoteDerive.oddRuns_getLsbD' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.oddRuns_getLsbD

/--
info: 'LeanLLVM.Vellum.QuoteDerive.escapedRuns_getLsbD' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.escapedRuns_getLsbD

/--
info: 'LeanLLVM.Vellum.QuoteDerive.boundaryEscape_getLsbD' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.boundaryEscape_getLsbD

/--
info: 'LeanLLVM.Vellum.QuoteDerive.runParityBefore_start' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.runParityBefore_start

/--
info: 'LeanLLVM.Vellum.QuoteDerive.runParity_iterate' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.runParity_iterate

/--
info: 'LeanLLVM.Vellum.QuoteDerive.startLane_backslash' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.startLane_backslash

/--
info: 'LeanLLVM.Vellum.QuoteDerive.escape_at_run_end' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.escape_at_run_end

/--
info: 'LeanLLVM.Vellum.QuoteDerive.kernelEscape_of_clear' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.kernelEscape_of_clear

/--
info: 'LeanLLVM.Vellum.QuoteDerive.kernelEscape_of_set' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.kernelEscape_of_set

/--
info: 'LeanLLVM.Vellum.QuoteDerive.kernelEscape_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.kernelEscape_eq

/--
info: 'LeanLLVM.Vellum.QuoteDerive.kernelQuote_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.kernelQuote_eq

/--
info: 'LeanLLVM.Vellum.QuoteDerive.isQuoteB_and_isBackslashB' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.isQuoteB_and_isBackslashB

/--
info: 'LeanLLVM.Vellum.QuoteDerive.specQuote64_disjoint' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.specQuote64_disjoint

/--
info: 'LeanLLVM.Vellum.QuoteDerive.classCarryAt_oddRun_zero' does not depend on any axioms
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.classCarryAt_oddRun_zero

/--
info: 'LeanLLVM.Vellum.QuoteDerive.oddRun_lo' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.oddRun_lo

/--
info: 'LeanLLVM.Vellum.QuoteDerive.oddRun_hi' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.oddRun_hi

/--
info: 'LeanLLVM.Vellum.QuoteDerive.escapeLanes_eq_join' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.escapeLanes_eq_join

/--
info: 'LeanLLVM.Vellum.QuoteDerive.quoteMask_lo' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.quoteMask_lo

/--
info: 'LeanLLVM.Vellum.QuoteDerive.quoteMask_hi' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.quoteMask_hi

/--
info: 'LeanLLVM.Vellum.QuoteDerive.kernelQuote64' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.kernelQuote64

/--
info: 'LeanLLVM.Vellum.QuoteDerive.not_xor' does not depend on any axioms
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.not_xor

/--
info: 'LeanLLVM.Vellum.QuoteDerive.decide_succ_eq_succ' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.decide_succ_eq_succ

/--
info: 'LeanLLVM.Vellum.QuoteDerive.runParityBefore_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.runParityBefore_eq

/--
info: 'LeanLLVM.Vellum.QuoteDerive.suffixRun_eq_self_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.suffixRun_eq_self_iff

/--
info: 'LeanLLVM.Vellum.QuoteDerive.lzParity_eq_suffixRun' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.lzParity_eq_suffixRun

/--
info: 'LeanLLVM.Vellum.QuoteDerive.lzpc_getLsbD_zero' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.lzpc_getLsbD_zero

/--
info: 'LeanLLVM.Vellum.QuoteDerive.parity_top' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.parity_top

/--
info: 'LeanLLVM.Vellum.QuoteDerive.contrib_getLsbD_zero' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.contrib_getLsbD_zero

/--
info: 'LeanLLVM.Vellum.QuoteDerive.nextParity_getLsbD_zero' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.nextParity_getLsbD_zero

/--
info: 'LeanLLVM.Vellum.QuoteDerive.nextParity_getLsbD_of_pos' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.nextParity_getLsbD_of_pos

/--
info: 'LeanLLVM.Vellum.QuoteDerive.nextParity_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.nextParity_eq

/--
info: 'LeanLLVM.Vellum.QuoteDerive.ppn64' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.ppn64

/--
info: 'LeanLLVM.Vellum.QuoteDerive.nextParity_and_not_top' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.nextParity_and_not_top

/--
info: 'LeanLLVM.Vellum.QuoteDerive.topWord_eq_zero_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.topWord_eq_zero_iff

/--
info: 'LeanLLVM.Vellum.QuoteDerive.nextParity_ne_zero_imp_open' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.nextParity_ne_zero_imp_open

/--
info: 'LeanLLVM.Vellum.QuoteDerive.classStep_oddRun_gated' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.classStep_oddRun_gated

/--
info: 'LeanLLVM.Vellum.QuoteDerive.specCarry_hypothesis' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.specCarry_hypothesis

/--
info: 'LeanLLVM.Vellum.QuoteDerive.classState_self_open' does not depend on any axioms
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.QuoteDerive.classState_self_open


/-! #### Executed witness

The same block the specification's own witness uses — `"\""` and thirty-two spaces
in the low half, spaces in the high half — read through the kernel's instruction
sequence: the scattered parity marks lane 2, the escaped quote, and leaves lanes 0
and 3 as the string's boundaries, so `%qmc2` is `0b1001` and agrees with
`specQuote64`.  The block ends in a space, so neither side's outgoing parity is set.
-/

private def escapedQuoteBlock : Block32 :=
  fun i => match i.val with
    | 0 => 0x22
    | 1 => 0x5C
    | 2 => 0x22
    | 3 => 0x22
    | _ => 0x20

#guard kernelQuote (specMask64 IsQuoteB escapedQuoteBlock (fun _ => 0x20))
    (specMask64 IsBackslashB escapedQuoteBlock (fun _ => 0x20)) false false = 0b1001

#guard specQuote64 escapedQuoteBlock (fun _ => 0x20) ⟨false, false⟩ = 0b1001

-- The second number the negative witness below compares against, guarded here so that
-- its `≠` is a comparison of two guarded values rather than of one value and a literal.
#guard specQuote64 escapedQuoteBlock (fun _ => 0x20) ⟨false, true⟩ = 0b1000

#guard (kernelEscape (specMask64 IsBackslashB escapedQuoteBlock (fun _ => 0x20))
    false false).toNat % 4 = 0

#guard (nextParity (specMask64 IsBackslashB escapedQuoteBlock (fun _ => 0x20))
    false false).toNat = 0

example :
    kernelQuote (specMask64 IsQuoteB escapedQuoteBlock (fun _ => 0x20))
        (specMask64 IsBackslashB escapedQuoteBlock (fun _ => 0x20)) false false
      = specQuote64 escapedQuoteBlock (fun _ => 0x20) ⟨false, false⟩ :=
  kernelQuote64 _ _ _ _ _ rfl

-- The invariant is not decoration.  The same block with a state that claims an odd
-- run before the window while no run is open — `st.oddRun = true`, `%opennz` false —
-- is read differently: the specification's fold keeps lane 0 out of the unescaped
-- quotes (`0b1000`), while the kernel's boundary bit is gated by the run-open bit and
-- keeps it (`0b1001`).  The kernel never reaches that state, because `%ppnc2` implies
-- `%topc2`; the value below is the witness that the hypothesis carries content.
#guard kernelQuote (specMask64 IsQuoteB escapedQuoteBlock (fun _ => 0x20))
    (specMask64 IsBackslashB escapedQuoteBlock (fun _ => 0x20)) false false
  ≠ specQuote64 escapedQuoteBlock (fun _ => 0x20) ⟨false, true⟩
