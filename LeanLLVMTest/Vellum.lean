import LeanLLVM

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

example : ¬ LeanLLVM.CallRefines (fun _ _ => none) (envFor swar) seamSymbol :=
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
-- the frame is not a framed refinement.
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
  simtt_runFuel_some noCalls (loopFrame x) (Outcome.AgreesOutside (loopFrame x))
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

/-! #### The correspondence and the axiom footprint -/

/-- The handled correspondence: the handler's memory is the semantics' memory,
so the canonical resolution of a `runHandled` tree is exactly `runFuel`. -/
example (frame : Nat → Prop) (n : Nat) (f : LeanLLVM.Function) (s : LeanLLVM.State) :
    HandledExec noCalls (runHandled noCalls frame n f s) (runFuel noCalls n f s) :=
  handled_runFuel noCalls frame n f s

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
