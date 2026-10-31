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
