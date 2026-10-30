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

The same `eutt` detector, frame, leaf postcondition and initial memories are
used for the affirmative timeout control and its four mismatches, then for the
divergence bounds and the loop/candidate instance.  The pins below are the
kernel's axiom footprints.
-/

open LeanLLVM
open LeanLLVM.ITree

section EuttChecks

/-- A fixed argument, so every check below uses one frame and postcondition. -/
abbrev checkX : BitVec 64 := 0x0123456789ABCDEF

abbrev checkFrame : Nat → Prop := loopFrame checkX

abbrev checkPost : Outcome → Outcome → Prop := LeanLLVM.Outcome.AgreesOutside (loopFrame checkX)

/-- The affirmative control: a budget timeout matches itself. -/
example : eutt checkFrame checkPost (timeoutT, ([] : Mem)) (timeoutT, ([] : Mem)) :=
  eutt_timeout_timeout checkFrame checkPost Empty.elim Empty.elim [] []

/-- A timeout is not a right undefined behaviour. -/
example : ¬ eutt checkFrame checkPost (timeoutT, ([] : Mem)) (ubT, ([] : Mem)) :=
  not_eutt_timeout_ub checkFrame checkPost Empty.elim Empty.elim [] []

/-- Nor is a left undefined behaviour a timeout. -/
example : ¬ eutt checkFrame checkPost (ubT, ([] : Mem)) (timeoutT, ([] : Mem)) :=
  not_eutt_ub_timeout checkFrame checkPost Empty.elim Empty.elim [] []

/-- A timeout is not a return. -/
example : ¬ eutt checkFrame checkPost (timeoutT, ([] : Mem))
    (ITree.ret (Outcome.ret (some (.int 64 0)) []), ([] : Mem)) :=
  not_eutt_timeout_ret checkFrame checkPost _ [] [] Empty.elim

/-- Nor is a return a timeout. -/
example : ¬ eutt checkFrame checkPost
    (ITree.ret (Outcome.ret (some (.int 64 0)) []), ([] : Mem)) (timeoutT, ([] : Mem)) :=
  not_eutt_ret_timeout checkFrame checkPost _ [] [] Empty.elim

/-- A right `ub` admits a completed left return. -/
example : eutt checkFrame checkPost
    (ITree.ret (Outcome.ret (some (.int 64 0)) []), ([] : Mem)) (ubT, ([] : Mem)) :=
  eutt_ret_ub checkFrame checkPost _ [] []

/-- A left `ub` node is not matched by a defined return. -/
example : ¬ eutt checkFrame checkPost (ubT, ([] : Mem))
    (ITree.ret (Outcome.ret (some (.int 64 0)) []), ([] : Mem)) :=
  not_eutt_ub_ret checkFrame checkPost _ [] [] [] Empty.elim

/-- Left silent divergence is the bottom against a return. -/
example : eutt checkFrame checkPost (ITree.infTau, ([] : Mem))
    (ITree.ret (Outcome.ret (some (.int 64 0)) []), ([] : Mem)) :=
  eutt_diverges_ret checkFrame checkPost _ [] []

/-- Right silent divergence is not admitted by a return. -/
example : ¬ eutt checkFrame checkPost
    (ITree.ret (Outcome.ret (some (.int 64 0)) []), ([] : Mem)) (ITree.infTau, ([] : Mem)) :=
  not_eutt_ret_diverges checkFrame checkPost _ [] []

/-- Both sides diverge silently, so the negative just above is not the whole
story: the same detector admits two silent divergences. -/
example : eutt checkFrame checkPost (ITree.infTau, ([] : Mem)) (ITree.infTau, ([] : Mem)) :=
  eutt_diverges_diverges checkFrame checkPost [] []

/-- Left silent divergence is related to a right `ub`. -/
example : eutt checkFrame checkPost (ITree.infTau, ([] : Mem)) (ubT, ([] : Mem)) :=
  eutt_diverges_ub checkFrame checkPost Empty.elim [] []

/-- The loop instance: the parsed loop as target, the unrolled candidate as
source, at the allocator-derived frame. -/
example (x : BitVec 64) : eutt (loopFrame x) (Outcome.AgreesOutside (loopFrame x))
    (loopTree x, ([] : Mem)) (candidateTree x, ([] : Mem)) :=
  loop_candidate_eutt x

/-- The same postcondition rejects a return whose memory differs at address
zero, outside the frame. -/
example (x : BitVec 64) (v : Option Value) :
    ¬ (Outcome.ret v [(0, 1)]).AgreesOutside (loopFrame x) (Outcome.ret v []) :=
  outcome_address_zero_rejected x v

end EuttChecks

/-! #### The UB terminal class

A `ret` leaf carrying `Outcome.ub` and a `vis Ev.ub` node are one terminal
class, and `post` never sees `ub`.  The absence check is paired with an
affirmative check under the same postcondition, so a detector that rejected
every return cannot pass it.
-/

section EuttUbChecks

/-- The postcondition under which every pair of outcomes is related. -/
abbrev checkPostTrue : Outcome → Outcome → Prop := fun _ _ => True

/-- The postcondition under which no pair of outcomes is related. -/
abbrev checkPostFalse : Outcome → Outcome → Prop := fun _ _ => False

/-- The affirmative control for the absence check below: under the same
postcondition, two `ret` leaves carrying the same defined outcome are related. -/
example : eutt checkFrame checkPostTrue
    (ITree.ret (Outcome.ret (some (.int 64 0)) []), ([] : Mem))
    (ITree.ret (Outcome.ret (some (.int 64 0)) []), ([] : Mem)) :=
  (eutt_ret_ret_iff checkFrame checkPostTrue _ _ _ _ _ _).mpr trivial

/-- A left `ret` leaf carrying `Outcome.ub` is not related to a defined `ret`
leaf, even when `post` holds of every pair. -/
example : ¬ eutt checkFrame checkPostTrue
    (ITree.ret Outcome.ub, ([] : Mem))
    (ITree.ret (Outcome.ret (some (.int 64 0)) []), ([] : Mem)) :=
  not_eutt_ret_ub_ret checkFrame checkPostTrue _ [] [] []

/-- A left `vis Ev.ub` node is absent from the same check, so the two shapes
behave alike on the left. -/
example : ¬ eutt checkFrame checkPostTrue (ubT, ([] : Mem))
    (ITree.ret (Outcome.ret (some (.int 64 0)) []), ([] : Mem)) :=
  not_eutt_ub_ret checkFrame checkPostTrue _ [] [] [] Empty.elim

/-- A right `ret` leaf carrying `Outcome.ub` admits a completed left return
even when `post` holds of no pair, which is what makes the UB admission
`post`-independent. -/
example : eutt checkFrame checkPostFalse
    (ITree.ret (Outcome.ret (some (.int 64 0)) []), ([] : Mem))
    (ITree.ret Outcome.ub, ([] : Mem)) :=
  eutt_ret_ub_terminal checkFrame checkPostFalse _ [] (UbTerminal.ret [])

/-- The two shapes are one class on both sides: `ret .ub` against `ret .ub`. -/
example : eutt checkFrame checkPostFalse
    (ITree.ret Outcome.ub, ([] : Mem)) (ITree.ret Outcome.ub, ([] : Mem)) :=
  eutt_ub_terminal checkFrame checkPostFalse (UbTerminal.ret []) (UbTerminal.ret [])

/-- `ret .ub` on the left against a `vis Ev.ub` node on the right. -/
example : eutt checkFrame checkPostFalse
    (ITree.ret Outcome.ub, ([] : Mem)) (ubT, ([] : Mem)) :=
  eutt_ub_terminal checkFrame checkPostFalse (UbTerminal.ret [])
    (UbTerminal.vis Empty.elim [])

/-- A `vis Ev.ub` node on the left against `ret .ub` on the right. -/
example : eutt checkFrame checkPostFalse
    (ubT, ([] : Mem)) (ITree.ret Outcome.ub, ([] : Mem)) :=
  eutt_ub_terminal checkFrame checkPostFalse (UbTerminal.vis Empty.elim [])
    (UbTerminal.ret [])

/-- And a `vis Ev.ub` node against itself. -/
example : eutt checkFrame checkPostFalse (ubT, ([] : Mem)) (ubT, ([] : Mem)) :=
  eutt_ub_ub checkFrame checkPostFalse Empty.elim Empty.elim [] []

/-- Neither shape is a timeout: a `ret` leaf carrying `Outcome.ub` is absent
from the timeout check exactly where the `vis Ev.ub` node is. -/
example : ¬ eutt checkFrame checkPostFalse (ITree.ret Outcome.ub, ([] : Mem))
    (timeoutT, ([] : Mem)) :=
  not_eutt_ret_timeout checkFrame checkPostFalse Outcome.ub [] [] Empty.elim

end EuttUbChecks

/-! #### Visible loads use the memories' canonical response

The load clause relates a visible load only when the two memories give the same
canonical response.  The checks below share one detector, one event, one
continuation and one frame, and differ only in the memories: equal defined
bytes, two undefined loads, and a disagreeing pair.  Address `0` is outside the
check frame, so the load stays visible instead of becoming a silent step.
-/

section EuttLoadChecks

open LeanLLVM
open LeanLLVM.ITree

/-- The continuation of the load checks: the same returned value and an empty
memory on both sides, so the postcondition is closed as soon as the event
matches. -/
abbrev loadK : Option Value → ITree.Tree Ev Outcome :=
  fun _ => ITree.ret (Outcome.ret (some (.int 8 1)) [])

/-- Address `0` lies outside the loop's band, so a load there is not silent. -/
theorem load_address_outside : ¬ InFrame checkFrame 0 (.int 8) := by
  intro hf
  have h : Band 1 17 0 := by simpa [checkFrame, loopFrame_eq] using hf 0 (by decide)
  simp [Band] at h

/-- The positive check's two memories give the same canonical response. -/
theorem load_value_equal :
    loadValue [(0, 1)] (.int 8) 0 = loadValue [(0, 1), (5, 9)] (.int 8) 0 := by
  decide

/-- The affirmative control's two memories are both undefined at the address. -/
theorem load_value_none :
    loadValue ([] : Mem) (.int 8) 0 = loadValue [(5, 9)] (.int 8) 0 := by
  decide

/-- The negative check's two memories disagree about the byte at the address. -/
theorem load_value_disagree :
    loadValue [(0, 1)] (.int 8) 0 ≠ loadValue [(0, 2)] (.int 8) 0 := by
  decide

/-- Equal defined responses: the same visible load matches at two different
memories, and the identical returns close the postcondition. -/
example : eutt checkFrame checkPost
    (ITree.vis (Ev.load 0 (.int 8)) loadK, ([(0, 1)] : Mem))
    (ITree.vis (Ev.load 0 (.int 8)) loadK, ([(0, 1), (5, 9)] : Mem)) := by
  refine (eutt_iff checkFrame checkPost _ _).mpr ?_
  refine EuttF.vis_load 0 (.int 8) loadK loadK (SilentHead.refl _ _)
    (SilentHead.refl _ _) load_value_equal (fun v => ?_)
  exact (eutt_ret_ret_iff checkFrame checkPost _ _ _ _ _ _).mpr
    (Outcome.agreesOutside_refl _ checkFrame)

/-- Two undefined loads are admitted as well: the affirmative control for the
negative below, under the same detector, event, continuation and frame. -/
example : eutt checkFrame checkPost
    (ITree.vis (Ev.load 0 (.int 8)) loadK, ([] : Mem))
    (ITree.vis (Ev.load 0 (.int 8)) loadK, ([(5, 9)] : Mem)) := by
  refine (eutt_iff checkFrame checkPost _ _).mpr ?_
  refine EuttF.vis_load 0 (.int 8) loadK loadK (SilentHead.refl _ _)
    (SilentHead.refl _ _) load_value_none (fun v => ?_)
  exact (eutt_ret_ret_iff checkFrame checkPost _ _ _ _ _ _).mpr
    (Outcome.agreesOutside_refl _ checkFrame)

/-- A disagreeing pair is refused by the same detector: the load is visible, so
the load clause is the only one that can match, and its response equality fails
on the two actual memories. -/
example : ¬ eutt checkFrame checkPost
    (ITree.vis (Ev.load 0 (.int 8)) loadK, ([(0, 1)] : Mem))
    (ITree.vis (Ev.load 0 (.int 8)) loadK, ([(0, 2)] : Mem)) :=
  not_eutt_load_of_disagree load_address_outside load_value_disagree

end EuttLoadChecks

/-! #### The bridge transports in the target-to-source direction

Two checks on the bridge itself: the fixed-budget transport applied to the
loop's completed run mentions the *matched* outcomes in its postcondition, and
a postcondition that holds of no pair is not manufactured, so the matched-return
disjunct is the postcondition's and not a silent success.
-/

section BridgeChecks

open LeanLLVM
open LeanLLVM.ITree

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
  eutt_runFuel_some noCalls (loopFrame x) (Outcome.AgreesOutside (loopFrame x))
    loopFunction candidateFunction [.int 64 x] 19 10000
    (Outcome.ret (some (.int 64 (spec x))) mem) (loop_candidate_eutt x) h19

/-- The postcondition is not bypassed: with a post that holds of no pair, two
defined returns are not related, so the bridge's matched-return disjunct cannot
be made of an unrelated pair. -/
example : ¬ eutt checkFrame (fun _ _ => False)
    (ITree.ret (Outcome.ret (some (.int 64 0)) []), ([] : Mem))
    (ITree.ret (Outcome.ret (some (.int 64 0)) []), ([] : Mem)) := by
  intro h
  exact (eutt_ret_ret_iff checkFrame (fun _ _ => False) _ _ _ _ _ _).mp h

end BridgeChecks

/-- info: 'LeanLLVM.ITree.eutt_exec_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.eutt_exec_some

/-- info: 'LeanLLVM.ITree.eutt_runFuel_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.eutt_runFuel_some

/-- info: 'LeanLLVM.ITree.eutt_beh_inclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.eutt_beh_inclusion

/-- info: 'LeanLLVM.ITree.refinesWithin_of_eutt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.refinesWithin_of_eutt

/-- info: 'LeanLLVM.ITree.refines_of_eutt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.refines_of_eutt

/-- info: 'LeanLLVM.ITree.not_eutt_load_of_disagree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.not_eutt_load_of_disagree

/-- info: 'LeanLLVM.ITree.loop_candidate_beh_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.loop_candidate_beh_bridge

/-- info: 'LeanLLVM.ITree.EuttF_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.EuttF_monotone

/-- info: 'LeanLLVM.ITree.eutt_silentHead_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.eutt_silentHead_left

/-- info: 'LeanLLVM.ITree.infTau_diverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.infTau_diverges

/-- info: 'LeanLLVM.ITree.not_silentDiverges_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.not_silentDiverges_ret

/-- info: 'LeanLLVM.ITree.eutt_ret_ret_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.eutt_ret_ret_iff

/-- info: 'LeanLLVM.ITree.not_eutt_ub_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.not_eutt_ub_ret

/-- info: 'LeanLLVM.ITree.not_eutt_ub_terminal_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.not_eutt_ub_terminal_ret

/-- info: 'LeanLLVM.ITree.not_eutt_ret_ub_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.not_eutt_ret_ub_ret

/-- info: 'LeanLLVM.ITree.eutt_ub_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.eutt_ub_terminal

/-- info: 'LeanLLVM.ITree.eutt_ret_ub_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.eutt_ret_ub_terminal

/-- info: 'LeanLLVM.ITree.eutt_diverges_diverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.eutt_diverges_diverges

/-- info: 'LeanLLVM.ITree.not_eutt_ret_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.not_eutt_ret_timeout

/-- info: 'LeanLLVM.ITree.not_eutt_timeout_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.not_eutt_timeout_ret

/-- info: 'LeanLLVM.ITree.not_eutt_timeout_ub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.not_eutt_timeout_ub

/-- info: 'LeanLLVM.ITree.not_eutt_ub_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.not_eutt_ub_timeout

/-- info: 'LeanLLVM.ITree.exec_runT' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.exec_runT

/-- info: 'LeanLLVM.ITree.loop_candidate_eutt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.loop_candidate_eutt

/-- info: 'LeanLLVM.ITree.outcome_address_zero_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.outcome_address_zero_rejected

/-- info: 'LeanLLVM.ITree.eutt_eq_plfp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.eutt_eq_plfp

/-- info: 'LeanLLVM.ITree.eutt_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.ITree.eutt_unfold
