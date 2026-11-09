import LeanLLVM
import LeanLLVM.Vellum.JsonEntrySteps
import LeanLLVM.Vellum.JsonScanABI
import LeanLLVM.Vellum.JsonScanModel
import LeanLLVM.Vellum.JsonScanIR
import LeanLLVM.Vellum.JsonScanLane
import LeanLLVM.Vellum.JsonScanSpec
import LeanLLVM.Vellum.Pclmul
import LeanLLVM.Vellum.JsonS1MasksSteps
import LeanLLVM.Vellum.JsonB8Steps
import LeanLLVM.Vellum.JsonUnitContracts
import LeanLLVM.Vellum.JsonEscapeSpec
import LeanLLVM.Vellum.JsonEscapeSteps

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



/-! ### The stage-1 classification masks

The kernel's five-word environment, the two usability corollaries, and — below,
with the theorem they are stated for — the public results of the stage-1 mask
unit.  Every pin is `[propext, Quot.sound]` or narrower; `s1_masks_decompose`
carries no `Classical.choice` because it is a bit-level identity about bytes.
-/

/-- info: 'LeanLLVM.Vellum.JsonS1MasksIR.s1_masks_decompose' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksIR.s1_masks_decompose

/-- info: 'LeanLLVM.Vellum.JsonS1MasksIR.s1_masks_candidate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksIR.s1_masks_candidate

/-! ### The stage-1 mask unit's step corpus

The emitted body's execution is stated at an opaque environment, with each
instruction's operands as hypotheses; the composition conses onto a chain ending in
a variable.  The pins record that the shape carries no extra axiom: `s1_chain6`,
the six-step witness, is `[propext, Quot.sound]` only.
-/

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.denoteCode_cons_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.denoteCode_cons_of

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_step9' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_step9

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_step10' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_step10

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_chain6' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_chain6

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_load0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_load0

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_ptr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_ptr

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_load1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_load1

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_chain3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_chain3

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.withEnv' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.withEnv

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.backLo' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.backLo

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.backHi' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.backHi

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.backLo_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.backLo_length

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.backHi_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.backHi_length

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_bitcast2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_bitcast2

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_bitcast3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_bitcast3

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_shuffle4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_shuffle4

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_bitcast5' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_bitcast5

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_icmp6' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_icmp6

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_quote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_quote

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_quoteChain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_quoteChain

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_backLoCmp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_backLoCmp

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_backLoMask' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_backLoMask

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_zext9' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_zext9

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_backHiCmp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_backHiCmp

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_backHiMask' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_backHiMask

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_zext12' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_zext12

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_shl13' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_shl13

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_or14' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_or14

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.conv9W' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.conv9W

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.conv12W' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.conv12W

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.shl13W' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.shl13W

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.or14W' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.or14W

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.isBackslashB_lane_bv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.isBackslashB_lane_bv

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.isBackslashB_lane' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.isBackslashB_lane

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.backLo_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.backLo_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.backHi_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.backHi_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.backLoW_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.backLoW_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.backHiW_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.backHiW_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.backLo_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.backLo_lt

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.backHi_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.backHi_lt

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.ofNat32_toNat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.ofNat32_toNat

/-- info: 'LeanLLVM.Vellum.JsonS1MasksIR.backslashWord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksIR.backslashWord

/-- info: 'LeanLLVM.Vellum.JsonS1MasksIR.ofNat_lanesToNat_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksIR.ofNat_lanesToNat_join

/-- info: 'LeanLLVM.Vellum.JsonS1MasksIR.zipReplicate_getElem?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksIR.zipReplicate_getElem?

/-- info: 'LeanLLVM.Vellum.JsonS1MasksIR.ofBool_eq_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksIR.ofBool_eq_one

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.mul_pow' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.mul_pow

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.conv9W_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.conv9W_toNat

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.conv12W_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.conv12W_toNat

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.shl13W_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.shl13W_toNat

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.or14W_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.or14W_comm

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_backslash_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_backslash_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.isQuoteB_lane_bv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.isQuoteB_lane_bv

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.isQuoteB_lane' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.isQuoteB_lane

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.isQuoteB_iff_bv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.isQuoteB_iff_bv

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.isQuoteB_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.isQuoteB_iff

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_quote_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_quote_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksIR.controlLanes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksIR.controlLanes

/-- info: 'LeanLLVM.Vellum.JsonS1MasksIR.ofBool_eq_one_bool' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksIR.ofBool_eq_one_bool

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.isControlB_iff_bv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.isControlB_iff_bv

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.isControlB_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.isControlB_iff

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_control_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_control_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksIR.loTab16' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksIR.loTab16

/-- info: 'LeanLLVM.Vellum.JsonS1MasksIR.hiTab16' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksIR.hiTab16

/-- info: 'LeanLLVM.Vellum.JsonS1MasksIR.tabAnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksIR.tabAnd

/-- info: 'LeanLLVM.Vellum.JsonS1MasksIR.tabAnd_delim_bv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksIR.tabAnd_delim_bv

/-- info: 'LeanLLVM.Vellum.JsonS1MasksIR.tabAnd_space_bv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksIR.tabAnd_space_bv

/-- info: 'LeanLLVM.Vellum.JsonS1MasksIR.tabAnd_delim' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksIR.tabAnd_delim

/-- info: 'LeanLLVM.Vellum.JsonS1MasksIR.tabAnd_space' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksIR.tabAnd_space

/-- info: 'LeanLLVM.Vellum.JsonS1MasksIR.split16' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksIR.split16

/-- info: 'LeanLLVM.Vellum.JsonS1MasksIR.split16'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksIR.split16'

/-- info: 'LeanLLVM.Vellum.JsonS1MasksIR.getD_two_copies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksIR.getD_two_copies

/-- info: 'LeanLLVM.Vellum.JsonS1MasksIR.pshufbLanes_two_copies_lane' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksIR.pshufbLanes_two_copies_lane

/-- info: 'LeanLLVM.Vellum.JsonS1MasksIR.bitcastVecLanes_unpackLanes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksIR.bitcastVecLanes_unpackLanes




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


/-! ### The table region, the nibble arithmetic and the delimiter word

The pins below cover the helper list — the step lemmas, the composition lemmas and
the lane-to-word bridge — together with the nibble arithmetic the table region rests
on and the delimiter word's identity.  Every one is at the standard footprint
`[propext, Quot.sound]` or narrower; a widened one fails elaboration.

Two core lemmas the first draft reached for carry `Classical.choice` and are not used
here: `Nat.mod_mul_right_div_self` (replaced by `mod_mul_div`, derived from
`Nat.mod_add_div`, `Nat.add_mul_mod_self_left`, `Nat.add_mul_div_left`,
`Nat.mod_eq_of_lt` and `Nat.div_eq_of_lt`) and `BitVec.getLsbD_allOnes` (replaced by
the `~~~x` route through `BitLanes.getLsbD_not_of_lt`).  The pins for those two
replacements and their consumers are what hold that repair in place. -/

/-- info: 'LeanLLVM.Vellum.JsonS1MasksIR.evalInstr_binopVec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksIR.evalInstr_binopVec

/-- info: 'LeanLLVM.Vellum.JsonS1MasksIR.zipReplicate_getElem?_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksIR.zipReplicate_getElem?_len

/-- info: 'LeanLLVM.Vellum.JsonS1MasksIR.zipReplicate_map' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksIR.zipReplicate_map

/-- info: 'LeanLLVM.Vellum.JsonS1MasksIR.zipReplicate_mapM' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksIR.zipReplicate_mapM

/-- info: 'LeanLLVM.Vellum.JsonS1MasksIR.mapM_some_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksIR.mapM_some_map

/-- info: 'LeanLLVM.Vellum.JsonS1MasksIR.evalOperands_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksIR.evalOperands_cons

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.unpackLanes_getElem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.unpackLanes_getElem

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.unpackLanes_getElem_toNat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.unpackLanes_getElem_toNat

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.mod_pow16_div16' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.mod_pow16_div16

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.lane_shr4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.lane_shr4

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.shr4Lanes_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.shr4Lanes_length

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.shr4Lanes_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.shr4Lanes_getD

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.shr4_mod_even' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.shr4_mod_even

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.shr4_mod_odd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.shr4_mod_odd

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.packLanes_shr4_mod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.packLanes_shr4_mod

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.and15_eq_mod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.and15_eq_mod

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.nibbleLanes_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.nibbleLanes_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.loTabV_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.loTabV_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.hiTabV_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.hiTabV_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_bitcastHalf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_bitcastHalf

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_shr4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_shr4

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_andNib' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_andNib

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_pshufb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_pshufb

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_bitcast8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_bitcast8

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_andHiNib' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_andHiNib

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_andTables' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_andTables

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_and63' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_and63

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_icmpEq0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_icmpEq0

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_icmpUlt64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_icmpUlt64

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_bitcastMask32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_bitcastMask32

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_compl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_compl

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.ofNat32_toNat'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.ofNat32_toNat'

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.complW_getLsbD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.complW_getLsbD

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.getD_map' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.getD_map

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.zip_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.zip_getD

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.andLanes_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.andLanes_getD

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.nibLanes_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.nibLanes_getD

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.sLanes_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.sLanes_getD

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.nibLanes_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.nibLanes_length

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.sLanes_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.sLanes_length

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.pshufbLanes_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.pshufbLanes_length

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.andLanes_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.andLanes_length

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.getLsbD7_of_lt16' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.getLsbD7_of_lt16

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.hiNibbleLanes_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.hiNibbleLanes_length

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.hiNibbleLanes_getD' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.hiNibbleLanes_getD

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.loLanes_getD_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.loLanes_getD_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.loLanes_getD_loWord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.loLanes_getD_loWord

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.loLanes_hiNibble' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.loLanes_hiNibble

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.tabLoLanes_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.tabLoLanes_getD

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.tabHiLanes_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.tabHiLanes_getD

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.tabLanes_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.tabLanes_length

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.andWordLanes_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.andWordLanes_getD

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.hiNibbleLanes_toNat_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.hiNibbleLanes_toNat_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.sWordLanes_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.sWordLanes_getD

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.sWordLanes_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.sWordLanes_length

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.cmpWordLanes_getElem?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.cmpWordLanes_getElem?

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.bool_not_decide' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.bool_not_decide

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.lanesToNat_testBit_bool' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.lanesToNat_testBit_bool

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.loToBitVec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.loToBitVec

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.add_rotate' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.add_rotate

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.mod_mul_div' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.mod_mul_div

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.delimLoW_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.delimLoW_eq


/-! ### The high half's table region

Every lemma below is its low-half counterpart at `hiWord`/`hiLanes`, and each holds the
same footprint as the lemma it mirrors — the mirror introduced no widening. -/

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.hiLanes_getD_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.hiLanes_getD_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.hiLanes_getD_hiWord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.hiLanes_getD_hiWord

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.hiLanes_hiNibble' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.hiLanes_hiNibble

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.tabLoLanesHi_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.tabLoLanesHi_getD

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.tabHiLanesHi_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.tabHiLanesHi_getD

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.tabLanesHi_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.tabLanesHi_length

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.andWordLanesHi_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.andWordLanesHi_getD

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.hiNibbleLanes_toNat_eq_hi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.hiNibbleLanes_toNat_eq_hi

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.sWordLanesHi_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.sWordLanesHi_getD

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.sWordLanesHi_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.sWordLanesHi_length

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.cmpWordLanesHi_getElem?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.cmpWordLanesHi_getElem?

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.delimHiW_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.delimHiW_eq


/-! ### The join and the delimiter identity

`s1_delimiter_eq` is the first of the milestone's six mask identities stated at the
kernel's units: the body's `%or5.i.i`, read as a natural, is the specification's
`IsDelimB` mask over the block.  `joinW_toNat` is the join it rides on, and it is
where the operand order is settled at the `BitVec` level rather than by `Nat.lor`
commutativity — which this core does not carry. -/

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.joinW_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.joinW_toNat

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_delimiter_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_delimiter_eq


/-! ### The whitespace word's low half

`wsLoW_eq` is the fifth of the six mask identities at the half's units; the block's
`joinW` and the high-half mirror are what make it `s1_whitespace_eq` at sixty-four
lanes.  `not_ult64_bv` is the per-byte link `!(x < 64) = (x &&& 0xC0 ≠ 0))` — the
emission's `ult 64` against the table's bits six and seven. -/

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.andWordLanes_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.andWordLanes_length

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.ult64Lanes_getElem?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.ult64Lanes_getElem?

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.andWordLanes_eq_tabAnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.andWordLanes_eq_tabAnd

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.not_ult64_bv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.not_ult64_bv

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.wsLoW_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.wsLoW_eq


/-! ### The whitespace identity

`s1_whitespace_eq` is the fifth of the six mask identities at the kernel's units: the
body's `%or.i.i`, read as a natural, is the specification's `IsSpaceB` mask over the
block.  It is the delimiter's skeleton with `ult 64` in place of the `&&& 0x3F`
equality, so the high half is three declarations rather than a second development. -/

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.andWordLanesHi_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.andWordLanesHi_length

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.andWordLanesHi_eq_tabAnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.andWordLanesHi_eq_tabAnd

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.wsHiW_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.wsHiW_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_whitespace_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_whitespace_eq

/-! ### The escape region

`s1f_escaped`'s arithmetic: the run starts and ends, the parity alternate, the two
gathers, the scatter and the boundary lane, then `%or15.i.i` identified with
`QuoteDerive`'s `kernelEscape`.  Each word is `[propext, Quot.sound]` or narrower —
the `bv` truncation, the lane helpers and the identity included.
-/

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.bv_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.bv_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.bv_toNat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.bv_toNat

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.ofNat_toNat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.ofNat_toNat

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.xor_allOnes_eq_not' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.xor_allOnes_eq_not

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.oneLane_and' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.oneLane_and

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.and_oneLane' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.and_oneLane

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.oneLane_and_not' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.oneLane_and_not

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.oneW_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.oneW_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.and_oneW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.and_oneW

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.evenLanes_literal' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.evenLanes_literal

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.evenC_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.evenC_eq

/-! ### The escape words' own equations

Each `…W_eq` states a word as the body composes it without `evalInstr`'s
truncation, and each is consumed by one of the identities pinned below.  Pinning
the word equations is what keeps a widening in a step's value from reaching those
identities without a red pin of its own.
-/

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.bsW_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.bsW_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escShlW_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escShlW_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escOr62W_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escOr62W_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escNotW_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escNotW_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escAndStartsW_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escAndStartsW_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escAnd1W_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escAnd1W_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escAnd2W_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escAnd2W_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escOr3W_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escOr3W_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escShrW_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escShrW_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escNot4W_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escNot4W_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escAnd5W_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escAnd5W_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escShl6W_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escShl6W_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escAnd7W_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escAnd7W_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escXorEvenW_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escXorEvenW_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escPext1W_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escPext1W_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escPext2W_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escPext2W_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escXor36W_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escXor36W_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escNot10W_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escNot10W_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escPdepW_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escPdepW_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escNot12W_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escNot12W_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escAnd39W_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escAnd39W_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escAnd14W_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escAnd14W_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escapedWord_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escapedWord_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escXor25W_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escXor25W_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escAnd26W_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escAnd26W_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.openW_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.openW_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.pparW_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.pparW_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.natToBytes_bit' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.natToBytes_bit

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.loadValue_int64' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.loadValue_int64

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.bv1_zero_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.bv1_zero_one

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.nat32' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.nat32

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.ofNat_conv9' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.ofNat_conv9

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.ofNat_shl13' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.ofNat_shl13

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.shl13_lane0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.shl13_lane0

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.or14W_lane0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.or14W_lane0

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escAnd1W_lane' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escAnd1W_lane

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escAnd2W_lane' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escAnd2W_lane

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escRunStarts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escRunStarts

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escRunEnds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escRunEnds

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escAfterRuns' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escAfterRuns

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escAlt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escAlt

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escOddRuns' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escOddRuns

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escEscapedRuns' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escEscapedRuns

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escBoundary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escBoundary

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escapedWord_eq_kernelEscape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escapedWord_eq_kernelEscape

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.bsW_eq_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.bsW_eq_spec

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escaped_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escaped_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escGep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escGep

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escShl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escShl

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escOpenLoad' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escOpenLoad

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escOr62' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escOr62

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escNot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escNot

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escAndStarts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escAndStarts

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escAnd1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escAnd1

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escAnd2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escAnd2

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escOr3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escOr3

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escShr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escShr

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escNot4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escNot4

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escAnd5' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escAnd5

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escShl6' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escShl6

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escPparLoad' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escPparLoad

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escAnd7' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escAnd7

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escXorEven' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escXorEven

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escPext1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escPext1

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escPext2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escPext2

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escXor36' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escXor36

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escNot10' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escNot10

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escPdep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escPdep

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escCmp63' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escCmp63

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escTobool' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escTobool

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escOrCond' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escOrCond

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escCond24' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escCond24

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escNot17' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escNot17

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escCtlz' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escCtlz

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escShr16' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escShr16

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escNot12' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escNot12

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escAnd39' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escAnd39

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escAnd14' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escAnd14

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escOr15' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escOr15

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escXor25' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escXor25

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_escAnd26' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_escAnd26

/-! ### The unescaped-quote and in-string words

`%and.i` — the raw quote word without the escapes — is `specQuote64`, and
`%xor.i` — the block's carry-less product XOR the carry slot's word — is
`specInString64`.  The `classWindow`-level algebra that separates the two is
`quoteMask_and_not_escaped`; every pin here is `[propext, Quot.sound]` or narrower.
-/

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.isUnescapedQuote_and_isEscapedQuote' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.isUnescapedQuote_and_isEscapedQuote

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.quote_and_not_escaped_lane' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.quote_and_not_escaped_lane

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.quoteMask_and_not_escaped' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.quoteMask_and_not_escaped

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.qrawW_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.qrawW_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.notEscW_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.notEscW_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.andQuoteW_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.andQuoteW_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_and_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_and_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.andQuoteW_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.andQuoteW_spec

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_andNotEsc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_andNotEsc

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_andQuote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_andQuote

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_vecInit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_vecInit

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_pclmul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_pclmul

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_vecext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_vecext

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_imGep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_imGep

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.seedBytes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.seedBytes

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_imLoad' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_imLoad

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_inString' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_inString

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_imSign' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_imSign

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_instring_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_instring_eq

/-! ### The joins, the control word and the stores

The two `zext`/`shl`/`or` joins are stated once, parametrically in the destination
and the word, and the join word is `joinW`; the control word is the quote word's
shape at `ult 0x20`; the six stores are two parametric steps.  All
`[propext, Quot.sound]` or narrower.
-/

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.bv32' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.bv32

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.bv32_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.bv32_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.shiftLeft_toNat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.shiftLeft_toNat

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.shlJoin_hr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.shlJoin_hr

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.or_bv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.or_bv

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.orJoin_hr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.orJoin_hr

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_zextJoin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_zextJoin

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_shlJoin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_shlJoin

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_orJoin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_orJoin

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.joinBody_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.joinBody_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_wsJoin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_wsJoin

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_delimJoin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_delimJoin

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_shuffle9' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_shuffle9

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_bitcast10' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_bitcast10

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_icmp11' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_icmp11

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_storeInt64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_storeInt64

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_storeVec1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_storeVec1

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_wsGep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_wsGep

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_ctlGep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_ctlGep

/-! ### The unit's `ub` case, and the memory facts the readback needs

`s1_masks_undefined_of_no_read`: a block that is absent across the whole 64 bytes
the body reads reaches `ub` — at the first load when its half is the absent one,
at the second load when that one is.  With it, the two `readBytes` facts the slot
readback rests on (a read above a written range, and two consecutive reads
composing).  All `[propext, Quot.sound]` or narrower.
-/

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.denoteCode_cons_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.denoteCode_cons_none

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1MasksInstrs_three' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1MasksInstrs_three

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_load0_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_load0_none

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_load0_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_load0_bytes

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_load1_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_load1_none

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.step_s1Masks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.step_s1Masks

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_masks_undefined_of_no_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_masks_undefined_of_no_read

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.readByte_writeBytes_above' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.readByte_writeBytes_above

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.readBytes_writeBytes_above' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.readBytes_writeBytes_above

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.readBytes_app' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.readBytes_app

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.readBytes_second_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.readBytes_second_none

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_wsGep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_wsGep

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_ctlGep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_ctlGep

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_delimGep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_delimGep

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_inStringGep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_inStringGep

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_backslashGep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_backslashGep

/-! ### The composed run, its readback and the six stored words

`s1_run` is the body composed instruction by instruction, and `s1_runFuel` reads
it as one control step.  The slot readback turns each of its nine writes into a
read at the address the write is at, the six `_spec` lemmas identify those words
with the specification's masks, and `s1Slot_outside` is the byte sweep for the
bytes in neither slot.  All `[propext, Quot.sound]` or narrower; `withEnv_mem` is
a projection and carries no axiom at all.
-/

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_run

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_runFuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_runFuel

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.withEnv_mem' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.withEnv_mem

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.or5W_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.or5W_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.orWsW_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.orWsW_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.controlLanes_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.controlLanes_length

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.readImCarry_after_stores' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.readImCarry_after_stores

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.readBytes_slot_same' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.readBytes_slot_same

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.readBytes_slot_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.readBytes_slot_below

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.readBytes_slot_above' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.readBytes_slot_above

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.readByte_slot_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.readByte_slot_outside

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_quote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_quote

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_delim' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_delim

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_instring' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_instring

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_space' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_space

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_backslash' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_backslash

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_control

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_open' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_open

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_ppar' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_ppar

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_im' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_im

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_carry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_carry

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.specDelimiter64_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.specDelimiter64_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.specBackslash64_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.specBackslash64_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.specSpace64_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.specSpace64_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.specControl64_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.specControl64_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.packLanes_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.packLanes_control

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_quote_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_quote_spec

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_delim_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_delim_spec

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_instring_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_instring_spec

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_space_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_space_spec

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_backslash_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_backslash_spec

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_control_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_control_spec

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_outside

/-! ### The outgoing carry

`carry64_oddRun_eq` and `carry64_inside_eq` read the specification's outgoing
carry at the body's own units — the lane recursion, and bit 63 of the carry-less
product — and `runParityBefore_eq` is that recursion in closed form, so the
trailing run and the incoming parity are the only things it depends on.
`s1_open_spec` is the first of the body's three carry words.  All
`[propext, Quot.sound]` or narrower.
-/

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.carry64_oddRun_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.carry64_oddRun_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.carry64_inside_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.carry64_inside_eq

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.div_pow_two_mod_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.div_pow_two_mod_two

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_open_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_open_spec

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.flipBits_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.flipBits_succ

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.succ_mod_two_test' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.succ_mod_two_test

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.runParityBefore_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.runParityBefore_eq

/-! ### The outgoing carry, the slot-order mirror, and the terminal theorem

The carry slot's three words are `s1_open_spec`, `s1_ppar_spec` and
`s1_inside_spec`, and `s1_masks_refines` assembles the run, the six mask clauses,
the carry triple and the outside sweep.  Every one of these is `[propext,
Quot.sound]` or narrower **except** the three that read the sign word, which carry
`Classical.choice` through this core's bit-to-magnitude bridge:
`sshiftRight_63`, `s1_inside_spec`, and so `s1_masks_refines`.  The pins state that
footprint rather than claiming the narrower one.
-/

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escCtlz_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escCtlz_toNat

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escShr16_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escShr16_toNat

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.oneLane_toNat' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.oneLane_toNat

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.oneLane_eq_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.oneLane_eq_zero

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escCmp63L_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escCmp63L_one

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escToboolL_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escToboolL_one

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escOrCondL_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escOrCondL_one

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.escCond24_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.escCond24_toNat

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.suffixRun_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.suffixRun_full

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.eq_allOnes_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.eq_allOnes_iff

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.trailingRun_eq_64_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.trailingRun_eq_64_iff

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.trailingRun_eq_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.trailingRun_eq_zero

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.flipBits_64' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.flipBits_64

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_ppar_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_ppar_spec

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_open_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_open_below

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_ppar_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_ppar_below

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_im_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_im_below

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_carry_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1Slot_carry_below

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.slotTake' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.slotTake

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.slotDrop' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.slotDrop

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.blockTake' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.blockTake

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.blockDrop' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.blockDrop

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.sshiftRight_63' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.sshiftRight_63

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_inside_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_inside_spec

/-- info: 'LeanLLVM.Vellum.JsonS1MasksSteps.s1_masks_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonS1MasksSteps.s1_masks_refines

/-! ### The entry word and its tail

Both statements are over the block layer's own masks and consume no step lemma,
so both are at the ceiling with no carrier.  `entry_mask_eq` rests on
`BitLanes.getLsbD_not_of_lt`; the tail's proof rests on three further `BitLanes`
lane facts (`testBit_two_pow_sub_one`, `allOnes_getLsbD_of_lt` and
`ctpop_eq_setLanes_length`), the first two proved there without the
`Classical.choice` that `Nat.testBit_two_pow_sub_one` and
`BitVec.getLsbD_allOnes` carry, so the pins below hold each of those facts where
it is. -/

/-- info: 'LeanLLVM.Vellum.JsonScanSpec.entry_mask_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonScanSpec.entry_mask_eq

/-- info: 'LeanLLVM.Vellum.JsonEntryIR.entry_tail_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntryIR.entry_tail_eq

/-- info: 'LeanLLVM.Vellum.BitLanes.getLsbD_not_of_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.getLsbD_not_of_lt

/-- info: 'LeanLLVM.Vellum.BitLanes.testBit_two_pow_sub_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.testBit_two_pow_sub_one

/-- info: 'LeanLLVM.Vellum.BitLanes.allOnes_getLsbD_of_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.allOnes_getLsbD_of_lt

/-! ### The entry unit's step corpus

**The `Classical.choice` these pins report is none of the three carriers the
stage-1 pins name** (`sshiftRight_63`, `s1_inside_spec`, `s1_masks_refines`):
none of them is consumed here. It is introduced by the entry lemmas' own proof
terms, and the pins below name the declaration that introduced it rather than a
single origin, because the entry corpus has more than one:

* `step_gep64` widens in its own proof term — measured at
  `[propext, Classical.choice, Quot.sound]` while each of its dependencies
  (`evalInstr_gep`, `evalOperand_reg_of`, `Ty.sizeBytes`) is clean — through a
  `Classical.propDecidable`-discharged `Decidable` inside it. Every pin that
  steps a `getelementptr` reaches the choice there.
* `findBlock_pos8Body`, `findBlock_pos8Groups`, `findBlock_pos8Advance` and
  `findBlock_pos8Exit` each widen in their own proof terms, independently of
  `step_gep64`; `findBlock_pos8Entry` reaches nothing beyond `propext`. A pin
  that steps through a block lookup names the lookup it consumed —
  `pos8Exit_step`, for instance, reports the choice from `findBlock_pos8Exit`.

`entry_pos8_refines`'s footprint, and the footprint of every helper it consumes,
is `[propext, Quot.sound]` plus those carriers and the two `BitLanes` lane facts
the intrinsic calls resolve through (`ctpop_eq_setLanes_length` and
`cttz_eq_head`), which the pins below keep where they are. -/

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.entry_pos8_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.entry_pos8_refines

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.pos8_loop_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.pos8_loop_run

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.pos8Groups_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.pos8Groups_run

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.pos8Body_step_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.pos8Body_step_zero

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.pos8Body_step_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.pos8Body_step_pos

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.pos8Groups_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.pos8Groups_step

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.pos8Cleanup_step_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.pos8Cleanup_step_last

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.pos8Cleanup_step_more' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.pos8Cleanup_step_more

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.pos8Exit_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.pos8Exit_step

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.pos8Entry_step_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.pos8Entry_step_zero

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.pos8Entry_step_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.pos8Entry_step_pos

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.pos8MemFold_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.pos8MemFold_read

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.pos8MemFold_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.pos8MemFold_frame

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.pos8Stream_eq_positions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.pos8Stream_eq_positions

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.pos8Stream_eq_streamPrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.pos8Stream_eq_streamPrefix

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.blockMem_frame_tight' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.blockMem_frame_tight

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.blockStore_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.blockStore_frame

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.readBytes_wordsOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.readBytes_wordsOf

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.denoteCode_params' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.denoteCode_params

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.pos8_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.pos8_init

/-! The carriers themselves, at the footprint each introduces.  `step_gep64` and
the four block lookups `findBlock_pos8Body`, `findBlock_pos8Groups`,
`findBlock_pos8Advance` and `findBlock_pos8Exit` widen in their own proof terms,
independently of one another; `findBlock_pos8Entry` reaches nothing beyond
`propext`.  Every pin in this section that reports `Classical.choice` names the
declaration it reached, and these pins hold those declarations where they are. -/

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.step_gep64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.step_gep64

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.findBlock_pos8Entry' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.findBlock_pos8Entry

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.findBlock_pos8Body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.findBlock_pos8Body

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.findBlock_pos8Groups' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.findBlock_pos8Groups

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.findBlock_pos8Advance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.findBlock_pos8Advance

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.findBlock_pos8Exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.findBlock_pos8Exit

/-! The two lane facts the entry theorem's intrinsic calls resolve to, held at
the ceiling recorded for them: `ctpop_eq_setLanes_length` at
`[propext, Quot.sound]`, `cttz_eq_head` at `[propext]`. -/

/-- info: 'LeanLLVM.Vellum.BitLanes.ctpop_eq_setLanes_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.ctpop_eq_setLanes_length

/-- info: 'LeanLLVM.Vellum.BitLanes.cttz_eq_head' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.cttz_eq_head

/-! The UTF-8 stage's two instructions, at the footprint their facts hold
without a carrier: the saturating subtract's two cases and the zero test's two
answers are decided by the byte comparison and the and-word, not by a choice. -/

/-- info: 'LeanLLVM.Vellum.BitLanes.subsSat_of_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.subsSat_of_le

/-- info: 'LeanLLVM.Vellum.BitLanes.subsSat_of_gt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.subsSat_of_gt

/-- info: 'LeanLLVM.Vellum.BitLanes.ptestz_eq_one_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.ptestz_eq_one_iff

/-- info: 'LeanLLVM.Vellum.BitLanes.ptestz_eq_zero_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.ptestz_eq_zero_iff

/-! The lane algebra: the twenty-seven declarations the `BitLanes` section at the
end of that module adds — five distribution, four packing, six fold-and-lane, two
zero-and-reduce, one zero-lane identity, five `i8`, and four controls, which is
23 + 4 — in declaration order, with the count on each heading so the composition is
read off the block rather than reconstructed from it.  The seven `private` helpers
of that section are outwith this count: they cannot be named from another file and
so are not pinned.  Every one of the twenty-seven is at the module's
ceiling — `[propext, Quot.sound]` — except `zipWith_zero_right` and
`packLanes_eq_zero_iff_control`, which report `[propext]` alone (list induction and
a closed `decide`, respectively).  A carrier appearing here would mean a lane fact
was proved through a core lemma that carries one, and the module's docstring names
the two routes it is allowed to take to the all-ones word — so the pin, not the
docstring, is what holds it. -/

/-! #### Distribution: the word cut at a lane (5) -/

/-- info: 'LeanLLVM.Vellum.BitLanes.unpackLanes_or' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.unpackLanes_or

/-- info: 'LeanLLVM.Vellum.BitLanes.unpackLanes_and' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.unpackLanes_and

/-- info: 'LeanLLVM.Vellum.BitLanes.unpackLanes_xor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.unpackLanes_xor

/-- info: 'LeanLLVM.Vellum.BitLanes.unpackLanes_allOnes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.unpackLanes_allOnes

/-- info: 'LeanLLVM.Vellum.BitLanes.unpackLanes_not' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.unpackLanes_not

/-! #### Packing: the list read back from the word (4) -/

/-- info: 'LeanLLVM.Vellum.BitLanes.packLanes_zipWith_or' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.packLanes_zipWith_or

/-- info: 'LeanLLVM.Vellum.BitLanes.packLanes_zipWith_and' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.packLanes_zipWith_and

/-- info: 'LeanLLVM.Vellum.BitLanes.packLanes_zipWith_xor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.packLanes_zipWith_xor

/-- info: 'LeanLLVM.Vellum.BitLanes.packLanes_map_not' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.packLanes_map_not

/-! #### The lane operations and the bitwise folds (6) -/

/-- info: 'LeanLLVM.Vellum.BitLanes.getLsbD_or_eq_false_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.getLsbD_or_eq_false_iff

/-- info: 'LeanLLVM.Vellum.BitLanes.getLsbD_and_eq_true_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.getLsbD_and_eq_true_iff

/-- info: 'LeanLLVM.Vellum.BitLanes.getLsbD_xor_eq_false_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.getLsbD_xor_eq_false_iff

/-- info: 'LeanLLVM.Vellum.BitLanes.foldl_or_getLsbD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.foldl_or_getLsbD

/-- info: 'LeanLLVM.Vellum.BitLanes.foldl_and_getLsbD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.foldl_and_getLsbD

/-- info: 'LeanLLVM.Vellum.BitLanes.foldl_xor_getLsbD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.foldl_xor_getLsbD

/-! #### Zero and reduce: the packed word read as its lanes, and as a `List.all` (2) -/

/-- info: 'LeanLLVM.Vellum.BitLanes.packLanes_eq_zero_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.packLanes_eq_zero_iff

/-- info: 'LeanLLVM.Vellum.BitLanes.packLanes_eq_zero_iff_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.packLanes_eq_zero_iff_all

/-! #### The zero lane as an identity, for an arrow's own carrier (1) -/

/-- info: 'LeanLLVM.Vellum.BitLanes.zipWith_zero_right' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.zipWith_zero_right

/-! #### The `i8` facts (5) -/

/-- info: 'LeanLLVM.Vellum.BitLanes.getLsbD_seven_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.getLsbD_seven_iff

/-- info: 'LeanLLVM.Vellum.BitLanes.getLsbD_seven_false_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.getLsbD_seven_false_iff

/-- info: 'LeanLLVM.Vellum.BitLanes.getLsbD_highBit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.getLsbD_highBit

/-- info: 'LeanLLVM.Vellum.BitLanes.and80_eq_zero_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.and80_eq_zero_iff

/-- info: 'LeanLLVM.Vellum.BitLanes.and80_eq_zero_iff_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.and80_eq_zero_iff_lt

/-! #### The controls (4) -/

/-- info: 'LeanLLVM.Vellum.BitLanes.packLanes_zipWith_or_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.packLanes_zipWith_or_control

/-- info: 'LeanLLVM.Vellum.BitLanes.foldl_or_getLsbD_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.foldl_or_getLsbD_control

/-- info: 'LeanLLVM.Vellum.BitLanes.packLanes_eq_zero_iff_control' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.packLanes_eq_zero_iff_control

/-- info: 'LeanLLVM.Vellum.BitLanes.and80_eq_zero_iff_control' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BitLanes.and80_eq_zero_iff_control

/-! The zero word's two facts, at the ceiling they hold without a carrier: the
all-clear lanes are found through `BitVec.getLsbD_zero` and
`BitLanes.filter_eq_nil_of_all_false`, not through `List.filter_eq_nil_iff`,
which carries `Classical.choice`; the population count of the zero word then
follows.  Both are consumed by the fold lemmas below, so a proof that reintroduces
the choice-carrying list lemma shows here and at `b8MemFold_frame`. -/

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.setLanes_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.setLanes_zero

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.ctpop_zero64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.ctpop_zero64

/-! The `ub` bricks: the body-level fact both companions consume, for each body. -/

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.pos8Body_ub_of_no_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.pos8Body_ub_of_no_read

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.b8Body_ub_of_no_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.b8Body_ub_of_no_read

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.findBlock_b8Body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.findBlock_b8Body

/-! The mask-word half of the `ub` companion: the loop's own induction
(`pos8_loop_run_ub`) and the whole-function statement built from it
(`entry_pos8_undefined_of_no_read`), then the three read facts it rests on and the
memory projection it states its invariant with. The `Classical.choice` these
report is `step_gep64`'s, as the block above records: the companion reaches it
through `pos8Body_ub_of_no_read`, and the two read facts are `propext`-only. -/

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.entry_pos8_undefined_of_no_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.entry_pos8_undefined_of_no_read

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.pos8_loop_run_ub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.pos8_loop_run_ub

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.natToBytes_bytesToNat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.natToBytes_bytesToNat

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.readBytes_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.readBytes_length

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.natToBytes_of_readBytes_eight' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.natToBytes_of_readBytes_eight

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.state_mem_update_pc' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.state_mem_update_pc

/-! The block kernel's entry stream, at the ceiling the entry statement records:
the refinement, the agreement with POS8, and the `ub` companion with the loop
recurrence and the per-block step count it rests on. -/

/-- info: 'LeanLLVM.Vellum.JsonB8Steps.entry_b8_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonB8Steps.entry_b8_refines

/-- info: 'LeanLLVM.Vellum.JsonB8Steps.entry_pos8_b8_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonB8Steps.entry_pos8_b8_agree

/-- info: 'LeanLLVM.Vellum.JsonB8Steps.entry_b8_undefined_of_no_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonB8Steps.entry_b8_undefined_of_no_read

/-- info: 'LeanLLVM.Vellum.JsonB8Steps.b8_loop_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonB8Steps.b8_loop_run

/-- info: 'LeanLLVM.Vellum.JsonB8Steps.b8_loop_run_ub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonB8Steps.b8_loop_run_ub

/-- info: 'LeanLLVM.Vellum.JsonB8Steps.b8Block_pos_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonB8Steps.b8Block_pos_run

/-- info: 'LeanLLVM.Vellum.JsonB8Steps.b8BlockSteps_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonB8Steps.b8BlockSteps_two

/-! The fold's two facts, which the block statement rests on and which no
`getelementptr` enters: `b8MemFold_read` gives back the positions the fold writes,
`b8MemFold_frame` leaves every read outside the fold's span alone.  Both hold at
`[propext, Quot.sound]` with no carrier — the frame's zero-block step reaches the
zero word's empty lane list through `setLanes_zero`, so there is nothing here to
name. -/

/-- info: 'LeanLLVM.Vellum.JsonB8Steps.b8MemFold_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonB8Steps.b8MemFold_read

/-- info: 'LeanLLVM.Vellum.JsonB8Steps.b8MemFold_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonB8Steps.b8MemFold_frame

/-! ### The entry companion's table-row half

The mirror of the block above.  Where the mask word's half takes the whole table
readable (`readBytes mem0 tab 8192 = some pos8Table`), the row half takes it
readable in every row but the one group `g` of block `j`'s word selects — the
whole table readable contradicts the failing row, so the two halves cannot share
that premise.  Pinned: the whole-function statement, the loop's induction, the
two compositions of the row-readable runners (`pos8Groups_run_row` for a block
that completes, `pos8Groups_ub_of_row` for one that does not), the `if.end` step
built from the first, the group runner both rest on, one failing prefix, and
`blockMem_read_row`, the frame that carries a row past the stores.

The `Classical.choice` these report is `step_gep64`'s, as the entry step corpus
block above records: the row half reaches it through `pos8Head_run_row` and
through the `_none_row` prefixes, which step the same `getelementptr` before the
load that fails.  `blockMem_read_row` reports `[propext, Quot.sound]` — it only
frames a read, and no `getelementptr` is in it. -/

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.entry_pos8_undefined_of_no_row' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.entry_pos8_undefined_of_no_row

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.pos8_loop_run_row_ub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.pos8_loop_run_row_ub

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.pos8Groups_run_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.pos8Groups_run_row

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.pos8Groups_ub_of_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.pos8Groups_ub_of_row

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.pos8Groups_step_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.pos8Groups_step_row

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.pos8Head_run_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.pos8Head_run_row

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.pos8Head_run_none_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.pos8Head_run_none_row

/-- info: 'LeanLLVM.Vellum.JsonEntrySteps.blockMem_read_row' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonEntrySteps.blockMem_read_row

/-! ### The UTF-8 stage's specification

The tables and the eight-class vocabulary, the per-position characterization, the
refused and accepted witnesses, the valid-prefix relations the stage's verdict is
judged against, and the definitions those rest on — fifty theorems first, then
thirty-two definitions.  The ceiling is the repository's,
`[propext, Quot.sound]`, and of the eighty-two pins twenty-eight report no axiom
at all, three report `propext` alone (`sixteen_split` and the two list reads
`klAt` and `klByte`), and fifty-one report the ceiling.  No pin reports
`Classical.choice`: the characterization is decided over the tables' nibbles
rather than over the bytes, and the definitions compare with `decide` rather than
`BEq`, whose `UInt8` instance is the classical one and would carry that carrier
into every theorem about the stage.

A pin records a declaration's axiom footprint, not its statement: two theorems
with different statements and the same footprint pin identically, so the
statements are read in `LeanLLVM/JSON/Utf8.lean` and
`LeanLLVM/Vellum/JsonUtf8Spec.lean` and the pins are what say no axiom entered
them.
-/

/-! ### The valid-prefix relations -/
/-- info: 'LeanLLVM.JSON.validPrefix_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.JSON.validPrefix_iff

/-- info: 'LeanLLVM.JSON.validPrefix_of_utf8Chars' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.JSON.validPrefix_of_utf8Chars

/-- info: 'LeanLLVM.JSON.utf8Spans_cases' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.JSON.utf8Spans_cases

/-- info: 'LeanLLVM.JSON.utf8Char_cases' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.JSON.utf8Char_cases

/-- info: 'LeanLLVM.JSON.utf8Char_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.JSON.utf8Char_head

/-- info: 'LeanLLVM.JSON.utf8Char_one_byte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.JSON.utf8Char_one_byte

/-- info: 'LeanLLVM.JSON.utf8Spans_eq_of_no_start' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.JSON.utf8Spans_eq_of_no_start

/-- info: 'LeanLLVM.JSON.head?_eq_of_hasPrefix_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.JSON.head?_eq_of_hasPrefix_cons

/-- info: 'LeanLLVM.JSON.not_utf8PrefixOf_of_no_start' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.JSON.not_utf8PrefixOf_of_no_start

/-! ### The relations' witnesses -/
/-- info: 'LeanLLVM.JSON.utf8Chars_two' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.JSON.utf8Chars_two

/-- info: 'LeanLLVM.JSON.validPrefix_two' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.JSON.validPrefix_two

/-- info: 'LeanLLVM.JSON.utf8PrefixOf_lone_lead' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.JSON.utf8PrefixOf_lone_lead

/-- info: 'LeanLLVM.JSON.validPrefix_lone_lead' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.JSON.validPrefix_lone_lead

/-- info: 'LeanLLVM.JSON.not_utf8Chars_lone_lead' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.JSON.not_utf8Chars_lone_lead

/-- info: 'LeanLLVM.JSON.not_validPrefix_lone_cont' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.JSON.not_validPrefix_lone_cont

/-! ### The tables and the eight-class vocabulary -/
/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klTables_bytes' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klTables_bytes

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.subsSat_high_bit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.subsSat_high_bit

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klErrByte_eq_klSc_xor_klMust' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klErrByte_eq_klSc_xor_klMust

/-! ### The nibble reduction -/
/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.nib_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.nib_toNat

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.nib_div' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.nib_div

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.nib_mod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.nib_mod

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.nib_high' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.nib_high

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.nib_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.nib_self

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.sixteen_split' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.sixteen_split

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klSc_p1_nib' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klSc_p1_nib

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klSc_c_nib' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klSc_c_nib

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klSc_nib' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klSc_nib

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klPair_c_nib' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klPair_c_nib

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klPair_p1_nib' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klPair_p1_nib

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.isCont_p1_nib' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.isCont_p1_nib

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.isCont_c_nib' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.isCont_c_nib

/-! ### The per-position characterization -/
/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klSc_zero_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klSc_zero_iff

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klSc_twoConts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klSc_twoConts

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klErrByte_eq_zero_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klErrByte_eq_zero_iff

/-! ### The refused and accepted witnesses -/
/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.refused_tooShort' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.refused_tooShort

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.refused_tooLong' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.refused_tooLong

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.refused_overlong3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.refused_overlong3

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.refused_tooLarge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.refused_tooLarge

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.refused_surrogate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.refused_surrogate

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.refused_overlong2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.refused_overlong2

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.refused_tooLarge1000' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.refused_tooLarge1000

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.refused_twoConts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.refused_twoConts

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.refused_witnesses_distinct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.refused_witnesses_distinct

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.accepted_ascii' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.accepted_ascii

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.accepted_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.accepted_two

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.accepted_three_E0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.accepted_three_E0

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.accepted_three_ED' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.accepted_three_ED

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.accepted_four_F0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.accepted_four_F0

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.accepted_four_F4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.accepted_four_F4

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.accepted_four_middle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.accepted_four_middle

/-! ### The definitions

Every declaration the specification introduces that is not a theorem: the
relations' own carriers, the three tables, the eight class constants, the four
per-position and stream words, the five block-layer words and the three RFC
predicates.  Their footprints are the ones their values use — `klAt` and
`klByte` reach `propext` through `List.getD`, and the rest of the stream words
reach the ceiling the same way — so a noncomputable definition, which is what a
`BEq` comparison on `UInt8` would produce, would show here.
-/

/-- info: 'LeanLLVM.JSON.Utf8Spans' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.JSON.Utf8Spans

/-- info: 'LeanLLVM.JSON.Utf8Chars' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.JSON.Utf8Chars

/-- info: 'LeanLLVM.JSON.Utf8PrefixOf' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.JSON.Utf8PrefixOf

/-- info: 'LeanLLVM.JSON.ValidPrefix' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.JSON.ValidPrefix

/-- info: 'LeanLLVM.JSON.IsUtf8LeadByte' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.JSON.IsUtf8LeadByte

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klT1' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klT1

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klT2' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klT2

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klT3' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klT3

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.tooShort' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.tooShort

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.tooLong' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.tooLong

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.overlong3' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.overlong3

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.tooLarge' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.tooLarge

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.surrogate' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.surrogate

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.overlong2' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.overlong2

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.tooLarge1000' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.tooLarge1000

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.twoConts' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.twoConts

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klAt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klAt

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klSc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klSc

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klMust' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klMust

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klErrByte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klErrByte

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klByte' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klByte

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klErrVec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klErrVec

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klErr32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klErr32

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klErrBlk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klErrBlk

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klAsciiBlk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klAsciiBlk

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klAll

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klTailByte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klTailByte

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klStage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klStage

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.IsContByte' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.IsContByte

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.NeedsCont' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.NeedsCont

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.KlPair' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.KlPair

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.nib' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.nib

/-! ### The verdict at the block boundary

`klStage` evaluated at the boundary its contract is about: a document whose
length is a whole number of blocks leaves the position after its last byte
unscanned, so a truncated final character is accepted there and rejected one byte
later, where the padding supplies that position.  The gate does not move either
verdict, and the tail test is what restores a byte that can never begin a
character.  These are evaluations rather than theorems: the quantified statements
about the same boundary are `klErrByte_eq_zero_iff`'s accepted and refused
witnesses and, at the document level, the refinement's corollaries.
-/

/-- A document of `n` bytes: `n - 1` ASCII bytes then `last`. -/
def klDoc (n : Nat) (last : UInt8) : List UInt8 := List.replicate (n - 1) 0x41 ++ [last]

-- A truncated `E2` at a whole number of blocks is accepted, and one byte later
-- the padding position exists and the same character is refused.
#guard JsonUtf8Spec.klStage (klDoc 64 0xE2) 64 false = 0
#guard JsonUtf8Spec.klStage (klDoc 64 0xE2) 64 true = 0
#guard JsonUtf8Spec.klStage (klDoc 65 0xE2) 65 false = 1
#guard JsonUtf8Spec.klStage (klDoc 65 0xE2) 65 true = 1

-- The tail test's three answers at the last scanned position.
#guard JsonUtf8Spec.klStage (klDoc 64 0xC2) 64 false = 0
#guard JsonUtf8Spec.klStage (klDoc 64 0xC1) 64 false = 1
#guard JsonUtf8Spec.klStage (klDoc 64 0xF5) 64 false = 1

-- The four restricted first continuations, at their edge and one past it.
#guard JsonUtf8Spec.klStage [0xE0, 0xA0, 0x80] 3 false = 0
#guard JsonUtf8Spec.klStage [0xE0, 0x80, 0x80] 3 false = 1
#guard JsonUtf8Spec.klStage [0xED, 0x9F, 0x80] 3 false = 0
#guard JsonUtf8Spec.klStage [0xED, 0xA0, 0x80] 3 false = 1
#guard JsonUtf8Spec.klStage [0xF0, 0x90, 0x80, 0x80] 4 false = 0
#guard JsonUtf8Spec.klStage [0xF0, 0x80, 0x80, 0x80] 4 false = 1
#guard JsonUtf8Spec.klStage [0xF4, 0x8F, 0x80, 0x80] 4 false = 0
#guard JsonUtf8Spec.klStage [0xF4, 0x90, 0x80, 0x80] 4 false = 1

-- The empty document, and a lone continuation.
#guard JsonUtf8Spec.klStage [] 0 false = 0
#guard JsonUtf8Spec.klStage [] 0 true = 0
#guard JsonUtf8Spec.klStage [0x80] 1 false = 1

/-! ### The UTF-8 stage's interface and execution

`JsonUtf8IR` pins the fixture and states the staged window and the run's budget;
`JsonUtf8Steps` holds the body's step lemmas, the backward `getelementptr` the
seven backward sites need, the `klMust` bridge and the gate lemma.

The three `getelementptr` steps report `Classical.choice` through
`BitVec.signExtend_eq` — measured: that lemma is `[propext, Classical.choice,
Quot.sound]`, while `evalInstr_gep_back` itself is `[propext, Quot.sound]` and does
not carry the choice.  It is the same lemma `step_gep64` uses, so no new carrier
is introduced here, and `step_gep64_imm` reaches it without `evalInstr_gep_back`
appearing in its proof.  No other declaration here reports a
carrier its own docstring does not name.
-/

-- The fixture text, read at elaboration.
/--
info: 'LeanLLVM.Vellum.JsonUtf8IR.utf8Src' does not depend on any axioms
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8IR.utf8Src

-- The parse the fixture pin runs.  It reports `Classical.choice` because the
-- parser's character classification does; no statement below inherits it.
/--
info: 'LeanLLVM.Vellum.JsonUtf8IR.firstFunction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8IR.firstFunction

-- The pinned AST: nine blocks, 160 instruction lines and nine terminators, which
-- is the fixture's own 169.
/--
info: 'LeanLLVM.Vellum.JsonUtf8IR.utf8Function' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8IR.utf8Function

/--
info: 'LeanLLVM.Vellum.JsonUtf8IR.reg' does not depend on any axioms
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8IR.reg

/--
info: 'LeanLLVM.Vellum.JsonUtf8IR.lit' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8IR.lit

/--
info: 'LeanLLVM.Vellum.JsonUtf8IR.splatOf' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8IR.splatOf

/--
info: 'LeanLLVM.Vellum.JsonUtf8IR.lanesOf' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8IR.lanesOf

/--
info: 'LeanLLVM.Vellum.JsonUtf8IR.highBitMask' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8IR.highBitMask

/--
info: 'LeanLLVM.Vellum.JsonUtf8IR.t1Lanes' does not depend on any axioms
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8IR.t1Lanes

/--
info: 'LeanLLVM.Vellum.JsonUtf8IR.t2Lanes' does not depend on any axioms
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8IR.t2Lanes

/--
info: 'LeanLLVM.Vellum.JsonUtf8IR.t3Lanes' does not depend on any axioms
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8IR.t3Lanes

/--
info: 'LeanLLVM.Vellum.JsonUtf8IR.pshufb' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8IR.pshufb

/--
info: 'LeanLLVM.Vellum.JsonUtf8IR.usubSat' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8IR.usubSat

/--
info: 'LeanLLVM.Vellum.JsonUtf8IR.ptestz' does not depend on any axioms
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8IR.ptestz

/--
info: 'LeanLLVM.Vellum.JsonUtf8IR.utf8Entry' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8IR.utf8Entry

/--
info: 'LeanLLVM.Vellum.JsonUtf8IR.utf8LrPh' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8IR.utf8LrPh

/--
info: 'LeanLLVM.Vellum.JsonUtf8IR.utf8ForBodyUs' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8IR.utf8ForBodyUs

/--
info: 'LeanLLVM.Vellum.JsonUtf8IR.utf8ThenUs' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8IR.utf8ThenUs

/--
info: 'LeanLLVM.Vellum.JsonUtf8IR.utf8EndUs' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8IR.utf8EndUs

/--
info: 'LeanLLVM.Vellum.JsonUtf8IR.utf8Cleanup' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8IR.utf8Cleanup

/--
info: 'LeanLLVM.Vellum.JsonUtf8IR.utf8ForBody' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8IR.utf8ForBody

/--
info: 'LeanLLVM.Vellum.JsonUtf8IR.utf8Then20' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8IR.utf8Then20

/--
info: 'LeanLLVM.Vellum.JsonUtf8IR.utf8End24' does not depend on any axioms
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8IR.utf8End24

-- The staged window: three prefix bytes, the document, zero padding.
/--
info: 'LeanLLVM.Vellum.JsonUtf8IR.utf8Window' does not depend on any axioms
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8IR.utf8Window

-- The staged window on the carrier `ValidPrefix` is stated over.
/--
info: 'LeanLLVM.Vellum.JsonUtf8IR.utf8WinPrefix' does not depend on any axioms
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8IR.utf8WinPrefix

-- `n ≤ 64 * ((n + 63) / 64)`: the padding count subtracts something smaller.
/--
info: 'LeanLLVM.Vellum.JsonUtf8IR.le_mul_div_sixtyfour' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8IR.le_mul_div_sixtyfour

-- The window's length is `3 + 64 * nb` at the block count.
/--
info: 'LeanLLVM.Vellum.JsonUtf8IR.utf8Window_length' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8IR.utf8Window_length

-- The run's budget as a function of the block count.
/--
info: 'LeanLLVM.Vellum.JsonUtf8IR.fuelOf' does not depend on any axioms
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8IR.fuelOf


-- The execution: steps, the backward GEP, the bridge, the gate lemma.

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.fuelOf_eq' does not depend on any axioms
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.fuelOf_eq

-- The magnitude reading of a backward index: `2^63 ≤ v` is `k ≤ 2^63` at the
-- magnitude.
/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.signExtend_magnitude' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.signExtend_magnitude

-- The backward `getelementptr`: the index is `2^64 - k`, the bound is the
-- displacement against the base, and `k ≤ 2^63` is the branch premise, derived
-- from `hk` rather than assumed; without it `k = 2^63 + 1` makes the lemma false.
/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.step_gep64_back' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.step_gep64_back

-- The forward `getelementptr` at an immediate offset.
/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.step_gep64_imm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.step_gep64_imm

-- The backward `getelementptr` at an immediate offset: the tail's `-1`.
/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.step_gep64_imm_back' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.step_gep64_imm_back

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.step_and_reg' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.step_and_reg

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.step_or_reg' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.step_or_reg

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.step_icmp_ne_imm' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.step_icmp_ne_imm

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.step_icmp_ult_imm' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.step_icmp_ult_imm

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.step_icmp_ugt_imm' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.step_icmp_ugt_imm

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.wordBytes' does not depend on any axioms
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.wordBytes

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.wordBytes_length' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.wordBytes_length

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.map_toBitVec_eq_byteLanes' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.map_toBitVec_eq_byteLanes

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.nat256' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.nat256

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.step_load32_8' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.step_load32_8

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.step_load4_64' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.step_load4_64

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.step_load16_16' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.step_load16_16

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.highBit_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.highBit_iff

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.and_highBit' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.and_highBit

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.subsSat_96_high' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.subsSat_96_high

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.subsSat_112_high' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.subsSat_112_high

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.or_high' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.or_high

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.u80' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.u80

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.u0' does not depend on any axioms
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.u0

-- The bridge the specification left as a limit: the emission's masked `must` word
-- at one position is the specification's `klMust`, from `subsSat_high_bit`.
/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.klMust_bridge' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klMust_bridge

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.klT1T2_ascii_facts' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klT1T2_ascii_facts

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.klSc_ascii_facts' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klSc_ascii_facts

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.klSc_ascii' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klSc_ascii

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.klMust_ascii' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klMust_ascii

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.klErrByte_ascii' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klErrByte_ascii

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.klErrVec_ascii' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klErrVec_ascii

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.ascii_append' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.ascii_append

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.ascii_take' does not depend on any axioms
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.ascii_take

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.ascii_drop' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.ascii_drop

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.ascii_getD' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.ascii_getD

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.klErr32_ascii' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klErr32_ascii

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8Skip_eq_zero' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8Skip_eq_zero

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.t1Lanes_eq' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.t1Lanes_eq

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.t2Lanes_eq' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.t2Lanes_eq

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.t3Lanes_eq' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.t3Lanes_eq

-- The interface invariant: `klStage`'s stated length is the document's, so its
-- block count and its tail test are about the same bytes.
/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.klStage_of_length' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klStage_of_length

-- The witness that refutes the window reading of `klErrByte`: zero here, and an
-- error at each of the two positions before it.
/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.klErrByte_window_witness' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klErrByte_window_witness

-- The position one place before the witness, and two places before it: the error
-- the window reading would have misplaced.
/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.klErrByte_window_witness_earlier' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klErrByte_window_witness_earlier

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.klErrByte_window_witness_earliest' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klErrByte_window_witness_earliest

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.klPair_witness_refused' does not depend on any axioms
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klPair_witness_refused

-- `klAsciiBlk` is the block's bytes: the fold's bit 7, proved once by induction
-- with `BitVec.getLsbD_or`, and the byte bound it stands for.
/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.and80_eq_zero' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.and80_eq_zero

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.getLsbD_false_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.getLsbD_false_iff

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.fold_or_u8_getLsbD' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.fold_or_u8_getLsbD

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.and80_u8' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.and80_u8

/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.klAsciiBlk_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klAsciiBlk_iff

/-! ### The gate's two paths are one statement

`klAll` carries the gate as a parameter: a block whose sixty-four bytes are ASCII
and whose predecessor was ASCII is skipped by the gated path and evaluated by the
free one.  These declarations are the block fold's invariant — the two states
agree, the accumulator keeps its lane count, and a set `prev_ascii` means the
three bytes before the block are ASCII — and the invariance that closes over it.
Every one reports `[propext, Quot.sound]` at most: the proof is an induction over
blocks with the lane algebra and the table's ASCII facts, and it consumes no
body step and no `getelementptr`, so this stage's own ceiling is untouched. -/

-- The three bytes before a block, as `klAll` reads them.
/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.klPre' does not depend on any axioms
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klPre

-- A block of the window: sixty-four bytes after the three prefix bytes.
/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.klBlk' does not depend on any axioms
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klBlk

-- `klAll`'s step at one block index and one state.
/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.klStep' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klStep

-- One gate's run over `nb` blocks of the window.
/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.klRun' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klRun

-- `klAll` is the run: the specification's inline step is `klStep`.
/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.klAll_eq_klRun' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klAll_eq_klRun

-- The three bytes before block `bi + 1` are block `bi`'s last three.
/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.klPre_succ' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klPre_succ

-- The gate's step is the same step, given the predecessor's ASCII reading.
/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.klStep_gate' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klStep_gate

-- The step keeps the accumulator's lane count.
/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.klStep_length' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klStep_length

-- The run's invariant: the two gates agree, the lane count is kept, and a set
-- `prev_ascii` means the bytes before the next block are ASCII.
/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.klRun_invariant' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klRun_invariant

-- **The gate invariance, unconditionally**: `klAll true bs = klAll false bs`.
/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.klAll_gate_invariant' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klAll_gate_invariant

-- The window whose `klPre win 1` is not ASCII: the invariance needs nothing
-- beyond itself, because the skip is decided by the state's flag.
/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.klAll_gate_invariant_counterexample' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klAll_gate_invariant_counterexample

-- The same window's block 0 is not ASCII, so no skip is taken at `bi = 1`.
/--
info: 'LeanLLVM.Vellum.JsonUtf8Steps.counterexample_block0_not_ascii' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.counterexample_block0_not_ascii

/-! ### The window aggregation

`klErrWin` reads one staged position's error byte as a proposition, `klErrAll` is
that reading over the first `L` positions, and `IsCharEnd` is the byte predicate a
character's end leaves behind.  The twenty-seven pins below are the role
statements and one control per family: three definitions, seven bridge statements
(the Nat forms of `NeedsCont`, `IsCharEnd` and `KlPair`, the pair condition's two
half-facts, and the `IsCharEnd` bound), four byte reads at a character's offset,
five character steps (the four per-length steps and `char_ok`), and eight bound
and constructor facts the steps consume.  The arithmetic shims the steps use
(`win_shift`, `win_m0`..`win_m3`, `klByte_of_drop_eq`) interrupt no statement a
reader looks for and are not pinned. -/
/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klErrWin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klErrWin

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klErrAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klErrAll

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.IsCharEnd' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.IsCharEnd

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.needsCont_nat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.needsCont_nat

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.needsCont_false_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.needsCont_false_iff

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.isCharEnd_nat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.isCharEnd_nat

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.isCharEnd_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.isCharEnd_lt

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klPair_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klPair_iff

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.ok_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.ok_right

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.ok_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.ok_left

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klByte_drop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klByte_drop

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klByte_drop_any' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klByte_drop_any

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klByte_prefix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klByte_prefix

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.drop_of_literal' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.drop_of_literal

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.char1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.char1

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.char2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.char2

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.char3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.char3

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.char4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.char4

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.char_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.char_ok

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.not_cont_of_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.not_cont_of_lt

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.not_needsCont_of_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.not_needsCont_of_lt

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.cont_of_bounds' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.cont_of_bounds

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.not_cont_of_lead' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.not_cont_of_lead

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.needsCont_of_lead' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.needsCont_of_lead

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.needsCont_of_lead3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.needsCont_of_lead3

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.cont_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.cont_le

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.not_cont_of_ge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.not_cont_of_ge

/-! ### The UTF-8 body's foundation

The pins for `JsonUtf8Steps`' new declarations: the seven backward `getelementptr`
sites, the lane identity that reads the body's packed words as `klErrBlk`'s byte
list, the accumulator step at `klErrBlk`'s vocabulary, and the step corpus the two
loop bodies are built from.  Each line's footprint is measured, not assumed: the
`getelementptr` sites and the immediate `gep` step carry `Classical.choice`
because `evalInstr_gep`'s branch does, which is the carrier M3 inherits; no other
declaration here reaches a fourth axiom.  The controls sit beside their families:
`neg_toNat_two` and `neg_toNat_three` beside `neg_toNat_one` (a magnitude is not
`2 ^ 64 - 1` for every `k`), `sizeBytes_i8` beside the sites (the displacement is
the element's, and an `i8` is one byte), and `klErrBlk_length`/`errHalf_length`
beside the identity's lane counts. -/

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.neg_toNat_one' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.neg_toNat_one

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.neg_toNat_two' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.neg_toNat_two

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.neg_toNat_three' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.neg_toNat_three

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.sizeBytes_i8' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.sizeBytes_i8

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.step_gep64_m1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.step_gep64_m1

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.step_gep64_m2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.step_gep64_m2

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.step_gep64_m3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.step_gep64_m3

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.t1V_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.t1V_eq

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.t2V_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.t2V_eq

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.t3V_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.t3V_eq

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.t1HalfV_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.t1HalfV_getD

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.pshufb_t1_lane' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.pshufb_t1_lane

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.pshufb_t2_lane' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.pshufb_t2_lane

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.pshufb_t3_lane' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.pshufb_t3_lane

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.nibLanes_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.nibLanes_toNat

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.hiNibbleLanes_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.hiNibbleLanes_toNat

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.nibLanes_shr4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.nibLanes_shr4

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.getD_zipWith' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.getD_zipWith

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.mustHalf_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.mustHalf_getD

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.scHalf_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.scHalf_getD

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.errHalfBytes_eq_zip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.errHalfBytes_eq_zip

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.bitcastVecLanes_and64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.bitcastVecLanes_and64

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.bitcastVecLanes_or64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.bitcastVecLanes_or64

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.bitcastVecLanes_xor64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.bitcastVecLanes_xor64

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.byteView_of64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.byteView_of64

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.highLanes64_bytes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.highLanes64_bytes

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.errHalfBytes_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.errHalfBytes_eq

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.errHalf_bitcast_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.errHalf_bitcast_eq

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.errBlkBytes_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.errBlkBytes_eq

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.klErrVec_take' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klErrVec_take

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.klErrBlk_eq_vecs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klErrBlk_eq_vecs

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.byteLanes_zipWith_or' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.byteLanes_zipWith_or

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.packLanes_byteLanes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.packLanes_byteLanes

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.packLanes_bitcast8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.packLanes_bitcast8

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.natToBytes_bytesToNat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.natToBytes_bytesToNat

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.bytesToNat_zipWith_or' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.bytesToNat_zipWith_or

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.or_rotate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.or_rotate

/-- info: 'or_rotate' depends on axioms: [propext] -/
#guard_msgs in
#print axioms or_rotate

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.errHalf_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.errHalf_length

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.packLanes_errHalf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.packLanes_errHalf

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.errBlk_word_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.errBlk_word_eq

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.klErrBlk_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klErrBlk_length

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.scRaw_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.scRaw_eq

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.errRaw_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.errRaw_eq

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.errRaw_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.errRaw_length

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.zip_mapM_binop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.zip_mapM_binop

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8_step_vec_and' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8_step_vec_and

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8_step_and15' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8_step_and15

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8_step_andHigh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8_step_andHigh

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8_step_shr16' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8_step_shr16

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8_step_bc64_8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8_step_bc64_8

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8_step_bc8_64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8_step_bc8_64

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8_step_pshufb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8_step_pshufb

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8_step_usubSat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8_step_usubSat

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8_phi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8_phi

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8_step_load8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8_step_load8

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8_step_gep_imm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8_step_gep_imm

/-! ### The body's two loops, its reduce and its tail

Every declaration the loop bodies, the reduce and the tail introduce, at the
footprint it was measured at.  Three carry `Classical.choice` —
`utf8Ungated_body`, `utf8Gated_body` and `utf8Tail` — and each names the same
carrier: `BitVec.signExtend_eq`, the sign-extension premise their
`getelementptr` steps read.  That is one of C64's four known routes and the
carrier M2's `step_gep64` pin already names; `evalInstr_gep`,
`evalInstr_gep_back` and `evalOperand_reg_of` carry none, so nothing new enters
here.  The reduce's `ptestz` and the returned word's `zext` reach the carrier
not at all.

**One carrier, two descriptions.**  The `step_gep64` paragraph of M2's
`Classical.choice` block above reports this same footprint by its *mechanism* —
the `Classical.propDecidable`-discharged `Decidable` inside the step's own proof
term — while this block reports it by the *lemma* that carries it,
`BitVec.signExtend_eq`, which is the last line of `step_gep64`'s proof and of
`utf8_step_gep`'s alike; a reader meeting both should not conclude that there are
two carriers, nor that the second one needs a decision. -/


/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.t1Lanes_length' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.t1Lanes_length

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.t2Lanes_length' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.t2Lanes_length

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.t3Lanes_length' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.t3Lanes_length

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.len32_pshufb_nib' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.len32_pshufb_nib

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.len32_pshufb_hi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.len32_pshufb_hi

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.len32_byteLanes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.len32_byteLanes

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.shl64_six' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.shl64_six

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.errRawBlk_word_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.errRawBlk_word_eq

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8_step_icmp_eq_imm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8_step_icmp_eq_imm

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8_step_and_imm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8_step_and_imm

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8_step_zext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8_step_zext

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8Ungated_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8Ungated_body

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8Gated_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8Gated_body

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8Reduce' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8Reduce

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8Tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8Tail

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8Return' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8Return

/-! ### The blocks around the loops, and their stepping surface

The header, latch, entry and selection chains, the nine block lookups and the
`runFuel` reductions a block-by-block run needs.  `utf8ForBodyUs_run` is the only
one that carries `Classical.choice`, and it carries the same carrier the bodies
do — `BitVec.signExtend_eq`, reached through `utf8_step_gep` for the block's
base.  The nine lookups are `[propext]`-only: each is proved by `decide`, so the
lookup is the kernel's computation on the pinned block list and no `Decidable`
instance is consulted classically.  That is narrower than the `simp`-proved
lookups which **do** carry choice (`findBlock_pos8Body` and its group), and level
with `findBlock_pos8Entry`, which is `simp`-proved and `[propext]`-only — so the
difference is the proof route and not the goal, and no attribution is owed for
these nine. -/


/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8_step_lshr_imm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8_step_lshr_imm

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8Entry_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8Entry_run

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8LrPh_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8LrPh_run

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8ForBodyUs_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8ForBodyUs_run

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8EndUs_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8EndUs_run

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.findBlock_utf8Entry' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.findBlock_utf8Entry

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.findBlock_utf8LrPh' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.findBlock_utf8LrPh

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.findBlock_utf8ForBodyUs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.findBlock_utf8ForBodyUs

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.findBlock_utf8ThenUs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.findBlock_utf8ThenUs

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.findBlock_utf8EndUs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.findBlock_utf8EndUs

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.findBlock_utf8Cleanup' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.findBlock_utf8Cleanup

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.findBlock_utf8ForBody' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.findBlock_utf8ForBody

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.findBlock_utf8Then20' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.findBlock_utf8Then20

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.findBlock_utf8End24' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.findBlock_utf8End24

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.step_of_utf8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.step_of_utf8

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.runFuel_jump_utf8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.runFuel_jump_utf8

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.runFuel_ret_utf8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.runFuel_ret_utf8

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.runFuel_ub_utf8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.runFuel_ub_utf8

/-! #### The window split, shared by the run lemmas and the companion

`take_append_take_len` and `win_read` are the two lemmas that turn C60's single
`hread` into every interior thirty-two-byte read, and the body and the `ub`
companion read the window through them rather than through two splitters that
would have to be kept in agreement.  The generalised `utf8Ungated_body` was
re-measured when its predecessor became a parameter: same footprint, same
carrier — `BitVec.signExtend_eq` — and the pin below is the measurement, not a
carry-over. -/

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.take_append_take_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.take_append_take_len

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.win_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.win_read

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8Ungated_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8Ungated_body

/-! #### The validity stage's reconstruction

`klErrAll` over the padded sixty-four-byte-multiple window, together with the
condition that the last byte of a full block is not a tail byte, is exactly a
valid prefix under `Utf8Spans`.  The pins below are this appendix's measurement:
`klErrAll_window_iff` is the equivalence, `validPrefix_of_klErrAll` the direction
that rebuilds the character stream, and the two `C0` witnesses the positions where
the same bytes are valid at one block boundary and refused at the other. -/

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klByte_getElem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klByte_getElem

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.literal_drop_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.literal_drop_cons

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.utf8Char_length_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.utf8Char_length_le

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.utf8Spans_length_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.utf8Spans_length_le

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.utf8Char_drop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.utf8Char_drop

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.drop_three_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.drop_three_cons

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.literal_drop_list' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.literal_drop_list

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klByte_append_left' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klByte_append_left

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klErrWin_append_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klErrWin_append_left

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.spans_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.spans_ok

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.char_prefix_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.char_prefix_ok

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.u8_le_of_toNat' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.u8_le_of_toNat

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.u8_lt_of_toNat' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.u8_lt_of_toNat

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klErrWin_at_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klErrWin_at_succ

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klErrWin_at_succ2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klErrWin_at_succ2

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klErrWin_at_succ3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klErrWin_at_succ3

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.not_charEnd_of_ge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.not_charEnd_of_ge

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.not_cont_of_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.not_cont_of_pair

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.not_klPair_of_dead' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.not_klPair_of_dead

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.not_needsCont_of_charEnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.not_needsCont_of_charEnd

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.pair_two_cont' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.pair_two_cont

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.pair_three0_cont' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.pair_three0_cont

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.pair_three1_cont' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.pair_three1_cont

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.pair_three2_cont' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.pair_three2_cont

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.pair_three3_cont' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.pair_three3_cont

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.pair_four0_cont' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.pair_four0_cont

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.pair_four1_cont' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.pair_four1_cont

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.pair_four2_cont' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.pair_four2_cont

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klTailByte_true_ge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klTailByte_true_ge

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klTailByte_false_of_lead' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klTailByte_false_of_lead

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klTailByte_false_of_cont' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klTailByte_false_of_cont

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klTailByte_false_of_charEnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klTailByte_false_of_charEnd

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.utf8PrefixOf_of_literal_take' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.utf8PrefixOf_of_literal_take

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.utf8Spans_tail_drop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.utf8Spans_tail_drop

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.utf8Spans_literal_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.utf8Spans_literal_tail

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.help_drop1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.help_drop1

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.help_drop2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.help_drop2

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.help_drop3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.help_drop3

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.literal_take_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.literal_take_append

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.literal_length_lt_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.literal_length_lt_append

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klTailByte_true_of_C0_C1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klTailByte_true_of_C0_C1

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klTailByte_true_of_F5' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klTailByte_true_of_F5

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.validPrefix_of_klErrAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.validPrefix_of_klErrAll

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.not_klTailByte_of_char_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.not_klTailByte_of_char_prefix

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.le_mul_div_sixtyfour' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.le_mul_div_sixtyfour

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klByte_append_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klByte_append_right

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klByte_replicate_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klByte_replicate_zero

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klByte_win_pad_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klByte_win_pad_last

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klByte_win_doc_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klByte_win_doc_last

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.validPrefix_zero_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.validPrefix_zero_cons

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.validPrefix_zero_cons_back' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.validPrefix_zero_cons_back

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.validPrefix_three_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.validPrefix_three_cons

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.validPrefix_three_cons_back' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.validPrefix_three_cons_back

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klByte_take_len' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klByte_take_len

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.pad_eq_zero_of_mod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.pad_eq_zero_of_mod

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.not_klTailByte_last_of_validPrefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.not_klTailByte_last_of_validPrefix

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.klErrAll_window_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.klErrAll_window_iff

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.witness_C0_nonmultiple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.witness_C0_nonmultiple

/-- info: 'LeanLLVM.Vellum.JsonUtf8Spec.witness_C0_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Spec.witness_C0_block

/-! ### The staged window's bridge, its accumulator and the ungated loop's run

Every declaration the window's byte reading, the accumulator fold, the read
utility and the ungated loop's run introduce, at the footprint each was measured
at.  **One carrier appears, and it is inherited**: `utf8Ungated_loop_run` carries
`BitVec.signExtend_eq`, the same carrier the two body lemmas and the tail already
name — it consumes `utf8Ungated_body`, whose seven backward `getelementptr` sites
read it.  Nothing else here carries `Classical.choice`: the arithmetic is stated
so that no decision procedure is consulted, and `omega` is not used in any of
these proofs.

**Two library lemmas are replaced rather than inherited, because their own proof
terms carry `Classical.choice` and the statements do not need it**:
`List.drop_take` and `Nat.div_lt_of_lt_mul`, re-proved here as `drop_take'` and
`div_lt_of_lt_mul'` from `List`'s recursion and the division identity.  Naming
them is the point: a later proof that reaches for the library lemma would put the
carrier back into a statement — `klAll_zero_iff_klErrAll` above all, which the
headline's right-hand side reads — that no emission and no classical argument
requires. -/

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8Kept' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8Kept

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8Stream' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8Stream

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.klAcc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klAcc

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8GateWord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8GateWord

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.readBytes_eq_none_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.readBytes_eq_none_iff

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.readBytes_eq_none_of_readByte_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.readBytes_eq_none_of_readByte_none

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.exists_readBytes_of_readable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.exists_readBytes_of_readable

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.klByte_append_zeros' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klByte_append_zeros

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.klByte_window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klByte_window

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.klErrWin_window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klErrWin_window

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.klErrAll_window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klErrAll_window

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.u8_or_eq_zero_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.u8_or_eq_zero_iff

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.klByte_take_drop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klByte_take_drop

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.klErrVec_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klErrVec_getD

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.drop_take'' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.drop_take'

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.block_arg_lo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.block_arg_lo

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.block_arg_hi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.block_arg_hi

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.klErrBlk_getD_zero_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klErrBlk_getD_zero_iff

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.klStep_false_fst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klStep_false_fst

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.klRun_false_fst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klRun_false_fst

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.klAll_false_eq_klAcc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klAll_false_eq_klAcc

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.zipWith_or_zero_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.zipWith_or_zero_iff

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.all_zero_replicate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.all_zero_replicate

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.eq_replicate_zero_iff_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.eq_replicate_zero_iff_getD

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.klAcc_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klAcc_succ

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.klAcc_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klAcc_length

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.klAcc_zero_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klAcc_zero_iff

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.div_lt_of_lt_mul'' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.div_lt_of_lt_mul'

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.klAcc_zero_iff_klErrAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klAcc_zero_iff_klErrAll

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.klAll_zero_iff_klErrAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klAll_zero_iff_klErrAll

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.denoteCode_kept' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.denoteCode_kept

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.ofBool_of_true' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.ofBool_of_true

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.ofBool_of_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.ofBool_of_false

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.execTerm_condbr_true' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.execTerm_condbr_true

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.execTerm_condbr_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.execTerm_condbr_false

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8Kept_body' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8Kept_body

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8Kept_then' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8Kept_then

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8Kept_us' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8Kept_us

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8Kept_end' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8Kept_end

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.body_stream' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.body_stream

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.take67_drop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.take67_drop

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.stream_slice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.stream_slice

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.klErrVec_eq_of_getD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klErrVec_eq_of_getD

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.klErrVec_slice_window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klErrVec_slice_window

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.klErrBlk_window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klErrBlk_window

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.win_read_slice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.win_read_slice

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8Ungated_loop_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8Ungated_loop_run

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.bytesToNat_eq_zero_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.bytesToNat_eq_zero_iff

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.u8_and_high_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.u8_and_high_lt

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.u8_or_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.u8_or_lt

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.byteLanes_zipWith_and_toBitVec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.byteLanes_zipWith_and_toBitVec

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.byteLanes_zipWith_and' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.byteLanes_zipWith_and

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.bytesToNat_zipWith_and' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.bytesToNat_zipWith_and

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.packLanes_highLanes64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.packLanes_highLanes64

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8GateWord_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8GateWord_eq

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.ascii_of_ptestz' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.ascii_of_ptestz

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.ofBool_eq_one_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.ofBool_eq_one_iff

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.bit1_and_eq_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.bit1_and_eq_one

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.bit1_eq_zero_of_ne_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.bit1_eq_zero_of_ne_one

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.ptestz_eq_one_or_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.ptestz_eq_one_or_zero

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.ptestz_eq_one_of_ne_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.ptestz_eq_one_of_ne_zero

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.orcond_one_imp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.orcond_one_imp

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.ptestz_ascii' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.ptestz_ascii

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8Ungated_preheader_operands' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8Ungated_preheader_operands

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.sixtyfour_mul_div_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.sixtyfour_mul_div_le

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8SpanBound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8SpanBound

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8BlkErr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8BlkErr

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.klAccStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klAccStep

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.klAcc_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klAcc_step

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8BlkErr_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8BlkErr_eq

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.klAccStep_pack' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.klAccStep_pack

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8GateBit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8GateBit

/-! ### The unreadable byte: the least index, the block facts and the step

Every declaration the unreadable-byte statement's two supporting halves introduce,
at the footprint each was measured at.  **One carrier appears, and it is inherited**:
`utf8ForBodyUs_denote_none` and `utf8ForBody_denote_none` carry
`BitVec.signExtend_eq`, the same carrier the body lemmas and the ungated loop's
run already name — each runs its block's forward `getelementptr` sites
(`utf8_step_gep`, `utf8_step_gep_imm`) to reach the failing header load, and
that is where the carrier enters.  Nothing else here carries `Classical.choice`:
the least-index argument is an induction that cases on the head byte, the
earlier blocks' reads come from `readBytes_eq_none_of_readByte_none` and
`exists_readBytes_of_readable`, and the block facts go through
`denoteCode_cons_none` and `evalInstr_load_none`, each at `[propext,
Quot.sound]`. -/

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.exists_least_unreadable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.exists_least_unreadable

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8_least_unreadable_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8_least_unreadable_block

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8_block_two_reads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8_block_two_reads

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8ForBodyUs_denote_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8ForBodyUs_denote_none

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8ForBody_denote_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8ForBody_denote_none

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.step_ub_utf8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.step_ub_utf8

/-! ### The gated loop's run

Every declaration the gated loop's run introduces, at the footprint each was
measured at, in the order the section declares them.  **One carrier appears, and
it is inherited**: `utf8Gated_loop_run` carries `BitVec.signExtend_eq`, the same
carrier the header's run lemma, the gated body, the ungated body and the ungated
loop's run already name — it consumes `utf8ForBodyUs_run` and `utf8Gated_body`,
whose forward and backward `getelementptr` sites read it, and nothing else here
carries `Classical.choice`.  `blk_split` is proved through
`take_append_take_len` and not through `List.take_add`, whose own proof term
carries `Classical.choice` that the statement does not need. -/

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.blk_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.blk_split

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.latch_keeps_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.latch_keeps_two

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.denoteCode_lookupName_of_not_dst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.denoteCode_lookupName_of_not_dst

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.withEnv_setJmp' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.withEnv_setJmp

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.evalOperand_reg_withEnv' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.evalOperand_reg_withEnv

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.packLanes_zipWith_or_reorder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.packLanes_zipWith_or_reorder

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8Gated_loop_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8Gated_loop_run

/-! ### The `ub` companion over the staged window

Every declaration `utf8_stage_undefined_of_no_read` introduces, at the footprint
each was measured at, in the order the section declares them: the entry and guard
arithmetic, the guard's own entry, the read ladder the statement's prefix needs,
the two loops' reach lemmas, the initial state's projections, and the companion
itself.

**One carrier appears, and it is inherited**: `utf8Ungated_reach`,
`utf8Gated_reach` and `utf8_stage_undefined_of_no_read` carry
`Classical.choice`, which is `step_gep64`'s `BitVec.signExtend_eq` — the reach
lemmas consume `utf8Ungated_body` and `utf8Gated_body`, and the companion
consumes `utf8ForBody_denote_none` and `utf8ForBodyUs_denote_none`, each of which
steps a `getelementptr` whose sign extension carries it.  Nothing else here
carries it: the entry arithmetic, the read ladder, the slice identities and the
pack facts are `propext`-only or `[propext, Quot.sound]`, and no proof reaches
`List.drop_take`, `Nat.div_lt_of_lt_mul` or `List.take_add`. -/

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.ofNat64_add63' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.ofNat64_add63

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.ofNat64_ushr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.ofNat64_ushr

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.div44_ofNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.div44_ofNat

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.ofNat64_ult_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.ofNat64_ult_false

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.prefix_readable_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.prefix_readable_bytes

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.win_read_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.win_read_len

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.win_read_slice_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.win_read_slice_len

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.stream_slice_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.stream_slice_at

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.packLanes_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.packLanes_word

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.packLanes_fits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.packLanes_fits

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8Ungated_reach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8Ungated_reach

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8Gated_reach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8Gated_reach

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.initState_utf8_pc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.initState_utf8_pc

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.lookupName_initState_utf8' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.lookupName_initState_utf8

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8_stage_undefined_of_no_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8_stage_undefined_of_no_read

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8_stage_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8_stage_refines

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8_stage_refines_chars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8_stage_refines_chars

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.utf8_stage_refines_mod0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.utf8_stage_refines_mod0

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.validPrefix_padded_iff_utf8Chars' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.validPrefix_padded_iff_utf8Chars

/-- info: 'LeanLLVM.Vellum.JsonUtf8Steps.t16_zero_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonUtf8Steps.t16_zero_iff


/-! ### The memory-aware records and their calls

`JsonUnitContracts.lean` states the three units' boundary records, proves each
one a `Satisfies` instance, and exercises the controls that make the records
non-vacuous.  The footprints below are measured at each declaration; the module
pins the same facts at its end, so a proof that reaches a new carrier fails in
either place. -/

/-- info: 'LeanLLVM.Vellum.ofNat_toNat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.ofNat_toNat

/-- info: 'LeanLLVM.Vellum.wordsAt_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.wordsAt_eq

/-- info: 'LeanLLVM.Vellum.masks_next_independent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.masks_next_independent

/-- info: 'LeanLLVM.Vellum.entry_pos8_next_independent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.entry_pos8_next_independent

/-- info: 'LeanLLVM.Vellum.entry_b8_next_independent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.entry_b8_next_independent

/-- info: 'LeanLLVM.Vellum.utf8_next_independent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.utf8_next_independent

/-- info: 'LeanLLVM.Vellum.masks_valueIrrelevant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.masks_valueIrrelevant

/-- info: 'LeanLLVM.Vellum.masks_written_extent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.masks_written_extent

/-- info: 'LeanLLVM.Vellum.masks_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.masks_satisfies

/-- info: 'LeanLLVM.Vellum.entry_pos8_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.entry_pos8_satisfies

/-- info: 'LeanLLVM.Vellum.entry_b8_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.entry_b8_satisfies

/-- info: 'LeanLLVM.Vellum.utf8_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.utf8_satisfies

/-- info: 'LeanLLVM.Vellum.masks_pre_inhabited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.masks_pre_inhabited

/-- info: 'LeanLLVM.Vellum.entry_pos8_pre_inhabited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.entry_pos8_pre_inhabited

/-- info: 'LeanLLVM.Vellum.entry_b8_pre_inhabited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.entry_b8_pre_inhabited

/-- info: 'LeanLLVM.Vellum.utf8_pre_inhabited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.utf8_pre_inhabited

/-- info: 'LeanLLVM.Vellum.masks_post_not_implied' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.masks_post_not_implied

/-- info: 'LeanLLVM.Vellum.entry_pos8_post_not_implied' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.entry_pos8_post_not_implied

/-- info: 'LeanLLVM.Vellum.entry_b8_post_not_implied' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.entry_b8_post_not_implied

/-- info: 'LeanLLVM.Vellum.utf8_post_not_implied' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.utf8_post_not_implied

/-- info: 'LeanLLVM.Vellum.masksStaged_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.masksStaged_satisfies

/-- info: 'LeanLLVM.Vellum.masksStaged_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.masksStaged_calls

/-- info: 'LeanLLVM.Vellum.masks_shifted_calls_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.masks_shifted_calls_refused

/-- info: 'LeanLLVM.Vellum.readsValue_not_valueIrrelevant' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.readsValue_not_valueIrrelevant

/-! ### The memory-aware relation's declarations

`LeanLLVM/Vellum/Refinement.lean` adds the relation and the two bridges.  Each
declaration C81 enumerates is pinned here, and the two bridges with them, so the
"nothing it adds is unpinned" clause is checked by the build rather than stated
in prose.  `wordsAt_eq` lives beside the extractor it decodes and is pinned in the
section above. -/

/-- info: 'LeanLLVM.Vellum.MemContract' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.MemContract

/-- info: 'LeanLLVM.Vellum.EntryState' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.EntryState

/-- info: 'LeanLLVM.Vellum.initState_eq_entryState' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.initState_eq_entryState

/-- info: 'LeanLLVM.Vellum.BehFromState' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.BehFromState

/-- info: 'LeanLLVM.Vellum.Satisfies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Satisfies

/-- info: 'LeanLLVM.Vellum.Satisfies.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Satisfies.mono

/-- info: 'LeanLLVM.Vellum.ValueIrrelevant' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.ValueIrrelevant

/-- info: 'LeanLLVM.Vellum.CallSatisfies' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.CallSatisfies

/-- info: 'LeanLLVM.Vellum.voidRet' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.voidRet

/-- info: 'LeanLLVM.Vellum.envForUnit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.envForUnit

/-- info: 'LeanLLVM.Vellum.retsValued' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.retsValued

/-- info: 'LeanLLVM.Vellum.ret_some_of_retsValued' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.ret_some_of_retsValued

/-- info: 'LeanLLVM.Vellum.wordsAt' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.wordsAt

/-- info: 'LeanLLVM.Vellum.satisfies_calls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.satisfies_calls

/-- info: 'LeanLLVM.Vellum.satisfies_calls_void' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.satisfies_calls_void


-- The composition law's other half: the refutation and its witness.

/-- info: 'LeanLLVM.Vellum.masksMispost_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.masksMispost_witness

/-- info: 'LeanLLVM.Vellum.masksMispost_not_satisfies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.masksMispost_not_satisfies

/-! ### The escape unit's pinned bodies

`JsonEscapeIR` parses `probes/install/ir/json-escape.candidate.ll` and pins the
four definitions it commits against literals.  The pin is restated here because
this file is compiled from source by the criterion's own evidence command: a
`#guard` in a library module is a claim about a build, and the fixture is a file
that can change independently of every module that reads it. -/

-- The fixture's four definitions, whole and in its order: the list entry point,
-- the expander's entry point, the decoder and the batch.
#guard decide
  ((parseModule JsonEscapeIR.escapeSrc).toOption.map (fun m => m.functions) =
    some [JsonEscapeIR.escapeListFunction, JsonEscapeIR.escapeExpandFunction,
      JsonEscapeIR.usDecFunction, JsonEscapeIR.xlBatchFunction])

-- The enumeration behind the shapes the two records are read at: 41 blocks and
-- 412 instruction lines over the four bodies.
#guard (JsonEscapeIR.escapeListFunction.blocks.length +
  JsonEscapeIR.escapeExpandFunction.blocks.length +
  JsonEscapeIR.usDecFunction.blocks.length +
  JsonEscapeIR.xlBatchFunction.blocks.length) = 41
#guard ((JsonEscapeIR.escapeListFunction.blocks.map (fun b => b.instrs.length)).sum +
  (JsonEscapeIR.escapeExpandFunction.blocks.map (fun b => b.instrs.length)).sum +
  (JsonEscapeIR.usDecFunction.blocks.map (fun b => b.instrs.length)).sum +
  (JsonEscapeIR.xlBatchFunction.blocks.map (fun b => b.instrs.length)).sum) = 412

-- The two entry points' parameter lists, as the fixture writes them.
#guard JsonEscapeIR.escapeListFunction.params.map (fun p => p.1) =
  ["%bs", "%ctl", "%im", "%blk0", "%xp", "%xn", "%carry"]
#guard JsonEscapeIR.usDecFunction.params.map (fun p => p.1) =
  ["%p", "%n", "%dst", "%err", "%xp", "%xj", "%nxp", "%pos0", "%tab"]

/-! ### The batch's record and its instance

`JsonEscapeBatch` states `Γ_xl_batch` and proves it of the pinned batch body; the
pins below are read here because this file is compiled from source on every
evidence run, so the axioms the batch rests on are checked by the same command
that checks the fixture pin above. -/

/-- info: 'LeanLLVM.Vellum.batch_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.batch_run

/-- info: 'LeanLLVM.Vellum.batchCount_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.batchCount_eq

/-- info: 'LeanLLVM.Vellum.Γ_xl_batch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.Γ_xl_batch

/-- info: 'LeanLLVM.Vellum.xl_batch_satisfies' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.xl_batch_satisfies

/-! ### The escape list's loop invariant and batch call site

`JsonEscapeListInvariant` states the batch loop's state and turns
`xl_batch_satisfies` into the call-site claim.  The pins are read here because
this file is compiled from source on every evidence run. -/

/-- info: 'LeanLLVM.Vellum.classCarryAt_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.classCarryAt_append

/-- info: 'LeanLLVM.Vellum.classCarryAt_oddRun' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.classCarryAt_oddRun

/-- info: 'LeanLLVM.Vellum.parityAt_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.parityAt_append

/-- info: 'LeanLLVM.Vellum.xl_batch_call_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.xl_batch_call_eq

/-- info: 'LeanLLVM.Vellum.ListLoopInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.ListLoopInv

/-! The list block's remaining two modules, at the ceiling.

`JsonEscapeListFixpoint` carries the `xl_lanes` doubling map in one lemma in two
halves: the rule's word is the map's fixed point, and thirty-two iterations from
the entry blocks' seed reach it.  `JsonEscapeBatchEntries` carries the batch's
store: the entry formula inside the population count, the exact eight-entry write
at `%o`, and the frame outside those thirty-two bytes.  Each fact is pinned at what
it holds without a carrier: `propext` and `Quot.sound`, and nothing from
`Classical`. -/

/-- info: 'LeanLLVM.Vellum.stepWord_specRunStarts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.stepWord_specRunStarts

/-- info: 'LeanLLVM.Vellum.stepN_escapeSeed_specRunStarts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.stepN_escapeSeed_specRunStarts

/-- info: 'LeanLLVM.Vellum.stepN_fixed_eq_specRunStarts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.stepN_fixed_eq_specRunStarts

/-- info: 'LeanLLVM.Vellum.stepN_32_is_fixed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.stepN_32_is_fixed

/-- info: 'LeanLLVM.Vellum.batchMem_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.batchMem_entry

/-- info: 'LeanLLVM.Vellum.batchMem_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.batchMem_read

/-- info: 'LeanLLVM.Vellum.batchMem_unchanged' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.batchMem_unchanged

/-- info: 'LeanLLVM.Vellum.batchMem_entry_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.batchMem_entry_value

/-- info: 'LeanLLVM.Vellum.setLanes_batchChain_eight' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.setLanes_batchChain_eight

/-! ### The escape list's entry trace

`JsonEscapeListLanes` identifies the loop's word with the position rule;
`JsonEscapeListBody` proves the three entry blocks' instruction runs and their
control steps, and states the seed equality.  The pins are read here because this
file is compiled from source on every evidence run. -/

/-- info: 'LeanLLVM.Vellum.setLanes_specPositionWord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.setLanes_specPositionWord

/-- info: 'LeanLLVM.Vellum.stepWord_fixed_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.stepWord_fixed_iff

/-- info: 'LeanLLVM.Vellum.seed_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.seed_eq

/-- info: 'LeanLLVM.Vellum.entry_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.entry_denote

/-- info: 'LeanLLVM.Vellum.ifThen_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.ifThen_denote

/-- info: 'LeanLLVM.Vellum.ifEnd_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.ifEnd_denote

/-- info: 'LeanLLVM.Vellum.entry_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.entry_step

/-- info: 'LeanLLVM.Vellum.ifThen_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.ifThen_step

/-- info: 'LeanLLVM.Vellum.ifEnd_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.ifEnd_step

/-- info: 'LeanLLVM.Vellum.seed_then_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.seed_then_run

/-- info: 'LeanLLVM.Vellum.seed_entry_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.seed_entry_run

/-- info: 'LeanLLVM.Vellum.LRun.runFuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.LRun.runFuel

/-! ### The loop fuel layer

`LoopFuel` carries the fuel induction for a loop whose exit test reads its own
carried word: a `runFuel` measure that is the iteration bound, and a step that
consumes the invariant and nothing about the exit word.  `JsonEscapeListLoop`
closes the escape list's `xl_lanes` loop on it, with the lane width's bound as the
measure.  Each fact is pinned at what it holds without a carrier. -/

/-- info: 'LeanLLVM.Vellum.CarriedLoop.run_from' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.CarriedLoop.run_from

/-- info: 'LeanLLVM.Vellum.CarriedLoop.run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.CarriedLoop.run

/-- info: 'LeanLLVM.Vellum.CarriedLoop.run_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.CarriedLoop.run_at

/-- info: 'LeanLLVM.Vellum.lstDoBody_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.lstDoBody_denote

/-- info: 'LeanLLVM.Vellum.lstDoBody_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.lstDoBody_step

/-- info: 'LeanLLVM.Vellum.bitVec_one_eq_zero_or_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.bitVec_one_eq_zero_or_one

/-- info: 'LeanLLVM.Vellum.lstLanesInv_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.lstLanesInv_entry

/-- info: 'LeanLLVM.Vellum.lstLanesLoop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.lstLanesLoop

/-- info: 'LeanLLVM.Vellum.lanes_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.lanes_run

/-- info: 'LeanLLVM.Vellum.lanes_run_from_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.lanes_run_from_head

/-- info: 'LeanLLVM.Vellum.lanes_run_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.lanes_run_at

/-! ### `JsonEscapeListRun` — the run after the lanes loop

The module sits above `JsonEscapeListLoop`, so its imports run one way:
`Run → ListLoop → ListBody → Steps`.  The pins are the trace's: the staging's byte
facts, the or/add identity the inlined first batch needs, and the four blocks after
the lanes loop. -/

/-- info: 'LeanLLVM.Vellum.carry_words' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.carry_words

/-- info: 'LeanLLVM.Vellum.b_load64_nat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.b_load64_nat

/-- info: 'LeanLLVM.Vellum.b_store64_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.b_store64_mem

/-- info: 'LeanLLVM.Vellum.b_gep4_reg32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.b_gep4_reg32

/-- info: 'LeanLLVM.Vellum.b_gep4_reg64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.b_gep4_reg64

/-- info: 'LeanLLVM.Vellum.b_zext32_64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.b_zext32_64

/-- info: 'LeanLLVM.Vellum.nat_lor_mul_two_pow_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.nat_lor_mul_two_pow_add

/-- info: 'LeanLLVM.Vellum.bv32_or_lane_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.bv32_or_lane_toNat

/-- info: 'LeanLLVM.Vellum.lstLanesExit_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.lstLanesExit_step

/-- info: 'LeanLLVM.Vellum.cSt8_eq_clearLow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.cSt8_eq_clearLow

/-- info: 'LeanLLVM.Vellum.lstForPre_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.lstForPre_step

/-- info: 'LeanLLVM.Vellum.lstWhilePre_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.lstWhilePre_step

/-- info: 'LeanLLVM.Vellum.lstEmitExit_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.lstEmitExit_step

/-! ### The decoder's loop instance, staging exclusions and budget

The block appended for `JsonEscapeDecodeRun.lean`; it begins at line 9514 and is
contiguous to the end of this file. -/

/-- info: 'LeanLLVM.Vellum.DecodeNoAlias' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.DecodeNoAlias

/-- info: 'LeanLLVM.Vellum.decodeNextIdx' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.decodeNextIdx

/-- info: 'LeanLLVM.Vellum.evalICmp_ult_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.evalICmp_ult_zero_iff

/-- info: 'LeanLLVM.Vellum.escapeExpandBudget' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.escapeExpandBudget

/-- info: 'LeanLLVM.Vellum.escapeExpandBudget_decomp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.escapeExpandBudget_decomp

/-- info: 'LeanLLVM.Vellum.signExtend_self_toNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.signExtend_self_toNat

/-- info: 'LeanLLVM.Vellum.decodeLatch_step_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.decodeLatch_step_exit

/-- info: 'LeanLLVM.Vellum.latchInv_budget' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.latchInv_budget

/-- info: 'LeanLLVM.Vellum.latchInv_exit_at_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.latchInv_exit_at_zero

/-- info: 'LeanLLVM.Vellum.decodeLatch_step_enter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.decodeLatch_step_enter

/-- info: 'LeanLLVM.Vellum.decodeWalkFuel_contribution' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.decodeWalkFuel_contribution

/-- info: 'LeanLLVM.Vellum.decodeRefuses' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.decodeRefuses

/-- info: 'LeanLLVM.Vellum.decodeTwoExit' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.decodeTwoExit

/-- info: 'LeanLLVM.Vellum.DecodeRefusalExit' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.DecodeRefusalExit

/-- info: 'LeanLLVM.Vellum.expandBodyLen' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.expandBodyLen

/-- info: 'LeanLLVM.Vellum.expandPosCount' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.expandPosCount

/-- info: 'LeanLLVM.Vellum.expandExitFuel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.expandExitFuel

/-- info: 'LeanLLVM.Vellum.ExpandSeed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.ExpandSeed

/-- info: 'LeanLLVM.Vellum.ExpandExit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.ExpandExit

/-- info: 'LeanLLVM.Vellum.run_stages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.run_stages

/-- info: 'LeanLLVM.Vellum.escape_expand_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.escape_expand_satisfies

/-! ### The assembled pipeline's fixture, census and call environment -/

/-- info: 'LeanLLVM.Vellum.JsonPipelineIR.pipelineBody' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonPipelineIR.pipelineBody

/-- info: 'LeanLLVM.Vellum.JsonPipelineIR.Γ_entry_pos8at' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonPipelineIR.Γ_entry_pos8at

/-- info: 'LeanLLVM.Vellum.JsonPipelineIR.envForPos8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonPipelineIR.envForPos8

/-- info: 'LeanLLVM.Vellum.JsonPipelineIR.satisfies_calls_pos8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonPipelineIR.satisfies_calls_pos8

/-- info: 'LeanLLVM.Vellum.JsonPipelineIR.pipelineCalls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonPipelineIR.pipelineCalls

/-- info: 'LeanLLVM.Vellum.JsonPipelineIR.pipelineCalls_masks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonPipelineIR.pipelineCalls_masks

/-! ### The generic block evaluator, and the pos8 no-gate arm's closed blocks -/

/-- info: 'LeanLLVM.Vellum.JsonPipelineBlockEval.entry_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonPipelineBlockEval.entry_denote

/-- info: 'LeanLLVM.Vellum.JsonPipelineBlockEval.cleanup_fromIfThen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonPipelineBlockEval.cleanup_fromIfThen

/-- info: 'LeanLLVM.Vellum.JsonPipelineBlockEval.cleanup_fromIfEnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonPipelineBlockEval.cleanup_fromIfEnd

/-- info: 'LeanLLVM.Vellum.JsonPipelineBlockEval.usUs_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonPipelineBlockEval.usUs_denote

/-! ### The expander's staged invariant and the empty-list entry run -/

/-- info: 'LeanLLVM.Vellum.AssemblyLatchInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.AssemblyLatchInv

/-- info: 'LeanLLVM.Vellum.assemblyLatchInv_latch' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.assemblyLatchInv_latch

/-- info: 'LeanLLVM.Vellum.assemblyLatchInv_params' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.assemblyLatchInv_params

/-- info: 'LeanLLVM.Vellum.assemblyLatchInv_paddr_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.assemblyLatchInv_paddr_eq

/-- info: 'LeanLLVM.Vellum.escAt_length_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.escAt_length_le

/-- info: 'LeanLLVM.Vellum.entryState_env' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.entryState_env

/-- info: 'LeanLLVM.Vellum.entryState_cells' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.entryState_cells

/-- info: 'LeanLLVM.Vellum.emptySeedRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.emptySeedRun

/-- info: 'LeanLLVM.Vellum.refusalReturn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.refusalReturn

/-! ### The staged arm statements and the two-exit instance -/

/-- info: 'LeanLLVM.Vellum.AssemblyLatchExit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.AssemblyLatchExit

/-- info: 'LeanLLVM.Vellum.AssemblyRefusalExit' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.AssemblyRefusalExit

/-- info: 'LeanLLVM.Vellum.assemblyExitWord' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.assemblyExitWord

/-- info: 'LeanLLVM.Vellum.assemblyLatchStepExit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.assemblyLatchStepExit

/-- info: 'LeanLLVM.Vellum.assemblyBoundLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.assemblyBoundLoop

/-- info: 'LeanLLVM.Vellum.assemblyBoundLoop_run_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.assemblyBoundLoop_run_at

/-! ### The refusal word's empty-memory consequence -/

/-- info: 'LeanLLVM.Vellum.readBytes_empty_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.readBytes_empty_succ

/-- info: 'LeanLLVM.Vellum.DecodeRefusalExit_mem_ne_nil' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.DecodeRefusalExit_mem_ne_nil

/-! ### The relational exit word and the two acceptance theorems -/

/-- info: 'LeanLLVM.Vellum.ExpandStaging' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.ExpandStaging

/-- info: 'LeanLLVM.Vellum.AssemblyLatchExit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.AssemblyLatchExit

/-- info: 'LeanLLVM.Vellum.AssemblyEntryExit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.AssemblyEntryExit

/-- info: 'LeanLLVM.Vellum.AssemblyWhileBody6Exit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.AssemblyWhileBody6Exit

/-- info: 'LeanLLVM.Vellum.AssemblyWhileBodyExit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.AssemblyWhileBodyExit

/-- info: 'LeanLLVM.Vellum.AssemblySuccessExit' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.AssemblySuccessExit

/-- info: 'LeanLLVM.Vellum.AssemblyRefusalExit' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.AssemblyRefusalExit

/-- info: 'LeanLLVM.Vellum.assemblyExitWord' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.assemblyExitWord

/-- info: 'LeanLLVM.Vellum.assemblyLatchInv_dest' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.assemblyLatchInv_dest

/-- info: 'LeanLLVM.Vellum.assemblyLatchInv_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.assemblyLatchInv_frame

/-- info: 'LeanLLVM.Vellum.assemblyLatchStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.assemblyLatchStep

/-- info: 'LeanLLVM.Vellum.assemblyRefusalArm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.assemblyRefusalArm

/-! #### Acceptance (a): every `phi` edge is admitted -/

/-- info: 'LeanLLVM.Vellum.admits_latchEdge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.admits_latchEdge

/-- info: 'LeanLLVM.Vellum.admits_entryEdge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.admits_entryEdge

/-- info: 'LeanLLVM.Vellum.admits_whileBody6Edge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.admits_whileBody6Edge

/-- info: 'LeanLLVM.Vellum.admits_whileBodyEdge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.admits_whileBodyEdge

/-- info: 'LeanLLVM.Vellum.admits_successEdge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.admits_successEdge

/-- info: 'LeanLLVM.Vellum.admits_refusalEdge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.admits_refusalEdge

/-! #### Acceptance (b): the two dead edges are excluded by the range clause -/

/-- info: 'LeanLLVM.Vellum.assemblyWhileBody6Exit_vacuous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.assemblyWhileBody6Exit_vacuous

/-- info: 'LeanLLVM.Vellum.assemblyWhileBodyExit_vacuous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.assemblyWhileBodyExit_vacuous

/-! #### `.exit`: the landed half, and the refutation kept as the reason -/

/-- info: 'LeanLLVM.Vellum.args_ptr_slots' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.args_ptr_slots

/-- info: 'LeanLLVM.Vellum.staging_ptr_slots' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.staging_ptr_slots

/-- info: 'LeanLLVM.Vellum.cleanup41Return' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.cleanup41Return

/-- info: 'LeanLLVM.Vellum.cleanup41SuccessReturn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.cleanup41SuccessReturn

/-- info: 'LeanLLVM.Vellum.refusalExit_post' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.refusalExit_post

/-- info: 'LeanLLVM.Vellum.successExit_post' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.successExit_post

/-- info: 'LeanLLVM.Vellum.stuckState_refusalExit_false' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.stuckState_refusalExit_false

/-- info: 'LeanLLVM.Vellum.assemblyExitWord_stuckState_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.assemblyExitWord_stuckState_false

/-! #### The emitter's arithmetic: the word, the surrogate range, the pair value -/

/-- info: 'LeanLLVM.Vellum.udIfEnd32Word_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.udIfEnd32Word_toNat

/-- info: 'LeanLLVM.Vellum.udIfEnd3I_highSurrogate_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.udIfEnd3I_highSurrogate_iff

/-- info: 'LeanLLVM.Vellum.udIfThen26I_pairValue' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.udIfThen26I_pairValue
