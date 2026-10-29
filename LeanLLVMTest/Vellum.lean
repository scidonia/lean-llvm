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
