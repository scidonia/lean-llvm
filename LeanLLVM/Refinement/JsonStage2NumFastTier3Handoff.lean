/-
Tier 3's copy: the nest's exit block, and the residual loop's entry.

`JsonStage2NumFastTier3CopyUnroll` proves the four-way unrolled nest at its own
blocks and leaves the exit block's `phi`s as the loop's exit word
(`t3MainExitWord`).  `JsonStage2NumFastTier3CopyLoop` proves the residual loop's
induction from its head, `T3EpilInv`, whose budget is the peel's residue
`%xtraiter`.  This module is the step between them: the exit block
`for.end100.i.i.loopexit.unr-lcssa`, and the entry of the residual loop at the
state the copy's exit word names.

**The exit block's two edges.**  The block is three `phi`s and one test:

* `%e.1.i.i.lcssa.ph`, `%i.3735.i.i.unr` and `%e.0734.i.i.unr`, whose incoming
  at the nest's latch is `%e.1.i.i.3`, `%inc99.i.i.3` and `%e.1.i.i.3`;
* `%lcmp.mod.not = (%xtraiter == 0)`, which is the block's own test.

So the block's step is a jump, and the test's two answers are the two edges: at
`%xtraiter = 0` it leaves for `for.end100.i.i`, the copy's exit — the residual
loop is not entered at all — and below that it leaves for the residual head,
`for.body87.i.i.epil`, with the nest's two carried words installed.

**The handoff's strict inequality.**  `t3MainExitWord` carries
`i.toNat + xt ≤ Nd`: the index plus the residue is inside the staging, not
strictly below it.  `T3EpilInv` needs two more things of that arithmetic.
`i.toNat + (xtraiter - c) ≤ N` at `c = 0` is the exit word's own inequality, so
it needs nothing extra; but the invariant also carries the store's bound,
`(evalICmp .slt e t3Cap = 1 → i.toNat < N)`, and `i < Nd` is strict only when the
residue is positive.  The invariant is inhabited only with a visit left
(`1 ≤ r` with `c + r = xtraiter`), so at `xtraiter = 0` there is no invariant
state at all — `t3EpilInv_zero_uninhabited` — and the strict form of the handoff
is therefore the true one: `t3_exit_handoff` takes `1 ≤ xt`, and at `xt = 0` the
exit block's own test is what finishes the copy (`t3_exit_zero_branch`), so the
residual loop is never entered and its invariant owes nothing.  Both branches
are proved below; the strict form is not a convenience.

There is no `sorry`, `admit` or `native_decide` below.
-/
import LeanLLVM.Refinement.JsonStage2NumFastTier3CopyUnroll

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonScanLane
open LeanLLVM.Refinement.NumFastTier3
open LeanLLVM.Refinement.NumFastTier3Copy
open LeanLLVM.Refinement.NumFastTier3CopyLoop
open LeanLLVM.Refinement.NumFastTier3CopyUnroll

namespace NumFastTier3Handoff

/-! ### The exit block, from its pin -/

/-- `for.end100.i.i.loopexit.unr-lcssa`: the nest's exit word. -/
def t3ExitInstrs : List Instr :=
  [Instr.phi "%e.1.i.i.lcssa.ph" (Ty.int 64)
     [("for.body87.i.i.preheader", (Operand.imm Const.poison)),
      ("for.inc98.i.i.3", (Operand.reg "%e.1.i.i.3"))],
   Instr.phi "%i.3735.i.i.unr" (Ty.int 64)
     [("for.body87.i.i.preheader", (Operand.reg "%i.2.i.i")),
      ("for.inc98.i.i.3", (Operand.reg "%inc99.i.i.3"))],
   Instr.phi "%e.0734.i.i.unr" (Ty.int 64)
     [("for.body87.i.i.preheader", (Operand.imm (Const.int 64 0x0000000000000000#64))),
      ("for.inc98.i.i.3", (Operand.reg "%e.1.i.i.3"))],
   Instr.icmp "%lcmp.mod.not" (IPred.eq) 64 (Operand.reg "%xtraiter")
     (Operand.imm (Const.int 64 0x0000000000000000#64))]

/-- The pin, at the named list: the block is the parse's. -/
theorem t3_exit_find :
    numFastBody.findBlock "for.end100.i.i.loopexit.unr-lcssa" =
      some ⟨"for.end100.i.i.loopexit.unr-lcssa", t3ExitInstrs,
        Term.condbr (Operand.reg "%lcmp.mod.not") "for.end100.i.i"
          "for.body87.i.i.epil"⟩ := by
  simpa only [t3ExitInstrs] using numFast_findBlock_for_end100_i_i_loopexit_unr_lcssa

/-- The environment the exit block installs at the nest's latch: the three
`phi`s (the accumulator twice and the index) and the residue's test. -/
def t3ExitEnv (env : Env) (ea i xt : BitVec 64) : Env :=
  ("%lcmp.mod.not", .int 1 (evalICmp .eq xt 0x0#64)) ::
  ("%e.0734.i.i.unr", .int 64 ea) :: ("%i.3735.i.i.unr", .int 64 i) ::
  ("%e.1.i.i.lcssa.ph", .int 64 ea) :: env

/-- The first `phi`'s selection at the latch's edge, as its pin writes it. -/
theorem t3_exit_phi_incoming_e :
    phiIncoming "for.inc98.i.i.3"
      [("for.body87.i.i.preheader", (Operand.imm Const.poison)),
       ("for.inc98.i.i.3", (Operand.reg "%e.1.i.i.3"))]
      = some (Operand.reg "%e.1.i.i.3") := by
  simp [phiIncoming]

/-- The index's `phi` selection at the latch's edge. -/
theorem t3_exit_phi_incoming_i :
    phiIncoming "for.inc98.i.i.3"
      [("for.body87.i.i.preheader", (Operand.reg "%i.2.i.i")),
       ("for.inc98.i.i.3", (Operand.reg "%inc99.i.i.3"))]
      = some (Operand.reg "%inc99.i.i.3") := by
  simp [phiIncoming]

/-- The accumulator's `phi` selection at the latch's edge: the same cell as the
first `phi`. -/
theorem t3_exit_phi_incoming_e2 :
    phiIncoming "for.inc98.i.i.3"
      [("for.body87.i.i.preheader", (Operand.imm (Const.int 64 0x0000000000000000#64))),
       ("for.inc98.i.i.3", (Operand.reg "%e.1.i.i.3"))]
      = some (Operand.reg "%e.1.i.i.3") := by
  simp [phiIncoming]

/-- **The exit block's chain.**  At the nest's latch the three `phi`s install the
exit word's index and accumulator, and the block's test reads `%xtraiter`. -/
theorem t3_exit_denote {calls : Calls} {env : Env} {s : State} {ea i xt : BitVec 64}
    (hpre : s.pre = some "for.inc98.i.i.3")
    (hea : lookupName env "%e.1.i.i.3" = some (.int 64 ea))
    (hi : lookupName env "%inc99.i.i.3" = some (.int 64 i))
    (hxt : lookupName env "%xtraiter" = some (.int 64 xt)) :
    denoteCode calls t3ExitInstrs (stateAt env s) =
      some (stateAt (t3ExitEnv env ea i xt) s) := by
  unfold t3ExitInstrs
  rw [t3_denoteCode_phi3 (calls := calls) (env := env) (s := s)
    "%e.1.i.i.lcssa.ph" (Ty.int 64) _
    "%i.3735.i.i.unr" (Ty.int 64) _
    "%e.0734.i.i.unr" (Ty.int 64) _
    [Instr.icmp "%lcmp.mod.not" (IPred.eq) 64 (Operand.reg "%xtraiter")
      (Operand.imm (Const.int 64 0x0000000000000000#64))]
    hpre t3_exit_phi_incoming_e
    (evalOperand_reg_of env s "%e.1.i.i.3" (.int 64 ea) hea)
    t3_exit_phi_incoming_i
    (evalOperand_reg_of env s "%inc99.i.i.3" (.int 64 i) hi)
    t3_exit_phi_incoming_e2
    (evalOperand_reg_of env s "%e.1.i.i.3" (.int 64 ea) hea)
    (hst := by rfl)]
  rw [denoteCode_icmp_imm_w calls
    (("%e.0734.i.i.unr", .int 64 ea) :: ("%i.3735.i.i.unr", .int 64 i) ::
      ("%e.1.i.i.lcssa.ph", .int 64 ea) :: env) s
    "%lcmp.mod.not" "%xtraiter" (IPred.eq)
    (by
      rw [lookupName_cons_ne (k := "%e.0734.i.i.unr") (n := "%xtraiter") _ _ (by decide),
        lookupName_cons_ne (k := "%i.3735.i.i.unr") (n := "%xtraiter") _ _ (by decide),
        lookupName_cons_ne (k := "%e.1.i.i.lcssa.ph") (n := "%xtraiter") _ _ (by decide)]
      exact hxt)]
  simp only [denoteCode_nil, t3ExitEnv, stateAt]

/-! ### The two edges

An unconditional branch after the test, so the block always leaves by a jump:
the residue's two answers are the copy's two continuations. -/

/-- **The copy's exit at a spent residue.**  At `%xtraiter = 0` the exit block
leaves for `for.end100.i.i`: there is no residual visit. -/
theorem t3_exit_step_zero {calls : Calls} {env : Env} {s : State} {ea i xt : BitVec 64}
    (hpc : s.pc = "for.end100.i.i.loopexit.unr-lcssa")
    (hpre : s.pre = some "for.inc98.i.i.3")
    (hea : lookupName env "%e.1.i.i.3" = some (.int 64 ea))
    (hi : lookupName env "%inc99.i.i.3" = some (.int 64 i))
    (hxt : lookupName env "%xtraiter" = some (.int 64 xt))
    (hbit : evalICmp .eq xt 0x0#64 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3ExitEnv env ea i xt)
        { s with pc := "for.end100.i.i",
                 pre := some "for.end100.i.i.loopexit.unr-lcssa" }) := by
  refine numFast_step_at (s' := stateAt (t3ExitEnv env ea i xt) s)
    (b := ⟨"for.end100.i.i.loopexit.unr-lcssa", t3ExitInstrs,
      Term.condbr (Operand.reg "%lcmp.mod.not") "for.end100.i.i"
        "for.body87.i.i.epil"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using t3_exit_find
  · exact t3_exit_denote hpre hea hi hxt
  · rw [numFast_execTerm_condbr_one _ "%lcmp.mod.not" "for.end100.i.i"
      "for.body87.i.i.epil" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- **The residual loop's entry at a live residue.**  At a nonzero residue the
exit block leaves for `for.body87.i.i.epil`, installing the nest's two carried
words under the names the residual head's `phi`s read. -/
theorem t3_exit_step_pos {calls : Calls} {env : Env} {s : State} {ea i xt : BitVec 64}
    (hpc : s.pc = "for.end100.i.i.loopexit.unr-lcssa")
    (hpre : s.pre = some "for.inc98.i.i.3")
    (hea : lookupName env "%e.1.i.i.3" = some (.int 64 ea))
    (hi : lookupName env "%inc99.i.i.3" = some (.int 64 i))
    (hxt : lookupName env "%xtraiter" = some (.int 64 xt))
    (hbit : evalICmp .eq xt 0x0#64 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3ExitEnv env ea i xt)
        { s with pc := "for.body87.i.i.epil",
                 pre := some "for.end100.i.i.loopexit.unr-lcssa" }) := by
  refine numFast_step_at (s' := stateAt (t3ExitEnv env ea i xt) s)
    (b := ⟨"for.end100.i.i.loopexit.unr-lcssa", t3ExitInstrs,
      Term.condbr (Operand.reg "%lcmp.mod.not") "for.end100.i.i"
        "for.body87.i.i.epil"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using t3_exit_find
  · exact t3_exit_denote hpre hea hi hxt
  · rw [numFast_execTerm_condbr_zero _ "%lcmp.mod.not" "for.end100.i.i"
      "for.body87.i.i.epil" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-! ### The exit block's environment, read through its four bindings

The three `phi`s sit above the exit word's environment and the test sits above
them, so every other name reads through the block's own cells. -/

/-- The exit word's two `phi` cells, at the environment the block installs. -/
theorem t3ExitEnv_unr_cells {env : Env} {ea i xt : BitVec 64} :
    lookupName (t3ExitEnv env ea i xt) "%i.3735.i.i.unr" = some (.int 64 i) ∧
    lookupName (t3ExitEnv env ea i xt) "%e.0734.i.i.unr" = some (.int 64 ea) := by
  refine ⟨?_, ?_⟩
  · simp only [t3ExitEnv]
    rw [lookupName_cons_ne (k := "%lcmp.mod.not") (n := "%i.3735.i.i.unr") _ _ (by decide),
      lookupName_cons_ne (k := "%e.0734.i.i.unr") (n := "%i.3735.i.i.unr") _ _ (by decide),
      lookupName_cons_self]
  · simp only [t3ExitEnv]
    rw [lookupName_cons_ne (k := "%lcmp.mod.not") (n := "%e.0734.i.i.unr") _ _ (by decide),
      lookupName_cons_self]

/-- The names the residual invariant reads through the block's cells. -/
theorem t3ExitEnv_other (env : Env) (ea i xt : BitVec 64) :
    lookupName (t3ExitEnv env ea i xt) "%p" = lookupName env "%p" ∧
    lookupName (t3ExitEnv env ea i xt) "%dig.i.i" = lookupName env "%dig.i.i" ∧
    lookupName (t3ExitEnv env ea i xt) "%xtraiter" = lookupName env "%xtraiter" := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [t3ExitEnv]
    rw [lookupName_cons_ne (k := "%lcmp.mod.not") (n := "%p") _ _ (by decide),
      lookupName_cons_ne (k := "%e.0734.i.i.unr") (n := "%p") _ _ (by decide),
      lookupName_cons_ne (k := "%i.3735.i.i.unr") (n := "%p") _ _ (by decide),
      lookupName_cons_ne (k := "%e.1.i.i.lcssa.ph") (n := "%p") _ _ (by decide)]
  · simp only [t3ExitEnv]
    rw [lookupName_cons_ne (k := "%lcmp.mod.not") (n := "%dig.i.i") _ _ (by decide),
      lookupName_cons_ne (k := "%e.0734.i.i.unr") (n := "%dig.i.i") _ _ (by decide),
      lookupName_cons_ne (k := "%i.3735.i.i.unr") (n := "%dig.i.i") _ _ (by decide),
      lookupName_cons_ne (k := "%e.1.i.i.lcssa.ph") (n := "%dig.i.i") _ _ (by decide)]
  · simp only [t3ExitEnv]
    rw [lookupName_cons_ne (k := "%lcmp.mod.not") (n := "%xtraiter") _ _ (by decide),
      lookupName_cons_ne (k := "%e.0734.i.i.unr") (n := "%xtraiter") _ _ (by decide),
      lookupName_cons_ne (k := "%i.3735.i.i.unr") (n := "%xtraiter") _ _ (by decide),
      lookupName_cons_ne (k := "%e.1.i.i.lcssa.ph") (n := "%xtraiter") _ _ (by decide)]

/-! ### The handoff, and why its inequality is strict -/

/-- **The residual invariant is uninhabited at a spent residue.**  `T3EpilInv`
carries `1 ≤ r` with `c + r = xtraiter`, so `xtraiter = 0` has no state: the
copy's `xt = 0` branch owes the residual loop nothing. -/
theorem t3EpilInv_zero_uninhabited (p digA N : Nat) (s : State) (c : Nat) :
    ¬ T3EpilInv p digA N 0 0 s c := by
  intro h
  have hpos := T3EpilInv.rpos h
  omega

/-- **The handoff.**  From the nest's exit word, at a residue with a visit left,
the exit block's step reaches the residual head and the invariant holds there at
the whole residue with no visit counted: the index and the accumulator are the
exit word's, the staging is the copy's, and the store's strict bound follows from
`1 ≤ xt` and the exit word's `i + xt ≤ Nd`.  One control step. -/
theorem t3_exit_handoff {calls : Calls} {p digA Nd xt : Nat} {e : State}
    (hpc : t3MainExit e) (h : t3MainExitWord p digA Nd xt e) (hxt : 1 ≤ xt) :
    ∃ (f : State) (j : Nat), j ≤ 1 ∧ T3EpilInv p digA Nd xt xt f 0 ∧
      ∀ k, runFuel calls (j + k) numFastBody (stateAt e.env e) =
        runFuel calls k numFastBody f := by
  obtain ⟨hpre, hp, hdig, hx, hstage, hnd, hxt3, i, ea, hinc, hea, hi63, hea7, hle⟩ := h
  have hne : BitVec.ofNat 64 xt ≠ (0x0#64 : BitVec 64) := by
    intro hh
    have h2 := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h2
    simp only [BitVec.toNat_ofNat, Nat.zero_mod] at h2
    omega
  have hbit : evalICmp .eq (BitVec.ofNat 64 xt) 0x0#64 = (0 : BitVec 1) :=
    t3_icmp_eq_zero hne
  have hstep : step calls numFastBody (stateAt e.env e) =
      .jump (stateAt (t3ExitEnv e.env ea i (BitVec.ofNat 64 xt))
        { e with pc := "for.body87.i.i.epil",
                 pre := some "for.end100.i.i.loopexit.unr-lcssa" }) :=
    t3_exit_step_pos (calls := calls) hpc hpre hea hinc hx hbit
  have hunr := t3ExitEnv_unr_cells (env := e.env) (ea := ea) (i := i)
    (xt := BitVec.ofNat 64 xt)
  have hoth := t3ExitEnv_other e.env ea i (BitVec.ofNat 64 xt)
  refine ⟨stateAt (t3ExitEnv e.env ea i (BitVec.ofNat 64 xt))
    { e with pc := "for.body87.i.i.epil",
             pre := some "for.end100.i.i.loopexit.unr-lcssa" }, 1, le_rfl, ?_, ?_⟩
  · refine ⟨rfl, ?_, ?_, ?_, ?_, hnd, hxt3, ?_, hxt, by omega⟩
    · simp only [stateAt]
      rw [hoth.1]
      exact hp
    · simp only [stateAt]
      rw [hoth.2.1]
      exact hdig
    · simp only [stateAt]
      rw [hoth.2.2]
      exact hx
    · intro k hk
      exact hstage k hk
    · refine ⟨i, ea, hi63, hea7, by omega, by omega, Or.inl ⟨rfl, hunr.1, hunr.2, rfl⟩⟩
  · intro k
    exact runFuel_jump_prefix hstep k

/-- **The spent-residue branch.**  At `xt = 0` the exit block leaves for the
copy's own exit block, and no residual visit follows: the branch is the exit
block's own test, not a handoff. -/
theorem t3_exit_zero_branch {calls : Calls} {p digA Nd : Nat} {e : State}
    (hpc : t3MainExit e) (h : t3MainExitWord p digA Nd 0 e) :
    ∃ (f : State) (j : Nat), j ≤ 1 ∧
      f.pc = "for.end100.i.i" ∧
      f.pre = some "for.end100.i.i.loopexit.unr-lcssa" ∧
      (∀ c, ¬ T3EpilInv p digA Nd 0 0 f c) ∧
      ∀ k, runFuel calls (j + k) numFastBody (stateAt e.env e) =
        runFuel calls k numFastBody f := by
  obtain ⟨hpre, _, _, hx, _, _, _, i, ea, hinc, hea, _, _, _⟩ := h
  have hbit : evalICmp .eq (BitVec.ofNat 64 0) 0x0#64 = (1 : BitVec 1) := by
    have hz : BitVec.ofNat 64 0 = (0x0#64 : BitVec 64) := rfl
    rw [hz]
    exact evalICmp_eq_refl _
  have hstep : step calls numFastBody (stateAt e.env e) =
      .jump (stateAt (t3ExitEnv e.env ea i (BitVec.ofNat 64 0))
        { e with pc := "for.end100.i.i",
                 pre := some "for.end100.i.i.loopexit.unr-lcssa" }) :=
    t3_exit_step_zero (calls := calls) hpc hpre hea hinc hx hbit
  refine ⟨stateAt (t3ExitEnv e.env ea i (BitVec.ofNat 64 0))
    { e with pc := "for.end100.i.i",
             pre := some "for.end100.i.i.loopexit.unr-lcssa" }, 1, le_rfl, rfl, rfl, ?_, ?_⟩
  · intro c hc
    exact t3EpilInv_zero_uninhabited p digA Nd _ c hc
  · intro k
    exact runFuel_jump_prefix hstep k

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.NumFastTier3Handoff.t3_exit_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms t3_exit_denote

/-- info: 'LeanLLVM.Refinement.NumFastTier3Handoff.t3_exit_step_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms t3_exit_step_pos

/-- info: 'LeanLLVM.Refinement.NumFastTier3Handoff.t3_exit_handoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms t3_exit_handoff

/-- info: 'LeanLLVM.Refinement.NumFastTier3Handoff.t3EpilInv_zero_uninhabited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms t3EpilInv_zero_uninhabited

/-- info: 'LeanLLVM.Refinement.NumFastTier3Handoff.t3_exit_zero_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms t3_exit_zero_branch

end NumFastTier3Handoff

end LeanLLVM.Refinement
