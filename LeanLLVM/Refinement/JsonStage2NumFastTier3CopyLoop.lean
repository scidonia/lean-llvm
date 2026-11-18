/-
Tier 3's residual copy loop: its measure, invariant and exit.

`JsonStage2NumFastTier3CopySteps` gives the ladder's per-edge steps.  This module
fixes the *shape* of the residual loop's induction — the head, the exit block, the
bound, the cost, the invariant, the exit test and the exit's word — and takes the
loop's two visits as parameters, the shape `numFastScanBoundLoop` fixes for the
digit run.  The visits themselves are runs over four blocks of concrete cells and
are the piece not discharged here; nothing else about the induction is assumed.

**The measure.**  The counter `%epil.iter` runs from zero to the peel's residue
`%xtraiter`; the latch's own test is `%epil.iter + 1 = %xtraiter`, so the
invariant is inhabited only while at least one visit is left (`1 ≤ r` with
`c + r = xtraiter`), and a visit costs three control steps — the test, the store
when the accumulator is below the cap, and the latch.  `exit_at_zero` is
therefore vacuous by construction: a state at the head with no visit left is not
an invariant state.  That is what makes the loop's contribution to a record's
budget `(xtraiter + 1) * 3`, a term of the caller's arguments.

**What the invariant carries.**  The two carried words (the digit index and the
accumulator), the staging the store reads — every index below the digit count
reads a digit byte — and the edge, because the head's `phi` reads the
predecessor's cells: the loop-exit block's on the first visit, the latch's on
every later one.  The store block writes no memory, so the loop's memory is the
staging's and the digit facts are carried rather than re-derived.
-/
import LeanLLVM.Refinement.JsonStage2NumFastTier3CopySteps
import LeanLLVM.Refinement.LoopFuel

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.NumFastTier3Copy

namespace NumFastTier3CopyLoop

/-- The residual copy loop's state at its head. -/
def T3EpilInv (p digA N xtraiter : Nat) (r : Nat) (s : State) (c : Nat) : Prop :=
  s.pc = "for.body87.i.i.epil" ∧
  lookupName s.env "%p" = some (.ptr p) ∧
  lookupName s.env "%dig.i.i" = some (.ptr digA) ∧
  lookupName s.env "%xtraiter" = some (.int 64 (BitVec.ofNat 64 xtraiter)) ∧
  (∀ k, k < N → ∃ d, readBytes s.mem (p + k) 1 = some [d] ∧
    48 ≤ d.toNat ∧ d.toNat ≤ 57) ∧
  N < 2 ^ 63 ∧
  xtraiter ≤ 3 ∧
  (∃ (i e : BitVec 64),
    i.toNat < 2 ^ 63 ∧ e.toNat < 10 ^ 7 ∧
    i.toNat + (xtraiter - c) ≤ N ∧
    (evalICmp .slt e t3Cap = (1 : BitVec 1) → i.toNat < N) ∧
    ((s.pre = some "for.end100.i.i.loopexit.unr-lcssa" ∧
        lookupName s.env "%i.3735.i.i.unr" = some (.int 64 i) ∧
        lookupName s.env "%e.0734.i.i.unr" = some (.int 64 e) ∧ c = 0)
      ∨ (s.pre = some "for.inc98.i.i.epil" ∧
        lookupName s.env "%inc99.i.i.epil" = some (.int 64 i) ∧
        lookupName s.env "%e.1.i.i.epil" = some (.int 64 e) ∧
        lookupName s.env "%epil.iter.next" =
          some (.int 64 (BitVec.ofNat 64 c))))) ∧
  1 ≤ r ∧ c + r = xtraiter

/-- The invariant is inhabited only with a visit left. -/
theorem T3EpilInv.rpos {p digA N xtraiter r : Nat} {s : State} {c : Nat}
    (h : T3EpilInv p digA N xtraiter r s c) : 1 ≤ r :=
  h.2.2.2.2.2.2.2.2.1

/-- The counter and the budget are the peel's residue. -/
theorem T3EpilInv.cr {p digA N xtraiter r : Nat} {s : State} {c : Nat}
    (h : T3EpilInv p digA N xtraiter r s c) : c + r = xtraiter :=
  h.2.2.2.2.2.2.2.2.2

/-- The residual loop's exit test: the latch's counter has one step left. -/
def t3EpilAtBound (xtraiter : Nat) : State → Nat → Bool :=
  fun _ c => decide (xtraiter ≤ c + 1)

/-- The residual loop leaves for the copy's exit block. -/
def t3EpilExit : State → Prop := fun e => e.pc = "for.end100.i.i"

/-- **The residual copy loop's shape.**  `step_exit` and `step_loop` are its two
visits: the test, the store when the accumulator is below the cap, and the latch,
at an exact count within the three steps a visit costs.  Everything else — the
head, the exit block, the bound, the invariant, the exit test and the budget — is
fixed here, and `run_at` below is the induction at that shape. -/
def t3EpilLoopOf (calls : Calls) (p digA N xtraiter : Nat)
    (ExitW : State → Prop)
    (step_exit : ∀ (r : Nat) (s : State) (c : Nat),
      T3EpilInv p digA N xtraiter r s c → t3EpilAtBound xtraiter s c = true →
      ∃ (e : State) (j : Nat), j ≤ 3 ∧ t3EpilExit e ∧ ExitW e ∧
        ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e)
    (step_loop : ∀ (r : Nat) (s : State) (c : Nat),
      T3EpilInv p digA N xtraiter (r + 1) s c →
      t3EpilAtBound xtraiter s c = false →
      ∃ (e : State) (c' : Nat) (j : Nat), j ≤ 3 ∧
        e.pc = "for.body87.i.i.epil" ∧ c < c' ∧
        T3EpilInv p digA N xtraiter r e c' ∧
        ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e) :
    BoundLoop calls numFastBody where
  head := "for.body87.i.i.epil"
  exitBlock := "for.end100.i.i"
  N := xtraiter
  cost := 3
  Inv := T3EpilInv p digA N xtraiter
  atBound := t3EpilAtBound xtraiter
  Exit := t3EpilExit
  ExitWord := ExitW
  step_exit := step_exit
  step_loop := step_loop
  exit_at_zero := by
    intro s c h
    exact absurd (T3EpilInv.rpos h) (by omega)
  budget := by
    intro r s c h
    have hcr := T3EpilInv.cr h
    exact ⟨by omega, by omega⟩

/-- **The residual loop from its head.**  At the whole bound as its budget the run
reaches the copy's exit block within `(xtraiter + 1) * 3` control steps — a term
of the caller's arguments — and leaves the exit block's predecessor and the
accumulator its `phi` reads. -/
theorem t3EpilLoop_run_at (calls : Calls) (p digA N xtraiter : Nat)
    (ExitW : State → Prop)
    (step_exit : ∀ (r : Nat) (s : State) (c : Nat),
      T3EpilInv p digA N xtraiter r s c → t3EpilAtBound xtraiter s c = true →
      ∃ (e : State) (j : Nat), j ≤ 3 ∧ t3EpilExit e ∧ ExitW e ∧
        ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e)
    (step_loop : ∀ (r : Nat) (s : State) (c : Nat),
      T3EpilInv p digA N xtraiter (r + 1) s c →
      t3EpilAtBound xtraiter s c = false →
      ∃ (e : State) (c' : Nat) (j : Nat), j ≤ 3 ∧
        e.pc = "for.body87.i.i.epil" ∧ c < c' ∧
        T3EpilInv p digA N xtraiter r e c' ∧
        ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e)
    (s : State) (c : Nat) (h : T3EpilInv p digA N xtraiter xtraiter s c)
    (k : Nat) {o : Outcome}
    (hcont : ∀ (e : State), t3EpilExit e → ExitW e →
      runFuel calls k numFastBody e = some o) :
    runFuel calls ((xtraiter + 1) * 3 + k) numFastBody s = some o :=
  (t3EpilLoopOf calls p digA N xtraiter ExitW step_exit step_loop).run_at s c h k hcont

/-! ### Axiom footprints -/

#print axioms T3EpilInv.rpos
#print axioms T3EpilInv.cr
#print axioms t3EpilLoopOf
#print axioms t3EpilLoop_run_at

end NumFastTier3CopyLoop

end LeanLLVM.Refinement
