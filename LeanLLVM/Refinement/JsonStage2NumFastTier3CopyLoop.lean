/-
Tier 3's residual copy loop: its measure, invariant and exit.

`JsonStage2NumFastTier3CopySteps` gives the ladder's per-edge steps.  This module
fixes the *shape* of the residual loop's induction — the head, the exit block, the
bound, the cost, the invariant, the exit test and the exit's word — the shape
`numFastScanBoundLoop` fixes for the digit run, and then discharges its two
visits: `t3Epil_step_exit_test` and `t3Epil_step_loop_test` are `runFuel` chains
of at most three control steps over the concrete latch/test/store states, so
`t3EpilLoop` is the loop's induction at the emitted blocks and
`t3EpilLoop_run_at'` is its budget at a caller's continuation.

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
open LeanLLVM.Refinement.JsonScanLane
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

/-! ### The two visits

`t3EpilLoopOf` takes the residual loop's two visits as parameters.  They are the
two theorems below: one iteration is the head's test, the store when the
accumulator is below `10 ^ 6`, and the latch, at the state `T3EpilInv` names.
Each is a `runFuel` chain of at most three control steps from the concrete
latch/test/store states, so `t3EpilLoopOf`'s two parameters are filled and the
loop's budget `(xtraiter + 1) * 3` is a term of the arguments.

`t3EpilAtBound` is `decide (xtraiter ≤ c + 1)`; the two arms read it as that
inequality.  The environments a visit crosses are the head's, the store's and the
latch's, and each lookup below is either a name outside one of them or the one
cell the visit needs.

The exit word is what `for.end100.i.i`'s `phi` takes: the peel's residue, the
staging the copy read (the store writes no memory), and the two words the latch
carried out.  The visits keep the index and the accumulator within their bounds:
`i.toNat < N` at every store, and `10 * e + d < 10 ^ 7` after one. -/

theorem t3EpilAtBound_true {xtraiter c : Nat} {s : State}
    (h : t3EpilAtBound xtraiter s c = true) : xtraiter ≤ c + 1 := by
  simpa only [t3EpilAtBound, decide_eq_true_eq] using h

theorem t3EpilAtBound_false {xtraiter c : Nat} {s : State}
    (h : t3EpilAtBound xtraiter s c = false) : ¬ xtraiter ≤ c + 1 := by
  simpa only [t3EpilAtBound, decide_eq_false_iff_not] using h

theorem t3_stateAt_env_self (s : State) : stateAt s.env s = s := rfl

theorem t3_signExtend_self_toNat (x : BitVec 64) : (x.signExtend 64).toNat = x.toNat := by
  rw [BitVec.signExtend_eq]

theorem t3Epil_ofNat_succ {c : Nat} (h : c + 1 < 2 ^ 64) :
    BitVec.ofNat 64 c + 0x1#64 = BitVec.ofNat 64 (c + 1) := by
  apply BitVec.toNat_inj.mp
  have hx : c % 2 ^ 64 = c := Nat.mod_eq_of_lt (by omega)
  have hy : (1 : Nat) % 2 ^ 64 = 1 := Nat.mod_eq_of_lt (by decide)
  have hz : (c + 1) % 2 ^ 64 = c + 1 := Nat.mod_eq_of_lt (by omega)
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hx, hy, hz]

theorem t3_add_one_toNat {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 0x1#64).toNat = x.toNat + 1 := by
  have h1 : (0x0000000000000001#64 : BitVec 64).toNat = 1 := by decide
  rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt h]

/-- The store block's environment as the residual latch sees it. -/
def t3EpilStore (env : Env) (e : BitVec 64) (d : UInt8) (a : Nat) : Env :=
  t3StoreEnv env "%mul91.i.i.epil" "%arrayidx92.i.i.epil" "%68" "%conv93.i.i.epil"
    "%sub94.i.i.epil" "%add96.i.i.epil" e d a

/-- The residual latch's environment. -/
def t3EpilLatch (env : Env) (e i n u : BitVec 64) : Env :=
  t3LatchEnv env "%e.1.i.i.epil" "%inc99.i.i.epil" "%epil.iter.next"
    "%epil.iter.cmp.not" e i n u

/-- The accumulator the store block writes. -/
def t3EpilStoreAdd96 (e : BitVec 64) (d : UInt8) : BitVec 64 :=
  ((e * 10#64) + 0xffffffffffffffd0#64) + BitVec.ofNat 64 (vByte d).toNat

/-- The state a visit leaves at the residual head. -/
def t3EpilBackState (env : Env) (base : State) (xtraiter : Nat) (e i n : BitVec 64) : State :=
  stateAt (t3EpilLatch env e i n (BitVec.ofNat 64 xtraiter))
    { base with pc := "for.body87.i.i.epil", pre := some "for.inc98.i.i.epil" }

/-- The state a visit leaves at the copy's exit block. -/
def t3EpilExitState (env : Env) (base : State) (xtraiter : Nat) (e i n : BitVec 64) : State :=
  stateAt (t3EpilLatch env e i n (BitVec.ofNat 64 xtraiter))
    { base with pc := "for.end100.i.i", pre := some "for.inc98.i.i.epil" }

/-- The state the residual head leaves for its store. -/
def t3EpilStoreState (env : Env) (i e n : BitVec 64) (base : State) : State :=
  stateAt (t3EpilHeadEnv env i e n)
    { base with pc := "if.then90.i.i.epil", pre := some "for.body87.i.i.epil" }

/-- The state the residual head leaves past its store. -/
def t3EpilSkipState (env : Env) (i e n : BitVec 64) (base : State) : State :=
  stateAt (t3EpilHeadEnv env i e n)
    { base with pc := "for.inc98.i.i.epil", pre := some "for.body87.i.i.epil" }

/-- The state the residual store leaves. -/
def t3EpilStoredState (env : Env) (e : BitVec 64) (d : UInt8) (a : Nat)
    (base : State) : State :=
  stateAt (t3EpilStore env e d a)
    { base with pc := "for.inc98.i.i.epil", pre := some "if.then90.i.i.epil" }

theorem t3EpilHeadEnv_lookup_other (env : Env) (i e n : BitVec 64) {c : String}
    (h1 : c ≠ "%cmp88.i.i.epil" := by decide) (h2 : c ≠ "%epil.iter" := by decide)
    (h3 : c ≠ "%e.0734.i.i.epil" := by decide) (h4 : c ≠ "%i.3735.i.i.epil" := by decide) :
    lookupName (t3EpilHeadEnv env i e n) c = lookupName env c := by
  simp only [t3EpilHeadEnv]
  rw [lookupName_cons_ne _ _ (Ne.symm h1), lookupName_cons_ne _ _ (Ne.symm h2),
    lookupName_cons_ne _ _ (Ne.symm h3), lookupName_cons_ne _ _ (Ne.symm h4)]

theorem t3EpilHeadEnv_i (env : Env) (i e n : BitVec 64) :
    lookupName (t3EpilHeadEnv env i e n) "%i.3735.i.i.epil" = some (.int 64 i) := by
  simp only [t3EpilHeadEnv]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide), lookupName_cons_self]

theorem t3EpilHeadEnv_e (env : Env) (i e n : BitVec 64) :
    lookupName (t3EpilHeadEnv env i e n) "%e.0734.i.i.epil" = some (.int 64 e) := by
  simp only [t3EpilHeadEnv]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_self]

theorem t3EpilHeadEnv_iter (env : Env) (i e n : BitVec 64) :
    lookupName (t3EpilHeadEnv env i e n) "%epil.iter" = some (.int 64 n) := by
  simp only [t3EpilHeadEnv]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]

theorem t3EpilStoreEnv_lookup_other (env : Env) (e : BitVec 64) (d : UInt8)
    (a : Nat) {c : String}
    (h1 : c ≠ "%add96.i.i.epil" := by decide) (h2 : c ≠ "%sub94.i.i.epil" := by decide)
    (h3 : c ≠ "%conv93.i.i.epil" := by decide) (h4 : c ≠ "%68" := by decide)
    (h5 : c ≠ "%arrayidx92.i.i.epil" := by decide)
    (h6 : c ≠ "%mul91.i.i.epil" := by decide) :
    lookupName (t3EpilStore env e d a) c = lookupName env c := by
  simp only [t3EpilStore, t3StoreEnv]
  rw [lookupName_cons_ne _ _ (Ne.symm h1), lookupName_cons_ne _ _ (Ne.symm h2),
    lookupName_cons_ne _ _ (Ne.symm h3), lookupName_cons_ne _ _ (Ne.symm h4),
    lookupName_cons_ne _ _ (Ne.symm h5), lookupName_cons_ne _ _ (Ne.symm h6)]

theorem t3EpilStore_add96 (env : Env) (e : BitVec 64) (d : UInt8) (a : Nat) :
    lookupName (t3EpilStore env e d a) "%add96.i.i.epil"
      = some (.int 64 (t3EpilStoreAdd96 e d)) := by
  simp only [t3EpilStore, t3StoreEnv, t3EpilStoreAdd96]
  exact lookupName_cons_self ..

theorem t3EpilStore_i (env : Env) (e : BitVec 64) (d : UInt8) (a : Nat)
    (i e0 n : BitVec 64) :
    lookupName (t3EpilStore (t3EpilHeadEnv env i e0 n) e d a) "%i.3735.i.i.epil"
      = some (.int 64 i) := by
  rw [t3EpilStoreEnv_lookup_other, t3EpilHeadEnv_i]

theorem t3EpilStore_iter (env : Env) (e : BitVec 64) (d : UInt8) (a : Nat)
    (i e0 n0 : BitVec 64) :
    lookupName (t3EpilStore (t3EpilHeadEnv env i e0 n0) e d a) "%epil.iter"
      = some (.int 64 n0) := by
  rw [t3EpilStoreEnv_lookup_other, t3EpilHeadEnv_iter]

theorem t3EpilStore_xt (env : Env) (e : BitVec 64) (d : UInt8) (a : Nat)
    (i e0 n0 : BitVec 64) :
    lookupName (t3EpilStore (t3EpilHeadEnv env i e0 n0) e d a) "%xtraiter"
      = lookupName env "%xtraiter" := by
  rw [t3EpilStoreEnv_lookup_other, t3EpilHeadEnv_lookup_other]

theorem t3EpilStore_e (env : Env) (e : BitVec 64) (d : UInt8) (a : Nat)
    (i e0 n0 : BitVec 64) :
    lookupName (t3EpilStore (t3EpilHeadEnv env i e0 n0) e d a) "%e.0734.i.i.epil"
      = some (.int 64 e0) := by
  rw [t3EpilStoreEnv_lookup_other, t3EpilHeadEnv_e]

theorem t3EpilLatchEnv_lookup_other (env : Env) (e i n u : BitVec 64) {c : String}
    (h1 : c ≠ "%epil.iter.cmp.not" := by decide)
    (h2 : c ≠ "%epil.iter.next" := by decide)
    (h3 : c ≠ "%inc99.i.i.epil" := by decide) (h4 : c ≠ "%e.1.i.i.epil" := by decide) :
    lookupName (t3EpilLatch env e i n u) c = lookupName env c := by
  simp only [t3EpilLatch, t3LatchEnv]
  rw [lookupName_cons_ne _ _ (Ne.symm h1), lookupName_cons_ne _ _ (Ne.symm h2),
    lookupName_cons_ne _ _ (Ne.symm h3), lookupName_cons_ne _ _ (Ne.symm h4)]

theorem t3EpilLatchEnv_inc99 (env : Env) (e i n u : BitVec 64) :
    lookupName (t3EpilLatch env e i n u) "%inc99.i.i.epil" = some (.int 64 i) := by
  simp only [t3EpilLatch, t3LatchEnv]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_self]

theorem t3EpilLatchEnv_e1 (env : Env) (e i n u : BitVec 64) :
    lookupName (t3EpilLatch env e i n u) "%e.1.i.i.epil" = some (.int 64 e) := by
  simp only [t3EpilLatch, t3LatchEnv]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide), lookupName_cons_self]

theorem t3EpilLatchEnv_next (env : Env) (e i n u : BitVec 64) :
    lookupName (t3EpilLatch env e i n u) "%epil.iter.next" = some (.int 64 n) := by
  simp only [t3EpilLatch, t3LatchEnv]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]

/-- What the residual loop leaves for `for.end100.i.i`. -/
def t3EpilExitWord (p digA N xtraiter : Nat) : State → Prop := fun st =>
  lookupName st.env "%xtraiter" = some (.int 64 (BitVec.ofNat 64 xtraiter)) ∧
  lookupName st.env "%p" = some (.ptr p) ∧
  lookupName st.env "%dig.i.i" = some (.ptr digA) ∧
  (∀ k, k < N → ∃ d, readBytes st.mem (p + k) 1 = some [d] ∧
    48 ≤ d.toNat ∧ d.toNat ≤ 57) ∧
  (∃ i e : BitVec 64,
    lookupName st.env "%inc99.i.i.epil" = some (.int 64 i) ∧
    lookupName st.env "%e.1.i.i.epil" = some (.int 64 e) ∧
    e.toNat < 10 ^ 7 ∧ i.toNat ≤ N)

/-- **The exit state and its word.** -/
theorem t3Epil_exit_word {p digA N xtraiter : Nat} {env : Env} {base : State}
    {i e n : BitVec 64}
    (hp : lookupName env "%p" = some (.ptr p))
    (hdig : lookupName env "%dig.i.i" = some (.ptr digA))
    (hxt : lookupName env "%xtraiter" = some (.int 64 (BitVec.ofNat 64 xtraiter)))
    (hstage : ∀ k, k < N → ∃ d, readBytes base.mem (p + k) 1 = some [d] ∧
      48 ≤ d.toNat ∧ d.toNat ≤ 57)
    (he7 : e.toNat < 10 ^ 7) (hiN : i.toNat ≤ N) :
    t3EpilExit (t3EpilExitState env base xtraiter e i n) ∧
      t3EpilExitWord p digA N xtraiter (t3EpilExitState env base xtraiter e i n) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, i, e, ?_, ?_, he7, hiN⟩
  · simp only [t3EpilExitState, stateAt]; rw [t3EpilLatchEnv_lookup_other]; exact hxt
  · simp only [t3EpilExitState, stateAt]; rw [t3EpilLatchEnv_lookup_other]; exact hp
  · simp only [t3EpilExitState, stateAt]; rw [t3EpilLatchEnv_lookup_other]; exact hdig
  · intro k hk
    simp only [t3EpilExitState, stateAt]
    exact hstage k hk
  · simp only [t3EpilExitState, stateAt]
    exact t3EpilLatchEnv_inc99 env e i n (BitVec.ofNat 64 xtraiter)
  · simp only [t3EpilExitState, stateAt]
    exact t3EpilLatchEnv_e1 env e i n (BitVec.ofNat 64 xtraiter)



/-- **The residual loop's exit visit.**  At the head with one visit left, the
head's test, the store when the accumulator is below the cap, and the latch reach
`for.end100.i.i` within three control steps, leaving the exit word. -/
theorem t3Epil_step_exit_test {calls : Calls} {p digA N xtraiter : Nat}
    (r : Nat) (s : State) (c : Nat)
    (h : T3EpilInv p digA N xtraiter r s c)
    (hb : t3EpilAtBound xtraiter s c = true) :
    ∃ (e : State) (j : Nat), j ≤ 3 ∧ t3EpilExit e ∧
      t3EpilExitWord p digA N xtraiter e ∧
      ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e := by
  obtain ⟨hpc, hp, hdig, hxt, hstage, hN, hx3, ⟨i, e, hi63, he7, hile, himp, hedge⟩, hr1, hcr⟩ := h
  have hbnd : xtraiter ≤ c + 1 := t3EpilAtBound_true hb
  have hxeq : c + 1 = xtraiter := by omega
  have hi1 : (i + 0x1#64).toNat = i.toNat + 1 := t3_add_one_toNat (by omega)
  have hi1N : (i + 0x1#64).toNat ≤ N := by omega
  have hpos : (i.signExtend 64).toNat < 2 ^ 63 := by
    rw [t3_signExtend_self_toNat]; exact hi63
  rcases hedge with ⟨hpre, hi, he, hc0⟩ | ⟨hpre, hi, he, hn⟩
  · -- the entry edge: the peeled nest's first visit
    subst hc0
    have hx1 : xtraiter = 1 := by omega
    have hu1 : evalICmp .eq ((0 : BitVec 64) + 0x1#64) (BitVec.ofNat 64 xtraiter)
        = (1 : BitVec 1) := by
      rw [hx1]; decide
    by_cases hbit : evalICmp .slt e t3Cap = (1 : BitVec 1)
    · -- the accumulator is below the cap: the store runs
      obtain ⟨d, hread, hd48, hd57⟩ := hstage i.toNat (himp hbit)
      have he63 : e.toNat < 2 ^ 63 := by omega
      have he6 : e.toNat < 10 ^ 6 := by
        have h' := (slt_one_iff he63 t3Cap_lt_two).mp hbit
        simpa only [t3Cap_toNat] using h'
      obtain ⟨he7', -⟩ := t3_store_next_lt he6 hd48 hd57
      have hread' : readBytes s.mem (p + (i.signExtend 64).toNat) 1 = some [d] := by
        rw [t3_signExtend_self_toNat]; exact hread
      have hstep1 : step calls numFastBody s = .jump (t3EpilStoreState s.env i e 0 s) := by
        simpa only [t3EpilStoreState, t3_stateAt_env_self] using
          t3_epil_head_step_entry_store (calls := calls) (env := s.env) (s := s)
            (i := i) (e := e) hpc hpre hi he hbit
      have hstep2 : step calls numFastBody (t3EpilStoreState s.env i e 0 s) =
          .jump (t3EpilStoredState (t3EpilHeadEnv s.env i e 0) e d
            (p + (i.signExtend 64).toNat) s) := by
        simpa only [t3EpilStoreState, t3EpilStoredState, t3EpilStore] using
          t3_if_then90_step_epil (calls := calls) (env := t3EpilHeadEnv s.env i e 0)
            (s := { s with pc := "if.then90.i.i.epil", pre := some "for.body87.i.i.epil" })
            (e := e) (b := p) (idx := i) (d := d)
            rfl (t3EpilHeadEnv_e s.env i e 0) hp (t3EpilHeadEnv_i s.env i e 0) hpos hread'
      have hstep3 : step calls numFastBody
          (t3EpilStoredState (t3EpilHeadEnv s.env i e 0) e d
            (p + (i.signExtend 64).toNat) s) =
          .jump (t3EpilExitState (t3EpilStore (t3EpilHeadEnv s.env i e 0) e d
            (p + (i.signExtend 64).toNat)) s xtraiter (t3EpilStoreAdd96 e d)
            (i + 0x1#64) (0 + 0x1#64)) := by
        simpa only [t3EpilStoredState, t3EpilExitState, t3EpilLatch, t3EpilStore] using
          t3_latch_epil_step_exit (calls := calls)
            (env := t3EpilStore (t3EpilHeadEnv s.env i e 0) e d
              (p + (i.signExtend 64).toNat))
            (s := { s with pc := "for.inc98.i.i.epil", pre := some "if.then90.i.i.epil" })
            (e := t3EpilStoreAdd96 e d) (i := i) (n := 0)
            (u := BitVec.ofNat 64 xtraiter)
            rfl rfl
            (t3EpilStore_add96 (t3EpilHeadEnv s.env i e 0) e d
              (p + (i.signExtend 64).toNat))
            (t3EpilStore_i s.env e d (p + (i.signExtend 64).toNat) i e 0)
            (t3EpilStore_iter s.env e d (p + (i.signExtend 64).toNat) i e 0)
            (by rw [t3EpilStore_xt]; exact hxt) hu1
      have hEW := t3Epil_exit_word
        (env := t3EpilStore (t3EpilHeadEnv s.env i e 0) e d
          (p + (i.signExtend 64).toNat))
        (base := s) (i := i + 0x1#64) (e := t3EpilStoreAdd96 e d) (n := 0 + 0x1#64)
        (by rw [t3EpilStoreEnv_lookup_other, t3EpilHeadEnv_lookup_other]; exact hp)
        (by rw [t3EpilStoreEnv_lookup_other, t3EpilHeadEnv_lookup_other]; exact hdig)
        (by rw [t3EpilStore_xt]; exact hxt) hstage he7' hi1N
      refine ⟨t3EpilExitState (t3EpilStore (t3EpilHeadEnv s.env i e 0) e d
        (p + (i.signExtend 64).toNat)) s xtraiter (t3EpilStoreAdd96 e d)
        (i + 0x1#64) (0 + 0x1#64), 3, by decide, hEW.1, hEW.2, ?_⟩
      intro k
      rw [show 3 + k = ((k + 1) + 1) + 1 from by omega]
      simp only [runFuel, hstep1, hstep2, hstep3]
    · -- the cap refuses the store: the head goes straight to the latch
      have hbit0 : evalICmp .slt e t3Cap = (0 : BitVec 1) := by
        rcases bitVec1_eq_zero_or_one (evalICmp .slt e t3Cap) with h' | h'
        · exact h'
        · exact absurd h' hbit
      have hstep1 : step calls numFastBody s = .jump (t3EpilSkipState s.env i e 0 s) := by
        simpa only [t3EpilSkipState, t3_stateAt_env_self] using
          t3_epil_head_step_entry_skip (calls := calls) (env := s.env) (s := s)
            (i := i) (e := e) hpc hpre hi he hbit0
      have hstep2 : step calls numFastBody (t3EpilSkipState s.env i e 0 s) =
          .jump (t3EpilExitState (t3EpilHeadEnv s.env i e 0) s xtraiter e
            (i + 0x1#64) (0 + 0x1#64)) := by
        simpa only [t3EpilSkipState, t3EpilExitState, t3EpilLatch] using
          t3_latch_epil_step_exit_skip (calls := calls)
            (env := t3EpilHeadEnv s.env i e 0)
            (s := { s with pc := "for.inc98.i.i.epil", pre := some "for.body87.i.i.epil" })
            (e := e) (i := i) (n := 0) (u := BitVec.ofNat 64 xtraiter)
            rfl rfl (t3EpilHeadEnv_e s.env i e 0) (t3EpilHeadEnv_i s.env i e 0)
            (t3EpilHeadEnv_iter s.env i e 0)
            (by rw [t3EpilHeadEnv_lookup_other]; exact hxt) hu1
      have hEW := t3Epil_exit_word (env := t3EpilHeadEnv s.env i e 0) (base := s)
        (i := i + 0x1#64) (e := e) (n := 0 + 0x1#64)
        (by rw [t3EpilHeadEnv_lookup_other]; exact hp)
        (by rw [t3EpilHeadEnv_lookup_other]; exact hdig)
        (by rw [t3EpilHeadEnv_lookup_other]; exact hxt) hstage he7 hi1N
      refine ⟨t3EpilExitState (t3EpilHeadEnv s.env i e 0) s xtraiter e
        (i + 0x1#64) (0 + 0x1#64), 2, by decide, hEW.1, hEW.2, ?_⟩
      intro k
      rw [show 2 + k = (k + 1) + 1 from by omega]
      simp only [runFuel, hstep1, hstep2]
  · -- the latch's edge: the counter is one short of the residue
    have hc_lt : c + 1 < 2 ^ 64 := by omega
    have hu : evalICmp .eq (BitVec.ofNat 64 c + 0x1#64) (BitVec.ofNat 64 xtraiter)
        = (1 : BitVec 1) := by
      rw [t3Epil_ofNat_succ hc_lt, hxeq]; simp [evalICmp]
    by_cases hbit : evalICmp .slt e t3Cap = (1 : BitVec 1)
    · obtain ⟨d, hread, hd48, hd57⟩ := hstage i.toNat (himp hbit)
      have he63 : e.toNat < 2 ^ 63 := by omega
      have he6 : e.toNat < 10 ^ 6 := by
        have h' := (slt_one_iff he63 t3Cap_lt_two).mp hbit
        simpa only [t3Cap_toNat] using h'
      obtain ⟨he7', -⟩ := t3_store_next_lt he6 hd48 hd57
      have hread' : readBytes s.mem (p + (i.signExtend 64).toNat) 1 = some [d] := by
        rw [t3_signExtend_self_toNat]; exact hread
      have hstep1 : step calls numFastBody s =
          .jump (t3EpilStoreState s.env i e (BitVec.ofNat 64 c) s) := by
        simpa only [t3EpilStoreState, t3_stateAt_env_self] using
          t3_epil_head_step_back_store (calls := calls) (env := s.env) (s := s)
            (i := i) (e := e) (n := BitVec.ofNat 64 c) hpc hpre hi he hn hbit
      have hstep2 : step calls numFastBody
          (t3EpilStoreState s.env i e (BitVec.ofNat 64 c) s) =
          .jump (t3EpilStoredState (t3EpilHeadEnv s.env i e (BitVec.ofNat 64 c)) e d
            (p + (i.signExtend 64).toNat) s) := by
        simpa only [t3EpilStoreState, t3EpilStoredState, t3EpilStore] using
          t3_if_then90_step_epil (calls := calls)
            (env := t3EpilHeadEnv s.env i e (BitVec.ofNat 64 c))
            (s := { s with pc := "if.then90.i.i.epil", pre := some "for.body87.i.i.epil" })
            (e := e) (b := p) (idx := i) (d := d)
            rfl (t3EpilHeadEnv_e s.env i e (BitVec.ofNat 64 c)) hp
            (t3EpilHeadEnv_i s.env i e (BitVec.ofNat 64 c)) hpos hread'
      have hstep3 : step calls numFastBody
          (t3EpilStoredState (t3EpilHeadEnv s.env i e (BitVec.ofNat 64 c)) e d
            (p + (i.signExtend 64).toNat) s) =
          .jump (t3EpilExitState (t3EpilStore (t3EpilHeadEnv s.env i e
            (BitVec.ofNat 64 c)) e d (p + (i.signExtend 64).toNat)) s xtraiter
            (t3EpilStoreAdd96 e d) (i + 0x1#64)
            (BitVec.ofNat 64 c + 0x1#64)) := by
        simpa only [t3EpilStoredState, t3EpilExitState, t3EpilLatch, t3EpilStore] using
          t3_latch_epil_step_exit (calls := calls)
            (env := t3EpilStore (t3EpilHeadEnv s.env i e (BitVec.ofNat 64 c)) e d
              (p + (i.signExtend 64).toNat))
            (s := { s with pc := "for.inc98.i.i.epil", pre := some "if.then90.i.i.epil" })
            (e := t3EpilStoreAdd96 e d) (i := i) (n := BitVec.ofNat 64 c)
            (u := BitVec.ofNat 64 xtraiter)
            rfl rfl
            (t3EpilStore_add96 (t3EpilHeadEnv s.env i e (BitVec.ofNat 64 c)) e d
              (p + (i.signExtend 64).toNat))
            (t3EpilStore_i s.env e d (p + (i.signExtend 64).toNat) i e
              (BitVec.ofNat 64 c))
            (t3EpilStore_iter s.env e d (p + (i.signExtend 64).toNat) i e
              (BitVec.ofNat 64 c))
            (by rw [t3EpilStore_xt]; exact hxt) hu
      have hEW := t3Epil_exit_word
        (env := t3EpilStore (t3EpilHeadEnv s.env i e (BitVec.ofNat 64 c)) e d
          (p + (i.signExtend 64).toNat))
        (base := s) (i := i + 0x1#64) (e := t3EpilStoreAdd96 e d)
        (n := BitVec.ofNat 64 c + 0x1#64)
        (by rw [t3EpilStoreEnv_lookup_other, t3EpilHeadEnv_lookup_other]; exact hp)
        (by rw [t3EpilStoreEnv_lookup_other, t3EpilHeadEnv_lookup_other]; exact hdig)
        (by rw [t3EpilStore_xt]; exact hxt) hstage he7' hi1N
      refine ⟨t3EpilExitState (t3EpilStore (t3EpilHeadEnv s.env i e
        (BitVec.ofNat 64 c)) e d (p + (i.signExtend 64).toNat)) s xtraiter
        (t3EpilStoreAdd96 e d) (i + 0x1#64) (BitVec.ofNat 64 c + 0x1#64),
        3, by decide, hEW.1, hEW.2, ?_⟩
      intro k
      rw [show 3 + k = ((k + 1) + 1) + 1 from by omega]
      simp only [runFuel, hstep1, hstep2, hstep3]
    · have hbit0 : evalICmp .slt e t3Cap = (0 : BitVec 1) := by
        rcases bitVec1_eq_zero_or_one (evalICmp .slt e t3Cap) with h' | h'
        · exact h'
        · exact absurd h' hbit
      have hstep1 : step calls numFastBody s =
          .jump (t3EpilSkipState s.env i e (BitVec.ofNat 64 c) s) := by
        simpa only [t3EpilSkipState, t3_stateAt_env_self] using
          t3_epil_head_step_back_skip (calls := calls) (env := s.env) (s := s)
            (i := i) (e := e) (n := BitVec.ofNat 64 c) hpc hpre hi he hn hbit0
      have hstep2 : step calls numFastBody
          (t3EpilSkipState s.env i e (BitVec.ofNat 64 c) s) =
          .jump (t3EpilExitState (t3EpilHeadEnv s.env i e (BitVec.ofNat 64 c)) s
            xtraiter e (i + 0x1#64) (BitVec.ofNat 64 c + 0x1#64)) := by
        simpa only [t3EpilSkipState, t3EpilExitState, t3EpilLatch] using
          t3_latch_epil_step_exit_skip (calls := calls)
            (env := t3EpilHeadEnv s.env i e (BitVec.ofNat 64 c))
            (s := { s with pc := "for.inc98.i.i.epil", pre := some "for.body87.i.i.epil" })
            (e := e) (i := i) (n := BitVec.ofNat 64 c)
            (u := BitVec.ofNat 64 xtraiter)
            rfl rfl (t3EpilHeadEnv_e s.env i e (BitVec.ofNat 64 c))
            (t3EpilHeadEnv_i s.env i e (BitVec.ofNat 64 c))
            (t3EpilHeadEnv_iter s.env i e (BitVec.ofNat 64 c))
            (by rw [t3EpilHeadEnv_lookup_other]; exact hxt) hu
      have hEW := t3Epil_exit_word (env := t3EpilHeadEnv s.env i e (BitVec.ofNat 64 c))
        (base := s) (i := i + 0x1#64) (e := e) (n := BitVec.ofNat 64 c + 0x1#64)
        (by rw [t3EpilHeadEnv_lookup_other]; exact hp)
        (by rw [t3EpilHeadEnv_lookup_other]; exact hdig)
        (by rw [t3EpilHeadEnv_lookup_other]; exact hxt) hstage he7 hi1N
      refine ⟨t3EpilExitState (t3EpilHeadEnv s.env i e (BitVec.ofNat 64 c)) s xtraiter
        e (i + 0x1#64) (BitVec.ofNat 64 c + 0x1#64), 2, by decide, hEW.1, hEW.2, ?_⟩
      intro k
      rw [show 2 + k = (k + 1) + 1 from by omega]
      simp only [runFuel, hstep1, hstep2]


theorem t3Epil_zero_succ : ((0 : BitVec 64) + 0x1#64) = BitVec.ofNat 64 (0 + 1) := by decide

/-- **The residual loop's loop visit.**  With more than one visit left, the head's
test, the store when the accumulator is below the cap, and the latch re-enter the
residual head with the index advanced and the counter incremented. -/
theorem t3Epil_step_loop_test {calls : Calls} {p digA N xtraiter : Nat}
    (r : Nat) (s : State) (c : Nat)
    (h : T3EpilInv p digA N xtraiter (r + 1) s c)
    (hb : t3EpilAtBound xtraiter s c = false) :
    ∃ (e : State) (c' : Nat) (j : Nat), j ≤ 3 ∧
      e.pc = "for.body87.i.i.epil" ∧ c < c' ∧
      T3EpilInv p digA N xtraiter r e c' ∧
      ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e := by
  obtain ⟨hpc, hp, hdig, hxt, hstage, hN, hx3, ⟨i, e, hi63, he7, hile, himp, hedge⟩, hr1, hcr⟩ := h
  have hnot : ¬ xtraiter ≤ c + 1 := t3EpilAtBound_false hb
  have hrem : xtraiter - (c + 1) = r := by omega
  have hr1' : 1 ≤ r := by omega
  have hc_lt : c + 1 < 2 ^ 64 := by omega
  have hi1 : (i + 0x1#64).toNat = i.toNat + 1 := t3_add_one_toNat (by omega)
  have hi1lt : (i + 0x1#64).toNat < 2 ^ 63 := by omega
  have hpos : (i.signExtend 64).toNat < 2 ^ 63 := by
    rw [t3_signExtend_self_toNat]; exact hi63
  rcases hedge with ⟨hpre, hi, he, hc0⟩ | ⟨hpre, hi, he, hn⟩
  · -- the entry edge
    subst hc0
    have hu0 : evalICmp .eq ((0 : BitVec 64) + 0x1#64) (BitVec.ofNat 64 xtraiter)
        = (0 : BitVec 1) := by
      have h1eq : ((0 : BitVec 64) + 0x1#64) = (0x1#64 : BitVec 64) := by decide
      have hne : ¬ ((0x1#64 : BitVec 64) = BitVec.ofNat 64 xtraiter) := by
        intro hh
        have h2 := congrArg BitVec.toNat hh
        rw [show (0x1#64 : BitVec 64).toNat = 1 from by decide, BitVec.toNat_ofNat] at h2
        rw [Nat.mod_eq_of_lt (by omega : xtraiter < 2 ^ 64)] at h2
        omega
      have hdec : decide ((0x1#64 : BitVec 64) = BitVec.ofNat 64 xtraiter) = false :=
        decide_eq_false_iff_not.mpr hne
      simp only [evalICmp, h1eq, hdec]
      decide
    have hn0 : ((0 : BitVec 64) + 0x1#64) = BitVec.ofNat 64 (0 + 1) := t3Epil_zero_succ
    by_cases hbit : evalICmp .slt e t3Cap = (1 : BitVec 1)
    · obtain ⟨d, hread, hd48, hd57⟩ := hstage i.toNat (himp hbit)
      have he63 : e.toNat < 2 ^ 63 := by omega
      have he6 : e.toNat < 10 ^ 6 := by
        have h' := (slt_one_iff he63 t3Cap_lt_two).mp hbit
        simpa only [t3Cap_toNat] using h'
      obtain ⟨he7', -⟩ := t3_store_next_lt he6 hd48 hd57
      have hread' : readBytes s.mem (p + (i.signExtend 64).toNat) 1 = some [d] := by
        rw [t3_signExtend_self_toNat]; exact hread
      have hstep1 : step calls numFastBody s = .jump (t3EpilStoreState s.env i e 0 s) := by
        simpa only [t3EpilStoreState, t3_stateAt_env_self] using
          t3_epil_head_step_entry_store (calls := calls) (env := s.env) (s := s)
            (i := i) (e := e) hpc hpre hi he hbit
      have hstep2 : step calls numFastBody (t3EpilStoreState s.env i e 0 s) =
          .jump (t3EpilStoredState (t3EpilHeadEnv s.env i e 0) e d
            (p + (i.signExtend 64).toNat) s) := by
        simpa only [t3EpilStoreState, t3EpilStoredState, t3EpilStore] using
          t3_if_then90_step_epil (calls := calls) (env := t3EpilHeadEnv s.env i e 0)
            (s := { s with pc := "if.then90.i.i.epil", pre := some "for.body87.i.i.epil" })
            (e := e) (b := p) (idx := i) (d := d)
            rfl (t3EpilHeadEnv_e s.env i e 0) hp (t3EpilHeadEnv_i s.env i e 0) hpos hread'
      have hstep3 : step calls numFastBody
          (t3EpilStoredState (t3EpilHeadEnv s.env i e 0) e d
            (p + (i.signExtend 64).toNat) s) =
          .jump (t3EpilBackState (t3EpilStore (t3EpilHeadEnv s.env i e 0) e d
            (p + (i.signExtend 64).toNat)) s xtraiter (t3EpilStoreAdd96 e d)
            (i + 0x1#64) (0 + 0x1#64)) := by
        simpa only [t3EpilStoredState, t3EpilBackState, t3EpilLatch, t3EpilStore] using
          t3_latch_epil_step_back_store (calls := calls)
            (env := t3EpilStore (t3EpilHeadEnv s.env i e 0) e d
              (p + (i.signExtend 64).toNat))
            (s := { s with pc := "for.inc98.i.i.epil", pre := some "if.then90.i.i.epil" })
            (e := t3EpilStoreAdd96 e d) (i := i) (n := 0)
            (u := BitVec.ofNat 64 xtraiter)
            rfl rfl
            (t3EpilStore_add96 (t3EpilHeadEnv s.env i e 0) e d
              (p + (i.signExtend 64).toNat))
            (t3EpilStore_i s.env e d (p + (i.signExtend 64).toNat) i e 0)
            (t3EpilStore_iter s.env e d (p + (i.signExtend 64).toNat) i e 0)
            (by rw [t3EpilStore_xt]; exact hxt) hu0
      refine ⟨t3EpilBackState (t3EpilStore (t3EpilHeadEnv s.env i e 0) e d
        (p + (i.signExtend 64).toNat)) s xtraiter (t3EpilStoreAdd96 e d)
        (i + 0x1#64) (0 + 0x1#64), 0 + 1, 3, by decide, rfl, by omega, ?_, ?_⟩
      · simp only [t3EpilBackState, stateAt]
        refine ⟨rfl, ?_, ?_, ?_, ?_, hN, hx3, ⟨i + 0x1#64, t3EpilStoreAdd96 e d,
          hi1lt, he7', ?_, ?_, ?_⟩, hr1', by omega⟩
        · rw [t3EpilLatchEnv_lookup_other, t3EpilStoreEnv_lookup_other,
            t3EpilHeadEnv_lookup_other]; exact hp
        · rw [t3EpilLatchEnv_lookup_other, t3EpilStoreEnv_lookup_other,
            t3EpilHeadEnv_lookup_other]; exact hdig
        · rw [t3EpilLatchEnv_lookup_other, t3EpilStore_xt]; exact hxt
        · intro k hk; exact hstage k hk
        · rw [hi1, hrem]; omega
        · omega
        · refine Or.inr ⟨rfl, ?_, ?_, ?_⟩
          · exact t3EpilLatchEnv_inc99 _ _ _ _ _
          · exact t3EpilLatchEnv_e1 _ _ _ _ _
          · rw [hn0]; exact t3EpilLatchEnv_next _ _ _ _ _
      · intro k
        rw [show 3 + k = ((k + 1) + 1) + 1 from by omega]
        simp only [runFuel, hstep1, hstep2, hstep3]
    · have hbit0 : evalICmp .slt e t3Cap = (0 : BitVec 1) := by
        rcases bitVec1_eq_zero_or_one (evalICmp .slt e t3Cap) with h' | h'
        · exact h'
        · exact absurd h' hbit
      have hstep1 : step calls numFastBody s = .jump (t3EpilSkipState s.env i e 0 s) := by
        simpa only [t3EpilSkipState, t3_stateAt_env_self] using
          t3_epil_head_step_entry_skip (calls := calls) (env := s.env) (s := s)
            (i := i) (e := e) hpc hpre hi he hbit0
      have hstep2 : step calls numFastBody (t3EpilSkipState s.env i e 0 s) =
          .jump (t3EpilBackState (t3EpilHeadEnv s.env i e 0) s xtraiter e
            (i + 0x1#64) (0 + 0x1#64)) := by
        simpa only [t3EpilSkipState, t3EpilBackState, t3EpilLatch] using
          t3_latch_epil_step_back (calls := calls) (env := t3EpilHeadEnv s.env i e 0)
            (s := { s with pc := "for.inc98.i.i.epil", pre := some "for.body87.i.i.epil" })
            (e := e) (i := i) (n := 0) (u := BitVec.ofNat 64 xtraiter)
            rfl rfl (t3EpilHeadEnv_e s.env i e 0) (t3EpilHeadEnv_i s.env i e 0)
            (t3EpilHeadEnv_iter s.env i e 0)
            (by rw [t3EpilHeadEnv_lookup_other]; exact hxt) hu0
      refine ⟨t3EpilBackState (t3EpilHeadEnv s.env i e 0) s xtraiter e
        (i + 0x1#64) (0 + 0x1#64), 0 + 1, 2, by decide, rfl, by omega, ?_, ?_⟩
      · simp only [t3EpilBackState, stateAt]
        refine ⟨rfl, ?_, ?_, ?_, ?_, hN, hx3, ⟨i + 0x1#64, e, hi1lt, he7, ?_, ?_, ?_⟩,
          hr1', by omega⟩
        · rw [t3EpilLatchEnv_lookup_other, t3EpilHeadEnv_lookup_other]; exact hp
        · rw [t3EpilLatchEnv_lookup_other, t3EpilHeadEnv_lookup_other]; exact hdig
        · rw [t3EpilLatchEnv_lookup_other, t3EpilHeadEnv_lookup_other]; exact hxt
        · intro k hk; exact hstage k hk
        · rw [hi1, hrem]; omega
        · omega
        · refine Or.inr ⟨rfl, ?_, ?_, ?_⟩
          · exact t3EpilLatchEnv_inc99 _ _ _ _ _
          · exact t3EpilLatchEnv_e1 _ _ _ _ _
          · rw [hn0]; exact t3EpilLatchEnv_next _ _ _ _ _
      · intro k
        rw [show 2 + k = (k + 1) + 1 from by omega]
        simp only [runFuel, hstep1, hstep2]
  · -- the latch's edge
    have hu : evalICmp .eq (BitVec.ofNat 64 c + 0x1#64) (BitVec.ofNat 64 xtraiter)
        = (0 : BitVec 1) := by
      rw [t3Epil_ofNat_succ hc_lt]
      have hne : ¬ (BitVec.ofNat 64 (c + 1) = BitVec.ofNat 64 xtraiter) := by
        intro hh
        have h2 := congrArg BitVec.toNat hh
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h2
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2
        omega
      have hdec : decide (BitVec.ofNat 64 (c + 1) = BitVec.ofNat 64 xtraiter) = false :=
        decide_eq_false_iff_not.mpr hne
      simp only [evalICmp, hdec]
      decide
    by_cases hbit : evalICmp .slt e t3Cap = (1 : BitVec 1)
    · obtain ⟨d, hread, hd48, hd57⟩ := hstage i.toNat (himp hbit)
      have he63 : e.toNat < 2 ^ 63 := by omega
      have he6 : e.toNat < 10 ^ 6 := by
        have h' := (slt_one_iff he63 t3Cap_lt_two).mp hbit
        simpa only [t3Cap_toNat] using h'
      obtain ⟨he7', -⟩ := t3_store_next_lt he6 hd48 hd57
      have hread' : readBytes s.mem (p + (i.signExtend 64).toNat) 1 = some [d] := by
        rw [t3_signExtend_self_toNat]; exact hread
      have hstep1 : step calls numFastBody s =
          .jump (t3EpilStoreState s.env i e (BitVec.ofNat 64 c) s) := by
        simpa only [t3EpilStoreState, t3_stateAt_env_self] using
          t3_epil_head_step_back_store (calls := calls) (env := s.env) (s := s)
            (i := i) (e := e) (n := BitVec.ofNat 64 c) hpc hpre hi he hn hbit
      have hstep2 : step calls numFastBody
          (t3EpilStoreState s.env i e (BitVec.ofNat 64 c) s) =
          .jump (t3EpilStoredState (t3EpilHeadEnv s.env i e (BitVec.ofNat 64 c)) e d
            (p + (i.signExtend 64).toNat) s) := by
        simpa only [t3EpilStoreState, t3EpilStoredState, t3EpilStore] using
          t3_if_then90_step_epil (calls := calls)
            (env := t3EpilHeadEnv s.env i e (BitVec.ofNat 64 c))
            (s := { s with pc := "if.then90.i.i.epil", pre := some "for.body87.i.i.epil" })
            (e := e) (b := p) (idx := i) (d := d)
            rfl (t3EpilHeadEnv_e s.env i e (BitVec.ofNat 64 c)) hp
            (t3EpilHeadEnv_i s.env i e (BitVec.ofNat 64 c)) hpos hread'
      have hstep3 : step calls numFastBody
          (t3EpilStoredState (t3EpilHeadEnv s.env i e (BitVec.ofNat 64 c)) e d
            (p + (i.signExtend 64).toNat) s) =
          .jump (t3EpilBackState (t3EpilStore (t3EpilHeadEnv s.env i e
            (BitVec.ofNat 64 c)) e d (p + (i.signExtend 64).toNat)) s xtraiter
            (t3EpilStoreAdd96 e d) (i + 0x1#64) (BitVec.ofNat 64 c + 0x1#64)) := by
        simpa only [t3EpilStoredState, t3EpilBackState, t3EpilLatch, t3EpilStore] using
          t3_latch_epil_step_back_store (calls := calls)
            (env := t3EpilStore (t3EpilHeadEnv s.env i e (BitVec.ofNat 64 c)) e d
              (p + (i.signExtend 64).toNat))
            (s := { s with pc := "for.inc98.i.i.epil", pre := some "if.then90.i.i.epil" })
            (e := t3EpilStoreAdd96 e d) (i := i) (n := BitVec.ofNat 64 c)
            (u := BitVec.ofNat 64 xtraiter)
            rfl rfl
            (t3EpilStore_add96 (t3EpilHeadEnv s.env i e (BitVec.ofNat 64 c)) e d
              (p + (i.signExtend 64).toNat))
            (t3EpilStore_i s.env e d (p + (i.signExtend 64).toNat) i e
              (BitVec.ofNat 64 c))
            (t3EpilStore_iter s.env e d (p + (i.signExtend 64).toNat) i e
              (BitVec.ofNat 64 c))
            (by rw [t3EpilStore_xt]; exact hxt) hu
      have hnext : (BitVec.ofNat 64 c + 0x1#64) = BitVec.ofNat 64 (c + 1) :=
        t3Epil_ofNat_succ hc_lt
      refine ⟨t3EpilBackState (t3EpilStore (t3EpilHeadEnv s.env i e
        (BitVec.ofNat 64 c)) e d (p + (i.signExtend 64).toNat)) s xtraiter
        (t3EpilStoreAdd96 e d) (i + 0x1#64) (BitVec.ofNat 64 c + 0x1#64),
        c + 1, 3, by decide, rfl, by omega, ?_, ?_⟩
      · simp only [t3EpilBackState, stateAt]
        refine ⟨rfl, ?_, ?_, ?_, ?_, hN, hx3, ⟨i + 0x1#64, t3EpilStoreAdd96 e d,
          hi1lt, he7', ?_, ?_, ?_⟩, hr1', by omega⟩
        · rw [t3EpilLatchEnv_lookup_other, t3EpilStoreEnv_lookup_other,
            t3EpilHeadEnv_lookup_other]; exact hp
        · rw [t3EpilLatchEnv_lookup_other, t3EpilStoreEnv_lookup_other,
            t3EpilHeadEnv_lookup_other]; exact hdig
        · rw [t3EpilLatchEnv_lookup_other, t3EpilStore_xt]; exact hxt
        · intro k hk; exact hstage k hk
        · rw [hi1, hrem]; omega
        · omega
        · refine Or.inr ⟨rfl, ?_, ?_, ?_⟩
          · exact t3EpilLatchEnv_inc99 _ _ _ _ _
          · exact t3EpilLatchEnv_e1 _ _ _ _ _
          · rw [hnext]; exact t3EpilLatchEnv_next _ _ _ _ _
      · intro k
        rw [show 3 + k = ((k + 1) + 1) + 1 from by omega]
        simp only [runFuel, hstep1, hstep2, hstep3]
    · have hbit0 : evalICmp .slt e t3Cap = (0 : BitVec 1) := by
        rcases bitVec1_eq_zero_or_one (evalICmp .slt e t3Cap) with h' | h'
        · exact h'
        · exact absurd h' hbit
      have hstep1 : step calls numFastBody s =
          .jump (t3EpilSkipState s.env i e (BitVec.ofNat 64 c) s) := by
        simpa only [t3EpilSkipState, t3_stateAt_env_self] using
          t3_epil_head_step_back_skip (calls := calls) (env := s.env) (s := s)
            (i := i) (e := e) (n := BitVec.ofNat 64 c) hpc hpre hi he hn hbit0
      have hstep2 : step calls numFastBody
          (t3EpilSkipState s.env i e (BitVec.ofNat 64 c) s) =
          .jump (t3EpilBackState (t3EpilHeadEnv s.env i e (BitVec.ofNat 64 c)) s
            xtraiter e (i + 0x1#64) (BitVec.ofNat 64 c + 0x1#64)) := by
        simpa only [t3EpilSkipState, t3EpilBackState, t3EpilLatch] using
          t3_latch_epil_step_back (calls := calls)
            (env := t3EpilHeadEnv s.env i e (BitVec.ofNat 64 c))
            (s := { s with pc := "for.inc98.i.i.epil", pre := some "for.body87.i.i.epil" })
            (e := e) (i := i) (n := BitVec.ofNat 64 c)
            (u := BitVec.ofNat 64 xtraiter)
            rfl rfl (t3EpilHeadEnv_e s.env i e (BitVec.ofNat 64 c))
            (t3EpilHeadEnv_i s.env i e (BitVec.ofNat 64 c))
            (t3EpilHeadEnv_iter s.env i e (BitVec.ofNat 64 c))
            (by rw [t3EpilHeadEnv_lookup_other]; exact hxt) hu
      have hnext : (BitVec.ofNat 64 c + 0x1#64) = BitVec.ofNat 64 (c + 1) :=
        t3Epil_ofNat_succ hc_lt
      refine ⟨t3EpilBackState (t3EpilHeadEnv s.env i e (BitVec.ofNat 64 c)) s xtraiter
        e (i + 0x1#64) (BitVec.ofNat 64 c + 0x1#64), c + 1, 2, by decide, rfl,
        by omega, ?_, ?_⟩
      · simp only [t3EpilBackState, stateAt]
        refine ⟨rfl, ?_, ?_, ?_, ?_, hN, hx3, ⟨i + 0x1#64, e, hi1lt, he7, ?_, ?_, ?_⟩,
          hr1', by omega⟩
        · rw [t3EpilLatchEnv_lookup_other, t3EpilHeadEnv_lookup_other]; exact hp
        · rw [t3EpilLatchEnv_lookup_other, t3EpilHeadEnv_lookup_other]; exact hdig
        · rw [t3EpilLatchEnv_lookup_other, t3EpilHeadEnv_lookup_other]; exact hxt
        · intro k hk; exact hstage k hk
        · rw [hi1, hrem]; omega
        · omega
        · refine Or.inr ⟨rfl, ?_, ?_, ?_⟩
          · exact t3EpilLatchEnv_inc99 _ _ _ _ _
          · exact t3EpilLatchEnv_e1 _ _ _ _ _
          · rw [hnext]; exact t3EpilLatchEnv_next _ _ _ _ _
      · intro k
        rw [show 2 + k = (k + 1) + 1 from by omega]
        simp only [runFuel, hstep1, hstep2]

/-- **The residual copy loop's instance.**  The two visits discharge
`t3EpilLoopOf`'s parameters, so the loop is an induction at the emitted blocks
and needs nothing else. -/
def t3EpilLoop (calls : Calls) (p digA N xtraiter : Nat) : BoundLoop calls numFastBody :=
  t3EpilLoopOf calls p digA N xtraiter (t3EpilExitWord p digA N xtraiter)
    (t3Epil_step_exit_test (calls := calls))
    (t3Epil_step_loop_test (calls := calls))

/-- **The residual copy loop from its head, discharged.**  At the whole bound the
run reaches `for.end100.i.i` within `(xtraiter + 1) * 3` control steps with the
exit word, and the continuation is the caller's. -/
theorem t3EpilLoop_run_at' (calls : Calls) (p digA N xtraiter : Nat) (s : State)
    (c : Nat) (h : T3EpilInv p digA N xtraiter xtraiter s c) (k : Nat) {o : Outcome}
    (hcont : ∀ (e : State), t3EpilExit e → t3EpilExitWord p digA N xtraiter e →
      runFuel calls k numFastBody e = some o) :
    runFuel calls ((xtraiter + 1) * 3 + k) numFastBody s = some o :=
  t3EpilLoop_run_at calls p digA N xtraiter (t3EpilExitWord p digA N xtraiter)
    (t3Epil_step_exit_test (calls := calls))
    (t3Epil_step_loop_test (calls := calls)) s c h k hcont

/-! ### Axiom footprints -/

#print axioms T3EpilInv.rpos
#print axioms T3EpilInv.cr
#print axioms t3EpilLoopOf
#print axioms t3EpilLoop_run_at
#print axioms t3Epil_step_exit_test
#print axioms t3Epil_step_loop_test
#print axioms t3EpilLoop
#print axioms t3EpilLoop_run_at'

end NumFastTier3CopyLoop

end LeanLLVM.Refinement
