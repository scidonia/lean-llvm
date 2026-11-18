/-
The copy's four-way unrolled main loop, as a `BoundLoop` shape and its budget.

`JsonStage2NumFastTier3CopySteps` gives the ladder's per-edge steps and
`JsonStage2NumFastTier3CopyLoop` the residual loop's induction.  The copy's main
loop is the nest those steps belong to: `for.body87.i.i` consumes four digits per
visit — the head's test and store, then the three repeated tests `for.inc98.i.i`,
`.1`, `.2` with their stores — and the last test's latch, `for.inc98.i.i.3`,
counts the visit against `%unroll_iter` and either re-enters the head or leaves
for `for.end100.i.i.loopexit.unr-lcssa`.  This module fixes that loop's *shape*
and its budget at the emitted blocks; its two visits are the piece still owed,
and `t3MainLoopOf` names exactly what they must supply.

**The measure.**  The latch's test is `%niter.next.3 = %unroll_iter`, and
`%niter` advances by four, so the counter `c` here is the *visit index*: the
carried `%niter` is `4 * c`, the bound is the visit count `nv = %unroll_iter / 4`,
and a visit spends one unit of the budget.  `budget` is then `c + r = nv`, and
`t3MainLoopOf` takes `%unroll_iter = 4 * nv` as the arithmetic the entry block's
`and` supplies: without it the latch's test would be about a bound that is not
the visit count's multiple.

**What the invariant carries.**  The frame (`t3MainFrame`): the digit array's
base, the copy array's pointer, the two bounds, the three `invariant.gep` bases
the stores read, the staging — every index below the digit count reads a digit
byte — and the digit count's bound.  The carried words are the digit index, the
accumulator and the visit index, with `i.toNat + 4 * r + xt = Nd`: the visits
left, four digits each, plus the peel's residue `xt` spend the staging exactly,
which is what the stores' reads and the exit's handoff both need.  The edge is
carried because the head's `phi`s read the predecessor's cells: the preheader's
`%i.2.i.i` on the first visit, the latch's three on every later one.  A visit
writes no memory — the nest only computes the accumulator — so the staging is
carried rather than re-derived.

**The exit.**  `t3MainExitWord` is what `for.end100.i.i.loopexit.unr-lcssa`'s
`phi`s read: the latch's `%inc99.i.i.3` and `%e.1.i.i.3`, and the frame, with
`i + xt ≤ Nd` — the residue and index the peel's own loop is entered at.  The
step from that exit block's `phi`s into `T3EpilInv` is
`JsonStage2NumFastTier3CopySteps`' `t3_epil_head_step_entry_store`/`_skip`'s
predecessor edge, and is owed with the visits.

**What is owed, precisely.**  `t3MainLoopOf` takes its two arms as parameters.
Each is one visit: the head's step at the edge the invariant names, then
`for.inc98.i.i`'s test and its three repetitions, then the latch.  The per-edge
steps are proved (`t3_head_step_entry_store`, `t3_head_step_back_skip`,
`t3_inc98_step_store_1`, `t3_if_then90_step_3`, `t3_latch3_step_exit`, …), so the
arm is their composition: at most nine control steps, the stopping states named
by `t3MainInv` and `t3MainExitWord`.  This module does not claim them.
-/
import LeanLLVM.Refinement.JsonStage2NumFastTier3CopyLoop

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

namespace NumFastTier3CopyUnroll

/-! ### The frame: the cells no visit writes -/

/-- What a visit does not touch: the digit array's base, the copy array's
pointer, the two bounds, the three `invariant.gep` bases the stores read, the
staging, and the digit count's bound. -/
def t3MainFrame (p digA Nd u xt : Nat) (env : Env) (mem : Mem) : Prop :=
  lookupName env "%p" = some (.ptr p) ∧
  lookupName env "%dig.i.i" = some (.ptr digA) ∧
  lookupName env "%unroll_iter" = some (.int 64 (BitVec.ofNat 64 u)) ∧
  lookupName env "%xtraiter" = some (.int 64 (BitVec.ofNat 64 xt)) ∧
  lookupName env "%invariant.gep" = some (.ptr (p + 1)) ∧
  lookupName env "%invariant.gep1191" = some (.ptr (p + 2)) ∧
  lookupName env "%invariant.gep1193" = some (.ptr (p + 3)) ∧
  (∀ k, k < Nd → ∃ d, readBytes mem (p + k) 1 = some [d] ∧
    48 ≤ d.toNat ∧ d.toNat ≤ 57) ∧
  Nd < 2 ^ 63

/-! ### The invariant -/

/-- The main loop's state at its head: the frame, the carried index, the
accumulator and the visit index, with the staging's arithmetic, and the edge the
head's `phi`s read. -/
def t3MainInv (p digA Nd nv u xt : Nat) (r : Nat) (s : State) (c : Nat) : Prop :=
  s.pc = "for.body87.i.i" ∧
  t3MainFrame p digA Nd u xt s.env s.mem ∧
  (∃ (i e : BitVec 64),
    i.toNat < 2 ^ 63 ∧ e.toNat < 10 ^ 7 ∧
    i.toNat + 4 * r + xt = Nd ∧
    ((s.pre = some "for.body87.i.i.preheader.new" ∧
        lookupName s.env "%i.2.i.i" = some (.int 64 i) ∧ c = 0)
      ∨ (s.pre = some "for.inc98.i.i.3" ∧
        lookupName s.env "%inc99.i.i.3" = some (.int 64 i) ∧
        lookupName s.env "%e.1.i.i.3" = some (.int 64 e) ∧
        lookupName s.env "%niter.next.3" =
          some (.int 64 (BitVec.ofNat 64 (4 * c)))))) ∧
  c + r = nv ∧
  1 ≤ r

/-- The invariant's counter is the remaining visit budget. -/
theorem t3MainInv.cr {p digA Nd nv u xt r : Nat} {s : State} {c : Nat}
    (h : t3MainInv p digA Nd nv u xt r s c) : c + r = nv :=
  h.2.2.2.1

/-- The invariant is inhabited only with a visit left. -/
theorem t3MainInv.rpos {p digA Nd nv u xt r : Nat} {s : State} {c : Nat}
    (h : t3MainInv p digA Nd nv u xt r s c) : 1 ≤ r :=
  h.2.2.2.2

/-- The loop's exit test: the latch's next counter reaches the bound.  The
carried `%niter` is `4 * c`, so the latch's `%niter.next.3 = %unroll_iter` reads
`4 * (c + 1) = %unroll_iter`, and with `%unroll_iter = 4 * nv` that is `nv ≤ c +
1`. -/
def t3MainAtBound (nv : Nat) : State → Nat → Bool :=
  fun _ c => decide (nv ≤ c + 1)

/-- The nest's exit block. -/
def t3MainExit : State → Prop := fun e => e.pc = "for.end100.i.i.loopexit.unr-lcssa"

/-- What the nest's exit block's `phi`s read: the latch's two cells and the
frame, with the residue and index the peel's own loop is entered at. -/
def t3MainExitWord (p digA Nd xt : Nat) : State → Prop := fun e =>
  e.pre = some "for.inc98.i.i.3" ∧
  lookupName e.env "%p" = some (.ptr p) ∧
  lookupName e.env "%dig.i.i" = some (.ptr digA) ∧
  lookupName e.env "%xtraiter" = some (.int 64 (BitVec.ofNat 64 xt)) ∧
  (∀ k, k < Nd → ∃ d, readBytes e.mem (p + k) 1 = some [d] ∧
    48 ≤ d.toNat ∧ d.toNat ≤ 57) ∧
  Nd < 2 ^ 63 ∧ xt ≤ 3 ∧
  (∃ (i ea : BitVec 64),
    lookupName e.env "%inc99.i.i.3" = some (.int 64 i) ∧
    lookupName e.env "%e.1.i.i.3" = some (.int 64 ea) ∧
    i.toNat < 2 ^ 63 ∧ ea.toNat < 10 ^ 7 ∧ i.toNat + xt ≤ Nd)

/-! ### The shape -/

/-- **The main loop's shape.**  Head, exit, bound, cost, invariant, exit test and
exit word are fixed at the emitted blocks; the two visits are its arms.  A visit
is at most nine control steps: the head's test, four tests and up to four stores,
and the latch. -/
def t3MainLoopOf (calls : Calls) (p digA Nd nv u xt : Nat) (hu : u = 4 * nv)
    (step_exit : ∀ (r : Nat) (s : State) (c : Nat),
      t3MainInv p digA Nd nv u xt r s c → t3MainAtBound nv s c = true →
      ∃ (e : State) (j : Nat), j ≤ 9 ∧ t3MainExit e ∧
        t3MainExitWord p digA Nd xt e ∧
        ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e)
    (step_loop : ∀ (r : Nat) (s : State) (c : Nat),
      t3MainInv p digA Nd nv u xt (r + 1) s c → t3MainAtBound nv s c = false →
      ∃ (e : State) (c' : Nat) (j : Nat), j ≤ 9 ∧ e.pc = "for.body87.i.i" ∧ c < c' ∧
        t3MainInv p digA Nd nv u xt r e c' ∧
        ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e) :
    BoundLoop calls numFastBody where
  head := "for.body87.i.i"
  exitBlock := "for.end100.i.i.loopexit.unr-lcssa"
  N := nv
  cost := 9
  Inv := t3MainInv p digA Nd nv u xt
  atBound := t3MainAtBound nv
  Exit := t3MainExit
  ExitWord := t3MainExitWord p digA Nd xt
  step_exit := step_exit
  step_loop := step_loop
  exit_at_zero := by
    intro s c h
    exact absurd (t3MainInv.rpos h) (by omega)
  budget := by
    intro r s c h
    have hcr := t3MainInv.cr h
    omega

/-- **The main loop from its head.**  At the whole visit bound the run reaches
the nest's exit block within `(nv + 1) * 9` control steps — a term of the
caller's arguments — leaving the latch's cells and the staging's residue. -/
theorem t3MainLoop_run_at (calls : Calls) (p digA Nd nv u xt : Nat) (hu : u = 4 * nv)
    (step_exit : ∀ (r : Nat) (s : State) (c : Nat),
      t3MainInv p digA Nd nv u xt r s c → t3MainAtBound nv s c = true →
      ∃ (e : State) (j : Nat), j ≤ 9 ∧ t3MainExit e ∧
        t3MainExitWord p digA Nd xt e ∧
        ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e)
    (step_loop : ∀ (r : Nat) (s : State) (c : Nat),
      t3MainInv p digA Nd nv u xt (r + 1) s c → t3MainAtBound nv s c = false →
      ∃ (e : State) (c' : Nat) (j : Nat), j ≤ 9 ∧ e.pc = "for.body87.i.i" ∧ c < c' ∧
        t3MainInv p digA Nd nv u xt r e c' ∧
        ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e)
    (s : State) (c : Nat) (h : t3MainInv p digA Nd nv u xt nv s c) (k : Nat)
    {o : Outcome}
    (hcont : ∀ (e : State), t3MainExit e → t3MainExitWord p digA Nd xt e →
      runFuel calls k numFastBody e = some o) :
    runFuel calls ((nv + 1) * 9 + k) numFastBody s = some o :=
  (t3MainLoopOf calls p digA Nd nv u xt hu step_exit step_loop).run_at s c h k hcont

/-! ### Axiom footprints -/

#print axioms t3MainInv.cr
#print axioms t3MainInv.rpos
#print axioms t3MainLoopOf
#print axioms t3MainLoop_run_at

end NumFastTier3CopyUnroll

end LeanLLVM.Refinement
