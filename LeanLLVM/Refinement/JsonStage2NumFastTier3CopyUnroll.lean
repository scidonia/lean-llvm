/-
The copy's four-way unrolled main loop, as a `BoundLoop` shape and its budget.

`JsonStage2NumFastTier3CopySteps` gives the ladder's per-edge steps and
`JsonStage2NumFastTier3CopyLoop` the residual loop's induction.  The copy's main
loop is the nest those steps belong to: `for.body87.i.i` consumes four digits per
visit — the head's test and store, then the three repeated tests `for.inc98.i.i`,
`.1`, `.2` with their stores — and the last test's latch, `for.inc98.i.i.3`,
counts the visit against `%unroll_iter` and either re-enters the head or leaves
for `for.end100.i.i.loopexit.unr-lcssa`.  This module fixes that loop's *shape*
and its budget at the emitted blocks, and discharges its two visits: `t3Visit`
is one visit's run, and `t3Main_step_exit`/`t3Main_step_loop` are `t3MainLoopOf`'s
parameters, hence `t3MainLoop` and `t3MainLoop_run_at'`.

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
residue's bound `xt ≤ 3` is a conjunct of the invariant: the peel hands a residue
below four, and the exit word carries it for the residual loop's entry, which
needs it (`T3EpilInv`).  The step from that exit block's `phi`s into `T3EpilInv`
is a separate one, at the exit block's own pin.

**The visits.**  `t3Visit` is one visit: the head's test at the invariant's edge,
then `for.inc98.i.i`'s test and its three repetitions with their stores, reaching
the latch's entry within eight control steps.  It is stated at a *position*
(`t3LadderAt`), so the four stages — `t3HeadVisit`, `t3AtA`, `t3AtB`, `t3AtC` —
compose by the run's own append rather than by a case bash over the four stores:
each stage is at most two control steps, one for the test and one for the store
the cap permits.  The arms then spend the ninth on the latch, whose test reaches
`%unroll_iter` exactly when the carried counter `4 * c` is one visit short of the
bound: `t3Main_step_exit` leaves the exit word, `t3Main_step_loop` re-enters the
head with the index advanced by four and the counter by one visit.
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
accumulator and the visit index, with the staging's arithmetic, the edge the
head's `phi`s read, and the peel's residue below four — the bound the exit word
hands the residual loop. -/
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
  1 ≤ r ∧
  xt ≤ 3

/-- The invariant's counter is the remaining visit budget. -/
theorem t3MainInv.cr {p digA Nd nv u xt r : Nat} {s : State} {c : Nat}
    (h : t3MainInv p digA Nd nv u xt r s c) : c + r = nv :=
  h.2.2.2.1

/-- The invariant is inhabited only with a visit left. -/
theorem t3MainInv.rpos {p digA Nd nv u xt r : Nat} {s : State} {c : Nat}
    (h : t3MainInv p digA Nd nv u xt r s c) : 1 ≤ r :=
  h.2.2.2.2.1

/-- The residue is a peel's: below four, which is what the exit word hands the
epilogue's loop. -/
theorem t3MainInv.xt3 {p digA Nd nv u xt r : Nat} {s : State} {c : Nat}
    (h : t3MainInv p digA Nd nv u xt r s c) : xt ≤ 3 :=
  h.2.2.2.2.2

/-- The loop's exit test: the latch's next counter reaches the bound.  The
carried `%niter` is `4 * c`, so the latch's `%niter.next.3 = %unroll_iter` reads
`4 * (c + 1) = %unroll_iter`, and with `%unroll_iter = 4 * nv` that is `nv ≤ c +
1`. -/
def t3MainAtBound (nv : Nat) : State → Nat → Bool :=
  fun _ c => decide (nv ≤ c + 1)

/-- The exit test reads `nv ≤ c + 1`. -/
theorem t3MainAtBound_true {nv c : Nat} {s : State}
    (h : t3MainAtBound nv s c = true) : nv ≤ c + 1 := by
  simpa only [t3MainAtBound, decide_eq_true_eq] using h

/-- Its refusal is the opposite inequality. -/
theorem t3MainAtBound_false {nv c : Nat} {s : State}
    (h : t3MainAtBound nv s c = false) : ¬ nv ≤ c + 1 := by
  simpa only [t3MainAtBound, decide_eq_false_iff_not] using h

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

/-! ### The visit: the ladder's blocks and the accumulator

A visit is the head's test, then the three repeated tests with their stores, then
the latch.  `JsonStage2NumFastTier3CopySteps` proves each block's step at its own
in-edge; what the visit adds is the composition, and the arithmetic that makes it
atomic: the stores' successor cell `10 * e + d`, the staging slack the four
stores' reads need, and the counter's four-step advance.

The section fixes, once, the four store environments and the three test
environments of the unrolled body, their frame transport, and the one bundle a
position in the ladder is: the block, the frame, the index and the counter the
ladder carries, the accumulator the block's `phi` selects at either in-edge, and
the slack.  The four position lemmas then read the same way at their own names. -/

/-- The store block's successor cell: `10 * e + d` as a `BitVec`. -/
def t3StoreNext (e : BitVec 64) (d : UInt8) : BitVec 64 :=
  ((e * 10#64) + 0xffffffffffffffd0#64) + BitVec.ofNat 64 (vByte d).toNat

/-- The successor cell's `Nat` reading, at a digit's byte. -/
theorem t3StoreNext_toNat {e : BitVec 64} {d : UInt8}
    (he : e.toNat < 10 ^ 7) (hlo : 48 ≤ d.toNat) (hhi : d.toNat ≤ 57) :
    (t3StoreNext e d).toNat = 10 * e.toNat + (d.toNat - 48) :=
  t3_store_next_toNat he hlo hhi

/-- The successor cell stays inside the bound while the accumulator is below the
cap. -/
theorem t3StoreNext_lt {e : BitVec 64} {d : UInt8}
    (he : e.toNat < 10 ^ 6) (hlo : 48 ≤ d.toNat) (hhi : d.toNat ≤ 57) :
    (t3StoreNext e d).toNat < 10 ^ 7 :=
  (t3_store_next_lt he hlo hhi).1

/-- **The frame's cells.**  A visitor reads the seven cells the frame binds, the
staging and the digit count's bound; these are the projections a visit uses. -/
theorem t3MainFrame.p {p digA Nd u xt : Nat} {env : Env} {mem : Mem}
    (h : t3MainFrame p digA Nd u xt env mem) :
    lookupName env "%p" = some (.ptr p) := h.1

theorem t3MainFrame.dig {p digA Nd u xt : Nat} {env : Env} {mem : Mem}
    (h : t3MainFrame p digA Nd u xt env mem) :
    lookupName env "%dig.i.i" = some (.ptr digA) := h.2.1

theorem t3MainFrame.iter {p digA Nd u xt : Nat} {env : Env} {mem : Mem}
    (h : t3MainFrame p digA Nd u xt env mem) :
    lookupName env "%unroll_iter" = some (.int 64 (BitVec.ofNat 64 u)) := h.2.2.1

theorem t3MainFrame.xt {p digA Nd u xt : Nat} {env : Env} {mem : Mem}
    (h : t3MainFrame p digA Nd u xt env mem) :
    lookupName env "%xtraiter" = some (.int 64 (BitVec.ofNat 64 xt)) := h.2.2.2.1

theorem t3MainFrame.gep1 {p digA Nd u xt : Nat} {env : Env} {mem : Mem}
    (h : t3MainFrame p digA Nd u xt env mem) :
    lookupName env "%invariant.gep" = some (.ptr (p + 1)) := h.2.2.2.2.1

theorem t3MainFrame.gep2 {p digA Nd u xt : Nat} {env : Env} {mem : Mem}
    (h : t3MainFrame p digA Nd u xt env mem) :
    lookupName env "%invariant.gep1191" = some (.ptr (p + 2)) := h.2.2.2.2.2.1

theorem t3MainFrame.gep3 {p digA Nd u xt : Nat} {env : Env} {mem : Mem}
    (h : t3MainFrame p digA Nd u xt env mem) :
    lookupName env "%invariant.gep1193" = some (.ptr (p + 3)) := h.2.2.2.2.2.2.1

theorem t3MainFrame.stage {p digA Nd u xt : Nat} {env : Env} {mem : Mem}
    (h : t3MainFrame p digA Nd u xt env mem) (k : Nat) (hk : k < Nd) :
    ∃ d, readBytes mem (p + k) 1 = some [d] ∧ 48 ≤ d.toNat ∧ d.toNat ≤ 57 :=
  h.2.2.2.2.2.2.2.1 k hk

theorem t3MainFrame.nd {p digA Nd u xt : Nat} {env : Env} {mem : Mem}
    (h : t3MainFrame p digA Nd u xt env mem) : Nd < 2 ^ 63 := h.2.2.2.2.2.2.2.2

/-! ### The unrolled body's environments

The four stores and the three repeated tests differ only in their cells' names,
so each is an abbreviation of `JsonStage2NumFastTier3CopySteps`' shape at its own
list. -/

/-- The first digit's store, `if.then90.i.i`. -/
def t3S1 (env : Env) (e : BitVec 64) (d : UInt8) (a : Nat) : Env :=
  t3StoreEnv env "%mul91.i.i" "%arrayidx92.i.i" "%64" "%conv93.i.i" "%sub94.i.i"
    "%add96.i.i" e d a

/-- The second digit's store, `if.then90.i.i.1`. -/
def t3S2 (env : Env) (e : BitVec 64) (d : UInt8) (a : Nat) : Env :=
  t3StoreEnv env "%mul91.i.i.1" "%gep" "%65" "%conv93.i.i.1" "%sub94.i.i.1"
    "%add96.i.i.1" e d a

/-- The third digit's store, `if.then90.i.i.2`. -/
def t3S3 (env : Env) (e : BitVec 64) (d : UInt8) (a : Nat) : Env :=
  t3StoreEnv env "%mul91.i.i.2" "%gep1192" "%66" "%conv93.i.i.2" "%sub94.i.i.2"
    "%add96.i.i.2" e d a

/-- The fourth digit's store, `if.then90.i.i.3`. -/
def t3S4 (env : Env) (e : BitVec 64) (d : UInt8) (a : Nat) : Env :=
  t3StoreEnv env "%mul91.i.i.3" "%gep1194" "%67" "%conv93.i.i.3" "%sub94.i.i.3"
    "%add96.i.i.3" e d a

/-- The first repeated test, `for.inc98.i.i`. -/
def t3T1 (env : Env) (e : BitVec 64) : Env :=
  t3TestEnv env "%e.1.i.i" "%cmp88.i.i.1" e

/-- The second repeated test, `for.inc98.i.i.1`. -/
def t3T2 (env : Env) (e : BitVec 64) : Env :=
  t3TestEnv env "%e.1.i.i.1" "%cmp88.i.i.2" e

/-- The third repeated test, `for.inc98.i.i.2`. -/
def t3T3 (env : Env) (e : BitVec 64) : Env :=
  t3TestEnv env "%e.1.i.i.2" "%cmp88.i.i.3" e

/-- The main latch, `for.inc98.i.i.3`. -/
def t3Lat (env : Env) (e i n u : BitVec 64) : Env :=
  t3LatchEnv env "%e.1.i.i.3" "%inc99.i.i.3" "%niter.next.3" "%niter.ncmp.3" e i n u

/-! #### The cells each environment keeps -/

theorem t3HeadEnv_other {env : Env} {i e n : BitVec 64} {c : String}
    (h1 : c ≠ "%cmp88.i.i" := by decide) (h2 : c ≠ "%niter" := by decide)
    (h3 : c ≠ "%e.0734.i.i" := by decide) (h4 : c ≠ "%i.3735.i.i" := by decide) :
    lookupName (t3HeadEnv env i e n) c = lookupName env c := by
  simp only [t3HeadEnv]
  rw [lookupName_cons_ne _ _ (Ne.symm h1), lookupName_cons_ne _ _ (Ne.symm h2),
    lookupName_cons_ne _ _ (Ne.symm h3), lookupName_cons_ne _ _ (Ne.symm h4)]

theorem t3HeadEnv_i (env : Env) (i e n : BitVec 64) :
    lookupName (t3HeadEnv env i e n) "%i.3735.i.i" = some (.int 64 i) := by
  simp only [t3HeadEnv]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide), lookupName_cons_self]

theorem t3HeadEnv_e (env : Env) (i e n : BitVec 64) :
    lookupName (t3HeadEnv env i e n) "%e.0734.i.i" = some (.int 64 e) := by
  simp only [t3HeadEnv]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_self]

theorem t3HeadEnv_niter (env : Env) (i e n : BitVec 64) :
    lookupName (t3HeadEnv env i e n) "%niter" = some (.int 64 n) := by
  simp only [t3HeadEnv]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]

theorem t3S1_other (env : Env) (e : BitVec 64) (d : UInt8) (a : Nat) {c : String}
    (h1 : c ≠ "%add96.i.i" := by decide) (h2 : c ≠ "%sub94.i.i" := by decide)
    (h3 : c ≠ "%conv93.i.i" := by decide) (h4 : c ≠ "%64" := by decide)
    (h5 : c ≠ "%arrayidx92.i.i" := by decide) (h6 : c ≠ "%mul91.i.i" := by decide) :
    lookupName (t3S1 env e d a) c = lookupName env c := by
  simp only [t3S1, t3StoreEnv]
  rw [lookupName_cons_ne _ _ (Ne.symm h1), lookupName_cons_ne _ _ (Ne.symm h2),
    lookupName_cons_ne _ _ (Ne.symm h3), lookupName_cons_ne _ _ (Ne.symm h4),
    lookupName_cons_ne _ _ (Ne.symm h5), lookupName_cons_ne _ _ (Ne.symm h6)]

theorem t3S2_other (env : Env) (e : BitVec 64) (d : UInt8) (a : Nat) {c : String}
    (h1 : c ≠ "%add96.i.i.1" := by decide) (h2 : c ≠ "%sub94.i.i.1" := by decide)
    (h3 : c ≠ "%conv93.i.i.1" := by decide) (h4 : c ≠ "%65" := by decide)
    (h5 : c ≠ "%gep" := by decide) (h6 : c ≠ "%mul91.i.i.1" := by decide) :
    lookupName (t3S2 env e d a) c = lookupName env c := by
  simp only [t3S2, t3StoreEnv]
  rw [lookupName_cons_ne _ _ (Ne.symm h1), lookupName_cons_ne _ _ (Ne.symm h2),
    lookupName_cons_ne _ _ (Ne.symm h3), lookupName_cons_ne _ _ (Ne.symm h4),
    lookupName_cons_ne _ _ (Ne.symm h5), lookupName_cons_ne _ _ (Ne.symm h6)]

theorem t3S3_other (env : Env) (e : BitVec 64) (d : UInt8) (a : Nat) {c : String}
    (h1 : c ≠ "%add96.i.i.2" := by decide) (h2 : c ≠ "%sub94.i.i.2" := by decide)
    (h3 : c ≠ "%conv93.i.i.2" := by decide) (h4 : c ≠ "%66" := by decide)
    (h5 : c ≠ "%gep1192" := by decide) (h6 : c ≠ "%mul91.i.i.2" := by decide) :
    lookupName (t3S3 env e d a) c = lookupName env c := by
  simp only [t3S3, t3StoreEnv]
  rw [lookupName_cons_ne _ _ (Ne.symm h1), lookupName_cons_ne _ _ (Ne.symm h2),
    lookupName_cons_ne _ _ (Ne.symm h3), lookupName_cons_ne _ _ (Ne.symm h4),
    lookupName_cons_ne _ _ (Ne.symm h5), lookupName_cons_ne _ _ (Ne.symm h6)]

theorem t3S4_other (env : Env) (e : BitVec 64) (d : UInt8) (a : Nat) {c : String}
    (h1 : c ≠ "%add96.i.i.3" := by decide) (h2 : c ≠ "%sub94.i.i.3" := by decide)
    (h3 : c ≠ "%conv93.i.i.3" := by decide) (h4 : c ≠ "%67" := by decide)
    (h5 : c ≠ "%gep1194" := by decide) (h6 : c ≠ "%mul91.i.i.3" := by decide) :
    lookupName (t3S4 env e d a) c = lookupName env c := by
  simp only [t3S4, t3StoreEnv]
  rw [lookupName_cons_ne _ _ (Ne.symm h1), lookupName_cons_ne _ _ (Ne.symm h2),
    lookupName_cons_ne _ _ (Ne.symm h3), lookupName_cons_ne _ _ (Ne.symm h4),
    lookupName_cons_ne _ _ (Ne.symm h5), lookupName_cons_ne _ _ (Ne.symm h6)]

theorem t3T1_other (env : Env) (e : BitVec 64) {c : String}
    (h1 : c ≠ "%cmp88.i.i.1" := by decide) (h2 : c ≠ "%e.1.i.i" := by decide) :
    lookupName (t3T1 env e) c = lookupName env c := by
  simp only [t3T1, t3TestEnv]
  rw [lookupName_cons_ne _ _ (Ne.symm h1), lookupName_cons_ne _ _ (Ne.symm h2)]

theorem t3T2_other (env : Env) (e : BitVec 64) {c : String}
    (h1 : c ≠ "%cmp88.i.i.2" := by decide) (h2 : c ≠ "%e.1.i.i.1" := by decide) :
    lookupName (t3T2 env e) c = lookupName env c := by
  simp only [t3T2, t3TestEnv]
  rw [lookupName_cons_ne _ _ (Ne.symm h1), lookupName_cons_ne _ _ (Ne.symm h2)]

theorem t3T3_other (env : Env) (e : BitVec 64) {c : String}
    (h1 : c ≠ "%cmp88.i.i.3" := by decide) (h2 : c ≠ "%e.1.i.i.2" := by decide) :
    lookupName (t3T3 env e) c = lookupName env c := by
  simp only [t3T3, t3TestEnv]
  rw [lookupName_cons_ne _ _ (Ne.symm h1), lookupName_cons_ne _ _ (Ne.symm h2)]

theorem t3Lat_other (env : Env) (e i n u : BitVec 64) {c : String}
    (h1 : c ≠ "%niter.ncmp.3" := by decide) (h2 : c ≠ "%niter.next.3" := by decide)
    (h3 : c ≠ "%inc99.i.i.3" := by decide) (h4 : c ≠ "%e.1.i.i.3" := by decide) :
    lookupName (t3Lat env e i n u) c = lookupName env c := by
  simp only [t3Lat, t3LatchEnv]
  rw [lookupName_cons_ne _ _ (Ne.symm h1), lookupName_cons_ne _ _ (Ne.symm h2),
    lookupName_cons_ne _ _ (Ne.symm h3), lookupName_cons_ne _ _ (Ne.symm h4)]

/-! #### The cells each environment writes -/

theorem t3S1_add96 (env : Env) (e : BitVec 64) (d : UInt8) (a : Nat) :
    lookupName (t3S1 env e d a) "%add96.i.i" = some (.int 64 (t3StoreNext e d)) := by
  simp only [t3S1, t3StoreEnv, t3StoreNext]
  exact lookupName_cons_self ..

theorem t3S2_add96 (env : Env) (e : BitVec 64) (d : UInt8) (a : Nat) :
    lookupName (t3S2 env e d a) "%add96.i.i.1" = some (.int 64 (t3StoreNext e d)) := by
  simp only [t3S2, t3StoreEnv, t3StoreNext]
  exact lookupName_cons_self ..

theorem t3S3_add96 (env : Env) (e : BitVec 64) (d : UInt8) (a : Nat) :
    lookupName (t3S3 env e d a) "%add96.i.i.2" = some (.int 64 (t3StoreNext e d)) := by
  simp only [t3S3, t3StoreEnv, t3StoreNext]
  exact lookupName_cons_self ..

theorem t3S4_add96 (env : Env) (e : BitVec 64) (d : UInt8) (a : Nat) :
    lookupName (t3S4 env e d a) "%add96.i.i.3" = some (.int 64 (t3StoreNext e d)) := by
  simp only [t3S4, t3StoreEnv, t3StoreNext]
  exact lookupName_cons_self ..

theorem t3T1_e (env : Env) (e : BitVec 64) :
    lookupName (t3T1 env e) "%e.1.i.i" = some (.int 64 e) := by
  simp only [t3T1, t3TestEnv]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]

theorem t3T2_e (env : Env) (e : BitVec 64) :
    lookupName (t3T2 env e) "%e.1.i.i.1" = some (.int 64 e) := by
  simp only [t3T2, t3TestEnv]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]

theorem t3T3_e (env : Env) (e : BitVec 64) :
    lookupName (t3T3 env e) "%e.1.i.i.2" = some (.int 64 e) := by
  simp only [t3T3, t3TestEnv]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]

theorem t3Lat_inc (env : Env) (e i n u : BitVec 64) :
    lookupName (t3Lat env e i n u) "%inc99.i.i.3" = some (.int 64 i) := by
  simp only [t3Lat, t3LatchEnv]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_self]

theorem t3Lat_e1 (env : Env) (e i n u : BitVec 64) :
    lookupName (t3Lat env e i n u) "%e.1.i.i.3" = some (.int 64 e) := by
  simp only [t3Lat, t3LatchEnv]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide), lookupName_cons_self]

theorem t3Lat_next (env : Env) (e i n u : BitVec 64) :
    lookupName (t3Lat env e i n u) "%niter.next.3" = some (.int 64 n) := by
  simp only [t3Lat, t3LatchEnv]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]

/-! #### The frame through each environment -/

theorem t3MainFrame_head {p digA Nd u xt : Nat} {env : Env} {mem : Mem}
    {i e n : BitVec 64} (h : t3MainFrame p digA Nd u xt env mem) :
    t3MainFrame p digA Nd u xt (t3HeadEnv env i e n) mem := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, h8, h9⟩
  · rw [t3HeadEnv_other]; exact h1
  · rw [t3HeadEnv_other]; exact h2
  · rw [t3HeadEnv_other]; exact h3
  · rw [t3HeadEnv_other]; exact h4
  · rw [t3HeadEnv_other]; exact h5
  · rw [t3HeadEnv_other]; exact h6
  · rw [t3HeadEnv_other]; exact h7

theorem t3MainFrame_T1 {p digA Nd u xt : Nat} {env : Env} {mem : Mem}
    {e : BitVec 64} (h : t3MainFrame p digA Nd u xt env mem) :
    t3MainFrame p digA Nd u xt (t3T1 env e) mem := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, h8, h9⟩
  · rw [t3T1_other]; exact h1
  · rw [t3T1_other]; exact h2
  · rw [t3T1_other]; exact h3
  · rw [t3T1_other]; exact h4
  · rw [t3T1_other]; exact h5
  · rw [t3T1_other]; exact h6
  · rw [t3T1_other]; exact h7

theorem t3MainFrame_T2 {p digA Nd u xt : Nat} {env : Env} {mem : Mem}
    {e : BitVec 64} (h : t3MainFrame p digA Nd u xt env mem) :
    t3MainFrame p digA Nd u xt (t3T2 env e) mem := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, h8, h9⟩
  · rw [t3T2_other]; exact h1
  · rw [t3T2_other]; exact h2
  · rw [t3T2_other]; exact h3
  · rw [t3T2_other]; exact h4
  · rw [t3T2_other]; exact h5
  · rw [t3T2_other]; exact h6
  · rw [t3T2_other]; exact h7

theorem t3MainFrame_T3 {p digA Nd u xt : Nat} {env : Env} {mem : Mem}
    {e : BitVec 64} (h : t3MainFrame p digA Nd u xt env mem) :
    t3MainFrame p digA Nd u xt (t3T3 env e) mem := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, h8, h9⟩
  · rw [t3T3_other]; exact h1
  · rw [t3T3_other]; exact h2
  · rw [t3T3_other]; exact h3
  · rw [t3T3_other]; exact h4
  · rw [t3T3_other]; exact h5
  · rw [t3T3_other]; exact h6
  · rw [t3T3_other]; exact h7

theorem t3MainFrame_S1 {p digA Nd u xt : Nat} {env : Env} {mem : Mem}
    {e : BitVec 64} {d : UInt8} {a : Nat} (h : t3MainFrame p digA Nd u xt env mem) :
    t3MainFrame p digA Nd u xt (t3S1 env e d a) mem := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, h8, h9⟩
  · rw [t3S1_other]; exact h1
  · rw [t3S1_other]; exact h2
  · rw [t3S1_other]; exact h3
  · rw [t3S1_other]; exact h4
  · rw [t3S1_other]; exact h5
  · rw [t3S1_other]; exact h6
  · rw [t3S1_other]; exact h7

theorem t3MainFrame_S2 {p digA Nd u xt : Nat} {env : Env} {mem : Mem}
    {e : BitVec 64} {d : UInt8} {a : Nat} (h : t3MainFrame p digA Nd u xt env mem) :
    t3MainFrame p digA Nd u xt (t3S2 env e d a) mem := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, h8, h9⟩
  · rw [t3S2_other]; exact h1
  · rw [t3S2_other]; exact h2
  · rw [t3S2_other]; exact h3
  · rw [t3S2_other]; exact h4
  · rw [t3S2_other]; exact h5
  · rw [t3S2_other]; exact h6
  · rw [t3S2_other]; exact h7

theorem t3MainFrame_S3 {p digA Nd u xt : Nat} {env : Env} {mem : Mem}
    {e : BitVec 64} {d : UInt8} {a : Nat} (h : t3MainFrame p digA Nd u xt env mem) :
    t3MainFrame p digA Nd u xt (t3S3 env e d a) mem := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, h8, h9⟩
  · rw [t3S3_other]; exact h1
  · rw [t3S3_other]; exact h2
  · rw [t3S3_other]; exact h3
  · rw [t3S3_other]; exact h4
  · rw [t3S3_other]; exact h5
  · rw [t3S3_other]; exact h6
  · rw [t3S3_other]; exact h7

theorem t3MainFrame_S4 {p digA Nd u xt : Nat} {env : Env} {mem : Mem}
    {e : BitVec 64} {d : UInt8} {a : Nat} (h : t3MainFrame p digA Nd u xt env mem) :
    t3MainFrame p digA Nd u xt (t3S4 env e d a) mem := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, h8, h9⟩
  · rw [t3S4_other]; exact h1
  · rw [t3S4_other]; exact h2
  · rw [t3S4_other]; exact h3
  · rw [t3S4_other]; exact h4
  · rw [t3S4_other]; exact h5
  · rw [t3S4_other]; exact h6
  · rw [t3S4_other]; exact h7

theorem t3MainFrame_lat {p digA Nd u xt : Nat} {env : Env} {mem : Mem}
    {e i n u' : BitVec 64} (h : t3MainFrame p digA Nd u xt env mem) :
    t3MainFrame p digA Nd u xt (t3Lat env e i n u') mem := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, h8, h9⟩
  · rw [t3Lat_other]; exact h1
  · rw [t3Lat_other]; exact h2
  · rw [t3Lat_other]; exact h3
  · rw [t3Lat_other]; exact h4
  · rw [t3Lat_other]; exact h5
  · rw [t3Lat_other]; exact h6
  · rw [t3Lat_other]; exact h7

/-! ### The counter's four-step advance, and the latch's test

The latch computes `%niter.next.3 = %niter + 4` and compares it with
`%unroll_iter`.  The carried `%niter` is `4 * c`, so the comparison is between
`ofNat 64 (4 * c + 4)` and `ofNat 64 u`, and the two facts below are what the
arms read: the identity (which holds at every counter, wrapped or not), and the
`Nat` separation at a counter that has not reached the bound, where the trip
count's distance is at most `2 ^ 63` because the staging's slack is. -/

/-- The counter's four-step advance, at every counter. -/
theorem t3_ofNat_four {c : Nat} :
    BitVec.ofNat 64 (4 * c) + 0x4#64 = BitVec.ofNat 64 (4 * c + 4) := by
  refine BitVec.toNat_inj.mp ?_
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h4 : (4 : Nat) % 2 ^ 64 = 4 := Nat.mod_eq_of_lt (by decide)
  rw [h4]
  exact (Nat.add_mod (4 * c) 4 (2 ^ 64)).symm

/-- The index's four-step advance: no wrap while the index is a signed word's. -/
theorem t3_add_four_toNat {x : BitVec 64} (h : x.toNat + 4 < 2 ^ 64) :
    (x + 0x4#64).toNat = x.toNat + 4 := by
  have h4 : (0x4#64 : BitVec 64).toNat = 4 := by decide
  rw [BitVec.toNat_add, h4, Nat.mod_eq_of_lt h]

/-- Four times a successor, distributed: the visit's count in `Nat` terms. -/
theorem t3_four_succ (x : Nat) : 4 * (x + 1) = 4 * x + 4 := by
  rw [Nat.mul_add, Nat.mul_one]

/-- Four times a sum. -/
theorem t3_four_add (a b : Nat) : 4 * (a + b) = 4 * a + 4 * b := Nat.mul_add 4 a b

/-- A positive count's four is at least four: the stores' read slack. -/
theorem t3_four_le {r : Nat} (h : 1 ≤ r) : 4 ≤ 4 * r := by
  have := Nat.mul_le_mul_left 4 h
  simpa using this

/-- Two naturals less than `n` apart have different residues. -/
theorem t3_mod_ne {a b n : Nat} (hn : 0 < n) (ha : a < b) (hb : b < a + n) :
    a % n ≠ b % n := by
  intro h
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  have hd0 : 0 < d := by omega
  have hd : d < n := by omega
  have hdmod : d % n = d := Nat.mod_eq_of_lt hd
  rw [Nat.add_mod, hdmod] at h
  have har : a % n < n := Nat.mod_lt _ hn
  rcases Nat.lt_or_ge (a % n + d) n with hcase | hcase
  · rw [Nat.mod_eq_of_lt hcase] at h; omega
  · rw [Nat.mod_eq_sub_mod hcase] at h
    have hsub : a % n + d - n < n := by omega
    rw [Nat.mod_eq_of_lt hsub] at h
    omega

/-- The same separation at the words the latch compares. -/
theorem t3_ofNat_ne {a b : Nat} (ha : a < b) (hb : b < a + 2 ^ 64) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
  intro h
  have h2 := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h2
  exact t3_mod_ne (by decide) ha hb h2

/-- The equality bit at two equal words. -/
theorem t3_icmp_eq_one {w : Nat} {a b : BitVec w} (h : a = b) :
    evalICmp .eq a b = (1 : BitVec 1) := by
  subst h
  rw [show evalICmp .eq a a = BitVec.ofBool (decide (a = a)) from rfl]
  exact NumFastStarts.ofBool_bool.mpr (decide_eq_true rfl)

/-- The equality bit at two distinct words. -/
theorem t3_icmp_eq_zero {w : Nat} {a b : BitVec w} (h : a ≠ b) :
    evalICmp .eq a b = (0 : BitVec 1) := by
  rcases bitVec1_eq_zero_or_one (evalICmp .eq a b) with h0 | h1
  · exact h0
  · rw [show evalICmp .eq a b = BitVec.ofBool (decide (a = b)) from rfl] at h1
    exact absurd (decide_eq_true_iff.mp (NumFastStarts.ofBool_bool.mp h1)) h

/-! ### The position in the ladder

A position is a block, the frame, the index and the counter the ladder carries,
the accumulator the block's `phi` selects at either in-edge, and the slack the
four stores' reads need from the staging. -/

/-- A position in the unrolled ladder. -/
def t3LadderAt (p digA Nd u xt c : Nat) (i : BitVec 64)
    (pc cellSt preSt cellSk preSk : String) (s : State) : Prop :=
  s.pc = pc ∧
  t3MainFrame p digA Nd u xt s.env s.mem ∧
  lookupName s.env "%i.3735.i.i" = some (.int 64 i) ∧
  i.toNat < 2 ^ 63 ∧
  i.toNat + 4 ≤ Nd ∧
  lookupName s.env "%niter" = some (.int 64 (BitVec.ofNat 64 (4 * c))) ∧
  (∃ e : BitVec 64, e.toNat < 10 ^ 7 ∧
    ((s.pre = some preSt ∧ lookupName s.env cellSt = some (.int 64 e)) ∨
     (s.pre = some preSk ∧ lookupName s.env cellSk = some (.int 64 e))))

/-! ### The position lemmas

Each reads the same way: at a test block, the accumulator its `phi` selects is
spent on the store when the cap allows and skipped otherwise, one control step
each; the successor position carries the store's `10 * e + d` or the carried word
unchanged.  The two in-edges of the test are the two disjuncts of the bundle, so
the four combinations are four chains of at most two steps. -/

/-- **The fourth digit's test to the latch.**  Two steps at most. -/
theorem t3AtC {calls : Calls} {p digA Nd u xt c : Nat} {i : BitVec 64} {s : State}
    (h : t3LadderAt p digA Nd u xt c i "for.inc98.i.i.2" "%add96.i.i.2"
      "if.then90.i.i.2" "%e.1.i.i.1" "for.inc98.i.i.1" s) :
    ∃ (e : State) (j : Nat), j ≤ 2 ∧
      t3LadderAt p digA Nd u xt c i "for.inc98.i.i.3" "%add96.i.i.3"
        "if.then90.i.i.3" "%e.1.i.i.2" "for.inc98.i.i.2" e ∧
      ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e := by
  obtain ⟨hpc, hframe, hi, hi63, hiNd, hn, eA, heA7, hedge⟩ := h
  have hpos : (i.signExtend 64).toNat < 2 ^ 63 := by
    rw [t3_signExtend_self_toNat]; exact hi63
  have hedge2 := hedge
  by_cases hbit : evalICmp .slt eA t3Cap = (1 : BitVec 1)
  · -- the digit is stored: the test's step, then the store's
    have heA6 : eA.toNat < 10 ^ 6 := by
      have h' := (slt_one_iff (by omega) t3Cap_lt_two).mp hbit
      simpa only [t3Cap_toNat] using h'
    obtain ⟨d, hreadp, hd48, hd57⟩ := hframe.stage (3 + i.toNat) (by omega)
    have hread : readBytes s.mem ((p + 3) + (i.signExtend 64).toNat) 1 = some [d] := by
      rw [t3_signExtend_self_toNat,
        show (p + 3) + i.toNat = p + (3 + i.toNat) from by omega]
      exact hreadp
    have hstep1 : step calls numFastBody s =
        .jump (stateAt (t3T3 s.env eA)
          { s with pc := "if.then90.i.i.3", pre := some "for.inc98.i.i.2" }) := by
      rcases hedge with ⟨hpre, hcell⟩ | ⟨hpre, hcell⟩
      · simpa only [t3T3, t3_stateAt_env_self] using
          t3_inc98_step_store_2 (calls := calls) (env := s.env) (s := s) (e := eA)
            hpc hpre hcell hbit
      · have hop : evalOperand (stateAt s.env s) (.reg "%e.1.i.i.1")
            = some (.int 64 eA) :=
          evalOperand_reg_of s.env s "%e.1.i.i.1" (.int 64 eA) hcell
        simpa only [t3T3, t3_stateAt_env_self] using
          t3_test_step_store calls "for.inc98.i.i.2" "%e.1.i.i.2" "%cmp88.i.i.3"
            [("if.then90.i.i.2", (Operand.reg "%add96.i.i.2")),
             ("for.inc98.i.i.1", (Operand.reg "%e.1.i.i.1"))]
            "if.then90.i.i.3" "for.inc98.i.i.3" t3_inc98_find_2 hpc hpre (by decide)
            hop hbit
    have hstep2 : step calls numFastBody
        (stateAt (t3T3 s.env eA)
          { s with pc := "if.then90.i.i.3", pre := some "for.inc98.i.i.2" }) =
        .jump (stateAt (t3S4 (t3T3 s.env eA) eA d
            ((p + 3) + (i.signExtend 64).toNat))
          { s with pc := "for.inc98.i.i.3", pre := some "if.then90.i.i.3" }) := by
      simpa only [t3S4] using
        t3_if_then90_step_3 (calls := calls) (env := t3T3 s.env eA)
          (s := { s with pc := "if.then90.i.i.3", pre := some "for.inc98.i.i.2" })
          (e := eA) (b := p + 3) (idx := i) (d := d)
          rfl (t3T3_e s.env eA) (by rw [t3T3_other]; exact hframe.gep3)
          (by rw [t3T3_other]; exact hi) hpos hread
    obtain ⟨he7', -⟩ := t3_store_next_lt heA6 hd48 hd57
    refine ⟨stateAt (t3S4 (t3T3 s.env eA) eA d
        ((p + 3) + (i.signExtend 64).toNat))
        { s with pc := "for.inc98.i.i.3", pre := some "if.then90.i.i.3" },
      2, by decide, ?_, ?_⟩
    · simp only [stateAt]
      refine ⟨rfl, t3MainFrame_S4 (t3MainFrame_T3 hframe), ?_, hi63, hiNd, ?_,
        t3StoreNext eA d, he7', Or.inl ⟨rfl, ?_⟩⟩
      · rw [t3S4_other, t3T3_other]; exact hi
      · rw [t3S4_other, t3T3_other]; exact hn
      · exact t3S4_add96 (t3T3 s.env eA) eA d _
    · intro k
      rw [show 2 + k = (k + 1) + 1 from by omega]
      simp only [runFuel, hstep1, hstep2]
  · -- the digit is skipped: the test's step alone
    have hbit0 : evalICmp .slt eA t3Cap = (0 : BitVec 1) := by
      rcases bitVec1_eq_zero_or_one (evalICmp .slt eA t3Cap) with h' | h'
      · exact h'
      · exact absurd h' hbit
    have hstep1 : step calls numFastBody s =
        .jump (stateAt (t3T3 s.env eA)
          { s with pc := "for.inc98.i.i.3", pre := some "for.inc98.i.i.2" }) := by
      rcases hedge2 with ⟨hpre, hcell⟩ | ⟨hpre, hcell⟩
      · have hop : evalOperand (stateAt s.env s) (.reg "%add96.i.i.2")
            = some (.int 64 eA) :=
          evalOperand_reg_of s.env s "%add96.i.i.2" (.int 64 eA) hcell
        simpa only [t3T3, t3_stateAt_env_self] using
          t3_test_step_skip calls "for.inc98.i.i.2" "%e.1.i.i.2" "%cmp88.i.i.3"
            [("if.then90.i.i.2", (Operand.reg "%add96.i.i.2")),
             ("for.inc98.i.i.1", (Operand.reg "%e.1.i.i.1"))]
            "if.then90.i.i.3" "for.inc98.i.i.3" t3_inc98_find_2 hpc hpre (by decide)
            hop hbit0
      · simpa only [t3T3, t3_stateAt_env_self] using
          t3_inc98_step_skip_2 (calls := calls) (env := s.env) (s := s) (e := eA)
            hpc hpre hcell hbit0
    refine ⟨stateAt (t3T3 s.env eA)
        { s with pc := "for.inc98.i.i.3", pre := some "for.inc98.i.i.2" },
      1, by decide, ?_, ?_⟩
    · simp only [stateAt]
      refine ⟨rfl, t3MainFrame_T3 hframe, ?_, hi63, hiNd, ?_, eA, heA7,
        Or.inr ⟨rfl, t3T3_e s.env eA⟩⟩
      · rw [t3T3_other]; exact hi
      · rw [t3T3_other]; exact hn
    · intro k
      rw [show 1 + k = k + 1 from by omega]
      simp only [runFuel, hstep1]

/-- **The third digit's test to the fourth.**  Two steps at most. -/
theorem t3AtB {calls : Calls} {p digA Nd u xt c : Nat} {i : BitVec 64} {s : State}
    (h : t3LadderAt p digA Nd u xt c i "for.inc98.i.i.1" "%add96.i.i.1"
      "if.then90.i.i.1" "%e.1.i.i" "for.inc98.i.i" s) :
    ∃ (e : State) (j : Nat), j ≤ 2 ∧
      t3LadderAt p digA Nd u xt c i "for.inc98.i.i.2" "%add96.i.i.2"
        "if.then90.i.i.2" "%e.1.i.i.1" "for.inc98.i.i.1" e ∧
      ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e := by
  obtain ⟨hpc, hframe, hi, hi63, hiNd, hn, eA, heA7, hedge⟩ := h
  have hpos : (i.signExtend 64).toNat < 2 ^ 63 := by
    rw [t3_signExtend_self_toNat]; exact hi63
  have hedge2 := hedge
  by_cases hbit : evalICmp .slt eA t3Cap = (1 : BitVec 1)
  · have heA6 : eA.toNat < 10 ^ 6 := by
      have h' := (slt_one_iff (by omega) t3Cap_lt_two).mp hbit
      simpa only [t3Cap_toNat] using h'
    obtain ⟨d, hreadp, hd48, hd57⟩ := hframe.stage (2 + i.toNat) (by omega)
    have hread : readBytes s.mem ((p + 2) + (i.signExtend 64).toNat) 1 = some [d] := by
      rw [t3_signExtend_self_toNat,
        show (p + 2) + i.toNat = p + (2 + i.toNat) from by omega]
      exact hreadp
    have hstep1 : step calls numFastBody s =
        .jump (stateAt (t3T2 s.env eA)
          { s with pc := "if.then90.i.i.2", pre := some "for.inc98.i.i.1" }) := by
      rcases hedge with ⟨hpre, hcell⟩ | ⟨hpre, hcell⟩
      · simpa only [t3T2, t3_stateAt_env_self] using
          t3_inc98_step_store_1 (calls := calls) (env := s.env) (s := s) (e := eA)
            hpc hpre hcell hbit
      · have hop : evalOperand (stateAt s.env s) (.reg "%e.1.i.i")
            = some (.int 64 eA) :=
          evalOperand_reg_of s.env s "%e.1.i.i" (.int 64 eA) hcell
        simpa only [t3T2, t3_stateAt_env_self] using
          t3_test_step_store calls "for.inc98.i.i.1" "%e.1.i.i.1" "%cmp88.i.i.2"
            [("if.then90.i.i.1", (Operand.reg "%add96.i.i.1")),
             ("for.inc98.i.i", (Operand.reg "%e.1.i.i"))]
            "if.then90.i.i.2" "for.inc98.i.i.2" t3_inc98_find_1 hpc hpre (by decide)
            hop hbit
    have hstep2 : step calls numFastBody
        (stateAt (t3T2 s.env eA)
          { s with pc := "if.then90.i.i.2", pre := some "for.inc98.i.i.1" }) =
        .jump (stateAt (t3S3 (t3T2 s.env eA) eA d
            ((p + 2) + (i.signExtend 64).toNat))
          { s with pc := "for.inc98.i.i.2", pre := some "if.then90.i.i.2" }) := by
      simpa only [t3S3] using
        t3_if_then90_step_2 (calls := calls) (env := t3T2 s.env eA)
          (s := { s with pc := "if.then90.i.i.2", pre := some "for.inc98.i.i.1" })
          (e := eA) (b := p + 2) (idx := i) (d := d)
          rfl (t3T2_e s.env eA) (by rw [t3T2_other]; exact hframe.gep2)
          (by rw [t3T2_other]; exact hi) hpos hread
    obtain ⟨he7', -⟩ := t3_store_next_lt heA6 hd48 hd57
    refine ⟨stateAt (t3S3 (t3T2 s.env eA) eA d
        ((p + 2) + (i.signExtend 64).toNat))
        { s with pc := "for.inc98.i.i.2", pre := some "if.then90.i.i.2" },
      2, by decide, ?_, ?_⟩
    · simp only [stateAt]
      refine ⟨rfl, t3MainFrame_S3 (t3MainFrame_T2 hframe), ?_, hi63, hiNd, ?_,
        t3StoreNext eA d, he7', Or.inl ⟨rfl, ?_⟩⟩
      · rw [t3S3_other, t3T2_other]; exact hi
      · rw [t3S3_other, t3T2_other]; exact hn
      · exact t3S3_add96 (t3T2 s.env eA) eA d _
    · intro k
      rw [show 2 + k = (k + 1) + 1 from by omega]
      simp only [runFuel, hstep1, hstep2]
  · have hbit0 : evalICmp .slt eA t3Cap = (0 : BitVec 1) := by
      rcases bitVec1_eq_zero_or_one (evalICmp .slt eA t3Cap) with h' | h'
      · exact h'
      · exact absurd h' hbit
    have hstep1 : step calls numFastBody s =
        .jump (stateAt (t3T2 s.env eA)
          { s with pc := "for.inc98.i.i.2", pre := some "for.inc98.i.i.1" }) := by
      rcases hedge2 with ⟨hpre, hcell⟩ | ⟨hpre, hcell⟩
      · have hop : evalOperand (stateAt s.env s) (.reg "%add96.i.i.1")
            = some (.int 64 eA) :=
          evalOperand_reg_of s.env s "%add96.i.i.1" (.int 64 eA) hcell
        simpa only [t3T2, t3_stateAt_env_self] using
          t3_test_step_skip calls "for.inc98.i.i.1" "%e.1.i.i.1" "%cmp88.i.i.2"
            [("if.then90.i.i.1", (Operand.reg "%add96.i.i.1")),
             ("for.inc98.i.i", (Operand.reg "%e.1.i.i"))]
            "if.then90.i.i.2" "for.inc98.i.i.2" t3_inc98_find_1 hpc hpre (by decide)
            hop hbit0
      · simpa only [t3T2, t3_stateAt_env_self] using
          t3_inc98_step_skip_1 (calls := calls) (env := s.env) (s := s) (e := eA)
            hpc hpre hcell hbit0
    refine ⟨stateAt (t3T2 s.env eA)
        { s with pc := "for.inc98.i.i.2", pre := some "for.inc98.i.i.1" },
      1, by decide, ?_, ?_⟩
    · simp only [stateAt]
      refine ⟨rfl, t3MainFrame_T2 hframe, ?_, hi63, hiNd, ?_, eA, heA7,
        Or.inr ⟨rfl, t3T2_e s.env eA⟩⟩
      · rw [t3T2_other]; exact hi
      · rw [t3T2_other]; exact hn
    · intro k
      rw [show 1 + k = k + 1 from by omega]
      simp only [runFuel, hstep1]

/-- **The second digit's test to the third.**  Two steps at most. -/
theorem t3AtA {calls : Calls} {p digA Nd u xt c : Nat} {i : BitVec 64} {s : State}
    (h : t3LadderAt p digA Nd u xt c i "for.inc98.i.i" "%add96.i.i"
      "if.then90.i.i" "%e.0734.i.i" "for.body87.i.i" s) :
    ∃ (e : State) (j : Nat), j ≤ 2 ∧
      t3LadderAt p digA Nd u xt c i "for.inc98.i.i.1" "%add96.i.i.1"
        "if.then90.i.i.1" "%e.1.i.i" "for.inc98.i.i" e ∧
      ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e := by
  obtain ⟨hpc, hframe, hi, hi63, hiNd, hn, eA, heA7, hedge⟩ := h
  have hpos : (i.signExtend 64).toNat < 2 ^ 63 := by
    rw [t3_signExtend_self_toNat]; exact hi63
  have hedge2 := hedge
  by_cases hbit : evalICmp .slt eA t3Cap = (1 : BitVec 1)
  · have heA6 : eA.toNat < 10 ^ 6 := by
      have h' := (slt_one_iff (by omega) t3Cap_lt_two).mp hbit
      simpa only [t3Cap_toNat] using h'
    obtain ⟨d, hreadp, hd48, hd57⟩ := hframe.stage (1 + i.toNat) (by omega)
    have hread : readBytes s.mem ((p + 1) + (i.signExtend 64).toNat) 1 = some [d] := by
      rw [t3_signExtend_self_toNat,
        show (p + 1) + i.toNat = p + (1 + i.toNat) from by omega]
      exact hreadp
    have hstep1 : step calls numFastBody s =
        .jump (stateAt (t3T1 s.env eA)
          { s with pc := "if.then90.i.i.1", pre := some "for.inc98.i.i" }) := by
      rcases hedge with ⟨hpre, hcell⟩ | ⟨hpre, hcell⟩
      · simpa only [t3T1, t3_stateAt_env_self] using
          t3_inc98_step_store (calls := calls) (env := s.env) (s := s) (e := eA)
            hpc hpre hcell hbit
      · have hop : evalOperand (stateAt s.env s) (.reg "%e.0734.i.i")
            = some (.int 64 eA) :=
          evalOperand_reg_of s.env s "%e.0734.i.i" (.int 64 eA) hcell
        simpa only [t3T1, t3_stateAt_env_self] using
          t3_test_step_store calls "for.inc98.i.i" "%e.1.i.i" "%cmp88.i.i.1"
            [("if.then90.i.i", (Operand.reg "%add96.i.i")),
             ("for.body87.i.i", (Operand.reg "%e.0734.i.i"))]
            "if.then90.i.i.1" "for.inc98.i.i.1" t3_inc98_find hpc hpre (by decide)
            hop hbit
    have hstep2 : step calls numFastBody
        (stateAt (t3T1 s.env eA)
          { s with pc := "if.then90.i.i.1", pre := some "for.inc98.i.i" }) =
        .jump (stateAt (t3S2 (t3T1 s.env eA) eA d
            ((p + 1) + (i.signExtend 64).toNat))
          { s with pc := "for.inc98.i.i.1", pre := some "if.then90.i.i.1" }) := by
      simpa only [t3S2] using
        t3_if_then90_step_1 (calls := calls) (env := t3T1 s.env eA)
          (s := { s with pc := "if.then90.i.i.1", pre := some "for.inc98.i.i" })
          (e := eA) (b := p + 1) (idx := i) (d := d)
          rfl (t3T1_e s.env eA) (by rw [t3T1_other]; exact hframe.gep1)
          (by rw [t3T1_other]; exact hi) hpos hread
    obtain ⟨he7', -⟩ := t3_store_next_lt heA6 hd48 hd57
    refine ⟨stateAt (t3S2 (t3T1 s.env eA) eA d
        ((p + 1) + (i.signExtend 64).toNat))
        { s with pc := "for.inc98.i.i.1", pre := some "if.then90.i.i.1" },
      2, by decide, ?_, ?_⟩
    · simp only [stateAt]
      refine ⟨rfl, t3MainFrame_S2 (t3MainFrame_T1 hframe), ?_, hi63, hiNd, ?_,
        t3StoreNext eA d, he7', Or.inl ⟨rfl, ?_⟩⟩
      · rw [t3S2_other, t3T1_other]; exact hi
      · rw [t3S2_other, t3T1_other]; exact hn
      · exact t3S2_add96 (t3T1 s.env eA) eA d _
    · intro k
      rw [show 2 + k = (k + 1) + 1 from by omega]
      simp only [runFuel, hstep1, hstep2]
  · have hbit0 : evalICmp .slt eA t3Cap = (0 : BitVec 1) := by
      rcases bitVec1_eq_zero_or_one (evalICmp .slt eA t3Cap) with h' | h'
      · exact h'
      · exact absurd h' hbit
    have hstep1 : step calls numFastBody s =
        .jump (stateAt (t3T1 s.env eA)
          { s with pc := "for.inc98.i.i.1", pre := some "for.inc98.i.i" }) := by
      rcases hedge2 with ⟨hpre, hcell⟩ | ⟨hpre, hcell⟩
      · have hop : evalOperand (stateAt s.env s) (.reg "%add96.i.i")
            = some (.int 64 eA) :=
          evalOperand_reg_of s.env s "%add96.i.i" (.int 64 eA) hcell
        simpa only [t3T1, t3_stateAt_env_self] using
          t3_test_step_skip calls "for.inc98.i.i" "%e.1.i.i" "%cmp88.i.i.1"
            [("if.then90.i.i", (Operand.reg "%add96.i.i")),
             ("for.body87.i.i", (Operand.reg "%e.0734.i.i"))]
            "if.then90.i.i.1" "for.inc98.i.i.1" t3_inc98_find hpc hpre (by decide)
            hop hbit0
      · simpa only [t3T1, t3_stateAt_env_self] using
          t3_inc98_step_skip (calls := calls) (env := s.env) (s := s) (e := eA)
            hpc hpre hcell hbit0
    refine ⟨stateAt (t3T1 s.env eA)
        { s with pc := "for.inc98.i.i.1", pre := some "for.inc98.i.i" },
      1, by decide, ?_, ?_⟩
    · simp only [stateAt]
      refine ⟨rfl, t3MainFrame_T1 hframe, ?_, hi63, hiNd, ?_, eA, heA7,
        Or.inr ⟨rfl, t3T1_e s.env eA⟩⟩
      · rw [t3T1_other]; exact hi
      · rw [t3T1_other]; exact hn
    · intro k
      rw [show 1 + k = k + 1 from by omega]
      simp only [runFuel, hstep1]

/-- **The head's test to the first repeated test.**  The preheader's edge carries
the dispatch's index and two zeros, so its store always runs; the latch's edge
carries the three cells, and the accumulator's test decides.  Two steps at
most. -/
theorem t3HeadVisit {calls : Calls} {p digA Nd nv u xt r c : Nat} {s : State}
    (h : t3MainInv p digA Nd nv u xt r s c) :
    ∃ (e : State) (j : Nat) (i : BitVec 64), j ≤ 2 ∧
      i.toNat + 4 * r + xt = Nd ∧
      t3LadderAt p digA Nd u xt c i "for.inc98.i.i" "%add96.i.i" "if.then90.i.i"
        "%e.0734.i.i" "for.body87.i.i" e ∧
      ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e := by
  obtain ⟨hpc, hframe, ⟨i, e0, hi63, he07, hile, hedge⟩, hcr, hr1, hxt3⟩ := h
  have hiNd : i.toNat + 4 ≤ Nd := by omega
  have hiN : i.toNat < Nd := by omega
  have hpos : (i.signExtend 64).toNat < 2 ^ 63 := by
    rw [t3_signExtend_self_toNat]; exact hi63
  have hread : ∀ d : UInt8, readBytes s.mem (p + (i.signExtend 64).toNat) 1 = some [d] →
      readBytes s.mem (p + (i.signExtend 64).toNat) 1 = some [d] := fun _ hh => hh
  rcases hedge with ⟨hpre, hi2, hc0⟩ | ⟨hpre, hinc99, he13, hn3⟩
  · -- the preheader's edge: the accumulator is zero, so the store always runs
    subst hc0
    have hbit : evalICmp .slt (0 : BitVec 64) t3Cap = (1 : BitVec 1) := by decide
    obtain ⟨d, hreadp, hd48, hd57⟩ := hframe.stage i.toNat hiN
    have hr : readBytes s.mem (p + (i.signExtend 64).toNat) 1 = some [d] := by
      rw [t3_signExtend_self_toNat]; exact hreadp
    have hstep1 : step calls numFastBody s =
        .jump (stateAt (t3HeadEnv s.env i 0 0)
          { s with pc := "if.then90.i.i", pre := some "for.body87.i.i" }) := by
      simpa only [t3_stateAt_env_self] using
        t3_head_step_entry_store (calls := calls) (env := s.env) (s := s) (i := i)
          hpc hpre hi2 hbit
    have hstep2 : step calls numFastBody
        (stateAt (t3HeadEnv s.env i 0 0)
          { s with pc := "if.then90.i.i", pre := some "for.body87.i.i" }) =
        .jump (stateAt (t3S1 (t3HeadEnv s.env i 0 0) 0 d
            (p + (i.signExtend 64).toNat))
          { s with pc := "for.inc98.i.i", pre := some "if.then90.i.i" }) := by
      simpa only [t3S1] using
        t3_if_then90_step (calls := calls) (env := t3HeadEnv s.env i 0 0)
          (s := { s with pc := "if.then90.i.i", pre := some "for.body87.i.i" })
          (e := 0) (b := p) (idx := i) (d := d)
          rfl (t3HeadEnv_e s.env i 0 0) (by rw [t3HeadEnv_other]; exact hframe.p)
          (t3HeadEnv_i s.env i 0 0) hpos hr
    obtain ⟨he7', -⟩ := t3_store_next_lt (e := (0 : BitVec 64)) (by decide) hd48 hd57
    refine ⟨stateAt (t3S1 (t3HeadEnv s.env i 0 0) 0 d
        (p + (i.signExtend 64).toNat))
        { s with pc := "for.inc98.i.i", pre := some "if.then90.i.i" },
      2, i, by decide, hile, ?_, ?_⟩
    · simp only [stateAt]
      refine ⟨rfl, t3MainFrame_S1 (t3MainFrame_head hframe), ?_, hi63, hiNd, ?_,
        t3StoreNext 0 d, he7', Or.inl ⟨rfl, ?_⟩⟩
      · rw [t3S1_other]; exact t3HeadEnv_i s.env i 0 0
      · rw [t3S1_other,
          show BitVec.ofNat 64 (4 * 0) = (0 : BitVec 64) from by decide]
        exact t3HeadEnv_niter s.env i 0 0
      · exact t3S1_add96 (t3HeadEnv s.env i 0 0) 0 d _
    · intro k
      rw [show 2 + k = (k + 1) + 1 from by omega]
      simp only [runFuel, hstep1, hstep2]
  · -- the latch's edge: the accumulator's test decides
    by_cases hbit : evalICmp .slt e0 t3Cap = (1 : BitVec 1)
    · have he06 : e0.toNat < 10 ^ 6 := by
        have h' := (slt_one_iff (by omega) t3Cap_lt_two).mp hbit
        simpa only [t3Cap_toNat] using h'
      obtain ⟨d, hreadp, hd48, hd57⟩ := hframe.stage i.toNat hiN
      have hr : readBytes s.mem (p + (i.signExtend 64).toNat) 1 = some [d] := by
        rw [t3_signExtend_self_toNat]; exact hreadp
      have hstep1 : step calls numFastBody s =
          .jump (stateAt
            (t3HeadEnv s.env i e0 (BitVec.ofNat 64 (4 * c)))
            { s with pc := "if.then90.i.i", pre := some "for.body87.i.i" }) := by
        simpa only [t3_stateAt_env_self] using
          t3_head_step_back_store (calls := calls) (env := s.env) (s := s) (i := i)
            (e := e0) (n := BitVec.ofNat 64 (4 * c)) hpc hpre hinc99 he13 hn3 hbit
      have hstep2 : step calls numFastBody
          (stateAt (t3HeadEnv s.env i e0 (BitVec.ofNat 64 (4 * c)))
            { s with pc := "if.then90.i.i", pre := some "for.body87.i.i" }) =
          .jump (stateAt
            (t3S1 (t3HeadEnv s.env i e0 (BitVec.ofNat 64 (4 * c))) e0 d
              (p + (i.signExtend 64).toNat))
            { s with pc := "for.inc98.i.i", pre := some "if.then90.i.i" }) := by
        simpa only [t3S1] using
          t3_if_then90_step (calls := calls)
            (env := t3HeadEnv s.env i e0 (BitVec.ofNat 64 (4 * c)))
            (s := { s with pc := "if.then90.i.i", pre := some "for.body87.i.i" })
            (e := e0) (b := p) (idx := i) (d := d)
            rfl (t3HeadEnv_e s.env i e0 _) (by rw [t3HeadEnv_other]; exact hframe.p)
            (t3HeadEnv_i s.env i e0 _) hpos hr
      obtain ⟨he7', -⟩ := t3_store_next_lt he06 hd48 hd57
      refine ⟨stateAt (t3S1 (t3HeadEnv s.env i e0 (BitVec.ofNat 64 (4 * c))) e0 d
          (p + (i.signExtend 64).toNat))
          { s with pc := "for.inc98.i.i", pre := some "if.then90.i.i" },
        2, i, by decide, hile, ?_, ?_⟩
      · simp only [stateAt]
        refine ⟨rfl, t3MainFrame_S1 (t3MainFrame_head hframe), ?_, hi63, hiNd, ?_,
          t3StoreNext e0 d, he7', Or.inl ⟨rfl, ?_⟩⟩
        · rw [t3S1_other]; exact t3HeadEnv_i s.env i e0 _
        · rw [t3S1_other]; exact t3HeadEnv_niter s.env i e0 _
        · exact t3S1_add96 (t3HeadEnv s.env i e0 _) e0 d _
      · intro k
        rw [show 2 + k = (k + 1) + 1 from by omega]
        simp only [runFuel, hstep1, hstep2]
    · have hbit0 : evalICmp .slt e0 t3Cap = (0 : BitVec 1) := by
        rcases bitVec1_eq_zero_or_one (evalICmp .slt e0 t3Cap) with h' | h'
        · exact h'
        · exact absurd h' hbit
      have hstep1 : step calls numFastBody s =
          .jump (stateAt
            (t3HeadEnv s.env i e0 (BitVec.ofNat 64 (4 * c)))
            { s with pc := "for.inc98.i.i", pre := some "for.body87.i.i" }) := by
        simpa only [t3_stateAt_env_self] using
          t3_head_step_back_skip (calls := calls) (env := s.env) (s := s) (i := i)
            (e := e0) (n := BitVec.ofNat 64 (4 * c)) hpc hpre hinc99 he13 hn3 hbit0
      refine ⟨stateAt (t3HeadEnv s.env i e0 (BitVec.ofNat 64 (4 * c)))
          { s with pc := "for.inc98.i.i", pre := some "for.body87.i.i" },
        1, i, by decide, hile, ?_, ?_⟩
      · simp only [stateAt]
        refine ⟨rfl, t3MainFrame_head hframe, ?_, hi63, hiNd, ?_, e0, he07,
          Or.inr ⟨rfl, ?_⟩⟩
        · exact t3HeadEnv_i s.env i e0 _
        · exact t3HeadEnv_niter s.env i e0 _
        · exact t3HeadEnv_e s.env i e0 _
      · intro k
        rw [show 1 + k = k + 1 from by omega]
        simp only [runFuel, hstep1]

/-- Two `runFuel` prefixes at a shared state append. -/
theorem t3_runFuel_append {calls : Calls} {f : Function} {s e e' : State} {j j' : Nat}
    (h1 : ∀ k, runFuel calls (j + k) f s = runFuel calls k f e)
    (h2 : ∀ k, runFuel calls (j' + k) f e = runFuel calls k f e') :
    ∀ k, runFuel calls (j + j' + k) f s = runFuel calls k f e' := by
  intro k
  rw [show j + j' + k = j + (j' + k) from by omega, h1 (j' + k), h2 k]

/-- **One visit of the unrolled nest.**  From the invariant's head state, the
head's test, the three repeated tests with their stores, and nothing else: the
run reaches the latch's entry within eight control steps, carrying the frame, the
index, the counter and the accumulator the latch reads.  The ninth step is the
latch's, and it is the arms' to spend. -/
theorem t3Visit {calls : Calls} {p digA Nd nv u xt r c : Nat} {s : State}
    (h : t3MainInv p digA Nd nv u xt r s c) :
    ∃ (e : State) (j : Nat) (i : BitVec 64), j ≤ 8 ∧
      i.toNat + 4 * r + xt = Nd ∧
      t3LadderAt p digA Nd u xt c i "for.inc98.i.i.3" "%add96.i.i.3"
        "if.then90.i.i.3" "%e.1.i.i.2" "for.inc98.i.i.2" e ∧
      ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e := by
  obtain ⟨e1, j1, i, hj1, hile, hb1, hrun1⟩ := t3HeadVisit (calls := calls) h
  obtain ⟨e2, j2, hj2, hb2, hrun2⟩ := t3AtA (calls := calls) hb1
  obtain ⟨e3, j3, hj3, hb3, hrun3⟩ := t3AtB (calls := calls) hb2
  obtain ⟨e4, j4, hj4, hb4, hrun4⟩ := t3AtC (calls := calls) hb3
  exact ⟨e4, j1 + j2 + j3 + j4, i, by omega, hile, hb4,
    t3_runFuel_append (t3_runFuel_append (t3_runFuel_append hrun1 hrun2) hrun3) hrun4⟩

/-- **The latch's exit step at either in-edge.**  The store's edge selects
`%add96.i.i.3` and the test's edge `%e.1.i.i.2`; both are the latch's accumulator
`phi`, so the step is one statement at the bundle's disjunction. -/
theorem t3_latch3_step_exit_pre {calls : Calls} {env : Env} {s : State}
    {e i n u : BitVec 64}
    (hpc : s.pc = "for.inc98.i.i.3")
    (hpre : (s.pre = some "if.then90.i.i.3" ∧
        lookupName env "%add96.i.i.3" = some (.int 64 e)) ∨
      (s.pre = some "for.inc98.i.i.2" ∧
        lookupName env "%e.1.i.i.2" = some (.int 64 e)))
    (hi : lookupName env "%i.3735.i.i" = some (.int 64 i))
    (hn : lookupName env "%niter" = some (.int 64 n))
    (hu : lookupName env "%unroll_iter" = some (.int 64 u))
    (hbit : evalICmp .eq (n + 0x4#64) u = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3LatchEnv env "%e.1.i.i.3" "%inc99.i.i.3" "%niter.next.3"
        "%niter.ncmp.3" e (i + 0x4#64) (n + 0x4#64) u)
        { s with pc := "for.end100.i.i.loopexit.unr-lcssa",
                 pre := some "for.inc98.i.i.3" }) := by
  rcases hpre with ⟨hpre, hcell⟩ | ⟨hpre, hcell⟩
  · exact t3_latch3_step_exit (calls := calls) (env := env) (s := s) (e := e)
      (i := i) (n := n) (u := u) hpc hpre hcell hi hn hu hbit
  · have hop : evalOperand (stateAt env s) (.reg "%e.1.i.i.2") = some (.int 64 e) :=
      evalOperand_reg_of env s "%e.1.i.i.2" (.int 64 e) hcell
    exact t3_latch_step_taken calls "for.inc98.i.i.3" "%e.1.i.i.3" "%i.3735.i.i"
      "%niter" "%unroll_iter" "%inc99.i.i.3" "%niter.next.3" "%niter.ncmp.3"
      [("if.then90.i.i.3", (Operand.reg "%add96.i.i.3")),
       ("for.inc98.i.i.2", (Operand.reg "%e.1.i.i.2"))]
      0x4#64 0x4#64 "for.end100.i.i.loopexit.unr-lcssa" "for.body87.i.i"
      t3_latch3_find hpc hpre (by decide) hop hi hn hu
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hbit

/-- **The latch's back step at either in-edge.** -/
theorem t3_latch3_step_back_pre {calls : Calls} {env : Env} {s : State}
    {e i n u : BitVec 64}
    (hpc : s.pc = "for.inc98.i.i.3")
    (hpre : (s.pre = some "if.then90.i.i.3" ∧
        lookupName env "%add96.i.i.3" = some (.int 64 e)) ∨
      (s.pre = some "for.inc98.i.i.2" ∧
        lookupName env "%e.1.i.i.2" = some (.int 64 e)))
    (hi : lookupName env "%i.3735.i.i" = some (.int 64 i))
    (hn : lookupName env "%niter" = some (.int 64 n))
    (hu : lookupName env "%unroll_iter" = some (.int 64 u))
    (hbit : evalICmp .eq (n + 0x4#64) u = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t3LatchEnv env "%e.1.i.i.3" "%inc99.i.i.3" "%niter.next.3"
        "%niter.ncmp.3" e (i + 0x4#64) (n + 0x4#64) u)
        { s with pc := "for.body87.i.i", pre := some "for.inc98.i.i.3" }) := by
  rcases hpre with ⟨hpre, hcell⟩ | ⟨hpre, hcell⟩
  · have hop : evalOperand (stateAt env s) (.reg "%add96.i.i.3") = some (.int 64 e) :=
      evalOperand_reg_of env s "%add96.i.i.3" (.int 64 e) hcell
    exact t3_latch_step_back calls "for.inc98.i.i.3" "%e.1.i.i.3" "%i.3735.i.i"
      "%niter" "%unroll_iter" "%inc99.i.i.3" "%niter.next.3" "%niter.ncmp.3"
      [("if.then90.i.i.3", (Operand.reg "%add96.i.i.3")),
       ("for.inc98.i.i.2", (Operand.reg "%e.1.i.i.2"))]
      0x4#64 0x4#64 "for.end100.i.i.loopexit.unr-lcssa" "for.body87.i.i"
      t3_latch3_find hpc hpre (by decide) hop hi hn hu
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hbit
  · exact t3_latch3_step_back (calls := calls) (env := env) (s := s) (e := e)
      (i := i) (n := n) (u := u) hpc hpre hcell hi hn hu hbit

/-! ### The two visits

`t3MainLoopOf` takes the nest's two visits as parameters.  `t3Visit` is the
nine-step body of either: the head's test, the three repeated tests with their
stores, and the latch is the ninth.  What remains for each arm is the latch's one
control step at the invariant's counter — its test reaches `%unroll_iter` exactly
when the budget is spent, and misses it otherwise — and the state it leaves.

The latch's counter is the *visit index*: the carried `%niter` is `4 * c` and the
step advances it by four, so at the bound `4 * (c + 1) = 4 * nv = u` and off the
bound `4 * (c + 1) < u < 4 * (c + 1) + 2 ^ 64`, the upper end because the
staging's slack bounds the distance to `2 ^ 63`. -/

/-- **The nest's exit visit.**  At the bound the latch's test holds, and the run
reaches `for.end100.i.i.loopexit.unr-lcssa` within nine control steps, leaving the
latch's cells, the frame and the residue. -/
theorem t3Main_step_exit {calls : Calls} {p digA Nd nv u xt : Nat} (hu : u = 4 * nv)
    (r : Nat) (s : State) (c : Nat)
    (h : t3MainInv p digA Nd nv u xt r s c) (hb : t3MainAtBound nv s c = true) :
    ∃ (e : State) (j : Nat), j ≤ 9 ∧ t3MainExit e ∧ t3MainExitWord p digA Nd xt e ∧
      ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e := by
  have hxt30 : xt ≤ 3 := t3MainInv.xt3 h
  have hcr0 : c + r = nv := t3MainInv.cr h
  have hr1 : 1 ≤ r := t3MainInv.rpos h
  have hbnd : nv ≤ c + 1 := t3MainAtBound_true hb
  have hnv : nv = c + 1 := by omega
  have hu4 : u = 4 * c + 4 := by rw [hu, hnv, t3_four_succ]
  obtain ⟨e1, j1, i, hj1, hile, hb1, hrun1⟩ := t3Visit (calls := calls) h
  obtain ⟨hpc1, hframe1, hi1, hi163, hi1Nd, hn1, eA, heA7, hedge1⟩ := hb1
  have h4r : 4 ≤ 4 * r := t3_four_le hr1
  have hle1 : i.toNat + 4 ≤ i.toNat + 4 * r := Nat.add_le_add_left h4r _
  have hle2 : i.toNat + 4 * r ≤ i.toNat + 4 * r + xt := Nat.le_add_right _ _
  have hi4Nd : i.toNat + 4 ≤ Nd := by rw [← hile]; exact le_trans hle1 hle2
  have hu4' : i.toNat + 4 + xt ≤ Nd := by
    rw [← hile]; exact Nat.add_le_add_right hle1 xt
  have hi63' : i.toNat + 4 < 2 ^ 63 := lt_of_le_of_lt hi4Nd hframe1.nd
  have hi4 : i.toNat + 4 < 2 ^ 64 := lt_trans hi63' (by decide)
  have hbit : evalICmp .eq (BitVec.ofNat 64 (4 * c) + 0x4#64) (BitVec.ofNat 64 u)
      = (1 : BitVec 1) := t3_icmp_eq_one (by rw [t3_ofNat_four, hu4])
  have hstep : step calls numFastBody e1 =
      .jump (stateAt (t3Lat e1.env eA (i + 0x4#64)
          (BitVec.ofNat 64 (4 * c) + 0x4#64) (BitVec.ofNat 64 u))
        { e1 with pc := "for.end100.i.i.loopexit.unr-lcssa",
                  pre := some "for.inc98.i.i.3" }) := by
    have hs := t3_latch3_step_exit_pre (calls := calls) (env := e1.env) (s := e1)
      (e := eA) (i := i) (n := BitVec.ofNat 64 (4 * c)) (u := BitVec.ofNat 64 u)
      hpc1 hedge1 hi1 hn1 hframe1.iter hbit
    simpa only [t3Lat, t3_stateAt_env_self] using hs
  refine ⟨stateAt (t3Lat e1.env eA (i + 0x4#64)
      (BitVec.ofNat 64 (4 * c) + 0x4#64) (BitVec.ofNat 64 u))
      { e1 with pc := "for.end100.i.i.loopexit.unr-lcssa",
                pre := some "for.inc98.i.i.3" },
    j1 + 1, by omega, rfl, ?_, ?_⟩
  · simp only [stateAt]
    refine ⟨rfl, ?_, ?_, ?_, ?_, hframe1.nd, hxt30, i + 0x4#64, eA, ?_, ?_, ?_, heA7, ?_⟩
    · rw [t3Lat_other]; exact hframe1.p
    · rw [t3Lat_other]; exact hframe1.dig
    · rw [t3Lat_other]; exact hframe1.xt
    · intro k hk; exact hframe1.stage k hk
    · exact t3Lat_inc e1.env eA (i + 0x4#64) _ _
    · exact t3Lat_e1 e1.env eA (i + 0x4#64) _ _
    · rw [t3_add_four_toNat hi4]; exact hi63'
    · rw [t3_add_four_toNat hi4]; exact hu4'
  · intro k
    rw [show j1 + 1 + k = j1 + (k + 1) from by omega, hrun1 (k + 1)]
    simp only [runFuel, hstep]

/-- **The nest's loop visit.**  Below the bound the latch's test fails, and the run
re-enters `for.body87.i.i` within nine control steps carrying the index advanced
by four, the accumulator the visit computed, and the counter advanced by one
visit. -/
theorem t3Main_step_loop {calls : Calls} {p digA Nd nv u xt : Nat} (hu : u = 4 * nv)
    (r : Nat) (s : State) (c : Nat)
    (h : t3MainInv p digA Nd nv u xt (r + 1) s c) (hb : t3MainAtBound nv s c = false) :
    ∃ (e : State) (c' : Nat) (j : Nat), j ≤ 9 ∧ e.pc = "for.body87.i.i" ∧ c < c' ∧
      t3MainInv p digA Nd nv u xt r e c' ∧
      ∀ k, runFuel calls (j + k) numFastBody s = runFuel calls k numFastBody e := by
  have hxt30 : xt ≤ 3 := t3MainInv.xt3 h
  have hcr0 : c + (r + 1) = nv := t3MainInv.cr h
  have hnf : ¬ nv ≤ c + 1 := t3MainAtBound_false hb
  have hr1 : 1 ≤ r := by omega
  obtain ⟨e1, j1, i, hj1, hile, hb1, hrun1⟩ := t3Visit (calls := calls) h
  obtain ⟨hpc1, hframe1, hi1, hi163, hi1Nd, hn1, eA, heA7, hedge1⟩ := hb1
  have h4r : 4 ≤ 4 * r := t3_four_le hr1
  have hile' : i.toNat + (4 * r + 4) + xt = Nd := by
    rw [← t3_four_succ r]; exact hile
  have h4le : 4 ≤ 4 * r + 4 := le_trans h4r (Nat.le_add_right _ _)
  have hle1 : i.toNat + 4 ≤ i.toNat + (4 * r + 4) := Nat.add_le_add_left h4le _
  have hle2 : i.toNat + (4 * r + 4) ≤ i.toNat + (4 * r + 4) + xt := Nat.le_add_right _ _
  have hi4Nd : i.toNat + 4 ≤ Nd := by rw [← hile']; exact le_trans hle1 hle2
  have hi63' : i.toNat + 4 < 2 ^ 63 := lt_of_le_of_lt hi4Nd hframe1.nd
  have hi4 : i.toNat + 4 < 2 ^ 64 := lt_trans hi63' (by decide)
  have h4rNd : 4 * r + 4 ≤ Nd := by
    rw [← hile']; exact le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _)
  have h4r4 : 4 * r + 4 < 2 ^ 63 := lt_of_le_of_lt h4rNd hframe1.nd
  have h4rlt : 4 * r < 2 ^ 64 :=
    lt_trans (lt_trans (Nat.lt_add_of_pos_right (by decide : 0 < (4 : Nat))) h4r4) (by decide)
  have hu' : u = 4 * c + 4 * r + 4 := by
    rw [hu, ← hcr0, t3_four_add, t3_four_succ, Nat.add_assoc]
  have hbit0 : evalICmp .eq (BitVec.ofNat 64 (4 * c) + 0x4#64) (BitVec.ofNat 64 u)
      = (0 : BitVec 1) := by
    refine t3_icmp_eq_zero ?_
    rw [t3_ofNat_four, hu']
    exact t3_ofNat_ne (by omega) (by omega)
  have hstep : step calls numFastBody e1 =
      .jump (stateAt (t3Lat e1.env eA (i + 0x4#64)
          (BitVec.ofNat 64 (4 * c) + 0x4#64) (BitVec.ofNat 64 u))
        { e1 with pc := "for.body87.i.i", pre := some "for.inc98.i.i.3" }) := by
    have hs := t3_latch3_step_back_pre (calls := calls) (env := e1.env) (s := e1)
      (e := eA) (i := i) (n := BitVec.ofNat 64 (4 * c)) (u := BitVec.ofNat 64 u)
      hpc1 hedge1 hi1 hn1 hframe1.iter hbit0
    simpa only [t3Lat, t3_stateAt_env_self] using hs
  refine ⟨stateAt (t3Lat e1.env eA (i + 0x4#64)
      (BitVec.ofNat 64 (4 * c) + 0x4#64) (BitVec.ofNat 64 u))
      { e1 with pc := "for.body87.i.i", pre := some "for.inc98.i.i.3" },
    c + 1, j1 + 1, by omega, rfl, by omega, ?_, ?_⟩
  · simp only [stateAt]
    refine ⟨rfl, t3MainFrame_lat hframe1, ?_, ?_, by omega, hxt30⟩
    · refine ⟨i + 0x4#64, eA, ?_, heA7, ?_, ?_⟩
      · rw [t3_add_four_toNat hi4]; exact hi63'
      · rw [t3_add_four_toNat hi4]; omega
      · refine Or.inr ⟨rfl, ?_, ?_, ?_⟩
        · exact t3Lat_inc e1.env eA (i + 0x4#64) _ _
        · exact t3Lat_e1 e1.env eA (i + 0x4#64) _ _
        · rw [show BitVec.ofNat 64 (4 * (c + 1))
              = BitVec.ofNat 64 (4 * c) + 0x4#64 from by
              rw [t3_four_succ, t3_ofNat_four]]
          exact t3Lat_next e1.env eA (i + 0x4#64) _ _
    · omega
  · intro k
    rw [show j1 + 1 + k = j1 + (k + 1) from by omega, hrun1 (k + 1)]
    simp only [runFuel, hstep]

/-- **The unrolled nest's instance.**  The two visits discharge `t3MainLoopOf`'s
parameters, so the nest is an induction at the emitted blocks and needs nothing
else. -/
def t3MainLoop (calls : Calls) (p digA Nd nv u xt : Nat) (hu : u = 4 * nv) :
    BoundLoop calls numFastBody :=
  t3MainLoopOf calls p digA Nd nv u xt hu (t3Main_step_exit hu) (t3Main_step_loop hu)

/-- **The unrolled nest from its head, discharged.**  At the whole visit bound the
run reaches the nest's exit block within `(nv + 1) * 9` control steps with the exit
word, and the continuation is the caller's. -/
theorem t3MainLoop_run_at' (calls : Calls) (p digA Nd nv u xt : Nat) (hu : u = 4 * nv)
    (s : State) (c : Nat) (h : t3MainInv p digA Nd nv u xt nv s c) (k : Nat)
    {o : Outcome}
    (hcont : ∀ (e : State), t3MainExit e → t3MainExitWord p digA Nd xt e →
      runFuel calls k numFastBody e = some o) :
    runFuel calls ((nv + 1) * 9 + k) numFastBody s = some o :=
  t3MainLoop_run_at calls p digA Nd nv u xt hu (t3Main_step_exit hu)
    (t3Main_step_loop hu) s c h k hcont

/-! ### Axiom footprints -/

#print axioms t3MainInv.cr
#print axioms t3MainInv.rpos
#print axioms t3MainInv.xt3
#print axioms t3MainLoopOf
#print axioms t3MainLoop_run_at
#print axioms t3_ofNat_four
#print axioms t3_add_four_toNat
#print axioms t3_ofNat_ne
#print axioms t3Visit
#print axioms t3Main_step_exit
#print axioms t3Main_step_loop
#print axioms t3MainLoop
#print axioms t3MainLoop_run_at'

end NumFastTier3CopyUnroll

end LeanLLVM.Refinement
