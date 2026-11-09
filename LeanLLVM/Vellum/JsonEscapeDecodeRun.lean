/-
The decoder's loop instance, its staging exclusions, and its budget.

`@us_dec_x` walks the caller's position list, copying the bytes between positions
and decoding each escape.  `JsonEscapeDecodeTrace` states what each of the body's
blocks does at the fixture's own instruction list; `JsonEscapeDecodeLoop` states
the loop shape and derives the bound and the invariant's budget from
`DecodeInv` alone.  This module joins the two: the invariant the trace's block
facts consume, the exit arm composed from `cleanup32`'s own step, the staging
exclusions the record must carry, and the loop's fuel as a term of the arguments
and the caller's memory.

Three things are stated here and nothing else.

**The staging exclusions.**  Executed on the pinned body, four aliasing pairs the
record's `pre` admits make its `post` false: `tab` inside the destination extent
(the raw copy overwrites the table entry a later escape reads), `err` inside it
(the copy destroys the offset the `post` claims unchanged), `err` and `xj` the
same slot (the cursor store overwrites the offset), and `xj` inside the claimed
prefix (the cursor store overwrites decoded bytes, and no ordering saves it
because the store is the last write of every successful path).  `DecodeNoAlias`
states the four exclusions over the extents the body touches; the record's `pre`
is the surface that must carry them, and this module states them beside the arms
that need them rather than editing the record.

**The latch invariant.**  `DecodeLatch` is the loop's state at `cleanup32`: the
walk (`DecodeInv`), the predecessor edge, and the cells the iteration reads,
including the link between the walk's index `c` and the block's own `%add28`.  The
link is what `DecodeInv` alone lacks, and without it neither arm is a statement
about the body: the exit test reads `%cmp4`, not `c`.

**The loop's fuel.**  `decodeWalkFuel` is `(nps + 1) * decodeIterCost n`, a term of
the arguments (`nps`, `n`) with `decodeIterCost` bounding one iteration's control
steps, and `escapeExpandBudget` is the whole body's fuel in the same vocabulary.
`DecodeLatch` supplies `nps` from `n` and the list's length, so the fuel never
reads the run's own trip count.

The iteration arm is the one thing not proved here, and its residual is exactly
stated: the run from the latch back to the latch crosses the two copy loops and
the escape emitter, and the copy loops' own `BoundLoop` instances are the same
assembly one level down.  `decodeLatch_step_loop` records the obligation in the
shape the shape consumes, and the docstring above the residual names the exact
block at which the composition stops.
-/
import LeanLLVM.Vellum.JsonEscapeDecodeTrace
import LeanLLVM.Vellum.JsonEscapeDecodeLoop

set_option autoImplicit false
set_option maxRecDepth 16000

namespace LeanLLVM.Vellum

open LeanLLVM
open LeanLLVM.Vellum.JsonEscapeIR
open LeanLLVM.Vellum.JsonEscapeIntrinsics
open LeanLLVM.Vellum.JsonScanSpec

/-! ### The staging the record must exclude

Each clause is a caller promise about two regions the body touches: the extent the
run writes (`dst` through the decoded length plus the sixty-four bytes the stored
form reaches) against a region a later read or the `post` depends on.  They are
stated over extents rather than base pointers because an overlap of the bases
alone changes nothing; what matters is whether the written window reaches the
region.

The four rows behind them are executed on the pinned body, each at a staging the
record's `pre` admits as it stands, and each makes `post` false:

* `tab` inside the destination extent: the raw copy's sixty-four-byte write
  reaches `tab[0x22]`, and the following `\"` escape stores the raw-copy byte
  instead of the escape's own byte (body `34×'a'` then `\"`, positions `[34]`);
* `err` inside it: the copy writes the decoded bytes over the offset slot, so the
  `post`'s unchanged-offset clause is false (body `A\nB`, positions `[1]`);
* `err` and `xj` the same slot: the trailing cursor store leaves `1` where the
  `post` reads the caller's offset (`0`);
* `xj` inside the claimed prefix: the trailing cursor store overwrites the first
  eight decoded bytes, and no ordering saves this pair because that store is the
  last write of every successful path. -/
def DecodeNoAlias (n dst err xj tab : Nat) : Prop :=
  (tab + 256 ≤ dst ∨ dst + n + 64 ≤ tab) ∧
  (err + 8 ≤ dst ∨ dst + n + 64 ≤ err) ∧
  (err + 8 ≤ xj ∨ xj + 8 ≤ err) ∧
  (xj + 8 ≤ dst ∨ dst + n + 64 ≤ xj)

/-- The same predicate with the destination extent written as the body's own
`n + 64`, which is the number the record's `HasBytes` clause already names. -/
theorem decodeNoAlias_extent {n dst err xj tab : Nat} (h : DecodeNoAlias n dst err xj tab) :
    (tab + 256 ≤ dst ∨ dst + n + 64 ≤ tab) ∧
    (err + 8 ≤ dst ∨ dst + n + 64 ≤ err) ∧
    (err + 8 ≤ xj ∨ xj + 8 ≤ err) ∧
    (xj + 8 ≤ dst ∨ dst + n + 64 ≤ xj) := h

/-! ### The instruction vocabulary the arms read -/

/-- The comparison `%cmp25`: the advance is the surrogate pair's twelve. -/
def decodePairBit (adv : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (evalICmp .eq adv (BitVec.ofInt 64 12)).toNat

/-- The index `cleanup32` forms and tests: `%add28 = %inc11 + %conv27`.  This is
the block's own advance, and it is the value the loop's invariant carries. -/
def decodeNextIdx (inc11 adv : BitVec 64) : BitVec 64 := inc11 + decodePairBit adv

/-- The unsigned test reads as its `Nat` proposition at zero. -/
theorem evalICmp_ult_zero_iff {w : Nat} (x y : BitVec w) :
    evalICmp .ult x y = (0 : BitVec 1) ↔ ¬ x.toNat < y.toNat := by
  unfold evalICmp
  cases hb : BitVec.ult x y
  · have h : ¬ x.toNat < y.toNat := by
      intro hlt
      have htrue : BitVec.ult x y = true := (BitVec.ult_iff_toNat_lt).2 hlt
      rw [htrue] at hb
      exact Bool.noConfusion hb
    simp [h]
  · have h : x.toNat < y.toNat := by
      rw [← BitVec.ult_iff_toNat_lt]
      exact hb
    simp [h]

/-- The unsigned test reads as its `Nat` proposition at one. -/
theorem evalICmp_ult_one_iff {w : Nat} (x y : BitVec w) :
    evalICmp .ult x y = (1 : BitVec 1) ↔ x.toNat < y.toNat := by
  unfold evalICmp
  cases hb : BitVec.ult x y
  · have h : ¬ x.toNat < y.toNat := by
      intro hlt
      have htrue : BitVec.ult x y = true := (BitVec.ult_iff_toNat_lt).2 hlt
      rw [htrue] at hb
      exact Bool.noConfusion hb
    simp [h]
  · have h : x.toNat < y.toNat := by
      rw [← BitVec.ult_iff_toNat_lt]
      exact hb
    simp [h]

/-! ### The loop's fuel as a term of the arguments -/

/-- The control steps one position iteration may take: `cleanup32`'s step, the
position read, the straight-line part of the copy, the longest escape arm, and the
latch's own exit test.  The copy's vector loop and the escape emitter's two-byte
arm are each bounded by the caller's `n`: a copy moves sixty-four bytes a trip, and
a surrogate pair consumes twelve bytes, so `n / 64 + 2` bounds the copy and `16`
covers the longest emitter path (`if.end.i` through `if.end.i115`, `if.end3.i`,
`land.lhs.true22.i`, `if.then26.i`, `if.end32.i` and the two refusals). -/
def decodeIterCost (n : Nat) : Nat := 16 + (n / 64 + 2)

/-- The walk's fuel: one iteration's cost per unit of the position bound, plus the
exit iteration.  `nps` is the position list's length and `n` the body's, both
terms of the caller's arguments. -/
def decodeWalkFuel (nps n : Nat) : Nat := (nps + 1) * decodeIterCost n

/-- The expander's fuel, as a term of the argument list and the caller's memory.
The body is four straight-line or counted stages: `entry` and the pre-scan's
per-position steps, the position walk, the final copy's vector trips, and the
return.  The scan advances the position cursor once per iteration and its bound is
the list's length, so its contribution is `(nps + 1) * 3`; the final copy moves
sixty-four bytes a trip, so its contribution is `n / 64 + 3`.

The memory parameter is deliberately not read: every stage's trip count is decided
by the arguments under the record's `pre`, and a budget that read the memory would
have to agree with the record's own `readBytes` witnesses about bytes the run
itself writes.  It stays a parameter because `MemContract.budget` takes one. -/
def escapeExpandBudget (args : List Value) (_mem : Mem) : Nat :=
  match args with
  | [.ptr _, .int 64 nv, .ptr _, .ptr _, .ptr _, .ptr _, .int 64 npsv, .int 64 _, .ptr _] =>
      (npsv.toNat + 1) * 3 + decodeWalkFuel npsv.toNat nv.toNat + (nv.toNat / 64 + 3) + 4
  | _ => 0

/-- The budget's decomposition: the four stages of the body add up to it. -/
theorem escapeExpandBudget_decomp (n nps : Nat) (hn : n < 2 ^ 64) (hnps : nps < 2 ^ 64) :
    escapeExpandBudget [.ptr 0, .int 64 (BitVec.ofNat 64 n), .ptr 0, .ptr 0, .ptr 0,
      .ptr 0, .int 64 (BitVec.ofNat 64 nps), .int 64 0, .ptr 0] [] =
      (nps + 1) * 3 + decodeWalkFuel nps n + (n / 64 + 3) + 4 := by
  simp only [escapeExpandBudget, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt hnps]

/-- The position walk's contribution is inside the body's budget. -/
theorem decodeWalkFuel_le_budget {n nps : Nat} :
    decodeWalkFuel nps n ≤
      (nps + 1) * 3 + decodeWalkFuel nps n + (n / 64 + 3) + 4 := by
  omega

/-! ### The latch invariant

The loop's state at `cleanup32`, carrying the walk and the cells the next
iteration's blocks read.  The predecessor field fixes which edge the state arrived
on, because the block's two `phi`s take their operands from different registers on
the emitter edge and the simple-escape edge.  `%add28`'s value is `decodeNextIdx`
of the cells `cleanup32` itself will read, and that equality is the register link
`DecodeInv` does not carry. -/
def DecodeLatch (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (s : State) (c : Nat) : Prop :=
  ∃ (i : Nat) (out : List UInt8) (prev : String)
    (sub : BitVec 64) (inc11 : BitVec 64) (adv : BitVec 64) (j : BitVec 64)
    (nxp : BitVec 64)
    (paddr : Nat) (xpaddr : Nat) (tabaddr : Nat) (err : Nat) (xjaddr : Nat)
    (pos0v : BitVec 64) (addv : BitVec 64) (nv : BitVec 64),
    s.pc = "cleanup32" ∧
    DecodeInv body st s.mem dst nps i c out goal ∧
    c ≤ nps ∧
    s.pre = some prev ∧
    lookupName s.env "%sub" = some (.int 64 sub) ∧
    lookupName s.env "%inc11" = some (.int 64 inc11) ∧
    lookupName s.env "%nxp" = some (.int 64 nxp) ∧
    nxp.toNat = nps ∧
    ((prev = "if.end32.i" ∧ lookupName s.env "%add.i125" = some (.int 64 j) ∧
        lookupName s.env "%adv.1.i" = some (.int 64 adv))
      ∨ (prev = "if.then6.i" ∧ lookupName s.env "%add8.i" = some (.int 64 j) ∧
        adv = BitVec.ofInt 64 2)) ∧
    (decodeNextIdx inc11 adv).toNat = c ∧
    (adv + sub).toNat = i ∧
    j.toNat = out.length ∧
    lookupName s.env "%p" = some (.ptr paddr) ∧
    lookupName s.env "%dst" = some (.ptr dst) ∧
    lookupName s.env "%xp" = some (.ptr xpaddr) ∧
    lookupName s.env "%tab" = some (.ptr tabaddr) ∧
    lookupName s.env "%err" = some (.ptr err) ∧
    lookupName s.env "%xj" = some (.ptr xjaddr) ∧
    lookupName s.env "%pos0" = some (.int 64 pos0v) ∧
    lookupName s.env "%add" = some (.int 64 addv) ∧
    lookupName s.env "%n" = some (.int 64 nv)

/-- What the walk leaves at the exit: the invariant at the exit block, together
with the cells `while.end35`'s `phi`s take from `cleanup32`.  The continuation
reads `%j.3` as the decoded length, `%add24` as the byte cursor, and `%add28` as
the position index; the parameters are the caller's staging, carried so the final
copy's trace can name them. -/
def DecodeLatchExit (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (c : Nat) (s : State) : Prop :=
  ∃ (i : Nat) (out : List UInt8) (j : BitVec 64) (add24 : BitVec 64)
    (add28 : BitVec 64)
    (paddr : Nat) (xpaddr : Nat) (tabaddr : Nat) (err : Nat) (xjaddr : Nat)
    (pos0v : BitVec 64) (addv : BitVec 64) (nv : BitVec 64),
    s.pc = "while.end35" ∧
    DecodeInv body st s.mem dst nps i c out goal ∧
    lookupName s.env "%j.3" = some (.int 64 j) ∧
    j.toNat = out.length ∧
    lookupName s.env "%add24" = some (.int 64 add24) ∧
    add24.toNat = i ∧
    lookupName s.env "%add28" = some (.int 64 add28) ∧
    add28.toNat = c ∧
    lookupName s.env "%p" = some (.ptr paddr) ∧
    lookupName s.env "%dst" = some (.ptr dst) ∧
    lookupName s.env "%xp" = some (.ptr xpaddr) ∧
    lookupName s.env "%tab" = some (.ptr tabaddr) ∧
    lookupName s.env "%err" = some (.ptr err) ∧
    lookupName s.env "%xj" = some (.ptr xjaddr) ∧
    lookupName s.env "%pos0" = some (.int 64 pos0v) ∧
    lookupName s.env "%add" = some (.int 64 addv) ∧
    lookupName s.env "%n" = some (.int 64 nv)

/-! ### The exit arm

At the latch, `%cmp4 = icmp ult %add28, %nxp` is the whole exit test, and its
false arm is one control step.  The arm composes `udCleanup32_step_zero` at the
two edges the latch admits and carries the walk and the cells into the exit
predicate. -/

/-- `evalOperand` at a register the environment binds. -/
theorem evalOperand_reg_eq (env : Env) (s : State) (n : String) (v : Value)
    (h : lookupName env n = some v) : evalOperand (withEnv env s) (.reg n) = some v := by
  simp only [withEnv, evalOperand, h]

theorem latch_phi_operand_emitter :
    phiIncoming "if.end32.i" udCleanup32IncomingJ = some (.reg "%add.i125") := by
  decide

theorem latch_phi_operand_emitter_adv :
    phiIncoming "if.end32.i" udCleanup32IncomingAdv = some (.reg "%adv.1.i") := by
  decide

theorem latch_phi_operand_simple :
    phiIncoming "if.then6.i" udCleanup32IncomingJ = some (.reg "%add8.i") := by
  decide

theorem latch_phi_operand_simple_adv :
    phiIncoming "if.then6.i" udCleanup32IncomingAdv =
      some (.imm (.int 64 (BitVec.ofInt 64 2))) := by
  decide

/-- **The exit arm.**  From the latch with `%cmp4` false — which the invariant's
index link and `c ≤ nps` make equivalent to `nps ≤ c` — one control step reaches
`while.end35` and leaves the walk and the cells the exit block's `phi`s take from
the latch. -/
theorem decodeLatch_step_exit {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {s : State} {c : Nat} (h : DecodeLatch body st dst nps goal s c)
    (hat : decide (nps ≤ c) = true) :
    ∃ (e : State) (j : Nat), j ≤ 1 ∧ e.pc = "while.end35" ∧
      DecodeLatchExit body st dst nps goal c e ∧
      ∀ k, runFuel escapeCalls (j + k) usDecFunction s =
        runFuel escapeCalls k usDecFunction e := by
  obtain ⟨i, out, prev, sub, inc11, adv, j, nxp, paddr, xpaddr, tabaddr, err, xjaddr,
    pos0v, addv, nv, hpc, hwalk, hcle, hpre, hsub, hinc11, hnxp, hnps, hphi, hnext,
    hi, hjlen, hpcell, hdstcell, hxpcell, htabcell, herrcell, hxjcell, hpos0cell,
    haddcall, hncell⟩ := h
  have hge : ¬ (decodeNextIdx inc11 adv).toNat < nxp.toNat := by
    rw [hnext, hnps]
    exact Nat.not_lt_of_ge (of_decide_eq_true hat)
  have hcond : evalICmp .ult (decodeNextIdx inc11 adv) nxp = (0 : BitVec 1) :=
    (evalICmp_ult_zero_iff _ _).2 hge
  rcases hphi with ⟨hprev, hj, ha⟩ | ⟨hprev, hj, hadv⟩
  · -- the emitter edge: both `phi` operands are registers
    subst hprev
    let e : State :=
      { (withEnv (udCleanup32Env s.env j adv sub inc11 nxp) s) with
          pc := "while.end35", pre := some "cleanup32" }
    have hstep : step escapeCalls usDecFunction s = .jump e := by
      have h1 := udCleanup32_step_zero s.env s "if.end32.i" (.reg "%add.i125")
        (.reg "%adv.1.i") j adv sub inc11 nxp hpc hpre
        latch_phi_operand_emitter latch_phi_operand_emitter_adv
        (evalOperand_reg_eq s.env s "%add.i125" (.int 64 j) hj)
        (by
          rw [evalOperand_reg_eq (("%j.3", .int 64 j) :: s.env) s "%adv.1.i"
            (.int 64 adv) (by rw [lookupName_cons_ne _ _ (by decide)]; exact ha)])
        hsub hinc11 hnxp hcond
      have hs : withEnv s.env s = s := rfl
      rw [hs] at h1
      exact h1
    refine ⟨e, 1, by omega, rfl, ?_, fun k => runFuel_jump_prefix hstep k⟩
    refine ⟨i, out, j, adv + sub, decodeNextIdx inc11 adv, paddr, xpaddr, tabaddr,
      err, xjaddr, pos0v, addv, nv, rfl, ?_, ?_, hjlen, ?_, hi, ?_, hnext,
      hpcell, hdstcell, hxpcell, htabcell, herrcell, hxjcell, hpos0cell, haddcall,
      hncell⟩
    · rw [show e.mem = s.mem from rfl]
      exact hwalk
    · simp only [e, withEnv, udCleanup32Env]; ud_lk
    · simp only [e, withEnv, udCleanup32Env]; ud_lk
    · simp only [e, withEnv, udCleanup32Env, decodeNextIdx, decodePairBit]; ud_lk
  · -- the simple-escape edge: `%j.3` is a register, `%adv.2` is the literal two
    subst hprev
    let e : State :=
      { (withEnv (udCleanup32Env s.env j adv sub inc11 nxp) s) with
          pc := "while.end35", pre := some "cleanup32" }
    have hstep : step escapeCalls usDecFunction s = .jump e := by
      have h1 := udCleanup32_step_zero s.env s "if.then6.i" (.reg "%add8.i")
        (.imm (.int 64 (BitVec.ofInt 64 2))) j adv sub inc11 nxp hpc hpre
        latch_phi_operand_simple latch_phi_operand_simple_adv
        (evalOperand_reg_eq s.env s "%add8.i" (.int 64 j) hj)
        (by rw [hadv]; rfl)
        hsub hinc11 hnxp hcond
      have hs : withEnv s.env s = s := rfl
      rw [hs] at h1
      exact h1
    refine ⟨e, 1, by omega, rfl, ?_, fun k => runFuel_jump_prefix hstep k⟩
    refine ⟨i, out, j, adv + sub, decodeNextIdx inc11 adv, paddr, xpaddr, tabaddr,
      err, xjaddr, pos0v, addv, nv, rfl, ?_, ?_, hjlen, ?_, hi, ?_, hnext,
      hpcell, hdstcell, hxpcell, htabcell, herrcell, hxjcell, hpos0cell, haddcall,
      hncell⟩
    · rw [show e.mem = s.mem from rfl]
      exact hwalk
    · simp only [e, withEnv, udCleanup32Env]; ud_lk
    · simp only [e, withEnv, udCleanup32Env]; ud_lk
    · simp only [e, withEnv, udCleanup32Env, decodeNextIdx, decodePairBit]; ud_lk



/-! ### The loop instance

The latch invariant in the shape `BoundLoop` consumes: the walk's cells and the
iteration budget.  The budget pair `c ≤ nps ∧ nps ≤ c + r` is what makes the
measure the budget rather than the difference, because one iteration advances the
position index by one or two while spending exactly one unit.

The exit is `cleanup32`'s own test; the iteration arm is the one residual, and it is
stated in the shape the loop consumes rather than left implicit.  Its run crosses
the two copy loops and the escape emitter, so its proof is the same assembly one
level down: each copy loop is itself a `BoundLoop` whose head is `while.body.i91` or
`while.body.i` and whose arms are the trace's copy steps. -/

/-- The latch invariant at an iteration budget: the walk's cells, and the distance
to the bound measured as a budget pair. -/
def LatchInv (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (r : Nat) (s : State) (c : Nat) : Prop :=
  DecodeLatch body st dst nps goal s c ∧ nps ≤ c + r

/-- The index is inside the bound. -/
theorem decodeLatch_cle {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {s : State} {c : Nat}
    (h : DecodeLatch body st dst nps goal s c) : c ≤ nps := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hcle, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := h
    exact hcle

/-- The latch invariant's budget pair. -/
theorem latchInv_budget {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {r : Nat} {s : State} {c : Nat}
    (h : LatchInv body st dst nps goal r s c) : c ≤ nps ∧ nps ≤ c + r :=
  ⟨decodeLatch_cle h.1, h.2⟩

/-- At the end of the budget the latch's own test holds, so the loop cannot stay
in it. -/
theorem latchInv_exit_at_zero {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {s : State} {c : Nat}
    (h : LatchInv body st dst nps goal 0 s c) : decide (nps ≤ c) = true := by
  have hb := latchInv_budget h
  exact decide_eq_true (by omega)

/-- The iteration arm's shape: one run from the latch back to the latch, spending
one unit of the budget and advancing the index. -/
def LatchStepLoop (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (cost : Nat) : Prop :=
  ∀ (r : Nat) (s : State) (c : Nat),
    LatchInv body st dst nps goal (r + 1) s c →
    decide (nps ≤ c) = false →
    ∃ (e : State) (c' : Nat) (j : Nat), j ≤ cost ∧ e.pc = "cleanup32" ∧ c < c' ∧
      LatchInv body st dst nps goal r e c' ∧
      ∀ k, runFuel escapeCalls (j + k) usDecFunction s =
        runFuel escapeCalls k usDecFunction e

/-- **The decoder's walk is a `BoundLoop`.**  The bound is the position list's
length, the head the latch, and the exit the block the latch leaves for.  The exit
arm is `decodeLatch_step_exit`; the iteration arm is the residual, stated in the
shape the loop consumes. -/
def decodeLatchBoundLoop (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (cost : Nat) (hcost : 1 ≤ cost)
    (hloop : LatchStepLoop body st dst nps goal cost) :
    BoundLoop escapeCalls usDecFunction where
  head := "cleanup32"
  exitBlock := "while.end35"
  N := nps
  cost := cost
  Inv := LatchInv body st dst nps goal
  atBound := fun _ c => decide (nps ≤ c)
  ExitWord := fun e => ∃ c, DecodeLatchExit body st dst nps goal c e
  step_exit := by
    intro r s c h hat
    obtain ⟨hl, _⟩ := h
    obtain ⟨e, j, hj, hpc, hexit, hrun⟩ := decodeLatch_step_exit hl hat
    exact ⟨e, j, by omega, hpc, ⟨c, hexit⟩, hrun⟩
  step_loop := hloop
  exit_at_zero := by
    intro s c h
    exact latchInv_exit_at_zero h
  budget := by
    intro r s c h
    exact latchInv_budget h

/-- **The walk's fuel is a term of the arguments.**  With the iteration arm, the
latch reaches the exit within `(nps + 1) * cost` control steps, and a completed exit
continuation lifts to the whole walk. -/
theorem decodeBoundLoop_run_at (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (cost : Nat) (hcost : 1 ≤ cost)
    (hloop : LatchStepLoop body st dst nps goal cost)
    (s : State) (c : Nat) (k : Nat)
    (hinv : LatchInv body st dst nps goal nps s c) {o : Outcome}
    (hcont : ∀ (e : State), e.pc = "while.end35" →
      (∃ c', DecodeLatchExit body st dst nps goal c' e) →
      runFuel escapeCalls k usDecFunction e = some o) :
    runFuel escapeCalls ((nps + 1) * cost + k) usDecFunction s = some o :=
  (decodeLatchBoundLoop body st dst nps goal cost hcost hloop).run_at s c hinv k hcont

/-- The walk's contribution to the expander's budget: `(nps + 1) * decodeIterCost n`
is a summand of `escapeExpandBudget` at the caller's arguments. -/
theorem decodeWalkFuel_contribution {n nps : Nat} (hn : n < 2 ^ 64) (hnps : nps < 2 ^ 64) :
    (nps + 1) * decodeIterCost n ≤
      escapeExpandBudget [.ptr 0, .int 64 (BitVec.ofNat 64 n), .ptr 0, .ptr 0, .ptr 0,
        .ptr 0, .int 64 (BitVec.ofNat 64 nps), .int 64 0, .ptr 0] [] := by
  rw [escapeExpandBudget_decomp n nps hn hnps]
  simp only [decodeWalkFuel]
  omega

/-- **Sign extension at equal width is the identity**, so the `%arrayidx` steps'
hypothesis `(k.signExtend 64).toNat = k.toNat` is a fact rather than a restriction
on a staging.  Carrier: `BitVec.signExtend_eq`, whose footprint is
`[propext, Classical.choice, Quot.sound]`. -/
theorem signExtend_self_toNat (x : BitVec 64) : (x.signExtend 64).toNat = x.toNat := by
  rw [BitVec.signExtend_eq]



/-- **The iteration's first block.**  From the latch with `%cmp4` true — the
invariant's index link and `c < nps` make it the block's own test — `cleanup32`'s
one control step reaches `while.body6` carrying the advance `%add28`, the byte
cursor `%add24` and the prefix length `%j.3`, which are the operands the block's
three `phi`s read on the `cleanup32` edge.  The caller's staging cells ride through
unchanged, so the next block's trace has what it reads. -/
theorem decodeLatch_step_enter {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {s : State} {c : Nat} (h : DecodeLatch body st dst nps goal s c)
    (hlt : c < nps) :
    ∃ (e : State) (i : Nat) (out : List UInt8) (sub : BitVec 64) (adv : BitVec 64)
      (inc11 : BitVec 64) (j : BitVec 64) (nxp : BitVec 64)
      (paddr : Nat) (xpaddr : Nat) (tabaddr : Nat) (err : Nat) (xjaddr : Nat)
      (pos0v : BitVec 64) (addv : BitVec 64) (nv : BitVec 64),
      e.pc = "while.body6" ∧
      DecodeInv body st e.mem dst nps i c out goal ∧
      lookupName e.env "%add28" = some (.int 64 (decodeNextIdx inc11 adv)) ∧
      lookupName e.env "%add24" = some (.int 64 (adv + sub)) ∧
      lookupName e.env "%j.3" = some (.int 64 j) ∧
      j.toNat = out.length ∧
      lookupName e.env "%xp" = some (.ptr xpaddr) ∧
      lookupName e.env "%add" = some (.int 64 addv) ∧
      lookupName e.env "%p" = some (.ptr paddr) ∧
      lookupName e.env "%dst" = some (.ptr dst) ∧
      lookupName e.env "%tab" = some (.ptr tabaddr) ∧
      lookupName e.env "%err" = some (.ptr err) ∧
      lookupName e.env "%xj" = some (.ptr xjaddr) ∧
      lookupName e.env "%pos0" = some (.int 64 pos0v) ∧
      lookupName e.env "%n" = some (.int 64 nv) ∧
      ∀ k, runFuel escapeCalls (1 + k) usDecFunction s =
        runFuel escapeCalls k usDecFunction e := by
  obtain ⟨i, out, prev, sub, inc11, adv, j, nxp, paddr, xpaddr, tabaddr, err, xjaddr,
    pos0v, addv, nv, hpc, hwalk, hcle, hpre, hsub, hinc11, hnxp, hnps, hphi, hnext,
    hi, hjlen, hpcell, hdstcell, hxpcell, htabcell, herrcell, hxjcell, hpos0cell,
    haddcall, hncell⟩ := h
  have hgt : (decodeNextIdx inc11 adv).toNat < nxp.toNat := by
    rw [hnext, hnps]; exact hlt
  have hcond : evalICmp .ult (decodeNextIdx inc11 adv) nxp = (1 : BitVec 1) :=
    (evalICmp_ult_one_iff _ _).2 hgt
  rcases hphi with ⟨hprev, hj, ha⟩ | ⟨hprev, hj, hadv⟩
  · subst hprev
    let e : State :=
      { (withEnv (udCleanup32Env s.env j adv sub inc11 nxp) s) with
          pc := "while.body6", pre := some "cleanup32" }
    have hstep : step escapeCalls usDecFunction s = .jump e := by
      have h1 := udCleanup32_step s.env s "if.end32.i" (.reg "%add.i125")
        (.reg "%adv.1.i") j adv sub inc11 nxp hpc hpre
        latch_phi_operand_emitter latch_phi_operand_emitter_adv
        (evalOperand_reg_eq s.env s "%add.i125" (.int 64 j) hj)
        (by
          rw [evalOperand_reg_eq (("%j.3", .int 64 j) :: s.env) s "%adv.1.i"
            (.int 64 adv) (by rw [lookupName_cons_ne _ _ (by decide)]; exact ha)])
        hsub hinc11 hnxp hcond
      have hs : withEnv s.env s = s := rfl
      rw [hs] at h1
      exact h1
    refine ⟨e, i, out, sub, adv, inc11, j, nxp, paddr, xpaddr, tabaddr, err, xjaddr,
      pos0v, addv, nv, rfl, ?_, ?_, ?_, ?_, hjlen, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, fun k => runFuel_jump_prefix hstep k⟩
    · rw [show e.mem = s.mem from rfl]; exact hwalk
    · simp only [e, withEnv, udCleanup32Env, decodeNextIdx, decodePairBit]; ud_lk
    · simp only [e, withEnv, udCleanup32Env]; ud_lk
    · simp only [e, withEnv, udCleanup32Env]; ud_lk
    · exact hxpcell
    · exact haddcall
    · exact hpcell
    · exact hdstcell
    · exact htabcell
    · exact herrcell
    · exact hxjcell
    · exact hpos0cell
    · exact hncell
  · subst hprev
    let e : State :=
      { (withEnv (udCleanup32Env s.env j adv sub inc11 nxp) s) with
          pc := "while.body6", pre := some "cleanup32" }
    have hstep : step escapeCalls usDecFunction s = .jump e := by
      have h1 := udCleanup32_step s.env s "if.then6.i" (.reg "%add8.i")
        (.imm (.int 64 (BitVec.ofInt 64 2))) j adv sub inc11 nxp hpc hpre
        latch_phi_operand_simple latch_phi_operand_simple_adv
        (evalOperand_reg_eq s.env s "%add8.i" (.int 64 j) hj)
        (by rw [hadv]; rfl)
        hsub hinc11 hnxp hcond
      have hs : withEnv s.env s = s := rfl
      rw [hs] at h1
      exact h1
    refine ⟨e, i, out, sub, adv, inc11, j, nxp, paddr, xpaddr, tabaddr, err, xjaddr,
      pos0v, addv, nv, rfl, ?_, ?_, ?_, ?_, hjlen, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, fun k => runFuel_jump_prefix hstep k⟩
    · rw [show e.mem = s.mem from rfl]; exact hwalk
    · simp only [e, withEnv, udCleanup32Env, decodeNextIdx, decodePairBit]; ud_lk
    · simp only [e, withEnv, udCleanup32Env]; ud_lk
    · simp only [e, withEnv, udCleanup32Env]; ud_lk
    · exact hxpcell
    · exact haddcall
    · exact hpcell
    · exact hdstcell
    · exact htabcell
    · exact herrcell
    · exact hxjcell
    · exact hpos0cell
    · exact hncell

/-! ### The refusal instance's boundary

The loop's second exit — `cleanup41` on a refusal — is a normal outcome the record
covers, so the loop needs an instance whose exit names it.  Its exit test is the
disjunction "at the bound or the head position refuses", and its boundary at
budget zero is **vacuous rather than relied on**: at budget zero the invariant
forces `c = nps`, the remaining list is empty, and the walk is a decode, so no
state carrying a refused goal satisfies the invariant there.  That is stated here
so the second instance's `exit_at_zero` is discharged by a lemma rather than by an
argument in prose. -/

/-- A refused goal cannot be carried at budget zero: the budget forces the index to
the bound, where the walk has nothing left to refuse. -/
theorem latch_refused_budget_zero_absurd {body : List UInt8} {st : ClassState}
    {dst nps : Nat} {goal : EscapeOutcome} {s : State} {c : Nat} {off k : Nat}
    (hgoal : goal = .refused off k) (h : LatchInv body st dst nps goal 0 s c) : False := by
  have hb := latchInv_budget h
  have hc : c = nps := by omega
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hwalk, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := h.1
  have hdec := DecodeInv.exit hwalk hc
  rw [hgoal] at hdec
  exact EscapeOutcome.noConfusion hdec

/-! ### Axiom footprints -/

-- The staging predicate is a definition, not a theorem.
/-- info: 'LeanLLVM.Vellum.DecodeNoAlias' does not depend on any axioms -/
#guard_msgs in
#print axioms DecodeNoAlias

/-- info: 'LeanLLVM.Vellum.decodeNextIdx' depends on axioms: [propext] -/
#guard_msgs in
#print axioms decodeNextIdx

/-- info: 'LeanLLVM.Vellum.evalICmp_ult_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evalICmp_ult_zero_iff

/-- info: 'LeanLLVM.Vellum.escapeExpandBudget' depends on axioms: [propext] -/
#guard_msgs in
#print axioms escapeExpandBudget

/-- info: 'LeanLLVM.Vellum.escapeExpandBudget_decomp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms escapeExpandBudget_decomp

/-- info: 'LeanLLVM.Vellum.decodeLatch_step_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decodeLatch_step_exit

/-- info: 'LeanLLVM.Vellum.latchInv_budget' depends on axioms: [propext] -/
#guard_msgs in
#print axioms latchInv_budget

/-- info: 'LeanLLVM.Vellum.latchInv_exit_at_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms latchInv_exit_at_zero

/-- info: 'LeanLLVM.Vellum.decodeLatchBoundLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decodeLatchBoundLoop

/-- info: 'LeanLLVM.Vellum.decodeBoundLoop_run_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decodeBoundLoop_run_at

/-- info: 'LeanLLVM.Vellum.signExtend_self_toNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms signExtend_self_toNat

/-- info: 'LeanLLVM.Vellum.decodeLatch_step_enter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms decodeLatch_step_enter

/-- info: 'LeanLLVM.Vellum.latch_refused_budget_zero_absurd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms latch_refused_budget_zero_absurd

/-- info: 'LeanLLVM.Vellum.decodeWalkFuel_contribution' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms decodeWalkFuel_contribution

end LeanLLVM.Vellum
