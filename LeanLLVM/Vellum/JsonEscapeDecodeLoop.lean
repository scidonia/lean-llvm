/-
The decoder's bound exit, on `LoopFuel.BoundLoop`.

`@us_dec_x`'s position walk is the bound-exit shape: its latch `cleanup32` forms
the next position index `%add28` from `%inc11` and the surrogate advance, and
compares it with the list's length `%nxp` —

    %add28  = add %inc11, %conv27          ; one, or two for a surrogate pair
    %cmp4   = icmp ult %add28, %nxp
    condbr %cmp4, "while.body6", "while.end35"

so the loop continues while the index is below the bound and leaves at it.  The
measure is `nps - k`, and one iteration advances `k` by one, or by two for a
surrogate pair, so the distance to the bound falls by at least one per iteration.

`decodeLoopInv` states `DecodeInv` in `BoundLoop`'s form: the walk from the
position index the latch carries is the caller's goal, the state is at the latch,
the index is inside the list, and the iteration budget covers the distance to the
bound.  `decodeLoopInv_entry` is `DecodeInv`'s own seed at the head, so the entry
needs nothing beyond `decodeInv_seed`; `decodeBoundLoop` builds the loop from it,
and `decodeLoop_run_at` reads off the loop's fuel — `(nps + 1) * cost`, a term of
the arguments, because `nps` is the length `%nxp` carries and `cost` is a constant.

**What is a hypothesis and why.**  The two arms are the body's facts, and they are
the only thing the shape asks for: `step_exit` is the latch's exit arm, a single
step whose instruction-level half is `udCleanup32_step_zero`
(`JsonEscapeDecodeTrace`), and `step_loop` is one iteration's run from the latch
back to it, through `while.body6`, the copy and the escape emitter.  Composing
that run from the trace's per-block facts is the assembly that the expander's
record still owes; it is not an induction, and this module's point is that nothing
in the loop's shape waits on it.  The bound, the budget arithmetic and the
distance's decrease are discharged here from `DecodeInv` alone.
-/
import LeanLLVM.Vellum.JsonEscapeDecodeTrace

set_option autoImplicit false
set_option maxRecDepth 8000

namespace LeanLLVM.Vellum

open LeanLLVM
open LeanLLVM.Vellum.JsonScanSpec
open LeanLLVM.Vellum.JsonEscapeIR
open LeanLLVM.Vellum.JsonEscapeIntrinsics

/-! ### The invariant in `BoundLoop`'s form -/

/-- `DecodeInv` at the loop's latch: after `r` iterations' budget the state is at
`cleanup32` carrying the position index `c`, and the walk from `c` is the caller's
goal.  The bound is the list's length, and the index is inside it. -/
def decodeLoopInv (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (r : Nat) (s : State) (c : Nat) : Prop :=
  ∃ (i : Nat) (out : List UInt8),
    DecodeInv body st s.mem dst nps i c out goal ∧
    s.pc = "cleanup32" ∧
    c ≤ nps ∧
    nps ≤ c + r

/-- The latch's exit test: `%cmp4` is the unsigned comparison of the carried index
with the bound, so the exit bit is `nps ≤ c`.  The state plays no part in it — the
comparison is the one `cleanup32` forms from its own `phi` and `%nxp`. -/
def decodeAtBound (nps : Nat) : State → Nat → Bool :=
  fun _ c => decide (nps ≤ c)

/-- **The invariant's entry.**  `DecodeInv`'s own seed at the latch with the whole
bound as its budget: entering the walk at the caller's position index `k0` costs
the loop's shape nothing but the head state and `k0 ≤ nps`. -/
theorem decodeLoopInv_entry (body : List UInt8) (st : ClassState) (dst nps k0 : Nat)
    (s : State) (hlist : (escAt body st 0).length = nps) (hpc : s.pc = "cleanup32")
    (hk0 : k0 ≤ nps) :
    decodeLoopInv body st dst nps
      (escapeDecodeGo body 0 k0 ((escAt body st 0).drop k0) []) nps s k0 := by
  refine ⟨0, [], decodeInv_seed hlist, hpc, hk0, by omega⟩

/-! ### The loop -/

/-- **The decoder's walk is a `BoundLoop`.**  The bound is the position list's
length, the head the walk's latch and the exit the block it leaves for.  The bound,
the exit test and the budget are fixed here; the two arms are the body's, stated as
the shape's per-iteration facts. -/
def decodeBoundLoop (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (cost : Nat) (ExitWord : State → Prop)
    (step_exit : ∀ (r : Nat) (s : State) (c : Nat),
      decodeLoopInv body st dst nps goal r s c → decodeAtBound nps s c = true →
      ∃ (e : State) (j : Nat), j ≤ cost ∧ e.pc = "while.end35" ∧ ExitWord e ∧
        ∀ k, runFuel escapeCalls (j + k) usDecFunction s =
          runFuel escapeCalls k usDecFunction e)
    (step_loop : ∀ (r : Nat) (s : State) (c : Nat),
      decodeLoopInv body st dst nps goal (r + 1) s c → decodeAtBound nps s c = false →
      ∃ (e : State) (c' : Nat) (j : Nat), j ≤ cost ∧ e.pc = "cleanup32" ∧ c < c' ∧
        decodeLoopInv body st dst nps goal r e c' ∧
        ∀ k, runFuel escapeCalls (j + k) usDecFunction s =
          runFuel escapeCalls k usDecFunction e) :
    BoundLoop escapeCalls usDecFunction where
  head := "cleanup32"
  exitBlock := "while.end35"
  N := nps
  cost := cost
  Inv := decodeLoopInv body st dst nps goal
  atBound := decodeAtBound nps
  ExitWord := ExitWord
  step_exit := step_exit
  step_loop := step_loop
  exit_at_zero := by
    intro s c h
    obtain ⟨_i, _out, _hwalk, _hpc, _hcle, hge⟩ := h
    show decide (nps ≤ c) = true
    exact decide_eq_true (by omega)
  budget := by
    intro r s c h
    obtain ⟨_i, _out, _hwalk, _hpc, hcle, hge⟩ := h
    exact ⟨hcle, hge⟩

/-- **The walk's fuel is a term of the arguments.**  With the body's two arms, the
latch reaches the exit within `(nps + 1) * cost` control steps, and a completed
exit continuation lifts to the whole loop.  The induction is `BoundLoop.run_at`'s;
nothing here is specific to the decoder beyond `DecodeInv`'s own walk. -/
theorem decodeLoop_run_at (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (cost : Nat) (ExitWord : State → Prop)
    (step_exit : ∀ (r : Nat) (s : State) (c : Nat),
      decodeLoopInv body st dst nps goal r s c → decodeAtBound nps s c = true →
      ∃ (e : State) (j : Nat), j ≤ cost ∧ e.pc = "while.end35" ∧ ExitWord e ∧
        ∀ k, runFuel escapeCalls (j + k) usDecFunction s =
          runFuel escapeCalls k usDecFunction e)
    (step_loop : ∀ (r : Nat) (s : State) (c : Nat),
      decodeLoopInv body st dst nps goal (r + 1) s c → decodeAtBound nps s c = false →
      ∃ (e : State) (c' : Nat) (j : Nat), j ≤ cost ∧ e.pc = "cleanup32" ∧ c < c' ∧
        decodeLoopInv body st dst nps goal r e c' ∧
        ∀ k, runFuel escapeCalls (j + k) usDecFunction s =
          runFuel escapeCalls k usDecFunction e)
    (s : State) (c : Nat) (k : Nat)
    (hinv : decodeLoopInv body st dst nps goal nps s c) {o : Outcome}
    (hcont : ∀ (e : State), e.pc = "while.end35" → ExitWord e →
      runFuel escapeCalls k usDecFunction e = some o) :
    runFuel escapeCalls ((nps + 1) * cost + k) usDecFunction s = some o :=
  (decodeBoundLoop body st dst nps goal cost ExitWord step_exit step_loop).run_at
    s c hinv k hcont

/-! ### The blocks the shape names

The head and the exit are blocks of the pinned body, so a fixture whose block moved
fails here rather than in the arms. -/

/-- info: 'LeanLLVM.Vellum.findBlock_udCleanup32' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udCleanup32

/-- The exit block is the pinned body's `while.end35`. -/
theorem findBlock_udWhileEnd35 :
    usDecFunction.findBlock "while.end35" =
      some (blockAt usDecFunction 23 (by decide)) := by decide

/-- info: 'LeanLLVM.Vellum.findBlock_udWhileEnd35' depends on axioms: [propext] -/
#guard_msgs in
#print axioms findBlock_udWhileEnd35

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Vellum.decodeLoopInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms decodeLoopInv

/-- info: 'LeanLLVM.Vellum.decodeAtBound' does not depend on any axioms -/
#guard_msgs in
#print axioms decodeAtBound

/-- info: 'LeanLLVM.Vellum.decodeLoopInv_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms decodeLoopInv_entry

/-- info: 'LeanLLVM.Vellum.decodeBoundLoop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms decodeBoundLoop

/-- info: 'LeanLLVM.Vellum.decodeLoop_run_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms decodeLoop_run_at

end LeanLLVM.Vellum
