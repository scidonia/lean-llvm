/-
`num_fast_el1`'s scan: the `BoundLoop` the lexical scan's digit run is, and the
straight-line steps around it.

`JsonStage2HelperIRNumFast` pins the body at every block.  This module takes the
first step the sibling bodies took against their pins — the loop — and fixes the
recipe's shape for it; the straight-line steps and the refusal run are
`JsonStage2NumFastBody`'s, and the conversion arm's proof is open.

**The scan's shape, and why it is two exits.**  The body's first loop is the
`num_d8_el1` fast path (`while.body`/`cleanup`), which calls out of line and is
therefore not this module's: a `Calls` entry for the eight-digit reader would have
to answer with the digit pair the two registers carry, and no entry in the walk's
environment does.  The lexical scan proper is the digit run at `land.lhs.true41`,
and that is the loop `BoundLoop` is built over.  Its head is the test block: the
block loads the byte at the counter and tests it against `'0'` … `'9'`; a digit
continues through `while.body52` (the `idig < 19` guard, whose arithmetic is
`if.then55`) and `if.end62`, whose `%exitcond.not` is the "counter reached the
length" test, and a non-digit leaves for `if.end68`.

So the loop leaves **two** ways — `if.end68` at the head's own test, `if.end230`
at `if.end62`'s — and `BoundLoop`'s shape is the disjunctive one the decoder's
instance already uses: `Exit` is the predicate naming both, `atBound` is the
disjunction of their tests, and one `step_exit` covers both.  The measure is the
distance to the length, `n - c`, which is why `N` is `n` and `atBound`'s first
disjunct is `n ≤ c + 1`: with `c + r = n` the budget can only reach zero when the
counter is one short of the bound.  The second disjunct is the non-digit test,
read off the byte the head is about to load, so the head's own test is available
as a `Bool` at `(state, counter)` without the state carrying the byte.  A byte
that does not read at all also exits — the head's load would be `ub` — so the
equivalence below carries a third disjunct for the absent byte, and the invariant
carries the byte's presence, which is what makes the exit the one the body takes.

**The cost.**  One iteration is at most four control steps: the head (its three
`phi`s, the address, the load, the subtract-and-test, and the branch), then
`while.body52`'s guard, then `if.then55` when the guard holds, then `if.end62`.
The exit at `if.end68` is the head's step alone (one step); the exit at
`if.end230` is the head, `while.body52`, `if.then55` and `if.end62` (four).  Both
are inside `cost = 4`, so every instantiation passes that number.

**What is proved, and what the arms owe.**  `numFastScanBoundLoop` fixes the
bound, the head's test, the invariant and the budget, and takes the two arms as
the shape's per-iteration facts — the decoder's and the copy loops' instances
state theirs the same way.  `numFastScan_run_at` is then
`BoundLoop`'s own induction at that instance, so the fuel the scan spends is
`(n + 1) * 4` — a term of the arguments and not of the trip count.  The arms
themselves are **not** discharged here: each is a `runFuel` prefix over four
concrete blocks, and the four blocks' `denoteCode` chains are the obligation,
stated below rather than assumed.  A body-level proof of the accepting row needs
the conversion arm first, so the arms are what a later session picks up.

**The exits the instance hands back.**  The instance's `Exit` names `if.end68` and
`if.end230`; what a caller does from either is its own continuation, and
`numFastScan_run_at` takes it as `hcont`.  The empty lexeme's continuation — the
refusal's store and return — is `JsonStage2NumFastBody.numFastBody_run_empty`,
stated against `s2NumFastContract`'s own `post` and `foot`.
-/
import LeanLLVM.Refinement.JsonStage2HelperIRNumFast
import LeanLLVM.Refinement.JsonStage2Helpers
import LeanLLVM.JSON.Bytes

set_option autoImplicit false
set_option maxRecDepth 10000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON (IsDigitB)

/-! ### The scan's bound

The head's test, read as a `Bool` at `(state, counter)`: the counter is one short
of the length, or the byte the head would load is not a digit.  A byte that does
not read is not a digit by this reading (`readByte … = none` answers `false` from
`numFastDigitAt`), which makes the test exit rather than take the loop; the
invariant below carries the byte's presence so the exit is the one the body
takes. -/

/-- Whether the byte at `p + c` is a digit, read from the memory. -/
def numFastDigitAt (m : Mem) (p c : Nat) : Bool :=
  match readByte m (p + c) with
  | some b => IsDigitB b
  | none => false

/-- **The head's test**: the counter reaches the length, or the byte at the
counter is not a digit.  The two disjuncts are the body's two exits — `if.end230`
from `if.end62`'s `%exitcond.not` and `if.end68` from the head's own test. -/
def numFastScanAtBound (mem0 : Mem) (p n : Nat) : State → Nat → Bool :=
  fun _ c => decide (n ≤ c + 1) || !numFastDigitAt mem0 p c

/-- The head's test, as the three readings: the bound reached, the byte absent, the
byte not a digit.  The memory is the staging's `mem0`
rather than the state's: the loop writes nothing, and stating it at `mem0` is what
lets `atBound` be read from the counter alone. -/
theorem numFastScanAtBound_eq (mem0 : Mem) (p n : Nat) (s : State) (c : Nat) :
    numFastScanAtBound mem0 p n s c = true ↔
      (n ≤ c + 1 ∨ readByte mem0 (p + c) = none ∨
        ∃ b, readByte mem0 (p + c) = some b ∧ !IsDigitB b = true) := by
  unfold numFastScanAtBound numFastDigitAt
  cases hrc : readByte mem0 (p + c) with
  | none =>
      rw [Bool.or_eq_true, decide_eq_true_eq]
      exact ⟨fun _ => Or.inr (Or.inl rfl), fun _ => Or.inr (by rfl)⟩
  | some b =>
      rw [Bool.or_eq_true, decide_eq_true_eq]
      have hsn : (some b = (none : Option UInt8)) = False := by simp
      rw [hsn]
      simp only [false_or]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr ⟨b, rfl, h⟩
      · rintro (h | ⟨b', hb', h⟩)
        · exact Or.inl h
        · have hbb : b = b' := Option.some.inj hb'
          rw [← hbb] at h
          exact Or.inr h

/-- **The invariant at the head.**  The state is at `land.lhs.true41`, the memory
is the staging's, the counter is the distance already consumed (`c + r = n`), the
length and the base are bound, the byte at the counter is present when the counter
is inside the lexeme, and the head's `phi` sources carry the counter: `%inc64` on
the back edge, `%i.1558` at the entry.  The `idig`/`ip` values are existentially
quantified and not fixed — the loop carries them, and the body's control flow
depends on `idig` only through its own guard, which the arms case-split. -/
def numFastScanInv (mem0 : Mem) (p n : Nat) (r : Nat) (s : State) (c : Nat) : Prop :=
  s.pc = "land.lhs.true41" ∧ s.mem = mem0 ∧ c + r = n ∧
  lookupName s.env "%p" = some (.ptr p) ∧
  lookupName s.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) ∧
  (c < n → ∃ b, readByte mem0 (p + c) = some b) ∧
  (match s.pre with
   | some "if.end62" =>
       ∃ (idig ip : BitVec 64),
         lookupName s.env "%inc64" = some (.int 64 (BitVec.ofNat 64 c)) ∧
         lookupName s.env "%inc63" = some (.int 64 idig) ∧
         lookupName s.env "%ip.4" = some (.int 64 ip)
   | some "land.lhs.true41.preheader" =>
       ∃ (idig ip : BitVec 64),
         lookupName s.env "%i.1558" = some (.int 64 (BitVec.ofNat 64 c)) ∧
         lookupName s.env "%idig.0560" = some (.int 64 idig) ∧
         lookupName s.env "%ip.0562" = some (.int 64 ip)
   | _ => False)

/-- **The invariant's entry**: the head carrying the entry's counter `c0`, with
the length as the whole budget. -/
theorem numFastScanInv_entry (mem0 : Mem) (p n c0 : Nat) (s : State)
    (hpc : s.pc = "land.lhs.true41") (hmem : s.mem = mem0)
    (hp : lookupName s.env "%p" = some (.ptr p))
    (hn : lookupName s.env "%n" = some (.int 64 (BitVec.ofNat 64 n)))
    (hbyte : c0 < n → ∃ b, readByte mem0 (p + c0) = some b)
    (hpre : match s.pre with
      | some "if.end62" =>
          ∃ (idig ip : BitVec 64),
            lookupName s.env "%inc64" = some (.int 64 (BitVec.ofNat 64 c0)) ∧
            lookupName s.env "%inc63" = some (.int 64 idig) ∧
            lookupName s.env "%ip.4" = some (.int 64 ip)
      | some "land.lhs.true41.preheader" =>
          ∃ (idig ip : BitVec 64),
            lookupName s.env "%i.1558" = some (.int 64 (BitVec.ofNat 64 c0)) ∧
            lookupName s.env "%idig.0560" = some (.int 64 idig) ∧
            lookupName s.env "%ip.0562" = some (.int 64 ip)
      | _ => False)
    (hc0 : c0 ≤ n) :
    numFastScanInv mem0 p n (n - c0) s c0 :=
  ⟨hpc, hmem, by omega, hp, hn, hbyte, hpre⟩

/-- **The scan is a `BoundLoop`.**  The bound, the head's test, the invariant and
the budget are fixed here; the two arms are the body's — the exit step and one
iteration's return to the head — stated as the shape's per-iteration facts, as the
decoder's and the copy loops' instances state theirs.  The two exits share one
induction: `Exit` is the disjunction of the blocks they leave for, and `atBound`
is the disjunction of their tests. -/
def numFastScanBoundLoop (mem0 : Mem) (p n : Nat) (cost : Nat)
    (Exit ExitWord : State → Prop)
    (step_exit : ∀ (r : Nat) (s : State) (c : Nat),
      numFastScanInv mem0 p n r s c →
      numFastScanAtBound mem0 p n s c = true →
      ∃ (e : State) (j : Nat), j ≤ cost ∧ Exit e ∧ ExitWord e ∧
        ∀ k, runFuel s2HelperCalls (j + k) numFastBody s =
          runFuel s2HelperCalls k numFastBody e)
    (step_loop : ∀ (r : Nat) (s : State) (c : Nat),
      numFastScanInv mem0 p n (r + 1) s c →
      numFastScanAtBound mem0 p n s c = false →
      ∃ (e : State) (c' : Nat) (j : Nat), j ≤ cost ∧ e.pc = "land.lhs.true41" ∧
        c < c' ∧ numFastScanInv mem0 p n r e c' ∧
        ∀ k, runFuel s2HelperCalls (j + k) numFastBody s =
          runFuel s2HelperCalls k numFastBody e) :
    BoundLoop s2HelperCalls numFastBody where
  head := "land.lhs.true41"
  exitBlock := "if.end68"
  N := n
  cost := cost
  Inv := numFastScanInv mem0 p n
  atBound := numFastScanAtBound mem0 p n
  Exit := Exit
  ExitWord := ExitWord
  step_exit := step_exit
  step_loop := step_loop
  exit_at_zero := by
    intro s c h
    obtain ⟨_hpc, _hmem, hsum, _⟩ := h
    rw [numFastScanAtBound_eq]
    exact Or.inl (by omega)
  budget := by
    intro r s c h
    obtain ⟨_hpc, _hmem, hsum, _⟩ := h
    omega

/-- **The scan's fuel is a term of the arguments.**  With the body's two arms, the
head reaches an exit within `(n + 1) * cost` control steps, and a completed exit
continuation lifts to the whole loop.  The induction is `BoundLoop.run_at`'s;
nothing here is specific to the scan beyond its invariant. -/
theorem numFastScan_run_at (mem0 : Mem) (p n : Nat) (cost : Nat)
    (Exit ExitWord : State → Prop)
    (step_exit : ∀ (r : Nat) (s : State) (c : Nat),
      numFastScanInv mem0 p n r s c →
      numFastScanAtBound mem0 p n s c = true →
      ∃ (e : State) (j : Nat), j ≤ cost ∧ Exit e ∧ ExitWord e ∧
        ∀ k, runFuel s2HelperCalls (j + k) numFastBody s =
          runFuel s2HelperCalls k numFastBody e)
    (step_loop : ∀ (r : Nat) (s : State) (c : Nat),
      numFastScanInv mem0 p n (r + 1) s c →
      numFastScanAtBound mem0 p n s c = false →
      ∃ (e : State) (c' : Nat) (j : Nat), j ≤ cost ∧ e.pc = "land.lhs.true41" ∧
        c < c' ∧ numFastScanInv mem0 p n r e c' ∧
        ∀ k, runFuel s2HelperCalls (j + k) numFastBody s =
          runFuel s2HelperCalls k numFastBody e)
    (s : State) (c : Nat) (k : Nat) (hinv : numFastScanInv mem0 p n n s c)
    {o : Outcome}
    (hcont : ∀ (e : State), Exit e → ExitWord e →
      runFuel s2HelperCalls k numFastBody e = some o) :
    runFuel s2HelperCalls ((n + 1) * cost + k) numFastBody s = some o :=
  (numFastScanBoundLoop mem0 p n cost Exit ExitWord step_exit step_loop).run_at
    s c hinv k hcont


/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.numFastScanAtBound_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms numFastScanAtBound_eq

/-- info: 'LeanLLVM.Refinement.numFastScanBoundLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms numFastScanBoundLoop

/-- info: 'LeanLLVM.Refinement.numFastScan_run_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms numFastScan_run_at

end LeanLLVM.Refinement
