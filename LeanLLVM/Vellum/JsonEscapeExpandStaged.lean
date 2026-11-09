/-
The staged invariant and the exit word the assembled expander's arms consume.

`DecodeLatch` (`JsonEscapeDecodeRun.lean`) binds the state's `%p`, `%xp`, `%tab`,
`%pos0` and `%n` to existentials and pins only `%dst` and `%nxp.toNat = nps`; it
carries no staging.  The first block after the latch — `while.body6`, whose
`%arrayidx7` load reads four bytes at `%xp + 4 * c` — therefore cannot be
evaluated from `LatchInv` alone: a state can satisfy it while `%xp` points at
memory that holds no position stream.  `StagedLatchInv`
(`JsonEscapeCopyLoops.lean`) adds the staging the two copies and the seed already
consume; `AssemblyLatchInv` adds the five register cells the staging and the
record's `pre` are about.

The two arm statements and the exit word below are the consumer-side forms of
this milestone's arms.  They live here, below `JsonEscapeExpandRun`, because the
decode module's own definitions are body-generic: `LatchStepLoopTwo` cannot be
stated at `AssemblyLatchInv` (the name is not in scope there), and `%err`/`%xj`
are the record's destinations, not the decode module's to know.

**The exit word, and what this module adds to it.**  The decoded exit stores
`%k.1.lcssa = %add28` at `%xj` in `us_run.exit112` (`JsonEscapeIR.lean:602`),
after the final copy, while the post's cursor clause names the walk's own `nps`;
`DecodeLatchExit` now records the equality (`c = nps`, derived at the arm from the
latch's `c ≤ nps` and the false exit test), so `AssemblyLatchExit` is its
projection.  The refusal's two stores happen in `if.then20`/`if.then22`
(`:384-385`, `:539-540`), before the exit state at `cleanup41`, and
`DecodeRefusalExit` records them with the destinations bound existentially;
`AssemblyRefusalExit` adds the two equalities tying those destinations to the
record's — the residue this module owes, because the record's `err` and `xj` are
its own.  The `cleanup41` *return* half needs none of the store facts
(`refusalReturn`).
-/
import LeanLLVM.Vellum.JsonEscapeCompose

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Vellum

open LeanLLVM
open LeanLLVM.Vellum.JsonEscapeIR
open LeanLLVM.Vellum.JsonEscapeIntrinsics
open LeanLLVM.Vellum.JsonScanSpec

/-! ### The staged invariant the arms consume -/

/-- The latch with the caller's staging and the five register cells that staging
and the record's `pre` are about.  A cell holds one value, so the pinnings are
not a second claim beside `DecodeLatch`'s: they force its existentials equal
(`assemblyLatchInv_paddr_eq`). -/
def AssemblyLatchInv (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (b xp tab : Nat) (pos0 n : Nat) (ps : List Nat)
    (r c : Nat) (s : State) : Prop :=
  StagedLatchInv body st dst nps goal xp pos0 n ps r c s ∧
  lookupName s.env "%p" = some (.ptr b) ∧
  lookupName s.env "%xp" = some (.ptr xp) ∧
  lookupName s.env "%tab" = some (.ptr tab) ∧
  lookupName s.env "%pos0" = some (.int 64 (BitVec.ofNat 64 pos0)) ∧
  lookupName s.env "%n" = some (.int 64 (BitVec.ofNat 64 n))

/-- The staged latch under the pinnings. -/
theorem assemblyLatchInv_staged {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {b xp tab pos0 n : Nat} {ps : List Nat} {r c : Nat}
    {s : State} (h : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps r c s) :
    StagedLatchInv body st dst nps goal xp pos0 n ps r c s := h.1

/-- The latch's own invariant. -/
theorem assemblyLatchInv_latch {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {b xp tab pos0 n : Nat} {ps : List Nat} {r c : Nat}
    {s : State} (h : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps r c s) :
    LatchInv body st dst nps goal r s c :=
  stagedLatchInv_latch h.1

/-- The caller's staging, with the `%add` cell beside it. -/
theorem assemblyLatchInv_staging {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {b xp tab pos0 n : Nat} {ps : List Nat} {r c : Nat}
    {s : State} (h : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps r c s) :
    ∃ addv : BitVec 64,
      DecodeStaging s.mem nps xp pos0 n ps addv ∧
      lookupName s.env "%add" = some (.int 64 addv) :=
  stagedLatchInv_staging h.1

/-- The latch's budget pair. -/
theorem assemblyLatchInv_budget {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {b xp tab pos0 n : Nat} {ps : List Nat} {r c : Nat}
    {s : State} (h : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps r c s) :
    c ≤ nps ∧ nps ≤ c + r :=
  stagedLatchInv_budget h.1

/-- The five parameter cells. -/
theorem assemblyLatchInv_params {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {b xp tab pos0 n : Nat} {ps : List Nat} {r c : Nat}
    {s : State} (h : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps r c s) :
    lookupName s.env "%p" = some (.ptr b) ∧
      lookupName s.env "%xp" = some (.ptr xp) ∧
      lookupName s.env "%tab" = some (.ptr tab) ∧
      lookupName s.env "%pos0" = some (.int 64 (BitVec.ofNat 64 pos0)) ∧
      lookupName s.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- The pinning forces `DecodeLatch`'s `%p` existential: the two values are equal,
so the extension refines the decode invariant rather than competing with it. -/
theorem assemblyLatchInv_paddr_eq {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {b xp tab pos0 n : Nat} {ps : List Nat} {r c : Nat}
    {s : State} (h : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps r c s)
    {paddr : Nat} (hp : lookupName s.env "%p" = some (.ptr paddr)) : paddr = b := by
  have hb : lookupName s.env "%p" = some (.ptr b) := h.2.1
  rw [hp] at hb
  exact Value.ptr.inj (Option.some.inj hb)

/-! ### The exit word the consumer needs

The decoded exit gains the index the exit proves, and the refusal exit gains the
destinations and the two stores the refusal path performed before `cleanup41`.
`err` and `xj` are the record's, so they are parameters of the word. -/

/-- The decoded exit: `DecodeLatchExit`'s data, whose own body records that the
index it left is `nps`. -/
def AssemblyLatchExit (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (c : Nat) (e : State) : Prop :=
  DecodeLatchExit body st dst nps goal c e

/-- The refusal exit: `DecodeRefusalExit`'s data — the two stores included — with
its existential destinations tied to the record's. -/
def AssemblyRefusalExit (err xj : Nat) (e : State) : Prop :=
  DecodeRefusalExit e ∧
  lookupName e.env "%err" = some (.ptr err) ∧
  lookupName e.env "%xj" = some (.ptr xj)

/-- The exit word's three edges, with the two strengthened forms. -/
def assemblyExitWord (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (err xj : Nat) (e : State) : Prop :=
  (∃ c, AssemblyLatchExit body st dst nps goal c e) ∨
  AssemblyRefusalExit err xj e ∨
  DecodeEntryExit body st dst nps goal e

/-! ### The two arm statements -/

/-- **The iteration arm**, at the staged invariant: one position's copy, its
escape, and the return to the latch with the index advanced. -/
def assemblyLatchStep (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (b xp tab pos0 n : Nat) (ps : List Nat)
    (cost : Nat) : Prop :=
  ∀ (r : Nat) (s : State) (c : Nat),
    AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps (r + 1) c s →
    (decide (nps ≤ c) || decodeRefuses body ps pos0 c) = false →
    ∃ (e : State) (c' : Nat) (j : Nat), j ≤ cost ∧ e.pc = "cleanup32" ∧
      c < c' ∧
      AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps r c' e ∧
      ∀ k, runFuel escapeCalls (j + k) usDecFunction s =
        runFuel escapeCalls k usDecFunction e

/-- **The refusal arm**, at the staged invariant: the refusal's stores and its
exit at `cleanup41`, with the exit word's strengthened refusal form. -/
def assemblyRefusalArm (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (b xp tab pos0 n : Nat) (ps : List Nat) (err xj : Nat)
    (cost : Nat) : Prop :=
  ∀ (r : Nat) (s : State) (c : Nat),
    AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps r c s →
    (decide (nps ≤ c) || decodeRefuses body ps pos0 c) = true → ¬ nps ≤ c →
    ∃ (e : State) (j : Nat), j ≤ cost ∧ decodeTwoExit e ∧
      assemblyExitWord body st dst nps goal err xj e ∧
      ∀ k, runFuel escapeCalls (j + k) usDecFunction s =
        runFuel escapeCalls k usDecFunction e

/-! ### The decoded exit at the arm

`DecodeLatch` carries `c ≤ nps`; the exit test being false is `nps ≤ c`; the two
give the index the exit's store carries. -/
theorem assemblyLatchStepExit {body : List UInt8} {st : ClassState} {dst nps : Nat}
    {goal : EscapeOutcome} {b xp tab pos0 n : Nat} {ps : List Nat} {r c : Nat}
    {s : State} (h : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps r c s)
    (hb : decide (nps ≤ c) = true) :
    ∃ (e : State) (j : Nat), j ≤ 1 ∧ e.pc = "while.end35" ∧
      AssemblyLatchExit body st dst nps goal c e ∧
      ∀ k, runFuel escapeCalls (j + k) usDecFunction s =
        runFuel escapeCalls k usDecFunction e := by
  obtain ⟨e, j, hj, hpc, hexit, hrun⟩ :=
    decodeLatch_step_exit (assemblyLatchInv_latch h).1 hb
  exact ⟨e, j, hj, hpc, hexit, hrun⟩


/-! ### The two-exit instance at the staged invariant

One `BoundLoop` for both exits, at the invariant the arms consume: the bound is
the list's length, the head the latch, the exit test the disjunction "at the bound
or the head position refuses", and the exit word the strengthened three-edge one.
The exit arm's bound case is `assemblyLatchStepExit`; the refusal case is the
caller's arm. -/
def assemblyBoundLoop (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (b xp tab pos0 n : Nat) (ps : List Nat) (err xj : Nat)
    (cost : Nat) (hcost : 1 ≤ cost)
    (hrefuse : assemblyRefusalArm body st dst nps goal b xp tab pos0 n ps err xj cost)
    (hloop : assemblyLatchStep body st dst nps goal b xp tab pos0 n ps cost) :
    BoundLoop escapeCalls usDecFunction where
  head := "cleanup32"
  exitBlock := "while.end35"
  N := nps
  cost := cost
  Inv := fun r s c => AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps r c s
  atBound := fun _ c => decide (nps ≤ c) || decodeRefuses body ps pos0 c
  Exit := decodeTwoExit
  ExitWord := assemblyExitWord body st dst nps goal err xj
  step_exit := by
    intro r s c h hat
    by_cases hb : nps ≤ c
    · obtain ⟨e, j, hj, hpc, hexit, hrun⟩ :=
        assemblyLatchStepExit h (decide_eq_true hb)
      exact ⟨e, j, by omega, Or.inl hpc, Or.inl ⟨c, hexit⟩, hrun⟩
    · have hrf : decodeRefuses body ps pos0 c = true := by
        cases hr : decodeRefuses body ps pos0 c with
        | false =>
            rw [hr] at hat
            simp [hb] at hat
        | true => rfl
      exact hrefuse r s c h hat hb
  step_loop := hloop
  exit_at_zero := by
    intro s c h
    have hb := assemblyLatchInv_budget h
    simp [decide_eq_true (by omega : nps ≤ c)]
  budget := by
    intro r s c h
    exact assemblyLatchInv_budget h

/-- **The staged walk's fuel**: from the latch at the whole bound, the run reaches
an exit state the word admits within `(nps + 1) * cost`, and a continuation that
splits once at the exit lifts to the whole walk. -/
theorem assemblyBoundLoop_run_at (body : List UInt8) (st : ClassState) (dst nps : Nat)
    (goal : EscapeOutcome) (b xp tab pos0 n : Nat) (ps : List Nat) (err xj : Nat)
    (cost : Nat) (hcost : 1 ≤ cost)
    (hrefuse : assemblyRefusalArm body st dst nps goal b xp tab pos0 n ps err xj cost)
    (hloop : assemblyLatchStep body st dst nps goal b xp tab pos0 n ps cost)
    (s : State) (c : Nat) (k : Nat)
    (hinv : AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps nps c s)
    {o : Outcome}
    (hcont : ∀ (e : State), decodeTwoExit e →
      assemblyExitWord body st dst nps goal err xj e →
      runFuel escapeCalls k usDecFunction e = some o) :
    runFuel escapeCalls ((nps + 1) * cost + k) usDecFunction s = some o :=
  (assemblyBoundLoop body st dst nps goal b xp tab pos0 n ps err xj cost hcost
    hrefuse hloop).run_at s c hinv k hcont

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Vellum.AssemblyLatchInv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AssemblyLatchInv

/-- info: 'LeanLLVM.Vellum.assemblyLatchInv_latch' depends on axioms: [propext] -/
#guard_msgs in
#print axioms assemblyLatchInv_latch

/-- info: 'LeanLLVM.Vellum.assemblyLatchInv_params' depends on axioms: [propext] -/
#guard_msgs in
#print axioms assemblyLatchInv_params

/-- info: 'LeanLLVM.Vellum.assemblyLatchInv_paddr_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms assemblyLatchInv_paddr_eq

/-- info: 'LeanLLVM.Vellum.AssemblyLatchExit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AssemblyLatchExit

/-- info: 'LeanLLVM.Vellum.AssemblyRefusalExit' does not depend on any axioms -/
#guard_msgs in
#print axioms AssemblyRefusalExit

/-- info: 'LeanLLVM.Vellum.assemblyExitWord' depends on axioms: [propext] -/
#guard_msgs in
#print axioms assemblyExitWord

/-- info: 'LeanLLVM.Vellum.assemblyLatchStepExit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms assemblyLatchStepExit

/-- info: 'LeanLLVM.Vellum.assemblyBoundLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms assemblyBoundLoop

/-- info: 'LeanLLVM.Vellum.assemblyBoundLoop_run_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms assemblyBoundLoop_run_at

end LeanLLVM.Vellum
