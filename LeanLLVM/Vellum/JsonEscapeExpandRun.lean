/-
The expander's record, composed from the decoder's two-exit loop.

`JsonEscapeDecodeRun` proves the walk's fuel as a term of the arguments and leaves
two arm facts named.  This module composes the body's run around that loop:
`entry` and the pre-scan reach the latch, the two-exit induction walks the position
list to one of its exits, and the exit continuation carries the state to the
record's post.  What is proved here is that they compose into `Satisfies` at
`escapeExpandBudget`, with nothing left implicit; the four facts the loop analysis
names are hypotheses of that theorem, stated in one bundle at one staging so the
arms, the seed and the continuation are facts about the same run.

**The budget's own terms.**  `escapeExpandBudget` reads two numbers out of the
argument list — the body's length and the position count — and each stage's
allowance is one summand of it: the pre-scan's `(nps + 1) * 3`, the entry's first
iteration (`decodeIterCost n`, because the walk's latch is reached only through a
position), the walk's `decodeWalkFuel nps n`, and the final copy's `n / 64 + 3`
plus the return's four control steps.  `expandBodyLen`, `expandPosCount` and `expandExitFuel` name those
readings so the stages and the record use one vocabulary; the composition's
arithmetic is then `omega` on the budget's own decomposition rather than a fact
about the run.

**The stages are stated over the record's own surface.**  `ExpandSeed` and
`ExpandExit` take the argument list, the memory and the next id, and the record's
own witnesses `b xp tab err xj pos0 ps`, so a hypothesis about them is a
hypothesis about the record's own `pre` and not about an invented staging.
`ExpandSeed` carries `AssemblyLatchInv` at the whole bound — the state
`BoundLoop.run` starts from — and `ExpandExit` carries the two exit targets' data
(`decodeTwoExit` / `assemblyExitWord`) and the post, because the two exits leave
different continuations and the split is taken once, between them.

**The invariant is the staged one.**  `JsonEscapeExpandStaged` defines
`AssemblyLatchInv` as `StagedLatchInv` (`JsonEscapeCopyLoops`, which the copy
instances already consume) plus the five register cells the record's `pre` is
about: `%p`, `%xp`, `%tab`, `%pos0` and `%n`.  `DecodeLatch` binds those to
existentials, so a block that reads the position stream or the body cannot be
stepped from the plain latch; the pinnings are equalities of the same cells, so
they force the existentials rather than competing with them
(`assemblyLatchInv_paddr_eq`).  The exit word is `assemblyExitWord`: the decoded
edge records the index the exit proves (`c = nps`), the refusal edge records the
two stores the refusal performed before `cleanup41`, and the entry edge is
`DecodeEntryExit` unchanged.

**What is proved and what is assumed.**  `run_stages` is the composition: three
prefix facts give one run bounded by the sum of their allowances.  It consumes
`assemblyBoundLoop`'s `BoundLoop.run` and nothing else about the body, so the exit split
is one case split inside the continuation hypothesis rather than a case in the
induction.  `escape_expand_satisfies` instantiates it at `EntryState` and derives
the record's two conjuncts from `runFuel_outcome_unique`: completion at the budget
is the composed run raised to it, and the post at every behaviour is the post at
the composed outcome, the others being that same outcome.

The four facts left as hypotheses are the ones the loop analysis names: the
iteration arm, the refusal arm, the entry half-iteration, and the two exit
continuations.  No `sorry`, no `admit` and no `native_decide` stands behind any of
them; the file states them and their composition, and every theorem it proves is
pinned at the footprint the development already carries.
-/
import LeanLLVM.Vellum.JsonEscapeDecodeRun
import LeanLLVM.Vellum.JsonEscapeSteps
import LeanLLVM.Vellum.JsonEscapeExpandStaged

set_option autoImplicit false
set_option maxRecDepth 16000

namespace LeanLLVM.Vellum

open LeanLLVM
open LeanLLVM.Vellum.JsonEscapeIR
open LeanLLVM.Vellum.JsonEscapeIntrinsics
open LeanLLVM.Vellum.JsonScanSpec

/-! ### The budget's own terms -/

/-- The body's length as the record's argument list carries it: the second
argument, `%n`, read at its own width. -/
def expandBodyLen (args : List Value) : Nat :=
  match args with
  | [_, .int 64 nv, _, _, _, _, _, _, _] => nv.toNat
  | _ => 0

/-- The position count as the record's argument list carries it: the seventh
argument, `%nps`, read at its own width. -/
def expandPosCount (args : List Value) : Nat :=
  match args with
  | [_, _, _, _, _, _, .int 64 npsv, _, _] => npsv.toNat
  | _ => 0

/-- The final copy and return's allowance: `n / 64 + 3` vector trips for the
sixty-four-byte copy, and the four control steps of the return.  It is the last
two summands of `escapeExpandBudget`, in the same vocabulary. -/
def expandExitFuel (args : List Value) : Nat := expandBodyLen args / 64 + 3 + 4

/-! ### The two run stages

Both are stated at the argument list, the memory and the next id, which is the
record's own surface, and at the staging the loop's invariant names.  The seed
reaches `LatchInv` at the whole bound — the state `BoundLoop.run` starts from —
and the exit continuation takes whichever exit the loop reached. -/

/-! ### The entry stage's own terms

The entry's allowance is measured in the trace's own blocks rather than written as
a closed form.  `entryBlocks` is the entry's own stretch to `while.end` — the
`entry` block, `land.rhs`'s first visit, and `while.end` — and
`preScanPerPosition` is what one position the scan passes over adds: `while.body`,
then the `land.rhs` it returns to.  The record's staging bounds the passes-over at
zero (every entry lies inside the body's window), so the empty-list path is
`entryBlocks` alone.

The budget's `(nps + 1) * 3` summand is the closed form that bounds their sum, and
that is a corollary (`preScanFuel_le`), not the statement: a third entry path then
appears as a missing term here instead of as an unsatisfiable bound nobody tried.
-/

/-- The entry's own blocks to `while.end`. -/
def entryBlocks : Nat := 3

/-- One position the pre-scan passes over: `while.body` and the `land.rhs` it
returns to. -/
def preScanPerPosition : Nat := 2

/-- The pre-scan's allowance at `k` positions passed over. -/
def preScanFuel (k : Nat) : Nat := entryBlocks + preScanPerPosition * k

/-- The closed form the budget carries bounds the derived terms. -/
theorem preScanFuel_le {k nps : Nat} (hk : k ≤ nps) :
    preScanFuel k ≤ (nps + 1) * 3 := by
  unfold preScanFuel entryBlocks preScanPerPosition
  omega

/-- **The entry stage, in two arms.**

The latch arm is the pre-scan plus one iteration: the walk's head is `cleanup32`,
and the entry reaches it only through a position, so the first iteration is the
entry's own cost and not the loop's.

The empty arm is the staging whose list has nothing left to walk (`k0 = nps`,
which covers every body with no escape, `nps = 0`): the entry leaves for
`while.end35` at `while.end` and never reaches the latch.  Its state carries the
walk at `(0, nps, [])` — the whole body copied, which is `decoded body nps` — and
its `phi` operands are `while.end`'s own, so the arm is stated at the cells that
edge supplies rather than at the latch's. -/
def ExpandSeed (args : List Value) (mem : Mem) (next : Nat) (body : List UInt8)
    (st : ClassState) (dst : Nat) (goal : EscapeOutcome)
    (b xp tab err xj pos0 : Nat) (ps : List Nat)
    (hstaging : ExpandStaging args mem next body st dst (expandPosCount args) goal b xp
      tab pos0 (expandBodyLen args) ps err xj) : Prop :=
  (∃ (s : State) (c j : Nat),
      j ≤ preScanFuel (expandPosCount args) + decodeIterCost (expandBodyLen args) ∧
      AssemblyLatchInv body st dst (expandPosCount args) goal b xp tab pos0
        (expandBodyLen args) ps err xj mem (expandPosCount args) c s ∧
      ∀ k, runFuel escapeCalls (j + k) usDecFunction
          (EntryState usDecFunction args mem next) =
        runFuel escapeCalls k usDecFunction s)
  ∨ (∃ (e : State) (j : Nat),
      j ≤ entryBlocks ∧
      e.pc = "while.end35" ∧
      goal = .decoded body (expandPosCount args) ∧
      assemblyExitWord args mem next body st dst (expandPosCount args) goal b xp tab
        pos0 (expandBodyLen args) ps err xj e ∧
      ∀ k, runFuel escapeCalls (j + k) usDecFunction
          (EntryState usDecFunction args mem next) =
        runFuel escapeCalls k usDecFunction e)

/-- **The exit stage.**  From either exit of that staging — the decoded walk at
`while.end35`, or the refusal at `cleanup41` — the run completes at the record's
post within the final copy's allowance.  The split at the two exits is here and
nowhere else. -/
def ExpandExit (args : List Value) (mem : Mem) (next : Nat) (body : List UInt8)
    (st : ClassState) (dst nps : Nat) (goal : EscapeOutcome) (b xp tab : Nat)
    (pos0 n : Nat) (ps : List Nat) (err xj : Nat) : Prop :=
  ∀ (e : State), decodeTwoExit e →
    assemblyExitWord args mem next body st dst nps goal b xp tab pos0 n ps err xj e →
    ∃ (o : Outcome), runFuel escapeCalls (expandExitFuel args) usDecFunction e = some o ∧
      (Γ_escape_expand escapeExpandBudget).post args mem next o

/-! ### The composition -/

/-- **Three stages compose into one run.**  The seed reaches the latch within
`(nps + 1) * 3`, the loop's induction reaches an exit within
`(nps + 1) * decodeIterCost n`, and the continuation finishes within `exitFuel`.
The conclusion is the run from the start state at the sum of the three
allowances: the loop's own `BoundLoop.run` supplies the prefix, and the
continuation supplies the outcome and the property.

Nothing here reads the body's blocks: the only thing consumed about the loop is its
`run`, at `assemblyBoundLoop`'s instance and its own `cost`, so the composition is
the arithmetic of the three allowances rather than a second analysis of the walk. -/
theorem run_stages {start : State} {P : Outcome → Prop} {args : List Value}
    {mem : Mem} {next : Nat} {body : List UInt8}
    {st : ClassState} {dst nps n : Nat} {goal : EscapeOutcome}
    {b xp tab err xj pos0 : Nat} {ps : List Nat}
    {cost exitFuel : Nat}
    (hstaging : ExpandStaging args mem next body st dst nps goal b xp tab pos0 n ps
      err xj)
    (hcost : 1 ≤ cost)
    (hrefuse : assemblyRefusalArm args mem next body st dst nps goal b xp tab pos0 n
      ps err xj hstaging cost)
    (hloop : assemblyLatchStep body st dst nps goal b xp tab pos0 n ps err xj mem
      cost)
    (hseed :
      (∃ (s : State) (c j : Nat), j ≤ preScanFuel nps + cost ∧
        AssemblyLatchInv body st dst nps goal b xp tab pos0 n ps err xj mem nps c s ∧
        ∀ k, runFuel escapeCalls (j + k) usDecFunction start =
          runFuel escapeCalls k usDecFunction s)
      ∨ (∃ (e : State) (j : Nat), j ≤ entryBlocks ∧ e.pc = "while.end35" ∧
        goal = .decoded body nps ∧
        assemblyExitWord args mem next body st dst nps goal b xp tab pos0 n ps err xj
          e ∧
        ∀ k, runFuel escapeCalls (j + k) usDecFunction start =
          runFuel escapeCalls k usDecFunction e))
    (hexit : ∀ (e : State), decodeTwoExit e →
      assemblyExitWord args mem next body st dst nps goal b xp tab pos0 n ps err xj e →
      ∃ (o : Outcome), runFuel escapeCalls exitFuel usDecFunction e = some o ∧ P o) :
    ∃ (o : Outcome) (K : Nat),
      K ≤ preScanFuel nps + cost +
        (nps + 1) * cost + exitFuel ∧
      runFuel escapeCalls K usDecFunction start = some o ∧ P o := by
  rcases hseed with ⟨s, c, j, hj, hinv, hrun⟩ | ⟨e, j, hj, hpc, _hgoal, hword, hrun⟩
  · obtain ⟨e, jl, hjl, hexi, hword, hrunl⟩ :=
      (assemblyBoundLoop args mem next body st dst nps goal b xp tab pos0 n ps err xj
        hstaging cost hcost hrefuse hloop).run s c hinv exitFuel
    simp only [assemblyBoundLoop] at hjl
    obtain ⟨o, ho, hPo⟩ := hexit e hexi hword
    refine ⟨o, j + (jl + exitFuel), ?_, ?_, hPo⟩
    · have hjl' : jl ≤ (nps + 1) * cost := by
        simpa [Nat.mul_one] using hjl
      omega
    · rw [hrun (jl + exitFuel), hrunl]
      exact ho
  · have hexi : decodeTwoExit e := Or.inl hpc
    obtain ⟨o, ho, hPo⟩ := hexit e hexi hword
    refine ⟨o, j + exitFuel, ?_, ?_, hPo⟩
    · unfold preScanFuel entryBlocks preScanPerPosition at *
      omega
    · rw [hrun exitFuel]
      exact ho

/-! ### The four facts, at one staging

The arms, the seed and the continuation must all be about the same run: the loop
instance's exit predicate names `body`, `st`, `dst`, `nps` and `goal`, and the
continuation reads the states it leaves.  One structure binds them, so a bundle is
a statement about one staging rather than four independent claims, and `ps` and
`pos0` appear where the body's own test does — in the two arms. -/

/-- **The decoder's four remaining facts**, at one staging: the iteration arm, the
refusal arm, the entry half-iteration, and the two exit continuations. -/
structure ExpandFacts (args : List Value) (mem : Mem) (next : Nat) where
  /-- The body the run decodes. -/
  body : List UInt8
  /-- The classifier state the position list is read off. -/
  st : ClassState
  /-- The destination base. -/
  dst : Nat
  /-- The outcome the caller's staging names. -/
  goal : EscapeOutcome
  /-- The caller's position list, as `*xp` holds it. -/
  ps : List Nat
  /-- The document offset of the body's first byte. -/
  pos0 : Nat
  /-- The body base the latch's `%p` reads. -/
  pb : Nat
  /-- The position stream base the latch's `%xp` reads. -/
  xp : Nat
  /-- The escape table's base, which the latch's `%tab` reads. -/
  tab : Nat
  /-- The offset slot's base, which the refusal stores to. -/
  err : Nat
  /-- The cursor slot's base, which the refusal and the success path store to. -/
  xj : Nat
  /-- **The caller's staging**, named by the record's own `pre` and identified with
  these witnesses: the producer supplies it from its `hpre`, and every exit word and
  arm is stated at it. -/
  staging : ExpandStaging args mem next body st dst (expandPosCount args) goal pb xp
    tab pos0 (expandBodyLen args) ps err xj
  /-- **The iteration arm**: the run from the latch back to the latch, crossing
  the two copy loops and the escape emitter. -/
  loop : assemblyLatchStep body st dst (expandPosCount args) goal pb xp tab pos0
    (expandBodyLen args) ps err xj mem (decodeIterCost (expandBodyLen args))
  /-- **The refusal arm**: the run from the latch to `cleanup41` at a position that
  refuses, crossing the same blocks as the iteration. -/
  refuse : assemblyRefusalArm args mem next body st dst (expandPosCount args) goal pb
    xp tab pos0 (expandBodyLen args) ps err xj staging
    (decodeIterCost (expandBodyLen args))
  /-- **The entry stage, in its two arms**: the pre-scan plus one iteration to the
  latch, or — when the list has nothing left to walk — the pre-scan straight to
  `while.end35`. -/
  seed : ExpandSeed args mem next body st dst goal pb xp tab err xj pos0 ps staging
  /-- **The exit continuations**: `while.end35`'s final copy and return, and
  `cleanup41`'s refusal and success returns. -/
  exit : ExpandExit args mem next body st dst (expandPosCount args) goal pb xp tab
    pos0 (expandBodyLen args) ps err xj

/-! ### The record's instance -/

/-- **The escape expander refines its record.**  From a staging the record admits,
the run of the pinned expander completes at the record's budget and every
behaviour it has satisfies the record's post: the decoded bytes at the cursor (or
the refusal's two stores), the returned count, and every byte outside the written
regions unchanged.

The bundle is the only hypothesis.  Its four fields are the decoder analysis's own
residuals, at the record's witnesses, so the statement assumes nothing about a
staging the record does not admit, and nothing about the body beyond the loop
instance and the two continuations. -/
theorem escape_expand_satisfies
    (hfacts : ∀ (args : List Value) (mem : Mem) (next : Nat),
      (Γ_escape_expand escapeExpandBudget).pre args mem next →
      ExpandFacts args mem next) :
    Satisfies escapeCalls usDecFunction (Γ_escape_expand escapeExpandBudget) := by
  intro args mem next hpre
  obtain ⟨body, st, dst, goal, ps, pos0, pb, xp, tab, err, xj, hstaging, hloop,
    hrefuse, hseed, hexit⟩ := hfacts args mem next hpre
  have hcost : 1 ≤ decodeIterCost (expandBodyLen args) := by
    unfold decodeIterCost
    omega
  obtain ⟨o, K, hK, hrun, hpost⟩ :=
    run_stages (start := EntryState usDecFunction args mem next)
      (P := (Γ_escape_expand escapeExpandBudget).post args mem next)
      (nps := expandPosCount args) (n := expandBodyLen args)
      (b := pb) (xp := xp) (tab := tab) (err := err) (xj := xj)
      (pos0 := pos0) (ps := ps) (mem := mem) (next := next) (args := args)
      (st := st) (body := body) (goal := goal) (dst := dst)
      hstaging hcost hrefuse hloop hseed hexit
  have hbudget : escapeExpandBudget args mem =
      (expandPosCount args + 1) * 3 + decodeIterCost (expandBodyLen args) +
      (expandPosCount args + 1) * decodeIterCost (expandBodyLen args) +
      expandExitFuel args := by
    obtain ⟨b, n, dst, err, xp, xj, nps, pos0, tab, body, ps, err0, k0,
      hargs, _hbody, _hxp, _hlen, _hrange, _hmap, _hcap, _hxj, _hxjle, _herr,
      _htab, _htail, _hdst, _hbdst, _hxpdst, _htabdst, _herrdst, _herrxj,
      _hxjdst⟩ := hpre
    rw [hargs]
    simp only [expandPosCount, expandBodyLen, expandExitFuel, escapeExpandBudget,
      decodeWalkFuel]
    omega
  have hcomp : runFuel escapeCalls (escapeExpandBudget args mem) usDecFunction
      (EntryState usDecFunction args mem next) = some o := by
    have hle : preScanFuel (expandPosCount args) +
        decodeIterCost (expandBodyLen args) +
        (expandPosCount args + 1) * decodeIterCost (expandBodyLen args) +
        expandExitFuel args ≤ escapeExpandBudget args mem := by
      rw [hbudget]
      have hscan : preScanFuel (expandPosCount args) ≤
          (expandPosCount args + 1) * 3 :=
        preScanFuel_le (Nat.le_refl _)
      omega
    exact runFuel_mono_le (Nat.le_trans hK hle) hrun
  refine ⟨?_, ?_⟩
  · cases o with
    | ub => exact absurd hpost (escape_expand_ub_false escapeExpandBudget args mem next)
    | ret v m =>
        cases v with
        | none => simp [Γ_escape_expand] at hpost
        | some v => exact ⟨v, m, hcomp⟩
  · intro o' ho'
    rcases ho' with ⟨_m', hm'⟩ | ⟨_m', hm'⟩
    · have hEq : Outcome.ub = o := runFuel_outcome_unique hm' hcomp
      rw [← hEq] at hpost
      exact absurd hpost (escape_expand_ub_false escapeExpandBudget args mem next)
    · have hEq : o' = o := runFuel_outcome_unique hm' hcomp
      rw [hEq]
      exact hpost

/-! ### Axiom footprints

`run_stages` and the record's instance carry `Classical.choice` because the loop
instance they consume does: `assemblyBoundLoop` inherits it from
`decodeLatch_step_exit`'s `evalICmp_ult_zero_iff`, the same `BitVec.ult` carrier
`JsonEscapeDecodeRun` names for the exit arm.  The rest is the development's own
ceiling. -/

/-- info: 'LeanLLVM.Vellum.expandBodyLen' depends on axioms: [propext] -/
#guard_msgs in
#print axioms expandBodyLen

/-- info: 'LeanLLVM.Vellum.expandPosCount' depends on axioms: [propext] -/
#guard_msgs in
#print axioms expandPosCount

/-- info: 'LeanLLVM.Vellum.expandExitFuel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms expandExitFuel

/-- info: 'LeanLLVM.Vellum.ExpandSeed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ExpandSeed

/-- info: 'LeanLLVM.Vellum.ExpandExit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ExpandExit

/-- info: 'LeanLLVM.Vellum.run_stages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_stages

/-- info: 'LeanLLVM.Vellum.escape_expand_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms escape_expand_satisfies

end LeanLLVM.Vellum
