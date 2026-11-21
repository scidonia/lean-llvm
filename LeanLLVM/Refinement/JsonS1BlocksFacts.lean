/-
The block unit's record instance and refinement, assembled from the committed
component modules.

`JsonS1BlocksSatisfies` states `s1_blocks_satisfies` with one hypothesis: for
every staging the record admits, the bundle `S1BlocksFacts` exists at the
record's own witnesses.  This module is that hypothesis's integration point.  It
names the bundle's three parts — the run at `s1BlocksBudget`, the staging's two
carried words and error bit, and the tail's memory shape — as the fields of
`S1BlocksResiduals`, proves `S1BlocksFacts` from those fields, and instantiates
the record instance and the refinement at `s1BlocksCallsEsc`.

## What each part consumes

* **`run`** — the full run from `EntryState` at the caller's allocator base,
  completing at `s1BlocksBudget`.  Its committed halves are the one-prefix
  (`JsonS1BlocksStream.s1BlocksPrefix_exit`, entry to `for.end101` with
  `ExitTermCells`) and the exits (`JsonS1BlocksPrefix.asciiExitCells_run` /
  `fusedExitCells_run`, the bound's block to the return with `VerdictPost`).
  The two halves are joined by `runFuel`'s prefix rule; the charge is
  `JsonS1BlocksSatisfies.s1BlocksBudget_of_entry`'s arithmetic.  The committed
  prefix states its own fuel only up to `s1BlocksInit` (the `next = 1` state)
  and does not expose it, so the joined run at the record's `next` is a field
  here rather than a term used from a module.

* **`staging`** — the two packed words and the error bit as a `VerdictStaging`
  at the document's block count.  Its committed halves are
  `JsonS1BlocksLoopFacts.staging_of_exitFacts` /
  `JsonS1BlocksStaging.acc_pack`; the loop's register-to-model identities are
  `JsonS1BlocksWordIdentities` (in flight) and the peel's own family is
  `JsonS1BlocksPeelStaging.lean` (in flight).

* **`tail`** — `S1BlocksTail` at the run's memory: the entry array's prefix, the
  run's frame (the one-region loop frame on the silent arms, the four-region one
  at the call's count on the escape arm), the stream's prefix, the peel's word,
  and on the escape arm the `EscapeReach` record.  Its committed pieces are
  `JsonS1BlocksLoopFacts.tail_peel_facts` / `LoopExitFacts`,
  `JsonS1BlocksRecordFrame`, `JsonS1BlocksSeparation` and the escape arm's
  `JsonS1BlocksEscapeRun.callTail_of_chain`; the loop's induction
  that carries `LoopExitFacts` through the four page shapes is not yet a
  committed theorem, so the shape is a field.

The residual is therefore not a weakening of the bundle: `S1BlocksResiduals`
and `S1BlocksFacts` are interderivable at fixed arguments (minus the argument
list equation, which `s1BlocksPre` already supplies), and no conclusion of
`s1_blocks_satisfies` or `s1_blocks_refines` is restated.  The three parts are
named in the field's docstring so the loop lane and the fuse/peel lanes can
discharge them one at a time.
-/
import LeanLLVM.Refinement.JsonS1BlocksSatisfies
import LeanLLVM.Refinement.JsonS1BlocksRefines
import LeanLLVM.Refinement.JsonS1BlocksContract

namespace LeanLLVM.Refinement.JsonS1BlocksFacts

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksSatisfies
open LeanLLVM.Refinement.JsonS1BlocksRefines
open LeanLLVM.Refinement.JsonS1BlocksVerdict
open LeanLLVM.Refinement.JsonS1BlocksStaging
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonScanSpec

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-- **The bundle's three parts, named.**

The `∃` binds the run's return value and memory once, so the staging and the tail
are both read at the run's own outcome rather than at independent witnesses.  The
parts are the run at `s1BlocksBudget`, the staging's two packed words and error
bit, and the tail's memory shape; the field docstring below states which
committed module supplies each and which lane still owes the remaining identity.
The module header has the full account. -/
structure S1BlocksResiduals (esc : Calls) (args : List Value) (mem : Mem) (next : Nat)
    (b ent xp nxp xcarry xn : Nat) (arm : BitVec 64) (bs : List UInt8) : Prop where
  /-- The three parts at the run's own return value and memory.  `ret` is the
  returned word and `M` the run's memory; `ascii` and `u8k` are the staging's two
  packed words, `err` its error bit and `gate` the classifier's gate.

  * The staging is `VerdictStaging` at the document's block count
    (`JsonS1BlocksLoopFacts.staging_of_exitFacts`,
    `JsonS1BlocksStaging.acc_pack`, and the in-flight
    `JsonS1BlocksWordIdentities` / `JsonS1BlocksPeelStaging`), and the returned
    word is read off it.
  * The run from the caller's allocator base completes at the record's budget
    (`JsonS1BlocksStream.s1BlocksPrefix_exit` joined to
    `JsonS1BlocksPrefix.asciiExitCells_run` / `fusedExitCells_run`, with
    `s1BlocksBudget_of_entry`'s charge).
  * The tail's memory shape at the run's memory is `S1BlocksTail`
    (`JsonS1BlocksLoopFacts`, `JsonS1BlocksRecordFrame`,
    `JsonS1BlocksSeparation`). -/
  parts : ∃ (ret : BitVec 64) (M : Mem) (ascii u8k : List (BitVec 64))
    (err : BitVec 1) (gate : Bool),
    VerdictStaging ascii u8k bs bs.length (blocksOf bs.length) gate err ∧
      ret = verdictWord ascii err ∧
      runFuel (s1BlocksCallsEsc esc) (s1BlocksBudget args mem) s1BlocksFunction
          (EntryState s1BlocksFunction args mem next) =
        some (.ret (some (.int 64 ret)) M) ∧
      S1BlocksTail mem ent xp nxp xcarry xn arm bs M

/-- **The bundle from its three parts.**  The argument-list equation is the only
input `S1BlocksResiduals` does not carry, because `s1BlocksPre` already fixes it
at the record's witnesses. -/
theorem s1BlocksFacts_of_residuals {esc : Calls} {args : List Value} {mem : Mem}
    {next : Nat} {b ent xp nxp xcarry xn : Nat} {arm : BitVec 64}
    {bs : List UInt8}
    (hargs : args = [.ptr b, .int 64 (BitVec.ofNat 64 bs.length), .ptr ent,
      .ptr xp, .ptr nxp, .ptr xcarry, .int 64 arm])
    (h : S1BlocksResiduals esc args mem next b ent xp nxp xcarry xn arm bs) :
    S1BlocksFacts esc args mem next b ent xp nxp xcarry xn arm bs := by
  obtain ⟨ret, M, ascii, u8k, err, gate, hstage, hret, hrun, htail⟩ := h.parts
  exact ⟨ret, M, ascii, u8k, err, gate, hstage, hret, hargs, hrun, htail⟩

/-- **The residual from the bundle.**  The two structures hold the same content
at fixed arguments; the split is a naming, not a weakening. -/
theorem s1BlocksResiduals_of_facts {esc : Calls} {args : List Value} {mem : Mem}
    {next : Nat} {b ent xp nxp xcarry xn : Nat} {arm : BitVec 64}
    {bs : List UInt8}
    (h : S1BlocksFacts esc args mem next b ent xp nxp xcarry xn arm bs) :
    S1BlocksResiduals esc args mem next b ent xp nxp xcarry xn arm bs := by
  obtain ⟨ret, M, ascii, u8k, err, gate, hstage, hret, -, hrun, htail⟩ := h
  exact ⟨⟨ret, M, ascii, u8k, err, gate, hstage, hret, hrun, htail⟩⟩

/-- **The run at the budget, and the post at its outcome.**  The residual's run
is the bundle's completion; the post, the document's blocks and the three staged
zeroes at the run's memory are
`JsonS1BlocksSatisfies.s1BlocksPost_and_document_of_facts` at the residual's
staging, tail and returned word.  This is the conjunction a consumer of the
record reads, with the completion at `s1BlocksBudget` and nothing assumed about
the post. -/
theorem s1BlocksRun_and_post_of_residuals {esc : Calls} {args : List Value}
    {mem : Mem} {next : Nat} {b ent xp nxp xcarry xn : Nat} {arm : BitVec 64}
    {bs : List UInt8}
    (hp : S1BlocksPreAt mem b ent xp nxp xcarry xn arm bs)
    (hargs : args = [.ptr b, .int 64 (BitVec.ofNat 64 bs.length), .ptr ent,
      .ptr xp, .ptr nxp, .ptr xcarry, .int 64 arm])
    (h : S1BlocksResiduals esc args mem next b ent xp nxp xcarry xn arm bs) :
    ∃ (ret : BitVec 64) (M : Mem),
      runFuel (s1BlocksCallsEsc esc) (s1BlocksBudget args mem) s1BlocksFunction
          (EntryState s1BlocksFunction args mem next) =
        some (.ret (some (.int 64 ret)) M) ∧
      s1BlocksPost args mem next (.ret (some (.int 64 ret)) M) ∧
      (∀ j, j < blocksOf bs.length →
        readBytes M (b + 64 * j) 64 = some (docBlock bs j)) ∧
      readBytes M (b - 3) 3 = some [0, 0, 0] := by
  obtain ⟨ret, M, ascii, u8k, err, gate, hstage, hret, hrun, htail⟩ := h.parts
  obtain ⟨hpost, hdoc, hzero⟩ :=
    s1BlocksPost_and_document_of_facts (next := next) hp hargs hstage hret htail
  exact ⟨ret, M, hrun, hpost, hdoc, hzero⟩

/-! ### The record instance, from the residuals -/

/-- **The block unit satisfies its record, from the three named parts.**  This is
`s1_blocks_satisfies` with its bundle hypothesis discharged by
`s1BlocksFacts_of_residuals`; the instance's statement is not restated. -/
theorem s1_blocks_satisfies_of_residuals {esc : Calls}
    (h : ∀ (args : List Value) (mem : Mem) (next : Nat)
        (b ent xp nxp xcarry xn : Nat) (arm : BitVec 64) (bs : List UInt8),
      s1BlocksPre args mem next →
      args = [.ptr b, .int 64 (BitVec.ofNat 64 bs.length), .ptr ent, .ptr xp,
              .ptr nxp, .ptr xcarry, .int 64 arm] →
      S1BlocksResiduals esc args mem next b ent xp nxp xcarry xn arm bs) :
    Satisfies (s1BlocksCallsEsc esc) s1BlocksFunction Γ_s1_blocks :=
  s1_blocks_satisfies fun args mem next b ent xp nxp xcarry xn arm bs hpre hargs =>
    s1BlocksFacts_of_residuals hargs (h args mem next b ent xp nxp xcarry xn arm bs
      hpre hargs)

/-- **The record instance, unconditionally over the selection, from a residual
that each selection's own staging supplies.** -/
theorem s1_blocks_satisfies_all_of_residuals
    (h : ∀ (esc : Calls) (args : List Value) (mem : Mem) (next : Nat)
        (b ent xp nxp xcarry xn : Nat) (arm : BitVec 64) (bs : List UInt8),
      s1BlocksPre args mem next →
      args = [.ptr b, .int 64 (BitVec.ofNat 64 bs.length), .ptr ent, .ptr xp,
              .ptr nxp, .ptr xcarry, .int 64 arm] →
      S1BlocksResiduals esc args mem next b ent xp nxp xcarry xn arm bs) :
    ∀ esc : Calls, Satisfies (s1BlocksCallsEsc esc) s1BlocksFunction Γ_s1_blocks :=
  fun esc => s1_blocks_satisfies_of_residuals (h esc)

/-! ### The refinement, from the record instance -/

/-- **The refinement follows from the record instance.**  `s1_blocks_refines`
runs from `s1BlocksInit`, which is `EntryState` at the empty-memory state's
allocator base (`next = 1`); the record instance at `next = 1` gives the post for
every behaviour, and the refinement's reachability hypothesis is one of those
behaviours.

The `escapeEntryAt` premise is not read: neither the pre nor the post mentions
the base or the selection's entry state, so the refinement holds at every base
the premise names.  This is the statement `JsonS1BlocksRefines.s1_blocks_refines`
defines, unchanged. -/
theorem s1_blocks_refines_of_satisfies
    (hsat : ∀ esc : Calls,
      Satisfies (s1BlocksCallsEsc esc) s1BlocksFunction Γ_s1_blocks) :
    s1_blocks_refines := by
  intro esc base _ args mem next hpre o ho
  have hEq : s1BlocksInit args mem = EntryState s1BlocksFunction args mem 1 := rfl
  have hb : BehFromState (s1BlocksCallsEsc esc) s1BlocksFunction
      (EntryState s1BlocksFunction args mem 1) o :=
    Or.inr (by rwa [← hEq])
  exact (hsat esc args mem 1 hpre).2 o hb

/-- **The refinement, from the bundle itself.**  The direct form: the bundle
hypothesis `JsonS1BlocksSatisfies.s1_blocks_satisfies` takes is the same, and the
refinement is its `next = 1` read. -/
theorem s1_blocks_refines_of_facts
    (h : ∀ (esc : Calls) (args : List Value) (mem : Mem) (next : Nat)
        (b ent xp nxp xcarry xn : Nat) (arm : BitVec 64) (bs : List UInt8),
      s1BlocksPre args mem next →
      args = [.ptr b, .int 64 (BitVec.ofNat 64 bs.length), .ptr ent, .ptr xp,
              .ptr nxp, .ptr xcarry, .int 64 arm] →
      S1BlocksFacts esc args mem next b ent xp nxp xcarry xn arm bs) :
    s1_blocks_refines :=
  s1_blocks_refines_of_satisfies fun esc => s1_blocks_satisfies (h esc)

/-- **The refinement, from the residuals.**  The record instance at each
selection is `s1_blocks_satisfies_of_residuals`; the refinement is its `next = 1`
read through `s1_blocks_refines_of_satisfies`. -/
theorem s1_blocks_refines_of_residuals
    (h : ∀ (esc : Calls) (args : List Value) (mem : Mem) (next : Nat)
        (b ent xp nxp xcarry xn : Nat) (arm : BitVec 64) (bs : List UInt8),
      s1BlocksPre args mem next →
      args = [.ptr b, .int 64 (BitVec.ofNat 64 bs.length), .ptr ent, .ptr xp,
              .ptr nxp, .ptr xcarry, .int 64 arm] →
      S1BlocksResiduals esc args mem next b ent xp nxp xcarry xn arm bs) :
    s1_blocks_refines :=
  s1_blocks_refines_of_satisfies (s1_blocks_satisfies_all_of_residuals h)

/-! ### Axiom footprints

The two bundle conversions are structure packing and projection, so they carry
nothing beyond the staging's carrier (`propext`, `Quot.sound`).  The record
instance inherits `JsonS1BlocksSatisfies.s1_blocks_satisfies`'s `propext`,
`Classical.choice`, `Quot.sound`; `s1_blocks_refines_of_satisfies` adds only
`BehFromState`'s definition and the `s1BlocksInit` identification (`propext`,
`Quot.sound`), while the forms built through the instance carry the instance's
`Classical.choice`.  `s1BlocksRun_and_post_of_residuals` reads
`s1BlocksPost_and_document_of_facts`, hence `Classical.choice`.  No statement
reaches `sorryAx`. -/
#print axioms LeanLLVM.Refinement.JsonS1BlocksFacts.S1BlocksResiduals
#print axioms LeanLLVM.Refinement.JsonS1BlocksFacts.s1BlocksFacts_of_residuals
#print axioms LeanLLVM.Refinement.JsonS1BlocksFacts.s1BlocksResiduals_of_facts
#print axioms LeanLLVM.Refinement.JsonS1BlocksFacts.s1BlocksRun_and_post_of_residuals
#print axioms LeanLLVM.Refinement.JsonS1BlocksFacts.s1_blocks_satisfies_of_residuals
#print axioms LeanLLVM.Refinement.JsonS1BlocksFacts.s1_blocks_satisfies_all_of_residuals
#print axioms LeanLLVM.Refinement.JsonS1BlocksFacts.s1_blocks_refines_of_satisfies
#print axioms LeanLLVM.Refinement.JsonS1BlocksFacts.s1_blocks_refines_of_facts
#print axioms LeanLLVM.Refinement.JsonS1BlocksFacts.s1_blocks_refines_of_residuals

end LeanLLVM.Refinement.JsonS1BlocksFacts
