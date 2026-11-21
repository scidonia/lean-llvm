/-
The block unit's record instance and refinement, assembled from the committed
component modules.

`JsonS1BlocksSatisfies` states `s1_blocks_satisfies` with one hypothesis: for
every staging the record admits, the bundle `S1BlocksFacts` exists at the
record's own witnesses.  This module is that hypothesis's integration point.  It
names the bundle's parts as the fields of `S1BlocksResiduals` — the staging's two
carried words and error bit, the tail's memory shape, the entry-to-exit prefix at
its own charge, and the exit at its own charge — proves `S1BlocksFacts` from
them, the **run at `s1BlocksBudget` included**, and instantiates the record
instance and the refinement at `s1BlocksCallsEsc`.

## The run is not a field

The bundle's run is the record's whole body at `s1BlocksBudget` from `EntryState`
at the caller's allocator base.  It is a *term* here, not a hypothesis: the two
halves that compose it each have a charge, and
`JsonS1BlocksExitFuel.s1BlocksRun_at_budget_of_chargedStages` joins them once
each charge is inside the budget.

* **The prefix.**  `JsonS1BlocksPrefixFuel.OnePrefixBounded` runs the entry, the
  ASCII phase, the hand-off and the fused loop to `for.end101`'s terminal at
  `8 * (%n >>> 6) + 21` control steps, and
  `JsonS1BlocksPrefixFuel.prefixCharge_le_budget` puts that charge inside the
  record's `8 * blocksOf + 32`.  The residual carries this segment, because
  `JsonS1BlocksPrefixFuel.s1BlocksPrefix_exit_bounded` states it from
  `s1BlocksInit` — the `next = 1` state — while the record's completion is read
  at the caller's `next`; `next` reaches the body only through the escape call's
  argument, so the transport to the caller's base is not a committed lemma.  At
  `next = 1` the field is `OnePrefixBounded` read through
  `s1BlocksInit_entryState`, so the residual's prefix conjunct is discharged by
  the committed prefix (at its own inputs) rather than assumed.
* **The exit.**  `JsonS1BlocksExitFuel.exitCharge` is `5` — `for.end101`'s step,
  the peel's `if.then103` where it is taken, and the merge's three steps to the
  return — and `exitCharge_le_room` puts it inside the room the budget leaves
  above the prefix's charge, at least `11` steps.  The residual carries the exit
  at the prefix's own terminal; `JsonS1BlocksExitFuel.asciiExitCells_charged` and
  `fusedExitCells_charged` supply it from the exit's model-side carries, which
  are the peel's bit and the three stagings at the arm's values.
* **The join.**  `s1BlocksRun_at_budget_of_chargedStages` takes the two segments
  and both charges' containment and returns the run at `s1BlocksBudget` at the
  exit's own `ret` and memory.

## The staging and the tail

* **`staging`** — the two packed words and the error bit as a `VerdictStaging`
  at the document's block count.  Its committed halves are
  `JsonS1BlocksLoopFacts.staging_of_exitFacts` /
  `JsonS1BlocksStaging.acc_pack`; the loop's register-to-model identities are
  `JsonS1BlocksWordIdentities` and the peel's own family is
  `JsonS1BlocksPeelStaging`.
* **`tail`** — `S1BlocksTail` at the run's memory: the entry array's prefix and
  frame, the stream's prefix, the peel's word, and on the escape arm the
  `EscapeReach` record.  Its committed pieces are
  `JsonS1BlocksLoopFacts.tail_peel_facts` / `LoopExitFacts`,
  `JsonS1BlocksRecordFrame`, and `JsonS1BlocksSeparation`; the loop's induction
  that carries `LoopExitFacts` through the four page shapes is not yet a
  committed theorem, and the calling arm's shape is `JsonS1BlocksEscapeRun`'s, so
  the shape is a field.

## Why the bundle is still the bundle

`S1BlocksFacts`'s statement is unchanged: the run's reading, the staging and the
tail are the same at the same witnesses.  What changed is that the run is no
longer an assumption — the residual holds its two charged segments, each inside
the record's own budget term, and the run follows.  The residual is therefore
strictly stronger than the bundle at fixed arguments, which is why no converse
conversion is stated here: a run at `s1BlocksBudget` does not decompose into the
two segments without the terminal the prefix reaches.

The staging, the tail and the exit's carries are named so the loop lane and the
fuse/peel lanes can discharge them one at a time.
-/
import LeanLLVM.Refinement.JsonS1BlocksSatisfies
import LeanLLVM.Refinement.JsonS1BlocksRefines
import LeanLLVM.Refinement.JsonS1BlocksContract
import LeanLLVM.Refinement.JsonS1BlocksPrefixFuel
import LeanLLVM.Refinement.JsonS1BlocksExitFuel

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
open LeanLLVM.Refinement.JsonS1BlocksPrefix
open LeanLLVM.Refinement.JsonS1BlocksPrefixFuel
open LeanLLVM.Refinement.JsonS1BlocksExitFuel
open LeanLLVM.Refinement.JsonScanSpec

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-- **The bundle's parts, named.**

The `∃` binds the run's return value and memory once, so the staging, the tail and
the two run segments are all read at the run's own outcome rather than at
independent witnesses.  The parts are the staging, the tail at the run's memory,
the entry-to-exit prefix at the record's allocator base with its charge, and the
exit from the prefix's terminal with its charge.  The run at `s1BlocksBudget` is
not a conjunct: `s1BlocksRun_at_budget_of_chargedStages` derives it from the two
segments, and `s1BlocksFacts_of_residuals` packs the bundle from it. -/
structure S1BlocksResiduals (esc : Calls) (args : List Value) (mem : Mem) (next : Nat)
    (b ent xp nxp xcarry xn : Nat) (arm : BitVec 64) (bs : List UInt8) : Prop where
  /-- The parts at the run's own return value and memory.  `ret` is the returned
  word and `M` the run's memory; `ascii` and `u8k` are the staging's two packed
  words, `err` its error bit and `gate` the classifier's gate.

  * The prefix segment runs from `EntryState` at the record's allocator base to
    the exit's terminal `e` in at most `8 * (%n >>> 6) + 21` steps, where `%n` is
    the argument list's second slot; the terminal is an `ExitTermCells` state at
    the entry's gate word, which is the interface the exit's per-arm lemmas are
    read at.
  * The exit segment runs from `e` to the return in at most `exitCharge` (`5`)
    steps at `ret` and `M`.
  * The staging is `VerdictStaging` at the document's block count
    (`JsonS1BlocksLoopFacts.staging_of_exitFacts`,
    `JsonS1BlocksStaging.acc_pack`, and the in-flight
    `JsonS1BlocksWordIdentities` / `JsonS1BlocksPeelStaging`), and the returned
    word is read off it.
  * The tail's memory shape at the run's memory is `S1BlocksTail`
    (`JsonS1BlocksLoopFacts`, `JsonS1BlocksRecordFrame`,
    `JsonS1BlocksSeparation`). -/
  parts : ∃ (ret : BitVec 64) (M : Mem) (ascii u8k : List (BitVec 64))
    (err : BitVec 1) (gate : Bool) (e : State) (N jE : Nat),
    VerdictStaging ascii u8k bs bs.length (blocksOf bs.length) gate err ∧
      ret = verdictWord ascii err ∧
      S1BlocksTail mem ent xp nxp xcarry xn arm bs M ∧
      N ≤ 8 * ((BitVec.ofNat 64 bs.length) >>> 6).toNat + 21 ∧
      (∀ k, runFuel (s1BlocksCallsEsc esc) (N + k) s1BlocksFunction
          (EntryState s1BlocksFunction args mem next) =
        runFuel (s1BlocksCallsEsc esc) k s1BlocksFunction e) ∧
      ExitTermCells b (BitVec.ofNat 64 bs.length) (entryGate arm) arm e ∧
      jE ≤ exitCharge ∧
      runFuel (s1BlocksCallsEsc esc) jE s1BlocksFunction e =
        some (.ret (some (.int 64 ret)) M)

/-- **The run at the budget, from the residual's two segments.**  The prefix's
charge is inside the budget (`JsonS1BlocksPrefixFuel.prefixCharge_le_budget`) and
the exit's charge is inside the room above it (`exitCharge_le_room`), so
`JsonS1BlocksExitFuel.s1BlocksRun_at_budget_of_chargedStages` joins the segments
at `s1BlocksBudget`. -/
theorem run_of_residuals {esc : Calls} {args : List Value} {mem : Mem} {next : Nat}
    {b ent xp nxp xcarry xn : Nat} {arm : BitVec 64} {bs : List UInt8}
    (hargs : args = [.ptr b, .int 64 (BitVec.ofNat 64 bs.length), .ptr ent,
      .ptr xp, .ptr nxp, .ptr xcarry, .int 64 arm])
    (h : S1BlocksResiduals esc args mem next b ent xp nxp xcarry xn arm bs) :
    ∃ (ret : BitVec 64) (M : Mem),
      runFuel (s1BlocksCallsEsc esc) (s1BlocksBudget args mem) s1BlocksFunction
          (EntryState s1BlocksFunction args mem next) =
        some (.ret (some (.int 64 ret)) M) := by
  obtain ⟨ret, M, ascii, u8k, err, gate, e, N, jE, -, -, -, hN, htrace, -, hjE,
    hexit⟩ := h.parts
  exact ⟨ret, M, JsonS1BlocksExitFuel.s1BlocksRun_at_budget_of_chargedStages
    (args := args) (mem := mem) (next := next) (b := b) (ent := ent) (xp := xp)
    (nxp := nxp) (xcarry := xcarry) (n := BitVec.ofNat 64 bs.length)
    (conv := entryGate arm) (arm := arm) (ret := ret) (M := M) (e := e) (N := N)
    (jE := jE) hargs hN htrace hjE hexit⟩

/-- **The bundle from its parts.**  The argument-list equation is the only input
`S1BlocksResiduals` does not carry, because `s1BlocksPre` already fixes it at the
record's witnesses.  The run is the residual's two segments joined at
`s1BlocksBudget`; the staging and the tail are the residual's own, at that run's
outcome. -/
theorem s1BlocksFacts_of_residuals {esc : Calls} {args : List Value} {mem : Mem}
    {next : Nat} {b ent xp nxp xcarry xn : Nat} {arm : BitVec 64}
    {bs : List UInt8}
    (hargs : args = [.ptr b, .int 64 (BitVec.ofNat 64 bs.length), .ptr ent,
      .ptr xp, .ptr nxp, .ptr xcarry, .int 64 arm])
    (h : S1BlocksResiduals esc args mem next b ent xp nxp xcarry xn arm bs) :
    S1BlocksFacts esc args mem next b ent xp nxp xcarry xn arm bs := by
  obtain ⟨ret, M, ascii, u8k, err, gate, e, N, jE, hstage, hret, htail, hN, htrace,
    -, hjE, hexit⟩ := h.parts
  have hrun : runFuel (s1BlocksCallsEsc esc) (s1BlocksBudget args mem)
      s1BlocksFunction (EntryState s1BlocksFunction args mem next) =
      some (.ret (some (.int 64 ret)) M) :=
    JsonS1BlocksExitFuel.s1BlocksRun_at_budget_of_chargedStages
      (args := args) (mem := mem) (next := next) (b := b) (ent := ent) (xp := xp)
      (nxp := nxp) (xcarry := xcarry) (n := BitVec.ofNat 64 bs.length)
      (conv := entryGate arm) (arm := arm) (ret := ret) (M := M) (e := e) (N := N)
      (jE := jE) hargs hN htrace hjE hexit
  exact ⟨ret, M, ascii, u8k, err, gate, hstage, hret, hargs, hrun, htail⟩

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
  obtain ⟨ret, M, ascii, u8k, err, gate, hstage, hret, -, hrun, htail⟩ :=
    s1BlocksFacts_of_residuals hargs h
  obtain ⟨hpost, hdoc, hzero⟩ :=
    s1BlocksPost_and_document_of_facts (next := next) hp hargs hstage hret htail
  exact ⟨ret, M, hrun, hpost, hdoc, hzero⟩

/-! ### The record instance, from the residuals -/

/-- **The block unit satisfies its record, from the named parts.**  This is
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

The residual's conversions join the two charged segments with
`JsonS1BlocksExitFuel.s1BlocksRun_at_budget_of_chargedStages`, which is
`runFuel`'s prefix composition, its monotonicity and the two charges'
arithmetic; they carry nothing beyond the staging's carrier, `propext` and
`Quot.sound`.  (The exit compositions that discharge the exit segment —
`JsonS1BlocksExitFuel.asciiExitCells_charged` and `fusedExitCells_charged` — add
`Classical.choice` for the two-valued branch splits and the peel's value
projections; they are consumed by whoever supplies the residual, not by these
conversions.)  The record instance inherits
`JsonS1BlocksSatisfies.s1_blocks_satisfies`'s `propext`, `Classical.choice`,
`Quot.sound`; `s1_blocks_refines_of_satisfies` adds only `BehFromState`'s
definition and the `s1BlocksInit` identification (`propext`, `Quot.sound`),
while the forms built through the instance carry the instance's
`Classical.choice`.  `s1BlocksRun_and_post_of_residuals` reads
`s1BlocksPost_and_document_of_facts`, hence `Classical.choice`.  No statement
reaches `sorryAx`. -/
#print axioms LeanLLVM.Refinement.JsonS1BlocksFacts.S1BlocksResiduals
#print axioms LeanLLVM.Refinement.JsonS1BlocksFacts.run_of_residuals
#print axioms LeanLLVM.Refinement.JsonS1BlocksFacts.s1BlocksFacts_of_residuals
#print axioms LeanLLVM.Refinement.JsonS1BlocksFacts.s1BlocksRun_and_post_of_residuals
#print axioms LeanLLVM.Refinement.JsonS1BlocksFacts.s1_blocks_satisfies_of_residuals
#print axioms LeanLLVM.Refinement.JsonS1BlocksFacts.s1_blocks_satisfies_all_of_residuals
#print axioms LeanLLVM.Refinement.JsonS1BlocksFacts.s1_blocks_refines_of_satisfies
#print axioms LeanLLVM.Refinement.JsonS1BlocksFacts.s1_blocks_refines_of_facts
#print axioms LeanLLVM.Refinement.JsonS1BlocksFacts.s1_blocks_refines_of_residuals

end LeanLLVM.Refinement.JsonS1BlocksFacts
