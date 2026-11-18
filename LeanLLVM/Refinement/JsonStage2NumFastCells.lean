/-
`num_fast_el1`'s carried cells: what a composition across a digit run must still
name, and the transport that carries it there.

`JsonStage2NumFastDigitRuns`' exit predicates name the cells their successors'
`phi`s read — the cursor, the length, the count `%7`, the accumulator and the
run's memory.  They do not name three cells no block of the body writes,
`%out`, `@NUMF_EL1_P10` and `@NUMF_EL1_POW10`, whose values are the caller's, nor
the sign `%tobool274.not`, which is `if.end`'s `phi` and which the scan's route
reads at the store.  A `runFuel` prefix does not expose the environments it
crosses, so no exit predicate can recover those cells from the run's start by
itself: the run is an identity of outcomes, and an outcome carries the returned
memory and not an environment.

**The transport.**  A run is a chain of control steps, so the cells are carried
by a chain: `NumFastChain` is a finite chain of `jump`s of the body, and each of
its steps states the block it takes is one whose instructions write none of the
cells in hand.  Three facts close it:

* the body's three kept cells are written by **no** block, so a chain carries
  them from any state, and the per-step obligation is a `decide` over the pinned
  body rather than a reading of the route (`numFast_out_unwritten`,
  `numFast_p10_unwritten`, `numFast_pow10_unwritten`);
* the sign is `if.end`'s alone, so a chain whose blocks avoid `if.end` carries it
  (`numFast_tobool_written_at_if_end`), which is what a chain entered after the
  dispatch's sign step does;
* the integer part's two cells are `if.end68`'s alone
  (`numFast_idig4_written_at_ifEnd68`, `numFast_ip5_written_at_ifEnd68`), so a
  step off that block leaves them where it found them
  (`numFast_step_intPart`) — the per-step fact the fraction run's arms conclude
  with, which is what the merge's `%idig`/`%ip` phis want;
* a chain is a `runFuel` prefix (`NumFastChain.runFuel`), so the cell transport
  and the fuel compose without a second statement of the run.

**Where it is spent.**  The digit runs' arms conclude the same transport as one
step's obligation (`numFast_step_cells`): `JsonStage2NumFastDigitRuns`'
`intRun_step_loop`, `intRun_step_exit` and `intRun_step_end230` carry the cells
their starting state had through one iteration's jumps, and
`JsonStage2NumFastCellsRun` conjoins them to the loop's invariant and exit word,
so the integer run's end-of-lexeme exit names the caller's cells.  The fraction
run's arms conclude the integer part's cells the same way
(`fracRun_step_loop`/`_exit`/`_end230`, with `numFast_step_intPart`), which is
what names `%idig.4`/`%ip.5` at the merge past it.  The dispatch's
sign word is `numFastSignWord`, defined here because the run's start and the
store's operand both read it.

**The generic form.**  The counted form of the same chain is `LoopFuel`'s `Path`,
generalised over the function with its count as `Path.length`.  A path at the
pinned body is handed to this module's users by `NumFastChain.ofPath`, and the
step's write-set fact is `PathTransport.step_lookupName` at `numFastBody`, which
is `numFast_step_lookup`.  A caller that wants its own fact at a loop's exit,
rather than a chain's end states, states it with `LoopFuel`'s `BoundLoopFrame`,
whose two arms conclude the property at their own endpoint
(`JsonStage2NumFastCellsRun`).

**Superseded.**  `JsonStage2NumFastSign`'s chain carried the sign alone, with
`if.end` the one block its steps had to avoid; the chain here takes the cells as
a parameter, so the same induction carries the sign, the three kept cells, or
both.  `JsonStage2NumFastSign` keeps the tie (`sign_tie`), which is the *value*
the sign carries rather than its transport.

There is no `sorry`, `admit` or `native_decide` below.
-/
import LeanLLVM.Refinement.JsonEntrySteps
import LeanLLVM.Refinement.JsonScanLane
import LeanLLVM.Refinement.JsonStage2NumFastScan
import LeanLLVM.Refinement.LoopFuel
import LeanLLVM.Refinement.PathTransport

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval

/-! ### The cells -/

/-- The three cells a caller stages and no block of the body writes: the answer's
address, and the two tables the tier-1 expression loads. -/
def numFastKept : List String := ["%out", "@NUMF_EL1_P10", "@NUMF_EL1_POW10"]

/-- `n` is a name no block of the body writes.  `abbrev`, so the `decide`s below
elaborate against the body rather than against the definition's name.  The
reading is `PathTransport`'s `UnwrittenBy`, stated once over the function. -/
abbrev NumFastUnwritten (n : String) : Prop := UnwrittenBy numFastBody n

/-- `n` is written only by the block named `pc`.  `PathTransport`'s
`WrittenOnlyAt`, at the pinned body. -/
abbrev NumFastWrittenOnlyAt (n pc : String) : Prop := WrittenOnlyAt numFastBody n pc

/-- **`%out` is nobody's destination.**  Closed, so `decide` reads it off the
pinned body. -/
theorem numFast_out_unwritten : NumFastUnwritten "%out" := by decide

/-- **`@NUMF_EL1_P10` is nobody's destination.** -/
theorem numFast_p10_unwritten : NumFastUnwritten "@NUMF_EL1_P10" := by decide

/-- **`@NUMF_EL1_POW10` is nobody's destination.** -/
theorem numFast_pow10_unwritten : NumFastUnwritten "@NUMF_EL1_POW10" := by decide

/-- **The sign's register is `if.end`'s alone.**  The body's one other writer of
`%tobool274.not` would be a `phi` outside `if.end`, and there is none. -/
theorem numFast_tobool_written_at_if_end :
    NumFastWrittenOnlyAt "%tobool274.not" "if.end" := by decide

/-- **The integer part's count is `if.end68`'s alone.**  The merge's `%idig` phi
reads it and writes a differently named cell, so the fraction run's traversal
leaves it. -/
theorem numFast_idig4_written_at_ifEnd68 :
    NumFastWrittenOnlyAt "%idig.4" "if.end68" := by decide

/-- **The integer part's accumulator is `if.end68`'s alone.** -/
theorem numFast_ip5_written_at_ifEnd68 :
    NumFastWrittenOnlyAt "%ip.5" "if.end68" := by decide

/-- Every name in the kept list is unwritten. -/
theorem NumFastUnwritten.of_mem {n : String} (hn : n ∈ numFastKept) :
    NumFastUnwritten n := by
  have h : n = "%out" ∨ n = "@NUMF_EL1_P10" ∨ n = "@NUMF_EL1_POW10" := by
    simpa only [numFastKept, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] using hn
  rcases h with rfl | rfl | rfl
  · exact numFast_out_unwritten
  · exact numFast_p10_unwritten
  · exact numFast_pow10_unwritten

/-! ### The state predicates

The kept cells are read against a reference environment — the one the caller
stages — so a composite states them there rather than at the block it reads them
from.  The sign is a value rather than a reference: it is `if.end`'s `phi`, and
what a reader wants is the word it wrote, not the cell it left. -/

/-- The three kept cells agree with the reference environment. -/
def NumFastKept (env0 : Env) (s : State) : Prop :=
  ∀ n ∈ numFastKept, lookupName s.env n = lookupName env0 n

/-- The sign's cell holds `sign`. -/
def NumFastSign (sign : BitVec 1) (s : State) : Prop :=
  lookupName s.env "%tobool274.not" = some (.int 1 sign)

/-- The dispatch's sign word: `%cmp1 = (%0 != '-')`, `if.end`'s `phi` and the
store's operand.  It is the value `if.end` writes, `evalICmp .ne` of the
lexeme's head byte against `'-'`, so a scan's exit carries it without a reader
having to re-run the dispatch. -/
def numFastSignWord (b : UInt8) : BitVec 1 :=
  evalICmp .ne (JsonScanLane.vByte b) 0x2d#8

/-- The integer part's two cells hold `idig` and `ip`: the count and the
accumulator `if.end68`'s `phi`s leave, which the fraction run carries and the
merge reads. -/
def NumFastIntPart (idig ip : BitVec 64) (s : State) : Prop :=
  lookupName s.env "%idig.4" = some (.int 64 idig) ∧
  lookupName s.env "%ip.5" = some (.int 64 ip)

/-- Both halves: the cells a scan's exit must still name. -/
def NumFastCarried (env0 : Env) (sign : BitVec 1) (s : State) : Prop :=
  NumFastKept env0 s ∧ NumFastSign sign s

/-- The kept cells hold at the state the reference environment is installed at. -/
theorem numFastKept_stateAt (env0 : Env) (s : State) :
    NumFastKept env0 (stateAt env0 s) :=
  fun _ _ => rfl

/-! ### One step

The two facts a step needs are `PathTransport`'s: the terminator leaves the
environment alone (`execTerm_env`) and a block that writes none of `n` leaves it
(`step_lookupName`).  Both are stated there once over the function; the body's
step is their instance at `numFastBody`. -/

/-- **A step's non-interference.**  `PathTransport.step_lookupName` at the pinned
body. -/
theorem numFast_step_lookup {calls : Calls} {s s' : State} {n : String}
    (hs : step calls numFastBody s = .jump s')
    (hno : ∀ b ∈ numFastBody.blocks, b.name = s.pc → ∀ i ∈ b.instrs, i.dst? ≠ some n) :
    lookupName s'.env n = lookupName s.env n :=
  step_lookupName hs hno

/-- **A step preserves the kept cells.**  No block writes them, so the step's own
block does, and the counter fact is `decide`d over the body. -/
theorem numFast_step_kept {calls : Calls} {s s' : State} {env0 : Env}
    (hs : step calls numFastBody s = .jump s') (h : NumFastKept env0 s) :
    NumFastKept env0 s' := by
  intro n hn
  rw [numFast_step_lookup (n := n) hs
    (fun b hb _ => NumFastUnwritten.of_mem hn b hb)]
  exact h n hn

/-- **A step off `if.end` preserves the sign.**  The sign's register is `if.end`'s
written at `if.end` and nowhere else, so a step whose block is not that one
leaves it. -/
theorem numFast_step_sign {calls : Calls} {s s' : State} {sign : BitVec 1}
    (hpc : s.pc ≠ "if.end") (hs : step calls numFastBody s = .jump s')
    (h : NumFastSign sign s) : NumFastSign sign s' := by
  have hno : ∀ b ∈ numFastBody.blocks, b.name = s.pc → ∀ i ∈ b.instrs,
      i.dst? ≠ some "%tobool274.not" :=
    fun b hb hbpc =>
      numFast_tobool_written_at_if_end b hb (by rw [hbpc]; exact hpc)
  show lookupName s'.env "%tobool274.not" = some (.int 1 sign)
  rw [numFast_step_lookup (n := "%tobool274.not") hs hno]
  exact h

/-- **A step's cells.**  One control step from a block that is not `if.end`
carries both the kept cells and the sign: the block writes neither, since the
kept names are nobody's destination and the sign's is `if.end`'s alone. -/
theorem numFast_step_cells {calls : Calls} {s s' : State} {env0 : Env}
    {sign : BitVec 1} (hpc : s.pc ≠ "if.end")
    (hs : LeanLLVM.step calls numFastBody s = .jump s') (h : NumFastCarried env0 sign s) :
    NumFastCarried env0 sign s' :=
  ⟨numFast_step_kept hs h.1, numFast_step_sign hpc hs h.2⟩

/-- **A step off `if.end68` preserves the integer part's cells.** -/
theorem numFast_step_intPart {calls : Calls} {s s' : State} {idig ip : BitVec 64}
    (hpc : s.pc ≠ "if.end68") (hs : LeanLLVM.step calls numFastBody s = .jump s')
    (h : NumFastIntPart idig ip s) : NumFastIntPart idig ip s' := by
  refine ⟨?_, ?_⟩
  · rw [numFast_step_lookup (n := "%idig.4") hs
      (fun b hb hbpc =>
        numFast_idig4_written_at_ifEnd68 b hb (by rw [hbpc]; exact hpc))]
    exact h.1
  · rw [numFast_step_lookup (n := "%ip.5") hs
      (fun b hb hbpc =>
        numFast_ip5_written_at_ifEnd68 b hb (by rw [hbpc]; exact hpc))]
    exact h.2

/-! ### The chain

A finite chain of the body's control steps.  `ok` is the chain's block filter: a
step is admitted only from a block `ok` admits, which is how a chain that must
avoid one block — `if.end`, for the sign — says so in its type.  The kept cells
need no filter: their blocks' freedom is uniform over the body. -/

/-- A finite chain of control steps of the body, each taken from a block `ok`
admits. -/
inductive NumFastChain (calls : Calls) (ok : String → Prop) : State → State → Prop
  /-- The empty chain. -/
  | refl (s : State) : NumFastChain calls ok s s
  /-- One step, then the rest. -/
  | step {s s' e : State} (hok : ok s.pc)
      (hs : LeanLLVM.step calls numFastBody s = .jump s')
      (ht : NumFastChain calls ok s' e) : NumFastChain calls ok s e

/-- **A path's chain.**  `Path` is the counted form of a chain.  At a fixed
function and filter the chain is the `Prop` a region's older users take, so a
caller holding the path hands them one; the chain's own consequences below then
follow. -/
def NumFastChain.ofPath {calls : Calls} {ok : String → Prop} {s e : State}
    (h : Path calls numFastBody ok s e) : NumFastChain calls ok s e :=
  match h with
  | .nil _ => .refl _
  | .step hok hs rest => .step hok hs (NumFastChain.ofPath rest)

/-- **The chain's fuel.**  A chain of `j` steps is a `runFuel` prefix: the run
from the head at `j + k` is the run from the tail at `k`. -/
theorem NumFastChain.runFuel {calls : Calls} {ok : String → Prop} {s e : State}
    (h : NumFastChain calls ok s e) :
    ∃ j, ∀ k, LeanLLVM.runFuel calls (j + k) numFastBody s
      = LeanLLVM.runFuel calls k numFastBody e := by
  induction h with
  | refl s => exact ⟨0, fun k => by simp⟩
  | step _ hs _ ih =>
      obtain ⟨j, hj⟩ := ih
      refine ⟨j + 1, fun k => ?_⟩
      rw [show j + 1 + k = 1 + (j + k) from by omega,
        runFuel_jump_prefix hs, hj]

/-- **The chain's kept cells.**  The three cells no block writes are the same at
both ends of any chain. -/
theorem NumFastChain.kept {calls : Calls} {ok : String → Prop} {env0 : Env}
    {s e : State} (h : NumFastChain calls ok s e) (hs : NumFastKept env0 s) :
    NumFastKept env0 e := by
  induction h with
  | refl s => exact hs
  | step _ hstep _ ih => exact ih (numFast_step_kept hstep hs)

/-- **The chain's sign.**  A chain whose steps avoid `if.end` leaves the sign
where it found it. -/
theorem NumFastChain.sign {calls : Calls} {ok : String → Prop} {sign : BitVec 1}
    {s e : State} (hok : ∀ pc, ok pc → pc ≠ "if.end") :
    NumFastChain calls ok s e → NumFastSign sign s → NumFastSign sign e := by
  intro h
  induction h with
  | refl s => exact id
  | step hokpc hstep _ ih =>
      exact fun hs => ih (numFast_step_sign (hok _ hokpc) hstep hs)

/-- Two chains in sequence. -/
theorem NumFastChain.append {calls : Calls} {ok : String → Prop} {s m e : State}
    (h1 : NumFastChain calls ok s m) :
    NumFastChain calls ok m e → NumFastChain calls ok s e := by
  induction h1 with
  | refl _ => exact id
  | step hokpc hstep _ ih => exact fun h2 => .step hokpc hstep (ih h2)

/-- One step's chain, at a block the filter admits. -/
theorem NumFastChain.single {calls : Calls} {ok : String → Prop} {s s' : State}
    (hok : ok s.pc) (hs : LeanLLVM.step calls numFastBody s = .jump s') :
    NumFastChain calls ok s s' :=
  .step hok hs (.refl s')


/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.numFast_out_unwritten' does not depend on any axioms -/
#guard_msgs in
#print axioms numFast_out_unwritten

/-- info: 'LeanLLVM.Refinement.numFast_tobool_written_at_if_end' does not depend on any axioms -/
#guard_msgs in
#print axioms numFast_tobool_written_at_if_end

/-- info: 'LeanLLVM.Refinement.numFast_idig4_written_at_ifEnd68' does not depend on any axioms -/
#guard_msgs in
#print axioms numFast_idig4_written_at_ifEnd68

/-- info: 'LeanLLVM.Refinement.numFast_ip5_written_at_ifEnd68' does not depend on any axioms -/
#guard_msgs in
#print axioms numFast_ip5_written_at_ifEnd68

/-- info: 'LeanLLVM.Refinement.numFast_step_lookup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numFast_step_lookup

/-- info: 'LeanLLVM.Refinement.NumFastChain.kept' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NumFastChain.kept

/-- info: 'LeanLLVM.Refinement.NumFastChain.sign' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NumFastChain.sign

/-- info: 'LeanLLVM.Refinement.numFast_step_intPart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numFast_step_intPart

/-- info: 'LeanLLVM.Refinement.numFast_step_cells' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms numFast_step_cells

/-- info: 'LeanLLVM.Refinement.NumFastChain.runFuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NumFastChain.runFuel

end LeanLLVM.Refinement
