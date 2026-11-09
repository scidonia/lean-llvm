/-
The lanes loop, re-closed with the memory it does not write.

`JsonEscapeListLoop` closes `do.body.i` on `LoopFuel`'s induction carrying the word
and the frame of *registers* the next block reads (`lstLanesKeeps`).  The exit block
`xl_lanes.exit` reads more than registers: it reads the caller's memory and it
stores into it, and the block after it reads the count's slot and the stream.  The
loop's own `ExitWord` says nothing about the exit state's memory, because
`runFuel (j + k) σ = runFuel k e` is a statement about fuel and a prefix, not about
the state `e`'s fields — nothing in the tree forces `e.mem = σ.mem`.

That is the fact this module adds.  `do.body.i` runs a `phi`, three register
operations and an `icmp`, so it writes no byte; the exit state's memory is the entry
state's.  The re-closing is an instance of the *same* induction with the memory
and the stream's second carry slot `%arrayidx1` added to `Inv` and `ExitWord` —
`entry` set that slot to `%carry + 8` and the loop leaves it alone.  It is a
new `CarriedLoop`, not an edit to `ListLoop`: the earlier instance is the loop with
what its own exit block needs, and this one is the loop with what the *emitter* needs,
stated by the module that traces the emitter.

The bound and the word are untouched: `N = 32` is the lane width's closure bound,
and the identification with `specRunStarts` is applied once to the fixed iterate the
induction hands back, exactly as `lanes_run` does.
-/
import LeanLLVM.Vellum.JsonEscapeListRun
import LeanLLVM.Vellum.JsonEscapeBatchEntries
import LeanLLVM.Vellum.LoopFuel

set_option maxRecDepth 8000

namespace LeanLLVM.Vellum

open LeanLLVM
open LeanLLVM.Vellum.JsonEscapeIR
open LeanLLVM.Vellum.JsonS1MasksIR
open LeanLLVM.Vellum.JsonEscapeIntrinsics
open LeanLLVM.Vellum.BitLanes

/-! ### The invariant, with the memory

`Inv` keeps `ListLoop`'s statement and adds the state's memory and the one cell the
loop never restates.  `ExitWord` keeps the word and the register frame and adds the
same two. -/

/-- The lanes loop's invariant with the memory it carries unchanged and the second
carry slot it never writes. -/
def lstLanesInvM (bs : BitVec 64) (prevb prevs : Bool) (env0 : Env) (mem : Mem)
    (i : Nat) (s : State) (w : BitVec 64) : Prop :=
  lstLanesInv bs prevb prevs env0 i s w ∧ s.mem = mem ∧
    lookupName s.env "%arrayidx1" = lookupName env0 "%arrayidx1"

/-- What the loop leaves, with the memory and the second carry slot the emitter
reads.  `%arrayidx1` is stated against the entry environment because `entry` is what
binds it (`%carry + 8`) and `do.body.i` binds only the five names it computes. -/
def lstLanesExitWordM (env0 : Env) (mem : Mem) (s : State) (w : BitVec 64) : Prop :=
  lstLanesExitWord env0 s w ∧ s.mem = mem ∧
    lookupName s.env "%arrayidx1" = lookupName env0 "%arrayidx1"

/-! ### The head block leaves the stream and the second carry slot alone

`ld5` is a binding prefix over `%e.1.i`, `%shl21.i`, `%and22.i`, `%or23.i` and
`%cmp24.not.i`; every other name is the incoming environment's. -/

/-- The loop's binding prefix does not reach `%arrayidx1`. -/
theorem ld5_arrayidx1 (env : Env) (bs w : BitVec 64) :
    lookupName (ld5 env bs w) "%arrayidx1" = lookupName env "%arrayidx1" := by
  ld_simp
  repeat rw [lookupName_cons_ne _ _ (by decide)]

/-- The successor state of the head block, as the induction's `step` leaves it. -/
def ldSucc (env : Env) (s : State) (bs w : BitVec 64) : State :=
  withEnv (ld5 env bs w)
    { s with pc := (if stepWord bs w = w then "xl_lanes.exit" else "do.body.i"),
             pre := some "do.body.i" }

/-- The successor's memory is the predecessor's: the head writes no byte. -/
theorem ldSucc_mem (env : Env) (s : State) (bs w : BitVec 64) :
    (ldSucc env s bs w).mem = s.mem := rfl

theorem ldSucc_arrayidx1 (env : Env) (s : State) (bs w : BitVec 64) (env0 : Env)
    (h : lookupName env "%arrayidx1" = lookupName env0 "%arrayidx1") :
    lookupName (ldSucc env s bs w).env "%arrayidx1" = lookupName env0 "%arrayidx1" := by
  show lookupName (ld5 env bs w) "%arrayidx1" = _
  rw [ld5_arrayidx1]; exact h

theorem ldSucc_pc_head (env : Env) (s : State) (bs w : BitVec 64)
    (hfix : stepWord bs w ≠ w) : (ldSucc env s bs w).pc = "do.body.i" := by
  unfold ldSucc withEnv; simp [hfix]

theorem ldSucc_pc_exit (env : Env) (s : State) (bs w : BitVec 64)
    (hfix : stepWord bs w = w) : (ldSucc env s bs w).pc = "xl_lanes.exit" := by
  unfold ldSucc withEnv; simp [hfix]

/-! ### The loop, as a `CarriedLoop` with the memory -/

/-- The lanes loop with the exit state's memory and second carry slot: the same
map, seed and bound, and `Inv`/`ExitWord` carrying the two facts the emitter's
entrance needs. -/
def lstLanesLoopM (bs : BitVec 64) (prevb prevs : Bool) (env0 : Env) (mem : Mem) :
    CarriedLoop escapeCalls escapeListFunction where
  head := "do.body.i"
  exitBlock := "xl_lanes.exit"
  map := stepWord bs
  seed := escapeSeed bs prevb prevs
  N := 32
  Inv := lstLanesInvM bs prevb prevs env0 mem
  ExitWord := lstLanesExitWordM env0 mem
  step_exit := by
    intro i s w h hfix
    obtain ⟨hinv, hmem, harr⟩ := h
    obtain ⟨hpc, hmask, ⟨p, op, hpre, hinc, hop⟩, _hiter, _hbound, hkeeps⟩ := hinv
    obtain ⟨hstep, hkeeps', _hmask', he, _hor⟩ :=
      lstDoBody_step s.env s bs w p op env0 hpc hpre hinc hop hmask hkeeps
    refine ⟨ldSucc s.env s bs w, hstep, ldSucc_pc_exit s.env s bs w hfix,
      ⟨he, hkeeps'⟩, ?_, ?_⟩
    · exact ldSucc_mem s.env s bs w ▸ hmem
    · exact ldSucc_arrayidx1 s.env s bs w env0 harr
  step_loop := by
    intro i s w h hfix
    obtain ⟨hinv, hmem, harr⟩ := h
    obtain ⟨hpc, hmask, ⟨p, op, hpre, hinc, hop⟩, hiter, hbound, hkeeps⟩ := hinv
    obtain ⟨hstep, hkeeps', hmask', he, hor⟩ :=
      lstDoBody_step s.env s bs w p op env0 hpc hpre hinc hop hmask hkeeps
    refine ⟨ldSucc s.env s bs w, hstep, ldSucc_pc_head s.env s bs w hfix, ?_,
      ldSucc_mem s.env s bs w ▸ hmem, ldSucc_arrayidx1 s.env s bs w env0 harr⟩
    have hi32 : i ≠ 32 := by
      intro h32
      refine hfix ?_
      rw [hiter, h32]
      exact stepN_32_is_fixed bs prevb prevs
    refine ⟨by simp only [ldSucc, hfix]; rfl, hmask',
      ⟨"do.body.i", .reg "%or23.i", rfl, ?_, ?_⟩, ?_, by omega, hkeeps'⟩
    · decide
    · show evalOperand (withEnv (ld5 s.env bs w)
        { s with pc := (if stepWord bs w = w then "xl_lanes.exit" else "do.body.i"),
                 pre := some "do.body.i" }) (.reg "%or23.i") = some (.int 64 (stepWord bs w))
      simpa only [withEnv, evalOperand] using hor
    · rw [hiter, stepN_succ]
  word_iterate := by
    intro i s w h
    rw [h.1.2.2.2.1, stepN_eq_iter]
  bound := by
    intro i s w h
    exact h.1.2.2.2.2.1
  fixed := by
    intro s w h
    obtain ⟨_hpc, _hmask, _hphi, hiter, _hbound, _hkeeps⟩ := h.1
    rw [hiter]
    exact stepN_32_is_fixed bs prevb prevs

/-! ### The loop's run, with the memory and the second carry slot

`CarriedLoop.run_from` does the induction; what is left is the one application of
`stepN_fixed_eq_specRunStarts` to the fixed iterate it hands back. -/

/-- **The lanes loop, with the memory, from iteration `i`.**  The run reaches
`xl_lanes.exit` within `32 - i + 1` control steps, carrying the rule's word, the
unchanged memory, and `%arrayidx1`'s value from the entry environment. -/
theorem lanes_mem_run (bs : BitVec 64) (prevb prevs : Bool) (env0 : Env) (mem : Mem)
    (i : Nat) (σ : State) (w : BitVec 64)
    (hinv : lstLanesInvM bs prevb prevs env0 mem i σ w) (k : Nat) :
    ∃ (e : State) (j : Nat), j ≤ 32 - i + 1 ∧ e.pc = "xl_lanes.exit" ∧
      lstLanesExitWordM env0 mem e (specRunStarts bs (prevb && prevs)) ∧
      runFuel escapeCalls (j + k) escapeListFunction σ =
        runFuel escapeCalls k escapeListFunction e := by
  obtain ⟨e, j, d, hj, hd, hpc, hexit, hfix, hrun⟩ :=
    (lstLanesLoopM bs prevb prevs env0 mem).run_from (32 - i) i σ w hinv rfl
  obtain hrun := hrun k
  refine ⟨e, j, hj, hpc, ?_, hrun⟩
  have hword : iter (stepWord bs) d (escapeSeed bs prevb prevs) =
      specRunStarts bs (prevb && prevs) := by
    rw [← stepN_eq_iter]
    exact stepN_fixed_eq_specRunStarts bs prevb prevs d (by rwa [stepN_eq_iter])
  have hexit' : lstLanesExitWordM env0 mem e
      (iter (stepWord bs) d (escapeSeed bs prevb prevs)) := hexit
  rw [hword] at hexit'
  exact hexit'

/-- **The lanes loop, with the memory, from its head**: thirty-one control steps
from `do.body.i` at iteration two. -/
theorem lanes_mem_run_from_head (bs : BitVec 64) (prevb prevs : Bool) (env0 : Env)
    (mem : Mem) (σ : State)
    (hinv : lstLanesInvM bs prevb prevs env0 mem 2 σ
      (stepN bs 2 (escapeSeed bs prevb prevs))) (k : Nat) :
    ∃ (e : State) (j : Nat), j ≤ 31 ∧ e.pc = "xl_lanes.exit" ∧
      lstLanesExitWordM env0 mem e (specRunStarts bs (prevb && prevs)) ∧
      runFuel escapeCalls (j + k) escapeListFunction σ =
        runFuel escapeCalls k escapeListFunction e :=
  lanes_mem_run bs prevb prevs env0 mem 2 σ _ hinv k

/-- **The lanes loop at its bound, with the memory.**  From the head the run
completes at thirty-one control steps plus the emitter's own fuel. -/
theorem lanes_mem_run_at (bs : BitVec 64) (prevb prevs : Bool) (env0 : Env) (mem : Mem)
    (σ : State) (k : Nat)
    (hinv : lstLanesInvM bs prevb prevs env0 mem 2 σ
      (stepN bs 2 (escapeSeed bs prevb prevs)))
    {o : Outcome}
    (hcont : ∀ (e : State) (_j : Nat), e.pc = "xl_lanes.exit" →
      lstLanesExitWordM env0 mem e (specRunStarts bs (prevb && prevs)) →
      runFuel escapeCalls k escapeListFunction e = some o) :
    runFuel escapeCalls (31 + k) escapeListFunction σ = some o := by
  obtain ⟨e, j, hj, hpc, hexit, hrun⟩ := lanes_mem_run_from_head bs prevb prevs env0 mem σ hinv k
  have hone : runFuel escapeCalls (j + k) escapeListFunction σ = some o := by
    rw [hrun]
    exact hcont e j hpc hexit
  exact runFuel_mono_le (by omega) hone

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Vellum.lstLanesInvM' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lstLanesInvM

/-- info: 'LeanLLVM.Vellum.lstLanesExitWordM' does not depend on any axioms -/
#guard_msgs in
#print axioms lstLanesExitWordM

/-- info: 'LeanLLVM.Vellum.ld5_arrayidx1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ld5_arrayidx1

/-- info: 'LeanLLVM.Vellum.lstLanesLoopM' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lstLanesLoopM

/-- info: 'LeanLLVM.Vellum.lanes_mem_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lanes_mem_run

/-- info: 'LeanLLVM.Vellum.lanes_mem_run_from_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lanes_mem_run_from_head

/-- info: 'LeanLLVM.Vellum.lanes_mem_run_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lanes_mem_run_at

end LeanLLVM.Vellum
