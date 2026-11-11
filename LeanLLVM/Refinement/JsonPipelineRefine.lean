/-
The assembled pipeline's refinement: one induction over its block loop.

`JsonPipelineContract` states the record the assembled body satisfies,
`Γ_pipeline_units`, and `JsonPipelineIR` pins the body and the call environment
the six units are reached through.  This module puts the two together: the
pipeline's own theorem is **one** induction over the block loop, and the
per-unit obligations it consumes are a **named bundle** — `PipelineUnits` — one
`CallSatisfies` per symbol at the arguments the body actually passes.

**Why the bundle and not six hypotheses.**  A per-unit refinement list says each
unit is fine and says nothing about the assembled program: a per-block call with
the wrong argument staging satisfies all six unit theorems.  The bundle is
therefore read at the pipeline's own call environment — `pipelineCalls tab base s2`,
which resolves each symbol to that unit's body, environment and record — so a
member is a fact about the pipeline's call site, and the induction below is the
only place a unit is consumed.

**Why an induction of its own rather than `BoundLoop`.**  `LoopFuel.BoundLoop`'s
`step_loop` concludes `e.pc = head`, a single block name; the pipeline's loop is
the arm-specialised body in four copies, so the block a running iteration sits at
depends on the arm the entry block selected (`for.body.us.us`, `for.body.us`,
`for.body.us83`, `for.body`).  A structure whose `head` is one name cannot hold
them.  `PipelineLoop` below is `BoundLoop` with the block name dropped and the
arm carried inside the invariant: the step is stated as a `runFuel` prefix from
one invariant state to the next, exactly as `BoundLoop`'s is, and the induction
consumes nothing else.  Its exit is a predicate, as `BoundLoop`'s is, so the arm
that leaves for `for.cond.cleanup` needs no separate instance.

**What is proved here, and what the bundle costs.**  `PipelineUnits` is
inhabited by the unit records themselves (`pipelineUnits_of_records`): five of
its members are `satisfies_calls`/`satisfies_calls_void` applied to the units'
own `Satisfies` theorems, and the sixth is the stage-2 slot, which has no body in
this tree and is therefore the caller's.  `pipeline_satisfies_of_units` is the
pipeline's `Satisfies` at `Γ_pipeline_units`, from that bundle and the body's
own remaining facts (`PipelineBodyFacts`: the loop instance, the three steps that
reach it, and the tail that carries an exit state to the record's post) — the
bundle is passed to that analysis, because consuming a member is what the arm and
tail traces do.

The mask call site is derived here rather than left to that analysis:
`masksPre_of_stagingWindow` is `Γ_masks.pre` at `[.ptr (b + 64 * i), .ptr sc,
.ptr mk]` from the staging's document window, its `3 ≤ b`, its carry slot and the
three separations `pipelineRegions` states — every hypothesis a clause of the
record, none a second promise.  The other three call sites need the same
derivation from clauses this file does not yet assemble: the POS8 and B8 emitters'
`pre` reads the entry stream at `entw` after the loop body's store and needs the
cursor left by the preceding iteration; the escape list's needs the count slot
the preceding iteration wrote; and the UTF-8 stage's is the window the staging's
`b - 3` clause states, with the tail's `0 < n`.  Each is a statement about the
invariant's carried cursors, so each belongs with the arm trace that carries them.

**Nothing here identifies the verdict with the reference parser.**  That is
`Σ_pipeline`'s and D2's, as `JsonPipelineContract`'s docstring says.  The
finalisation at the end of this module carries the identification as the named
predicate `ParserHalfForOutcome` and derives the specification's post from the
units' record around it.

**The parser predicate is indexed by the outcome, not by its verdict.**  An
earlier statement of the bridge took the parser half quantified over the
document, the returned memory *and the verdict*: one readable document then
supplied the acceptance equivalence at `1` and at `0`, so the premise was
inhabited by nothing — `LeanLLVMTest.Counterexamples.pipeline_parser_hsem_false`
is the regression that says so, and
`pipeline_units_finalisation_hsem_false` states the same for the finalisation's
own retired premise.  `ParserHalfForOutcome` reads the verdict, the returned
memory and the caller's slots out of the run's outcome and argument list, so a
run that returned `1` supplies the half at `1` and says nothing at `0`.
-/
import LeanLLVM.Refinement.JsonPipelineContract
import LeanLLVM.Refinement.JsonPipelineBlockEval
import LeanLLVM.Refinement.JsonPipelineSpec
import LeanLLVM.Refinement.LoopFuel

set_option autoImplicit false
set_option maxRecDepth 16000

namespace LeanLLVM.Refinement

open LeanLLVM

/-! ### The block-loop induction

`BoundLoop` without the block name: the four unswitched copies of the loop body
have four heads, and an induction over the block loop must carry the arm rather
than lay down four instances of itself.  The step is a `runFuel` prefix from one
invariant state to the next, so one iteration may cross the entry arm's two
selection blocks as well as sit in a self-looping body block; its cost is a term
of the caller's arguments, and the loop's whole fuel is `(N + 1) * cost`. -/

/-- An induction over a block loop whose body block depends on a value the loop
carries: the arm-specialised body in four copies.

`Inv mem r s` is the invariant with `r` iterations of budget left at the caller's
memory `mem`, `Exit mem s` names every state the loop may leave in (a disjunction
when the loop has a success path and a refusal path, or four heads when the body is
unswitched) *at* that same caller's memory, and the two arms are `runFuel` prefixes
at an exact count bounded by `cost`.  Nothing names a block: which block a state is
at is the invariant's business.

`Exit` takes the caller's memory because what the exit promises is a relation
between the memory the loop was entered at and the memory it leaves: the bytes
outside the loop's own writes are the caller's.  Stated at the state alone the
predicate says nothing about that relation, and an exit state in an empty memory —
one whose registers are bound and whose memory holds nothing — satisfies it while
no tail block can run from it.

It takes the caller's *argument list* for the same reason, one layer on: the exit's
frame names the carried record's write addresses, while the tail's claims — the
UTF-8 window, stage 2's staging, the record's post — are about the caller's.  A
predicate that cannot name the caller cannot say the two are the same addresses, so
`Inv`, `step` and `exit` take the list too: `exit : Inv mem args 0 s → ∃ e, Exit
mem args e` cannot produce an argument-tied exit from an argument-free invariant. -/
structure PipelineLoop (calls : Calls) (f : Function) where
  /-- The loop's iteration bound, a term of the caller's arguments. -/
  N : Nat
  /-- The per-iteration control-step bound, a term of the caller's arguments. -/
  cost : Nat
  /-- The invariant: with `r` iterations of budget left, the state is the loop's
  next iteration, carrying whatever the arm selected needs.  The caller's memory
  is an index and not part of the state, because the loop's frame — what the run
  leaves of the caller's staging where it wrote nothing — is a relation between
  that memory and the state's, and a state cannot name it.  The caller's argument
  list is an index for the same reason: the exit's claims are about the caller's
  buffers, and the state's cells are the carried record's addresses until the
  seed says which caller they came from. -/
  Inv : Mem → List Value → Nat → State → Prop
  /-- The states the loop may leave in, at the caller's memory and arguments. -/
  Exit : Mem → List Value → State → Prop
  /-- One iteration: from a state with `r + 1` iterations left, the run reaches a
  state with `r` left within `cost` control steps. -/
  step : ∀ (mem : Mem) (args : List Value) (r : Nat) (s : State),
    Inv mem args (r + 1) s →
    ∃ (e : State) (j : Nat), j ≤ cost ∧ Inv mem args r e ∧
      ∀ k, runFuel calls (j + k) f s = runFuel calls k f e
  /-- The last iteration reaches a state `Exit` admits, at the same memory and
  arguments. -/
  exit : ∀ (mem : Mem) (args : List Value) (s : State), Inv mem args 0 s →
    ∃ (e : State) (j : Nat), j ≤ cost ∧ Exit mem args e ∧
      ∀ k, runFuel calls (j + k) f s = runFuel calls k f e

/-- **The induction.**  From an invariant state with `r` iterations of budget,
the run reaches an exit state within `(r + 1) * cost` control steps.  The
recursion consumes the two arms only; the arm the entry block selected appears
wherever the invariant puts it, so the four copies are one induction. -/
theorem PipelineLoop.run_from {calls : Calls} {f : Function} (L : PipelineLoop calls f)
    (mem : Mem) (args : List Value) :
    ∀ (r : Nat) (s : State), L.Inv mem args r s →
      ∃ (e : State) (j : Nat), j ≤ (r + 1) * L.cost ∧ L.Exit mem args e ∧
        ∀ k, runFuel calls (j + k) f s = runFuel calls k f e
  | 0, s, h => by
      obtain ⟨e, j, hj, hexit, hrun⟩ := L.exit mem args s h
      exact ⟨e, j, by simpa using hj, hexit, hrun⟩
  | r + 1, s, h => by
      obtain ⟨e, j, hj, hinv, hrun⟩ := L.step mem args r s h
      obtain ⟨e', j', hj', hexit', hrun'⟩ := L.run_from mem args r e hinv
      refine ⟨e', j + j', ?_, hexit', fun k => ?_⟩
      · rw [Nat.succ_mul]
        omega
      · rw [show j + j' + k = j + (j' + k) from by omega, hrun (j' + k)]
        exact hrun' k

/-- The loop from its head, at the whole bound as its budget: the run reaches an
exit state within `(N + 1) * cost` control steps. -/
theorem PipelineLoop.run {calls : Calls} {f : Function} (L : PipelineLoop calls f)
    (mem : Mem) (args : List Value) (s : State) (h : L.Inv mem args L.N s) (k : Nat) :
    ∃ (e : State) (j : Nat), j ≤ (L.N + 1) * L.cost ∧ L.Exit mem args e ∧
      runFuel calls (j + k) f s = runFuel calls k f e := by
  obtain ⟨e, j, hj, hexit, hrun⟩ := L.run_from mem args L.N s h
  exact ⟨e, j, hj, hexit, hrun k⟩

/-- A budget at the bound, not at the trip count: a completed continuation from
any exit state lifts to the loop's head at `(N + 1) * cost + k`.  Only a
completed continuation can be lifted, because the exit is a jump and `runFuel`
past it executes the next block. -/
theorem PipelineLoop.run_at {calls : Calls} {f : Function} (L : PipelineLoop calls f)
    (mem : Mem) (args : List Value) (s : State) (h : L.Inv mem args L.N s) (k : Nat)
    {o : Outcome}
    (hcont : ∀ (e : State), L.Exit mem args e → runFuel calls k f e = some o) :
    runFuel calls ((L.N + 1) * L.cost + k) f s = some o := by
  obtain ⟨e, j, hj, hexit, hrun⟩ := L.run mem args s h k
  have hone : runFuel calls (j + k) f s = some o := by
    rw [hrun]
    exact hcont e hexit
  exact runFuel_mono_le (by omega) hone

end LeanLLVM.Refinement

/-! ### The per-unit bundle -/

namespace LeanLLVM.Refinement.JsonPipelineIR

open LeanLLVM.Refinement
open LeanLLVM.Refinement.JsonEntryIR (entryCalls entryPos8Function entryB8Function)
open LeanLLVM.Refinement.JsonS1MasksIR (s1Calls s1MasksFunction)
open LeanLLVM.Refinement.JsonUtf8IR (utf8Calls utf8Function)
open LeanLLVM.Refinement.JsonEscapeIR (escapeListCalls escapeListFunction)

/-- `CallSatisfies` is stated at a symbol, so it is invariant under the identity
of the selection at that symbol: an equality of functions at `sym` carries one
site's guarantee to another vocabulary for the same site.  This is what lets the
bundle read each unit at `pipelineCalls`'s own branch rather than at the
`envForUnit` term the unit's theorem mentions. -/
theorem CallSatisfies_congr {c c' : Calls} {Γ : MemContract} {sym : String}
    (h : c sym = c' sym) (hs : CallSatisfies c Γ sym) : CallSatisfies c' Γ sym := by
  intro args mem next hpre
  rw [← h]
  exact hs args mem next hpre

/-! ### The environment resolves each symbol

One equality per symbol, each the `if` chain's own branch: the pipeline's call
environment is not unfolded at a call site, so these are what identify the
selection a member's `CallSatisfies` is stated at.  `pipelineCalls_masks` is
`JsonPipelineIR`'s own; the five here are its siblings. -/

theorem pipelineCalls_pos8 (tab base : Nat) (s2 : Calls) :
    pipelineCalls tab base s2 entryPos8Sym = envForPos8 tab entryCalls entryPos8Sym := by
  funext args mem next
  simp only [pipelineCalls, masksSym, entryPos8Sym, entryB8Sym, escapeListSym,
    utf8Sym, stage2Sym]
  rfl

theorem pipelineCalls_b8 (tab base : Nat) (s2 : Calls) :
    pipelineCalls tab base s2 entryB8Sym =
      envForUnit entryB8Sym Γ_entry_b8 entryCalls entryB8Function entryB8Sym := by
  funext args mem next
  simp only [pipelineCalls, masksSym, entryPos8Sym, entryB8Sym, escapeListSym,
    utf8Sym, stage2Sym]
  rfl

theorem pipelineCalls_escape (tab base : Nat) (s2 : Calls) :
    pipelineCalls tab base s2 escapeListSym =
      envForUnit escapeListSym (Γ_escape_positions base escapePositionsBudget)
        (escapeListCalls Γ_xl_batch) escapeListFunction escapeListSym := by
  funext args mem next
  simp only [pipelineCalls, masksSym, entryPos8Sym, entryB8Sym, escapeListSym,
    utf8Sym, stage2Sym]
  rfl

theorem pipelineCalls_utf8 (tab base : Nat) (s2 : Calls) :
    pipelineCalls tab base s2 utf8Sym =
      envForUnit utf8Sym Γ_utf8 utf8Calls utf8Function utf8Sym := by
  funext args mem next
  simp only [pipelineCalls, masksSym, entryPos8Sym, entryB8Sym, escapeListSym,
    utf8Sym, stage2Sym]
  rfl

/-- The stage-2 slot's branch: the pipeline's environment forwards the symbol to
the caller's selection unchanged, so the slot's own `CallSatisfies` is a member
of the pipeline's bundle without re-derivation. -/
theorem pipelineCalls_stage2 (tab base : Nat) (s2 : Calls) :
    pipelineCalls tab base s2 stage2Sym = s2 stage2Sym := by
  funext args mem next
  simp only [pipelineCalls, masksSym, entryPos8Sym, entryB8Sym, escapeListSym,
    utf8Sym, stage2Sym]
  rfl

/-! ### The bundle -/

/-- **The pipeline's per-unit obligations, as one named bundle.**

Each field is a unit's `CallSatisfies` read at `pipelineCalls tab base s2` — the
environment the body calls through, whose `base` is the document's — so a member
is the guarantee at the pipeline's own call site: the arguments the body passes,
the record's budget for them, and the record's post at the outcome.  The escape
list's record is the one field indexed by `base`: its block clause reads the
document at `base + blockAddr blk0`, and the base is `pipeline.h`'s first
argument rather than a reading of the call's own list.  The stage-2 slot is
indexed by the caller's `Γ2` because that unit's *body* is not in this tree;
`JsonStage2Contract` holds the record (`Γ_stage2`), and
`pipeline_satisfies_at_stage2` builds this bundle at it, so what the caller still
supplies is the selection — `stage2Body`, `stage2Calls` and `stage2_satisfies`.

`stage2_verdict_bounded` is the one clause that is not a `CallSatisfies`: the
pipeline's post asserts the returned verdict is the ABI's accept/refuse word, and
on the `if.end34` arm that word is stage 2's return value.  `CallSatisfies`
exposes `Γ2.post` and nothing about the word, so the content the post's disjunct
needs is stated as its own named clause rather than read into `Γ2`'s post or
re-derived at the call site. -/
structure PipelineUnits (tab base : Nat) (s2 : Calls) (Γ2 : MemContract) where
  /-- The mask unit, at `[.ptr p, .ptr sc, .ptr mk]`.  Void-returning, so the
  bridge is `satisfies_calls_void`. -/
  masks : CallSatisfies (pipelineCalls tab base s2) Γ_masks masksSym
  /-- The POS8 entry emitter, at the five arguments the body passes; the staged
  table is appended by `envForPos8`. -/
  pos8 : CallSatisfies (pipelineCalls tab base s2) (Γ_entry_pos8at tab) entryPos8Sym
  /-- The B8 entry emitter, at the five arguments the body passes. -/
  b8 : CallSatisfies (pipelineCalls tab base s2) Γ_entry_b8 entryB8Sym
  /-- The escape-position list, at `[bs, ctl, im, blk0, xp, nxp, xcarry]`.
  Void-returning. -/
  escape : CallSatisfies (pipelineCalls tab base s2)
    (Γ_escape_positions base escapePositionsBudget) escapeListSym
  /-- The UTF-8 stage, at `[b, n, gate]`. -/
  utf8 : CallSatisfies (pipelineCalls tab base s2) Γ_utf8 utf8Sym
  /-- The stage-2 slot, at the caller's selection and record. -/
  stage2 : CallSatisfies (pipelineCalls tab base s2) Γ2 stage2Sym
  /-- The verdict stage 2 returns is the ABI's accept/refuse word. -/
  stage2_verdict_bounded : ∀ (args : List Value) (mem : Mem) (next : Nat)
    (v : Value) (m : Mem), Γ2.post args mem next (.ret (some v) m) →
    ∃ k : BitVec 64, v = .int 64 k ∧ (k = 0 ∨ k = 1)

/-- **The bundle, from the units' own records.**

Five members are discharged here: each is the unit's `Satisfies` theorem through
the bridge its return shape selects — `satisfies_calls_void` for the mask and the
escape list, whose entry points return `void`, and `satisfies_calls` for the two
entry emitters and UTF-8 — re-indexed to `pipelineCalls`'s branch at the symbol
by the resolution lemma above.  `satisfies_calls_pos8` is the POS8 member because
the capture made that emitter's static table a parameter and the pipeline passes
five arguments.

The sixth member and the verdict clause are the caller's: the stage-2 slot has no
body in this tree, so no theorem here can supply them. -/
theorem pipelineUnits_of_records (tab base : Nat) (s2 : Calls) (Γ2 : MemContract)
    (h2 : CallSatisfies s2 Γ2 stage2Sym)
    (h2v : ∀ (args : List Value) (mem : Mem) (next : Nat) (v : Value) (m : Mem),
      Γ2.post args mem next (.ret (some v) m) →
      ∃ k : BitVec 64, v = .int 64 k ∧ (k = 0 ∨ k = 1)) :
    PipelineUnits tab base s2 Γ2 where
  masks := CallSatisfies_congr (pipelineCalls_masks tab base s2)
    (satisfies_calls_void (calls := s1Calls) (body := s1MasksFunction)
      (Γ := Γ_masks) (sym := masksSym) masks_satisfies masks_valueIrrelevant)
  pos8 := CallSatisfies_congr (pipelineCalls_pos8 tab base s2)
    (satisfies_calls_pos8 tab entry_pos8_satisfies (by decide))
  b8 := CallSatisfies_congr (pipelineCalls_b8 tab base s2)
    (satisfies_calls (calls := entryCalls) (body := entryB8Function)
      (Γ := Γ_entry_b8) (sym := entryB8Sym) entry_b8_satisfies (by decide))
  escape := CallSatisfies_congr (pipelineCalls_escape tab base s2)
    (satisfies_calls_void (calls := escapeListCalls Γ_xl_batch)
      (body := escapeListFunction)
      (Γ := Γ_escape_positions base escapePositionsBudget) (sym := escapeListSym)
      (escape_positions_satisfies base)
      (escape_positions_valueIrrelevant base escapePositionsBudget))
  utf8 := CallSatisfies_congr (pipelineCalls_utf8 tab base s2)
    (satisfies_calls (calls := utf8Calls) (body := utf8Function)
      (Γ := Γ_utf8) (sym := utf8Sym) utf8_satisfies (by decide))
  stage2 := CallSatisfies_congr (pipelineCalls_stage2 tab base s2) h2
  stage2_verdict_bounded := h2v

end LeanLLVM.Refinement.JsonPipelineIR

/-! ### The mask call site

The loop body calls the mask unit at `[.ptr (b + 64 * i), .ptr sc, .ptr mk]`, so
the unit's `pre` at that site is a statement about one 64-byte block of the
document, the caller's carry slot, and the three separations `Γ_masks.pre` asks
for.  The lemmas below derive exactly that from the clauses the record's staging
already carries, one clause per hypothesis:

* `hwin` is `pipelineStaging`'s document window (`readBytes mem b (64 * blocks)`),
  and `h3` the `3 ≤ b` its UTF-8 clause states;
* `hsc` is its carry-slot clause, `carrySlot false false false` — `pipeline.h`'s
  "both zero for the first block";
* the three disjunctions are the pairs `pipelineRegions`' `DisjointRegions`
  states at the document window, the carry slot and the mask slot.

Nothing here mentions a register: the block index `m`, the base `b` and the two
slots are the staging's witnesses, which is what makes the site's obligation a
consequence of the record rather than a second promise. -/

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON (Block32)
open LeanLLVM.Refinement.JsonS1MasksIR (block64 carrySlot)

/-- A list of sixty-four bytes is the mask unit's two thirty-two-byte halves: the
decomposition `Γ_masks.pre`'s `lo hi` witnesses need, and the one thing the
mask record takes that the document window does not already carry. -/
theorem block64_exists (bs : List UInt8) (h : bs.length = 64) :
    ∃ lo hi : Block32, block64 lo hi = bs := by
  refine ⟨fun i => bs.get ⟨i.val, by have := i.isLt; omega⟩,
    fun i => bs.get ⟨32 + i.val, by have := i.isLt; omega⟩, ?_⟩
  have h1 : List.ofFn (fun i : Fin 32 => bs.get ⟨i.val, by have := i.isLt; omega⟩) =
      bs.take 32 := by
    apply List.ext_getElem
    · simp [List.length_take, h]
    · intro k hk1 hk2
      rw [List.getElem_ofFn, List.getElem_take]
      simp
  have h2 : List.ofFn (fun i : Fin 32 => bs.get ⟨32 + i.val, by have := i.isLt; omega⟩) =
      bs.drop 32 := by
    apply List.ext_getElem
    · simp [List.length_drop, h]
    · intro k hk1 hk2
      rw [List.getElem_ofFn, List.getElem_drop]
      simp
  rw [block64, h1, h2, List.take_append_drop]

/-- A read at an interior offset: a range that reads back reads back from any
interior offset too, at a length inside it.  This is `readBytes_split` twice —
once to reach the offset, once to cut the prefix of the requested length. -/
theorem readBytes_mid (m : Mem) {addr len i n : Nat} (hi : i + n ≤ len)
    {bs : List UInt8} (h : readBytes m addr len = some bs) :
    ∃ ws : List UInt8, readBytes m (addr + i) n = some ws ∧ ws = (bs.drop i).take n := by
  have hi' : i ≤ len := by omega
  obtain ⟨-, h2⟩ := readBytes_split m addr i (len - i) (by
    rw [Nat.add_sub_of_le hi']; exact h)
  have hl : len - i = n + (len - i - n) := by omega
  rw [hl] at h2
  obtain ⟨h3, -⟩ := readBytes_split m (addr + i) n (len - i - n) h2
  exact ⟨_, h3, rfl⟩

/-- The `m`-th block of the padded document window, as the bytes the mask unit's
`pre` names: the window read at `b`, cut at `64 * m`, sixty-four bytes long. -/
theorem blockRead_of_window {mem : Mem} {b blocks : Nat} {bs pad : List UInt8} {m : Nat}
    (hwin : readBytes mem b (64 * blocks) = some (bs ++ pad))
    (hlen : (bs ++ pad).length = 64 * blocks)
    (hm : m < blocks) :
    ∃ lo hi : Block32, readBytes mem (b + 64 * m) 64 = some (block64 lo hi) := by
  obtain ⟨ws, hws, rfl⟩ :=
    readBytes_mid mem (addr := b) (len := 64 * blocks) (i := 64 * m) (n := 64)
      (by omega) hwin
  have hlen' : (((bs ++ pad).drop (64 * m)).take 64).length = 64 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  obtain ⟨lo, hi, hb⟩ := block64_exists _ hlen'
  exact ⟨lo, hi, by rw [hws, ← hb]⟩

/-- The three separations `Γ_masks.pre` asks for, from the three the staged
regions state: the window's high end and the block's own address, on each side. -/
theorem separated_at_block {b sc mk rest p : Nat} (h3 : 3 ≤ b)
    (hpc : (b - 3) + (3 + rest) ≤ sc ∨ sc + 24 ≤ (b - 3))
    (hpo : (b - 3) + (3 + rest) ≤ mk ∨ mk + 48 ≤ (b - 3))
    (hco : sc + 24 ≤ mk ∨ mk + 48 ≤ sc)
    (hp : p + 64 ≤ b + rest) (hpge : b ≤ p) :
    (p + 64 ≤ sc ∨ sc + 24 ≤ p) ∧ (p + 64 ≤ mk ∨ mk + 48 ≤ p) ∧
      (sc + 24 ≤ mk ∨ mk + 48 ≤ sc) := by
  have hsub : (b - 3) + (3 + rest) = b + rest := by omega
  rw [hsub] at hpc hpo
  refine ⟨?_, ?_, hco⟩
  · rcases hpc with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rcases hpo with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

/-- The mask record's `pre` at one of the loop's blocks, from the four facts a
call site has: the block's bytes, the carry slot, and the three separations. -/
theorem masksPre_at {mem : Mem} {p sc mk : Nat} {lo hi : Block32}
    (hp : readBytes mem p 64 = some (block64 lo hi))
    (hsc : readBytes mem sc 24 = some (carrySlot false false false))
    (hpc : p + 64 ≤ sc ∨ sc + 24 ≤ p)
    (hpo : p + 64 ≤ mk ∨ mk + 48 ≤ p)
    (hco : sc + 24 ≤ mk ∨ mk + 48 ≤ sc) :
    Γ_masks.pre [.ptr p, .ptr sc, .ptr mk] mem 0 := by
  refine ⟨p, sc, mk, lo, hi, ⟨false, false⟩, false, false, rfl, hp, hsc, rfl,
    hpc, hpo, hco⟩

/-- A length is inside its own block count: `n ≤ 64 * pipelineBlocks n`.  This is
what makes the staged window's padding length add up to the block count. -/
theorem le_blocks_mul (n : Nat) : n ≤ 64 * pipelineBlocks n := by
  have h : 64 * ((n + 63) / 64) + (n + 63) % 64 = n + 63 := Nat.div_add_mod (n + 63) 64
  have hmod : (n + 63) % 64 < 64 := Nat.mod_lt _ (by decide)
  simp only [pipelineBlocks]
  omega

/-- **The mask unit's `pre` at the loop's block `m`, from the staging's own
clauses.**  The document window and its padding come from the staging's document
clause, the carry slot from its carry clause, and the three disjunctions from
`pipelineRegions`' pairwise separation; the block index `m` is inside the block
count, so the block's bytes are inside the window. -/
theorem masksPre_of_window {mem : Mem} {b sc mk : Nat} {bs pad : List UInt8}
    (h3 : 3 ≤ b)
    (hwin : readBytes mem b (64 * pipelineBlocks bs.length) = some (bs ++ pad))
    (hlen : (bs ++ pad).length = 64 * pipelineBlocks bs.length)
    (hsc : readBytes mem sc 24 = some (carrySlot false false false))
    (hpc : (b - 3) + (3 + 64 * pipelineBlocks bs.length) ≤ sc ∨ sc + 24 ≤ b - 3)
    (hpo : (b - 3) + (3 + 64 * pipelineBlocks bs.length) ≤ mk ∨ mk + 48 ≤ b - 3)
    (hco : sc + 24 ≤ mk ∨ mk + 48 ≤ sc)
    {m : Nat} (hm : m < pipelineBlocks bs.length) :
    Γ_masks.pre [.ptr (b + 64 * m), .ptr sc, .ptr mk] mem 0 := by
  obtain ⟨lo, hi, hblk⟩ := blockRead_of_window hwin hlen hm
  obtain ⟨hpc', hpo', hco'⟩ :=
    separated_at_block h3 hpc hpo hco (p := b + 64 * m)
      (rest := 64 * pipelineBlocks bs.length) (by omega) (by omega)
  exact masksPre_at hblk hsc hpc' hpo' hco'

/-- The same at the zero-padded window `pipelineStaging` writes down, where the
padding's length is the derivation rather than a hypothesis. -/
theorem masksPre_of_stagingWindow {mem : Mem} {b sc mk : Nat} {bs : List UInt8}
    (h3 : 3 ≤ b)
    (hwin : readBytes mem b (64 * pipelineBlocks bs.length) =
      some (bs ++ List.replicate (64 * pipelineBlocks bs.length - bs.length) 0))
    (hsc : readBytes mem sc 24 = some (carrySlot false false false))
    (hpc : (b - 3) + (3 + 64 * pipelineBlocks bs.length) ≤ sc ∨ sc + 24 ≤ b - 3)
    (hpo : (b - 3) + (3 + 64 * pipelineBlocks bs.length) ≤ mk ∨ mk + 48 ≤ b - 3)
    (hco : sc + 24 ≤ mk ∨ mk + 48 ≤ sc)
    {m : Nat} (hm : m < pipelineBlocks bs.length) :
    Γ_masks.pre [.ptr (b + 64 * m), .ptr sc, .ptr mk] mem 0 := by
  have hlen : (bs ++ List.replicate (64 * pipelineBlocks bs.length - bs.length) 0).length =
      64 * pipelineBlocks bs.length := by
    simp only [List.length_append, List.length_replicate]
    have := le_blocks_mul bs.length
    omega
  exact masksPre_of_window h3 hwin hlen hsc hpc hpo hco hm

end LeanLLVM.Refinement

/-! ### The body's own facts, and the composition

The bundle above is what the units guarantee.  What remains is about the body:
the loop instance (one `PipelineLoop` for the four arm-specialised copies), the
three control steps that reach it, and the tail that carries an exit state to the
record's post.  `PipelineBodyFacts` binds them at one staging, so a hypothesis
about them is a hypothesis about the record's own `pre` and not about an invented
staging — the shape `JsonEscapeExpandRun`'s `ExpandFacts` uses for the same
reason. -/

namespace LeanLLVM.Refinement

open LeanLLVM.Refinement.JsonPipelineIR
open LeanLLVM.JSON (Block32)
open LeanLLVM.Refinement.JsonS1MasksIR (block64 carrySlot)

/-- The document length as the pipeline's argument list carries it: the second
argument, `%n`, read at its own width.  `pipelineBudget` matches the same list,
so the two readings cannot drift. -/
def pipelineArgLen (args : List Value) : Nat :=
  match args with
  | [_, .int 64 n, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] => n.toNat
  | _ => 0

/-- The staging's argument shape, as the body's twenty arguments.  Stated so a
consumer of `pipelineStaging` gets the shape without the twenty-five clauses;
`pipelineBudget`'s match and this one are the same list. -/
theorem pipelineStaging_args {tab base : Nat} {args : List Value} {mem : Mem}
    (h : pipelineStaging tab base args mem) :
    ∃ (sc mk entw ep nk xp nxp xcarry dst ndst ev nev err : Nat)
      (n epcap xpcap dstcap evcap arm : BitVec 64),
      args = [.ptr base, .int 64 n, .ptr sc, .ptr mk, .ptr entw, .ptr ep, .int 64 epcap,
        .ptr nk, .ptr xp, .int 64 xpcap, .ptr nxp, .ptr xcarry, .ptr dst,
        .int 64 dstcap, .ptr ndst, .ptr ev, .int 64 evcap, .ptr nev, .ptr err,
        .int 64 arm] := by
  obtain ⟨sc, mk, entw, ep, nk, xp, nxp, xcarry, dst, ndst, ev, nev, err,
    nxp0, ndst0, nev0, n, epcap, xpcap, dstcap, evcap, arm, bs, hargs, -⟩ := h
  exact ⟨sc, mk, entw, ep, nk, xp, nxp, xcarry, dst, ndst, ev, nev, err,
    n, epcap, xpcap, dstcap, evcap, arm, hargs⟩

/-- **The staging determines the base, and it is the document's address.**

The base is a parameter of `Γ_pipeline_units` and of `pipelineCalls` because
`Satisfies` fixes the call environment before it quantifies over the arguments,
so it cannot be read out of the argument list there.  It is *not* therefore an
asserted value: the staging's own clauses say what it is — the ABI's first
argument (`.ptr base`), the address the padded document window is read at and
whose read-past tail is staged, and the address whose three preceding bytes the
UTF-8 window occupies — and this lemma hands a caller exactly those.  The escape
list's record is indexed by the
same number, and its block clause reads `base + blockAddr blk0`; a base chosen by
inspection rather than taken from here is the defect that clause exists to stop.

The slot order is the pinned ABI's, not assumed: `pipelineBody.params` opens with
`("%b", Ty.ptr)` and `pipeline.h` says the document is `b .. b + n - 1`.
-/
theorem pipelineStaging_base {tab base : Nat} {args : List Value} {mem : Mem}
    (h : pipelineStaging tab base args mem) :
    ∃ (n : BitVec 64) (bs : List UInt8),
      3 ≤ base ∧
      readBytes mem (base - 3) 3 = some (List.replicate 3 0) ∧
      readBytes mem base (64 * pipelineBlocks bs.length) = some
        (bs ++ List.replicate (64 * pipelineBlocks bs.length - bs.length) 0) ∧
      HasBytes mem (base + 64 * pipelineBlocks bs.length) 32 ∧
      ∃ rest : List Value, args = .ptr base :: .int 64 n :: rest := by
  obtain ⟨sc, mk, entw, ep, nk, xp, nxp, xcarry, dst, ndst, ev, nev, err,
    nxp0, ndst0, nev0, n, epcap, xpcap, dstcap, evcap, arm, bs,
    hargs, _hnlen, _hmax, hwin, htail, h3, hpre3, -⟩ := h
  exact ⟨n, bs, h3, hpre3, hwin, htail, _, by rw [hargs]⟩

/-- **The staging stages what the decoder reads past the document.**  The padded
window covers `base .. base + 64 * blocks`, the staging's tail clause covers
`base + 64 * blocks .. + 32`, and the document ends at `base + bs.length` with
`bs.length ≤ 64 * blocks`; a read across that boundary composes the two, so the
thirty-two bytes `Γ_stage2.pre` asks at `b + n` are read back from the staging
alone.  This is the extent `pipelineStaging` used to leave out: its window is
exactly the padded document, and the decoder's last read is the escape
expander's read-past. -/
theorem pipelineStaging_tail {tab base : Nat} {args : List Value} {mem : Mem}
    (h : pipelineStaging tab base args mem) :
    ∃ bs : List UInt8, HasBytes mem (base + bs.length) 32 := by
  obtain ⟨sc, mk, entw, ep, nk, xp, nxp, xcarry, dst, ndst, ev, nev, err,
    nxp0, ndst0, nev0, n, epcap, xpcap, dstcap, evcap, arm, bs,
    hargs, _hlen, _hmax, hwin, htail, -⟩ := h
  refine ⟨bs, ?_⟩
  have hw : bs.length ≤ 64 * pipelineBlocks bs.length := le_blocks_mul bs.length
  have hK : bs.length + (64 * pipelineBlocks bs.length - bs.length) =
      64 * pipelineBlocks bs.length := by omega
  have hwin' : readBytes mem base
      (bs.length + (64 * pipelineBlocks bs.length - bs.length)) =
      some (bs ++ List.replicate (64 * pipelineBlocks bs.length - bs.length) 0) := by
    rw [hK]; exact hwin
  obtain ⟨_, hmid⟩ :=
    readBytes_split mem base bs.length (64 * pipelineBlocks bs.length - bs.length) hwin'
  obtain ⟨vs, hvs⟩ := htail
  have haddr : base + bs.length + (64 * pipelineBlocks bs.length - bs.length) =
      base + 64 * pipelineBlocks bs.length := by omega
  have hcat : readBytes mem (base + bs.length)
      ((64 * pipelineBlocks bs.length - bs.length) + 32) =
      some (((bs ++ List.replicate
        (64 * pipelineBlocks bs.length - bs.length) 0).drop bs.length) ++ vs) := by
    refine JsonEntrySteps.readBytes_append mem
      (64 * pipelineBlocks bs.length - bs.length) (base + bs.length) _ 32 vs hmid ?_
    rw [haddr]; exact hvs
  refine ⟨(((bs ++ List.replicate
    (64 * pipelineBlocks bs.length - bs.length) 0).drop bs.length) ++ vs).take 32, ?_⟩
  rw [show (64 * pipelineBlocks bs.length - bs.length) + 32 =
      32 + (64 * pipelineBlocks bs.length - bs.length) from by omega] at hcat
  exact (readBytes_split mem (base + bs.length) 32
    (64 * pipelineBlocks bs.length - bs.length) hcat).1

-- The ABI's first slot is the document, which is the base the record takes: the
-- pinned AST's parameter list and `pipeline.h`'s "the document is `b .. b + n -
-- 1`" agree, and the staging's first argument clause is `.ptr base` at that slot.
#guard decide (pipelineBody.params.head? = some ("%b", Ty.ptr))

/-- **The record's budget at the document the staging names.**  `pipelineBudget`
is the arguments-only bound `4 * blocks + 16`; this is that term with `blocks`
read off the same argument list, which is what the composition's arithmetic
needs. -/
theorem pipelineBudget_of_staging {tab base : Nat} {args : List Value} {mem : Mem}
    (h : pipelineStaging tab base args mem) :
    pipelineBudget args mem =
      pipelineBlockAllowance * pipelineBlocks (pipelineArgLen args) +
        pipelineFinalisationAllowance := by
  obtain ⟨sc, mk, entw, ep, nk, xp, nxp, xcarry, dst, ndst, ev, nev, err,
    n, epcap, xpcap, dstcap, evcap, arm, hargs⟩ := pipelineStaging_args h
  subst hargs
  rfl

/-- **The body's remaining facts, at one staging.**

`loop` is the block loop: one instance for the four unswitched copies, with its
iteration bound the document's block count and its per-iteration cost inside
`pipelineBlockAllowance`.  `seed` is the three control steps from the entry block
to the loop's first iteration — and the zero-block document's exit, which the
entry test takes before the loop — with the prefix shape the loop's own induction
consumes.  `exit` is the tail: from any state the loop leaves in, the cleanup,
the UTF-8 call, the arm selection and stage 2 (or the zero it returns) reach a
verdict at the record's post.

**`Γ2` is the stage-2 slot, and the record that fills it is `JsonStage2Contract`'s
`Γ_stage2`.**  The parameter is phantom in the fields below: `loop`, `N_eq`,
`cost_le`, `seed` and `exit` are statements about `pipelineCalls tab base s2` and
`pipelineBody`, and none of them names `Γ2`.  `JsonStage2Contract`'s
`pipelineBodyFacts_of_record` states exactly that, so substituting `Γ_stage2` for
the slot is a rename, and `pipeline_satisfies_at_stage2` makes it.

**What the record's arrival closes, and what it does not.**  It closes the
bundle's stage-2 clause: `PipelineUnits`' `stage2_verdict_bounded` was a
hypothesis while the record did not exist, and at `Γ_stage2` it is proved from
the post (`stage2_verdict_bounded`), so a bundle at that record needs only the
stage-2 selection.  It does not close `hbody`, and it cannot: `loop`, `seed` and
`exit` are proofs about `pipelineBody`'s own blocks that the run reaches the post
`Γ_pipeline_units` states — the record states that post, not the proof — and the
stage-2 clauses inside it are about the memory the stage-2 run leaves, which the
tail's traces establish.  It also does not supply the selection, because the body
is still absent: `stage2Body`, `stage2Calls` and `stage2_satisfies`.  A record
invented here so the tail would go through would state stage 2's write set where
it is convenient rather than where it is measured, which is the adapter ruling's
error in the other direction. -/
structure PipelineBodyFacts (tab base : Nat) (s2 : Calls) (Γ2 : MemContract)
    (args : List Value) (mem : Mem) (next : Nat) where
  /-- The block loop, as one induction over the four arm-specialised copies. -/
  loop : PipelineLoop (pipelineCalls tab base s2) pipelineBody
  /-- Its iteration bound is the document's block count. -/
  N_eq : loop.N = pipelineBlocks (pipelineArgLen args)
  /-- Its per-iteration cost is inside the record's per-block allowance. -/
  cost_le : loop.cost ≤ pipelineBlockAllowance
  /-- The entry, the arm selection, and the loop's first iteration (or, for a
  zero-block document, the exit the entry test takes). -/
  seed : ∃ (e : State) (j : Nat), j ≤ 3 ∧
    ((loop.N = 0 ∧ loop.Exit mem args e) ∨ loop.Inv mem args loop.N e) ∧
    ∀ k, runFuel (pipelineCalls tab base s2) (j + k) pipelineBody
      (EntryState pipelineBody args mem next) =
      runFuel (pipelineCalls tab base s2) k pipelineBody e
  /-- The tail: from any exit state, the verdict and **the record's own post**.

  **The post is the record's, not a parameter.**  An earlier shape took
  `post : List Value → Mem → Nat → Outcome → Prop` as a parameter and concluded
  `post args mem next …`; that field is false rather than unproved, because
  `fun _ _ _ _ => False` is one of the predicates it quantified over.  What the
  tail's three blocks establish is the run's outcome and the memory it leaves, and
  the record's `dst`/`ndst`/`ev`/`nev`/`err` clauses are the stage-2 call's own
  post, so the conclusion names `Γ_pipeline_units` and the *proof* is where the
  stage-2 record must be visible: `Γ_stage2` is downstream of this module
  (`JsonStage2Contract` imports `PipelineBodyFacts`), so a bundle at an arbitrary
  `Γ2` cannot discharge this field, and the field is discharged at `Γ_stage2`.
  `Γ2` therefore stays phantom in every other field.

  **What the run needs, and what the predicate supplies.**  `loop.Exit mem args`
  is the predicate, at the caller's memory and arguments.  The three steps are
  proved — `PipelineBodyStep.pipelineExit_run` runs `for.cond.cleanup`, the branch
  and `cleanup` from an exit state and returns a verdict with the branch's memory
  — at the cells the exit block reads and at stage-2's `pre`.  `loop.Exit mem` is
  `pipelineLoopExit mem`, which names the program counter, the predecessor, the
  entry stream (with its document and block bounds), the tail's cells, the exiting
  count, the escape count's slot and growth, and the frame at `mem`
  (`PipelineBodyStep.pipelineLoopExit_cells`, `PipelineLoopCount`).  What it does
  not name is the two calls' inputs — the UTF-8 call's window and stage-2's `pre`
  — and those are consequences of the caller's staging: the loop's frame carries
  the staged bytes to the exit state and the count slot's store is one entry of
  the loop's own write list, so `PipelineDischarge.utf8Pre_of_staging` and
  `PipelineDischarge.stage2Pre_of_exit` derive them at the state's own memory.  The
  whole field, at `Γ_stage2`, is `PipelineDischarge.pipelineTailTarget`. -/
  exit : ∀ (e : State), loop.Exit mem args e →
    ∃ (verdict : BitVec 64) (m : Mem),
      runFuel (pipelineCalls tab base s2) 3 pipelineBody e =
        some (.ret (some (.int 64 verdict)) m) ∧
      (Γ_pipeline_units tab base).post args mem next (.ret (some (.int 64 verdict)) m)

/-- **The assembled pipeline satisfies its unit-level record.**

One theorem about one body: the per-unit obligations arrive as the bundle, and
everything else is the body's own shape, so nothing is assumed twice and no unit
is refined on its own.  The composition is the entry's three steps, the loop's
`(N + 1) * cost` from the induction, and the tail's three steps, which is
`4 * blocks + 16`'s own decomposition: `3 + (blocks + 1) * 1 + 3 ≤ 4 * blocks + 16`
at the bundle's `cost ≤ 4`.

The post is consumed once, at the exit state the loop leaves: every other
behaviour of the run is the same outcome by `runFuel_outcome_unique`, so the
record's post at that outcome is the post at all of them.

The base is quantified here rather than read off the arguments: `Satisfies` fixes
the call environment, so the escape-list record the body is judged against must be
chosen before the argument list is opened.  The staging ties it back — its first
argument clause is `.ptr base`, the ABI's document slot — so a base the caller's
arguments disagree with admits nothing.

**What `hbody` still owes, so that the hypothesis is not read as a gap.**  Its
`loop` and `cost_le` are proved (`PipelineBodyStep.pipelineLoop`, whose `step` is the
four arms' steps per entry shape), `N_eq` is the staging's block count, and `seed`'s
three control steps are proved (`PipelineBodyStep.pipelineSeed`, whose invariant
state carries the staging's regions).  It is stated as a hypothesis here because
this theorem's `Γ2` is arbitrary; at `Γ_stage2` the whole bundle, `exit`
included, is `PipelineDischarge.pipelineBodyFacts_of_exitStage2`.

* `exit`'s conclusion at `Γ_pipeline_units`'s post is the tail's: the cleanup
  block's store and its UTF-8 call, the two refusal branches, and the stage-2 call
  whose post is what the `dst`/`ndst`/`ev`/`nev`/`err` clauses are about.  The post
  is the record's own rather than a parameter of the field: the parameterised shape
  was false, not unproved, and it is retired.  The three steps are
  `PipelineBodyStep.pipelineExit_run` — one `denoteCode` trace per block at the
  exit state's own environment, composed into the three-fuel run, with the stage-2
  record consumed at the call site.  `pipelineLoopExit` supplies the cells, the
  predecessor and the exiting count (`PipelineBodyStep.pipelineLoopExit_cells`,
  `PipelineLoopCount`), and the two calls' inputs are consequences of the caller's
  staging (`PipelineDischarge.utf8Pre_of_staging`, `stage2Pre_of_exit`), so
  `PipelineDischarge.pipelineTailTarget` discharges the field and
  `pipeline_satisfies_at_stage2_of_exitStage2` takes no tail premise.  What the
  loop's exit hands on is the entry stream: the staging pins the count slot to the
  empty stream, the loop's emitters append onto nothing, and
  `PipelineBodyStep.pipelineExit_stream` states the read at the exit's own count,
  so the post's `readLanes32 m ep nk'` is derived from the pre instead of being a
  clause the exit could not reach. -/
theorem pipeline_satisfies_of_units (tab : Nat) (s2 : Calls) (Γ2 : MemContract)
    (units : ∀ base, PipelineUnits tab base s2 Γ2)
    (hbody : ∀ (base : Nat) (args : List Value) (mem : Mem) (next : Nat),
      (Γ_pipeline_units tab base).pre args mem next → PipelineUnits tab base s2 Γ2 →
      PipelineBodyFacts tab base s2 Γ2 args mem next) :
    ∀ base, Satisfies (pipelineCalls tab base s2) pipelineBody (Γ_pipeline_units tab base) := by
  intro base args mem next hpre
  obtain ⟨loop, hN, hcost, seed, hexit⟩ := hbody base args mem next hpre (units base)
  obtain ⟨e0, j0, hj0, hseed, hrun0⟩ := seed
  have hbudget := pipelineBudget_of_staging hpre
  -- the record's own arithmetic, in the block count the loop carries
  have hbudget4 : pipelineBudget args mem = 4 * loop.N + 16 := by
    rw [hbudget, ← hN]
    simp only [pipelineBlockAllowance, pipelineFinalisationAllowance]
  -- the composed outcome, once, from whichever way the seed reaches the loop
  have finish : ∀ (verdict : BitVec 64) (m : Mem) (fuel : Nat),
      runFuel (pipelineCalls tab base s2) fuel pipelineBody
        (EntryState pipelineBody args mem next) =
        some (.ret (some (.int 64 verdict)) m) →
      fuel ≤ pipelineBudget args mem →
      (Γ_pipeline_units tab base).post args mem next (.ret (some (.int 64 verdict)) m) →
      (∃ v m', runFuel (pipelineCalls tab base s2) (pipelineBudget args mem) pipelineBody
        (EntryState pipelineBody args mem next) = some (.ret v m')) ∧
      ∀ o, BehFromState (pipelineCalls tab base s2) pipelineBody
        (EntryState pipelineBody args mem next) o → (Γ_pipeline_units tab base).post args mem next o := by
    intro verdict m fuel hrun hle hpost
    have hb : runFuel (pipelineCalls tab base s2) (pipelineBudget args mem) pipelineBody
        (EntryState pipelineBody args mem next) =
        some (.ret (some (.int 64 verdict)) m) := runFuel_mono_le hle hrun
    refine ⟨⟨some (.int 64 verdict), m, hb⟩, ?_⟩
    intro o ho
    rcases ho with ⟨n, hn⟩ | ⟨n, hn⟩
    · have heq : (.ret (some (.int 64 verdict)) m : Outcome) = .ub :=
        runFuel_outcome_unique hb hn
      cases heq
    · rw [← runFuel_outcome_unique hb hn]
      exact hpost
  rcases hseed with ⟨hN0, hexit0⟩ | hinv
  · -- the zero-block document: the entry test leaves for the cleanup
    obtain ⟨verdict, m, hrun3, hpost3⟩ := hexit e0 hexit0
    have hrunJ : runFuel (pipelineCalls tab base s2) (j0 + 3) pipelineBody
        (EntryState pipelineBody args mem next) = some (.ret (some (.int 64 verdict)) m) := by
      rw [hrun0 3]
      exact hrun3
    refine finish verdict m (j0 + 3) hrunJ ?_ hpost3
    omega
  · -- the loop, at its bound, and the tail
    obtain ⟨e1, j1, hj1, hexit1, hrun1⟩ := loop.run mem args e0 hinv 3
    obtain ⟨verdict, m, hrun3, hpost3⟩ := hexit e1 hexit1
    have hrunJ : runFuel (pipelineCalls tab base s2) (j0 + (j1 + 3)) pipelineBody
        (EntryState pipelineBody args mem next) = some (.ret (some (.int 64 verdict)) m) := by
      rw [hrun0 (j1 + 3), hrun1]
      exact hrun3
    refine finish verdict m (j0 + (j1 + 3)) hrunJ ?_ hpost3
    have hmul : (loop.N + 1) * loop.cost ≤ (loop.N + 1) * pipelineBlockAllowance :=
      Nat.mul_le_mul_left _ hcost
    have hfour : (loop.N + 1) * pipelineBlockAllowance = 4 * loop.N + 4 := by
      rw [pipelineBlockAllowance, Nat.succ_mul]
      omega
    omega

/-- **A member consumed at the loop's block.**  With the mask unit's `pre` at
the arguments the body passes — `masksPre_of_stagingWindow` — the pipeline's call
environment resolves the call and returns an outcome whose post holds, with the
allocator reservation the record promises.  This is the shape every member is
used in: the `pre` from the staging, the record's post out. -/
theorem masksCall_at_block {tab base : Nat} {s2 : Calls} {Γ2 : MemContract}
    (units : PipelineUnits tab base s2 Γ2) {mem : Mem} {next p sc mk : Nat}
    (hpre : Γ_masks.pre [.ptr p, .ptr sc, .ptr mk] mem next) :
    ∃ r : CallOutcome,
      pipelineCalls tab base s2 masksSym [.ptr p, .ptr sc, .ptr mk] mem next = some r ∧
      Γ_masks.post [.ptr p, .ptr sc, .ptr mk] mem next (.ret (some r.ret) r.mem) ∧
      next ≤ r.next :=
  units.masks [.ptr p, .ptr sc, .ptr mk] mem next hpre

/-- **The pipeline's record from the units' own records.**  The bundle is
supplied by `pipelineUnits_of_records`, so the only unit-shaped hypothesis left
is the stage-2 slot — the one callee this tree holds no body for — and its
verdict clause.  Everything else the assembled body does is the body analysis's. -/
theorem pipeline_satisfies_of_records (tab : Nat) (s2 : Calls) (Γ2 : MemContract)
    (h2 : CallSatisfies s2 Γ2 stage2Sym)
    (h2v : ∀ (args : List Value) (mem : Mem) (next : Nat) (v : Value) (m : Mem),
      Γ2.post args mem next (.ret (some v) m) →
      ∃ k : BitVec 64, v = .int 64 k ∧ (k = 0 ∨ k = 1))
    (hbody : ∀ (base : Nat) (args : List Value) (mem : Mem) (next : Nat),
      (Γ_pipeline_units tab base).pre args mem next → PipelineUnits tab base s2 Γ2 →
      PipelineBodyFacts tab base s2 Γ2 args mem next) :
    ∀ base, Satisfies (pipelineCalls tab base s2) pipelineBody (Γ_pipeline_units tab base) :=
  pipeline_satisfies_of_units tab s2 Γ2
    (fun base => pipelineUnits_of_records tab base s2 Γ2 h2 h2v) hbody

/-! ### Axiom footprints

The composition adds nothing to the development's footprint.  The loop
induction, the resolution lemmas, the bridges and the call-site derivations are
all at `[propext, Quot.sound]`, and `pipeline_satisfies_of_units` is too: the
bundle is a hypothesis, so its own proof carries no unit.

The two theorems that *build* the bundle from the units inherit the unit records'
`Classical.choice`: each of `masks_satisfies`, `entry_pos8_satisfies`,
`entry_b8_satisfies`, `utf8_satisfies` and `escape_positions_satisfies` is at
`[propext, Classical.choice, Quot.sound]`, and `satisfies_calls`,
`satisfies_calls_void` and `satisfies_calls_pos8` are not the source — they are at
`[propext, Quot.sound]`.  The named carrier is therefore the unit records
themselves, not this module. -/

/-- info: 'LeanLLVM.Refinement.PipelineLoop.run_from' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PipelineLoop.run_from

/-- info: 'LeanLLVM.Refinement.PipelineLoop.run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PipelineLoop.run

/-- info: 'LeanLLVM.Refinement.PipelineLoop.run_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PipelineLoop.run_at

-- The declarations this module adds that the section above did not already
-- name.  Each is measured, not assumed: `[propext, Quot.sound]` for the loop
-- shape, the environment's resolutions and the call-site derivations;
-- `[propext]` for the readings of the staging that do no case analysis on a
-- quotient; and none for the congruence on `CallSatisfies`, which is `intro`,
-- `rw` and application.

/-- info: 'LeanLLVM.Refinement.PipelineLoop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PipelineLoop

/-- info: 'LeanLLVM.Refinement.JsonPipelineIR.PipelineUnits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.JsonPipelineIR.PipelineUnits

/-- info: 'LeanLLVM.Refinement.PipelineBodyFacts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PipelineBodyFacts

/-- info: 'LeanLLVM.Refinement.JsonPipelineIR.CallSatisfies_congr' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.JsonPipelineIR.CallSatisfies_congr

/-- info: 'LeanLLVM.Refinement.JsonPipelineIR.pipelineCalls_pos8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.JsonPipelineIR.pipelineCalls_pos8

/-- info: 'LeanLLVM.Refinement.JsonPipelineIR.pipelineCalls_b8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.JsonPipelineIR.pipelineCalls_b8

/-- info: 'LeanLLVM.Refinement.JsonPipelineIR.pipelineCalls_escape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.JsonPipelineIR.pipelineCalls_escape

/-- info: 'LeanLLVM.Refinement.JsonPipelineIR.pipelineCalls_utf8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.JsonPipelineIR.pipelineCalls_utf8

/-- info: 'LeanLLVM.Refinement.JsonPipelineIR.pipelineCalls_stage2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.JsonPipelineIR.pipelineCalls_stage2

/-- info: 'LeanLLVM.Refinement.block64_exists' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms block64_exists

/-- info: 'LeanLLVM.Refinement.readBytes_mid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readBytes_mid

/-- info: 'LeanLLVM.Refinement.blockRead_of_window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms blockRead_of_window

/-- info: 'LeanLLVM.Refinement.separated_at_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms separated_at_block

/-- info: 'LeanLLVM.Refinement.masksPre_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms masksPre_at

/-- info: 'LeanLLVM.Refinement.le_blocks_mul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms le_blocks_mul

/-- info: 'LeanLLVM.Refinement.masksPre_of_window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms masksPre_of_window

/-- info: 'LeanLLVM.Refinement.pipelineArgLen' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pipelineArgLen

/-- info: 'LeanLLVM.Refinement.pipelineStaging_args' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pipelineStaging_args

/-- info: 'LeanLLVM.Refinement.pipelineStaging_base' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pipelineStaging_base

/-- info: 'LeanLLVM.Refinement.pipelineStaging_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pipelineStaging_tail

/-- info: 'LeanLLVM.Refinement.pipelineBudget_of_staging' depends on axioms: [propext] -/
#guard_msgs in
#print axioms pipelineBudget_of_staging

/-- info: 'LeanLLVM.Refinement.pipeline_satisfies_of_units' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pipeline_satisfies_of_units

/-- info: 'LeanLLVM.Refinement.JsonPipelineIR.pipelineUnits_of_records' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.JsonPipelineIR.pipelineUnits_of_records

/-- info: 'LeanLLVM.Refinement.pipeline_satisfies_of_records' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pipeline_satisfies_of_records

/-- info: 'LeanLLVM.Refinement.masksPre_of_stagingWindow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms masksPre_of_stagingWindow

/-- info: 'LeanLLVM.Refinement.masksCall_at_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms masksCall_at_block

open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonEntryIR

/-! ### The finalisation: the units' record to the specification's post

`Satisfies` reads its pre and its post in the same place — `Γ.pre args mem next →
completion ∧ ∀ o, Beh … o → Γ.post args mem next o` — so the caller's staging is
in scope wherever the post is consumed.  The bridge below is stated at that shape:
the units' post, the staging, and the parser-side half that no units' post names.

**Why the parser half is a hypothesis and not derived.**  `pipelineUnitsPost`
names the four cursors, the two-valued verdict, the decoded and event extents, the
refusal word's presence and the frame.  It names neither the document nor `base`
— its argument pattern drops both — and it names neither `parseBytes` nor
`decodeTape`; `EventStreamRel` is a parameter (`JsonPipelineSpec.lean`).  So a
composition of the units' posts cannot produce the specification's document
clause, its acceptance equivalence, its accepted tape and value, or its refusal
offset.  Those are the reference parser's answers, and the records that carry them
are C95's `EventStreamRel`, C96's `Γ_stage2` and `tape_valid` — none of them a
unit in `Γ_pipeline_units`.

**The document clause is recovered from the staging.**  `pipelineStaging` reads
the padded window `readBytes mem base (64 * pipelineBlocks bs.length)`; the
specification reads the exact-length document, and `readBytes_split` gives the
prefix, so that clause is a consequence of the pre rather than of the parser half.
Everything else in `Sigma_pipeline` that is a fact about the caller's buffers —
the cursors, the verdict's two values, the extents, the frame — is derived from
`pipelineUnitsPost` below, including the frame's widened escape extent
(`batchReserve`). -/

/-- **The parser-side half of `Sigma_pipeline`, at the extents the units' post
names.**

The three conjuncts `pipelineUnitsPost` cannot supply: the verdict's equivalence
with the reference parser's acceptance, the accepted tape with its value and
validity, and the refusal word's offset.  `m` is the state the run returned, `bs`
the document the caller staged, `dst`, `ev`, `err` the caller's slots, and
`ndst'`, `nev'` the arena's and the event stream's extents.

**The extents are arguments, and they are the record's.**  The relation is
stated at the pair, so the arena and event bytes it relates are the ones read
there, and a caller supplies the pair its post names.  The record names exactly
one pair per outcome and memory: `pipelineOutputExtents` (`JsonPipelineContract`)
reads each extent from its cursor slot and bounds it below `2 ^ 64`, and the
bound is what makes the slot's eight bytes decide the number rather than its
residue (`pipelineOutputExtents_unique`).  So the hypothesis that carries this
predicate quantifies over pairs the record admits, which is one pair, and the
finalisation applies it at the pair its own post carries.  Nothing here is
quantified over prefixes: a relation that distinguishes prefixes is provable at
the run's extents, which is the case the earlier shape could not express. -/
def ParserHalf (eventRel : EventStreamRel) (bs : List UInt8)
    (verdict : BitVec 64) (m : Mem) (dst ev err ndst' nev' : Nat) : Prop :=
  (verdict = 1 ↔
      ∃ t : Tape, parseBytes Limits.default (ByteString.literal bs) = .ok t) ∧
  (verdict = 1 →
    ∃ (t : Tape) (v : LeanLLVM.JSON.Value) (arena evs : List UInt8),
      parseBytes Limits.default (ByteString.literal bs) = .ok t ∧
      t.input = ByteString.literal bs ∧
      decodeTape t = some v ∧
      readBytes m dst ndst' = some arena ∧
      readBytes m ev nev' = some evs ∧
      eventRel bs arena evs t.tokens ∧
      spansWellFormed t = true ∧
      ValidDocument (ByteString.literal bs) v) ∧
  (∀ e : Nat, readBytes m err 8 = some (wordBytes 8 e) → RefusalOffset bs e)

/-- **The parser half at one outcome of the run.**

`o` is an outcome of the run, `args` the caller's argument list, `mem` the memory
the run started in and `base` the document's address.  The verdict, the returned
memory and — through the argument list — the caller's three slots are the ones
*this outcome* carries: `verdict` is a field of `o` and not a quantified
variable, so the predicate says nothing about a verdict no execution produced.

The document is the one the argument list's length and the starting memory name.
Both are pinned rather than quantified: the length fixes the read and the read
fixes the bytes, so the `∃ bs` has at most one inhabitant per outcome.

`ndst'` and `nev'` are arguments, not this predicate's witnesses: they are the
pair the units' post names (`pipelineOutputExtents`), which its consumer supplies
and stage two's theorem is asked for.  The producer is asked only where the record
admits the pair, and that is one pair per outcome and memory.

**Why this is not the retired premise.**  The retired premise quantified the
verdict (and the returned memory and the slots) freely over a readable document;
`pipeline_parser_hsem_false` proves it implies `False`.  Here every one of those
values is a projection of `o`, and `o` is supplied by the run: a caller holding
`BehFromState … o` cannot choose a verdict the execution did not return.  The
producer of this predicate is stage two's body theorem — the record `Γ_stage2`
and `EventStreamRel` — and it is a hypothesis here only because that theorem is
not in this file. -/
def ParserHalfForOutcome (eventRel : EventStreamRel) (base : Nat)
    (args : List Value) (mem : Mem) (ndst' nev' : Nat) (o : Outcome) : Prop :=
  match o, args with
  | .ret (some (.int 64 verdict)) m,
    [.ptr _, .int 64 n, .ptr _, .ptr _, .ptr _, .ptr _, .int 64 _, .ptr _, .ptr _,
     .int 64 _, .ptr _, .ptr _, .ptr dst, .int 64 _, .ptr _, .ptr ev, .int 64 _,
     .ptr _, .ptr err, .int 64 _] =>
      ∃ bs : List UInt8,
        n.toNat = bs.length ∧
        readBytes mem base n.toNat = some bs ∧
        ParserHalf eventRel bs verdict m dst ev err ndst' nev'
  | _, _ => False

/-- **The finalisation, at the shape `Satisfies` consumes.**

From the staging, the units' post and the parser half at that same outcome, the
specification's post.  `hsem` is indexed by the outcome because the units' post
is: the verdict, the returned memory and the slots are that post's witnesses, and
the parser half reads them off the same `o`.  The document it carries is the one
the staging holds at `base`, which the length and the read identify.

`hsem` takes the extents because the record names them: it is asked at a pair the
record admits, and the post's own pair is the only one.  So the proof below
applies it at the post's witnesses and there is no quantifier over prefixes
anywhere on the path from the units' post to the specification's. -/
theorem pipeline_units_finalisation {eventRel : EventStreamRel} {tab base : Nat}
    {args : List Value} {mem : Mem} {next : Nat} {o : Outcome}
    (hpre : pipelineStaging tab base args mem)
    (hpost : pipelineUnitsPost args mem next o)
    (hsem : ∀ (ndst' nev' : Nat), pipelineOutputExtents args o ndst' nev' →
      ParserHalfForOutcome eventRel base args mem ndst' nev' o) :
    Sigma_pipeline eventRel base args mem next o := by
  obtain ⟨sc, mk, entw, ep, nk, xp, nxp, xcarry, dst, ndst, ev, nev, err,
    nxp0, ndst0, nev0, n, epcap, xpcap, dstcap, evcap, arm, bs, hargs,
    hlen, hbound, hwin, _htail, hbase3, hlow3, hpos, htab, hsc, hcarry, hnk0, hnxp0,
    hepcap,
    hxpbytes, hdstcap, hdstbytes, hevbytes, hevroom, hndst0, hnev0, hroomk,
    hroomx, h32, harm, hreads, hdisj⟩ := hpre
  subst hargs
  simp only [pipelineUnitsPost] at hpost
  split at hpost
  · exact hpost
  · rename_i _o0 verdict m'
    obtain ⟨hverdict, nk', nxp', ndst', nev', ent, ps, out, evs, hext, hnk, hnxp,
      hent, hxp, hdst, hev, herr, hunch⟩ := hpost
    -- the extents the record names are the ones it reads back through its slots
    have hndstSlot : readBytes m' ndst 8 = some (wordBytes 8 ndst') := hext.2.2.1
    have hnevSlot : readBytes m' nev 8 = some (wordBytes 8 nev') := hext.2.2.2
    have hbl : bs.length ≤ 64 * pipelineBlocks bs.length := le_blocks_mul bs.length
    have hK : bs.length + (64 * pipelineBlocks bs.length - bs.length) =
        64 * pipelineBlocks bs.length := by omega
    have hwin' : readBytes mem base
        (bs.length + (64 * pipelineBlocks bs.length - bs.length)) = some
          (bs ++ List.replicate (64 * pipelineBlocks bs.length - bs.length) 0) := by
      rw [hK]; exact hwin
    have hdoclen : readBytes mem base bs.length = some bs := by
      have hsplit := readBytes_split mem base bs.length
        (64 * pipelineBlocks bs.length - bs.length) hwin'
      rw [hsplit.1]
      simp
    have hdoc : readBytes mem base n.toNat = some bs := by
      rw [hlen]; exact hdoclen
    -- the outcome's own document, identified with the staging's by the read
    obtain ⟨bs', hlen', hread', hhalf⟩ := hsem ndst' nev' hext
    have hbs : bs' = bs := by
      rw [← hlen] at hdoclen
      rw [hread'] at hdoclen
      exact Option.some.inj hdoclen
    rw [hbs] at hhalf
    obtain ⟨hacc, haccepted, hrefused⟩ := hhalf
    unfold Sigma_pipeline
    refine ⟨bs, nk', nxp', ndst', nev', hlen, hdoc, hnk, hnxp, hndstSlot,
      hnevSlot, hverdict, hacc, ?_, ?_, ?_⟩
    · intro h1
      -- the half's arena and event stream are the post's: both are the read at
      -- the extents the record names, and a read's value is the memory's
      obtain ⟨t, v, arena, evs', ht, hin, hdec, hdst', hev', hrel, hspan, hvalid⟩ :=
        haccepted h1
      have har : arena = out := Option.some.inj (hdst'.symm.trans hdst)
      have hev'' : evs' = evs := Option.some.inj (hev'.symm.trans hev)
      rw [har] at hrel
      rw [hev''] at hrel
      exact ⟨t, v, out, evs, ht, hin, hdec, hdst, hev, hrel, hspan, hvalid⟩
    · intro h0
      obtain ⟨e, he⟩ := herr h0
      exact ⟨e, he, hrefused e he⟩
    · simpa [batchReserve] using hunch.2
  · exact hpost.elim

/-- **The specification's record from the units' record, without `mono`.**

`Satisfies`'s second conjunct has the pre in scope, and `Γ_pipeline` reads the
body's staging and budget by name, so the finalisation is applied where the post
is consumed: no post-to-post implication at `Satisfies.mono`'s shape, whose
hypothesis is stated without the pre, is available or needed.  The completion
conjunct transfers unchanged because both records' budgets are `pipelineBudget`
by definition.

**The parser half is a hypothesis at the run's own behaviours.**  `hsem` is
indexed by the outcome and gated by `BehFromState` at the pre's entry state: it
is asked for at the outcomes this run can produce, and only there.  That is what
the retired premise was not — it quantified the verdict freely, so one document
supplied the acceptance equivalence at `1` and at `0`
(`LeanLLVMTest.Counterexamples.pipeline_parser_hsem_false`).  The producer is
stage two's body theorem, which is not in this file; nothing here assumes the
parser's answer for an outcome the execution did not return. -/
theorem pipeline_satisfies_of_parser {calls : Calls} {f : Function}
    {eventRel : EventStreamRel} {tab base : Nat}
    (hunits : Satisfies calls f (Γ_pipeline_units tab base))
    (hsem : ∀ (args : List Value) (mem : Mem) (next : Nat) (o : Outcome)
      (ndst' nev' : Nat),
      pipelineStaging tab base args mem →
      BehFromState calls f (EntryState f args mem next) o →
      pipelineOutputExtents args o ndst' nev' →
      ParserHalfForOutcome eventRel base args mem ndst' nev' o) :
    Satisfies calls f (Γ_pipeline eventRel tab base) := by
  intro args mem next hpre
  have hstage : pipelineStaging tab base args mem := hpre.1
  obtain ⟨hcom, hpost⟩ := hunits args mem next hstage
  refine ⟨hcom, ?_⟩
  intro o ho
  exact pipeline_units_finalisation (eventRel := eventRel) (base := base)
    (args := args) (mem := mem) (next := next) (o := o) hstage (hpost o ho)
    (fun ndst' nev' hext => hsem args mem next o ndst' nev' hstage ho hext)

/-! ### The post alone does not imply the specification

The premise the bridge above does not have is not optional: `pipelineUnitsPost`
holds of a memory whose document is unreadable, so no `post → Sigma_pipeline`
implication exists at `Satisfies.mono`'s shape whatever the parser half says.  The
witness below is a shaped argument list and 104 zero bytes: every cursor slot and
prefix the units' post reads is present, the document at `1000` is not, and every
frame region is intact.  `Sigma_pipeline`'s first clause — the exact-length read
at `base` — is then false, which is the clause that does not follow. -/

/-- The witness memory: `n` zero bytes at addresses `0 … n-1`. -/
private def zeroCells (n : Nat) : Mem := (List.range n).map fun i => (i, (0 : UInt8))

/-- The witness arguments: the ABI's twenty slots, the document at `1000` with
length `4`, and every slot the units' post reads inside `zeroCells 104`. -/
private def gapArgs : List Value :=
  [.ptr 1000, .int 64 4, .ptr 0, .ptr 8, .ptr 16, .ptr 24, .int 64 0, .ptr 32,
   .ptr 40, .int 64 0, .ptr 48, .ptr 56, .ptr 64, .int 64 0, .ptr 72, .ptr 80,
   .int 64 0, .ptr 88, .ptr 96, .int 64 0]

/-- **The units' post does not imply the specification's post.**  The `Then` this
constructs is the whole of `Sigma_pipeline`; the failing conjunct is its document
clause, `readBytes mem base n.toNat = some bs`, which no clause of
`pipelineUnitsPost` reaches. -/
theorem pipelineUnitsPost_not_imp_Sigma :
    ∃ (eventRel : EventStreamRel) (base : Nat) (args : List Value) (mem : Mem)
      (next : Nat) (o : Outcome),
      pipelineUnitsPost args mem next o ∧
      ¬ Sigma_pipeline eventRel base args mem next o := by
  refine ⟨fun _ _ _ _ => False, 1000, gapArgs, zeroCells 104, 1,
    .ret (some (.int 64 0)) (zeroCells 104), ?_, ?_⟩
  · unfold pipelineUnitsPost
    refine ⟨Or.inl rfl, 0, 0, 0, 0, [], [], [], [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · simp only [pipelineOutputExtents]
      exact ⟨by decide, by decide, by decide, by decide⟩
    · decide
    · decide
    · rfl
    · rfl
    · rfl
    · rfl
    · intro _
      exact ⟨0, by decide⟩
    · intro h
      exact absurd h (by decide)
    · intro a _
      rfl
  · intro h
    unfold Sigma_pipeline at h
    obtain ⟨bs, nk', nxp', ndst', nev', hlen, hread, -⟩ := h
    have hnone : readBytes (zeroCells 104) 1000 ((4 : BitVec 64).toNat) = none := by
      decide
    rw [hnone] at hread
    cases hread

/-! ### Axiom footprints

The finalisation consumes the staging's own reading, `readBytes_split` and the
units' post; the parser half is a hypothesis, so the bridge adds no principle the
parser records do not carry.  Every declaration below sits at the development's
ceiling, `[propext, Quot.sound]`, measured rather than assumed; the counterexample
is no exception, though its witnesses are closed `Nat` and `List` computations. -/

/-- info: 'LeanLLVM.Refinement.ParserHalf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ParserHalf

/-- info: 'LeanLLVM.Refinement.ParserHalfForOutcome' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ParserHalfForOutcome

/-- info: 'LeanLLVM.Refinement.pipeline_units_finalisation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pipeline_units_finalisation

/-- info: 'LeanLLVM.Refinement.pipeline_satisfies_of_parser' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pipeline_satisfies_of_parser

/-- info: 'LeanLLVM.Refinement.pipelineUnitsPost_not_imp_Sigma' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pipelineUnitsPost_not_imp_Sigma

end LeanLLVM.Refinement
