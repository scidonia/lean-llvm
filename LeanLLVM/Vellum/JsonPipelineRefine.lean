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
`Σ_pipeline`'s and D2's, as `JsonPipelineContract`'s docstring says.
-/
import LeanLLVM.Vellum.JsonPipelineContract
import LeanLLVM.Vellum.JsonPipelineBlockEval
import LeanLLVM.Vellum.LoopFuel

set_option autoImplicit false
set_option maxRecDepth 16000

namespace LeanLLVM.Vellum

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

`Inv r s` is the invariant with `r` iterations of budget left, `Exit` names every
state the loop may leave in (a disjunction when the loop has a success path and a
refusal path, or four heads when the body is unswitched), and the two arms are
`runFuel` prefixes at an exact count bounded by `cost`.  Nothing names a block:
which block a state is at is the invariant's business. -/
structure PipelineLoop (calls : Calls) (f : Function) where
  /-- The loop's iteration bound, a term of the caller's arguments. -/
  N : Nat
  /-- The per-iteration control-step bound, a term of the caller's arguments. -/
  cost : Nat
  /-- The invariant: with `r` iterations of budget left, the state is the loop's
  next iteration, carrying whatever the arm selected needs. -/
  Inv : Nat → State → Prop
  /-- The states the loop may leave in. -/
  Exit : State → Prop
  /-- One iteration: from a state with `r + 1` iterations left, the run reaches a
  state with `r` left within `cost` control steps. -/
  step : ∀ (r : Nat) (s : State), Inv (r + 1) s →
    ∃ (e : State) (j : Nat), j ≤ cost ∧ Inv r e ∧
      ∀ k, runFuel calls (j + k) f s = runFuel calls k f e
  /-- The last iteration reaches a state `Exit` admits. -/
  exit : ∀ (s : State), Inv 0 s →
    ∃ (e : State) (j : Nat), j ≤ cost ∧ Exit e ∧
      ∀ k, runFuel calls (j + k) f s = runFuel calls k f e

/-- **The induction.**  From an invariant state with `r` iterations of budget,
the run reaches an exit state within `(r + 1) * cost` control steps.  The
recursion consumes the two arms only; the arm the entry block selected appears
wherever the invariant puts it, so the four copies are one induction. -/
theorem PipelineLoop.run_from {calls : Calls} {f : Function} (L : PipelineLoop calls f) :
    ∀ (r : Nat) (s : State), L.Inv r s →
      ∃ (e : State) (j : Nat), j ≤ (r + 1) * L.cost ∧ L.Exit e ∧
        ∀ k, runFuel calls (j + k) f s = runFuel calls k f e
  | 0, s, h => by
      obtain ⟨e, j, hj, hexit, hrun⟩ := L.exit s h
      exact ⟨e, j, by simpa using hj, hexit, hrun⟩
  | r + 1, s, h => by
      obtain ⟨e, j, hj, hinv, hrun⟩ := L.step r s h
      obtain ⟨e', j', hj', hexit', hrun'⟩ := L.run_from r e hinv
      refine ⟨e', j + j', ?_, hexit', fun k => ?_⟩
      · rw [Nat.succ_mul]
        omega
      · rw [show j + j' + k = j + (j' + k) from by omega, hrun (j' + k)]
        exact hrun' k

/-- The loop from its head, at the whole bound as its budget: the run reaches an
exit state within `(N + 1) * cost` control steps. -/
theorem PipelineLoop.run {calls : Calls} {f : Function} (L : PipelineLoop calls f)
    (s : State) (h : L.Inv L.N s) (k : Nat) :
    ∃ (e : State) (j : Nat), j ≤ (L.N + 1) * L.cost ∧ L.Exit e ∧
      runFuel calls (j + k) f s = runFuel calls k f e := by
  obtain ⟨e, j, hj, hexit, hrun⟩ := L.run_from L.N s h
  exact ⟨e, j, hj, hexit, hrun k⟩

/-- A budget at the bound, not at the trip count: a completed continuation from
any exit state lifts to the loop's head at `(N + 1) * cost + k`.  Only a
completed continuation can be lifted, because the exit is a jump and `runFuel`
past it executes the next block. -/
theorem PipelineLoop.run_at {calls : Calls} {f : Function} (L : PipelineLoop calls f)
    (s : State) (h : L.Inv L.N s) (k : Nat) {o : Outcome}
    (hcont : ∀ (e : State), L.Exit e → runFuel calls k f e = some o) :
    runFuel calls ((L.N + 1) * L.cost + k) f s = some o := by
  obtain ⟨e, j, hj, hexit, hrun⟩ := L.run s h k
  have hone : runFuel calls (j + k) f s = some o := by
    rw [hrun]
    exact hcont e hexit
  exact runFuel_mono_le (by omega) hone

end LeanLLVM.Vellum

/-! ### The per-unit bundle -/

namespace LeanLLVM.Vellum.JsonPipelineIR

open LeanLLVM.Vellum
open LeanLLVM.Vellum.JsonEntryIR (entryCalls entryPos8Function entryB8Function)
open LeanLLVM.Vellum.JsonS1MasksIR (s1Calls s1MasksFunction)
open LeanLLVM.Vellum.JsonUtf8IR (utf8Calls utf8Function)
open LeanLLVM.Vellum.JsonEscapeIR (escapeListCalls escapeListFunction)

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
argument rather than a reading of the call's own list.  The stage-2 slot is indexed by the
caller's `Γ2` because that unit's body and record are not in this tree.

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

end LeanLLVM.Vellum.JsonPipelineIR

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

namespace LeanLLVM.Vellum

open LeanLLVM
open LeanLLVM.JSON (Block32)
open LeanLLVM.Vellum.JsonS1MasksIR (block64 carrySlot)

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

end LeanLLVM.Vellum

/-! ### The body's own facts, and the composition

The bundle above is what the units guarantee.  What remains is about the body:
the loop instance (one `PipelineLoop` for the four arm-specialised copies), the
three control steps that reach it, and the tail that carries an exit state to the
record's post.  `PipelineBodyFacts` binds them at one staging, so a hypothesis
about them is a hypothesis about the record's own `pre` and not about an invented
staging — the shape `JsonEscapeExpandRun`'s `ExpandFacts` uses for the same
reason. -/

namespace LeanLLVM.Vellum

open LeanLLVM.Vellum.JsonPipelineIR
open LeanLLVM.JSON (Block32)
open LeanLLVM.Vellum.JsonS1MasksIR (block64 carrySlot)

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
theorem pipelineStaging_args {base : Nat} {args : List Value} {mem : Mem}
    (h : pipelineStaging base args mem) :
    ∃ (sc mk entw ep nk xp nxp xcarry dst ndst ev nev err : Nat)
      (n epcap xpcap dstcap evcap arm : BitVec 64),
      args = [.ptr base, .int 64 n, .ptr sc, .ptr mk, .ptr entw, .ptr ep, .int 64 epcap,
        .ptr nk, .ptr xp, .int 64 xpcap, .ptr nxp, .ptr xcarry, .ptr dst,
        .int 64 dstcap, .ptr ndst, .ptr ev, .int 64 evcap, .ptr nev, .ptr err,
        .int 64 arm] := by
  obtain ⟨sc, mk, entw, ep, nk, xp, nxp, xcarry, dst, ndst, ev, nev, err, tab,
    nk0, nxp0, ndst0, nev0, n, epcap, xpcap, dstcap, evcap, arm, bs, hargs, -⟩ := h
  exact ⟨sc, mk, entw, ep, nk, xp, nxp, xcarry, dst, ndst, ev, nev, err,
    n, epcap, xpcap, dstcap, evcap, arm, hargs⟩

/-- **The staging determines the base, and it is the document's address.**

The base is a parameter of `Γ_pipeline_units` and of `pipelineCalls` because
`Satisfies` fixes the call environment before it quantifies over the arguments,
so it cannot be read out of the argument list there.  It is *not* therefore an
asserted value: the staging's own clauses say what it is — the ABI's first
argument (`.ptr base`), the address the padded document window is read at, and
the address whose three preceding bytes the UTF-8 window occupies — and this
lemma hands a caller exactly those.  The escape list's record is indexed by the
same number, and its block clause reads `base + blockAddr blk0`; a base chosen by
inspection rather than taken from here is the defect that clause exists to stop.

The slot order is the pinned ABI's, not assumed: `pipelineBody.params` opens with
`("%b", Ty.ptr)` and `pipeline.h` says the document is `b .. b + n - 1`.
-/
theorem pipelineStaging_base {base : Nat} {args : List Value} {mem : Mem}
    (h : pipelineStaging base args mem) :
    ∃ (n : BitVec 64) (bs : List UInt8),
      3 ≤ base ∧
      readBytes mem (base - 3) 3 = some (List.replicate 3 0) ∧
      readBytes mem base (64 * pipelineBlocks bs.length) = some
        (bs ++ List.replicate (64 * pipelineBlocks bs.length - bs.length) 0) ∧
      ∃ rest : List Value, args = .ptr base :: .int 64 n :: rest := by
  obtain ⟨sc, mk, entw, ep, nk, xp, nxp, xcarry, dst, ndst, ev, nev, err, tab,
    nk0, nxp0, ndst0, nev0, n, epcap, xpcap, dstcap, evcap, arm, bs,
    hargs, _hnlen, _hmax, hwin, h3, hpre3, -⟩ := h
  exact ⟨n, bs, h3, hpre3, hwin, _, by rw [hargs]⟩

-- The ABI's first slot is the document, which is the base the record takes: the
-- pinned AST's parameter list and `pipeline.h`'s "the document is `b .. b + n -
-- 1`" agree, and the staging's first argument clause is `.ptr base` at that slot.
#guard decide (pipelineBody.params.head? = some ("%b", Ty.ptr))

/-- **The record's budget at the document the staging names.**  `pipelineBudget`
is the arguments-only bound `4 * blocks + 16`; this is that term with `blocks`
read off the same argument list, which is what the composition's arithmetic
needs. -/
theorem pipelineBudget_of_staging {base : Nat} {args : List Value} {mem : Mem}
    (h : pipelineStaging base args mem) :
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

**`Γ2` is the stage-2 slot, and pinning it is `Γ_stage2`'s to make.**  The
parameter is not a modelling convenience: the tail's post clauses about `dst`,
`ev`, `ndst`, `nev` and the refusal arm's `err` are facts about the memory the
stage-2 run leaves, and an arbitrary record implies none of them.  The record
that states those facts, `Γ_stage2`, does not exist in this tree, so the pin is
**deferred** to the slice that lands that record — deferred, not missing: it is
a substitution of the record once it exists, and `exit` below is stated at the
arbitrary slot until then.  A record invented here so the tail would go through
would state stage 2's write set where it is convenient rather than where it is
measured, which is the adapter ruling's error in the other direction. -/
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
    ((loop.N = 0 ∧ loop.Exit e) ∨ loop.Inv loop.N e) ∧
    ∀ k, runFuel (pipelineCalls tab base s2) (j + k) pipelineBody
      (EntryState pipelineBody args mem next) =
      runFuel (pipelineCalls tab base s2) k pipelineBody e
  /-- The tail: from any exit state, the verdict and the record's post.  Stated
  at the arbitrary stage-2 slot `Γ2`; the pin to `Γ_stage2` is deferred to that
  record's landing, as the structure's docstring says. -/
  exit : ∀ (e : State), loop.Exit e →
    ∃ (verdict : BitVec 64) (m : Mem),
      runFuel (pipelineCalls tab base s2) 3 pipelineBody e =
        some (.ret (some (.int 64 verdict)) m) ∧
      (Γ_pipeline_units base).post args mem next (.ret (some (.int 64 verdict)) m)

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
arguments disagree with admits nothing. -/
theorem pipeline_satisfies_of_units (tab : Nat) (s2 : Calls) (Γ2 : MemContract)
    (units : ∀ base, PipelineUnits tab base s2 Γ2)
    (hbody : ∀ (base : Nat) (args : List Value) (mem : Mem) (next : Nat),
      (Γ_pipeline_units base).pre args mem next → PipelineUnits tab base s2 Γ2 →
      PipelineBodyFacts tab base s2 Γ2 args mem next) :
    ∀ base, Satisfies (pipelineCalls tab base s2) pipelineBody (Γ_pipeline_units base) := by
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
      (Γ_pipeline_units base).post args mem next (.ret (some (.int 64 verdict)) m) →
      (∃ v m', runFuel (pipelineCalls tab base s2) (pipelineBudget args mem) pipelineBody
        (EntryState pipelineBody args mem next) = some (.ret v m')) ∧
      ∀ o, BehFromState (pipelineCalls tab base s2) pipelineBody
        (EntryState pipelineBody args mem next) o → (Γ_pipeline_units base).post args mem next o := by
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
    obtain ⟨e1, j1, hj1, hexit1, hrun1⟩ := loop.run e0 hinv 3
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
      (Γ_pipeline_units base).pre args mem next → PipelineUnits tab base s2 Γ2 →
      PipelineBodyFacts tab base s2 Γ2 args mem next) :
    ∀ base, Satisfies (pipelineCalls tab base s2) pipelineBody (Γ_pipeline_units base) :=
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

/-- info: 'LeanLLVM.Vellum.PipelineLoop.run_from' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PipelineLoop.run_from

/-- info: 'LeanLLVM.Vellum.PipelineLoop.run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PipelineLoop.run

/-- info: 'LeanLLVM.Vellum.PipelineLoop.run_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PipelineLoop.run_at

/-- info: 'LeanLLVM.Vellum.pipeline_satisfies_of_units' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pipeline_satisfies_of_units

/-- info: 'LeanLLVM.Vellum.JsonPipelineIR.pipelineUnits_of_records' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Vellum.JsonPipelineIR.pipelineUnits_of_records

/-- info: 'LeanLLVM.Vellum.pipeline_satisfies_of_records' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pipeline_satisfies_of_records

/-- info: 'LeanLLVM.Vellum.masksPre_of_stagingWindow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms masksPre_of_stagingWindow

/-- info: 'LeanLLVM.Vellum.masksCall_at_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms masksCall_at_block

end LeanLLVM.Vellum
