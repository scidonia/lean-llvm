/-
The stage-2 walk's traversal: the loop as a counted run.

`walkCompletes_of_prefix_chain` (`JsonStage2WalkSeed`) states the completion
conjunct of `Stage2WalkObligation` behind five premises: the seed's prefix, the
`WalkChain` value, the chain's step count, the return's step and the numeric
comparison against `stage2Budget`.  This module replaces the chain's step count
and the comparison with one loop-step premise, keeps the return's step inside that
premise's exit branch, and reads the chain as the run it is:

* **a segment is a counted run.**  `WalkSegment` is a `j` and a `runFuel`
  equality at that count, with `WalkInv` at the target; `WalkChain.steps` is its
  producer (`WalkSegment.of_chain`), `WalkSegment.trans` composes two and
  `WalkSegment.ret` spends the segment's count plus the returning step.  The
  chain is therefore not a second object beside the assembly: it is one way to
  supply a segment, and `WalkChain.inv_last` is the invariant the chain's tail
  carries — the clause every consumer of a chain's end state needs and the
  chain's own definition did not expose;
* **the budget is a potential, not the measure.**  `walkMeasure` is
  `(nep - k) * (4 * n + 6) + inner`, a termination witness: it falls at the
  header's pass (`walkMeasure_step`) and it dominates the iteration count
  (`walkIterations_le_measure`).  It is *not* a step count, and
  `walkMeasure_exceeds_budget_at_100` is the measurement that says so: at a
  hundred entries and a hundred bytes the measure is 40,600 against the
  record's 4,032, so spending the measure against `stage2Budget` would prove
  nothing about the walk.  The count is spent by `walkPotential`,
  `32 * (nep - k) + 8 * (n - the credit boundary at k)`: its entry term is
  one allowance per unconsumed entry and its byte term one per document byte not
  yet reached, read at the same index the dispatch's price is read at, so the credit
  *falls* as the walk consumes them, and
  `walkPotential_le` bounds it by `32 * nep + 8 * n` by saturation alone.  A
  revolution therefore has to show `p + walkPotential C' ≤ walkPotential C`, which
  `walkPotential_spend` reads in the direction the accounting has: the price inside
  the credit the revolution *consumes*, `p ≤ 32·Δk + 8·ΔA`, never inside the credit
  that remains.  That is the arithmetic the *The budget, counted* section fixes
  (22 blocks against 32, six against eight), and the byte term is the span an
  entry's stream position leaves, so a scan that emits nothing — whitespace, quote
  discovery — is paid out of the same credit.  Charging the decoded extents instead,
  as an earlier draft did, adds processed bytes to the remaining budget and denies
  the price even at `p = 0`.  The rows the change is stated at, the negative control
  on that form, and the dispatch's first pivots stepped on the pinned body are
  `tests/stage2-walk-credit.lean`;
* **the loop is an induction on the entry index.**  `WalkLoopStepThree` is the one
  premise this module leaves: at a loop-head state with the invariant and an
  unconsumed entry, either one revolution back to the head with the index
  advanced (`C.k < C'.k < nep`) and the potential spent, or the loop's terminal
  run — `q + 2` steps to a return at the verdict and the memory the run reaches,
  with the record's boundary there (`WalkTargetPost`, existentially in both the
  verdict and the memory, because the finalisation returns `1` on the accepted
  route and `0` on the refusal ones and the post is stated at the returned
  memory).  `walkLoopFinishesThree` is the
  well-founded completion: strong recursion on `nep - C.k`, which the
  revolution's strict advance makes finite, and whose count the measure
  dominates; the price telescopes to `walkPotential` at the head plus `F`.
  `walkCompletes_of_loop` adds the seed's `j` steps and the return's own step
  and reads the completion at `walkPotential + stage2FinalisationAllowance`;
  `walkCompletes_of_loop_budget` is that at `32 * nep + 8 * n + 32`, which is
  `stage2Budget` without the escape-position term, and
  `walkCompletes_of_seed_loop` is the same at the seed's three-step prefix
  (`walkSeedPrefix_runFuel`'s `3`, `walkSeedInvariant_geometry`'s invariant,
  `walkSeed`'s own empty carry so the potential is `32 * nep`).

What remains is `WalkLoopStepThree`, one premise per geometry, and the two premises
that supply it (the seed's run and entry, and the finalisation allowance's
arithmetic).  Named exactly:

1. **`WalkLoopStepThree`** — its left branch is one revolution from `NodeBlock21` back
   to it: the dispatch's pass to `cleanup478.i` (built from the census's class
   links, and the three steps it counts), the back edge (`walkBack_step`), the
   header's pass (`whileBody_step`) and the two `phi` runs, with `walkMeasure`'s
   strict decrease where `walkMeasure_step` states it and the traps excluded before
   their arms (`walkEventReserve_clear`, `walkArenaReserve_clear` are theorems of
   the invariant).  Its right branch is the terminal run: the test's false edge and the
   tail through `s2_walk.exit` or the refusal copy to `if.end`'s return, inside
   `F ≤ 27` — the finalisation allowance less the seed's three steps and the two
   terminal ones — at the memory the run returns, with `stage2Boundary` there.
   Both
   are stated at `WalkInv` and admit nothing beside it, which is what the carriers
   were converted for.  The revolution is *one* premise rather than a pass plus
   the two proved steps because `walkBack_step`'s statement gives the back edge's
   step, invariant and run but not the target state's `pre`, `%k.2.i` or
   `%sp.i.1` bindings, which are what `whileBody_step` reads; composing them from
   the statements alone is not possible, and the pass's premise carries the
   merge's facts instead;
2. **the seed** — `walkSeedPrefix_runFuel` is `hseed` at `j = 3` (the entry
   block, the preheader and the header's first pass, at the state they compose to)
   and `walkSeedInvariant_geometry` is `hInv` at that state, so this premise is
   proved and only its own three block runs, their pc facts and the entry test's
   bit are the caller's;
3. **`hF`** — `j + F + 2 ≤ stage2FinalisationAllowance`, i.e. `F ≤ 27` at the
   seed's three steps; and
4. **the geometry** — `WalkGeom` is `stage2Pre`'s witnesses, field for field, and
   `WalkStage` is `stage2StagedPre`'s staging extended by the watermark; neither
   construction is written here, so the completion above is stated at a geometry
   rather than at `stage2Args`.  That is the gap between
   `walkCompletes_at_stage2Budget` and `Stage2WalkCompletes`'s own quantifier, and
   it is a construction rather than a proof: every field of both structures is one
   of the two preconditions' clauses.

Where this stops, `JsonStage2WalkAssembly` picks up.  The revolution's composition
was blocked by `walkBack_step`'s existential target, and `walkBack_step_at` names it
(`cleanup478Out`) with the two `phi` values the header's pass reads, so one revolution
is the dispatch's segment, the merge's step and the header's pass
(`WalkDispatch.revolution`), and the loop's step is the dispatch's three outcomes
(`walkLoopStepThree_of_dispatchThree`, `JsonStage2WalkLoopStepOutcome`): `cont` takes
the revolution, and `finish` and `refuse` take the terminal branch.  Premise 1 is
therefore the dispatch's *result* — the segment to `cleanup478.i` with the merge's `phi`
facts, or the segment to `if.then` — beside the terminal post at the state it reaches
(`WalkTargetPost`, whose producers are `JsonStage2WalkTargetPost`'s four routes);
premise 3 is `walkExitFits`.
Premise 4 is a construction on both halves: `walkGeom_at_pre` is `stage2Pre`'s
witnesses as a `WalkGeom` with the argument list the geometry's own numbers, and `walkStage_at_pre`
is the adapter's staging as a `WalkStage`.  The second is the separation transports
(`walkDisjoint_drop_member`, `walkDisjoint_before`) after the two predicates' number
clauses make the columns agree — the widths `Γ_stage2.pre` states (`nxp`, `dstcap`,
`evcap`, which `Stage2Run`'s `nepLt`/`nxpLt`/`dstcapLt`/`evcapLt` read at the
*report*), the cursor's two witnesses as one word (`wordBytes8_mod_eq`, the staged
predicate's cursor-width clause), and the seven's end, which is the adapter's own
watermark at the objects it appends.

Nothing above is a claim about `Stage2WalkObligation`: its completion half is the
conjunct these premises discharge, and its post half is not read here. -/

import LeanLLVM.Refinement.JsonStage2WalkScope

namespace LeanLLVM.Refinement
namespace WalkScope

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR

set_option autoImplicit false

/-! ### The loop's head -/

/-- **The dispatch's entry block.**  `walkSeed` names it (`walkSeed_block`), the
header's first pass jumps to it, and the seed's prefix ends there
(`walkSeedPrefix_runFuel`). -/
def walkLoopHead : String := "NodeBlock21"

#guard decide (walkLoopHead = "NodeBlock21")

-- The head is one of the body's blocks: the guard's control, so a name that no
-- block carries cannot be the head.
#guard decide ((stage2Body.findBlock walkLoopHead).isSome = true)

/-- **The seed's carry is at the loop head**, by the two definitions' own
equations rather than by a hypothesis. -/
theorem walkSeed_block {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) :
    (walkSeed G S).block = walkLoopHead := rfl

/-! ### A counted segment

The trace vocabulary of `JsonStage2WalkScope` states a chain and reads its step
count out of it (`WalkChain.steps`).  A segment is that reading on its own: a
count and the `runFuel` equality at it, with the invariant at the target.  It is
weaker than a chain — nothing about the links it is made of survives — and it is
what the completion consumes, so the assembly states its premises at segments
and `WalkSegment.of_chain` is where a chain re-enters. -/

/-- **A counted segment of the walk's run**: `j` steps from `s` reach `s'` and
leave it exactly (for every further fuel), and `WalkInv` holds at the target.

**It carries no memory clause, and a word clause cannot be added here.**  At
`if.else285.i` the arena append stores `wordBytes 8 (a + l)` at `z + 48` while the
target carry's `alen` is unchanged — the carry is *ahead* of the arena, which that
link's own premise records (`hale : a + l ≤ C.alen` in `WalkLink.if_else285_i`).  So
"the word is `alen` at both ends" is false on that link, and the head's equality is a
property of a whole revolution rather than of a segment.  A *general* memory clause
would have to be a write trace, composed by `trans`; the head equality is stated
head-to-head beside the dispatch. -/
structure WalkSegment (calls : Calls) {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (C' : WalkCarry G) (s' : State) (j : Nat) : Prop where
  /-- The run, at the segment's own count and every continuation. -/
  run : ∀ n, runFuel calls (j + n) stage2Body s = runFuel calls n stage2Body s'
  /-- The invariant at the segment's target. -/
  inv' : WalkInv G C' s'
  /-- The adapter's staging is the same at both ends, as it is at every link:
  the segments are links and their compositions.  The terminal post reads its
  scratch objects at this staging, so the chain's endpoints have to carry it. -/
  stage_eq : C'.stage = C.stage

/-- **Segments compose**, and their counts add: the first's equality at the
second's count is the second's source. -/
theorem WalkSegment.trans {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C C' C'' : WalkCarry G} {s s' s'' : State} {j k : Nat}
    (h₁ : WalkSegment calls G C s C' s' j) (h₂ : WalkSegment calls G C' s' C'' s'' k) :
    WalkSegment calls G C s C'' s'' (j + k) where
  run n := by
    rw [show j + k + n = j + (k + n) from by omega, h₁.run (k + n), h₂.run n]
  inv' := h₂.inv'
  stage_eq := h₂.stage_eq.trans h₁.stage_eq

/-- **A segment that ended at the refusal copy, with the word the copy loads.**  The
refusal's offset store is the last write before `if.then` — `if.then56.i`,
`if.then205.i` and `if.then488.i` each write `wordBytes 8 k` at `%e + 8` — and the copy's
`%off` load reads exactly that word.  A bare `WalkSegment` carries the run and the
invariant and no memory, so the word is a field *beside* it: the producer states it at its
own store, and the word then travels with the segment to the copy.

`k` is not a projection of the carry: the arms that refuse write a position
(`if.then56.i`'s `%idxprom.i`) or the document's length (`if.then205.i`'s `%4`), so the
carry's `eoff` may differ from the word the copy will load, and `WalkInv.eoff_le` is only
a bound.  What the boundary needs of the word is `k ≤ G.n`, which is the field. -/
structure WalkRefuseSegment (calls : Calls) {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (Cd : WalkCarry G) (sd : State) (p : Nat) : Prop where
  /-- The run from the head to the refusal copy. -/
  seg : WalkSegment calls G C s Cd sd p
  /-- The endpoint is the copy's own block. -/
  block : Cd.block = "if.then"
  /-- The copy's `%off` load: a word inside the document, at `%e + 8`. -/
  word : ∃ k, k ≤ G.n ∧ readBytes sd.mem (Cd.stage.e + 8) 8 = some (wordBytes 8 k)

/-- **A chain's tail carries the invariant.**  The chain's constructors state it
at the head (`nil`) and at every link's target (`WalkLink.inv'`), so the last
state's invariant is the induction's, and it is what makes a chain usable as a
segment's second half. -/
theorem WalkChain.inv_last {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C C' : WalkCarry G} {s s' : State} (h : WalkChain calls G C s C' s') :
    WalkInv G C' s' := by
  induction h with
  | nil h => exact h
  | tail _ _ ih => exact ih

/-- **A chain keeps the adapter's staging**, as every link does.  Stated by
recursion rather than `induction` because the chain is a `Prop` and the motive is
about its two index carries. -/
theorem WalkChain.stage_eq {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C C' : WalkCarry G} {s s' : State} (h : WalkChain calls G C s C' s') :
    C'.stage = C.stage :=
  match h with
  | WalkChain.nil _ => rfl
  | WalkChain.tail hl ht => (WalkChain.stage_eq ht).trans hl.stage_eq

/-- **A chain is a segment, at the count `WalkChain.steps` names.**  The count is
existential and cannot be a function: `WalkChain` is a `Prop`, so a
`Nat`-valued `length` is not definable — that would be a large elimination — and a
chain's step count is always *some* `k` and never a projection of the chain.  That is why
the price a revolution states is `WalkSegment`'s own index and not a chain's
length, and why `WalkChain.steps` is stated with an existential rather than a
`def`. -/
theorem WalkSegment.of_chain {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C C' : WalkCarry G} {s s' : State} (h : WalkChain calls G C s C' s') :
    ∃ j, WalkSegment calls G C s C' s' j := by
  obtain ⟨j, hj⟩ := h.steps
  exact ⟨j, ⟨hj, h.inv_last, WalkChain.stage_eq h⟩⟩

/-- **Chains concatenate.**  The cons form (`tail`) is the only constructor, so
composition up to now was by re-deriving the left chain at the right's head; this
is the algebra the assembly composes a revolution out of its links with. -/
theorem WalkChain.append {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C C' C'' : WalkCarry G} {s s' s'' : State}
    (h₁ : WalkChain calls G C s C' s') (h₂ : WalkChain calls G C' s' C'' s'') :
    WalkChain calls G C s C'' s'' :=
  match h₁, h₂ with
  | .nil _, h₂ => h₂
  | .tail hl ht, h₂ => .tail hl (ht.append h₂)

/-- **A segment plus the returning step completes**, at the segment's count plus
one, for every budget at least that. -/
theorem WalkSegment.ret {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C C' : WalkCarry G} {s s' sret : State} {j : Nat} {v : Value}
    (h : WalkSegment calls G C s C' s' j) (hret : step calls stage2Body s' = .ret v sret) :
    ∀ N, j + 1 ≤ N → runFuel calls N stage2Body s = some (.ret v sret.mem) := by
  intro N hN
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hN
  have hfin : runFuel calls (j + 1) stage2Body s = some (.ret v sret.mem) := by
    rw [h.run 1]
    simp only [runFuel, hret]
  exact runFuel_mono (d := d) hfin

/-! ### The document's bytes are the spans' total

The byte term of the potential is the sum of the extents the arena has decoded,
and the invariant already states what makes that sum no more than the document's
length: the extents are in document order (`spans_order`) and each ends inside
the document (`spans_inside`).  Two ordered, in-document extents do not overlap,
so their lengths are at most the document's own. -/

/-- **Ordered, in-document extents sum to at most the document.**  The induction
carries the last extent's end as the start: the pairwise order places it at or
before the next extent's beginning, and the document's bound closes the last. -/
theorem walkSpans_sum_le_aux {m0 : Mem} (G : WalkGeom m0) :
    ∀ (l : List (Nat × Nat)) (start : Nat),
      l.Pairwise (fun r s : Nat × Nat => r.1 + r.2 ≤ s.1) →
      (∀ r ∈ l, r.1 + r.2 ≤ G.n) →
      (∀ r ∈ l, start ≤ r.1) → start ≤ G.n →
      (l.map (fun r => r.2)).sum + start ≤ G.n
  | [], start, _, _, _, hstart => by simpa using hstart
  | (a₁, a₂) :: l, start, hord, hin, hstart, _hstartn => by
      have hpair : l.Pairwise (fun r s : Nat × Nat => r.1 + r.2 ≤ s.1) :=
        (List.pairwise_cons.mp hord).2
      have hR : ∀ r ∈ l, a₁ + a₂ ≤ r.1 := fun r hr => (List.pairwise_cons.mp hord).1 r hr
      have hin' : ∀ r ∈ l, r.1 + r.2 ≤ G.n := fun r hr => hin r (List.mem_cons_of_mem _ hr)
      have hinside : a₁ + a₂ ≤ G.n := hin (a₁, a₂) (by simp)
      have hstart' : start ≤ a₁ := hstart (a₁, a₂) (by simp)
      have hrec := walkSpans_sum_le_aux G l (a₁ + a₂) hpair hin' hR hinside
      simp only [List.map_cons, List.sum_cons]
      omega

/-- **The decoded extents fit the document.** -/
theorem walkSpans_sum_le {m0 : Mem} (G : WalkGeom m0) {spans : List (Nat × Nat)}
    (hord : spans.Pairwise (fun r s : Nat × Nat => r.1 + r.2 ≤ s.1))
    (hin : ∀ r ∈ spans, r.1 + r.2 ≤ G.n) :
    (spans.map (fun r => r.2)).sum ≤ G.n := by
  have h := walkSpans_sum_le_aux G spans 0 hord hin (fun _ _ => Nat.zero_le _) (Nat.zero_le _)
  simpa using h

/-! ### The potential

`walkMeasure`'s outer factor is a *termination* radix; the budget's is a count.
The potential is the budget's own shape read at the carry as **credit**: one entry
allowance for each entry not yet dispatched, and one byte allowance for each
document byte not yet reached.  The byte term is read at the credit boundary —
`entryPos` below the entry stream, the document's length at and past it — because
the index a price is read at can leave the stream: `entryPos` totalises to zero
there, so a byte term read through it stops charging the document the walk has left
to reach.  At the boundary the term is what makes a revolution's price payable: an
entry's dispatch runs inside the bytes that entry spans, so the whitespace, quote
and escape scans — none of which emits arena output — are paid out of the same
credit.

Charging the *decoded* extents instead adds already-processed bytes to the
remaining budget: a revolution appending a hundred-byte span moved the potential by
`-32 + 800`, so `p + Φ(C′) ≤ Φ(C)` failed at `p = 0`.  The direction is fixed here —
the credit falls as bytes are consumed — and the revolution's price is stated
against what it consumes: `p ≤ 32·Δk + 8·ΔA`
(`walkPotential_spend`). -/

/-- **The credit boundary at an index**: the entry stream's position below the
stream, and the document's length at and past it.

`entryPos` is a stream read and totalises to zero past the stream; `boundary` is a
price index and totalises to the document's length.  Two quantities that agree below
the terminal index and must not agree at it: the terminal index has no entry
position, and the credit there is the document the walk has left to reach.  That is
why `price_eq_of_lt` is an equality rather than an implication, and why reading the
potential at this quantity leaves every non-terminal value unchanged. -/
def boundary {m0 : Mem} (G : WalkGeom m0) (k : Nat) : Nat :=
  if k < G.nep then entryPos G k else G.n

/-- **The walk's remaining budget, at the carry**: the entries not yet dispatched
and the document bytes not yet reached, read at the credit boundary.  The entry term
saturates at zero past its end and the boundary reads the document's length there,
so both terms are zero past the stream and the potential is bounded without
reference to the invariant. -/
def walkPotential {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) : Nat :=
  stage2EntryAllowance * (G.nep - C.k) +
    stage2ByteAllowance * (G.n - boundary G C.k)

/-- A strictly increasing index list's entries do not fall as the index rises,
read through `getD` (the shape the entry positions have). -/
theorem pairwise_lt_getD_le {l : List Nat} (hs : l.Pairwise (· < ·)) {d : Nat} {i j : Nat}
    (hij : i ≤ j) (hj : j < l.length) : l.getD i d ≤ l.getD j d := by
  have hi : i < l.length := lt_of_le_of_lt hij hj
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
  simp only [Option.getD_some]
  rcases Nat.lt_or_eq_of_le hij with h | h
  · exact le_of_lt ((List.pairwise_iff_getElem.mp hs) i j hi hj h)
  · subst h
    exact le_rfl

/-- **An entry the stream holds is inside the document.** -/
theorem entryPos_lt {m0 : Mem} (G : WalkGeom m0) {k : Nat} (hk : k < G.nep) :
    entryPos G k < G.n := by
  have hlen : G.ent.length = G.nep := by
    rw [← readLanes32_length m0 G.ep G.nep G.ent G.entries]
  have hk' : k < G.ent.length := by omega
  have hget : entryPos G k = G.ent[k] := by
    simp only [entryPos, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk',
      Option.getD_some]
  rw [hget]
  exact G.inside _ (List.getElem_mem hk')

/-- **The stream's positions advance with the index.** -/
theorem entryPos_mono {m0 : Mem} (G : WalkGeom m0) {k k' : Nat} (hkk : k ≤ k')
    (hk' : k' < G.nep) : entryPos G k ≤ entryPos G k' := by
  have hlen : G.ent.length = G.nep := by
    rw [← readLanes32_length m0 G.ep G.nep G.ent G.entries]
  have hk'' : k' < G.ent.length := by omega
  exact pairwise_lt_getD_le G.order hkk hk''

/-- **The potential is inside the record's entry and byte terms** — immediately,
by saturating subtraction: the index has not passed the stream, and every position
is at most the document's length. -/
theorem walkPotential_le {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) {s : State}
    (_hInv : WalkInv G C s) :
    walkPotential G C ≤ stage2EntryAllowance * G.nep + stage2ByteAllowance * G.n := by
  have h1 : stage2EntryAllowance * (G.nep - C.k) ≤ stage2EntryAllowance * G.nep :=
    Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h2 : stage2ByteAllowance * (G.n - boundary G C.k) ≤ stage2ByteAllowance * G.n :=
    Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  simp only [walkPotential, stage2EntryAllowance, stage2ByteAllowance] at h1 h2 ⊢
  omega

/-! ### The credit boundary

The potential's byte term is a document position, and the index it is read at can
leave the entry stream: `entryPos` is `G.ent.getD k 0`, so past the last entry it
totalises to zero (`entryPos_eq_zero_of_nep_le`).  A price read at that index
therefore charges nothing for the document bytes the walk has left to reach, while
the potential goes on counting them.  `boundary` is the index both readings use: the
stream's position below the stream and the document's length at and past it, and it
is defined above, where the potential's byte term names it.

**A module above the potential's definition cannot redefine it.**  The terminal
price this index serves is restated in `JsonStage2WalkCredit`, which is downstream of
this one
(`JsonStage2WalkCredit → JsonStage2WalkDispatchWitnessHlast → JsonStage2WalkFinishPath
→ JsonStage2WalkAssembly → JsonStage2WalkTraverse`), so a definition written there
would be invisible to the potential.  The index and its laws are stated here, where
the potential is defined; the price is stated there, where the terminal conjunct is.
-/

/-- **Below the stream the boundary is the stream's position.** -/
theorem boundary_eq_entryPos {m0 : Mem} (G : WalkGeom m0) {k : Nat} (hk : k < G.nep) :
    boundary G k = entryPos G k := by
  simp only [boundary, ite_eq_left hk]

/-- **At the terminal index the boundary is the document's length.** -/
theorem boundary_nep {m0 : Mem} (G : WalkGeom m0) : boundary G G.nep = G.n := by
  simp only [boundary, ite_eq_right (lt_irrefl G.nep)]

/-- **The boundary is inside the document**, at every index: a position below the
stream is one the entry stream holds (`entryPos_lt`), and at or past it the boundary
is the length itself. -/
theorem boundary_le {m0 : Mem} (G : WalkGeom m0) (k : Nat) : boundary G k ≤ G.n := by
  by_cases hk : k < G.nep
  · rw [boundary_eq_entryPos G hk]
    exact le_of_lt (entryPos_lt G hk)
  · rw [show boundary G k = G.n from by simp only [boundary, ite_eq_right hk]]

/-- **The stream's position past the stream is zero**, at every index from `nep` on:
`entryPos`'s default is the totalisation, not a position.  This is the form the
boundary's comparison needs, and it is what makes the old terminal byte term vanish. -/
theorem entryPos_eq_zero_of_nep_le {m0 : Mem} (G : WalkGeom m0) {k : Nat}
    (hk : G.nep ≤ k) : entryPos G k = 0 := by
  have hlen : G.ent.length = G.nep := by
    rw [← readLanes32_length m0 G.ep G.nep G.ent G.entries]
  simp only [entryPos, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by omega)]
  rfl

/-- **The boundary is never below the stream's position.**  Below the stream the two
coincide, and at or past it the stream reads zero while the boundary reads the
document's length.  This is the direction the price's substitution rests on: the
right-hand side the boundary form states is the `entryPos` form's plus what the
totalisation discards. -/
theorem boundary_ge_entryPos {m0 : Mem} (G : WalkGeom m0) (k : Nat) :
    entryPos G k ≤ boundary G k := by
  by_cases hk : k < G.nep
  · rw [boundary_eq_entryPos G hk]
  · rw [show boundary G k = G.n from by simp only [boundary, ite_eq_right hk],
      entryPos_eq_zero_of_nep_le G (by omega)]
    exact Nat.zero_le _

/-- **The boundary is monotone in the index.**  Two cases: both indices below the
stream, where it is `entryPos_mono`; or the upper one at or past `nep`, where the
boundary is the document's length and `boundary_le` bounds the lower one.  Unlike
`entryPos`, this needs no side condition on the upper index. -/
theorem boundary_mono {m0 : Mem} (G : WalkGeom m0) {k k' : Nat} (hkk : k ≤ k') :
    boundary G k ≤ boundary G k' := by
  by_cases hk' : k' < G.nep
  · have hk : k < G.nep := lt_of_le_of_lt hkk hk'
    rw [boundary_eq_entryPos G hk, boundary_eq_entryPos G hk']
    exact entryPos_mono G hkk hk'
  · rw [show boundary G k' = G.n from by simp only [boundary, ite_eq_right hk']]
    exact boundary_le G k

/-- **The last entry's boundary is at most the terminal one.**  The step the terminal
price reads: its byte term is a difference of boundaries, and the terminal index may
not fall below the entry before it. -/
theorem boundary_nep_ge_prev {m0 : Mem} (G : WalkGeom m0) :
    boundary G (G.nep - 1) ≤ boundary G G.nep :=
  boundary_mono G (Nat.sub_le _ _)

/-- **And the step is strict when there is an entry to take it from**, since every
entry's position is inside the document: the terminal boundary is past the last
entry position, not equal to it. -/
theorem boundary_nep_gt_prev {m0 : Mem} (G : WalkGeom m0) (hnep : 0 < G.nep) :
    boundary G (G.nep - 1) < boundary G G.nep := by
  have hprev : G.nep - 1 < G.nep := by omega
  rw [boundary_eq_entryPos G hprev, boundary_nep]
  exact entryPos_lt G hprev

/-- **Below the stream the price is the price.**  Both indices are stream positions,
so the boundary form and the `entryPos` form are the same number — every price the
walk states at `k2 < nep` is unchanged by the substitution, not merely implied by
it. -/
theorem price_eq_of_lt {m0 : Mem} (G : WalkGeom m0) {k k2 : Nat}
    (hk : k < G.nep) (hk2 : k2 < G.nep) :
    stage2EntryAllowance * (k2 - k) +
        stage2ByteAllowance * (boundary G k2 - boundary G k) =
      stage2EntryAllowance * (k2 - k) +
        stage2ByteAllowance * (entryPos G k2 - entryPos G k) := by
  rw [boundary_eq_entryPos G hk, boundary_eq_entryPos G hk2]

/-- **The old terminal byte term is zero.**  `entryPos_eq_zero_of_nep_le` reads as the
accounting defect: at the terminal index the `entryPos` form charges nothing for the
document bytes the walk has left to reach, whatever the price's block count. -/
theorem entryPosPrice_noByteAllowance {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) :
    stage2ByteAllowance * (entryPos G G.nep - entryPos G C.k) = 0 := by
  rw [entryPos_eq_zero_of_nep_le G (Nat.le_refl _), Nat.zero_sub, Nat.mul_zero]

/-- **The charge, both ways at a hundred bytes**: the boundary form pays a
hundred-byte trailing scan and the `entryPos` form — whose byte term is zero — does
not.  The rows are `walkCreditRows`' long-string width at the terminal entry. -/
theorem terminalScan_charge_control :
    (22 + 6 * 100) + 2 ≤ 32 + 8 * 100 ∧ ¬ ((22 + 6 * 100) + 2 ≤ 32 + 0) := by
  decide

/-! #### Spending the potential

The index is the price's, so the spend needs no side condition but the index's own
order: `boundary_mono` and `boundary_le` replace the stream form's positions and
monotonicity, and neither carries a `k2 < nep` condition.  That is what admits
`C'.k = G.nep`, the step the terminal dispatch takes. -/

/-- **A revolution's price, in the credit it consumes.**  `Δk` entries and `ΔA`
document bytes: `p ≤ 32·Δk + 8·ΔA` is the obligation the dispatch's counted path
owes, and it yields the potential's fall.  This is the direction the accounting
has — the price is bounded by the credit *consumed*, never by the credit that
remains — so one byte of the entry's span pays eight model steps of the
byte-dependent loops inside it. -/
theorem walkPotential_spend {m0 : Mem} (G : WalkGeom m0) {C C' : WalkCarry G} {p : Nat}
    (hk : C.k ≤ C'.k) (hk' : C'.k ≤ G.nep)
    (hall : p ≤ stage2EntryAllowance * (C'.k - C.k) +
      stage2ByteAllowance * (boundary G C'.k - boundary G C.k)) :
    p + walkPotential G C' ≤ walkPotential G C := by
  have h1 : G.nep - C.k = (G.nep - C'.k) + (C'.k - C.k) := by omega
  have hmono : boundary G C.k ≤ boundary G C'.k := boundary_mono G hk
  have hb : boundary G C.k ≤ G.n := boundary_le G C.k
  have hb' : boundary G C'.k ≤ G.n := boundary_le G C'.k
  have h2 : G.n - boundary G C.k =
      (G.n - boundary G C'.k) + (boundary G C'.k - boundary G C.k) := by omega
  simp only [walkPotential, stage2EntryAllowance, stage2ByteAllowance] at hall ⊢
  rw [h1, h2, Nat.mul_add, Nat.mul_add]
  omega

/-- **At and past the stream the credit is exhausted**: no entry left and no document
byte left to reach.  This is the terminal index's reading, and it is what the
`entryPos` form cannot state — there the potential is `8 · G.n` past the stream. -/
theorem walkPotential_zero_of_nep_le {m0 : Mem} (G : WalkGeom m0)
    {C : WalkCarry G} (hk : G.nep ≤ C.k) : walkPotential G C = 0 := by
  have h1 : G.nep - C.k = 0 := by omega
  have h2 : boundary G C.k = G.n := by
    simp only [boundary, ite_eq_right (by omega : ¬ C.k < G.nep)]
  simp only [walkPotential, h1, h2, Nat.sub_self, Nat.mul_zero, Nat.add_zero]

/-- **The terminal dispatch pays into the credit.**  The restated terminal conjunct as
the potential's spend: `p + 2` steps carry the loop from `C.k` to the terminal index,
the price is the entry's remaining span, and the potential at the terminal index is
zero.  The `entryPos` byte term could not state this — the spend's own hypothesis
would need `entryPos G C.k ≤ entryPos G G.nep`, false whenever the entry has a
position — and the boundary form states it as the spend at `C'.k = G.nep`. -/
theorem terminalCharge_boundary {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) {p : Nat}
    (hk : C.k < G.nep)
    (h : p + 2 ≤ stage2EntryAllowance * (G.nep - C.k) +
      stage2ByteAllowance * (G.n - entryPos G C.k)) :
    (p + 2) + walkPotential G { C with k := G.nep } ≤ walkPotential G C := by
  have hz : walkPotential G { C with k := G.nep } = 0 :=
    walkPotential_zero_of_nep_le G (le_of_eq rfl)
  rw [hz, Nat.add_zero]
  simp only [walkPotential, boundary_eq_entryPos G hk]
  exact h

/-- **The measure dominates the iteration count.**  The outer radix is
`cap + 1 ≥ 1`, so the remaining entries are at most the measure: the strong
recursion on `nep - k` is inside the one on the measure. -/
theorem walkIterations_le_measure {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) :
    G.nep - C.k ≤ walkMeasure G C := by
  have hcap : 1 ≤ walkInnerCap G + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have h1 : G.nep - C.k ≤ (G.nep - C.k) * (walkInnerCap G + 1) := by
    simpa using Nat.mul_le_mul_left (G.nep - C.k) hcap
  simp only [walkMeasure]
  omega

/-- **The measure is a termination witness, not a step count.**  Its outer
factor is the inner budget's radix, `4 * n + 6`, so at `nep` entries and `n`
bytes it is at least `nep * (4 * n + 6)` — while the record's own terms are
`32 * nep + 8 * n + 32`. -/
theorem walkMeasure_ge {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) :
    (G.nep - C.k) * (4 * G.n + 6) ≤ walkMeasure G C := by
  have hradix : walkInnerCap G + 1 = 4 * G.n + 6 := by simp [walkInnerCap]
  simp only [walkMeasure]
  rw [hradix]
  omega

/-- **The measurement that says the measure cannot be spent against the budget**:
at a hundred entries and a hundred bytes the measure's outer term is 40,600 and
the budget's two counted terms plus the finalisation allowance are 4,032. -/
theorem walkMeasure_exceeds_budget_at_100 :
    32 * 100 + 8 * 100 + 32 < 100 * (4 * 100 + 6) := by decide

/-! ### The loop's step and its completion

One premise: at the loop head, with the invariant and an unconsumed entry, either
one revolution with the potential spent, or the loop's exit.  The revolution's
target is the head again with the index strictly advanced — the header's pass
reads the phi the previous merge left, and `whileBody_step`'s guard is
`C.k < k < nep`, so the advance is not assumed to be one. -/

/-- **A segment followed by a counted run is one at the sum's count.**  A step whose
dispatch consumes its last entry is a segment to the state the dispatch reaches and
then that state's own run, and this is the prefix arithmetic the two compose by. -/
theorem WalkSegment.andRun {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s s₁ : State} {Cd : WalkCarry G} {sd : State} {p q : Nat}
    (hseg : WalkSegment calls G C s Cd sd p)
    (hrun : ∀ n, runFuel calls (q + n) stage2Body sd = runFuel calls n stage2Body s₁) :
    ∀ n, runFuel calls (p + q + n) stage2Body s = runFuel calls n stage2Body s₁ := by
  intro n
  rw [show p + q + n = p + (q + n) from by omega, hseg.run (q + n), hrun n]

/-- The thirteen arguments the record's boundary is stated at, spelled once in this
module so the loop's step, its completion and the predicate below name one list.
`JsonStage2WalkTargetPost`'s `walkFinishArgs` is the same list, and the two are
definitionally equal, so a boundary proved at one is a boundary at the other. -/
def walkTargetArgs {m0 : Mem} (G : WalkGeom m0) : List Value :=
  [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
   .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
   .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
   .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err]

/-- **The boundary at a fixed staging.**  `stage2Boundary` is existential in its
eight scratch witnesses; this is the same statement with those witnesses tied to
the adapter's staging `S`.  The frame's scratch entries are then the objects the
caller staged at the appended arguments, which is what a consumer of the count
slots needs: the post's generic witnesses could cover any region, so a frame read
at them says nothing about the caller's slots. -/
def Stage2BoundaryAtN (c ctype cst tok s z e d : Nat) (args : List Value) (mem : Mem)
    (next : Nat) (m : Mem) (v : Value) : Prop :=
  ∃ w : Stage2BoundaryWitness, Stage2BoundaryFacts w args mem next m v ∧
    w.c = c ∧ w.ctype = ctype ∧ w.cst = cst ∧ w.tok = tok ∧
    w.s = s ∧ w.z = z ∧ w.e = e ∧ w.d = d

/-- The same at a staging.  An `abbrev` so the eight addresses are reducible and a
rewrite of the staging rewrites the statement. -/
abbrev Stage2BoundaryAt {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    (args : List Value) (mem : Mem) (next : Nat) (m : Mem) (v : Value) : Prop :=
  Stage2BoundaryAtN S.c S.ctype S.cst S.tok S.s S.z S.e S.d args mem next m v

/-- **The fixed post at the boundary's thirteen arguments.**  This is the post a
record at the adapter's eight staging numbers states: the boundary at `args`,
with the scratch witnesses tied to those numbers. -/
def Stage2PostFixed (c ctype cst tok s z e d : Nat) (args : List Value) (mem : Mem)
    (next : Nat) : Outcome → Prop
  | .ret (some v) m => Stage2BoundaryAtN c ctype cst tok s z e d args mem next m v
  | _ => False

/-- **The post at a fixed staging**, at an outcome. -/
def Stage2PostAt {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    (args : List Value) (mem : Mem) (next : Nat) : Outcome → Prop
  | .ret (some v) m => Stage2BoundaryAt G S args mem next m v
  | _ => False

/-- **The walk's post at a loop state.**  `q` steps carry the state to a return, at
the verdict the run reaches and at the memory it returns, and the record's boundary
holds there (`stage2Boundary`, `JsonStage2Contract`) **at the carry's own staging**.
It is the terminal vocabulary the loop's branch needs and the one `WalkTargetRun`
could not state: that predicate is existential in the memory, and the record's post
is about the memory the run returns.  The fixed staging is what makes the frame
readable at the caller's count slots.

The count is the same one the terminal disjunct carried: `q` is the run's length less
the two terminal steps, so `q + 2` bounds the whole finalisation.  The thirteen
arguments are spelled once (`walkTargetArgs`); `JsonStage2WalkTargetPost` spells the
same list as `walkFinishArgs` and proves the boundary at all four terminal routes'
returned memories. -/
def WalkTargetPost (calls : Calls) {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) : Prop :=
  ∃ (q : Nat) (v : BitVec 64) (m : Mem), q + 2 ≤ 27 ∧
    runFuel calls (q + 2) stage2Body s = some (.ret (some (.int 64 v)) m) ∧
    Stage2BoundaryAt G C.stage (walkTargetArgs G) m0 G.next0 m (.int 64 v)

/-- **The loop's next step**: at the head, a revolution (potential spent) or the
loop's terminal run with the record's post at the memory it returns.  The terminal
bound is the potential *beside* `F`, not `F` alone: the last entry's dispatch is
byte-dependent work like any other revolution's, so the branch that dispatches it and
then finalises is bounded by the credit it consumes plus the finalisation allowance.

**The verdict is the run's, because no single one covers every state.**  At
`cleanup478.i` the accepted route returns `1` and the two refusal routes return `0`
(the three tails in `JsonStage2WalkExitProducer`), so a `v` fixed here would speak
about states the body does not have — and entry-stream exhaustion is not acceptance:
the terminal index at the merge says no entry is left, while the finalisation that
follows still decides.

**What a producer of this takes.**  `walkLoopStepThree_of_dispatchResult`
(`JsonStage2WalkDispatchThreeOfRun`) is the rule the layer applies: the dispatch's
result, a post producer at each of the finalisation's two entry blocks (`cleanup478.i`
and `if.then`) keyed to the outcome's own cells, and the merge's `%nep` value bounded
by the stream.  The arena word at the head is *not* among them: it was the third
argument once, and it was deleted as inert — neither the exit's producer nor this
step's consumer read it, and a slot holding `C.alen` is not a fact of the loop head at
all, since the reserve advances the carry by a token's document extent while the
write-back stores the decoded length (`JsonStage2WalkArenaWord`). -/
def WalkLoopStepThree (calls : Calls) {m0 : Mem} (G : WalkGeom m0) (F : Nat) : Prop :=
  ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead → C.k < G.nep →
    (∃ (C' : WalkCarry G) (s' : State) (p : Nat),
        WalkSegment calls G C s C' s' p ∧ C'.block = walkLoopHead ∧
        C.k < C'.k ∧ C'.k < G.nep ∧ p + walkPotential G C' ≤ walkPotential G C)
    ∨ (∃ (q : Nat) (v : BitVec 64) (m : Mem),
        q ≤ walkPotential G C + F ∧
        runFuel calls (q + 2) stage2Body s = some (.ret (some (.int 64 v)) m) ∧
        Stage2BoundaryAt G C.stage (walkTargetArgs G) m0 G.next0 m (.int 64 v))

/-- **The loop finishes, and its run is inside the potential.**  Strong recursion
on the remaining entries: the revolution's advance shortens it, and the terminal
bound is the potential at the state it is taken from plus `F` — the same credit,
because the last entry's dispatch is that state's remaining potential.  The verdict
and the memory are the terminal run's, carried out of the recursion rather than fixed
in advance, and the boundary is read at that memory. -/
theorem walkLoopFinishesThree {calls : Calls} {m0 : Mem} {G : WalkGeom m0} {F : Nat}
    (hstep : WalkLoopStepThree calls G F) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead) (hk : C.k < G.nep) :
    ∃ (q : Nat) (v : BitVec 64) (m : Mem),
      q + 2 ≤ walkPotential G C + F + 2 ∧
      runFuel calls (q + 2) stage2Body s = some (.ret (some (.int 64 v)) m) ∧
      Stage2BoundaryAt G C.stage (walkTargetArgs G) m0 G.next0 m (.int 64 v) := by
  have key : ∀ (m : Nat), ∀ (C : WalkCarry G) (s : State), G.nep - C.k = m →
      WalkInv G C s → C.block = walkLoopHead → C.k < G.nep →
      ∃ (q : Nat) (v : BitVec 64) (mr : Mem),
        q + 2 ≤ walkPotential G C + F + 2 ∧
        runFuel calls (q + 2) stage2Body s = some (.ret (some (.int 64 v)) mr) ∧
        Stage2BoundaryAt G C.stage (walkTargetArgs G) m0 G.next0 mr (.int 64 v) := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
        intro C s hm hInv hhead hk
        rcases hstep C s hInv hhead hk with
          ⟨C', s', p, hseg, hhead', hklt, hklt', hpot⟩ |
          ⟨q, v, mr, hq, hrun, hb⟩
        · obtain ⟨q, v, mr, hq', hrun', hb'⟩ :=
            ih (G.nep - C'.k) (by omega) C' s' rfl hseg.inv' hhead' hklt'
          rw [hseg.stage_eq] at hb'
          refine ⟨p + q, v, mr, by omega, ?_, hb'⟩
          rw [show p + q + 2 = p + (q + 2) from by omega, hseg.run (q + 2)]
          exact hrun'
        · exact ⟨q, v, mr, by omega, hrun, hb⟩
  exact key (G.nep - C.k) C s rfl hInv hhead hk

/-- **The completion at the potential's budget.**  The seed's `j` steps, the
loop's run and the returning step fit `walkPotential + the finalisation
allowance`, which is `j + F + 2 ≤ 32`'s content. -/
theorem walkCompletes_of_loop {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s sEntry : State} {j F : Nat}
    (hseed : ∀ n, runFuel calls (j + n) stage2Body sEntry = runFuel calls n stage2Body s)
    (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead) (hk : C.k < G.nep)
    (hstep : WalkLoopStepThree calls G F) (hF : j + F + 2 ≤ stage2FinalisationAllowance) :
    ∃ v' m, runFuel calls (walkPotential G C + stage2FinalisationAllowance) stage2Body sEntry
      = some (.ret v' m) := by
  obtain ⟨q, v, mr, hq, hrun, -⟩ :=
    walkLoopFinishesThree hstep C s hInv hhead hk
  have htotal : runFuel calls (j + (q + 2)) stage2Body sEntry =
      some (.ret (some (.int 64 v)) mr) := by
    rw [hseed (q + 2)]
    exact hrun
  have hle : j + (q + 2) ≤ walkPotential G C + stage2FinalisationAllowance := by omega
  exact ⟨some (.int 64 v), mr, runFuel_mono_le hle htotal⟩

/-- **The completion at the record's two counted terms.**  The potential is
inside `32 * nep + 8 * n` at the invariant, so the walk completes at that plus
the finalisation allowance — `stage2Budget` without the escape-position term. -/
theorem walkCompletes_of_loop_budget {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s sEntry : State} {j F : Nat}
    (hseed : ∀ n, runFuel calls (j + n) stage2Body sEntry = runFuel calls n stage2Body s)
    (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead) (hk : C.k < G.nep)
    (hstep : WalkLoopStepThree calls G F) (hF : j + F + 2 ≤ stage2FinalisationAllowance) :
    ∃ v' m, runFuel calls (32 * G.nep + 8 * G.n + 32) stage2Body sEntry =
      some (.ret v' m) := by
  obtain ⟨v', m, hrun⟩ :=
    walkCompletes_of_loop hseed hInv hhead hk hstep hF
  have hpot := walkPotential_le G C hInv
  refine ⟨v', m, ?_⟩
  refine runFuel_mono_le ?_ hrun
  simp only [stage2EntryAllowance, stage2ByteAllowance, stage2FinalisationAllowance] at hpot ⊢
  omega

/-! ### At the record's budget

`stage2Budget` reads three of the ABI's words: the entry count, the document's
length and the escape count.  The potential's bound is the first two plus the
finalisation allowance, and the escape count's term — `32 * nxp` — is the one
the bound does not name, so the two counted terms fit the record's budget as soon
as the two witnesses are their words' values.  The document's bound is
`stage2MaxDocument`'s, and the entry count's follows from the entry stream: its
positions are strictly increasing and inside the document, so there are at most
`n` of them (`nep_le`). -/

/-- **The potential's bound is inside `stage2Budget`**, at the ABI's thirteen
words. -/
theorem walkBudget_le_stage2Budget {mem : Mem}
    {b n ep nep xp nxp dst dstcap ndst ev evcap nev err : Nat}
    (hn : n < 2 ^ 64) (hnep : nep < 2 ^ 64) :
    32 * nep + 8 * n + 32 ≤
      stage2Budget [.ptr b, .int 64 (BitVec.ofNat 64 n), .ptr ep,
        .int 64 (BitVec.ofNat 64 nep), .ptr xp, .int 64 (BitVec.ofNat 64 nxp),
        .ptr dst, .int 64 (BitVec.ofNat 64 dstcap), .ptr ndst, .ptr ev,
        .int 64 (BitVec.ofNat 64 evcap), .ptr nev, .ptr err] mem := by
  simp only [stage2Budget, stage2EntryAllowance, stage2ByteAllowance,
    stage2PositionAllowance, stage2FinalisationAllowance, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hnep]
  omega

/-- **The completion at the record's own budget.**  The walk completes at
`stage2Budget` of the ABI's thirteen words, from the seed, the loop's step and the
two width facts — the completion conjunct of `Stage2WalkObligation` at the
geometry's numbers rather than at the potential's. -/
theorem walkCompletes_at_stage2Budget {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s sEntry : State} {j F : Nat}
    {b ep xp dst dstcap ndst ev evcap nev err nxp : Nat}
    (hseed : ∀ n, runFuel calls (j + n) stage2Body sEntry = runFuel calls n stage2Body s)
    (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead) (hk : C.k < G.nep)
    (hstep : WalkLoopStepThree calls G F) (hF : j + F + 2 ≤ stage2FinalisationAllowance)
    (hn : G.n < 2 ^ 64) (hnep : G.nep < 2 ^ 64) :
    ∃ v' m, runFuel calls
        (stage2Budget [.ptr b, .int 64 (BitVec.ofNat 64 G.n), .ptr ep,
          .int 64 (BitVec.ofNat 64 G.nep), .ptr xp, .int 64 (BitVec.ofNat 64 nxp),
          .ptr dst, .int 64 (BitVec.ofNat 64 dstcap), .ptr ndst, .ptr ev,
          .int 64 (BitVec.ofNat 64 evcap), .ptr nev, .ptr err] m0)
        stage2Body sEntry = some (.ret v' m) := by
  obtain ⟨v', m, hrun⟩ := walkCompletes_of_loop_budget hseed hInv hhead hk hstep hF
  exact ⟨v', m, runFuel_mono_le (walkBudget_le_stage2Budget hn hnep) hrun⟩

/-! ### At the seed

The seed's three-step prefix, its invariant and its empty carry: no entry is
consumed, so the credit's entry term is all of `32 * nep`, and the byte term is the
document from the first entry's position — the bytes the walk has not reached.  The
boundary agrees with the stream's position there given an entry to dispatch, and that
is the hypothesis the seed's potential carries.  The finalisation allowance covers
the exit's `F ≤ 27` steps, the seed's three and the return's one. -/

/-- **The seed's potential is its credit.**  `walkSeed`'s carry has consumed no
entries, so the entry term is the whole stream's and the byte term is the document
from the first entry's position.  The hypothesis is what makes the second sentence
true: at `G.nep = 0` the seed's boundary is the document's length at index zero, so
the credit is zero rather than `8 · G.n`. -/
theorem walkPotential_seed {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G)
    (hn : 0 < G.nep) :
    walkPotential G (walkSeed G S) =
      stage2EntryAllowance * G.nep +
        stage2ByteAllowance * (G.n - entryPos G 0) := by
  have hk : (walkSeed G S).k = 0 := rfl
  simp only [walkPotential, hk, Nat.sub_zero, boundary_eq_entryPos G hn]

/-- **The walk completes at the seed's potential plus the finalisation
allowance**, from the seed's prefix (`walkSeedPrefix_runFuel`'s `3`), the
invariant at the loop head (`walkSeedInvariant_geometry`), and the loop's step
with an exit inside twenty-seven steps. -/
theorem walkCompletes_of_seed_loop {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    (S : WalkStage G) {s sEntry : State} {F : Nat}
    (hn : 0 < G.nep)
    (hseed : ∀ n, runFuel calls (3 + n) stage2Body sEntry = runFuel calls n stage2Body s)
    (hInv : WalkInv G (walkSeed G S) s) (_hpc : s.pc = walkLoopHead)
    (hstep : WalkLoopStepThree calls G F) (hF : F ≤ 27) :
    ∃ v' m, runFuel calls
        (stage2EntryAllowance * G.nep +
          stage2ByteAllowance * (G.n - entryPos G 0) + stage2FinalisationAllowance)
        stage2Body sEntry = some (.ret v' m) := by
  have hk : (walkSeed G S).k < G.nep := by
    simp only [walkSeed]
    exact hn
  obtain ⟨v', m, hrun⟩ :=
    walkCompletes_of_loop (C := walkSeed G S) (j := 3) (F := F) hseed hInv
      (walkSeed_block G S) hk hstep (by
        simp only [stage2FinalisationAllowance]
        omega)
  refine ⟨v', m, ?_⟩
  rw [walkPotential_seed G S hn] at hrun
  simpa only [stage2EntryAllowance, stage2ByteAllowance, stage2FinalisationAllowance]
    using hrun

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.WalkSegment.trans
#print axioms LeanLLVM.Refinement.WalkScope.WalkChain.append
#print axioms LeanLLVM.Refinement.WalkScope.WalkChain.inv_last
#print axioms LeanLLVM.Refinement.WalkScope.WalkSegment.of_chain
#print axioms LeanLLVM.Refinement.WalkScope.WalkSegment.ret
#print axioms LeanLLVM.Refinement.WalkScope.WalkSegment.andRun
#print axioms LeanLLVM.Refinement.WalkScope.walkSpans_sum_le
#print axioms LeanLLVM.Refinement.WalkScope.walkPotential_le
#print axioms LeanLLVM.Refinement.WalkScope.walkPotential_spend
#print axioms LeanLLVM.Refinement.WalkScope.entryPos_lt
#print axioms LeanLLVM.Refinement.WalkScope.entryPos_mono
#print axioms LeanLLVM.Refinement.WalkScope.walkPotential_seed
#print axioms LeanLLVM.Refinement.WalkScope.walkIterations_le_measure
#print axioms LeanLLVM.Refinement.WalkScope.walkMeasure_ge
#print axioms LeanLLVM.Refinement.WalkScope.walkMeasure_exceeds_budget_at_100
#print axioms LeanLLVM.Refinement.WalkScope.walkLoopFinishesThree
#print axioms LeanLLVM.Refinement.WalkScope.walkCompletes_of_loop
#print axioms LeanLLVM.Refinement.WalkScope.walkCompletes_of_loop_budget
#print axioms LeanLLVM.Refinement.WalkScope.walkBudget_le_stage2Budget
#print axioms LeanLLVM.Refinement.WalkScope.walkCompletes_at_stage2Budget
#print axioms LeanLLVM.Refinement.WalkScope.walkCompletes_of_seed_loop

end WalkScope

end LeanLLVM.Refinement
