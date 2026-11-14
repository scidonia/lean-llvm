/-
# The arena cursor word: a predicate the exit no longer states

This module began as the cost of `WalkLoopStep`'s producer, whose third argument was the
arena word at the loop head:

```lean
readBytes s.mem (C.stage.z + 48) 8 = some (wordBytes 8 C.alen)
```

The obligation is gone: deleted in `3ea399e`, because it was both unsatisfiable and inert —
the sections below are the evidence, and `WalkExit`'s own docstring now records the deletion.
What remains here is what made the deletion decidable and what outlives it: the predicate
named (`WalkArenaWord`), its relation to `WalkInv.log_alen`, the seed's end, the write-back's
arithmetic (`arenaWord_writeBack_iff`, `not_arenaWord_of_lt`), and the census of the slot's
two writers.

**The rule this is worth remembering for:** the obligation survived as long as it did
because the predicate was *stated* and its two *ends* — the exit's premise, and the same
equality as a post clause — were two separate declarations, and nothing compared them.  A
premise that one end supplies and the other discards is invisible until both ends are held
in one hand, and a named predicate is what makes that comparison cheap.

**What it looked like and what it was.**  A producer of the equality would have meant naming
every successor along the dispatch; the equality's own falsity made the obligation six
statement lines of deletion instead, and a producer would have hidden that — a producer of a
falsehood reads as progress until someone asks what the premise is worth at both ends.

## Why `log_alen`'s inequality is not the equality the exit needs

`WalkInv.log_alen` is

```lean
∃ a, G.ndst0 ≤ a ∧ a ≤ C.alen ∧ readBytes s.mem (C.stage.z + 48) 8 = some (wordBytes 8 a)
```

and it is deliberately **not** `a = C.alen`, because the carry runs ahead of the slot
inside an append: `z_arena_reserve.exit` advances the carry by the token's document extent
and appends the window to the spans (`WalkLink.z_arena_reserve_exit`), the decoder then
writes the body, and only `if.else285.i` stores the slot — from `%z.val36 + %outn.i`, with
the store's own guard `hale : a + l ≤ C.alen`.  Between the reserve and the write-back the
slot is short of the carry by the part of the window the decoder has not filled, so an
equality clause in `WalkInv` would be **false on the walk's own path**, and no strengthening
of the invariant can replace the producer: the equality holds at a *moment*, and the moment
is a fact about the run.

`arenaWord_writeBack_iff` is that sentence mechanized: the slot after the store holds
`wordBytes 8 (a + l)`, so the exit's equality at the block's target holds **iff**
`a + l = C.alen` — the decoded prefix filling the reservation exactly.  The layer relates
those two numbers only by `≤` (`hale`, and `WalkInv.logArena_le` on the read side), so the
equality is supplied by whatever knows the decoder's output length equals the entry's
extent, and it is not a consequence of `WalkInv`.

## The predicate is a fact about a full reservation, not an invariant of the loop head

**Nothing in the layer forces the slot to hold `C.alen`.**  The two numbers are not the same
number, and they are not even functions of one another:

* `z_arena_reserve.exit` advances the carry by the token's **document extent** — the same
  `ext` it passes to the callee as the input length
  (`WalkLink.z_arena_reserve_exit`'s call arguments, `len = ext`);
* `if.else285.i` stores `%z.val36 + %outn.i`, and `%outn` is what the decoder wrote there:
  the body's extent on the copy arm, or the expander's **returned decoded length** on the
  escape arm (`JsonStage2StringBody`: `%call` → `%outn`).  `s2StringBodyPost`
  (`JsonStage2Helpers`) leaves the decoded length free of the input length.
* nothing lowers `alen` again: `stage2Body_arena_writers` bounds the writers to `entry` and
  `if.else285.i`, and no carry construction in the walk writes `alen` except the reserve
  exit's `C.alen + ext` (the seed's `G.ndst0` and `WalkDispatch`'s identity are the others).

So a body whose decoded length is shorter than its document extent — any escaping string —
leaves `slot < C.alen` at every subsequent loop head, and `not_arenaWord_of_lt` is that
state: the predicate is **false** there, not merely unproved.  `arenaWord_writeBack_iff` is
the same statement at the store: the equality holds at the write-back's target iff the
decoded prefix filled the reservation.

**Consequence.**  The equality was therefore **unsatisfiable at any input whose decoded
length is shorter than the extent it reserved**, and `WalkExit` asserted it twice — a premise
at the head and the same equality as a post clause at `sEnd`.  Its correct home is
`log_alen`'s witness `a`, not `C.alen`: the exit's slot copy *reads* `z + 48`, so the value it
carries is the slot's own, which `WalkInv.log_alen` already names (`a ≤ C.alen`), and the
exit's path stores nothing at that address (the census again).  Restating the clause at `a`
would have duplicated an invariant — `WalkInv G Cend sEnd` already carries that existential —
so the clause was deleted instead (`3ea399e`), and a producer of the equality at `C.alen`
would have been a producer of a falsehood.

**Why it was deleted rather than produced.**  Both ends discarded it: the only producer of
`WalkExit` took the head's word as an unused binder and never read it, and the only consumer
(`walkLoopStep_of_dispatch_exit`) destructured the post's word clause as `-`.  Nor was the
exit the whole story — the producer's live arena premise was the same equality one state
later, at `cleanup478.i`, where the slot has not been rewritten either and `log_alen` gives
`a ≤ C.alen` just as at the head.  So the repair was a deletion: the head word from the
premise, the word clause from the post, the merge's word from the producer.  `3ea399e`
performs it, and the tree confirms no proof step depended on them — the producer and all four
importers of `WalkExit` build, and the tracked test compiles.

**The search, after the deletion.**  `wordBytes 8 C.alen` appears in no statement of the
development: `grep -rn "wordBytes 8 C.alen" LeanLLVM/` now returns this module's own
predicate and the record of the deletion in `WalkExit`'s docstring, and nothing else — no
premise, no post, no lemma.  Before the deletion the same grep returned exactly the two
`WalkExit` clauses this section finds unsatisfiable, which is the whole argument: no third
statement ever mentioned the equality.  `WalkInv.logArena_le` reads the slot as `≤`, and
`spans_inside`/`spans_end` bound extents by the document and by the cursor.

## The two writers, and the number of revisions

`stage2Body_arena_writers` (`JsonStage2WalkAssembly`) decides it: of the body's 165 blocks,
exactly two store through `%alen` — `entry` (the initialisation, whose store is the seed's
`G.ndst0`) and `if.else285.i` (the append's write-back).  `%alen` is the body's only address
for `z + 48`.  So a run revises the slot **at most once per consumed entry**: `entry` once,
then one write-back per append, so at most `G.nep + 1` revisions in a run, and no revision
between one write-back and the next reserve.

That was the obligation's size, and it is why the statement would have been head-to-head
rather than per-path: *one* predicate, preserved across each revolution — not a memory trace
of the dispatch's ~15 blocks per token class times the scan's visits.  The two ends are
`WalkSeedState`'s slot clause (the seed, `walkSeed_arenaWord` below) and `if.else285.i`'s
store; there is no third place to look, and between them the slot can only be *revised*,
never silently rewritten.

## Why no producer was built, and what its absence shows about the vocabulary

This module does **not** prove the head-to-head preservation, and the reason is structural
rather than a missing arithmetic lemma — which is why the obligation was deleted rather than
produced.  The walk's step vocabulary carries no memory clause:
`WalkLink` is `{inv, step, inv', mono}` and `WalkSegment` is `{run, inv'}` — the segment's
own docstring says a general memory clause "would have to be a write trace, composed by
`trans`".  So the only memory-carrying statement that crosses a step or a segment is
`WalkInv.log_alen` — the inequality.

A memory equation is available for a step **only where a block's lemma names its
successor**: `walkIfEnd473_at` concludes `s' = { s with pc := …, pre := … }`, so its
successor's memory is the source's, and that is the idiom the exit producer uses for its
own blocks (`JsonStage2WalkExitProducer`, 489 lines for the last entry's tail).  The
dispatch's composites — `hlastPrefixSeg`, `contScanRounds`, `walkScanToMerge` — and the
revolution's two closing steps (`walkBack_step_at`, `whileBody_step`) name no memory, so
the predicate cannot be transported across them.

So a producer of the equality would have had to do one of two things, and neither is
assembly:

* **name every successor** along the dispatch — a second pass over the path at memory
  level, sized like the exit producer — with the write-back's `a + l = C.alen` as the one
  premise such a pass cannot derive; or
* **add a memory clause to the step and segment vocabulary** — a write trace with its own
  composition rule — which is a change to `JsonStage2WalkScope`'s `WalkLink` and
  `JsonStage2WalkTraverse`'s `WalkSegment`, and therefore to every producer that builds one.

Neither was needed, because the equality is not true.  The structural fact stands on its own
and is the constraint any future memory-level obligation meets: **a memory fact does not
cross a step or a segment unless some lemma names the successor**, the layer's composites
name their targets existentially, and the only memory-carrying clause that crosses them is
`WalkInv.log_alen`.

What this module settles — independently of the obligation it was written for — is the
predicate's shape, its compatibility with `log_alen`, the seed's base case, the two writer
blocks, the revision count, and the exact arithmetic the write-back's equality costs.
-/

import LeanLLVM.Refinement.JsonStage2WalkScope

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The predicate, in the shape the exit used to require -/

/-- **The arena cursor word at its slot.**  `%alen` addresses `z + 48`; the log's index is
the value the word holds.  This is the shape the exit used to require, named because the
comparison that decided against it needs a name: the seed's clause (`walkSeed_arenaWord`),
the write-back's store (`arenaWord_writeBack_iff`), and the two deleted `WalkExit` clauses
are all this predicate. -/
def WalkArenaWord {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) : Prop :=
  readBytes s.mem (C.stage.z + 48) 8 = some (wordBytes 8 C.alen)

/-- **The equality is the invariant's arena clause at its tight point.**  A state carrying
the word still satisfies `WalkInv`'s `log_alen` — with `a := C.alen` — so the equality was a
*strengthening*, not a competing clause: asserting it needed nothing removed from the
invariant, which is why its deletion takes nothing away either. -/
theorem WalkArenaWord.log_alen {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkArenaWord G C s) (hInv : WalkInv G C s) :
    ∃ a, G.ndst0 ≤ a ∧ a ≤ C.alen ∧
      readBytes s.mem (C.stage.z + 48) 8 = some (wordBytes 8 a) :=
  ⟨C.alen, hInv.alen_ge, le_rfl, h⟩

/-- **The seed end.**  The initialisation stores `G.ndst0` in the slot and the seed's carry
starts there, so the predicate holds at the loop head before any revision — the base case
any head-to-head producer starts from, and the reason `entry` needs no separate treatment:
its store is the seed's value. -/
theorem walkSeed_arenaWord {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) {s : State}
    (h : WalkSeedState G S s) : WalkArenaWord G (walkSeed G S) s := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, halen, -⟩ := h
  show readBytes s.mem (S.z + 48) 8 = some (wordBytes 8 (walkSeed G S).alen)
  rw [show (walkSeed G S).alen = G.ndst0 from rfl]
  exact halen

/-! ### The write-back's store, and what it costs

`if.else285.i` is `load %32, %outn.i; %add289.i = %z.val36 + %32; store %add289.i, %alen`
(`walkIf_else285_i`), and its link's guard is `hale : a + l ≤ C.alen`.  The two lemmas here
say what the store leaves and what the exit's equality consequently costs. -/

/-- **A store at the slot reads back as itself.**  `readBytes_writeBytes_same` at the
cursor's address and the word's length. -/
theorem arenaWord_store (m : Mem) (z v : Nat) :
    readBytes (writeBytes m (z + 48) (wordBytes 8 v)) (z + 48) 8 = some (wordBytes 8 v) := by
  have h := readBytes_writeBytes_same m (wordBytes 8 v) (addr := z + 48)
  simpa only [wordBytes, natToBytes_length] using h

/-- **A word below `2 ^ 64` is its own eight bytes.**  `wordBytes` keeps `v % 2 ^ 64`, so
two words below the modulus that print the same bytes are the same number. -/
theorem wordBytes8_inj {v w : Nat} (hv : v < 2 ^ 64) (hw : w < 2 ^ 64)
    (h : wordBytes 8 v = wordBytes 8 w) : v = w := by
  have hb := congrArg bytesToNat h
  simp only [wordBytes, natToBytes_toNat] at hb
  rw [show (256 : Nat) ^ 8 = 2 ^ 64 from by decide, Nat.mod_eq_of_lt hv,
    Nat.mod_eq_of_lt hw] at hb
  exact hb

/-- **The write-back's price.**  After the append's store the slot holds `a + l`, so the
exit's equality holds at the block's target **iff** the decoded prefix filled the
reservation.  The layer knows `a + l ≤ C.alen` (`hale`) and no more, which is exactly the
distance between `log_alen`'s inequality and the word the exit needs. -/
theorem arenaWord_writeBack_iff {m : Mem} {z a l alen : Nat}
    (hj : a + l < 2 ^ 64) (ha : alen < 2 ^ 64) :
    readBytes (writeBytes m (z + 48) (wordBytes 8 (a + l))) (z + 48) 8 =
        some (wordBytes 8 alen) ↔ a + l = alen := by
  rw [arenaWord_store, Option.some.injEq]
  exact ⟨fun h => wordBytes8_inj hj ha h, fun h => by rw [h]⟩

/-- **The lag is the store's, not the invariant's.**  If the slot holds `v` and `v` is
short of the carried cursor, the predicate is *false* at that state — which is the strict
case of the write-back's guard `hale`, i.e. the reserve has advanced the carry and the
store has not caught the slot up.  So no producer can read the equality off the reservation,
and no strengthening of `WalkInv` can put it there. -/
theorem not_arenaWord_of_lt {m : Mem} {z v alen : Nat}
    (hv : v < alen) (hvv : v < 2 ^ 64) (ha : alen < 2 ^ 64) :
    ¬ (readBytes (writeBytes m (z + 48) (wordBytes 8 v)) (z + 48) 8 =
        some (wordBytes 8 alen)) := by
  rw [arenaWord_store, Option.some.injEq]
  intro h
  exact absurd (wordBytes8_inj hvv ha h) (by omega)

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.WalkArenaWord.log_alen
#print axioms LeanLLVM.Refinement.WalkScope.walkSeed_arenaWord
#print axioms LeanLLVM.Refinement.WalkScope.arenaWord_writeBack_iff
#print axioms LeanLLVM.Refinement.WalkScope.not_arenaWord_of_lt

end WalkScope
end LeanLLVM.Refinement
