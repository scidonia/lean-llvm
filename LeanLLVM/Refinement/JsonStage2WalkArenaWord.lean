/-
# The arena cursor word: the exit's `hword`, and the size of producing it

`WalkLoopStep`'s producer (`walkLoopStep_of_dispatch_exit`, `JsonStage2WalkAssembly`) takes
three arguments, and the third is not implied by the other two:

```lean
hword : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
  readBytes s.mem (C.stage.z + 48) 8 = some (wordBytes 8 C.alen)
```

`WalkExit` only *takes* that word; `WalkDispatch` concludes `WalkInv` at the merge, whose
arena clause is the inequality `log_alen`.  So the word is its own producer.  This module
states what that producer is a statement about, lands the end it can land, and costs the
rest: the two blocks that write the slot, the number of times a run can revise it, and the
one arithmetic coincidence the exit's equality needs and the layer does not have.

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

## The two writers, and the number of revisions

`stage2Body_arena_writers` (`JsonStage2WalkAssembly`) decides it: of the body's 165 blocks,
exactly two store through `%alen` — `entry` (the initialisation, whose store is the seed's
`G.ndst0`) and `if.else285.i` (the append's write-back).  `%alen` is the body's only address
for `z + 48`.  So a run revises the slot **at most once per consumed entry**: `entry` once,
then one write-back per append, so at most `G.nep + 1` revisions in a run, and no revision
between one write-back and the next reserve.

That is the producer's size, and it is why the statement is head-to-head rather than
per-path: the obligation is *one* predicate, preserved across each revolution — not a
memory trace of the dispatch's ~15 blocks per token class times the scan's visits.  The
two ends are `WalkSeedState`'s slot clause (the seed, `walkSeed_arenaWord` below) and
`if.else285.i`'s store; there is no third place to look, and between them the predicate can
only be *revised*, never silently rewritten.

## What this module does not do, and why

It does **not** prove the head-to-head preservation, and the reason is structural rather
than a missing arithmetic lemma.  The walk's step vocabulary carries no memory clause:
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

So a producer of `hword` must do one of two things, and neither is assembly:

* **name every successor** along the dispatch — a second pass over the path at memory
  level, sized like the exit producer — with the write-back's `a + l = C.alen` as the one
  premise such a pass cannot derive; or
* **add a memory clause to the step and segment vocabulary** — a write trace with its own
  composition rule — which is a change to `JsonStage2WalkScope`'s `WalkLink` and
  `JsonStage2WalkTraverse`'s `WalkSegment`, and therefore to every producer that builds one.

What this module settles is the part that does not need either: the predicate's shape, its
compatibility with `log_alen`, the seed's base case, the two writer blocks, the revision
count, and the exact arithmetic the write-back's equality costs.
-/

import LeanLLVM.Refinement.JsonStage2WalkScope

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The predicate, in `hword`'s shape -/

/-- **The arena cursor word at its slot.**  `%alen` addresses `z + 48`; the log's index is
the value the word holds.  This is `hword`'s statement, named so the producer and its two
ends can be talked about: the seed's clause (`walkSeed_arenaWord`), the write-back's store
(`arenaWord_writeBack_iff`), and the exit's hypothesis are all this predicate. -/
def WalkArenaWord {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) : Prop :=
  readBytes s.mem (C.stage.z + 48) 8 = some (wordBytes 8 C.alen)

/-- **The equality is the invariant's arena clause at its tight point.**  A head carrying
the word still satisfies `WalkInv`'s `log_alen` — with `a := C.alen` — so the producer is a
*strengthening* at the head, not a competing clause: nothing has to be removed from the
invariant to carry both. -/
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
