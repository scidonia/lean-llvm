/-
The two-entry token's path: the facts its links need at states the segment reaches.

## What this module is for

`HstringFacts` (`JsonStage2WalkDispatchWitnessString`) supplies the fifteen-block
segment.  Composing it means threading each link's *target* state into the next
link's hypotheses, and the links' conclusions now name those states
(`WalkLink.if_end207_i`, `if_then219_i`, `if_end245_i`, `if_end290_i`,
`if_then281_i` among them).  What a composition still owes is the handful of
*facts* that no clause of `WalkInv` carries at the state where they are read.
This module proves the one of them that is a lemma rather than a premise.

## The root slot across `if.end207.i`

`if.then219.i` loads `%9` from `%root_done.i` — the second of `entry`'s four
allocations, at `G.next0 + 8`, four bytes wide — and hands it to
`s2_value_pos`, which at depth zero returns it unchanged.  The state it reads is
`if.end207.i`'s target, whose memory is the caller's with the *cursor record's*
`k` field written at `%k11.i = C.stage.c + 32`.

`WalkInv` binds the log's five words and the event trace, and no clause binds the
root slot, so the read has to be carried across that store.  It is a *crossing*,
not a premise: the cursor record is one of the seven objects the caller staged,
its extent ends at or below the cursor (`WalkStage.sevenEnd`), and the root slot
begins eight bytes above the cursor, so the store cannot reach it.
`walkReadBytes_rootSlot_of_cursorK` is that statement and
`WalkInv.readBytes_rootSlot` is it at an invariant state.

## What is *not* a lemma here

The log's base word (`readBytes mem C.stage.z 8 = some (wordBytes 8 G.ev)`) is
not one, and the reason is worth recording at the place a reader would try:
`%z`'s first eight bytes are *inside* the walk's write extent — `walkPresent`
carries the whole `(z, stage2LogExtent)` object — so `WalkInv.frame` (silence
*outside* that extent) says nothing about them, and the staging's clauses give
presence over the object (`WalkInv.owned`) rather than the value it holds.  The
value is the adapter's initialisation's, which `WalkStage` does not carry.  So
that fact is a supplied premise of the bundle at the head it is read from, not a
consequence of the invariant.
-/

import LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessString

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The cursor record's extent

The seven objects the walk writes are staged at or below the cursor, so the
cursor record — the first of them — ends there too.  This is the fact every
crossing of `%k11.i`'s store reads. -/

/-- **The cursor record ends at or below the call's cursor.** -/
theorem walkCursorRecord_end {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} :
    C.stage.c + stage2CursorExtent ≤ G.next0 :=
  C.stage.sevenEnd (C.stage.c, stage2CursorExtent) (by simp [stage2StagedWrites])

/-- **A read of the root slot survives `if.end207.i`'s cursor-record store.**
The store is eight bytes at `c + 32`; the cursor record's extent is `1192`, so
the store ends at `c + 40`, at or below the cursor, and the root slot begins at
`cursor + 8`. -/
theorem walkReadBytes_rootSlot_of_cursorK {m : Mem} {c next0 k : Nat}
    (hsep : c + stage2CursorExtent ≤ next0) :
    readBytes (writeBytes m (c + 32) (wordBytes 8 k)) (next0 + 8) 4
      = readBytes m (next0 + 8) 4 := by
  refine walkReadBytes_writeBytes_outside (start := c + 32) (addr := next0 + 8) (n := 4) ?_
  right
  have hlen : (wordBytes 8 k).length = 8 := natToBytes_length _ _
  simp only [stage2CursorExtent] at hsep
  rw [hlen]
  omega

/-- **The root slot's four bytes, read at the state `if.end207.i` leaves.**  The
head's read is the one `if.then219.i` needs: the store between them is the cursor
record's `k` field, and the root slot is above it.  No invariant is consumed — the
store's separation is `WalkStage.sevenEnd` at the staging the carry names — so the
fact is stated at the carry. -/
theorem walkReadBytes_rootSlot_at {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} {k : Nat} {rd : BitVec 32}
    (hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rd.toNat 4)) :
    readBytes (writeBytes s.mem (C.stage.c + 32) (wordBytes 8 k)) (G.next0 + 8) 4
      = some (natToBytes rd.toNat 4) := by
  rw [walkReadBytes_rootSlot_of_cursorK (c := C.stage.c) (next0 := G.next0)
    (walkCursorRecord_end (G := G) (C := C))]
  exact hread

/-! ### Axiom footprints -/

#print axioms LeanLLVM.Refinement.WalkScope.walkCursorRecord_end
#print axioms LeanLLVM.Refinement.WalkScope.walkReadBytes_rootSlot_of_cursorK
#print axioms LeanLLVM.Refinement.WalkScope.walkReadBytes_rootSlot_at

end WalkScope

end LeanLLVM.Refinement
