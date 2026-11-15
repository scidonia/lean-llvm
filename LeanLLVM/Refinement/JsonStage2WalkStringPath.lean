/-
The two-entry token's path: where the crossings the links need now live.

## What moved, and why

A composition of the token's links threads each link's *target* state into the
next link's hypotheses, so the facts a link reads must be stated at the memory the
previous link leaves.  Two of them are crossings of `if.end207.i`'s cursor-record
store: the root slot at `G.next0 + 8` (`if.then219.i`) and the log's `%z + 48`
word the arena's check and the reservation read.  A third, the log's arena-base
word at `%z + 40`, is *not* a crossing: no clause binds it, so it is a supplied
premise (the bundle's R5).

Those lemmas name only `WalkStage`, `State` and `readBytes`, and the composition
lives in `JsonStage2WalkDispatchWitnessString` — a module this one imports.  So a
module above the bundle cannot supply them to it: the lemmas moved *down* into the
bundle's `The root slot and the log across the cursor-record store` section
(`walkCursorRecord_end`, `walkReadBytes_rootSlot_of_cursorK`,
`walkReadBytes_rootSlot_at`, and the log's `walkCursorLog_sep` /
`walkReadBytes_log_of_cursorK`).  This module keeps the pins for the three that
came from here, so the footprints stay stated where they were stated before.

## What is *not* a lemma, here or below

The log's base word (`readBytes mem C.stage.z 8 = some (wordBytes 8 G.ev)`) is not
one, and the reason is worth recording at the place a reader would try: `%z`'s
first eight bytes are *inside* the walk's write extent — `walkPresent` carries the
whole `(z, stage2LogExtent)` object — so `WalkInv.frame` (silence *outside* that
extent) says nothing about them, and the staging's clauses give presence over the
object (`WalkInv.owned`) rather than the value it holds.  The value is the
adapter's initialisation's, which `WalkStage` does not carry.  So that fact is a
supplied premise at the state that reads it, not a consequence of the invariant;
the bundle names it R3, and the arena's base word at `%z + 40` is R5 for the same
reason.
-/

import LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessString

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### Axiom footprints

The three crossings are in the bundle now; these pins are the footprints they had
where they were first stated. -/

#print axioms LeanLLVM.Refinement.WalkScope.walkCursorRecord_end
#print axioms LeanLLVM.Refinement.WalkScope.walkReadBytes_rootSlot_of_cursorK
#print axioms LeanLLVM.Refinement.WalkScope.walkReadBytes_rootSlot_at

end WalkScope

end LeanLLVM.Refinement
