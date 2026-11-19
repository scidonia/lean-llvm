/-
# The whitespace skip's run, and where it landed

Not imported by any target and not built by `lake build`; this file is the pointer to the
statements, not a draft of them.  Everything it once held is in `JsonStage2WalkRevolution`
and its `JsonStage2WalkRevolutionScanRound` import.

**The definitions.**  `JsonStage2WalkRevolutionScanRound` holds the document's byte
(`wsByte`, `wsX`); `JsonStage2WalkRevolution` holds the skip's own: `scanB_ofNat`, `wsLandS`
(the landing), `wsLeafS` (the three leaves as one function, its arms `wsLeafS_43/46/48`),
`wsStopS` (the leaf's cells at `if.end372.i`), and the two total terms the bundle's fields
name states with — `wsPreS` (the preheader `%35`'s class selects) and `wsSlS` (its stop).

**The visits.**  The continuing back edge is `wsContinue43/46/48`, the exit's is
`wsVisit43Exit/46Exit/48Exit`, and `wsExit43/46/48` is each exit's segment to `if.end372.i`
at `wsStopS`.  The exit is not a wall: it is the back-edge proof with `if_pos` on the leaf's
test and `pc` moved.

**The induction.**  `wsLatchAt` is the latch at counter `i + n`, `wsStopAt` the stop at `k`,
`wsCont`/`wsStop` the byte's three-way class, and `wsLeafS_43/46/48_ee`/`_cond` the two
cells every visit reads.  `wsRun_go` carries the segment, its target's invariant and both
cells together and concludes `∃ n, n ≤ 5·(k - i) ∧ WalkSegment … n`; `wsRun` is the same at
`d = 0`.

**The composition.**  `wsSeamSeg` is the seam link, `wsFirstSeg43/46/48` the first visit at
each entry class, `wsEntry33/35/37` (and `wsEntryAt33/35/37` at an arbitrary check state) the
`%35` dispatch, `wsStopAt_pre43/46/48` the stop's predecessor per class, `contWsAfterPreAt`
the uniform tail, `wsPrice` the price, and `contWsRunAt33/35/37` the three arm wrappers.
`HcontRunBody`/`contWsRunBody` derive the segment from its own rows, and
`HcontRunFacts`/`contWsRunF`/`contWsPriceAt` are the bundle's instance, at
`∃ N, N ≤ 5·(k - ix.toNat) + 10` — a bound rather than an equality, because a continuing
byte costs four links at `LeafBlock43`'s class and five at `46`/`48`'s; the split is entry
at most `4`, first visit at most `5`, latch visits at most `5·(k - i)`, seam `1`.

**The bundle no longer carries the run.**  `HcontFacts` has no `sl`, `b8`, `hRun`, `hnRun`,
`hcond_sl` or count; it carries the class field `hClass` — the byte's disjunction, the
per-index group `∀ q, ix.toNat ≤ q → q < k → wsCont G q`, `wsStop G k`, `ix.toNat < k`, the
inner budget `v.toNat - ix.toNat ≤ C.inner`, and the price's start
`entryPos G C.k ≤ ix.toNat` — and the run is derived from it.  `hcontFacts_of_staging`
(`JsonStage2WalkHcontFactsOfStaging`) is the producer and `hcontRunFacts_of_contFacts` the
class-C instance; `wsRunHeadAt` and `wsLandingSegAt` build the head and the landing from
the bundle, and `runFacts_of_runBundle` (`JsonStage2WalkDispatchRunHead`) the whole
`RunFacts`.

Two facts the shape rests on:

* the retired `hRun` pinned the seam's byte to `%8` at its endpoint; with it gone, the
  bundle's `b8` and `x1` are two witnesses of one word, so the bundle uses `x1` for both;
* the run's derivation needs the class and the per-index group, the non-emptiness
  `ix.toNat < k`, the inner budget and the price's `entryPos` start — one field carrying
  them all is what makes a total producer possible, and the group reaches `ix.toNat` itself
  because the first visit reads the entry's own first byte.

The pins are the module's own `#print axioms` block: `wsRun`, `contWsRunF`,
`contWsRunAt33/35/37` and `hcontRunFacts_of_contFacts` at
`[propext, Classical.choice, Quot.sound]`; `wsPrice`, `contWsPriceAt` and
`wsStopAt_pre43/46/48` at `[propext, Quot.sound]`; the leaf-state peels at `[propext]`.
-/

import LeanLLVM.Refinement.JsonStage2WalkRevolution

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

end WalkScope
end LeanLLVM.Refinement
