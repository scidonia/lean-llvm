/-
# The whitespace skip's run: the composition around `wsRun`

Not imported by any target and not built by `lake build` — it elaborates against the
committed tree.

Everything this file has held is landed in `JsonStage2WalkRevolution`, above the
whitespace bundle: the definition layer, the skip's four visit segments, the run's
induction (`wsRun_go`, `wsRun`), and the composition around it — the seam (`wsSeamSeg`),
the first visit at each continuing class (`wsFirstSeg43/46/48`), the entry dispatch by
`%35`'s class (`wsEntry33/35/37`), the stop state's predecessor per class
(`wsStopAt_pre43/46/48`), the uniform tail (`contWsAfterPre`), the price (`wsPrice`) and
the three arm wrappers (`contWsRun33/35/37`).

The bundle's field surgery is *not* in the tree.  The 61-field version was drafted and
elaborated module-green — `HcontFacts` without `sl`/`hRun`/`hnRun`/`hcond_sl`, with the
class group `hClass` and the total stop term `wsSlS`, plus the derived
`contWsRunF`/`contWsPriceF` — but its producer (`hcontFacts_of_staging`) and consumer
(`walkRevolutionMergeSegWs`) were not finished, so it was reverted rather than left red.
Two facts the attempt established are recorded here for the next pass:

* the old `hRun` silently pinned the seam's byte to `%8` at its endpoint; with `hRun`
  gone, the bundle's `b8` and `x1` are two witnesses of one word, so the total bundle uses
  `x1` for both (64 − 5 + 1 = 60, the `hClass` addition included);
* the run's derivation needs the class *and* the skip's per-index group, the non-emptiness
  `ix.toNat < k`, the inner budget and the price's `entryPos` start — one field carrying
  them all is what makes a total producer possible.
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
