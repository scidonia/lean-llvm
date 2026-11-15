/-
# The whitespace skip's run: the composition around `wsRun`

Not imported by any target and not built by `lake build` — it elaborates against the
committed tree.

Everything this file has held is landed in `JsonStage2WalkRevolution`, above the
whitespace bundle: the definition layer (`wsByte`, `wsX`, `wsLandS`, `wsLeafS`, `wsStopS`),
`scanB_ofNat`, the leaf-class names (`wsLeafS_43/46/48`), the landing cells
(`wsLandS_env/ee/cond`), the continuing visits (`wsContinue43/46/48`), the latch's own facts
(`wsLatchOut_facts`), the dispatch's exit arms (`wsVisit43Exit/46Exit/48Exit`), the exit
visits at `wsStopS` (`wsExit43/46/48`), the run's indices and classes (`wsLatchAt`,
`wsStopAt`, `wsCont`, `wsStop`), the leaf states' two cells
(`wsLeafS_43/46/48_ee`/`_cond`), the run itself (`wsRun_go`, `wsRun`), and now the
composition around it: the seam (`wsSeamSeg`), the first visit at each continuing class
(`wsFirstSeg43/46/48`), the entry dispatch by `%35`'s class (`wsEntry33/35/37`), the stop
state's predecessor per class (`wsStopAt_pre43/46/48`), the uniform tail
(`contWsAfterPre`), the price (`wsPrice`) and the three arm wrappers
(`contWsRun33/35/37`).  Nothing is duplicated here: a piece drafted in this file moves
there once it elaborates, because that module is imported by the default target and this
one is not.

What the composition owes the bundle, and why it is not yet applied there: `HcontFacts` is
a `Type` produced for *every* head state, so a derived `hRun` would have to be built even
at the class whose `%35` does not enter the skip.  The run's derivation needs that class
as a premise (the three arm wrappers take it as a disjunction), and the seam needs the
token record's `%end.i` address — so deleting `sl`, `hRun`, `hnRun` and `hcond_sl` costs at
least one *new* supplied field rather than none.  That is the remaining design question,
recorded rather than decided here.
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
