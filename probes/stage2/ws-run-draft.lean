/-
# The whitespace skip's run: where the draft's content went

Not imported by any target and not built by `lake build` — it elaborates against the
committed tree, and it is where the run's remaining pieces are drafted.

Everything this file used to hold is landed in `JsonStage2WalkRevolution`, above the
whitespace bundle: the definition layer (`wsByte`, `wsX`, `wsLandS`, `wsLeafS`, `wsStopS`),
`scanB_ofNat`, the leaf-class names (`wsLeafS_43/46/48`), the landing cells
(`wsLandS_env/ee/cond`), the continuing visits (`wsContinue43/46/48`), the latch's own facts
(`wsLatchOut_facts`), the dispatch's exit arms (`wsVisit43Exit/46Exit/48Exit`) and the exit
visits at `wsStopS` (`wsExit43/46/48`).  Nothing is duplicated here: a piece drafted in this
file moves there once it elaborates, because that module is imported by the default target
and this one is not.

What is still missing is the run itself — `wsLatchAt`/`wsStopAt` and the induction on
`k - i` — and that is what this file is for.
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
