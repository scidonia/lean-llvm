/-
The walk's last entry: the two outcomes `WalkDispatchThree`'s `hlast` names.

## The premise both ends read

`hlast`'s hypothesis and the head prefix's premise are the **same fact** — the last
entry's `%inc ≥ %nep`, which `walkHeadChainToScan` takes as `hge` and `hlast` takes as
`¬ (C.k + 1 < G.nep)`.  That is why the composition is not four applications over
unrelated lemmas: it is **one premise, read at both ends**.  The last entry cannot
continue because its increments have reached the entry count, and the prefix cannot run
down the continuing arm for the same reason.

## The inventory

| piece | lemma | span |
|---|---|---|
| prefix | `walkHeadChainToScan` | `NodeBlock21 → while.body462.i` |
| scan → merge | `walkScanToMerge` | `while.body462.i → cleanup478.i` |
| merge step | `walkFinishMerge_at` | `cleanup478.i → if.then485.i` |
| path 3 | `walkFinishPath3` | `→ if.then` |
| continuation | `walkFinishRun` | `→ if.end` |
| flush | `WalkFlushAt.ofRun` | the refusal copy's four named steps |

The prefix is a `WalkChain` because its links are existential; the rest are segments,
and `WalkSegment.of_chain` is the direction between them — which is why the two live
in different shapes.

## Why this module exists

A composition's home is above every module its pieces live in, so this one imports the
three that hold the prefix, the scan and the finish paths.  It states no mathematics of
its own: what it will hold is the pair of segments `hlast` asks for, and the arithmetic
between them.

-/

import LeanLLVM.Refinement.JsonStage2WalkHeadChainScan
import LeanLLVM.Refinement.JsonStage2WalkFinishPath
import LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessFinish

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

end WalkScope

end LeanLLVM.Refinement
