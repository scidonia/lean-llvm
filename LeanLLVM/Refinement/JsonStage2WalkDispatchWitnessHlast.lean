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


## `hlast` as stated is not provable

`ofContinueAndLast`'s second hypothesis

```lean
∀ C s, WalkInv G C s → C.block = walkLoopHead → ¬ (C.k + 1 < G.nep) → (∃ …) ∨ (∃ …)
```

is a statement about **the last entry**, and the segments it asks for are statements
about **the input**.  The prefix `walkHeadChainToScan` reads `%8`'s byte, four class
bits on it, `%inc` and `%nep`'s values, and the twelve facts the entry established —
and **none of them is invariant-carried**, so no proof of the stated hypothesis exists.
`¬ (C.k + 1 < G.nep)` supplies exactly one of them: the prefix's `hge`, that the
increments have reached the entry count.  **That is why the premise looked sufficient:
it is the one field of the input's bundle that a hypothesis about the entry can imply.**

## The repair, in order

1. **a bundle**, on the module's own precedent (`s2StringBodyDecodedFacts`,
   `s2StringBodyRefusedFacts`): one `structure` whose fields are the prefix's premises,
   grouped by what they are about —
   * **the head's byte** — `h8`, and its four class bits `hlt91`, `hlt123`, `hlt125`,
     `hne125`;
   * **the entry counts** — `hinc`, `hnep`, and `hge : inc ≥ nep`;
   * **the default arm's cells** — `hpre5`, `hav5`, `hidx5`, `htok5`, `hgap5`, `hugt`;
   * **the seam's cells** — `hpre6`, `hin6`, `hv6`, `hend6`, `h8end`, `hbit6`;
   * **the second byte's class** — `h8c`, `hc110`, `hc116`, `hceq116`;
   * **the tail's own** — the three outcomes, the event, the seed's `cA`/`rdv`/`xA`/`ei`/`cd`,
     and `hTail`, the `WalkChain` from `TailStartC`'s state;
2. **`hlast_finish` and `hlast_refuse` take the bundle**, and are `of_chain`, `trans`,
   `omega` over it — `Cd.block = "cleanup478.i"` and `Cd.block = "if.then"` respectively,
   with `Cd.eoff ≤ G.n` for the refusal;
3. **`hlast` takes the same bundle**, so its statement reads
   `∀ C s, WalkInv G C s → C.block = walkLoopHead → ¬ (C.k + 1 < G.nep) → Facts C s → (∃ …) ∨ (∃ …)`;
4. **`ofContinueAndLast`'s second hypothesis gains the bundle** — mechanical, because it
   only passes `hlast` through, and its `hcont` sibling is untouched.

The two segments' goal texts, verbatim:

```lean
-- finish
∃ (Cd : WalkCarry G) (sd : State) (p k2 : Nat) (prev : String) (kOp : Operand) (nepv : BitVec 64),
  WalkSegment calls G C s Cd sd p ∧ Cd.block = "cleanup478.i" ∧ sd.pre = some prev ∧
  phiIncoming prev cleanupKIncoming = some kOp ∧ evalOperand sd kOp = some (.int 64 (k2)) ∧
  lookupName sd.env "%nep" = some (.int 64 nepv) ∧ k2 = nepv.toNat ∧
  p + 2 ≤ stage2EntryAllowance * (k2 - C.k) + stage2ByteAllowance * (entryPos G k2 - entryPos G C.k)

-- refuse
∃ (Cd : WalkCarry G) (sd : State) (p : Nat),
  WalkSegment calls G C s Cd sd p ∧ Cd.block = "if.then" ∧ Cd.eoff ≤ G.n ∧
  p + 2 ≤ stage2EntryAllowance * (G.nep - C.k) + stage2ByteAllowance * (G.n - entryPos G C.k)
```

The completion of the finish segment — `sd`'s `%nep`, the merge's `prev` and `k2` — is
`walkFinishMerge_at`'s seven `phi` premises at the state `walkScanToMerge` names, and
the refusal's `eoff` is the flush arm's own.

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
