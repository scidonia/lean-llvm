/-
The no-event assembly: the walk's obligation at the staging, and the call record
the pipeline's slot takes.

`JsonStage2NoEventWalkPremises` states what a dispatch supplies — the seed's
conclusion at `EntryState`, the run to the post-read head, the invariant and its
read facts there, and the loop's step — and derives both conjuncts of `Satisfies`
from it at an arbitrary staging.  This module is the composition the record's
consumers read:

* `stage2NoEventWalkObligation_of_staging` reads the tier's rows at
  `Γ_stage2_noevent`'s precondition and the four staged objects, composes them
  with the seed run and the flush route, and states the obligation at the one
  selection the record names, `gap := stage2GapRecover`;
* `stage2NoEventCallSatisfies_of_staging` hands that obligation, with the four
  objects' staging, to `satisfies_calls_stage2_noevent`, which projects the
  adapter's sixteen-slot argument list back to the twelve-slot record and yields
  the `CallSatisfies` a pipeline slot takes.

**The staging is a hypothesis, not a record field.**  The twelve-argument ABI
cannot name the four objects the flattening appends — the container stack, the
refusal record, the cursor record and the number path's output slot — so
`Γ_stage2_noevent.pre` excludes them and the adapter's `Γ_stage2_noevent_at`
adds `stage2NoEventStagedPre` to its own precondition.  The slot theorem names
both the rows and the staging, and no record in the tree is widened for it.

**What the claim is, and what it is not.**  The rows are the dispatch's data —
the count class's cycle-closing segments and the terminal routes' evidence, with
the acceptance's parse relation and the walk's report — assumed here and not
proved, and the gap helper is the tree's model `stage2GapRecover`, whose body
faithfulness is `docs/contract.md` §7.6's trust row rather than a proof.  Nothing
here makes either unconditional, and nothing here claims the certified walk's
premise tier is discharged.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkPremises

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR

/-! ### The obligation at the staging -/

/-- **The walk's obligation, from the tier's rows at the record's staging.**  The
rows are the dispatch's data at `Γ_stage2_noevent.pre` and the four staged
objects; `stage2NoEventWalkPremises_of_rows` composes them with the seed's run to
`NodeBlock5` and the empty stream's flush route into the premises, and
`stage2NoEventWalkObligation_of_premises` derives both conjuncts of `Satisfies` at
`Γ_stage2_noevent_at`.  The selection is `stage2GapRecover`, the model the
record's own default names. -/
theorem stage2NoEventWalkObligation_of_staging {stk e c d : Nat}
    (hrows : ∀ (a12 : List Value) (mem : Mem) (next : Nat),
      Γ_stage2_noevent.pre a12 mem next →
      stage2NoEventStagedPre a12 mem next stk e c d →
      Stage2NoEventWalkRows (stage2NoEventCalls stage2GapRecover) mem 27) :
    Stage2NoEventWalkObligation stage2GapRecover stk e c d :=
  stage2NoEventWalkObligation_of_premises (stage2NoEventWalkPremises_of_rows hrows)

/-! ### The pipeline's slot -/

/-- **The no-event entry's call record at the pipeline's slot.**  The staging of
the four objects is the hypothesis `Γ_stage2_noevent.pre` does not carry, so the
slot theorem names it beside the rows: `satisfies_calls_stage2_noevent` reads the
obligation at `Γ_stage2_noevent_at` and reports both conjuncts at the
twelve-slot prefix the record is stated on. -/
theorem stage2NoEventCallSatisfies_of_staging {stk e c d : Nat}
    (hrows : ∀ (a12 : List Value) (mem : Mem) (next : Nat),
      Γ_stage2_noevent.pre a12 mem next →
      stage2NoEventStagedPre a12 mem next stk e c d →
      Stage2NoEventWalkRows (stage2NoEventCalls stage2GapRecover) mem 27)
    (hstaged : ∀ {args : List Value} {mem : Mem} {next : Nat},
      Γ_stage2_noevent.pre args mem next →
        stage2NoEventStagedPre args mem next stk e c d) :
    CallSatisfies (envForStage2NoEvent stage2GapRecover stk e c d) Γ_stage2_noevent
      "leanllvm_json_stage2_noevent" :=
  satisfies_calls_stage2_noevent stk e c d
    (stage2NoEventWalkObligation_of_staging hrows) hstaged

/-! ### Axiom footprints -/

#print axioms stage2NoEventWalkObligation_of_staging
#print axioms stage2NoEventCallSatisfies_of_staging

end LeanLLVM.Refinement
