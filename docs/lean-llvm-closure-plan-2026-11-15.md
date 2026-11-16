# lean-llvm: the closure plan

**Date:** 15 November 2026. **Base:** `a95f955`. **Default target:** 1923 jobs, `LAKE_EXIT=0`.

## The finish lines, three, in increasing order

1. **Closure:** `stage2WalkObligation_of_staging` takes no bundle arguments — every
   premise is a theorem from the ABI preconditions.
2. **The review's milestone** (`lean-llvm-progress-handoff-4ca52e7`): the domain, the
   pinned implementation, the watermark inhabited, the bundles produced, returning
   execution, an output relation, refusal and frame guarantees, the build and a real
   caller.
3. **Phase E:** native helper bodies, parser correspondence, artifact binding —
   correspondence with artifacts outside the tree, recorded as an assumption set, not
   proved here.

Nothing below inflates the first into the second, and the second does not include the
third. When this document says "closed" it means the first.

## The order, with each item's statement and its acceptance

### Item 0 — the pipeline watermark (P0)

**Statement.** `Stage2Watermark` (`PipelineDischarge:1399`) quantifies `∀ S`
independently of the exit witness; at `S.ndst = e.next` the premise demands
`e.next + 8 ≤ e.next`.  It is incompatible with an inhabited exit predicate.

**Repair.** Index the exit predicate by its carried state and state the watermark for
that same state; or carry the allocator bound in the invariant and return it with the
exit witness.  The two are equivalent in reachability; the first is local to the exit,
the second is global but carries the bound to the report.

**Files:** `PipelineDischarge.lean`, `JsonPipelineRefine.lean`, and the stage-2
report/contract if the region list moves.

**Acceptance:** a regression proving the retired watermark plus an admitted exit implies
`False`; the replacement stated at the carried witness; the allocator bound derived from
staging and preserved by the steps; an instantiated case; `Stage2SlotKeeps` audited in
the same change.  Verification: `lake-locked.sh build`, `LAKE_EXIT=0`, no `sorryAx`,
and the two `False` and boundary statements' `#print axioms` printed.

**Size:** 1–3 rounds.

**Landed** on top of `7bb5c76` (working tree; default target 1923 jobs, `LAKE_EXIT=0`).
`retiredStage2Watermark` + `retiredStage2Watermark_false` state and refute the retired
form; `stage2Watermark` states the bound at the exit's own record through
`stage2ExitRegions_le_caps`; the bound is the invariant's `stage2StagedCaps` conjunct,
seeded from `pipelineStagedBelow` (`seedCarried_caps`) and carried by `pipelineCalls_next`
and `stage2StagedCaps_mono`; `Stage2SlotKeeps` is indexed by `pipelineLoopExitAt`; and
`pipelineTailTarget`, `pipelineBodyFacts_of_exitStage2` and
`pipeline_satisfies_at_stage2_of_exitStage2` take no watermark.  The instantiated case is
the tail's own: `pipelineTailTarget` reads the bound at a real exit and transports it to
the stage-2 call.

### Item 1 — the continuing arm's `ws` bundle

**Statement.** `HcontFacts` at 59 fields after the 59-field landing; the `ws` arm still
supplies the document facts (the per-index class `∀`, the document bytes), the tail
segment, `htok` and the traversal premises.

**Work.** `htok` needs the skip's register-preservation lemma — the run (`wsRun`) is
proved, so this is now a derivation, not a search.  The document facts are `WalkGeom`
consequences where the byte is read and a staging-separation clause otherwise.
`hcontFacts_of_staging`'s argument list shrinks by each derivation; a derived argument
is deleted, not kept beside its proof.

**Files:** `JsonStage2WalkHcontFactsOfStaging.lean`, `JsonStage2WalkRevolution.lean`.

**Acceptance:** the producer's supplied-argument count before and after, measured; each
survivor's producer named at the field; `walkMergeCells_ws`'s footprint unchanged.

**Size:** 1–2 rounds.

### Item 2 — the last-entry bundle's remaining rows

**Statement.** `HlastFacts` is 10 of 14 rows produced; the producer's supplied arguments
are 35.

**Work.** The four carriers landed by the running worker (`%4`, `%t352.i`, `%e`,
`%idxprom.i` as an `inc_reg`-class clause) retire about seven arguments: `h4L`,
`htokS`, `heL`, `hidxS`, then `hv63`, `hugt`, `hread35`/`b35`, `heM`/`h4M`.  What then
remains is named per row: the log's base word (a `WalkInv` clause at `%z + 0`), the
strict event count (`if.then425.i`'s one-record-per-entry count), the event width
(`WalkGeom.evLt`), and the contracts at their own memories.  Plus the loop-head
predicate that `WalkLoopEnd.facts` needs: the head's guard `C.k < G.nep`, which
`WalkInv.k_le` gives only as `≤`.

**Files:** the carrier worker's files, then `JsonStage2WalkDispatchWitnessHlast.lean`
and `JsonStage2WalkExitProducer.lean`.

**Acceptance:** rows before/after; supplied arguments before/after (baseline 35);
`hlastFacts_of_staging`'s footprint; whether `WalkLoopEnd.facts` now calls it.

**Size:** 1–2 rounds.

### Item 3 — the string residue

**Statement.** `HstringResidue` is 14 fields after the composition's closure, of which
five are input facts: `G.dst < 2^64`, `G.ev < 2^64`, `C.evlen < 2^63`,
`C.events.length < C.k` (strict), and `l ≤ ext`.

**Work.** The five move into `stage2Pre`/the staging hypotheses as input consequences —
a contract edit, the same shape as the frame's restatement, touching `Contract` and the
bundle module.  The other eight follow from the callee's contract at the call's own
memory, which the transport (`s2StringBodyPre_of_reads`) already reaches.

**Files:** `JsonStage2Contract.lean`, `JsonStage2WalkDispatchWitnessString.lean`,
`JsonStage2StringStageFacts.lean`.

**Acceptance:** `HstringResidue`'s count before/after; the five moved facts stated in
`stage2Pre`'s docstring as what they are; the rest proved at the call's memory.

**Size:** 1 round.

### Item 4 — phase D

**Statement.** `stage2WalkObligation_of_staging` takes `hcont`, `hend`, `hres`.  After
items 1–3, each is produced.

**Work.** `walkPremises_of_staging` derives the bundles from the staging: the flush arm
already has one, and the loop arm's three outcomes are proved.  The top level's premise
list becomes the record's own pre and staging, nothing else.

**Files:** `JsonStage2WalkPremisesOfStaging.lean`, `JsonStage2WalkFlushPost.lean`.

**Acceptance:** the obligation's argument list verbatim; `LAKE_EXIT=0`; its footprint.

**Size:** 1 round.

**The composition's shape (decided here so the round is not guessed at):** the three
bundles are produced from the staging at one call — `walkStage_at_pre_fields` supplies
the staging at the record's numbers, the flush arm is `stage2Post_of_staging_flush`, and
the loop arm's three outcomes are `WalkDispatchResult.toOutcome` at the result each
bundle produces.  The obligation's own `by_cases G.nep = 0` selects between them.  No
new premise may be introduced; a fact that is neither a staging fact nor an invariant
consequence is a finding, not a parameter.

### Item 5 — the caller-to-return theorem (the review's milestone)

**Statement.** One theorem for a precisely stated domain: returning execution within the
budget, the output's relation to the reference, refusal behaviour, frame guarantees —
from the repaired watermark and the discharged obligation.

**Work.** The reference-parser correspondence (`Sigma_pipeline`/`EventStreamRel`) is the
semantic half the review names and no file today touches; it is the next piece, and it
is stated as its own item, not absorbed here.

**Size:** its own session.

## Discipline (measured, not aspirational)

- **One compiler at a time**, enforced by `probes/install/lake-locked.sh` plus
  `pgrep -af 'bin/lean|lake build'` before any compilation — the lock refuses a
  contender, and the check covers `lake env lean`, which the lock does not.  A `/tmp`
  `mkdir` token does not survive a forked shell and must not be relied on.
- **No two workers whose cones share a module.**  Every parallel pair in this layer has
  collided on the dependency cone — `Hlast` below `Revolution`, `Revolution` below the
  string bundle, `PremisesOfStaging` importing all three.  The one split that paid was a
  module nothing else reads (`JsonStage2StringStageFacts`).
- **Commit each landing** with explicit paths, never `-a`/`.`, identity read back with
  `git log -1 --format='%an <%ae> | %cn <%ce>'` before it is reported; push immediately.
- **A supplied field with no named producer is a finding**, not a premise: the session's
  eight implicit-premise defects (the static frame, the `∀` over unreachable states, the
  two contradictory bundles, the producer's totality, the silently-pinned byte, the
  missing `%end.i` cell, the native certificate) were each found by a producer or a
  reviewer, never by an audit.
- **A build piped to `tail` reports `tail`'s status.**  Capture the status at the
  command (`{ …; echo "LAKE_EXIT=$?"; } > log 2>&1`) and read the log.
- **An axiom pin that passes only because the declaration above it failed is a fiction.**
  `sorryAx` in a pin's output is a red flag on the declaration, not on the pin.

## What this plan deliberately excludes

The native route, the compiler/backend/linker assumptions, and the platform are stated
in `docs/contract.md`'s trust ledger; they are not provable in this tree and are not
part of "closed".  The milestone's output relation to the reference parser is the next
session's work, not this plan's.

## The measure of progress

Not field counts or build success alone: the set of externally supplied execution and
semantic assumptions remaining at `stage2WalkObligation_of_staging`, and after item 4,
at the caller-to-return theorem.  Today's reading: three bundles, all true, all with
named producers; the top level's shape is `hcont, hend, hres`; the watermark is the one
false premise.
