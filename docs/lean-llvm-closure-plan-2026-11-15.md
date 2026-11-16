# lean-llvm: the closure plan

**Date:** 15 November 2026. **Base:** `a95f955`. **Default target:** 1923 jobs, `LAKE_EXIT=0`.

> **Correction (16 November 2026, at `d479b2a`).**  Finish line 1 and Item 4 are wrong as
> written: the obligation cannot lose both bundle arguments.  `hcont`
> (`WalkContinueFacts`) is class data — the head byte's exhaustive switch arm — but each
> arm's evidence carries a tail `WalkSegment` and the scan's traversal hypotheses that are
> per-state supplies, not `WalkInv` consequences, so no `∀ G` producer exists yet.
> `hend` (`WalkLoopEnd`) is worse than unproved: its `mergeWords`/`refuseWords` demand the
> log's arena word at `C.alen`, while `WalkInv.log_alen` gives only `∃ a ≤ C.alen`, and the
> write-back stores the decoder's output length against a reserve of the document extent
> (`JsonStage2WalkArenaWord`).  At an escaping input the slot is short, and
> `WalkMergeWords.not_of_short` / `not_walkLoopEnd_of_short`
> (`JsonStage2WalkPremisesOfStaging`) refute the bundle there, and
> `walkLoopEnd_universal_unsatisfiable` makes the universal bundle unsatisfiable once that
> witness exists.  So `∀ G, WalkLoopEnd G` is not a theorem,
> `stage2WalkObligation_of_staging` is vacuous (its hypothesis cannot be met, so it yields
> nothing about any document), and the claim to quote as closure is
> `stage2WalkObligation_of_premises` (`JsonStage2WalkAssembly`) — the obligation from the
> per-input `WalkPremises` and the record's post rule, with no bundle argument.  The
> reasoning, the refutation lemmas and the per-premise classification are at
> `JsonStage2WalkPremisesOfStaging`'s `WalkLoopEnd` note and its closing section.

## The finish lines, three, in increasing order

1. **Closure:** `stage2WalkObligation_of_premises` — the obligation from the per-input
   `WalkPremises` and the record's post rule, with no bundle argument.  *(Originally:
   "`stage2WalkObligation_of_staging` takes no bundle arguments — every premise is a
   theorem from the ABI preconditions."  That form is vacuous rather than unproved:
   `hend` is refuted at an escaping input, so its hypothesis cannot be met.  See the
   correction above; the original phrasing is replaced, not annotated.)*
2. **The review's milestone** (`lean-llvm-progress-handoff-4ca52e7`): the domain, the
   pinned implementation, the watermark inhabited, the bundles produced, returning
   execution, an output relation, refusal and frame guarantees, the build and a real
   caller.
3. **Phase E:** native helper bodies, parser correspondence, artifact binding —
   correspondence with artifacts outside the tree, recorded as an assumption set, not
   proved here.

Nothing below inflates the first into the second, and the second does not include the
third. When this document says "closed" it means the first.


## Session state at `5456e63` (read this first after a context break)

**Green:** default target 1981 jobs, `LAKE_EXIT=0`, no `sorryAx`, no `bv_decide`.
Everything below is committed and pushed; `HEAD` = `origin/main`.

**The dispatch census is exhaustive in the proved sense.**  `LastEntryArm` 14
constructors, `HcontArm` 15, and **neither has a `supplied` constructor**: every class of
the byte alphabet has a counted segment, a price, a staged document that dispatches through
the real arm, and a control.  The provenance: scalar and high-byte were already proved;
this session added string opener, closing-at-zero, comma and colon at zero, container
openers, comma and colon above zero, close-with-open, letters, `f`, class C, and the run at
both levels.  Two classes turned out never to have been owed at all (the high-byte route,
already carried by `ws`/`cleanup`) — stale prose, not a gap.

**The obligation still takes two bundles, and they are not yet theorems.**
`stage2WalkObligation_of_staging` takes `hcont : WalkContinueFacts` and
`hend : WalkLoopEnd`.  Phase D was expected to derive them by composition; it found they
cannot be derived at this layer, with the measurement recorded in
`JsonStage2WalkTerminalPrice`'s docstring §2: of the twenty-nine arm members, **two** have
bundle producers (`.ws`, `.highByte`).  The class bits, segments and registers demote
generically, but the remaining rows need per-document data the invariant does not fix — the
next lane's word, the byte before the entry's end, the root and log words' values, the depth
split — plus the callee preconditions at each tail's argument list and the traversal's
round/guard/byte facts.

**So the remaining work is a producer tier, not a composition**, and the enumeration classifies
each residual row **D** (a function of the class byte, `WalkInv`'s registers and the geometry —
with the definition to unfold) or **F** (genuinely free document/state data).  The conclusion it
supports: not one general class-demotion lemma per level — the F rows need per-class producers,
and the callee/traversal rows need the tier first.

**Three boundary facts, stated rather than proved, each with its witness:**
`WalkLoopEnd`'s log arena word is *false* at an escaping input (`JsonStage2WalkArenaWord`; a
reported-cursor decision, not a proof); `RunLastFacts.hbudget` is the terminal run's entry-only
price, and `JsonStage2WalkTerminalPrice` exhibits computed documents outside it and inside the
credit the potential pays; and the event-count clause is block-keyed (`walkEmitC`) because the
append re-establishes it at an unchanged index.

**The two process rules that made these rounds safe:** one compilation at a time under
`probes/install/lake-locked.sh` plus a `pgrep` check, and no two workers whose cones share a
module — `PremisesOfStaging` imports every bundle, so that is most pairs.  Use `edit`, and
`edit` with `replace_all: true` for bulk renames: five rounds reached for `sed`/`python3` on
exactly those and each recorded it as a deviation.

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

**Statement (corrected 16 November 2026).**  `stage2WalkObligation_of_premises` takes
`WalkPremises` and the record's post rule.  The original statement —
"`stage2WalkObligation_of_staging` takes `hcont`, `hend`, `hres`; after items 1–3, each is
produced" — is replaced: `hres` is gone (it is `HcontArm.twoEntry`'s field), and the other
two are not both producible.  `hend : ∀ G, WalkLoopEnd G` is *refutable* at an escaping
input (`WalkMergeWords.not_of_short`, `not_walkLoopEnd_of_short`,
`walkLoopEnd_universal_unsatisfiable`), so `stage2WalkObligation_of_staging` is vacuous and
its premise list cannot become "the record's own pre and staging, nothing else".

**Work.**  Produce `WalkPremises` from the record's own pre and staging.  The flush arm
already has a producer (`walkFlushAt_of_staging`); the seed and invariant conjuncts are
theorems; the loop step is where the per-state producers land.  `hcont` remains a producer
tier (its arm evidence carries a tail `WalkSegment` and the scan's traversal hypotheses);
`hend`'s word field is dropped or restated at `log_alen`'s witness rather than produced.
`walkPremises_of_staging` stays as the conditional transport and inherits the vacuity.

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
at the caller-to-return theorem.  **Corrected reading (16 November 2026):** the top level's
shape is `hcont, hend`; `hres` is an arm field; `hcont` is class data whose per-state
producers still take the tail and traversal premises; `hend` is *false* at an escaping
input (its log word), not merely unproved.  The one false premise was the watermark, which
was retired; the log word is the second, and it is the reason the closure claim is
`stage2WalkObligation_of_premises`.
