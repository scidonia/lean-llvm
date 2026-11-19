# Handoff: the walk's remaining gaps

**Tree at `ee7544f`.**  The gate this document sits on is the **local default target** at
`ee7544f`: green at **2,208 jobs**.  That number is the default target's, not the
`LeanLLVM` umbrella's: `ee7544f`'s own commit message records **1,106 jobs** for the
library build it ran, and the two are not interchangeable.  Each commit in the run records
its own build, and a green is not inherited across commits: `7209fc8` 1,107, `a84c287`
1,108, `282ac25` 1,108, `ef459b4` 1,109, `253b785` 1,110, `7167cca` 1,110 and `ee7544f`
1,106.  The commits that print axiom pins record the pins this document quotes
(`[propext, Classical.choice, Quot.sound]` or below); `ee7544f`'s message records its job
count and no pin, so no pin claim is attached to that build from its message.

This documentation pass ran no build of its own.  Every anchor below was read from the
`ee7544f` blob with `git show ee7544f:`, except the ones the sentence explicitly states at
`ef459b4`.  Where a declaration is named at a commit where it lived and `ee7544f` has
since deleted or moved it, the commit is named in the sentence and the anchor is stated at
that commit.  That applies in particular to the deleted whitespace modules:
`JsonStage2WalkDispatchWsRows`, `…WsRowsProduce` and `…WsRouteAudit` exist through
`7167cca` and are deleted at `ee7544f`, so their refutation anchors are read from
`ef459b4`.

The guard narrowing `816cf737` (the `.ws` run field's two head-byte bits) predates this
tree and is recorded in the whitespace section as part of the deleted group's history.  The
earlier 1,102-job umbrella build at `e268d1c` and the three module-target builds
(`…DispatchWsRowsProduce` 671 jobs, `…DispatchDefaultLane` 668, `…DispatchAbiOfInv` 666)
are history: they measured an older tree and are not evidence about `ee7544f`.

**Verify before trusting any claim below** — this session's own record is that
*every* statement-level defect was found by something trying to *use* or *supply* a
claim, never by an audit.  Capture the status where the command runs: a build piped to
`tail` reports `tail`'s exit code.

```bash
systemd-run --user --scope -p MemoryMax=12G -p MemorySwapMax=4G --quiet \
  nix develop -c bash probes/install/lake-locked.sh build
```

The ceiling is `AGENTS.md`'s: a module's elaboration has been measured above 6 GB, so the
build runs under 12 GB rather than the 6 GB this file used to show.  A build killed by the
ceiling is a signal that the module needs splitting or its `maxHeartbeats` raising, not a
reason to run the same command without it.

A full build is minutes warm.  **The two modules that used to dominate a rebuild are now
import front-ends.**  `JsonStage2WalkScope` is 20 KB over eleven modules: `WalkInv` is in
`JsonStage2WalkScopeRecord` (`next_ge`, `frame`), `walkStaticRegs`/`walkStaticNames` in
`JsonStage2WalkScopeGeom` (`:922`/`:902`), and `JsonStage2WalkScopeClassAB` is the largest
at 81 KB.  `JsonStage2StringBody` is a 100-line front-end over seven, with
`s2StringBodyBody_contract` in `JsonStage2StringBodyDecoded:376` and
`JsonStage2StringBodyArms` the largest at 73 KB.  Batch edits within one module as before;
the old "21 MB" and "7k lines / 12M heartbeats" figures describe the pre-split tree.

---

## What is proved

| Layer | Theorem |
|---|---|
**the walk, loop head → scan latch** | `walkHeadChainToScan` (`JsonStage2WalkHeadChainScan`) |
**the scan** | `walkScanArrival457_of_cell` (latch → last visit), `scanExitSeg`, `walkScanToMerge` (→ `cleanup478.i`) |
**the finish paths** | `walkFinishPath1`/`2`/`3`, `walkFinishRun`, and `walkFinish_not_frame_of` (why none is a `WalkSegment` at `if.end`) |
**the last entry** | `hlast_toMerge`, `hlast_finish`, `hlast_refuse` (`JsonStage2WalkDispatchWitnessHlast:367`/`:406`/`:437`); the last entry's arm is produced from the three last-level groups by `walkLoopEnd_of_payload` (`JsonStage2WalkPremisesOfStaging:484`), and those groups are the remaining last-level supply (see the frontier below); the last payload's own fields are produced in part (`hlastAbi_openCall` `JsonStage2WalkDispatchHlastSupply:219`, `hlastLane_of_not_wsStop` `:155`), its high-byte group carries the refusal evidence `HlastHighByteRefusal` (`hlastHighByteRefusal_of_stage` `:429`), and the emission residue **is** empty on that class (`hlastResidue_empty` `:460`); `hlastPrefixSeg` (`JsonStage2WalkPrefixCount:1049`) is 19 links (`hlast_toMerge` 20), so the price is `20 + 2 ≤ 32·1 + 8·0`.  **The slow scan is closed as a theorem (`7209fc8`):** `slowVisit_at` (`JsonStage2WalkDispatchSlowVisits:608`) is the stop visit's priced segment to `if.then`, `slowRun`/`slowRun_go` (`JsonStage2WalkDispatchSlowRound:864`/`:631`) prove the loop at `∃ n, n ≤ 5 * (G.n − entryPos G C.k) + 10`, and `slowAnswerOnePrice` (`:923`) prices that run inside `32·(G.nep − C.k) + 8·(G.n − entryPos G C.k)`.  `hlastAnswerOneRefuseRoute` (`JsonStage2WalkDispatchLastSeamRoute:224`) composes a prefix segment to `land.rhs.i103` with that run into `HlastRefuseRoute`, so `HlastSeam.answerOneRefuse` has its inhabitant (`hlastSeamAnswerOne_nonempty`, `:267`) with the arm's statement unchanged; the prefix from the head to the scan's landing is still supply.  The last rows' refusing leaves carry the same shape (`7167cca`): `HlastLettersRows` and `HlastClassCRows` hold `HlastSeamRefusal` plus a `HlastRefuseRoute`, and their arm is `LastEntryArm.refuse` |
**the continuing seam at a kind-`0` byte** | `HcontClassRows.refuseSeg` (`JsonStage2WalkDispatchClassRows:776`) — the refusal route as a segment with the slow scan's stop named — feeds the arm `HcontArm.badToken` (`JsonStage2WalkDispatchHcontArms:749`) and its `WalkDispatchResult.refuse`; `hcontArm_badToken_of_row` (`ClassRows:797`) builds that arm from `HcontClassRows` plus the head state's byte facts (tag bit clear, byte outside the three literal pivots), and the answer `0` and record come from `HcontSeamAbi.scanRefuse` — nothing supplies an answer.  The six tag-clear default classes and the high-byte `126`/`127` class take it (`JsonStage2WalkDispatchContinuing:23-25`), and the rows `HcontClassRows.seamScan` and `RunRow`'s three cast-leaf wrappers are **deleted** — the five purely kind-`0` `.run` arms no longer have a group of their own (`253b785` also deletes their five orphaned head-chain producers).  Seams there are unmixable: `hcontSeamCalls_no_kind_zero` (`JsonStage2WalkDispatchSeamCalls:765`) and `hcontSeamCalls_no_literal_zero` (`:791`) refute the emit group outright.  The four class-row fields at that literal — `cleanupRow`, `letters`, `c56Else`, `c58Else` — are stated as `HcontSeamRefusal` (`JsonStage2WalkDispatchSeams:373`) at the same carry, state and literal, not the emit row `HcontSeamRow` (`ClassRows:182`); as emit rows they were refuted by `HcontSeamRow.not_nonempty_zero` (`JsonStage2WalkDispatchClassRowsProduce:223`), and their consumers build `HcontArm.badToken` via `hcontArm_badToken_of_row`/`refuseSeg` (`282ac25`) |
**the last level's seam** | `HlastSeam` (`JsonStage2WalkDispatchSeams:406`) is the answer's **sum**: `answerZero` (`JsonStage2WalkDispatchSeams:410`, `HlastSeamZero` `JsonStage2WalkDispatchSeamRow:95`), `answerOneRefuse` (`JsonStage2WalkDispatchSeams:414`, `HlastSeamRefusal` `SeamRow:40`), `answerOneEmit` (`JsonStage2WalkDispatchSeams:416`, the emit group).  Producers: `hlastSeamZero_of_calls` (`JsonStage2WalkDispatchHlastSupply:407`), `hlastSeamRefusal_of_stage` (`:391`) and `HcontSeamAbi.last` (`JsonStage2WalkDispatchSeamCalls:733`); `hlastSeam_nonempty` (`HlastSupply:398`) keeps the sum inhabited, and the `answerOneRefuse` arm has its priced route to the copy (`hlastAnswerOneRefuseRoute`, `JsonStage2WalkDispatchLastSeamRoute:224`, `7209fc8`).  The two refusing last-row classes carry that route and the refusal rows themselves (`7167cca`; see the last-rows paragraph below).  The duplicate `scanEntry_envTok` is gone: `lastArmScanEntry_envTok` (`JsonStage2WalkDispatchLastArmRows:161`) is the one environment row, shared by the five long links |
**the string opener's other depth-zero arm** | `HcontArm.stringOpenZeroRefuse` (`JsonStage2WalkDispatchHcontArms`) — the same byte and state as `.twoEntry` but a nonzero root word: the value-position call answers `0`, `if.end245.i`'s `%or.cond523.i` is clear and the walk takes `if.then249.i` to the copy; `hcontStringOpenZeroRefuseRoute` composes the byte-`34` head chain, the call and the refusal store as one `WalkRefuseAt` (`refusePrice_of_le`), and `hcontArm_stringOpenZeroRefuse_of_staging` (`JsonStage2WalkDispatchContinuing`) is the arm's producer.  `walkContinueArm_of_payload`'s string branch now splits on the lane's root word, so the depth-zero class has both arms |
**the continue case** | `walkRevolutionMergeSeg`/`walkRevolutionMergeSegWs` (`JsonStage2WalkRevolutionSeg:618`/`:788`) — the scan-free and whitespace arms' priced segments to `cleanup478.i`, with the merge's three cells at the endpoint.  `walkRevolutionMergeSegWs` still serves the run class's scan (`HcontRunRow`/`.run`), not the deleted `.ws` arm.  `walkRevolution_seg` is retired rather than kept: its premise named the scan-free bundle at a state whose path is the run's |
**the dispatch, at its outcomes** | `WalkDispatchResult` + `WalkDispatchThree.ofResult` + `walkLoopStepThree_of_dispatchResult` |
**the flush arm** | `walkFlushAt_of_staging` (the run), `stage2Boundary_of_flush` (the six facts), `stage2Post_of_staging_flush` (the `nep = 0` post) |
**the emitted string body** | `s2StringBodyBody_contract` (`JsonStage2StringBodyDecoded:376`), axiom pin passing — and its precondition no longer asks the caller for the body's own slot (Gap 2) |
**the two-entry token** | `HstringFacts` + `stringPath_seg` + `WalkDispatchResult.ofStringMerge` (`JsonStage2WalkDispatchWitnessString`), the arm at `C.k + 2`; `HcontCase` is the class the continuing premise now names. The fifteen-link segment is proved, and `HstringResidue` (`JsonStage2WalkDispatchWitnessString:1949`) is a field-less `Prop`: `WalkStringResidue` is not a premise — see Gap 1 |
**the continuing payload's rows** | `HcontLane.defaultLane`'s row (`hcontDefaultRow_of_inv`, `JsonStage2WalkDispatchDefaultLane:124`; the field at `hcontLane_defaultLane`, `:161`), `HcontAbi.openCall` (`hcontAbi_openCall`, `JsonStage2WalkDispatchAbiOfInv:56`), and `HcontTrav.visits`' reduction (`hcontTrav_visits_of_class`, `:266`).  `HcontAbi.string` is repaired: lane-anchored, guarded by the accepting arm's `L.rd.toNat = 0`, with `hcontStringCalls_of_lane` (`JsonStage2WalkDispatchAbiOfInv:135`) as the row's composition; the old universal's refutation is `hcontStringCalls_uninhabited_of_ne` (`:100`).  `trav.visits` is now stated as document supply: `ScanVisitsDoc` (`JsonStage2WalkDispatchTravOfStaging:59`) says every index in a token's interior reads a `9` or `10`, `scanVisitsDoc_bits` (`:64`) bridges those bytes to the latch's comparisons, and `hcontTravVisits_of_doc` (`:80`) turns the row into the field (`f46dfa4`).  `WalkGeom` fixes no interior byte, so no variable-geometry producer can supply it |
**the whitespace skip's run** | `wsRun` (`JsonStage2WalkRevolution:1646`) with `wsRun_go` (`:1541`) and `contWsRunF` (`:3869`) — the run, its stop and its price derived, and `HcontFacts` carries no run field |
**the whitespace class is the refusal's** | The `126`/`127` class reaches `if.then413.i` through `if.else405.i`, whose kind literal is `0`, so the scalar call answers `0` and the walk refuses; the `.defaultValueHigh × .wsByte` cell builds `hcontArm_cleanup_of_class` (`JsonStage2WalkDispatchClassCase:284`, through `hcontArm_badToken_of_row`/`refuseSeg`), exactly as the three scan-free branches beside it.  `ee7544f` **deletes** `HcontWsRows`, `HcontWsTail`, `HcontFacts`' former producer `hcontFacts_of_rows`, `hcontArm_ws_of_rows`, `HcontWsSeam`/`hcontWsSeam_of_body`/`hcontScanTail_of_seam`, and the three modules `JsonStage2WalkDispatchWsRows`, `…WsRowsProduce` and `…WsRouteAudit`.  `HcontFacts`, its producer `hcontFacts_of_staging`, and the constructor `HcontArm.ws` remain in the tree and remain live — `hcontFacts_of_staging` still produces `HcontFacts` at one state, and `HcontArm.ws` is still a constructor of the continuing arm's inductive — but the continuing case never builds them; `wsRun`/`contWsRunF` stay and serve the run class's `.run` cell |
**the loop's exit, at its memories** | `JsonStage2WalkTargetPost`: the 25 conjuncts of `stage2Boundary` at the returned memory for all three terminal routes — `walkFinishPost_accept` (`:985`), `walkFinishPost_refuse` (`:1255`), `walkFinishPost_refuse488` (`:1446`), `walkFinishPost_copy` (`:1605`), composed by `walkFinishPost_merge` (`:1723`) and `walkFinishPost_refuseOfWords` (`:1765`) — and `WalkTargetPost` (`JsonStage2WalkTraverse:670`), the terminal predicate the loop's step carries |
**the top level** | `stage2WalkObligation_of_staging` (`JsonStage2WalkFlushPost:934`) — exactly five payload groups (`hcont`, `hrows`, `hlast`, `hlastRows`, `hlastArms`, `:935-939`) and **no `hpost`**; the loop arm's post is `stage2Post_of_staging_loop` (`JsonStage2WalkPremisesOfStaging:1154`) |
**the credit** | `walkPotential` reads through `boundary`: `32·(nep − k) + 8·(n − boundary k)` |

**Also worth knowing**: `JsonStage2WalkArenaWord` records why `WalkExit`'s arena
premise was *inert* and why it was deleted; `JsonStage2WalkCredit` states the terminal
price and why `entryPos` cannot serve as a price index.

---

## What is closed — Gaps 1–3

### Gap 1 — the two-entry token's bundle — **closed: the fifteen-link segment is a theorem**

`HstringFacts` and `WalkDispatchResult.ofStringMerge`
(`JsonStage2WalkDispatchWitnessString`) name the standalone string and give it an arm,
and `WalkContinueFacts` (`JsonStage2WalkPremisesOfStaging`) is a *class*:
`HcontCase.ws` (`HcontFacts`) or `HcontCase.twoEntry` (`HstringFacts`).  A standalone
string consumes **opener and closer**, and its merge index is `C.k + 2` via `%inc208.i`
(`WalkLink.if_end207_i`, `JsonStage2WalkStore:1778`).  So at `C.k = 0`, `G.nep = 2` —
where the head's test `0 + 1 < 2` sends the walk into the continuing branch — the branch
is `HcontCase.twoEntry`, supplied by `hcontArm_twoEntry_of_staging`
(`JsonStage2WalkDispatchStringOfStaging:176`) and consumed by
`WalkDispatchResult.ofStringMerge`.

**What landed.**  `stringPath_seg` is a *proof*: one `WalkSegment … 15` from the head to
`cleanup478.i`, with the endpoint's block, index and predecessor, the invariant there,
and the endpoint's two register cells (`%inc208.i = C.k + 2`, `%nep = G.nep`).  The
bundle carries **no segment field**: `Cd`, `sd`, `seg`, `hsegBlock`, `hsegK`, `hsegPre`
are gone, and `ofStringMerge` reads the segment and its endpoint from
`stringPath_seg`'s conclusion.  The arm's footprint is `[propext, Classical.choice,
Quot.sound]`, as is the segment's (`#print axioms` pins at the module's end).

The path is composed in four theorems, one per group of links, each ending at a `def`'d
state and a named carry:

| links | theorem | blocks |
|---|---|---|
| 1–5 | `strPath5` | `NodeBlock21`, `NodeBlock5`, `LeafBlock`, `sw.bb202.i`, `if.end207.i` |
| 6–8 | `strPath8` | `if.then219.i`, `if.end245.i`, `if.end256.i` |
| 9–10 | `strPath10` | `z_arena_reserve.exit`, `NodeBlock31` |
| 11–15 | `stringPath_seg` | `LeafBlock29`, both arms of its test, `if.end290.i`, `if.then328.i`, `if.else334.i` |

Every intermediate state is a `def` (`strS₁`–`strS₁₅`) whose cells and edge are the
link's own target, so each cast between a link and the composition is the link itself.

**The exposure link 15 needed, and how it is stated.**  `if.else334.i`'s target was
`callQuiet`'s existential.  `WalkLink.if_else334_i_at` takes the helper's answer `r` and
its call as parameters and concludes the target state:
`s' = { stateAt s.env {s with mem := r.mem, next := r.next} with pc := "cleanup478.i", pre := some s.pc }`.
`WalkLink.if_else334_i` is now its one-line corollary at the contract's own answer, so no
proof body is duplicated.

**The residue's provenance.**  `HstringResidue` (`JsonStage2WalkDispatchWitnessString`)
began as a `Type` of thirteen fields, each naming its producer where it was stated; the
module header's table records all thirteen and where each retired, and the structure now
carries none.  The register premises the composition used to take are the carriers' now:
`%c.i`, `%z`, `%xp` and `%nxp` are `walkStaticRegs`' (`WalkInv.regs` reads them at
every state) and `%arrayidx10.i` is `WalkIter.regarr`'s, produced by
`whileBody_step`'s `%3 + %idxprom.i` bind and read at link 8 by
`strArr_of_iter`.  The body's six memory clauses are not fields either: they are
the composition `strPath9` proves.  The answer's word was its own obligation rather than
a corollary of the bundle's `hy`, and the reason is why it needed a lemma: `hy` is stated
at the head's memory and cursor, while the call is made at the state link 8 leaves, whose
memory the reservation's zero has already written.  `stage2StringBody_head_form` is what
carries the form across that difference, and `strPath9` is where it is applied.

**R3 is not a lemma from `WalkInv.frame` and the staging**, and the reason is worth
keeping: `%z`'s first eight bytes lie **inside** the walk's write extent (`walkPresent`
carries the whole `(z, stage2LogExtent)` object), so the frame — which is silence
*outside* that extent — says nothing about them, and the staging's clauses give presence
over the object (`WalkInv.owned`) rather than the value it holds.  The bundle's
`The root slot and the log across the cursor-record store` section records the same
negative finding where a reader would try to derive it.

**The residue is empty, and each field's retirement is named.**  `HstringResidue`
(`JsonStage2WalkDispatchWitnessString:1949`) carries no fields at all, and
`WalkStringResidue` (`:1954`) is not a premise of the loop's step.  The thirteen fields it
had at its first statement are all produced by the layers below; the last two are
`WalkInv` clauses:

| id | field | became |
|---|---|---|
| R5 | arena-base word (`z + 40`) | `WalkInv.log_dst` (`JsonStage2WalkScopeRecord:387`) |
| R3 | base word (`z`) | `WalkInv.log_base` (`JsonStage2WalkScopeRecord:377`) |
| `r`, `hcallR` | the callee's answer and call | `s2StringBody_answers`, inside `strPath9` |
| R1's answer | the answer's word | `stage2StringBody_head_form`; the post at the callee's memory |
| R8 | `evalICmp .slt y 1 = 0` | `HcontArm.twoEntry`'s field: a refusing answer takes `if.then` |
| R2 | `l`, the `%outn` word, `l ≤ ext` | `s2StringBody_outn_le` and `s2StringBody_outn_at_call` |
| R6 | `G.dst < 2^64`, `G.ev < 2^64` | `WalkGeom.dstLt` and `WalkGeom.evLt` |
| — | `C.evlen < 2^63` | `WalkGeom.ev63`, through `WalkInv.evlen_le` |
| R4 | `C.events.length < C.k` | `WalkInv.events_le_of_tight`; the strict form is gone |

**The invariant's cursor pin** (finding 20) — **landed** as design (b):
`stage2BootstrapExtent : Nat := 28` (`JsonStage2Scratch:84`), the clause
`WalkInv.next_ge : G.next0 + stage2BootstrapExtent ≤ s.next`
(`JsonStage2WalkScopeRecord:422`), and the frame at
`walkWideAt G C (s.next - G.next0)` (`:440`).  The measurement that made it a one-pass
change stands: one line at 39 construction sites in ten modules, a new hypothesis at the
six helper transfers whose target state is a parameter `s₁` (`pureCore`, `pureJumpCore`,
`pureCoreCarried`, `callQuiet`, `callQuietBr`, `callQuietBrPending`) and 70 call sites in
nine modules.  The inequality rather than the equality is what keeps the clause uniform.

**The record level is the same finding** (finding 21), and **it is landed** in shape
(i): `Stage2Run` gains the stack end `nextEnd` — the clause `nextEnd_static`
(`JsonStage2Body:839`) places the five bootstrap slots inside the run's region — and the
post's stack part is the interval `[(next, nextEnd - next)]`.  `stage2Boundary`'s frame
conjunct is `∃ nextEnd, next ≤ nextEnd ∧ UnchangedOutside mem m
(stage2ReportFrame … next nextEnd)`, and the five slots are the stated consequence
`stage2AllocaWrites_reportFrame`, not a second region.  `Stage2Run.ofInv` and
`WalkInv.report` pick the end `stage2StackEnd next0 s.next`, so no caller carries the old
upper bound: the thirteen terminal theorems in `JsonStage2WalkTargetPost` lost `hnext`,
`WalkLoopEnd` lost `cursorLe`, and `walkWide_of_walkWideAt` — the lemma that needed the
cursor inside the five slots — is deleted.  The pipeline's own post follows: its stack
element is the interval `[(alloc, allocEnd - alloc)]` with `alloc ≤ allocEnd`, which is
what `PipelineDischarge` reads off the stage-2 post at the run's own end.

**Findings that still stand, at their links.**

- `WalkLink.z_arena_reserve_exit` (`JsonStage2WalkCall:2133`) **was unsatisfiable as
  written** and is repaired.  Its `hxj` put `%xj.i` at `G.next0 + 16`; `walkStaticRegs`
  (`JsonStage2WalkScopeGeom:922`) fixes `%xj.i` at `G.next0 + 12`; and at `+ 16` the
  string body's own `RegionsApart xj 8 outn 8` fails against `%outn.i = G.next0 + 20`
  (`16 + 8 > 20`).  No state satisfied `WalkInv` and that hypothesis together, so the
  ninth link could not be linked and the census row that calls it *proved* recorded a
  proof of a statement with no inhabitant.  The link states the staging's address, and
  its docstring records why the address is the link's rather than the caller's.
- the allocator-cursor pin `C.alen ≤ G.ndst0 + ix.toNat` is not a `WalkInv` clause:
  `pending = none` at a loop head, so `if_end256_i`'s `hcur` has no carrier; it is
  `HstringFacts`' field (`JsonStage2WalkDispatchWitnessString:406`), which is exactly the
  state where `pending` is `none`.
- `s2StringBodyPre`'s producer at the call site is `s2StringBodyPre_at_string_call`
  (`JsonStage2StringStageFacts:1236`), built on the assembler
  `s2StringBodyPre_of_staging` (`:121`) and the transport `s2StringBodyPre_of_reads`
  (`:369`).

### Gap 2 — F3, commit 2 (the string pre's private-slot presence) — **closed**

`s2StringBodyPre` (`JsonStage2Helpers:386`) no longer carries
`readBytes mem next 8 ≠ none`.  The clause was sufficient and not necessary, and what
makes it unnecessary is a commutation rather than an argument: the body's clear at `next`
is a write every crossing **moves**, so each crossing spends the presence of the region it
moves *into*.  `writeBytes_comm_of_present_right` is that move, `writeBytes_absorb_one`
now takes two presences where it took three, and `writeBytes_absorb_single` one where it
took two.  Eleven declarations lost a hypothesis and none gained one;
`s2StringBodyBody_contract`'s footprint is unchanged at
`[propext, Classical.choice, Quot.sound]`.

**The trap for the next reader.**  Which side the one-sided lemma spends:
`writeBytes_comm_of_present_left` spends the **first** write's region, `_right` the
**second's**.  `absorb_one` moves the first write (`ei`) across `dst`, so it needs
`_right`; `absorb_single` moves the second, so it needs `_left`.  `_right` in
`absorb_single` still compiles if the slot's presence is assumed — it silently restores
the clause.

### Gap 3 — the loop arm's `hpost` — **closed**

The loop arm's post is `stage2Post_of_staging_loop`
(`JsonStage2WalkPremisesOfStaging:1154`), built at `WalkLoopStepThree`'s terminal
disjunct (`JsonStage2WalkTraverse:698`), whose existential run carries
`Stage2BoundaryAt` at the memory it returns.  The terminal runs are theorems:
`walkFinishPost_accept` (`JsonStage2WalkTargetPost:985`), `walkFinishPost_refuse`
(`:1255`), `walkFinishPost_refuse488` (`:1446`) and `walkFinishPost_copy` (`:1605`),
composed by `walkFinishPost_merge` (`:1723`) and `walkFinishPost_refuseOfWords`
(`:1765`) into `WalkTargetPost` (`JsonStage2WalkTraverse:670`).  Consequently
`stage2WalkObligation_of_staging` (`JsonStage2WalkFlushPost:934`) takes the five payload
groups and **no `hpost`** (`:935-939`); `stage2WalkObligation_of_premises`
(`JsonStage2WalkAssembly:3137`) still takes the record's post rule as its `hpost`
argument, and the staging theorem discharges it with the flush and loop posts.

**The three routes, from the merge and from the copy.**  All at a variable `sd.mem`; each
is now a terminal run at its own block.

| route | path | writes over `sd.mem` | verdict | theorem |
|---|---|---|---|---|
| R1 accept | `cleanup478.i → if.then485.i → if.end490.i → s2_walk.exit → if.end` | 2 (`%alen` at `%ndst`, `%len` at `%nev`) | `1` | `walkFinishPost_accept` |
| R2/R3 refuse | `cleanup478.i → if.then485.i → (if.then488.i \| if.end490.i → if.then492.i) → if.then → if.end` | 4 (`%4` at `%e + 8`, then the record's three) | `0` | `walkFinishPost_refuse`/`_refuse488` |
| R0 refuse, already at the copy | `if.then → if.end` | 3 (the record's) | `0` | `walkFinishPost_copy` |

The word copied to `%ndst` is the log's arena word `a` with `ndst0 ≤ a ≤ Cd.alen`
(`WalkInv.log_alen`), **not** `Cd.alen`; `%nev` is exactly `Cd.evlen`
(`WalkInv.log_len`).  The rest of the 25 conjuncts of `stage2Boundary`
(`JsonStage2Contract:1137`) are `WalkInv`'s clauses — `alen_le`, `evlen_le`, `evlen_eq`,
`owned`, `frame`, `depth_reg`, `depth_cap`, `sp_le_wlen` — plus the geometry's two
capacity widths.

**Where the facts the routes needed now live.**  `%4`'s word is the static carrier's:
`%4` is an entry of `walkStaticRegs` (`JsonStage2WalkScopeGeom:940`), read by
`walkMerge4_of_regs` (`JsonStage2WalkTargetPost`), so no refusal arm supplies it.  The
finalisation's registers are the carrier's too, through `walkFinalEnv_of_regs`
(`JsonStage2WalkTargetPost`).  The refusal word at a direct copy entry is
`walkFinishPost_refuseOfWords`' argument; `WalkLink.refusalStore`
(`JsonStage2WalkScopeClasses:870`) stores it and sets `eoff`, and the copy's theorem
names the word at the copy's own state.  The merge's root-done word is `WalkInv.root_slot`
(`JsonStage2WalkScopeRecord`), and `walkFinishPost_merge` decides R1 against R2/R3 from
it.  The flush arm's producer donates `stage2Post_of_completion` and the packing shape of
`stage2Boundary_of_flush`; it does not donate `stage2Run_boundary`/
`stage2Boundary_of_parts`, whose `herrWalk`/`frameSlots` are false on these arms for the
reason `JsonStage2WalkFlushPost:38-50` records.

**The old stale line is gone with the module split.**  The reference this section used to
carry — `JsonStage2WalkScope.lean:2936`, calling the terminal run `WalkTargetRun` — has no
counterpart at `e268d1c`: `JsonStage2WalkScope` is a 315-line import front-end (see the
header), and the terminal vocabulary is `WalkTargetPost` (`JsonStage2WalkTraverse:670`).
The per-link evidence for the string path is recorded in
`JsonStage2WalkDispatchWitnessString`'s header (the fifteen links and the residue
retirement table); no register is a parameter, since `%c.i`, `%z`, `%xp` and `%nxp` are
`walkStaticRegs`' and `%arrayidx10.i` is `WalkIter.regarr`'s, so `WalkInv.regs` and
`WalkInv.iter` read all five at every loop state.

---

## What remains — five payload groups, and what each now costs

`stage2WalkObligation_of_staging` (`JsonStage2WalkFlushPost:934`) takes five groups
(`:935-939`), and `pipeline_satisfies_at_stage2_of_exitStage2` (`PipelineDischarge:2859`)
forwards the same five (`:2860-2864`), so the pipeline's statement inherits this list.  The
five are `hcont`, `hrows`, `hlast`, `hlastRows` and `hlastArms`; `hws` is gone with the
whitespace group (`ee7544f`), and the arity drop is a hypothesis removal with every
conclusion unchanged.  No group has an unconditional `∀ G` producer: the only whole-group
inhabitant is `hcontPayload_of_nep_zero` (`JsonStage2WalkDispatchSupply:1131`), and it is
pointwise at `G.nep = 0`, where no continuing head exists.

The row groups are now *built from a named supply structure* rather than stated as bare
goals: `HcontClassRows` by `hcontClassRows_of_supply` (its four literal-`0` fields restated
at `282ac25`), `HlastClassRows` by `hlastClassRows_of_supply` (`a84c287`) and
`HlastArmRows` by `hlastArmRows_of_supply` (supply six fields at `ee7544f`; its
`.letters`/`.classC` took their present refusal shape at `7167cca`).  The three self-refuting families the previous pass recorded
are all resolved at `ee7544f`: the class rows' four literal-`0` fields are
`HcontSeamRefusal` (`282ac25`), the last rows' `.letters` and `.classC` are the same
refusal shape plus `HlastRefuseRoute` (`7167cca`), and the `.ws` group was deleted rather
than restated (`ee7544f`).  No refuting theorem is recorded against a field of the five
groups at `ee7544f`; the three known families are the ones above.

The census below is per group; the value kind is `D` = document word, `S` = staged word (a
call row, staged argument list or model answer), `H` = hypothesis (a route, segment or
geometry premise).  Every build cited is its own commit's.

| group | produced (theorem) | supplied (carrier; value kind) | unsatisfiable (refuting theorem) |
|---|---|---|---|
| `HcontPayload` (`JsonStage2WalkDispatchSupply:864`) | `abi.openCall` (`hcontAbi_openCall`, `JsonStage2WalkDispatchAbiOfInv:56`) and `lane.defaultLane` (`hcontDefaultRow_of_inv`, `JsonStage2WalkDispatchDefaultLane:124`; field `:161`) at every `G`; `abi.string` (`hcontStringCalls_of_lane`, `AbiOfInv:135`) modulo its body-side supply `hpreS`/`y`/`hR8`.  The produced fields are **pointwise**; the group has no `∀ G` inhabitant | `lane.string` — carrier `HcontStringLane` (`Supply:313`), **D** (`bs`/`hreadLane`/`hq`, `rd`/`hreadRoot`, `A`/`hreadA`, `Cc`/`hreadC`) + **H** (`hcur`/`hwin`); `trav.visits` — `ScanVisitsDoc` (`JsonStage2WalkDispatchTravOfStaging:59`), **D** | none.  The only whole-group inhabitant is `hcontPayload_of_nep_zero` (`Supply:1131`, pin `JsonStage2WalkDispatchSupply:1162`): `Nonempty (HcontPayload G)` at `G.nep = 0`, where no continuing head exists |
| `HcontClassRows` (`JsonStage2WalkDispatchClassRows:652`, 16 fields) | `cleanup` (`hcontCleanupDoc_of_lane`, `ClassRows:160`), `run` (`hcontArm_run_of_row`, `ClassRows:290`) and `seam` (`hcontSeamAbi`, `JsonStage2WalkDispatchSeamCalls:744` from `HcontSeamStaging`, `:710`); constructor `hcontClassRows_of_supply` (`JsonStage2WalkDispatchClassRowsProduce:159`), `∀ G` form `_all` (`:181`) | `HcontClassRowsSupply` (`ClassRowsProduce:79`), 13 fields: `cleanupRow`/`letters`/`c56Else`/`c58Else` — `HcontSeamRefusal` at literal `0` (`:82`), **S**; `scalar` (`:88`, literal `7`), `fLetter` (`:100`, `9`), `c56True` (`:103`, `10`), `c58True` (`:110`, `8`) — `HcontSeamRow`, **S+D**; `scalarRun` (`:94`) — **D+S**; `deep` (`:117`) and `refuseSeg` (`:134`) — **H**; `runSkip` (`:121`) — **D**; `runTail` (`:126`) — **D+S** | none.  `HcontSeamRow.not_nonempty_zero` (`ClassRowsProduce:223`) refutes only the old emit-row form of the four fields; `282ac25` restated them as `HcontSeamRefusal` at the same carry, state and literal |
| `HlastPayload` (`JsonStage2WalkDispatchSupply:1013`) | `abi.openCall` (`hlastAbi_openCall`, `JsonStage2WalkDispatchHlastSupply:219`) at every `G`; `lane.tail`'s byte route at the premise `¬ wsStop G (G.n - 1)` (`hlastLane_of_not_wsStop`, `:155`), with `HlastTailLane_not_of_wsByte` (`:163`) showing the field empty at a whitespace last byte; `abi.highByte` (`hlastAbi_highByte`, `:439`) from the staged rows, and the emission residue is empty on the class (`hlastResidue_empty`, `:460`) | `HlastLane.tail`'s premise — **H** (geometry); `HlastAbi.highByte`'s carrier `HlastHighByteRefusal` (`JsonStage2WalkDispatchWitnessHlast:1560`): `rows` are **S** at `HlastSeamRefusal`, `route` is **H** (`HlastRefuseRoute`); root/log words produced (`hlastTailRoute_rootSlot_word`, `JsonStage2WalkDispatchHlastSupply:290`; `hlastTailRoute_logBase`, `HlastSupply:278`) | none.  The refusal route is composed by `hlastAnswerOneRefuseRoute` (`JsonStage2WalkDispatchLastSeamRoute:224`), and `hlastSeamAnswerOne_nonempty` (`JsonStage2WalkDispatchLastSeamRoute:267`) inhabits `HlastSeam.answerOneRefuse`; the head-to-landing prefix and the seam's refusal rows remain supply |
| `HlastClassRows` (`JsonStage2WalkDispatchClassRows:845`) | `tail` (assigned from `HlastPayload.lane.tail` in `hlastClassRows_of_supply`, `ClassRowsProduce:201`; `∀ G` form `_all` `ClassRowsProduce:207`), inheriting that field's `¬ wsStop` premise; constructor `hlastClassRows_of_supply` at `ClassRowsProduce:201` | `HlastClassRowsSupply` (`ClassRowsProduce:189`): `seam`, the last seam as the sum `HlastSeam` (`Seams:406`) — **S+H** (staged words at `hlastTailByte`, answer/record derived; `hlastSeamRefusal_of_stage` `HlastSupply:391`, `hlastSeamZero_of_calls` `HlastSupply:407`, whole sum `hlastSeam_nonempty` `HlastSupply:398`) | none |
| `HlastArmRows` (`JsonStage2WalkDispatchLastRows:305`, six fields) | `.fLetter`'s tail only, by `HlastFLetterSupply.rows` (`JsonStage2WalkDispatchLastArmRows:449`), applied in `hlastArmRows_of_supply` (`:589`); `∀ G` family `_family` (`:601`); `HlastClassCTrueRows`' tails are produced by `hlastClassCTrueRows_of_span` (`:276`) from the byte's span | `HlastArmSupply` (`LastArmRows:535`): `.scalar` (`:536`) — **D+S**; `.letters` (`:544`) — `HlastLettersRows` (`LastRows:148`), **S** refusal rows + **H** head chain and `HlastRefuseRoute`, the arm `LastEntryArm.refuse` (`7167cca`); `.classC` (`:559`) — `HlastClassCRows` (`LastRows:189`), **S** + **H** head chain, span and route, arm `.refuse`; `.classCTrue` (`:569`) — `HlastClassCTrueRows` (`LastRows:214`), **S**, the two emitting leaves; `.run` (`:579`) — `HlastRunRows` (`LastRows:241`), **D+S+H**; `lastArmScanEntry_envTok` (`LastArmRows:161`) is the shared environment row | none.  `HlastSeamTailSupply.not_nonempty_of_else405` (`LastArmRows:471`) still refutes the old emit tail at `LetS413`/`ClsS413F`/`HeadS413`; `7167cca` replaced it in `.letters`/`.classC` with `HlastSeamRefusal` + `HlastRefuseRoute` and added `.classCTrue` for `110`/`116` |

Everything between those groups and the obligation is produced: `walkPremises_of_staging`
(`JsonStage2WalkPremisesOfStaging:967`) reads the five and returns `WalkPremises`;
`walkContinueFacts_of_payload` (`JsonStage2WalkDispatchContinuing`) and
`walkLoopEnd_of_payload` (`JsonStage2WalkPremisesOfStaging:484`) build the two bundles from
them; `stage2Post_of_staging_flush` (`JsonStage2WalkFlushPost:854`) and
`stage2Post_of_staging_loop` (`JsonStage2WalkPremisesOfStaging:1154`) build the post.

**What the deletions mean for the obligation.**  `HcontSeamRow.not_nonempty_zero`
(`JsonStage2WalkDispatchClassRowsProduce:223`) and
`HlastSeamTailSupply.not_nonempty_of_else405`
(`JsonStage2WalkDispatchLastArmRows:471`) are unconditional `¬ Nonempty …` results at the
structures' own types: an obligation supplied with the old emit-row or emit-tail form would
have proved nothing about the walk.  All three uses of that form are resolved at
`ee7544f`: the class rows carry `HcontSeamRefusal`, the last rows carry `HlastSeamRefusal`
plus `HlastRefuseRoute`, and the `.ws` group is deleted.  The refutations remain in the
tree as the record of why the shapes changed.

### `HcontPayload`: the lane, the calls and the visits

* **`lane.defaultLane` — produced** (`hcontDefaultRow_of_inv`,
  `JsonStage2WalkDispatchDefaultLane:124`; the field at `hcontLane_defaultLane`, `:161`).
  The word is the entry stream's own (`walkReadBytes_entryPos_word`), its span and strict
  order are `entryPos_strict`'s, the compare is `contIx_toNat`'s, and the byte's class is
  `HcontByteClass.complete`'s.  Nothing is supplied, so the lane group now costs `string`
  alone (`hcontLane_of_string`, `:169`, fills it from that field).
* **`abi.openCall` — produced** (`hcontAbi_openCall`,
  `JsonStage2WalkDispatchAbiOfInv:56`): the root slot's word is
  `walkReadBytes_rootSlot_word`, the precondition `WalkInv.tyBytes`/`stBytes` at
  `C.sp - 1` (or nothing at depth zero), and the answer `s2ValuePos_answers`.  The same
  composition as `hlastAbi_openCall` (`JsonStage2WalkDispatchHlastSupply:219`).
* **`abi.string` — repaired** (`JsonStage2WalkDispatchAbiOfInv`).  The field now takes the
  lane's own words — `L.rd` (the root slot's read) and `L.A` (the log's arena read) — and
  the accepting arm's guard `L.rd.toNat = 0`:
  `∀ … → (L : HcontStringLane G C s) → L.rd.toNat = 0 → HcontStringCalls G C s L.rd L.A`.
  `walkContinueArm_of_payload` splits on it: the zero word is `hcontArm_twoEntry_of_payload`,
  the nonzero one is the refusal arm above.  The guard is load-bearing: at depth zero the
  callee's reply is `if rd = 0 then 1 else 0`
  (`stage2ValuePos_zero_reply`), so `HcontStringCalls` is uninhabited at every other word
  (`hcontStringCalls_uninhabited_of_ne`, `:100`), which is why the old universal (every
  `rd`, every `A`) could not be inhabited.  `hcontStringCalls_of_lane` composes what the
  field carries — the value-position pre from the invariant, the answer `1` and `hbranch`
  — so the row's remaining supply is exactly the body's side: `hpreS` (the arena's
  presence at `G.dst + L.A.toNat`), the answer `y` and its accepting test `hR8`.
* **`trav.visits` — document supply, now stated as its own row.**  `scanVisits_of_class`
  (`JsonStage2WalkDispatchAbiOfInv:214`) proves `ScanVisits` from one row: every index the
  extra-token scan visits reads a `9` or `10` byte.  `hcontTrav_visits_of_class` (`:266`)
  is the field from it.
  `f46dfa4` names that row: `ScanVisitsDoc` (`JsonStage2WalkDispatchTravOfStaging:59`) is
  "every index in `(entryPos C.k, entryPos (C.k+1))` reads a `9` or `10`",
  `scanVisitsDoc_bits` (`:64`) bridges those bytes to the latch's two comparisons, and
  `hcontTravVisits_of_doc` (`:80`) turns it into the field.  `WalkGeom`'s `doc`,
  `entries`, `order` and `inside` fix no interior byte value — a continuing token with a
  non-whitespace interior satisfies every `WalkGeom` clause and fails the row — so no
  producer can supply it at a variable geometry; the payload's supplier must carry it, and
  a future reader of `HcontPayload.trav` takes the field from that supplier.  Everything
  else in `ScanVisits` — `%3`'s address, the read, the `%47` cell and the three local facts
  — is the invariant's.

### The seam

`HcontSeamAbi` (`JsonStage2WalkDispatchSeams:449`) has five fields — `scanRefuse`,
`scanF`, `scan56True`, `scan58True` and `last` — and every one is inhabited: `hcontSeamAbi`
(`JsonStage2WalkDispatchSeamCalls:744`) builds the group from `HcontSeamStaging` (`:710`),
the seam's staged words, so the supply is that structure — `HcontSeamStage` (`:378`) per
emit field, `HcontSeamEmitStage` (`:401`) adding the emit row — and not five independent
rows.  The last entry's seam is the same group's `last` field, and the three-way `HlastSeam`
(`JsonStage2WalkDispatchSeams:406`) is its sum: `answerZero`/`answerOneRefuse`/
`answerOneEmit`, supplied by `hlastSeamZero_of_calls`/`hlastSeamRefusal_of_stage`/
`HcontSeamAbi.last` respectively.

The `if.else405.i` edge writes the literal `0`, and `stage2ScalarValue` answers `0` at kind
`0`, so that seam is a **refusal**, not an emission: it has the two leading calls, no third
call, and `HcontSeamAbi.scanRefuse` is derived from the staged words alone
(`hcontSeamRefusalOf`).  `hcontSeamCalls_no_kind_zero` (`JsonStage2WalkDispatchSeamCalls:765`) and
`hcontSeamCalls_no_literal_zero` (`SeamCalls:791`) refute the emit group at that literal.  Two
staged rows have no producer and are the class's document row: the scalar staging's first
two words (`hpreS`) and the scalar call's emit answer (`hemit`).

**Three refutations at that literal, all resolved at `ee7544f`.**

* `HcontSeamRow.not_nonempty_zero` (`JsonStage2WalkDispatchClassRowsProduce:223`) proves no
  `HcontSeamRow` exists at the literal `0`.  The four `HcontClassRows` fields that named
  that row at a `0` literal — `cleanupRow`, `letters`, `c56Else`, `c58Else` — were therefore
  uninhabited as stated; `282ac25` restates them as `HcontSeamRefusal`
  (`JsonStage2WalkDispatchSeams:373`) at the same carry, state and literal, keeping their
  names and positions, and the four consumer families build `HcontArm.badToken` through
  `hcontArm_badToken_of_row` (`ClassRows:797`) and `refuseSeg` (`ClassRows:776`).  The fields remain
  genuine supply: `HcontSeamRefusal` carries only call data, and the route is `refuseSeg`'s.
  This repair is landed.
* `HlastSeamTailSupply.not_nonempty_of_else405` (`JsonStage2WalkDispatchLastArmRows:471`)
  proves the emit tail has no inhabitant where the seam's literal is `0`.  `5cd238a` stated
  the last rows with an emitting `hTail` at exactly the three such seams — `LetS413`,
  `ClsS413F`, `HeadS413` — so those rows were uninhabited there.  `7167cca` lands the
  restatement: `HlastLettersRows` (`JsonStage2WalkDispatchLastRows:148`) and
  `HlastClassCRows` (`:189`) carry `HlastSeamRefusal` plus a `HlastRefuseRoute`
  (`JsonStage2WalkDispatchSeamRow:40`/`:77`), the new `HlastClassCTrueRows` (`JsonStage2WalkDispatchLastRows:214`) carries
  the emit payload for `110`/`116` only, and `LastEntryArm.refuse`
  (`JsonStage2WalkDispatchArms:316`'s inductive) is the arm the class case builds.  The
  refutation stays in the tree as the reason those seams are not emit groups.
* `hcontWsTail_not_nonempty`, `hcontWsRows_tail_false` and `hcontArm_ws_of_rows_vacuous`
  were compiled at `ef459b4` in `JsonStage2WalkDispatchWsRouteAudit` (`:95`/`:104`/`:116`),
  and proved `HcontWsTail` empty at every parameter: its `calls` field was an emit group
  with `hcA = 0` at `if.else405.i`.  `ee7544f` does not restate the tail; it **deletes the
  group**.  The next section records the second, independent reason — the `run` field was
  false at an admissible carry — and why deletion is the right cut rather than a repair.

**The vacuous `.run` cells — removed.**  The six tag-clear default classes'
`.run × wsByte` cells used to be inhabited only through `HcontClassRows.seamScan`, the emit
group at literal `0`, which `hcontSeamCalls_no_literal_zero` refutes (commit `8f56159` marked
each cell).  The repair landed as option (b): `HcontClassRows.refuseSeg`
(`JsonStage2WalkDispatchClassRows:776`) states the kind-`0` edge's *refusal* route as a
segment with the slow scan's stop named — `if.then413.i`'s call, `if.then425.i`'s scalar call
with answer `0`, `if.then432.i`, the slow scan at
`cond.end.i96`/`land.rhs.i103`/`while.body.i104`, `while.end.i`, `if.end.i97`, `if.else.i`,
`NodeBlock83`'s pivots, `if.else43.i`'s refusal store, `cleanup474.i` — and
`hcontArm_badToken_of_row` (`:797`) builds `HcontArm.badToken` from it plus the head state's
byte facts (tag bit clear, byte outside the three literal pivots), with the answer `0` and
the record taken from `HcontSeamAbi.scanRefuse` (nothing here supplies an answer).  Those
bytes are never value bytes, so the six tag-clear default classes take the refusal arm
(`JsonStage2WalkDispatchContinuing:25`) and its dispatch is `WalkDispatchResult.refuse`.
`HcontClassRows.seamScan` and `RunRow`'s three cast-leaf wrappers are **deleted**; the five
purely kind-`0` `.run` arms no longer have a group of their own, and `253b785` deletes their
five orphaned head-chain producers (`lowHeadChain_of_lane`, `midHeadChain_of_lane`,
`othHeadChain_of_lane`, `brkHeadChain_of_lane`, `brcHeadChain_of_lane`) and corrects the
prose in `DefaultLane`, `Supply`, `Seams`, `Residual` and `docs/contract.md`'s `c7`/`c8`
that still described those classes as building chains.  The continuing refusal continuation
segment is the arm's route; `HlastRefuseRoute` is the *last* level's counterpart, and its
composition from the slow scan is described above, with its head-to-landing prefix still
supply.

### Phase verdicts

- **C — landed: the branch census, the counted scans and the group producers.**  The
  continuing branch census is exhaustive (`HcontClass.complete`,
  `JsonStage2WalkDispatchHcontArms:301`) and the class case consumes it in
  `walkContinueFacts_of_payload` (`JsonStage2WalkDispatchContinuing:552`); the last entry's
  switch is the bit case in `walkLoopEnd_of_payload`, over `LastEntryArm`'s constructors
  (`JsonStage2WalkDispatchArms:316`).  The counted scan is `wsRun`
  (`JsonStage2WalkRevolution:1646`) with `wsRun_go` (`:1541`), composed into the entry,
  first visit, seam and price by `contWsRunF` (`:3869`), and the last entry's slow scan is
  `slowRun`/`slowRun_go` (`JsonStage2WalkDispatchSlowRound:864`/`:631`) with `slowVisit_at`
  (`JsonStage2WalkDispatchSlowVisits:608`) and `hlastAnswerOneRefuseRoute`
  (`JsonStage2WalkDispatchLastSeamRoute:224`, `7209fc8`).  The continuing kind-`0` refusal
  is landed (`refuseSeg`/`badToken`; the class rows' four zero-literal fields are
  `HcontSeamRefusal`, `282ac25`), the last level's seam is `HlastSeam`'s sum, and the last
  rows' refusing leaves are `HlastSeamRefusal` + `HlastRefuseRoute` (`7167cca`).  The `.ws`
  group is deleted (`ee7544f`), so the phase leaves the supply the census names, not a
  repair queue.  Remaining is that supply itself: `lane.string`, `abi.string`'s body side,
  `trav.visits`' `ScanVisitsDoc`, the class and last-level staged rows, and the last
  entry's head-to-landing prefix for `HlastRefuseRoute`.
- **D — half landed.**  `hpost` is retired from `stage2WalkObligation_of_staging`
  (`JsonStage2WalkFlushPost:934`); `WalkPremises` is not yet derived from the ABI preconditions.
  `walkPremises_of_staging` (`JsonStage2WalkPremisesOfStaging:967`) takes the five groups,
  so the five above are the whole distance between the staging and the ABI.
- **E — open, and partly outside Lean.**  The native route lacks the semantics-to-object
  step: `missingBridgePieces` (`JsonCallRoute:1478-1500`) names it beside the in-`lake`
  adapter, the staging copy, the link step and the table initialisation, and nothing
  connects a run of the linked object to `pipelineUnitsPost`.

---

## The whitespace class — deleted, and why (`ee7544f`)

The run the class needed is still a theorem, and the tree keeps it: `wsRun`
(`JsonStage2WalkRevolution:1646`) and its induction helper `wsRun_go` (`:1541`) prove the
skip from the latch to its stop, and `contWsRunF` (`:3869`) composes the entry dispatch,
the first visit, the run, the seam and the price as one existential segment.  `HcontFacts`
(`:2223`) carries no run field — the class is `hClass` and the run is derived — and it
carries **55** fields at `ee7544f` (counted over the structure body, `:2224-2418`); `hRun`,
`hnRun`, `hcond_sl`, `sl`, `b8` and the count `n` are retired.  The definition layer and
the visit segments remain in `probes/stage2/ws-run-draft.lean` (not imported, not built) as
the instrument: `wsByte`/`wsX`/`wsLandS`, `wsLeafS` (the three leaves as one `def`),
`wsStopS`, `scanB_ofNat`, `wsContinue43/46/48` and `wsVisit43Exit` — the **exit visit is
not a wall**, it is the back-edge proof with `if_pos` on the leaf's test and `pc` moved.

Five measured corrections, which the landed proof keeps:

1. **The count is a bound, not an equality.** `LeafBlock43`'s class costs 4 links per
   continuing byte, `46`/`48` cost 5, so the exact count is `9 + Σ c_p` and `5(k−i)+9` is
   attained only when every byte crosses the second pivot.  The run states
   `∃ n, n ≤ 5(k−i) + 9 ∧ WalkSegment … n`, which is the bound `contWsRunF` returns.
2. **The source is class-indexed too**: `%35 ∈ {9,10} → NodeBlock41 → LeafBlock33 →
   preheader` (3), `13` and `32` take 4.  Sourcing the run at `contLandS` needs a second
   three-way dispatch, which the plan named only for the endpoint.
3. **Premises the header omits**: `i ≤ k` (the measure `k−i` otherwise underflows) and
   `%35`'s class bits.  `entryPos G (C.k+1) ≤ G.n` is *not* new — it follows from `hk`,
   `G.inside` and `readLanes32_length`, but needs a small `entryPos_lt_n`.
4. **The price closes with the bound, and `+5` is load-bearing**: `8(v−1−k) = 8(v−i) −
   8(k−i) − 8`, so the left side is `≤ 8(v−i) + 1 − 3(k−i) ≤ 8·ΔA + 5` from exactly
   `entryPos C.k ≤ i` and `hspan`.
5. **Machinery**: nested record updates are `rfl`, but a lemma's `scanCarry*` target needs
   `scanCarryLatchOf`/`scanCarryLeafBlock46`/`_48`/`scanCarryNodeBlock50` in the `simpa`
   set; `.env` of `stateAt` does not reduce under `simp`/`dsimp`, so cell peels need the
   `show … (cells […]) …` or `…_env` idiom.

The order the evidence supported — (a) `wsVisit46Exit`/`wsVisit48Exit`; (b)
`wsExit43/46/48`; (c) `wsLatchAt`/`wsStopAt` and the induction; (d) the entry dispatch
with `ScanEntered` and `v − i ≤ C.inner`; (e) the seam at `wsStopS` and
`contWsStop_cond` — is the order in which it landed.  Its consumers are
`contWsRunAt33/35/37`, joined by `contWsAfterPreAt`.

**What `ee7544f` deleted, and the two independent reasons.**  The seam's emit group was
refuted first (`ef459b4`), and the run was then found refutable at an admissible state;
together they made the group unusable, and `ee7544f` removed it rather than restating its
tail.

*The seam.*  `HcontWsTail` (`JsonStage2WalkDispatchWsRows:122`, at `ef459b4`) carried
`calls : HcontSeamCalls G (ContTailStartC C) (contWsTailStart …)` and
`hcA : calls.cA = BitVec.ofNat 32 0`; that is an **emit** group at `if.else405.i`'s literal,
and no such group exists there.  The three refutations were compiled at `ef459b4` in
`JsonStage2WalkDispatchWsRouteAudit`:

* `hcontWsTail_not_nonempty` (`JsonStage2WalkDispatchWsRouteAudit:95`) proves `¬ Nonempty (HcontWsTail …)` at every
  parameter;
* `hcontWsRows_tail_false` (`WsRouteAudit:104`) is the group's `tail` field at a continuing head
  state, so `HcontWsRows` had no inhabitant at the case's own hypotheses;
* `hcontArm_ws_of_rows_vacuous` (`WsRouteAudit:116`) makes the `.ws` cell's whole argument list imply
  `False`, before any document row is read.

`ef459b4`'s message records the pins as `[propext, Quot.sound]`.

*The run.*  `HcontWsRows.run`'s hypotheses named the class's two head-byte bits, the entry
stream's span and the skip's document rows, but **not** the budget row
`v.toNat - (contIx G C).toNat ≤ C.inner`; the conclusion `HcontRunBody`
(`JsonStage2WalkRevolution:3738`) carries that row inside `hClass`, whose conjunct is
`v.toNat - ix.toNat ≤ C.inner` (`:3759`).  The producer takes exactly the missing premise —
`hcontRunBody_wsCheck`'s `hinner` (`JsonStage2WalkDispatchWsRowsProduce:108`, at
`ef459b4`) — which is the tell that the field, not the producer, was under-specified.  An
earlier narrowing (`816cf737`) had added the class's two head-byte bits to `run`'s guard,
which removed a separate `-`-head falsity (`hcontRunBody_dash_false`); it did not touch the
budget row, which no head-byte bit constrains.

**The counterexample — argued, not a compiled pin.**  Fix any `G`, `C`, `s` with
`hInv : WalkInv G C s`, `C.block = walkLoopHead`, `C.k + 1 < G.nep`, the class's two bits
and the lane rows, and set `C₀ := { C with inner := 0 }` at the same state.  Then:

* `WalkInv G C₀ s` holds.  The invariant's carry-level `inner` clause is `inner_cap`
  (`JsonStage2WalkScopeRecord:270`), which becomes `0 ≤ walkInnerCap G`
  (`JsonStage2WalkScopeGeom:686`); at `walkLoopHead = "NodeBlock21"` the block-local
  clause (`WalkInv.blockLocal`, `ScopeRecord:442`) is the guard `C.k < G.nep`
  (`JsonStage2WalkScopeGeom:784`), which names no budget; every other clause reads a
  carry field the update leaves alone.
* The field's hypotheses transfer definitionally, since they mention the carry only through
  `C.k` and `C.block`.  Applying `run` yields
  `b : HcontRunBody G C₀ (wsCheckS G C₀ s v)`.
* `b.hugt` gives `b.ix.toNat < b.v.toNat`, so the difference is positive; `b.hClass` gives
  `b.v.toNat - b.ix.toNat ≤ C₀.inner = 0`.  Contradiction.

The argument needs only `b.hugt` and `b.hClass`; it does not identify `b.v` with `v`, and
no document is read — the carry, not the bytes, makes the field empty.  An illustrative
document shape (`G.n = 3`, `G.bs = [126, 10, x]`, lane `2`, so the byte before the entry's
end is `10`) is available, but the refutation above is the claim.  It was drafted and
argued, **not elaborated**: no `#print axioms` line pins it, and this document does not
cite one.

**The cut.**  `ee7544f` deletes `HcontWsRows`, `HcontWsTail`, `hcontFacts_of_rows`,
`hcontArm_ws_of_rows`, `HcontWsSeam` with `hcontWsSeam_of_body` and
`hcontScanTail_of_seam`, and the modules `JsonStage2WalkDispatchWsRows`, `…WsRowsProduce`
and `…WsRouteAudit`, with their imports in `LeanLLVM.lean`.  The
`.defaultValueHigh × .wsByte` cell of `walkContinueArm_of_payload`
(`JsonStage2WalkDispatchContinuing`) builds `hcontArm_cleanup_of_class`
(`JsonStage2WalkDispatchClassCase:284`) — the same `badToken`/`refuseSeg` route as the
three scan-free branches beside it — and `HcontFacts` (`HcontArm.ws`'s bundle) and its
producer `hcontFacts_of_staging` (`JsonStage2WalkHcontFactsOfStaging:624`) remain live, as
does `wsRun`/`contWsRunF` for the `.run` class.

**Why deletion is the right cut.**  Restating the tail (the repair `ef459b4` recorded)
would have left `run` false at `C.inner = 0`: the class case would still have had to build
the `.ws` arm from a field no carry inhabits.  The refusal route reads no document row —
`126`/`127` reach `if.else405.i` through the head switch, and that seam's literal is fixed
by the class, not by the byte — so the delivered cell is true where the old one was empty.


**The last entry's arm.**  `WalkLoopEnd` (`JsonStage2WalkPremisesOfStaging:331`) carries
one field, `hlast : LastEntryArm`, and `walkLoopEnd_of_payload`
(`JsonStage2WalkPremisesOfStaging:484`) builds it from `HlastPayload`, `HlastClassRows` and
`HlastArmRows`; the merge's two log words are
`WalkInv.log_alen`'s witness (`walkMergeWords_of_inv`, `walkRefuseWords_of_inv`), not
fields.  `HlastFacts` (`JsonStage2WalkDispatchWitnessHlast:206`) is the input's facts at
the last entry.  The second pass's two corrections stand: the head byte's eight class
bits are **not** all `WalkGeom.doc` consequences — six follow from two
(`hlt125`/`hne125`, which pin the byte), and those two are the document's *content*;
and the head's guard is read off the block-local clause by `WalkInv.head_lt`
(`JsonStage2WalkScopeRecord:453`), so `C.k < G.nep` is a consequence at the loop head
rather than a supply.

**The last payload's own fields.**  `HlastAbi.openCall` is produced with no premise
(`hlastAbi_openCall`, `JsonStage2WalkDispatchHlastSupply:219`).  `HlastLane.tail`'s byte
route is produced at the geometry premise `¬ wsStop G (G.n - 1)`
(`HcontByteRoute_of_not_wsStop`, `:87`; the group at `hlastLane_of_not_wsStop`, `:155`): the
document's last byte has a route exactly when it is not one of the four whitespace bytes,
and nothing in `WalkGeom` or `WalkInv` excludes a document ending in whitespace.  The
high-byte group's root slot and log words are `hlastTailRoute_rootSlot_word` (`:290`) and
`hlastTailRoute_logBase` (`:278`).  The class **does not emit** (kind `0`, the scalar call
answers `0` and the walk never calls `s2_after_value`), so the emission bundle has no
inhabitant — `hlastResidue_empty` (`:460`) at the `HlastResidue` the tree carries — and the
old three-call empty form (`hlastHighByteAbi_empty`) no longer exists.  What the class's
payload carries instead is the **refusal evidence** `HlastHighByteRefusal`: the two leading
calls (`hlastHighByteRefusal_of_stage`, `:429`) and the answer-`0` sub-route derived through
`s2ScalarValue_refused`.  The **route to the refusal copy** — `HlastRefuseRoute`
(`JsonStage2WalkDispatchSeamRow:77`, stated in `JsonStage2WalkDispatchHlastSupply`'s header
as the class's route) — is the last
level's counterpart of the continuing class's `refuseSeg`, and its scan half is now a
theorem (`7209fc8`): `slowRun` proves `∃ n, n ≤ 5 * (G.n − entryPos G C.k) + 10`,
`slowVisit_at` composes the stop visit's own priced segment, and `slowAnswerOnePrice`
prices the run inside `32·(G.nep − C.k) + 8·(G.n − entryPos G C.k)`.
`hlastAnswerOneRefuseRoute` (`JsonStage2WalkDispatchLastSeamRoute:224`) composes a prefix
segment to `land.rhs.i103` and that run into a `HlastRefuseRoute`, and
`hlastSeamAnswerOne_nonempty` (`:267`) then inhabits `HlastSeam.answerOneRefuse` with the
arm's statement unchanged.  What is still supply is the prefix from the head to the scan's
landing and the seam's refusal rows themselves.

**The last rows now carry the refusal seams (`7167cca`).**  `HlastArmRows`
(`JsonStage2WalkDispatchLastRows:305`) has **six** fields — `.scalar`, `.letters`,
`.fLetter`, `.classC`, `.classCTrue`, `.run` — and `HlastArmSupply`
(`JsonStage2WalkDispatchLastArmRows:535`) mirrors them; `hlastArmRows_of_supply` (`:589`)
builds the group, producing only `.fLetter`'s tail (`HlastFLetterSupply.rows`, `:449`).
The two refusal classes are:

* `.letters` (`LastRows:320`) — `HlastLettersRows` (`JsonStage2WalkDispatchLastRows:148`): head chain, `HlastSeamRefusal`
  at `LetS413` and a `HlastRefuseRoute`; no emitting tail;
* `.classC` (`LastRows:342`) — `HlastClassCRows` (`JsonStage2WalkDispatchLastRows:189`): head chain, span,
  `HlastSeamRefusal` at the span's endpoint and the route.

`HlastClassCTrueRows` (`LastRows:214`) is the new emit row for the two class-C leaves
`110`/`116`, whose seams write `if.then403.i`'s `10` and `LeafBlock58`'s `8`; its tails are
produced by `hlastClassCTrueRows_of_span` (`LastArmRows:276`).  The guards are a
partition: `.classC` (`LastRows:342`) carries `hne110` and `hne116`, while `.classCTrue`
(`JsonStage2WalkDispatchLastRows:355`) carries `hleaf : %8 = 110 ∨ %8 = 116`; within the class-C range that reaches the
default arm, `.classC` is every byte but those two and `.classCTrue` is exactly those two.
The class case (`JsonStage2WalkPremisesOfStaging:512`/`:532`) builds `LastEntryArm.refuse`
from `.letters`'/`.classC`'s route, and `lastEntryArm_classC_of_staging` (`:519`/`:526`)
from `.classCTrue`'s tail.  `HlastSeamTailSupply.not_nonempty_of_else405` (`LastArmRows:471`)
remains as the refutation of the old emit form.

`.run`'s supply is a different gap — the tree's last-entry chains are stated at a scan-free
document byte, while the rows' guards name the entry's byte — and `.scalar`'s words are the
callees' staged rows.  No refuting theorem is recorded against a field of this group at
`ee7544f`.

## P0 — the pipeline watermark — repaired, with its regression proved

`Stage2Watermark` (`PipelineDischarge`) quantified `∀ S` **independently of the exit
witness**: `pipelineLoopExit mem args e → ∀ r ∈ stage2ExitRegions S, end(r) ≤ e.next`.
For any admitted `e`, choosing `S.ndst = e.next` put `(S.ndst, 8)` in
`stage2ExitRegions S`, so the premise demanded `e.next + 8 ≤ e.next`.  It was therefore
incompatible with an inhabited exit predicate, and the conditional pipeline result had an
unusable premise on the executions it means to cover — a **false premise at the pipeline
boundary**, where the remaining stage-2 bundles are unproduced but true.

The defect is now a checked statement rather than a paragraph.  `retiredStage2Watermark`
keeps the old form and `retiredStage2Watermark_false` refutes it at any admitted exit,
constructively: the quantifier is free in `S`, so the exit's own record with its refusal
slot moved to the cursor, `S.ndst := e.next`, demands `e.next + 8 ≤ e.next`.

**The repair, landed.**  Both halves the review asked for are in, and the bound is
*carried* rather than assumed:

* the exit predicate is stated in two layers — `pipelineLoopExitAt mem args S s` is the
  whole conjunction at *one* carried record, and `pipelineLoopExit mem args s` is
  `∃ S, pipelineLoopExitAt mem args S s` — so a consumer that must name the record it
  speaks about can.  `Stage2SlotKeeps` is re-indexed to the `At` form; so is the
  watermark;
* the invariant's last conjunct, in both shapes (`pipelineLoopInv`,
  `pipelineLoopInvSplit`), is `∀ r ∈ stage2StagedCaps S, r.1 + r.2 ≤ s.next`.
  `stage2StagedCaps` is the **staged** width list — the document at `n + 32`, the entry
  stream at `4 * (64 * blocks + 9)`, the escape list at `4 * (xn0 + 64 * blocks + 8)`,
  the arena and event capacities, the three slots — because no successor changes a
  capacity, whereas the counts `S.k` and `S.xn` grow every block.  `stage2StagedCaps_doc`
  is the `rfl` that pins the list's literal `32` to `stage2ReadTail`;
* the initial bound comes from staging, which is the only thing that can supply it:
  `pipelineSeed` takes `pipelineStagedBelow` and `seedCarried_caps` turns it into the
  clause at the record the seed builds;
* every step preserves it: no arm binds an `alloca` (`allocaTypes pipelineBody = []`),
  each call through `pipelineCalls` returns the cursor it was given
  (`pipelineCalls_next`), and `stage2StagedCaps_mono` carries the clause from the
  predecessor's cursor to the successor's.

The projection is the repaired watermark, at the exit's own witness:

    theorem stage2Watermark {mem : Mem} {args : List Value} :
        ∀ (S : PipelineLoopCarried) (e : State), pipelineLoopExitAt mem args S e →
          ∀ r ∈ stage2ExitRegions S, r.1 + r.2 ≤ e.next

It reads the invariant's clause at the tail's own list through
`stage2ExitRegions_le_caps`, whose only inputs are the exit's growth facts: `S.k ≤
64 * S.i` (from the stream's length and order), `S.i ≤ pipelineBlocks S.n.toNat` and
`S.xn ≤ S.xn0 + 64 * S.i`.  `stage2Pre_of_exit` still takes its `hwm` at the call's
`next`; the tail discharges it at the exiting cursor and transports it by the UTF-8
call's monotonicity.  `hwm` is gone from `pipelineTailTarget`,
`pipelineBodyFacts_of_exitStage2` and `pipeline_satisfies_at_stage2_of_exitStage2` — the
exit predicate carries the bound, so the tail reads it.

**The one tightening of the input domain.**  The cursor is a number the caller passes,
not an address a memory stores, so no clause of a memory predicate can relate it to the
staged objects.  `Γ_pipeline_units.pre` is therefore

    fun args mem next => pipelineStaging tab base args mem ∧
      pipelineStagedBelow tab base args mem next

and `pipelineSpecPre` carries the same second conjunct: the specification may claim
nothing about a caller the record would not admit.  It excludes no caller's memory —
`exists_stagedBelow` shows every staging is admissible at some cursor (the sum of the
staged ends), and on the advertised route `JsonCallRoute.routeSpecPre` discharges the
clause at the wrapper's own cursor `routeNext` through `routeStagedBelow`.  What it
excludes is a cursor *below* the objects the caller staged, which no execution presents.

The one clause the composite claim still takes at this boundary is `Stage2SlotKeeps`:
`Γ_stage2`'s post cannot state that the run left the caller's two count slots alone,
because the stage-2 ABI does not carry them.  That gap is named, not closed, and it is
the only staging-shape hypothesis the tail takes.

9. **In `∀ x ∈ s, p`, `s` is elaborated with `x` already in scope and its type a
   metavariable**: an occurrence of `x` inside `s` forces `x`'s type to whatever `s`'s
   use implies, and the error names `Membership`, not the statement, so it reads as a
   proof error when the fix is a one-token rename in the *statement*.  Measured at
   `seedInvSplit`'s `hcap`: `∀ q ∈ stage2StagedCaps (seedCarried … (r + 1) …), …` fails
   with `q has type Nat` when the binder is `q` and the list mentions it, and passes
   with a name that does not occur in the list.

## The findings — twenty-seven, and all of one family

*A statement that looks true because an unstated fact is load-bearing.* Each is
recorded where the next reader meets it, not in a report.

| # | Statement | Load-bearing fact not stated |
|---|---|---|
1 | the string pre without the presence clause | the model's memory |
2 | the string pre without the read/write separation | the callee's reads |
3 | a `WalkSegment` through `if.then` | `walkWide`'s field list |
4 | `HlastFacts`' provenance | four fields were invariant-carried, not the input's |
5 | `s2StringBodyBody_contract` at `out.length = 2^64 − 1` | the body's sentinel test; **false** — the pre now excludes it |
6 | `WalkExit`'s `Cend.k = G.nep` | contradicts its own premise; **false** |
7 | `WalkExit`'s arena word | **inert** — both ends discarded it; deleted |
8 | `HcontFacts.hge` | named the count test's *failing* arm under a succeeding hypothesis |
9 | `HcontFacts.hugt` | the last-entry arm at a continuing entry |
10 | `HcontFacts.heicd` | `v.toNat < v.toNat` — the scan is empty on that path |
11 | `WalkLocal` at `land.rhs457.i` | required `i < c`; the scan-free path is reachable; **`ScanEmpty` added** |
12 | `WalkExit`'s uniform verdict | **false** — the three tails return `1`, `0`, `0` |
13 | `ofContinueAndLast`'s rationale | the split does not classify the dispatch (fixed) |
14 | `stage2Boundary_of_parts` at the flush | `herrWalk` is false of that arm; no honest `Stage2Run` |
15 | the potential's byte term | `entryPos` totalises to **0** past the stream; the terminal charge vanished |
16 | `walkPotential_spend`'s `hmono` | **unstatable** at the terminal step; three hypotheses removed |
| 17 | "the whole string contract is absent" (the review) | it was proved an hour later — *reports decay* |
| 23 | `HlastFacts.hugt` against its own scan entry | **contradictory** — `hugt = 0` and the bundle's scan entry (`hlt2T` with `hcdT`/`h4L`/`heiT`) cannot both hold at a last entry, so the bundle was uninhabited there and `WalkLoopEnd.facts` vacuous.  **Repaired (two-sided)**: the head is the `hugt = 1` arm (`evalICmp .ugt (BitVec.ofNat 64 v) ix = 1`, `v` = `%4`'s word, via the whitespace check `land.lhs.true357.i → NodeBlock41 → NodeBlock39 → LeafBlock35`) and the tail is the scan-free segment (`WalkLink.if_then447_i_empty` + `consumerTailSegEmptyAt`: `%ee.1.i` and `%cond350.i` are the same word, so the test is `ult v v`).  `WalkInv` + `stage2MaxDocument` make the bundle's one width premise (`hv63 : v < 2^63`, needed by the gep's sign extension) inhabitable.  Machine-checked: `hlast_toMerge`, `hlastEntry_pc`, `hlastFacts_of_staging`, all `[propext, Classical.choice, Quot.sound]` |
| 22 | the merge's three cells as an unrestricted `∀` over *every* segment | **false, not merely unproduced**: that quantification reaches every segment from a head to `cleanup478.i`, and a segment through the header has `Cd.k = C.k + 1`, so `Cd.k = C.k` fails on a reachable segment.  The producer composes the revolution at named states (`JsonStage2WalkRevolutionSeg`) and produces the three cells **at its own endpoint** from `HcontFacts` plus the head's `%inc.i`/`%nep` cells (`mergeHeadCells`), the two register cells now `WalkInv` clauses and the index equation the endpoint's `blockIndex` |
| 18 | `WalkLink.z_arena_reserve_exit`'s `%xj.i` | **uninhabited**: it stated `G.next0 + 16` where `walkStaticRegs` states `+ 12`, and the string body's `RegionsApart xj 8 outn 8` is false at `+ 16` against `%outn.i = G.next0 + 20`.  **Repaired** — the link now states the staging's `+ 12` |
| 20 | `walkWide`'s stack list | **static where the allocator is monotone**: `stage2AllocaWrites G.next0`'s five slots cover the first allocating call only, and `WalkInv` carries no `s.next`, so the frame is false from a second call onward — the invariant would be uninhabited there, which is why nothing notices |
| 19 | `HstringFacts.hmergeCells` | **uninhabited**: a `∀` over every `WalkInv` state at `cleanup478.i` fixed `%inc208.i` and `%nep`, which the invariant binds nowhere, so the field was false at every other reachable endpoint.  **Repaired** — two fields at the bundle's own endpoint |
| 21 | `Stage2Run.walkFrame` and `stage2Boundary`'s frame conjunct | **was false, one level above 20; repaired.**  Both named `stage2ReportFrame … next`, whose stack part was `stage2AllocaWrites next` — the five bootstrap slots — so a run with a second allocating call wrote at `next + 36`, outside that list, and `Stage2Run.ofInv`'s `walkFrame` could not be inhabited at a loop end whose cursor passed `next0 + 36`.  The contract's stack region is now the interval `[(next, nextEnd - next)]`, `Stage2Run` carries the end with the clause that places the five slots inside it, and the five are the stated consequence `stage2AllocaWrites_reportFrame`.  The carried bound is gone: `Stage2Run.ofInv` takes no `hwin`, `walkFinishMem_base_frame` and the three boundary lemmas take no `hnext`, and `WalkLoopEnd.cursorLe` is deleted |
| 24 | `HcontClassRows.cleanupRow`/`letters`/`c56Else`/`c58Else` | **uninhabited as stated**: each named a `HcontSeamRow` at a literal-`0` edge, and `HcontSeamRow.not_nonempty_zero` (`JsonStage2WalkDispatchClassRowsProduce:223`) proves no such row exists there (`a84c287` recorded it).  **Repaired** (`282ac25`): the four fields are `HcontSeamRefusal` at the same carry, state and literal, their consumers build `HcontArm.badToken` via `hcontArm_badToken_of_row`/`refuseSeg`, and the fields remain supply rather than assumptions |
| 25 | `HlastLettersRows.hTail` and `HlastClassCRows.hTail` | **uninhabited as stated**: a three-call emit tail at `LetS413`/`ClsS413F`/`HeadS413`, which are `if.else405.i`'s literal-`0` seams, and `HlastSeamTailSupply.not_nonempty_of_else405` (`JsonStage2WalkDispatchLastArmRows:471`) refutes every such tail (`5cd238a` recorded it).  **Repaired** (`7167cca`): the two rows carry `HlastSeamRefusal` (`JsonStage2WalkDispatchSeamRow:40`) plus `HlastRefuseRoute` (`:77`), their arm is `LastEntryArm.refuse` (`JsonStage2WalkPremisesOfStaging:512`/`:532`), and the new `HlastClassCTrueRows` (`JsonStage2WalkDispatchLastRows:214`) carries the emit payload for `110`/`116` only |
| 26 | `HcontWsRows.tail`'s `HcontWsTail.calls` | **uninhabited at every parameter**: an emit group with `hcA = 0` at `if.else405.i`, refuted by `hcontSeamCalls_no_literal_zero`; `hcontWsTail_not_nonempty` (`JsonStage2WalkDispatchWsRouteAudit:95`), `hcontWsRows_tail_false` (`:104`) and `hcontArm_ws_of_rows_vacuous` (`:116`) are the compiled consequence at `ef459b4`.  **Resolved by deletion** (`ee7544f`): the group, `HcontWsSeam` and the three ws modules are removed, and the `.ws` cell builds `hcontArm_cleanup_of_class` (`JsonStage2WalkDispatchClassCase:284`) at the class's `refuseSeg` |
| 27 | `HcontWsRows.run`'s missing budget row | **refutable at an admissible carry**: the field's hypotheses omit `v.toNat - ix.toNat ≤ C.inner`, which its conclusion `HcontRunBody.hClass` requires (`JsonStage2WalkRevolution:3759`); at `C.inner = 0` — admissible, because `WalkInv.inner_cap` (`JsonStage2WalkScopeRecord:270`) bounds the budget above and the loop head's `WalkLocal` (`JsonStage2WalkScopeGeom:784`) names no budget — the conclusion asks `v - ix ≤ 0` while `hugt` gives `ix < v`.  **Argued, not compiled**; `ee7544f` removes the field with the group |

**Trend worth keeping**: 4, 5, 6, 8, 9, 10, 12, 18, 19, 20 and 22 were found by a *producer trying
to inhabit a bundle* — and 19 by a *reviewer* asking what inhabits one; 24, 25 and 26 were
found the same way, by a producer or a consumer reaching a seam whose stated group could
not exist, and 27 by reading the producer's own signature against the field's conclusion
(`hinner` had no counterpart in the field).  The two instruments agree, and both are cheap
relative to the proof they check.

**Building a producer is the instrument, not checking the proof** — and a field
that quantifies over states nobody occupies is the failure mode both find.

---

## The measured rules

1. **Name the term** — an abbreviation is not unfolded unless it is in the set.
2. **Stage what a proof rewrites inside** — one stage per rewrite site, or the `Mem`
   association list is walked at every level.
3. **Keep the leaves variable where the consumer unifies structurally**, concrete
   where its lemma carries the word; cross with **one-level** rewrites only.
4. **Unfold one level at a time** — three levels in one `rw` is 200 000 heartbeats;
   three one-level `rw`s are free.
5. **A `rfl` at a state whose memory is a three-deep `writeBytes` nest is a
   deterministic timeout**; the same fact with the memory a variable is instant.
6. `simp only` is a closed set (`le_refl`, implicit inference, rewrite order are
   outside it). Full `simp` on a `Mem` goal **loops**.
7. `set` is unavailable (no Mathlib) — use `generalize h : e = x`.
8. A record update broken across lines inside a term **fails to parse**.

**And the two sentences that outlive the work**:

> **A bundle is green when a producer inhabits it, not when it elaborates.**

> **When a repair cannot be made where it belongs, the first question is what sits
> below what — not who owns the file.**

---

## Process rules this repository now needs

- **A build piped to `tail` exits `0`.** `nix develop -c … lake-locked.sh build | tail`
  reports `tail`'s status, and the failure scrolls past. Capture the status where the
  command runs — `{ lake …; echo "LAKE_EXIT=$?"; } > log 2>&1` — and read the log; a
  red build was mistaken for a green one in this session for exactly this reason.
- **The manifest is the claim.** `LeanLLVM.lean` must import every module whose
  theorems you would cite; a module no target imports is a module whose green means
  nothing. (`WalkCredit`, `WalkFinishPath`, `HeadChainA/C/Scan`, `PrefixCount`,
  `WitnessHlast`, `Revolution`, `RevolutionPrefix`, `ArenaWord`, `ExitProducer`,
  `HcontFactsOfStaging`, `PremisesOfStaging`, `FlushPost`, `DispatchThreeOfRun` are
  all imported.)  The reverse failure is the expensive one: `LastSeamRoute`, `SeamRow`,
  `SlowScan`, `SlowVisits` and `TravOfStaging` were imported by no module until
  `676fe69`, so a red inside them was invisible to every umbrella build — the same gap
  `JsonStage2WalkEntry` had.  A module imported by nothing is invisible to the build.
  The reverse edit is deliberate: `ee7544f` removes the three ws modules from
  `LeanLLVM.lean` because the modules themselves are deleted, so the manifest and the
  tree agree at `ee7544f`.
- **Never `git reset`, `--hard`, `checkout -- .` or `clean`.** One reset in this
  shared checkout destroyed another worker's committed work.
- **Stage only your own hunks**, and derive a file's new content from **`HEAD`**,
  never from the commit you last read — a file rebuilt from an older base silently
  reverts whatever landed since.
- **One file, one owner.** Two workers authorized on one file produced a red tree.
- **A module is a cone; keep it small.** New facts go in the narrowest module that can
  state them, front-ends stay thin, and a lemma moves down to the consumer's level.  The
  cone is the unit of a parallel lane and the cost every later change pays; a doc-only
  edit that costs minutes is a split signal, not a scheduling problem.
- **Killing an agent does not kill its `systemd-run` scope children** — stop them
  with `pgrep -af 'lake build|bin/lean '` and `pkill`, or they compile for hours.
  **Do not kill a `lean` process that is writing an `.olean`**: `.lake` deletes the
  old one first, and a kill there leaves every downstream module failing on a missing
  file (recoverable, but a full rebuild).
