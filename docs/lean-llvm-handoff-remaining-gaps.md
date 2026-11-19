# Handoff: the walk's remaining gaps

**Tree at `0dc2fff`.**  The last default-target green recorded in this document is the
**1915-job** build at `a82619f`, with `leanllvm`, `ITree` and `LeanLLVMTest` included and
no `sorry`/`admit`/`native_decide`.  `LAKE_EXIT=0` was captured at the command, not
through a pipe.  One hundred and ninety-one commits have landed since, including the two
module splits noted below; the status in this file is read off the declarations at
`0dc2fff`, and a green is not inherited across those commits.

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
`JsonStage2WalkScopeGeom` (`:917`/`:897`), and `JsonStage2WalkScopeClassAB` is the largest
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
**the last entry** | `hlast_toMerge`, `hlast_finish`, `hlast_refuse` (`JsonStage2WalkDispatchWitnessHlast:366`/`:405`/`:436`); the last entry's arm is produced from the three last-level groups by `walkLoopEnd_of_payload` (`JsonStage2WalkPremisesOfStaging:450`), and those groups are the remaining last-level supply (see the frontier below); `hlastPrefixSeg` is 19 links (`hlast_toMerge` 20), so the price is `20 + 2 ≤ 32·1 + 8·0` |
**the continue case** | `walkRevolutionMergeSeg`/`walkRevolutionMergeSegWs` (`JsonStage2WalkRevolutionSeg:618`/`:788`) — the scan-free and whitespace arms' priced segments to `cleanup478.i`, with the merge's three cells at the endpoint.  `walkRevolution_seg` is retired rather than kept: its premise named the scan-free bundle at a state whose path is the run's |
**the dispatch, at its outcomes** | `WalkDispatchResult` + `WalkDispatchThree.ofResult` + `walkLoopStepThree_of_dispatchResult` |
**the flush arm** | `walkFlushAt_of_staging` (the run), `stage2Boundary_of_flush` (the six facts), `stage2Post_of_staging_flush` (the `nep = 0` post) |
**the emitted string body** | `s2StringBodyBody_contract` (`JsonStage2StringBodyDecoded:376`), axiom pin passing — and its precondition no longer asks the caller for the body's own slot (Gap 2) |
**the two-entry token** | `HstringFacts` + `stringPath_seg` + `WalkDispatchResult.ofStringMerge` (`JsonStage2WalkDispatchWitnessString`), the arm at `C.k + 2`; `HcontCase` is the class the continuing premise now names. The fifteen-link segment is proved, and `HstringResidue` (`:1945`) is a field-less `Prop`: `WalkStringResidue` is not a premise — see Gap 1 |
**the whitespace skip's run** | `wsRun` (`JsonStage2WalkRevolution:1646`) with `wsRun_go` (`:1541`) and `contWsRunF` (`:3869`) — the run, its stop and its price derived, and `HcontFacts` carries no run field |
**the loop's exit, at its memories** | `JsonStage2WalkTargetPost`: the 25 conjuncts of `stage2Boundary` at the returned memory for all three terminal routes — `walkFinishPost_accept` (`:985`), `walkFinishPost_refuse` (`:1255`), `walkFinishPost_refuse488` (`:1446`), `walkFinishPost_copy` (`:1605`), composed by `walkFinishPost_merge` (`:1723`) and `walkFinishPost_refuseOfWords` (`:1765`) — and `WalkTargetPost` (`JsonStage2WalkTraverse:672`), the terminal predicate the loop's step carries |
**the top level** | `stage2WalkObligation_of_staging` (`JsonStage2WalkFlushPost:934`) — exactly six payload groups (`hcont`, `hrows`, `hws`, `hlast`, `hlastRows`, `hlastArms`, `:935-940`) and **no `hpost`**; the loop arm's post is `stage2Post_of_staging_loop` (`JsonStage2WalkPremisesOfStaging:1089`) |
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
(`JsonStage2WalkDispatchStringOfStaging:181`) and consumed by
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
(`JsonStage2WalkDispatchWitnessString:1945`) carries no fields at all, and
`WalkStringResidue` (`:1950`) is not a premise of the loop's step.  The thirteen fields it
had at its first statement are all produced by the layers below; the last two are
`WalkInv` clauses:

| id | field | became |
|---|---|---|
| R5 | arena-base word (`z + 40`) | `WalkInv.log_dst` (`JsonStage2WalkScopeRecord:382`) |
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
  (`JsonStage2WalkScopeGeom:917`) fixes `%xj.i` at `G.next0 + 12`; and at `+ 16` the
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
(`JsonStage2WalkPremisesOfStaging:1089`), built at `WalkLoopStepThree`'s terminal
disjunct (`JsonStage2WalkTraverse:698`), whose existential run carries
`Stage2BoundaryAt` at the memory it returns.  The terminal runs are theorems:
`walkFinishPost_accept` (`JsonStage2WalkTargetPost:985`), `walkFinishPost_refuse`
(`:1255`), `walkFinishPost_refuse488` (`:1446`) and `walkFinishPost_copy` (`:1605`),
composed by `walkFinishPost_merge` (`:1723`) and `walkFinishPost_refuseOfWords`
(`:1765`) into `WalkTargetPost` (`JsonStage2WalkTraverse:672`).  Consequently
`stage2WalkObligation_of_staging` (`JsonStage2WalkFlushPost:934`) takes the six payload
groups and **no `hpost`** (`:935-940`); `stage2WalkObligation_of_premises`
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
(`JsonStage2Contract:1135`) are `WalkInv`'s clauses — `alen_le`, `evlen_le`, `evlen_eq`,
`owned`, `frame`, `depth_reg`, `depth_cap`, `sp_le_wlen` — plus the geometry's two
capacity widths.

**Where the facts the routes needed now live.**  `%4`'s word is the static carrier's:
`%4` is an entry of `walkStaticRegs` (`JsonStage2WalkScopeGeom:935`), read by
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
counterpart at `0dc2fff`: `JsonStage2WalkScope` is a 315-line import front-end (see the
header), and the terminal vocabulary is `WalkTargetPost` (`JsonStage2WalkTraverse:672`).
The per-link evidence for the string path is recorded in
`JsonStage2WalkDispatchWitnessString`'s header (the fifteen links and the residue
retirement table); no register is a parameter, since `%c.i`, `%z`, `%xp` and `%nxp` are
`walkStaticRegs`' and `%arrayidx10.i` is `WalkIter.regarr`'s, so `WalkInv.regs` and
`WalkInv.iter` read all five at every loop state.

---

## What remains — six payload groups, and the seam first

`stage2WalkObligation_of_staging` (`JsonStage2WalkFlushPost:934`) is the remaining
supply in full: six groups, none of which has a `∀ G` producer (`:935-940`).
`pipeline_satisfies_at_stage2_of_exitStage2` (`PipelineDischarge:2859`) forwards the same
six (`:2860-2865`), so the pipeline's statement inherits this list unchanged.

| group | declaration | state |
|---|---|---|
| `HcontPayload` | `JsonStage2WalkDispatchSupply:839` | produced only at `G.nep = 0` by `hcontPayload_of_nep_zero` (`:1146`) |
| `HcontClassRows` | `JsonStage2WalkDispatchClassRows:633` | unproduced; carries the seam (`seam : HcontSeamAbi`, `:727`) |
| `HcontWsRows` | `JsonStage2WalkDispatchWsRows:205` | unproduced |
| `HlastPayload` | `JsonStage2WalkDispatchSupply:1008` | unproduced |
| `HlastClassRows` | `JsonStage2WalkDispatchClassRows:759` | unproduced; carries the last seam (`:765`) |
| `HlastArmRows` | `JsonStage2WalkDispatchLastRows:236` | unproduced |

Everything between those groups and the obligation is produced: `walkPremises_of_staging`
(`JsonStage2WalkPremisesOfStaging:901`) reads the six and returns `WalkPremises`;
`walkContinueFacts_of_payload` (`JsonStage2WalkDispatchContinuing:217`) and
`walkLoopEnd_of_payload` (`JsonStage2WalkPremisesOfStaging:450`) build the two bundles
from them; `stage2Post_of_staging_flush` (`JsonStage2WalkFlushPost`) and
`stage2Post_of_staging_loop` (`JsonStage2WalkPremisesOfStaging:1089`) build the post.
The per-class rows inside `HcontClassRows` are where the work is, and the layer derives
the ones it can (`hcontClassRows_cleanup_of_payload`, `…ClassRows`).

### The next target: the seam's three calls

`HcontSeamCalls` (`JsonStage2WalkDispatchSeams:100`) is the three-call group: `r₁` with
`hpre₁`/`hcall₁`/`hret₁` (`s2_value_pos`), `r₂` with `hpre₂`/`hcall₂`/`hret₂`
(`od_scalar_value`), and `r₃` with `hpre₃`/`hcall₃` (`s2_after_value`), all at the seam's
one memory.  `HcontSeamAbi` (`:209`) bundles the seam per leaf — `scan`, `scanF`,
`scan56True`, `scan58True` and `last` — and is read as `HcontClassRows.seam`
(`JsonStage2WalkDispatchClassRows:727`); the last level states the same three calls
through `HlastClassRows.seam` (`:765`), at `hlastTail`.
`JsonStage2WalkDispatchResidual:143-151` identifies the seam's call chain as the widest
of the remaining obligations, and what it names is not a missing input: at each call
memory a producer owes the answer from `answers`, the postcondition from `sound`, the
frame from `framed`, and the next call's precondition at the memory the previous one
left.  The precedent is `s2StringBodyPre_at_string_call`
(`JsonStage2StringStageFacts:1236`), which does exactly that chain once for
`s2_string_body`; `s2AfterValuePre_of_inv` (`JsonStage2WalkDispatchResidual:192`) is the
shape that discharges the after-value call's stack-byte precondition out of
`WalkInv.tyBytes`/`stBytes`.

### Phase verdicts

- **C — landed.**  The continuing branch census is exhaustive (`HcontClass.complete`,
  `JsonStage2WalkDispatchHcontArms:299`) and the class case consumes it in
  `walkContinueFacts_of_payload` (`JsonStage2WalkDispatchContinuing:217`); the last
  entry's switch is the bit case in `walkLoopEnd_of_payload`
  (`JsonStage2WalkPremisesOfStaging:450`), over `LastEntryArm`'s constructors.  The
  counted scan is `wsRun` (`JsonStage2WalkRevolution:1646`) with `wsRun_go` (`:1541`),
  composed into the entry, first visit, seam and price by `contWsRunF` (`:3869`).  What
  the phase leaves is the per-class rows — the six groups, and the seam first.
- **D — half landed.**  `hpost` is retired from `stage2WalkObligation_of_staging`
  (`:934`); `WalkPremises` is not yet derived from the ABI preconditions.
  `walkPremises_of_staging` (`JsonStage2WalkPremisesOfStaging:901`) still takes the six
  groups, so the six above are the whole distance between the staging and the ABI.
- **E — open, and partly outside Lean.**  The native route lacks the semantics-to-object
  step: `missingBridgePieces` (`JsonCallRoute:1478-1500`) names it beside the in-`lake`
  adapter, the staging copy, the link step and the table initialisation, and nothing
  connects a run of the linked object to `pipelineUnitsPost`.

---

## The whitespace skip's run (`contWsRun`) — landed

`wsRun` (`JsonStage2WalkRevolution:1646`) and its induction helper `wsRun_go` (`:1541`)
prove the skip from the latch to its stop; `contWsRunF` (`:3869`) composes the entry
dispatch, the first visit, the run, the seam and the price as one existential segment.
`HcontFacts` (`:2223`) carries no run field — the class is `hClass` and the run is
derived — so the bundle is 59 fields rather than 64, and `hRun`, `hnRun`, `hcond_sl`,
`sl`, `b8` and the count `n` are retired.  The definition layer and the visit segments
remain in `probes/stage2/ws-run-draft.lean` (not imported, not built) as the instrument:
`wsByte`/`wsX`/`wsLandS`, `wsLeafS` (the three leaves as one `def`), `wsStopS`,
`scanB_ofNat`, `wsContinue43/46/48` and `wsVisit43Exit` — the **exit visit is not a
wall**, it is the back-edge proof with `if_pos` on the leaf's test and `pc` moved.

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


**The last entry's arm.**  `WalkLoopEnd` (`JsonStage2WalkPremisesOfStaging:317`) carries
one field, `hlast : LastEntryArm`, and `walkLoopEnd_of_payload` (`:450`) builds it from
`HlastPayload`, `HlastClassRows` and `HlastArmRows`; the merge's two log words are
`WalkInv.log_alen`'s witness (`walkMergeWords_of_inv`, `walkRefuseWords_of_inv`), not
fields.  `HlastFacts` (`JsonStage2WalkDispatchWitnessHlast:205`) is the input's facts at
the last entry.  The second pass's two corrections stand: the head byte's eight class
bits are **not** all `WalkGeom.doc` consequences — six follow from two
(`hlt125`/`hne125`, which pin the byte), and those two are the document's *content*;
and the head's guard is read off the block-local clause by `WalkInv.head_lt`
(`JsonStage2WalkScopeRecord:453`), so `C.k < G.nep` is a consequence at the loop head
rather than a supply.

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

## The findings — twenty-three, and all of one family

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

**Trend worth keeping**: 4, 5, 6, 8, 9, 10, 12, 18, 19, 20 and 22 were found by a *producer trying
to inhabit a bundle* — and 19 by a *reviewer* asking what inhabits one; the two
instruments agree, and both are cheap relative to the proof they check.

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
  all imported.)
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
