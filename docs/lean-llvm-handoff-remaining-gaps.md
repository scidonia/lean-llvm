# Handoff: the walk's remaining gaps

**Tree at `a82619f`.** Default target green: **1915 jobs**, `leanllvm` executable,
`ITree` and `LeanLLVMTest` included; no `sorry`/`admit`/`native_decide`; nothing
unpushed.  `LAKE_EXIT=0` captured at the command, not through a pipe.

**Verify before trusting any claim below** — this session's own record is that
*every* statement-level defect was found by something trying to *use* or *supply* a
claim, never by an audit.  Capture the status where the command runs: a build piped to
`tail` reports `tail`'s exit code.

```bash
systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=1G --quiet \
  nix develop -c bash probes/install/lake-locked.sh build
```

A full build is ~4 min warm. **`JsonStage2WalkScope` is the 21 MB module** — a
doc-only edit to it costs a 20-minute rebuild, so batch any edit there.
**`JsonStage2StringBody` is 7k lines with two 12M-heartbeat arms** — a failed proof at
its end costs a full ~10-minute re-elaboration, so edit it in one pass.

---

## What is proved

| Layer | Theorem |
|---|---|
**the walk, loop head → scan latch** | `walkHeadChainToScan` (`JsonStage2WalkHeadChainScan`) |
**the scan** | `walkScanArrival457` (latch → last visit), `scanExitSeg`, `walkScanToMerge` (→ `cleanup478.i`) |
**the finish paths** | `walkFinishPath1`/`2`/`3`, `walkFinishRun`, and `walkFinish_not_frame_of` (why none is a `WalkSegment` at `if.end`) |
**the last entry** | `hlast_toMerge`, `hlast_finish`, `hlast_refuse`; `HlastFacts` **10 of 14 rows produced**, the scan-free arm's fields all read off `%4`'s word, and the bundle inhabited at a real last entry — `hlastPrefixSeg` is 19 links (`hlast_toMerge` 20), so the price is `20 + 2 ≤ 32·1 + 8·0`
**the continue case** | `walkRevolution_seg` — a priced segment to `cleanup478.i` on the count test's *succeeding* arm |
**the dispatch, at its outcomes** | `WalkDispatchResult` + `WalkDispatchThree.ofResult` + `walkLoopStepThree_of_dispatchResult` |
**the flush arm** | `walkFlushAt_of_staging` (the run), `stage2Boundary_of_flush` (the six facts), `stage2Post_of_staging_flush` (the `nep = 0` post) |
**the emitted string body** | `s2StringBodyBody_contract` (`JsonStage2StringBody:6521`), axiom pin passing — and its precondition no longer asks the caller for the body's own slot (Gap 2) |
**the two-entry token** | `HstringFacts` + `stringPath_seg` + `WalkDispatchResult.ofStringMerge` (`JsonStage2WalkDispatchWitnessString`), the arm at `C.k + 2`; `HcontCase` is the class the continuing premise now names. The fifteen-link segment is proved from `HstringResidue`, whose fields name their producers — see Gap 1 |
**the loop's exit, at its memories** | `JsonStage2WalkTargetPost`: the 25 conjuncts of `stage2Boundary` at the returned memory for all three terminal routes, and the accept route's run. The two refusal routes' runs are unwritten |
**the top level** | `stage2WalkObligation_of_staging` — **still takes `hpost`** |
**the credit** | `walkPotential` reads through `boundary`: `32·(nep − k) + 8·(n − boundary k)` |

**Also worth knowing**: `JsonStage2WalkArenaWord` records why `WalkExit`'s arena
premise was *inert* and why it was deleted; `JsonStage2WalkCredit` states the terminal
price and why `entryPos` cannot serve as a price index.

---

## What remains — two gaps, in order

### Gap 1 — the two-entry token's bundle — **closed: the fifteen-link segment is a theorem**

`HstringFacts` and `WalkDispatchResult.ofStringMerge`
(`JsonStage2WalkDispatchWitnessString`) name the standalone string and give it an arm,
and `WalkContinueFacts` (`JsonStage2WalkPremisesOfStaging`) is a *class*:
`HcontCase.ws` (`HcontFacts`) or `HcontCase.twoEntry` (`HstringFacts`).  A standalone
string consumes **opener and closer**, and its merge index is `C.k + 2` via `%inc208.i`
(`WalkLink.if_end207_i`, `JsonStage2WalkStore:1596`).  So at `C.k = 0`, `G.nep = 2` —
where the head's test `0 + 1 < 2` sends the walk into the continuing branch — the branch
is `twoEntry` and it is a premise with a producer target, consumed by
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

**The residue: a `Type` of thirteen fields, one premise at the head.**  Everything the
fifteen links read beside the invariant is the head bundle's, `WalkInv`'s, or a `def`'d
state's cells, except `HstringResidue`
(`JsonStage2WalkDispatchWitnessString`), whose fields each name a producer and a
retirement where they are stated.  `WalkStringResidue G` is its per-state `∀`-form and
the fourth premise of `walkLoopStep_of_staging`, threaded from
`walkPremises_of_staging`, `stage2WalkCompletes_of_staging` and
`stage2WalkObligation_of_staging` (`JsonStage2WalkFlushPost`).

| id | fields | statement | producer | retires when |
|---|---|---|---|---|
| R5 | `hreadAr` | `readBytes … (z + 40) 8 = some (wordBytes 8 G.dst)` | the initialisation's store at `%z + 40` plus a `WalkInv` clause for the arena's base | that clause |
| R6 | `hGdst`, `hGev` | `G.dst < 2^64`, `G.ev < 2^64` | the ABI staging's address width (`stage2Regions`' `HasBytes`); `stage2Pre` states it for `b`, `ep`, `nxp`, `dstcap` and `evcap` only, so these two are the caller's | a `WalkGeom`/staging clause at the two addresses |
| R1's answer | `r`, `hcallR`, `hretR` | the callee's outcome, its call at link 8's memory, its word | `s2StringBodyPre_at_string_call` and `s2StringBody_sound`'s form (= the bundle's `y`) | the string body's staging at this call site |
| R8 | `hR8` | `evalICmp .slt y 1 = 0` | the callee's post: the form is `1` or `2` on the accepting arms | the post stating the form |
| R2 | `l`, `hreadOutn`, `hlext` | the decoded length at `r.mem` and `l ≤ ext` | `s2StringBodyPost`'s `%outn` word and `s2StringBody_outn_le` | a `s2StringBodyPost` clause relating the length to `len` |
| R3 | `hlogBase` | `readBytes r.mem C.stage.z 8 = some (wordBytes 8 G.ev)` | the initialisation's store at `%z + 0` plus a `WalkInv` clause for the log's base | that clause |
| R4 | `hltEvents` | `C.events.length < C.k` (strict) | `if.then425.i`'s one-record-per-emitting-entry count | a clause relating the trace's length to the entries consumed |
| — | `hev63` | `C.evlen < 2^63` | the staging's cursor word (`stage2Pre`'s `%nev`) | a staging clause |

Every field is a helper contract's output or an input fact; none is a register.
The register premises the composition used to take are the carriers' now:
`%c.i`, `%z`, `%xp` and `%nxp` are `walkStaticRegs`' (`WalkInv.regs` reads them at
every state) and `%arrayidx10.i` is `WalkIter.regarr`'s, produced by
`whileBody_step`'s `%3 + %idxprom.i` bind and read at link 8 by
`strArr_of_iter`.  The body's six memory clauses are not fields either: they are
the composition `strPath9` proves.  `hretR` is a field rather than a corollary of
the bundle's `hy`: `hy` is stated at the head's memory and cursor, and the call is
made at the state link 8 leaves, whose memory the reservation's zero has already
written, so the two are not the same proposition.

**R3 is not a lemma from `WalkInv.frame` and the staging**, and the reason is worth
keeping: `%z`'s first eight bytes lie **inside** the walk's write extent (`walkPresent`
carries the whole `(z, stage2LogExtent)` object), so the frame — which is silence
*outside* that extent — says nothing about them, and the staging's clauses give presence
over the object (`WalkInv.owned`) rather than the value it holds.  The bundle's
`The root slot and the log across the cursor-record store` section records the same
negative finding where a reader would try to derive it.

**What Gap 1 leaves open.**  Nothing the composition needs; three items, each with its
producer target named above.

- **The invariant's cursor pin** (finding 20) — still settled and unlanded; the
  measurements below stand unchanged.  The frame is sound only up to the first allocating
  call: the callee allocates its `%ei` slot at the cursor it is called with, the model's
  `alloca` always advances (`Semantics`, `.alloca`), and `walkWide`'s stack list is the
  fixed five bootstrap slots.  The first call's slot is `G.next0 + 28`, inside them; a
  second call's is `+36`, outside.  So `s2StringBodyFoot ⊆ walkWide` holds only at the
  first call, `WalkInv` carries no `s.next` clause to say which call it is, and the frame
  bridge is `s2StringBodyFoot_frame_walkWide` with that placement as a hypothesis.  The
  repair is design (b): `stage2BootstrapExtent : Nat := 28` and the clause
  `next_ge : G.next0 + stage2BootstrapExtent ≤ s.next`, with the frame at
  `walkWideAt G C (s.next - G.next0) := walkPresent G C ++ [(G.next0, s.next - G.next0)]`.
  The inequality rather than the equality is what makes the clause uniform (the equality
  would need `nb` in `WalkCarry` *and* `stage2BootstrapExtent ≤ C.nb` beside it).
  Landing it costs one line at 39 construction sites in ten modules — verified, that
  module built green with it — plus a new hypothesis at the six helper transfers whose
  target state is a parameter `s₁` (`pureCore`, `pureJumpCore`, `pureCoreCarried`,
  `callQuiet`, `callQuietBr`, `callQuietBrPending`) and 70 call sites in nine modules.
  It must land in one pass, because a helper that cannot prove the clause makes all 70 of
  its instances red.
- **The record level is the same finding** (finding 21), and **it is landed** in shape
  (i): `Stage2Run` gains the stack end `nextEnd` — the clause `nextEnd_static` places the
  five bootstrap slots inside the run's region — and the post's stack part is the interval
  `[(next, nextEnd - next)]`.  `stage2Boundary`'s frame conjunct is
  `∃ nextEnd, next ≤ nextEnd ∧ UnchangedOutside mem m (stage2ReportFrame … next nextEnd)`,
  and the five slots are the stated consequence `stage2AllocaWrites_reportFrame`, not a
  second region.  `Stage2Run.ofInv` and `WalkInv.report` pick the end
  `stage2StackEnd next0 s.next`, so no caller carries the old upper bound: the thirteen
  terminal theorems in `JsonStage2WalkTargetPost` lost `hnext`, `WalkLoopEnd` lost
  `cursorLe`, and `walkWide_of_walkWideAt` — the lemma that needed the cursor inside the
  five slots — is deleted.  The pipeline's own post follows: its stack element is the
  interval `[(alloc, allocEnd - alloc)]` with `alloc ≤ allocEnd`, which is what
  `PipelineDischarge` reads off the stage-2 post at the run's own end.
- **The residue's producers**, one row per field, in the table above.

**Findings that still stand, at their links.**

- `WalkLink.z_arena_reserve_exit` (`JsonStage2WalkCall`) **was unsatisfiable as written**
  and is repaired.  Its `hxj` put `%xj.i` at `G.next0 + 16`; `walkStaticRegs`
  (`JsonStage2WalkScope:1013`) fixes `%xj.i` at `G.next0 + 12`; and at `+ 16` the string
  body's own `RegionsApart xj 8 outn 8` fails against `%outn.i = G.next0 + 20`
  (`16 + 8 > 20`).  No state satisfied `WalkInv` and that hypothesis together, so the
  ninth link could not be linked and the census row that calls it *proved* recorded a
  proof of a statement with no inhabitant.  The link states the staging's address, and
  its docstring records why the address is the link's rather than the caller's.
- the allocator-cursor pin `C.alen ≤ G.ndst0 + ix.toNat` is not a `WalkInv` clause:
  `pending = none` at a loop head, so `if_end256_i`'s `hcur` has no carrier; it is the
  bundle's `hcur`, which is exactly the state where `pending` is `none`.
- `s2StringBodyPre`'s producer at the call site does not exist yet — *possible*, because
  Gap 2 removed the one clause a caller cannot supply; the assembler is
  `s2StringBodyPre_of_staging` (`JsonStage2StringStageFacts`), 37 named hypotheses.

### Gap 2 — F3, commit 2 (the string pre's private-slot presence) — **closed**

`s2StringBodyPre` (`JsonStage2Helpers:376`) no longer carries
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

### Gap 3 — the loop arm's `hpost`

B1's post is proved for `nep = 0` (`stage2Post_of_staging_flush`). **The loop arm's
post remains**, so `stage2WalkObligation_of_staging` still takes `hpost`
(`JsonStage2WalkPremisesOfStaging:607`).

**Why it is not a matter of applying what is there.** `stage2Boundary`
(`JsonStage2Contract:1004`, 25 conjuncts) is the post at the *returned* memory, and the
terminal vocabulary names a verdict, not a memory: `WalkTargetRun`
(`JsonStage2WalkLoopStepOutcome:105`) is existential in `m`, and `stage2Run_boundary`
wants the memory to be literally `stage2Report m0 …`.  So the first thing to build is an
output-side strengthening — the terminal run carrying its returned memory — and only
then the boundary.

**The three routes, from the merge and from the copy.**  All at a variable `sd.mem`:

| route | path | writes over `sd.mem` | verdict |
|---|---|---|---|
| R1 accept | `cleanup478.i → if.then485.i → if.end490.i → s2_walk.exit → if.end` | 2 (`%alen` at `%ndst`, `%len` at `%nev`) | `1` |
| R2/R3 refuse | `cleanup478.i → if.then485.i → (if.then488.i \| if.end490.i → if.then492.i) → if.then → if.end` | 4 (`%4` at `%e + 8`, then the record's three) | `0` |
| R0 refuse, already at the copy | `if.then → if.end` | 3 (the record's) | `0` |

The word copied to `%ndst` is the log's arena word `a` with `ndst0 ≤ a ≤ Cd.alen`
(`WalkInv.log_alen`), **not** `Cd.alen`; `%nev` is exactly `Cd.evlen`
(`WalkInv.log_len`).  The rest of the 25 are `WalkInv`'s clauses — `alen_le`,
`evlen_le`, `evlen_eq`, `owned`, `frame`, `depth_reg`, `depth_cap`, `sp_le_wlen` — plus
the geometry's two capacity widths.

**The three facts no clause carries**, each of which can be an argument at the terminal
producer before it is a `WalkInv` clause:

- `%4 = ofNat 64 G.n`.  `%4` is loaded once in `entry` from `%s + 8` (`JsonStage2IR:206`)
  and never rebound, so the fact is *derivable* if `%4` joins `walkStaticRegs`
  (`JsonStage2WalkScope:1013`) — a `∀`-over-list predicate, so the transports are
  unchanged — but that edit is in the 21 MB module.  Until then it is a supplied
  argument on the refusal routes.
- the refusal word at a direct copy entry (R0): `readBytes sd.mem (Cd.stage.e + 8) 8 =
  some (wordBytes 8 Cd.eoff)`.  `WalkLink.refusalStore` (`JsonStage2WalkScope:6147`)
  stores it and sets `eoff`, but its target is existential and `WalkSegment` keeps no
  memory, so the fact does not survive the segment.  `hlast_refuse`'s proof already
  names its target state, so this arm's instance is one `readBytes_writeBytes_len`.
- the merge's root-done word, `readBytes sd.mem (G.next0 + 8) 4 = some …`: it decides
  R1 against R2/R3 at `if.end490.i`, `WalkInv.owned` deliberately omits the four
  `alloca` slots, and `HlastFacts` is at the head rather than the merge.

**The composition.**  `WalkLoopStepThree`'s terminal disjunct (`JsonStage2WalkTraverse:604`)
must carry the boundary, which means a predicate below `Traverse` — it needs only
`stage2Boundary`, so a small module above `WalkScope` is enough.  Then `WalkLoopEnd`'s
`merge`/`refuse` take the outcome's own cells plus the facts above and conclude that
predicate, and `stage2Post_of_staging_loop` mirrors `stage2Post_of_staging_flush`
argument for argument; `stage2WalkObligation_of_staging` loses `hpost`.  The flush
arm's producer donates `stage2Post_of_completion` unchanged and the packing shape of
`stage2Boundary_of_flush`; it does *not* donate `stage2Run_boundary`/
`stage2Boundary_of_parts`, whose `herrWalk`/`frameSlots` are false on these arms for the
reason `JsonStage2WalkFlushPost:38-50` records.

**Non-vacuity, and the coupling.**  The post needs the terminal *block*, which the
outcome already carries — not the `finish`/`refuse` classification — so Gap 3 does not
depend on Gap 1.  After it, the top level still takes `hcont`, `hmerge`, `hend` and the
root-word fact; `hpost` is gone.

**Stale claim left in place, deliberately.**  `JsonStage2WalkScope.lean:2936` still calls the
terminal branch's run `WalkTargetRun` (supplied at the merge by `ExitTail`).  That is no
longer the loop's route; the line is left because the file is reserved for the frame
repair (finding 20), which rewrites its neighbourhood anyway, and a doc-only edit there
costs a full rebuild.  A reader of Scope should trust this document over that line.

**The composition's state.**  Ten links are proved as a `WalkSegment`: `strPath5`
(`NodeBlock21 → if.then219.i`, links 1–5), `strPath8` (`→ if.end256.i`, links 6–8)
and `strPath10` (`→ LeafBlock29`'s state, links 9–10), each pinned at
`[propext, Classical.choice, Quot.sound]`.  The carries `strC₁`–`strC₁₅` are
named, as are the states `strS₁`–`strS₁₀`; `if_end256_i` and
`z_arena_reserve_exit` name their targets (`walkIfEnd256OutAt`,
`walkZArenaReserveExitOutAt`, the second with the callee's `CallOutcome` as a
parameter).  `if_then328_i` is the one target the write-back links still need
exposed.  `if_else334_i` is the one link the census missed: its target is
`callQuiet`'s existential and needs the `walkIfThen447_at` exposure pattern; its
state is `{ stateAt s.env { s with mem := r.mem, next := r.next } with
pc := "cleanup478.i", pre := some s.pc }`.

**What each of links 6–10 takes.**  Links 6–8 take nothing beside the bundle and
the invariant: the two crossings are lemmas now (`walkReadBytes_rootSlot_at`,
`walkReadBytes_log_of_cursorK` — moved *down* into the bundle, beside
`walkCursorRecord_end`, because a module that imports the bundle cannot supply
it); `%idxprom.i` and `%conv211.i` are read out of the states' own environments;
the depth-zero reply is memory-independent (`s2ValuePosCall_ret_at_zero`); and
the arena check clears at `walkArenaReserve_clear`'s arithmetic plus the
`ugt`-at-zero reading (`walkEvalICmp_ugt_ofNat_zero`), with `%sub260.i`'s cell
reduced to the extent by `walkSub260_eq`.  Link 9 takes `harr` (`%arrayidx10.i`,
which the composition reads off `WalkInv.iter.regarr` via `strArr_of_iter`), the
callee's `r` with its call and its answer's word, R5 (`hreadAr`) and R6
(`hGdst`).  Link 10 takes R8.  `%c.i`, `%xp` and `%nxp` are not parameters: they
are `walkStaticRegs`', and `hInv8.regs` reads all three at link 8.  The body's six
memory clauses are not parameters either — `strPath9` proves them from the head
bundle.

**The stop point.**  Link 6's blocker was `walkReadBytes_rootSlot_at`, which
lived in `JsonStage2WalkStringPath` — a module that imports the bundle, so it
could not be used inside it.  The three crossing lemmas moved down into the
bundle (they name only `WalkStage`, `State` and `readBytes`), and
`JsonStage2WalkStringPath` now only pins their footprints.  With them, link 6
needed `hx` transported (at depth zero `s2_value_pos` is memory-independent,
`s2ValuePosCall_ret_at_zero`); link 7 needed only `if_end245_key_then219` and the
`%call222.i` cell; link 8 the cursor-record crossing of the log's `%z + 48` word
and the check's arithmetic; link 9 the parameters above; and link 10 R8.  The
next stop is link 11: the write-back arms (`if.then281.i`/`if.else285.i`) take the
decoded length `l` (R2), and `if_end290.i` takes the log's two words and R7.

**The residue is eight fields, not four** — measured from the links' own statements:

|#|field|why neither `WalkInv` nor the bundle supplies it|
|---|---|---|
|R1|the body's answer at the call site|the call is at link 8's target memory; `hpreS` is head-stated, so a pre transport across the two writes is owed, or the pre at that memory|
|R2|`l ≤ ext` **and** `readBytes r.mem (G.next0+20) 8 = some (wordBytes 8 l)`|`s2StringBody_outn_le` states the read at the model's memory; the crossing needs the pre's `RegionsApart next 8 outn 8`|
|R3|`readBytes s.mem C.stage.z 8 = some (wordBytes 8 G.ev)`|inside the write extent the frame is silent outside of|
|R4|`C.events.length < C.k`|`events_le` gives `≤`|
|R5|`readBytes s.mem (C.stage.z + 40) 8 = some (wordBytes 8 G.dst)`|no clause binds `z+40` (only +8/+16/+32/+48/+56)|
|R6|`G.dst < 2 ^ 64`|`WalkGeom` bounds `dstcap`, never `dst`|
|R7|`C.evlen < 2 ^ 63`|`evlen_le` gives `< 2^64`|
|R8|`evalICmp .slt f.y (ofNat 32 1) = 0`|`NodeBlock31`'s edge; it also yields `form ≠ 0`, which R2's producer needs|

`stringPath_seg` must stay existential in the callee's `r` and the write-back arm's
`l`, since the states after link 9 carry them.

**Landed and still owed, by residue.**  R1's answer (as `strPath10`'s `r`, its
call and its answer's word), R5, R6 and R8 are parameters of `strPath10`; R2, R3,
R4 and `hev63` are owed by links 11–15.  No register is a parameter: `%c.i`,
`%z`, `%xp` and `%nxp` are `walkStaticRegs`' and `%arrayidx10.i` is
`WalkIter.regarr`'s, so `WalkInv.regs`/`WalkInv.iter` read all five at every loop
state.

**What of it has landed.**  `JsonStage2WalkTargetPost` (imported at the end of
`LeanLLVM.lean`) proves the boundary — all 25 conjuncts of `stage2Boundary` — at the
returned memory for each of the three routes, with every memory lemma stated at a
variable `m : Mem`, plus the accept route's terminal run (`walkFinishPost_accept`).  It
takes four supplied facts and names each producer: `%4 = n` (derivable if `%4` joins
`walkStaticNames`), the log's arena word equal to the carry's cursor, the finalisation's
eight carrier registers, and R0's refusal word.  **Still missing**: the terminal runs for
R2/R3 and R0 (`walkFinishPost_refuse`, `_refuse488`, `_copy`) and the pins.  The
divergence that stopped them is an occurs-check on an abstract base memory — a step lemma
stated at a concrete state's memory — not a heartbeat wall; stating the step lemmas at a
memory parameter is the repair.

---

## The review's remaining phases

- **B2** — a standalone string consumed in the walk: **closed**. The bundle, the arm
  and the fifteen-link segment are proved (`strPath5`, `strPath8`, `strPath10`,
  `stringPath_seg`), and `HstringFacts` carries no segment field. What remains is the
  residue's *producers* — one row per field of `HstringResidue` — and the
  allocator-cursor pin, which are Gap 1's last three items.
- **C** — every dispatch branch and its counted scan. **A′ is the first branch**: two
  bundles (`HcontFacts` whitespace, `HcontCleanupFacts` scan-free), the third arm at
  `HcontCase` (`JsonStage2WalkDispatchWitnessString`), the `hRun`/`sl`-as-data
  refinement, `contWsRun`. **The plan is committed in `JsonStage2WalkRevolution`'s
  header** (`6792f9f`), including the finding that `hge`/`hugt`/`heicd` each named a
  continuation no state reaches.
- **D** — `WalkPremises` from the ABI preconditions; `Stage2WalkObligation` without
  `hpost`.
- **E** — the native route: helper bodies, parser correspondence, artifact binding.
  **Partly outside Lean.**

---

## The whitespace skip's run (`contWsRun`): where it stands

`HcontFacts.hRun`/`hnRun` are still supplied.  The definition layer and four of the six
visit segments are proved and kept as an instrument in
`probes/stage2/ws-run-draft.lean` (not imported, not built): `wsByte`/`wsX`/`wsLandS`,
`wsLeafS` (the three leaves as one `def`), `wsStopS`, `scanB_ofNat`, `wsContinue43/46/48`
and `wsVisit43Exit` — the **exit visit is not a wall**, it is the back-edge proof with
`if_pos` on the leaf's test and `pc` moved.

Five measured corrections to the plan:

1. **The count is a bound, not an equality.** `LeafBlock43`'s class costs 4 links per
   continuing byte, `46`/`48` cost 5, so the exact count is `9 + Σ c_p` and `5(k−i)+9` is
   attained only when every byte crosses the second pivot.  The run must state
   `∃ n, n ≤ 5(k−i) + 9 ∧ WalkSegment … n`, which is what `hnRun` consumes.
2. **The source is class-indexed too**: `%35 ∈ {9,10} → NodeBlock41 → LeafBlock33 →
   preheader` (3), `13` and `32` take 4.  Sourcing `hRun` at `contLandS` needs a second
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

Order the evidence supports: (a) `wsVisit46Exit`/`wsVisit48Exit` — mechanical copies of
the 43 case; (b) `wsExit43/46/48`; (c) `wsLatchAt`/`wsStopAt` and the induction; (d) the
entry dispatch with `ScanEntered` and `v − i ≤ C.inner`; (e) the seam at `wsStopS` and
`contWsStop_cond`, then delete `hRun`/`hnRun`/`hcond_sl`/`sl` and rewire the two
consumers.  ~500–700 lines, with (c), (d), (e) and the bundle rewrite the hard parts.


**The last-entry producer, after its second pass.**  Ten of `HlastFacts`' fourteen rows
are produced and the producer's supplied arguments fell 46 → 35.  Two premises of the
plan were wrong and are corrected here:

* the head byte's eight class bits are **not** all `WalkGeom.doc` consequences: six
  follow from two (`hlt125`/`hne125`, which pin the byte), and those two are the
  document's *content* — `WalkGeom.doc` fixes the byte's term, not its value;
* `WalkLoopEnd.facts` cannot yet call the producer: the producer needs
  `C.k < G.nep` as well as the head guard's negation, which is the loop-head predicate
  the review's F5 asks for (`WalkInv.k_le` gives only `≤`).  That is the gap between
  "the bundle is inhabited" and "the step can use it".

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
- **Killing an agent does not kill its `systemd-run` scope children** — stop them
  with `pgrep -af 'lake build|bin/lean '` and `pkill`, or they compile for hours.
  **Do not kill a `lean` process that is writing an `.olean`**: `.lake` deletes the
  old one first, and a kill there leaves every downstream module failing on a missing
  file (recoverable, but a 20-minute rebuild).

---

## How to resume

1. `git status` — anything uncommitted is a partial; `git checkout HEAD -- <path>`
   recovers it.
2. Full build (above). **If `Scope.olean` is missing, build
   `LeanLLVM.Refinement.JsonStage2WalkScope` first** — everything below it fails on
   "No such file or directory" and the message does not say why.
3. **Gap 1's remaining sub-items**: the residue's producers (one row per field of
   `HstringResidue`, in the module header's table) and the
   allocator-cursor pin — the last with the 70-site cost the header measures.  The
   register carriers are landed: `%c.i`, `%z`, `%xp` and `%nxp` are
   `walkStaticRegs`' and `%arrayidx10.i` is `WalkIter.regarr`'s, so no register is
   a residue field.  The
   segment itself is no longer among them: `stringPath_seg` is a theorem.
4. **Gap 3's two refusal terminal runs** (`walkFinishPost_refuse`, `_refuse488`,
   `_copy`) and the composition through `WalkLoopStepThree`, which is what removes
   `hpost` from the top level.  The boundary itself — all 25 conjuncts at the three
   returned memories — is proved (`JsonStage2WalkTargetPost`).
