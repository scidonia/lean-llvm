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
**the last entry** | `hlast_toMerge`, `hlast_finish`, `hlast_refuse`; `HlastFacts` **8 of 16 groups produced**, every other row naming why it cannot be |
**the continue case** | `walkRevolution_seg` — a priced segment to `cleanup478.i` on the count test's *succeeding* arm |
**the dispatch, at its outcomes** | `WalkDispatchResult` + `WalkDispatchThree.ofResult` + `walkLoopStepThree_of_dispatchResult` |
**the flush arm** | `walkFlushAt_of_staging` (the run), `stage2Boundary_of_flush` (the six facts), `stage2Post_of_staging_flush` (the `nep = 0` post) |
**the emitted string body** | `s2StringBodyBody_contract` (`JsonStage2StringBody:6521`), axiom pin passing — and its precondition no longer asks the caller for the body's own slot (Gap 2) |
**the two-entry token** | `HstringFacts` + `WalkDispatchResult.ofStringMerge` (`JsonStage2WalkDispatchWitnessString`), the arm at `C.k + 2`; `HcontCase` is the class the continuing premise now names. Its segment is supplied — see Gap 1 |
**the loop's exit, at its memories** | `JsonStage2WalkTargetPost`: the 25 conjuncts of `stage2Boundary` at the returned memory for all three terminal routes, and the accept route's run. The two refusal routes' runs are unwritten |
**the top level** | `stage2WalkObligation_of_staging` — **still takes `hpost`** |
**the credit** | `walkPotential` reads through `boundary`: `32·(nep − k) + 8·(n − boundary k)` |

**Also worth knowing**: `JsonStage2WalkArenaWord` records why `WalkExit`'s arena
premise was *inert* and why it was deleted; `JsonStage2WalkCredit` states the terminal
price and why `entryPos` cannot serve as a price index.

---

## What remains — two gaps, in order

### Gap 1 — the two-entry token's bundle — **stated, its segment supplied**

`HstringFacts` and `WalkDispatchResult.ofStringMerge`
(`JsonStage2WalkDispatchWitnessString`) name the standalone string and give it an arm,
and `WalkContinueFacts` (`JsonStage2WalkPremisesOfStaging`) is now a *class*:
`HcontCase.ws` (`HcontFacts`) or `HcontCase.twoEntry` (`HstringFacts`).  A standalone
string consumes **opener and closer**, and its merge index is `C.k + 2` via `%inc208.i`
(`WalkLink.if_end207_i`, `JsonStage2WalkStore:1596`).  So at `C.k = 0`, `G.nep = 2` —
where the head's test `0 + 1 < 2` sends the walk into the continuing branch — the branch
is `twoEntry` and no longer vacuous: it is a premise with a producer target, and the arm
that consumes it is `WalkDispatchResult.ofStringMerge` (footprint
`[propext, Quot.sound]`).

**What the arm owes, and the finding that stops the composition.**

- `WalkLink.z_arena_reserve_exit` (`JsonStage2WalkCall:1839`) **was unsatisfiable as
  written** and is repaired.  Its `hxj` put `%xj.i` at `G.next0 + 16`; `walkStaticRegs`
  (`JsonStage2WalkScope:1013`) fixes `%xj.i` at `G.next0 + 12`; and at `+ 16` the string
  body's own `RegionsApart xj 8 outn 8` fails against `%outn.i = G.next0 + 20`
  (`16 + 8 > 20`).  No state satisfied `WalkInv` and that hypothesis together, so the
  ninth of the fifteen blocks could not be linked and the census row that calls it
  *proved* recorded a proof of a statement with no inhabitant.  The link now states the
  staging's address, and its docstring records why the address is part of the link
  rather than the caller's.
- the allocator-cursor pin `C.alen ≤ G.ndst0 + ix.toNat` is not a `WalkInv` clause:
  `pending = none` at a loop head, so `if_end256_i`'s `hcur` has no carrier.
- `s2StringBodyPre`'s producer at the call site does not exist yet — now *possible*,
  because Gap 2 removed the one clause a caller cannot supply.

The module's header records exactly this, group by group; the arm reads the segment, its
endpoint's block, index and predecessor, its two endpoint cells and G2's count test, and
the remaining groups are stated
because they are what the producer must target.

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

- **B2** — a standalone string consumed in the walk: **the bundle and the arm are in
  place; the segment is not.** What it owes now, in order: the `z_arena_reserve_exit`
  `%xj.i` repair (finding 18), an allocator-cursor pin absent from `WalkInv`, and the
  `s2StringBodyPre` producer at the call site — now possible, because the pre no longer
  asks a caller for the body's own slot. With those, the fifteen links compose and
  `HstringFacts.seg` stops being supplied.
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

## The findings — nineteen, and all of one family

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
| 18 | `WalkLink.z_arena_reserve_exit`'s `%xj.i` | **uninhabited**: it stated `G.next0 + 16` where `walkStaticRegs` states `+ 12`, and the string body's `RegionsApart xj 8 outn 8` is false at `+ 16` against `%outn.i = G.next0 + 20`.  **Repaired** — the link now states the staging's `+ 12` |
| 19 | `HstringFacts.hmergeCells` | **uninhabited**: a `∀` over every `WalkInv` state at `cleanup478.i` fixed `%inc208.i` and `%nep`, which the invariant binds nowhere, so the field was false at every other reachable endpoint.  **Repaired** — two fields at the bundle's own endpoint |

**Trend worth keeping**: 4, 5, 6, 8, 9, 10, 12, 18 and 19 were found by a *producer trying
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
3. **Gap 1's remaining sub-items**, in the order the module header gives them: the
   register carriers `walkStaticRegs` omits (`%c.i`, `%xp`, `%nxp`, `%arrayidx10.i`), the
   two frame lemmas that would carry `s2StringBodyFoot` to `walkWide`, the
   allocator-cursor pin, and the `s2StringBodyPre` producer at the call site.  With those
   the fifteen links (all present) become a composition and `HstringFacts.seg` stops being
   a field.  The `%xj.i` repair (finding 18) is done; it was never the whole blocker.
4. **Gap 3's two refusal terminal runs** (`walkFinishPost_refuse`, `_refuse488`,
   `_copy`) and the composition through `WalkLoopStepThree`, which is what removes
   `hpost` from the top level.  The boundary itself — all 25 conjuncts at the three
   returned memories — is proved (`JsonStage2WalkTargetPost`).
