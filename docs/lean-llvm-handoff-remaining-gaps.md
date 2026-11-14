# Handoff: the walk's remaining gaps

**Tree at `f3d2164`.** `lake build LeanLLVMTest` green: **967 jobs**, `LeanLLVMTest`
included, no `sorry`/`admit`/`native_decide`, nothing unpushed.  The default target
(`leanllvm`, `ITree`, `LeanLLVMTest`) has not been re-measured since these commits; run
it before quoting a job count for it.

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
**the emitted string body** | `s2StringBodyBody_contract` (`JsonStage2StringBody:6521`), axiom pin passing |
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

- `WalkLink.z_arena_reserve_exit` (`JsonStage2WalkCall:1831`) is **unsatisfiable as
  written**.  Its `hxj` puts `%xj.i` at `G.next0 + 16`; `walkStaticRegs`
  (`JsonStage2WalkScope:1013`) fixes `%xj.i` at `G.next0 + 12`; and at `+ 16` the string
  body's own `RegionsApart xj 8 outn 8` fails against `%outn.i = G.next0 + 20`
  (`16 + 8 > 20`).  No state satisfies `WalkInv` and that hypothesis together, so the
  ninth of the fifteen blocks cannot be linked.  The repair is `+16 → +12` at four sites
  in `JsonStage2WalkCall`, and it belongs in its own change because it re-elaborates the
  walk layer.  The census row at `JsonStage2WalkScope:5662` still calls the link proved.
- the allocator-cursor pin `C.alen ≤ G.ndst0 + ix.toNat` is not a `WalkInv` clause:
  `pending = none` at a loop head, so `if_end256_i`'s `hcur` has no carrier.
- `s2StringBodyPre`'s producer at the call site does not exist yet — now *possible*,
  because Gap 2 removed the one clause a caller cannot supply.

The module's header records exactly this, group by group; the arm reads only the
segment, its endpoint and the two merge cells, and the remaining groups are stated
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
(`JsonStage2WalkPremisesOfStaging:586`).

---

## The review's remaining phases

- **B2** — a standalone string consumed in the walk: **blocked on Gap 1**. Seven
  sub-items are enumerated in `agent://PhaseBScope`'s report (a `s2StringBodyPre`
  producer at the call site, an allocator-cursor pin absent from `WalkInv`, a
  consumer theorem, the string arm's dispatch segment, a two-entry `finish`
  producer, its count, the boundary post).
- **C** — every dispatch branch and its counted scan. **A′ is the first branch**: two
  bundles (`HcontFacts` whitespace, `HcontCleanupFacts` scan-free), a `Sum` at
  `WalkContinueFacts`, the `hRun`/`sl`-as-data refinement, `contWsRun`. **The plan is
  committed in `JsonStage2WalkRevolution`'s header** (`6792f9f`), including the
  finding that `hge`/`hugt`/`heicd` each named a continuation no state reaches.
- **D** — `WalkPremises` from the ABI preconditions; `Stage2WalkObligation` without
  `hpost`.
- **E** — the native route: helper bodies, parser correspondence, artifact binding.
  **Partly outside Lean.**

---

## The findings — eighteen, and all of one family

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
| 18 | `WalkLink.z_arena_reserve_exit`'s `%xj.i` | **uninhabited**: it states `G.next0 + 16` where `walkStaticRegs` states `+ 12`, and the string body's `RegionsApart xj 8 outn 8` is false at `+ 16` against `%outn.i = G.next0 + 20` |

**Trend worth keeping**: 4, 5, 6, 8, 9, 10, 12 and 18 were found by a *producer trying to
inhabit a bundle*. **Building a producer is the instrument, not checking the proof.**

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
3. **The `z_arena_reserve_exit` repair** — `+16 → +12` at four sites in
   `JsonStage2WalkCall.lean` (finding 18). It is the cheapest unblocking move: without it
   the two-entry segment cannot be composed at all, and the census row that calls the
   link proved is wrong until it lands.
4. **Gap 1's remaining sub-items** — the allocator-cursor pin and the `s2StringBodyPre`
   producer at the call site, then the segment's fifteen links (all present) become a
   composition.
5. **Gap 3** — the loop arm's post, which is what removes `hpost` from the top level.
