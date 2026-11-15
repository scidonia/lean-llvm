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

### Gap 1 — the two-entry token's bundle — **ten of its fifteen links composed; the frame repair's pin is settled**

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
  because Gap 2 removed the one clause a caller cannot supply; the assembler is
  `s2StringBodyPre_of_staging` (`JsonStage2StringStageFacts`), 37 named hypotheses.
- **the frame is sound only up to the first allocating call** (finding 20).  The
  callee allocates its `%ei` slot at the cursor it is called with, and the model's
  `alloca` always advances (`Semantics`, `.alloca`); `walkWide`'s stack list is the
  fixed five bootstrap slots.  The first call's slot is `G.next0 + 28`, inside them;
  a second call's is `+36`, outside.  So `s2StringBodyFoot ⊆ walkWide` holds only at
  the first call, `WalkInv` carries no `s.next` clause to say which call it is, and
  the frame bridge is `s2StringBodyFoot_frame_walkWide` with that placement as a
  hypothesis.  Until it lands, the two-entry arm is provable per call but not across
  a document with a second allocating call.

  **The repair is settled, and it is one clause plus one definition.**  Design (b):
  the region is the state's cursor, so no `WalkCarry` field is needed.  The pin is
  `stage2BootstrapExtent : Nat := 28` — the end of `entry`'s four `alloca`s
  (`%ei.i` 8, `%root_done.i` 4, `%xj.i` 8, `%outn.i` 8), i.e. the cursor the loop is
  entered at — and the clause is

      next_ge : G.next0 + stage2BootstrapExtent ≤ s.next

  with the frame stated at `walkWideAt G C (s.next - G.next0) :=
  walkPresent G C ++ [(G.next0, s.next - G.next0)]`.

  The **inequality rather than the equality** is what makes the clause uniform: the
  equality `s.next = G.next0 + C.nb` would need `nb` carried in `WalkCarry` *and* a
  second clause `stage2BootstrapExtent ≤ C.nb` beside it — the equality alone gives
  no lower bound, because `WalkCarry` is a plain structure and nothing forbids
  `nb = 0` — and at the two allocating links (`z_arena_reserve_exit`, whose callee
  returns `next + 8`, and `if_then19_i`, `+936`) it needs arithmetic on both sides.
  The inequality needs `hInv.next_ge` at every non-allocating step and one `omega` at
  each allocating one, because every step either leaves `s.next` or advances it.

  **What landing it costs, measured — the site half is cheap and was verified.**
  The clause was landed in `JsonStage2WalkScope` and the module built green at it:
  39 construction sites in ten modules (`Scope` 10, `Store` 6, `Call` 5, `Final` 4,
  `Phi` 3, `Rest` 3, `DispatchWitnessFinish` 3, `Assembly` 2, `Induce` 2,
  `FinishPath` 1), and each takes one line — `next_ge := hInv.next_ge` where the
  target state is built from the site's own `s`, and
  `next_ge := by dsimp only; exact hInv.next_ge` where it is a `let` or a
  `{s with …}` update.  The seed supplies it from `WalkSeedState`, which gains the
  bound as a conjunct of the initialisation's obligation.  That half is a
  half-hour's work and it is *verified*, not estimated.

  **The half that is not cheap is the six helper transfers whose target state is a
  parameter `s₁`.**  `pureCore`, `pureJumpCore`, `pureCoreCarried`, `callQuiet`,
  `callQuietBr` and `callQuietBrPending` build the record at `{s₁ with pc, pre}`, so
  the clause at the target needs a fact about `s₁.next` that the helper does not
  have; each must take `hnext : G.next0 + stage2BootstrapExtent ≤ s₁.next` and every
  call site must pass it.  Measured call sites: `pureCore` 31 in eight modules
  (`Pure` 9, `Rest` 7, `Phi` 5, `Call` 3, `Entry` 2, `Induce` 2, `Scope` 2,
  `Assembly` 1), `pureJumpCore` 19 in seven, `pureCoreCarried` 5 in three,
  `callQuiet`/`callQuietBr` 6 each, `callQuietBrPending` 3 — **70 sites in nine
  modules, four of them inside `Scope`**, i.e. two more 20-minute `Scope`
  elaborations and a full cascade.  At the sites the argument is one line
  (`by simpa [stateAt] using hInv.next_ge` for a pure block, whose `s₁.next` is
  `s.next` definitionally, and `by rw [<the post's `r.next = next`>]; exact
  hInv.next_ge` or `by omega` for the call transfers), so the change is mechanical —
  but it must land *with* the clause in one pass, because a helper that cannot prove
  the clause makes all 70 of its instances red, and the 20-minute `Scope`
  elaboration makes partial passes expensive.

  **Status of the clause, stated where it is not:** `next_ge` is *verified at the
  clause and at `Scope`'s ten sites* — that module built green with it
  (`LAKE_EXIT=0`, one 20-minute elaboration) — and it is **not landed**, because the
  helper half below is a one-pass change and the session could not carry it.  A
  reader must not re-derive that: the statements, both halves' costs, and the
  rejected variant are all here.

  One consequence worth writing down before it is attempted: `pureCore` and its
  siblings are stated at an *arbitrary* `calls : Calls`, so their `s₁.next` cannot be
  bounded from the callee models inside the helper; the bound has to come in as the
  hypothesis above.  A cheaper variant that was considered and rejected: extend
  `walkCarried` with a `no-alloca` conjunct and prove `denoteCode`'s `next` monotone
  — rejected because `evalInstr`'s call case returns an arbitrary `CallOutcome`, so
  monotonicity is a fact about `stage2Calls stage2SubCalls` and not about `calls`,
  and the helpers are polymorphic in it.

  **The record-level consequence is authorised and is a correction, not a
  relaxation** (finding 21): `stage2ReportFrame`'s stack part is
  `stage2AllocaWrites next` — the same five bootstrap slots — so
  `Stage2Run.walkFrame` and the post's frame conjunct in `stage2Boundary` are
  **false** from a second allocating call, not merely unproved.  `Stage2Run.ofInv`
  (`JsonStage2WalkAssembly`) reads the record's frame off `WalkInv.frame`, so the two
  layers move together.

  Two shapes are available for the record level, and the choice is what a consumer
  reads: (i) `Stage2Run` gains the cursor the run left (`nextEnd`) and the post's
  stack region becomes `[(next, nextEnd - next)]`; (ii) the stack region becomes a
  *bound* the record already names, `[(next, stage2BootstrapExtent + nep * 944)]`
  (one `s2_string_body` call or one `num_fast_el1` call per entry, 8 or 936 bytes),
  which needs an invariant clause `s.next ≤ next0 + 28 + C.k * 944` to prove and
  leaves the post's signature alone.  (ii) touches `stage2ReportFrame` and the
  `walkFrame_reportFrame_coverage` lemma; (i) touches `stage2Boundary`'s 25-conjunct
  signature and therefore `JsonStage2WalkTargetPost`'s already-proved boundary and
  the flush path.  The five bootstrap slots must stay re-derivable either way — the
  lemma to state is `stage2AllocaWrites a ⊆ [(a, stage2BootstrapExtent + …)]`, so
  every consumer that read the old list still gets it.

**The eight links the composition has to work at, and each one's obstacle.**  The
other seven are consumed as they stand: `NodeBlock21_at`, `NodeBlock5_at`,
`LeafBlock_at` and `sw_bb202_i_at` need only `%8` (`WalkInv.iter`) and the two
counts, `_at`-shaped and already stating their targets; `if_else334_i` needs the
static carrier and a depth-zero `s2AfterValuePre`; `NodeBlock31_at` and
`LeafBlock29_at` need `%call272.i = y`, which is the call's answer.

| # | link | hypothesis the layer cannot supply | smallest honest fallback |
|---|---|---|---|
| 5 | `if_end207_i` | none — `%4`, `%inc.i`, `hb` and the lane read are the head's fields and the four preceding links write no memory | its target state, now exposed |
| 6 | `if_then219_i` | `hread`, the root slot's four bytes at the *call's* memory: `WalkInv` binds the log's five words and the trace but not `%root_done.i`'s | a `readBytes`-outside-a-write crossing for `if.end207.i`'s cursor-record store (one lemma, ~15 lines, disjointness from `WalkStage.sevenEnd`); `hx` then follows from `s2ValuePos_sound` at `sp = 0`, whose post returns the caller's memory and cursor |
| 7 | `if_end245_i` | none — `s.pre` is the step's, the phi is `if_end245_key_then219`, the operand is an `imm`, `%call222.i` is the previous target's binding | exposed target |
| 8 | `if_end256_i` | none — `hreadA`/`hC` are `log_alen`/`log_acap`, `hcur` is the bundle's, `hiv`/`hnext`/`hpl` its `G6`/`hwin` | exposed target (mechanical: its `s₁` is already an explicit `cells` list) |
| 9 | `z_arena_reserve_exit` | **six**: `hframe`, `howned`, `hlog`, `hev`, `hstTy`, `hstSt` at the callee's returned memory — the `s2StringBodyFoot → walkWide` bridge (a frame bridge, a presence bridge, five log-word crossings, the trace's, and the two stack maps') | **one** named field, stated at the link's own witness: `∀ r, stage2Calls … "s2_string_body" <args> s₉.mem s₉.next = some r → (those six at `r.mem` and the target carry)`.  Producers: `s2StringBodyFoot_frame_walkWide` (`JsonStage2StringStageFacts`) plus the four `walkReadBytes_*` crossings that `walkAfterValue_facts` already has at `s2_after_value`.  This is the field Step 1 retires |
| 10–11 | `NodeBlock31_at`, `LeafBlock29_at` | `%call272.i = y` at their states | the exposed `z_arena_reserve_exit` target plus the bundle's `hy` |
| 12 | `if_then281_i` / `if_else285_i_at` | the branch is on `y = 1`, so **both arms must be cased**; the `if.else285.i` arm's `hale : a + l ≤ C.alen` needs the decoded length to fit the reserved window, which `s2StringBodyPost` deliberately leaves free | a bundle field `l ≤ ext` at the arm, produced by `s2StringBody_outn_le` |
| 13 | `if_end290_i` | none — the two phis are the arm's own state, the two words are `log_len`/`log_cap`, and the branch `evlen + 13 ≤ evcap` is `walkEventReserve_clear` | exposed target |
| 14 | `if_then328_i` | **two**: `readBytes s.mem C.stage.z 8 = some (wordBytes 8 G.ev)` (the log's *base* word — no `WalkInv` clause binds it, and the staging gives presence, not the value) and `C.events.length < C.k` (strict; `events_le` gives `≤`) | two head fields, producers: the adapter's staging for the first, and the "one record per emitting entry" count of `if.then425.i` for the second |

**The residue of the composition: four fields, each with a producer and a
retirement.**  Everything else the fifteen links need is derivable from the head
bundle's fields, `WalkInv`'s clauses, the step's own `pre`, or the exposures above.
These four are what a composed segment must be handed, and each one's producer and
retirement is named rather than left to prose.

| id | field | statement | producer | retires when |
|---|---|---|---|---|
| R1 | `z_arena_reserve_exit`'s witness | `∀ r, stage2Calls stage2SubCalls "s2_string_body" [.ptr C.stage.c, .ptr (G.b + p + 1), .int 64 ext, .ptr (G.dst + A.toNat), .ptr (G.next0 + 20), .ptr G.xp, .ptr (G.next0 + 12), .int 64 G.nxp] s₉.mem s₉.next = some r → UnchangedOutside m0 r.mem (walkWide G C₉) ∧ (∀ q ∈ walkStaged G C₉, HasBytes r.mem q.1 q.2) ∧ (∀ off w, off + w ≤ stage2LogExtent → readBytes r.mem (C.stage.z + off) w = readBytes s₉.mem (C.stage.z + off) w) ∧ (the trace reads across) ∧ (both stack maps at `r.mem`)` | `s2StringBodyFoot_frame_walkWide` (`JsonStage2StringStageFacts`) for the frame and the presence, the four `walkReadBytes_*` crossings `walkAfterValue_facts` already has for the log, the trace and the two maps | the cursor-parameterised frame lands, i.e. the helper half of `next_ge` is landed with it |
| R2 | `houtn_le` | `l ≤ ext` at `if.else285.i`'s state: the decoded length fits the window `if.end256.i` reserved | `s2StringBody_outn_le` (`JsonStage2WalkArenaWord`'s neighbourhood) | a clause on `s2StringBodyPost` relating the decoded length to `len` |
| R3 | `hlogBase` | `readBytes s.mem C.stage.z 8 = some (wordBytes 8 G.ev)`, the log's base word, at the head | the initialisation's store at `%z + 0` — a `WalkSeedState` fact the record does not carry either — **plus** a `WalkInv` clause, because the seed alone does not give the fact at the state that reads it: `%z + 0` lies inside the walk's write extent, so no crossing of the frame reaches it | that clause (a clause addition, so the same 70-site cost `next_ge` measured) |
| R4 | `hltEvents` | `C.events.length < C.k` at the head — strict, where `events_le` gives `≤` | `if.then425.i`'s one-record-per-emitting-entry count | a clause relating the trace's length to the entries consumed |

R3 is *not* a lemma from `WalkInv.frame` and the staging, and the reason is worth
keeping: `%z`'s first eight bytes lie **inside** the walk's write extent
(`walkPresent` carries the whole `(z, stage2LogExtent)` object), so the frame — which
is silence *outside* that extent — says nothing about them, and the staging's
clauses give presence over the object (`WalkInv.owned`) rather than the value it
holds.  The bundle's `The root slot and the log across the cursor-record store`
section records the same negative finding at the place a reader would try to
derive it, and `JsonStage2WalkStringPath` — now a pointer to the lemmas that moved
down into the bundle — repeats it.

`hinc208`/`hnepM` are not in the residue: they are restated at the segment's own
endpoint (`HstringFacts.hmergeCells`, finding 19's shape), because `WalkInv` binds
neither register.

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
reduced to the extent by `walkSub260_eq`.  Link 9 takes `harr`
(`%arrayidx10.i`), `hcreg`, `hxpreg`, `hnxpreg` (`%c.i`, `%xp`, `%nxp`), the
callee's `r` with its call and its answer's word, R1 as one premise (the six
memory clauses), R5 (`hreadAr`) and R6 (`hGdst`).  Link 10 takes R8.  The four
registers are a premise of the composition rather than of the bundle: they are
bound by the header and `entry` and no `WalkInv` clause names them.

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

**Landed and still owed, by residue.**  R1 (as `strPath10`'s `hbodyR`, with the
callee's `r`, its call and its answer's word beside it), R5, R6 and R8 are
parameters of `strPath10`; R2, R3, R4 and R7 are owed by links 11–15, together
with the four uncarried registers (`%arrayidx10.i`, `%c.i`, `%xp`, `%nxp`), which
the table does not list because they are premises of the composition rather than
of the bundle.

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
  place, and ten of the fifteen links are composed** (`strPath5`, `strPath8`,
  `strPath10`). What remains: the write-back links
  (`if.then281.i`/`if.else285.i`, `if.end290.i`, `if.then328.i`/`if.else334.i`)
  with R2/R4/R7 and the `if_then328_i` exposure, the allocator-cursor pin absent
  from `WalkInv`, and the producer of R1's six memory clauses. With those, the
  fifteen links compose and `HstringFacts.seg` stops being supplied.
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

## The findings — twenty, and all of one family

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
| 20 | `walkWide`'s stack list | **static where the allocator is monotone**: `stage2AllocaWrites G.next0`'s five slots cover the first allocating call only, and `WalkInv` carries no `s.next`, so the frame is false from a second call onward — the invariant would be uninhabited there, which is why nothing notices |
| 19 | `HstringFacts.hmergeCells` | **uninhabited**: a `∀` over every `WalkInv` state at `cleanup478.i` fixed `%inc208.i` and `%nep`, which the invariant binds nowhere, so the field was false at every other reachable endpoint.  **Repaired** — two fields at the bundle's own endpoint |
| 21 | `Stage2Run.walkFrame` and `stage2Boundary`'s frame conjunct | **false, one level above 20**: both name `stage2ReportFrame … next`, whose stack part is `stage2AllocaWrites next` — the five bootstrap slots.  A run with a second allocating call writes at `next + 36`, outside that list, so the delivered frame is not a weak claim but an incorrect one, and `Stage2Run.ofInv`'s `walkFrame` cannot be inhabited at a loop end whose cursor passed `next0 + 36`.  The repair restates the contract's stack region at the cursor and keeps the five slots as a stated consequence (Gap 1) |

**Trend worth keeping**: 4, 5, 6, 8, 9, 10, 12, 18, 19 and 20 were found by a *producer trying
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
