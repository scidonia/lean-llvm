/-
The stage-2 walk's loop invariants, its measure, and its six back edges.

`Stage2WalkObligation` (`JsonStage2Body`) is `Satisfies` for the pinned 165-block
body, and its first conjunct is completion at `stage2Budget`
(`stage2WalkObligation_iff_completion`).  `runFuel` is fuel-indexed, so the proof
that resists is the loop: an invariant preserved by every arm, and a measure that
decreases on every iteration.  This module scopes that proof.  It discharges the
literal comparison's arm at the edge itself (the four scans' visits, the measure's
other four decreasing edges, are the guard-free rounds of
`JsonStage2WalkRevolutionScanRound`); the entry loop's edge (the merge at `cleanup478.i`, its two
`phi`s, the exit test, and the inner budget's refill), which preserves the invariant and
hands the decrease to the header's block (`walkMeasure_step`); and it states the
entry loop's first obligation.  It does not claim the obligation.

## What the loop carries

The walk is the outer entry loop `while.body.i`, with five inner loops.  Its state
is not a function of the report `Stage2Run` records, and the reason is recorded at
`Stage2Run`'s definition: the arena cursor is the *sum* of the extents the walk
decoded into it, and a sum of `Nat`s does not name its summands.  A record that
carried `alen` alone could not say what the walk had written, so the loop carries
the summands themselves:

* `spans : List (Nat × Nat)` — the decoded bodies' document extents, in document
  order.  The invariant states `alen ≤ ndst0 + spans.map (·.2) |>.sum` plus the
  two shape clauses, which is exactly the predicate `Stage2SpansInside` and
  exactly what `arenaLe_of_spans` consumes to give `alen ≤ ndst0 + n`.  The
  report keeps the bound, not the list;
* `events : List EventRecord` — the event records emitted, in order, at the widths
  their emitters write: one byte for a container marker or a literal, nine for a
  number (tag and binary64 payload), thirteen for a key or string (tag, length and
  span).  The cursor is the sum of the widths, `evlen = nev0 + sum
  (events.map encodedSize)`, which is the body's own arithmetic, and
  `events.length ≤ k` is the one-record-per-entry count
  `Stage2OneRecordPerEntry` needs.  `evBytes` says the bytes the trace names are
  the ones at the log's stream, so the carry is about what the body wrote.  A
  count times a constant was the defect this replaces: the encoding is
  variable-width, and a root `true` leaves the cursor one byte past its start;
* `k : Nat` — the block index into the entry stream, at the phi the loop reads
  (`%k.0.i249`);
* `alen` and `evlen` — the two cursors;
* `pending : Option (Nat × Nat × Nat)` — the record in flight: the entry
  position, the arena offset reserved for its decoded body, and that body's
  document extent, `none` between records.  The extent is carried because it is
  the number `z_arena_reserve`'s check is about: with it the arena trap's
  exclusion is a theorem of the invariant (`walkArenaReserve_clear`), with it
  absent the exclusion needed a hypothesis beside the record;
* `refusal : Bool` and `eoff : Nat` — the refusal bit and the offset it stores,
  the two clauses nothing in `Stage2Run`'s vocabulary names at the refusal arm;
* `block : String` — the block the run is at;
* `inner : Nat` — the remaining inner work at the block, the measure's second
  component;
* `sp : Nat` — the nesting depth, the index the two container stacks are written
  at and the value `%sp.i.0248` holds at the loop head;
* `stage : WalkStage G` — the adapter's staging of the walk's own objects
  (`%c.i`, `%ctype.i`, `%cst.i`, `%t352.i`, `%s`, `%z`, `%e`) and the caller's two
  count slots, with the presence and separation `stage2StagedPre` states.  It is
  fixed for the run, so it rides the carry rather than becoming a second index;
  the log's four fields are read at its `%z`.

The invariant also carries the log's four fields the reserves read —
`log_len` at `%z + 8` is `evlen`, `log_cap` at `%z + 16` is `evcap`, `log_alen`
at `%z + 48` is at most `alen`, and `log_acap` at `%z + 56` is `dstcap` — so
`if.end256.i`'s comparison of `alen + len + 64` against the word at `%z + 56` is
about the carried cursor and the staged capacity rather than an unread cell.  The
seed takes the four as `WalkSeedState` hypotheses (the initialisation's stores),
and every proved arm carries them through unchanged memory.

`WalkGeom` is `stage2Pre`'s staging, named field for field.  A geometry is not
assumed: `WalkGeom.nonempty` unpacks any `Γ_stage2.pre` into one, so the invariant
is not vacuous at a caller the record admits.

The memory half is two claims at two region lists.  `WalkInv.owned` is presence
over `walkStaged` — the extents the caller staged — and `WalkInv.frame` is silence
outside `walkWide`, the extents the run may write: the two cursors at their
carried values, the seven appended objects, `%d.i`'s slot, and the body's four
stack objects at `G.next0`.  The loop's first store (`%c.i + 32`), the nesting
arm's two stack writes and every helper's store through an `alloca` land inside
`walkWide` rather than contradicting it.  The split is forced: presence over the
four stack bytes is false at the loop head, and silence over the seven alone is
contradicted by the helpers.  The report's clauses at `alen + 64` are
`Stage2Run.walkPresent_of_written` and `Stage2Run.walkFrame_of_written`: the
arena's staged capacity supplies the reserve window's bytes and the watermark
places the four stack objects above every staged object.

The seven are the body's own objects: `%c.i`, `%ctype.i`, `%cst.i`, `%t352.i`,
`%s`, `%z`, `%e`, at the extents its `llvm.lifetime.start`s allocate
(`stage2StagedWrites`, guarded by `JsonStage2IR`'s `lifetimeExtents`), and
`WalkStage` carries the adapter's staging of them — presence and the
seventeen-object separation — for the run.  So the frame is not a widening chosen
here: it is the region the body writes, and the record's post names it
(`stage2Boundary`).

## The measure

The measure is a `Nat`, not a pair:

    walkMeasure G C = (G.nep - C.k) * (walkInnerCap G + 1) + C.inner
    walkInnerCap G  = 4 * G.n + 5

The pair is `(remaining entries, remaining inner budget)`, encoded lexicographically
with the budget's bound as the radix.  The inner component is a *shared* budget:
one iteration's worth of inner work, drawn on by every scan it runs, and refilled
at the loop head (`walkSeed G`, `walkBack_step`).  It has to be shared rather than
per-scan, because a scan's entry edge sets the component for the new scan, and a
later scan in the same iteration can have more remaining work than the earlier one
left; with the component read as one scan's remaining work the measure would rise
at every entry.  Read as a budget the entry edge sets nothing — it checks that the
remaining budget still covers the scan it enters, and `WalkLink.mono` holds by
equality — while each scan step spends one unit and the refill is paid for by the
outer factor.

`4 * n + 5` is that budget's value, and it is the conservative one: the four scans
`land.rhs.i`, `land.rhs.i103`, `land.rhs71.i` and `land.rhs457.i` each walk at
most the document — `n` bytes — and the literal comparison `for.body.i.i` is
bounded by `min (ee - idx) ln` with `ln` four or five at `if.end48.i`'s phi.  A
scan's bound register is one of two words: `%cond350.i` is either `%4` — the word
`entry` loads from the state's own slot at offset 8 — or `%conv347.i`, a `zext` of
a 32-bit lane of the entry stream read at `%inc.i`; `%cond.i` is either `%4` or
`%conv.i`, the same lane read.  A lane is an entry position, and every entry
position is below `n` (`WalkGeom.inside`), while `nep ≤ n` (`WalkGeom.nep_le`) is
what puts the lane's index inside the stream.  So each scan's remaining work `c - i`
has `c ≤ n`, and the sum over the iteration is at most `4 * n` plus the literal's
five.  The cap is a completion witness and not a tight bound: nothing here needs
the sum's true value, only that a budget of this size exists.

The bound is a field of the invariant, `WalkInv.inner_cap`, and every arm that
moves the inner component re-establishes it: the scan and literal arms lower it,
and the seed and the back edge set it to the cap itself.  Its production is the
seed's — `walkSeed G` carries the whole iteration's allowance and
`walkSeed_invariant` is the invariant at the loop head — and the refill at the
back edge is `WalkInv.inner_cap`'s `Nat.le_refl`.  What the entry edges read is
weaker than the cap and is what the per-scan arithmetic gives: a scan needs at
most `n + 5` of the budget, and the three scans that can have run before any entry
spend at most `3 * n`, so the remaining budget at an entry is at least `n + 5`.
That floor is the entry-edge links' hypothesis (`G.n + 5 ≤ C.inner`), the same
bargain class C strikes for the refusal offset's bound: the corpus-wide
justification is the per-iteration sum, and the link takes the fact it consumes.

The five arms proved below do not consume the cap's value: each decreases the
inner component at a fixed `k`, and the outer term is the same on both sides.
The entry loop's arm is the one that reads it, and it does not close; the first
obligation it needs is recorded in *The entry loop's first obligation* below.

## The arm, and the shape

Six back edges, on the body's 165 blocks (`#guard` at
`JsonStage2IR:1399`):

| back edge                     | loop                 | shape                        |
| ----------------------------- | -------------------- | ---------------------------- |
| `for.inc.i.i → for.body.i.i`  | literal comparison   | two blocks, no memory write  |
| `while.body370.i → land.rhs.i`| whitespace skip      | scans the gap                |
| `while.body.i104 → land.rhs.i103` | string scan      | scans to the closing quote   |
| `while.body76.i → land.rhs71.i`   | escape scan      | scans for a backslash        |
| `while.body462.i → land.rhs457.i` | extra-token scan | scans to the next entry      |
| `cleanup478.i → while.body.i` | the entry loop       | the whole dispatch           |

The smallest is `for.inc.i.i → for.body.i.i`: one control step (two pure
instructions and a `condbr`), no memory write, and the only proof is the block's
`denoteCode`, the branch, and `c - (i + 1) < c - i`.  `forInc_step` proves it
against `WalkInv` — every field of the invariant is preserved, and the measure
strictly decreases — and `forInc_arm` states the same at the invariant alone,
with only the latch's own guard beside it.

The hard arm is the entry loop's, `cleanup478.i → while.body.i`: its iteration is
the whole dispatch, and inside it are the three obligations the source's own
guards mark — the **nesting** state (`sp`, `ctype`, `cst`, and the `sp >= MAXD`
refusal) and the **two reserves** (`z_arena_reserve` before a decoded body and
`out_reserve(&z->ev, 13)` before each record), each of which can take a refusal
arm and leave the cursors, the refusal bit and the refusal offset as the record
must report them.  The edge itself closes — `walkBack_step` is `cleanup478.i`'s
merge, the exit test, and the budget's refill at the invariant — but the iteration
does not, and the obligation it needs is not one of those three: the first store
the iteration executes is the header's write to the caller's cursor record, and
the region claim does not name it.  *The entry loop's first obligation* below
states it, with the two `Owns` lemmas that make it a necessity rather than a
convenience.

The four scans are the middle.  Their common shape is `scan_step`, stated once: the
counter's `add`, the bound's `icmp eq` and the two-arm `condbr`, at the scan's own
names, with the step, the invariant and a strictly smaller measure.  The visit's own
row — what a traversal applies at each visiting counter — is the guard-free round of
`JsonStage2WalkRevolutionScanRound` (`scanRound_at` at the state's own cells, and
`scanRoundField` as the row).  The per-scan arms that used to wrap `scan_step` are
not here: each took a `ScanGuard` hypothesis that is false at every state whose
registers hold words, so the statements were vacuous, and they have been removed.

Each scan is the same latch: the counter steps by one, the scan's own bound is tested
for equality, and the test is clear because the counter is still short of it.
The latch block itself is pinned (`scanWhitespace_find` and its three
companions), the landing block's `phi` is read out of the body by `#guard`
(`scanLandSelect`), and a visit reads its counter and bound from `WalkLocal`
and writes the landing facts back into it.  The scans read staged memory — each landing
block loads a document byte — but none writes it, so the memory claim and the
carried extents are untouched.  `k` is not read, so the measure's outer factor is
the same on both sides and the decrease is the inner component's.

## What is not here

`Stage2WalkObligation` is not proved.  This module supplies the invariant
statement, the measure, five of the six arms, the block-local facts at the ten
blocks those arms reach, the seed (`walkSeed`/`WalkSeedState`/
`walkSeed_invariant`), the exit's clauses (`WalkInv.report`), the outer
iteration's strict decrease (`walkMeasure_step`), the entry loop's back edge
itself (`walkBack_step`: `cleanup478.i`'s merge, the exit test, and the inner
reset), and the nesting clause carried through every one of them
(`WalkInv.depth_reg`, `WalkInv.depth_cap`).  The entry loop's arm — the dispatch
the edge closes over — does not close, and its first obstruction is no longer the
frame: `WalkInv.frame` is the record's own write extent (`walkWide` at the
run's cursors), and the two forward stores that used to contradict it are
`WalkInv.frame_cursorK` (`while.body.i`'s `%c.i + 32`) and
`WalkInv.frame_stack` (`if.end24.i`'s two stack writes), both at the invariant.
What remains is the dispatch's own trace, and its register half is carried by
three fields: `WalkPtrs` binds `%3`, `%5`, `%k11.i`, `%ctype.i`, `%cst.i` and
`hash1.i.i`; `WalkRegs` binds the thirty-six static values `entry` and the
preheader fix (`%nep`, the stream's count, among them); and `WalkIter` binds the
header's per-iteration registers `%7`, `%8` and `%arrayidx10.i` at
`entryPos C.k`, `entryByte C.k` and `G.b + entryPos C.k`.  The static carrier is preserved by
`WalkRegs.bind`/`WalkRegs.cells_of` and, for a whole run, `WalkRegs.of_run` —
one `denoteCode_lookupName` per name and no memory reasoning; the per-iteration
registers' production is `whileBody_step`'s own three binds and its preservation is
`WalkIter.bind`/`WalkIter.cells_of`/`WalkIter.of_run`.  `WalkInv.log_hash`
carries the zeroed hash word `if.end24.i` branches on.  With them the dispatch's
two named blocks are steps.  `whileBody_step` runs
`while.body.i` from the invariant into `NodeBlock21`, advancing the entry index to
the merge's, taking the merge's depth, preserving every clause and decreasing
`walkMeasure`.  `ifEnd24_step` runs `if.end24.i` into `if.end.i.i` — the branch
its own zeroed hash word fixes, not an assumed guard — writing the two container
stacks at the carried depth, preserving every clause, with the measure unchanged
because the block advances neither the index nor the inner work.  Its chain is
split by `walkDenoteCode_append_some`, an append lemma for runs with no `phi`, so
the hash word's load and the branch test it feeds are two hand-written steps
rather than an automation target: that load's address metavariable was what an
all-automated chain left unresolved.

The trace itself is stated: `WalkLink` is one link (a control step that preserves
`WalkInv` and does not raise `walkMeasure`), `WalkChain` is a chain of them, and
`WalkChain.steps`, `WalkChain.measure_le` and `WalkChain.completes` read a chain
as a run, a measure bound, and a completion at a returning last state.

A hundred and fifty-three of the body's 165 blocks are links, and *The middle's
two classes* below is the census that decomposes the count: the two named arms
(`WalkLink.whileBody`, `WalkLink.ifEnd24`), the one that decreases the measure
(`WalkLink.forInc`), the classes A, B and B′, class C's
eighteen refusal stores, class D's ten stores (`JsonStage2WalkStore`), class E's
twelve merges and twelve of class G's fourteen reads (`JsonStage2WalkPhi`,
`JsonStage2WalkPure`), sixteen of class F's nineteen call blocks
(`JsonStage2WalkCall`), and the two entry links beside `while.body.i.lr.ph`
(`JsonStage2WalkEntry`).  The other four of the census's ten H1 latches are the
four scan headers: they are links no longer, and their visit is the counted round
(`walkScanRounds457_of_cell` applying `scanRound_at`) rather than a link.  The
shape each remaining class needs, and the nine blocks that are still not links,
are stated there.  `WalkLocal` is
still `True` at every block outside the ten whose carrier it names — the five
latches and their landings — so
well-foundedness over the whole control flow is not established, and
`Stage2WalkCompletes` is not inhabited.

**The open rows, named.**  Three remain, and none is claimed here.  The *entry
run* is no longer one: `JsonStage2WalkSeedRun`'s `walkSeedState` produces
`WalkSeedState` at the state the entry run leaves — its twenty-one clauses, the
three carriers and the frame and presence rows included — and
`walkSeedState_geometry` derives the run's two loads from the staging itself, so
`walkSeed_invariant`'s hypothesis is now a conclusion of the seed module.  What
remains: (1) the 165-block next-link lemma; (2) the well-founded completion one
level up from `WalkChain`; and (3) the budget's global accounting.  The container
stacks' contents are no longer one: `WalkCarry` carries the written mark and the
two maps, and `WalkInv` carries the two `WalkStackBytes` clauses beside
`sp ≤ wlen` and `wlen ≤ stage2StackExtent`, so a link that reads a stack byte at
`sp - 1` derives it from the map (`walkStack_valuePos`) rather than assuming it.  The census's 153 links are the arithmetic of the
*classes*, and a link whose source invariant no run reaches (the preheader's,
whose premise asks for `%k11.i` before the block binds it) is vacuous: it is
proved, and it moves nothing.  The four scan headers are not among them: their
visit is the counted round (`walkScanRounds457_of_cell` applying `scanRound_at`).
*The loop's forward stores* below states the rest in order, including the
pipeline's one pending transport-pair clause.

The cap is a clause and not an arm, and it is now carried: `WalkInv.inner_cap`
bounds the inner component by `walkInnerCap G` — the *shared* per-iteration budget,
`4 * n + 5`, not one scan's remaining work — the arms that move the component
re-establish it (the scan and literal arms because they lower it, the seed and the
back edge because they set it to the cap), and the seed satisfies it by
construction (`walkSeed_inner_cap`).  The value is the conservative sum of the four
scans' document bounds plus the literal comparison's five, and it is a completion
witness rather than a tight bound.  `WalkInv.alen_ge` is the second clause the exit
needed and the invariant did not carry: the report's `arenaGe`, the append-only
half of the arena cursor.

The nesting state is a clause too, and it is carried the same way: `depth_reg`
ties `%sp.i.0248` to the carry's `sp`, `depth_cap` bounds it by the stacks'
staged extent, the seed sets it to zero (`WalkSeedState`'s third clause is the
loop head's `phi`), and the arms that do not touch it carry it through their
binds.  Its `519` is the `MAXD` check's bound and stays with the arm (`NestGuard`):
a push at `519` carries `520` out of `if.end24.i`.  What the clause does not carry
is the stacks' contents — the push/pop discipline `ctype[i]`/`cst[i]` and
`s2_value_pos` maintain — which is the dispatch's, not the invariant's.
-/

/-
This module is the interface its consumers import: the walk-scope proof is in
the modules below, in dependency order, and the imports re-export every name.
-/
import LeanLLVM.Refinement.JsonStage2WalkScopeGeom
import LeanLLVM.Refinement.JsonStage2WalkScopeRecord
import LeanLLVM.Refinement.JsonStage2WalkScopeArms
import LeanLLVM.Refinement.JsonStage2WalkScopeStores
import LeanLLVM.Refinement.JsonStage2WalkScopeBlocks
import LeanLLVM.Refinement.JsonStage2WalkScopeStaged
import LeanLLVM.Refinement.JsonStage2WalkScopeDispatch
import LeanLLVM.Refinement.JsonStage2WalkScopeClasses
import LeanLLVM.Refinement.JsonStage2WalkScopeClassC
import LeanLLVM.Refinement.JsonStage2WalkScopeClassAB
import LeanLLVM.Refinement.JsonStage2WalkScopeBudget
