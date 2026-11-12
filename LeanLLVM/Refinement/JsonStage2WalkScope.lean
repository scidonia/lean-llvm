/-
The stage-2 walk's loop invariants, its measure, and its six back edges.

`Stage2WalkObligation` (`JsonStage2IR`) is `Satisfies` for the pinned 165-block
body, and its first conjunct is completion at `stage2Budget`
(`stage2WalkObligation_iff_completion`).  `runFuel` is fuel-indexed, so the proof
that resists is the loop: an invariant preserved by every arm, and a measure that
decreases on every iteration.  This module scopes that proof.  It discharges the
literal comparison's arm and the four scans', five edges that decrease the measure
at the edge itself; the entry loop's edge (the merge at `cleanup478.i`, its two
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
at `%z + 48` is `alen`, and `log_acap` at `%z + 56` is `dstcap` — so
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

The four scans are the middle, and their four arms are proved below against the
same `WalkInv`, one at a time:

| arm | source block | landing block | measure step |
| --- | ------------ | ------------- | ------------ |
| `whitespace_scan` | `while.body370.i` | `land.rhs.i` | `inner : c - i ↦ c - (i + 1)` |
| `string_scan` | `while.body.i104` | `land.rhs.i103` | `inner : c - i ↦ c - (i + 1)` |
| `escape_scan` | `while.body76.i` | `land.rhs71.i` | `inner : c - i ↦ c - (i + 1)` |
| `extraToken_scan` | `while.body462.i` | `land.rhs457.i` | `inner : c - i ↦ c - (i + 1)` |

Each is the same latch: the counter steps by one, the scan's own bound is tested
for equality, and the test is clear because the counter is still short of it.
The latch block itself is pinned (`scanWhitespace_find` and its three
companions), the landing block's `phi` is read out of the body by `#guard`
(`scanLandSelect`), and the arms read their counter and bound from `WalkLocal`
and write the landing facts back into it.  They read staged memory — each landing
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
What remains is the dispatch's own trace, and its register half is carried:
`WalkPtrs` binds `%3`, `%5`, `%k11.i`, `%ctype.i`, `%cst.i` and `%hash1.i.i` on
the invariant, produced at the seed and carried by the three arms, and
`WalkInv.log_hash` carries the zeroed hash word `if.end24.i` branches on.  With
them the dispatch's two named blocks are steps.  `whileBody_step` runs
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

A hundred and forty-nine of the body's 165 blocks are links, and *The middle's
two classes* below is the census that decomposes the count: the two named arms
(`WalkLink.whileBody`, `WalkLink.ifEnd24`), the five that decrease the measure
(`WalkLink.forInc` and the four scan headers), the classes A, B and B′, class C's
eighteen refusal stores, class D's ten stores (`JsonStage2WalkStore`), class E's
twelve merges and twelve of class G's fourteen reads (`JsonStage2WalkPhi`,
`JsonStage2WalkPure`), nine of class F's nineteen call blocks
(`JsonStage2WalkCall`), and the two entry links beside `while.body.i.lr.ph`
(`JsonStage2WalkEntry`).  The shape each remaining class needs, and the 16 blocks
that are still not links, are stated there.  `WalkLocal` is
still `True` at every block outside the ten the five measure arms reach, so
well-foundedness over the whole control flow is not established, and
`Stage2WalkCompletes` is not inhabited.
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
import LeanLLVM.Refinement.JsonStage2Body
import LeanLLVM.Refinement.JsonEscapeListBody

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.BlockEval

/-! ### The staging geometry -/

/-- `stage2Pre`'s witnesses, at the memory the caller staged.  A geometry is the
staging the loop reads, held fixed for the run; the invariant and the measure are
indexed by it.  Every field and every clause is `stage2Pre`'s, in the same order,
so the loop does not work at a weaker domain than the record admits. -/
structure WalkGeom (m0 : Mem) where
  /-- The document. -/
  b : Nat
  /-- The document's length. -/
  n : Nat
  /-- The entry stream. -/
  ep : Nat
  /-- The entry count. -/
  nep : Nat
  /-- The escape list. -/
  xp : Nat
  /-- The escape count. -/
  nxp : Nat
  /-- The arena. -/
  dst : Nat
  /-- The arena's capacity. -/
  dstcap : Nat
  /-- The arena's cursor slot. -/
  ndst : Nat
  /-- The event stream. -/
  ev : Nat
  /-- The event stream's capacity. -/
  evcap : Nat
  /-- The event stream's cursor slot. -/
  nev : Nat
  /-- The refusal slot. -/
  err : Nat
  /-- The document's bytes. -/
  bs : List UInt8
  /-- The entry stream's positions. -/
  ent : List Nat
  /-- The arena's cursor as staged. -/
  ndst0 : Nat
  /-- The event stream's cursor as staged. -/
  nev0 : Nat
  /-- The document is readable. -/
  doc : readBytes m0 b n = some bs
  /-- The decoder's read-past tail is staged. -/
  tail : HasBytes m0 (b + n) stage2ReadTail
  /-- The entry stream is readable. -/
  entries : readLanes32 m0 ep nep = some ent
  /-- The entry positions are in document order. -/
  order : ent.Pairwise (· < ·)
  /-- The entry positions are inside the document. -/
  inside : ∀ q ∈ ent, q < n
  /-- The escape list's bytes are staged. -/
  esc : HasBytes m0 xp (4 * nxp)
  /-- The arena is staged. -/
  arenaCap : HasBytes m0 dst dstcap
  /-- The arena has room for the document and the decoder's slack. -/
  arenaRoom : ndst0 + n + stage2ArenaReserve ≤ dstcap
  /-- The event stream is staged. -/
  evCap : HasBytes m0 ev evcap
  /-- The event stream has room for one record per input byte. -/
  evRoom : nev0 + stage2RecordBytes * n ≤ evcap
  /-- The arena's cursor slot reads as staged. -/
  ndstRead : readBytes m0 ndst 8 = some (wordBytes 8 ndst0)
  /-- The event cursor's slot reads as staged. -/
  nevRead : readBytes m0 nev 8 = some (wordBytes 8 nev0)
  /-- The refusal slot is staged. -/
  errBytes : HasBytes m0 err 8
  /-- The document's positions fit the entry stream's 32-bit words. -/
  maxDoc : n ≤ stage2MaxDocument
  /-- The staged objects are separate. -/
  separate : DisjointRegions
    (stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err)
  /-- **The cursor the call is made at**, which is where the body's four stack
  objects land (`stage2AllocaWrites`).  It is `Γ_stage2.pre`'s `next` and not a
  number chosen here. -/
  next0 : Nat
  /-- **The watermark**: every staged object ends at or below the cursor.  This is
  `stage2Pre`'s last clause, read at the geometry, and it is what makes the four
  stack objects disjoint from every staged byte — the fact the frame and the two
  read proofs below consume. -/
  watermark : ∀ r ∈ stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err,
    r.1 + r.2 ≤ next0

/-- **The staging is inhabited at every caller the record admits.**  `WalkGeom`
is `stage2Pre` unpacked, so a walk inside `Γ_stage2.pre` has a geometry to carry;
without this the invariant would be satisfiable only by a caller the record
refuses, which is the vacuity the completion conjunct exists to exclude. -/
theorem WalkGeom.nonempty {args : List Value} {m0 : Mem} {next : Nat}
    (h : Γ_stage2.pre args m0 next) : Nonempty (WalkGeom m0) := by
  have h' : stage2Pre args m0 next := h
  obtain ⟨b, n, ep, nep, xp, nxp, dst, dstcap, ndst, ev, evcap, nev, err, bs, ent,
    ndst0, nev0, -, doc, tail, entries, order, inside, esc, arenaCap, arenaRoom,
    evCap, evRoom, ndstRead, nevRead, errBytes, maxDoc, separate, hwm⟩ := h'
  exact ⟨{
    b := b
    n := n
    ep := ep
    nep := nep
    xp := xp
    nxp := nxp
    dst := dst
    dstcap := dstcap
    ndst := ndst
    ev := ev
    evcap := evcap
    nev := nev
    err := err
    bs := bs
    ent := ent
    ndst0 := ndst0
    nev0 := nev0
    doc := doc
    tail := tail
    entries := entries
    order := order
    inside := inside
    esc := esc
    arenaCap := arenaCap
    arenaRoom := arenaRoom
    evCap := evCap
    evRoom := evRoom
    ndstRead := ndstRead
    nevRead := nevRead
    errBytes := errBytes
    maxDoc := maxDoc
    separate := separate
    next0 := next
    watermark := hwm
  }⟩

/-- The entry count is at most the document's: the stream's positions are
strictly increasing and inside the document.  `Stage2Run.nep_le` is the same fact
at the report; the loop needs it at the staging. -/
theorem WalkGeom.nep_le {m0 : Mem} (G : WalkGeom m0) : G.nep ≤ G.n := by
  rw [← readLanes32_length m0 G.ep G.nep G.ent G.entries]
  exact length_le_of_pairwise_lt G.order G.inside

/-! ### The carry and the invariant -/

/-- **The staging the walk's own objects have at the adapter.**  `WalkGeom` is
`stage2Pre`'s thirteen-argument staging; the flattened body also receives the
eight objects the constraint flattening appends, plus the caller's two count
slots.  They are fixed for the run, so the carry holds them: `stage2StagedPre`
gives their presence and separation, and the log's fields are read at the log's
own address (`stage2.c`'s `ZOut` at `%z`).

The two count slots are here for the reason `stage2StagedPre` states them: the
adapter separates them from the seven scratch objects, and a caller reads them
back after the run, so the staging that the port speaks about is the seventeen-
object one. -/
structure WalkStage {m0 : Mem} (G : WalkGeom m0) where
  /-- The cursor record `%c.i`. -/
  c : Nat
  /-- The type stack `%ctype.i`. -/
  ctype : Nat
  /-- The state stack `%cst.i`. -/
  cst : Nat
  /-- The scalar token `%t352.i`. -/
  tok : Nat
  /-- The walk's own staging record `%s`. -/
  s : Nat
  /-- The log `%z`. -/
  z : Nat
  /-- The refusal record `%e`. -/
  e : Nat
  /-- The caller's entry-count slot. -/
  nkSlot : Nat
  /-- The caller's escape-count slot. -/
  nxpSlot : Nat
  /-- The staged objects are separate, as the adapter's staging states them.  The
  pre also stages `%d.i` beside this list (`stage2StagedPre`'s own entry); the
  carry names the seventeen because that is every object the walk writes. -/
  separate : DisjointRegions
    (stage2StagedRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev G.evcap
      G.ndst G.nev G.err c ctype cst tok s z e nkSlot nxpSlot)
  /-- The seven objects the walk writes are present in the staged memory. -/
  present : ∀ r ∈ stage2StagedWrites c ctype cst tok s z e, HasBytes m0 r.1 r.2
  /-- **The number path's output slot `%d.i`**, an appended parameter rather than
  one of the seven: `num_fast_el1`'s accepting arm stores the converted value
  through it (`s2NumFastFoot`'s `(out, 8)`). -/
  d : Nat
  /-- `%d.i`'s eight bytes are staged. -/
  dPresent : HasBytes m0 d 8
  /-- **`%d.i` is separate from the walk's staged objects** — the adapter's
  separation of its own slot (`stage2StagedPre_dSep`), in the orientation the
  frame's exclusions read. -/
  dSep : ∀ r ∈ stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err c ctype cst tok s z e,
    r.1 + r.2 ≤ d ∨ d + 8 ≤ r.1
  /-- **The seven appended objects end at or below the call's cursor.**  `%ei.i`,
  `%root_done.i`, `%xj.i` and `%outn.i` are the body's own four `alloca`s at
  `G.next0` (`stage2AllocaWrites`), and the seven the constraint flattening
  appends are the *caller's* objects, staged before the call — so every one of
  them, and `%d.i` too, ends at or below the cursor the callee allocates from.
  This is `Γ_stage2.pre`'s watermark statement (`stage2Pre`'s last clause, which
  `WalkGeom.watermark` carries at the thirteen ABI objects) at the objects the
  adapter appends.  It is stated here rather than in `stage2StagedPre` because
  the adapter's predicate does not carry the call's `next`: the cursor is the
  run's, so the relation between the seven and it is the run's staging's to
  state.  Its consumers are `WalkStage.rootSlot_log` and `WalkStage.rootSlot_ev`,
  and they are what makes the container-closing helper's root slot — and its
  container byte — fresh of the log and the event stream, so a link that calls
  `s2_after_value` needs no staging hypothesis beside it. -/
  sevenEnd : ∀ r ∈ stage2StagedWrites c ctype cst tok s z e, r.1 + r.2 ≤ G.next0

/-- **The root slot misses the log.**  `%root_done.i` is the second allocated slot
at `G.next0 + 8`, four bytes wide, and the log ends at or below `G.next0`, so the
two are separate: `walkAfterValue_facts`' depth-zero arm writes the root flag and
the log's four fields read across it. -/
theorem WalkStage.rootSlot_log {m0 : Mem} {G : WalkGeom m0} (S : WalkStage G) :
    G.next0 + 8 + 4 ≤ S.z ∨ S.z + stage2LogExtent ≤ G.next0 + 8 := by
  have h := S.sevenEnd (S.z, stage2LogExtent) (by simp [stage2StagedWrites])
  simp only [stage2LogExtent] at h ⊢
  omega

/-- **The root slot misses the event stream.**  Same slot, and the stream is one
of the thirteen ABI objects, so `WalkGeom.watermark` places its whole capacity at
or below the cursor. -/
theorem WalkStage.rootSlot_ev {m0 : Mem} {G : WalkGeom m0} (S : WalkStage G) :
    G.next0 + 8 + 4 ≤ G.ev + G.nev0 ∨ G.ev + G.evcap ≤ G.next0 + 8 := by
  have h := G.watermark (G.ev, G.evcap) (by simp [stage2Regions])
  omega


/-- What the loop carries between iterations.  The extents are a list because a
cursor is their sum and a sum does not name its summands (`Stage2Run`'s
definition records the obstruction). -/
structure WalkCarry {m0 : Mem} (G : WalkGeom m0) where
  /-- The block index into the entry stream. -/
  k : Nat
  /-- The arena cursor. -/
  alen : Nat
  /-- The event cursor. -/
  evlen : Nat
  /-- The event records emitted, in order, at the widths their emitters write. -/
  events : List EventRecord
  /-- The decoded bodies' document extents, in document order. -/
  spans : List (Nat × Nat)
  /-- The record in flight: its entry position, the arena offset reserved for
  its decoded body, and that body's document extent.  The extent is the third
  component rather than something the arms re-derive: `z_arena_reserve` tests
  `alen + len + 64` against the arena's capacity, and `len` — the token's
  document extent, `entry[k+1] - entry[k] - 1` — is the number the test is
  about.  Carrying it is what makes the arena trap's exclusion a statement of
  this invariant instead of a hypothesis beside it. -/
  pending : Option (Nat × Nat × Nat)
  /-- The refusal bit. -/
  refusal : Bool
  /-- The refusal offset. -/
  eoff : Nat
  /-- The block the run is at. -/
  block : String
  /-- The remaining inner work at that block. -/
  inner : Nat
  /-- The nesting depth, the index the two container stacks are written at.  It is
  `%sp.i.0248`'s value at the loop head's `phi`; the merge at `cleanup478.i` is
  the edge that moves it. -/
  sp : Nat
  /-- The adapter's staging of the walk's own objects, fixed for the run. -/
  stage : WalkStage G

/-! ### The walk's three region lists

The record's memory claim is two claims, and the region they are stated over is a
list each:

* `walkStaged` — the objects the run *makes present*, at the extents the caller
  staged them: the arena's window (the decoded document plus the decoder's slack),
  the two cursor slots, the refusal slot, the seven appended objects and `%d.i`'s
  slot.  Every extent is a constant of the geometry, so no arm's step has to
  re-derive it as a cursor moves: presence is monotone and a store only adds
  cells.
* `walkWide` — the objects the run may *write*: the arena's decoded prefix and the
  event stream's prefix at the carried cursors (the extents the body stores into),
  the seven, `%d.i`, and the four stack objects the body allocates at the cursor
  `stage2AllocaWrites G.next0`.

The split is not a choice of presentation.  A single `Owns` at `walkWide` would
demand *presence* of the four stack bytes, which is false at the loop head: the
`alloca`s create no cells and nothing writes them until a helper stores through
them.  And a single `Owns` at the staged list only would be contradicted by every
helper call that writes a stack slot.  So the run carries presence over what the
caller staged and silence over what the run may write, and the two lists differ by
exactly the four slots.

The four are *fresh* — outside `walkStaged`'s every byte — because both lists' bases
were staged at or below `G.next0` (`G.watermark`) and every alloca entry starts
there (`stage2AllocaWrites_start`).  That is the fact the document's and the entry
stream's read proofs read: a byte inside a staged object is below `next0`, hence
outside `walkAlloca`, hence outside `walkWide`. -/

/-- The objects the run makes present, at the extents the caller staged them. -/
def walkStaged {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) : List (Nat × Nat) :=
  [(G.dst, G.ndst0 + G.n + stage2ArenaReserve), (G.ndst, 8), (G.ev, G.evcap),
   (G.nev, 8), (G.err, 8)] ++
    stage2ReportScratch C.stage.c C.stage.ctype C.stage.cst C.stage.tok C.stage.s
      C.stage.z C.stage.e C.stage.d

/-- The run's write extents at the carried cursors: the arena's decoded prefix, the
seven appended objects, `%d.i`, and the event stream's prefix. -/
def walkPresent {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) : List (Nat × Nat) :=
  [(G.dst, C.alen), (G.ev, C.evlen)] ++
    stage2ReportScratch C.stage.c C.stage.ctype C.stage.cst C.stage.tok C.stage.s
      C.stage.z C.stage.e C.stage.d

/-- The objects the run may write, at its cursors: the write extents above and the
body's four stack slots. -/
def walkWide {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) : List (Nat × Nat) :=
  walkPresent G C ++ stage2AllocaWrites G.next0

/-- **The frame's list grows with the cursors.**  Every entry of the list at one
carry lies inside an entry of the list at another, when the arena's and the event
stream's cursors only advance and the staging is the same.  This is the coverage a
step that moves a cursor reads (`UnchangedOutside.write_grow`), and the two
cursor-moving stores of the arena and the event stream are its only consumers. -/
theorem walkWide_grow {m0 : Mem} {G : WalkGeom m0} {C C' : WalkCarry G}
    (hala : C.alen ≤ C'.alen) (hevl : C.evlen ≤ C'.evlen) (hstage : C'.stage = C.stage) :
    ∀ r ∈ walkWide G C, ∃ s ∈ walkWide G C', s.1 ≤ r.1 ∧ r.1 + r.2 ≤ s.1 + s.2 := by
  intro r hr
  simp only [walkWide, walkPresent, stage2ReportScratch] at hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_cons.mp hr with rfl | hr1
      · exact ⟨(G.dst, C'.alen), by simp [walkWide, walkPresent], le_rfl, by omega⟩
      · rcases List.mem_cons.mp hr1 with rfl | hnil
        · exact ⟨(G.ev, C'.evlen), by simp [walkWide, walkPresent], le_rfl, by omega⟩
        · exact absurd hnil (by simp)
    · exact ⟨r, by
        simp only [walkWide, walkPresent]
        refine List.mem_append_left _ (List.mem_append_right _ ?_)
        rw [hstage]
        exact hr, le_rfl, le_rfl⟩
  · exact ⟨r, by simp [walkWide, walkPresent, hr], le_rfl, le_rfl⟩

/-- A byte inside the staged objects is inside the frame's list. -/
theorem walkWide_of_staged {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {a : Nat}
    (h : inRegions (stage2ReportScratch C.stage.c C.stage.ctype C.stage.cst
      C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d) a) :
    inRegions (walkWide G C) a := by
  obtain ⟨r, hr, hi⟩ := h
  exact ⟨r, List.mem_append_left _ (List.mem_append_right _ hr), hi⟩

/-- A byte inside the two staged prefixes is inside the frame's list. -/
theorem walkWide_of_prefix {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {a : Nat}
    (h : inRegions [(G.dst, C.alen), (G.ev, C.evlen)] a) :
    inRegions (walkWide G C) a := by
  obtain ⟨r, hr, hi⟩ := h
  exact ⟨r, List.mem_append_left _ (List.mem_append_left _ hr), hi⟩

/-- A byte inside the seven appended objects is inside the frame's list. -/
theorem walkWide_of_seven {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {a : Nat}
    (h : inRegions (stage2StagedWrites C.stage.c C.stage.ctype C.stage.cst
      C.stage.tok C.stage.s C.stage.z C.stage.e) a) :
    inRegions (walkWide G C) a :=
  walkWide_of_staged (inRegions_mono (fun r hr => List.mem_append_left _ hr) h)

/-- A byte below the watermark is outside the four stack slots. -/
theorem not_walkAlloca_of_lt {m0 : Mem} {G : WalkGeom m0} {a : Nat}
    (h : a < G.next0) :
    ¬ inRegions (stage2AllocaWrites G.next0) a :=
  not_inRegions_allocaWrites h

/-- **A byte of a staged ABI object is below the watermark.**  The staging's
entries are the objects the read proofs exclude, and each ends at or below the
cursor, so every byte of one is below it — and therefore outside the four stack
slots. -/
theorem staged_lt_watermark {m0 : Mem} {G : WalkGeom m0} {r : Nat × Nat} {a : Nat}
    (hr : r ∈ stage2Regions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev G.evcap
      G.ndst G.nev G.err)
    (ha : a < r.1 + r.2) : a < G.next0 :=
  Nat.lt_of_lt_of_le ha (G.watermark r hr)

/-- A write at a byte the frame's list covers leaves the frame. -/
theorem walkFrame_write_inside {m0 m : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {a : Nat} {bs : List UInt8}
    (h : UnchangedOutside m0 m (walkWide G C))
    (hw : ∀ k, k < bs.length → inRegions (walkWide G C) (a + k)) :
    UnchangedOutside m0 (writeBytes m a bs) (walkWide G C) :=
  h.write_inside hw

/-- A store at a byte inside one of the walk's staged extents preserves the frame
(the common shape: the cursor record's field, the two stacks, the log's fields). -/
theorem walkFrame_write_staged {m0 m : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {a : Nat} {bs : List UInt8}
    (h : UnchangedOutside m0 m (walkWide G C))
    (hw : ∀ k, k < bs.length →
      inRegions (stage2ReportScratch C.stage.c C.stage.ctype C.stage.cst
        C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d) (a + k)) :
    UnchangedOutside m0 (writeBytes m a bs) (walkWide G C) :=
  h.write_inside (fun k hk => walkWide_of_staged (hw k hk))

/-- Presence is monotone under a write.  The target memory is named so that a
caller states the memory the run left rather than having the write inferred from
the goal: a step's memory is a stack of writes, and the caller's `rfl` fixes the
inner one. -/
theorem walkStaged_write {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {m m' : Mem}
    {a : Nat} {bs : List UInt8}
    (hm : m' = writeBytes m a bs)
    (h : ∀ r ∈ walkStaged G C, HasBytes m r.1 r.2) :
    ∀ r ∈ walkStaged G C, HasBytes m' r.1 r.2 := by
  subst hm
  exact fun r hr => hasBytes_writeBytes (h r hr)

/-- A scan's counter at a block that reads it: the counter register holds `i`,
the scan's own bound register holds `c`, and the remaining work `c - i` is inside
the iteration's remaining inner budget.  Every scan tests its counter for equality
with that bound, so the two registers are what both its guard and its measure are
read from, and `c - i ≤ inner` is what makes the step's decrement safe. -/
def ScanCount (s : State) (phi cond : String) (inner : Nat) : Prop :=
  ∃ i c : Nat, c - i ≤ inner ∧ i < c ∧ c < 2 ^ 64 ∧
    lookupName s.env phi = some (.int 64 (BitVec.ofNat 64 i)) ∧
    lookupName s.env cond = some (.int 64 (BitVec.ofNat 64 c))

/-- The same at a scan's landing block.  The counter is the increment the latch
wrote — `BlockEval`'s `phi` selects it because the predecessor names the latch —
and the bound register is the one the latch read. -/
def ScanLanded (s : State) (src inc cond : String) (inner : Nat) : Prop :=
  ∃ i c : Nat, c - i ≤ inner ∧ i < c ∧ c < 2 ^ 64 ∧
    s.pre = some src ∧
    lookupName s.env inc = some (.int 64 (BitVec.ofNat 64 i)) ∧
    lookupName s.env cond = some (.int 64 (BitVec.ofNat 64 c))

/-- A scan's latch guard, at the carry.  Whatever counter and bound the local fact
pins, the increment is still short of the bound, so the latch's equality test is
clear and the back edge — not the exit — is the edge it takes.  The guard is
stated over the local fact's own witness rather than beside it: a caller has the
registers in hand, so it never has a second existential to reconcile with the
first. -/
def ScanGuard (s : State) (phi cond : String) (inner : Nat) : Prop :=
  ∀ i c : Nat, c - i ≤ inner →
    lookupName s.env phi = some (.int 64 (BitVec.ofNat 64 i)) →
    lookupName s.env cond = some (.int 64 (BitVec.ofNat 64 c)) →
    i + 1 < c

/-- **The inner work one iteration is allowed**, the inner component's bound and
the radix's base in `walkMeasure`.  It is a budget shared by the whole iteration,
not one scan's remaining work: the scans reset the inner component as each one is
entered, so the measure rises across an entry unless the value it carries is a
resource the whole iteration draws on.  Four scans may each walk the document, and
the literal comparison adds at most five bytes, so `4 * n + 5` covers every path
the dispatch has.  It is a completion witness and not a tight bound. -/
def walkInnerCap {m0 : Mem} (G : WalkGeom m0) : Nat := 4 * G.n + 5

/-- **A scan's landing block entered from its first predecessor.**  A scan's
landing block (`land.rhs*`) has two predecessors: its latch, on the back edge, and
the block that enters the scan first.  Only the back edge has the latch's
increment to read, so on the entry edge the counter is the value the landing
block's own `phi` will select from that predecessor, and the fact is that value —
not `ScanLanded`'s, which is about the other edge.  A landing block's local fact
is therefore the disjunction of the two. -/
def ScanEntered (s : State) (src counter cond : String) (inner : Nat) : Prop :=
  ∃ i c : Nat, c - i ≤ inner ∧ i < c ∧ c < 2 ^ 64 ∧ s.pre = some src ∧
    lookupName s.env counter = some (.int 64 (BitVec.ofNat 64 i)) ∧
    lookupName s.env cond = some (.int 64 (BitVec.ofNat 64 c))

/-- The block-local half of the invariant: the remaining budget's coverage of the
work still to do, and the registers it is read from, at the ten blocks the five
proved arms reach — the literal comparison's two and each of the four scans'
latch and landing.  A landing block
has two predecessors, so its fact is disjunctive: `ScanLanded` on the latch's back
edge and `ScanEntered` on the edge that first enters the scan, and the literal
comparison's landing block is the same pair (the latch's `%inc.i.i` or
`if.end48.i`'s zero).  At every other block it is `True`; pinning it there is the
remaining arm's work (the entry loop's), and the module docstring says so rather
than claiming a bound it does not have. -/
def WalkLocal {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) : Prop :=
  if C.block = "for.inc.i.i" then
    ∃ i c : Nat, c - i ≤ C.inner ∧ i < c ∧ c < 2 ^ 64 ∧
      lookupName s.env "%i.029.i.i" = some (.int 64 (BitVec.ofNat 64 i)) ∧
      lookupName s.env "%cond.i.i" = some (.int 64 (BitVec.ofNat 64 c))
  else if C.block = "for.body.i.i" then
    ((∃ i c : Nat, c - i ≤ C.inner ∧ i < c ∧ c < 2 ^ 64 ∧
        s.pre = some "for.inc.i.i" ∧
        lookupName s.env "%inc.i.i" = some (.int 64 (BitVec.ofNat 64 i)) ∧
        lookupName s.env "%cond.i.i" = some (.int 64 (BitVec.ofNat 64 c))) ∨
      (∃ c : Nat, c ≤ C.inner ∧ 0 < c ∧ c < 2 ^ 64 ∧
        s.pre = some "if.end48.i" ∧
        lookupName s.env "%cond.i.i" = some (.int 64 (BitVec.ofNat 64 c))))
  else if C.block = "while.body370.i" then
    ScanCount s "%ee.0.i238" "%cond350.i" C.inner
  else if C.block = "land.rhs.i" then
    (ScanLanded s "while.body370.i" "%inc371.i" "%cond350.i" C.inner ∨
      ScanEntered s "land.rhs.i.preheader" "%idxprom.i" "%cond350.i" C.inner)
  else if C.block = "while.body.i104" then
    ScanCount s "%ee.011.i" "%cond.i" C.inner
  else if C.block = "land.rhs.i103" then
    (ScanLanded s "while.body.i104" "%inc.i105" "%cond.i" C.inner ∨
      ScanEntered s "cond.end.i96" "%idxprom.i" "%cond.i" C.inner)
  else if C.block = "while.body76.i" then
    ScanCount s "%s2.020.i" "%cond.i" C.inner
  else if C.block = "land.rhs71.i" then
    (ScanLanded s "while.body76.i" "%inc77.i" "%cond.i" C.inner ∨
      ScanEntered s "if.end67.i" "%ee.0.lcssa.i" "%cond.i" C.inner)
  else if C.block = "while.body462.i" then
    ScanCount s "%q.0.i246" "%cond350.i" C.inner
  else if C.block = "land.rhs457.i" then
    (ScanLanded s "while.body462.i" "%inc463.i" "%cond350.i" C.inner ∨
      ScanEntered s "if.then447.i" "%ee.1.i" "%cond350.i" C.inner)
  else True

/-- **The pointer registers the dispatch's blocks read**, in one place.

`%3` and `%5` are `entry`'s two loads — the document's base and the entry
stream's base — and the four others are the addresses the header and the nesting
arm read: `%k11.i` is the cursor record's `k` field (`%c.i + 32`), `%ctype.i` and
`%cst.i` are the two container stacks' bases, and `%hash1.i.i` is the log's hash
word (`%z + 32`).  Each is bound before the loop and no block of the dispatch
rebinds one, which is why the invariant carries them as bindings: a block's
`denoteCode` reads them, and the carry is where the run's fixed addresses live.
`WalkPtrs.bind` is the step that says a bind at any other name preserves all six.

They are binding facts about the emitted body rather than clauses about the
walk's memory — `%3`'s *value* is the document's address, and only the
initialisation knows it is `G.b` — so they sit beside `blockIndex` and
`depth_reg` rather than with the log's fields, and their production is the seed's. -/
def WalkPtrs {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (env : Env) : Prop :=
  lookupName env "%3" = some (.ptr G.b) ∧
    lookupName env "%5" = some (.ptr G.ep) ∧
    lookupName env "%k11.i" = some (.ptr (C.stage.c + 32)) ∧
    lookupName env "%ctype.i" = some (.ptr C.stage.ctype) ∧
    lookupName env "%cst.i" = some (.ptr C.stage.cst) ∧
    lookupName env "%hash1.i.i" = some (.ptr (C.stage.z + 32))

/-- **A bind at another name preserves all six pointer registers.**  Each
disequality is a literal comparison, so an arm discharges it with `decide`; the
six conclusions are the six cells read back out of the extended environment. -/
theorem WalkPtrs.bind {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {env : Env}
    (h : WalkPtrs G C env) {d : String} {v : Value}
    (h3 : ¬ d = "%3") (h5 : ¬ d = "%5") (hk : ¬ d = "%k11.i")
    (hc : ¬ d = "%ctype.i") (hs : ¬ d = "%cst.i") (hh : ¬ d = "%hash1.i.i") :
    WalkPtrs G C ((d, v) :: env) := by
  obtain ⟨hd3, hd5, hdk, hdc, hds, hdh⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [lookupName, ite_eq_right h3]; exact hd3
  · simp only [lookupName, ite_eq_right h5]; exact hd5
  · simp only [lookupName, ite_eq_right hk]; exact hdk
  · simp only [lookupName, ite_eq_right hc]; exact hdc
  · simp only [lookupName, ite_eq_right hs]; exact hds
  · simp only [lookupName, ite_eq_right hh]; exact hdh

/-- **A run of two binds at other names preserves the six pointer registers.** -/
theorem WalkPtrs.bind_pair {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {env : Env}
    (h : WalkPtrs G C env) {a b : String} {va vb : Value}
    (ha : ¬ a = "%3" ∧ ¬ a = "%5" ∧ ¬ a = "%k11.i" ∧ ¬ a = "%ctype.i"
      ∧ ¬ a = "%cst.i" ∧ ¬ a = "%hash1.i.i")
    (hb : ¬ b = "%3" ∧ ¬ b = "%5" ∧ ¬ b = "%k11.i" ∧ ¬ b = "%ctype.i"
      ∧ ¬ b = "%cst.i" ∧ ¬ b = "%hash1.i.i") :
    WalkPtrs G C ((b, vb) :: (a, va) :: env) :=
  (h.bind ha.1 ha.2.1 ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2.1 ha.2.2.2.2.2).bind
    hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2

/-- **The walk's invariant.**  Everything the loop carries, at the block it is at,
and the memory it has written.  This is the predicate every one of the six arms
must preserve; `forInc_step` proves the literal comparison's arm does and
`whitespace_scan`, `string_scan`, `escape_scan` and `extraToken_scan` prove the
four scans' do. -/
structure WalkInv {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) : Prop where
  /-- The run is at the carried block. -/
  pc_eq : s.pc = C.block
  /-- The entry index is the phi the outer loop reads. -/
  blockIndex : lookupName s.env "%k.0.i249" = some (.int 64 (BitVec.ofNat 64 C.k))
  /-- The index has not passed the stream. -/
  k_le : C.k ≤ G.nep
  /-- At most one record per entry consumed. -/
  events_le : C.events.length ≤ C.k
  /-- **The event cursor is the trace's own width sum.**  `out_raw` advances
  `o->len` by the bytes it reserves, and the trace records each write at the width
  its emitter gives it — one, nine or thirteen.  So the cursor is
  `nev0 + sum (trace.map encodedSize)`, which is the body's arithmetic; the
  equality this replaces, `nev0 + 13 * records`, was false at a literal's and at a
  number's emission (`LeanLLVMTest.Counterexamples.stage2_evlen_thirteen_eq_false`
  and `…_number`). -/
  evlen_eq : C.evlen = G.nev0 + (C.events.map EventRecord.encodedSize).sum
  /-- **The trace is the stream's written suffix.**  The records the carry names
  are the bytes at the log's stream from the staged cursor on, in order.  This is
  what makes the carry a statement about memory rather than about a counter: the
  cursor's value and the bytes under it are two readings of one trace. -/
  evBytes : readBytes s.mem (G.ev + G.nev0)
      (C.events.map EventRecord.encodedBytes).flatten.length =
    some (C.events.map EventRecord.encodedBytes).flatten
  /-- The arena cursor is bounded by the extents it decoded. -/
  alen_le_sum : C.alen ≤ G.ndst0 + (C.spans.map (fun r => r.2)).sum
  /-- The arena cursor only appends: this is the report's `Stage2Run.arenaGe`,
  read off the carry rather than assumed.  Without it the upper bound above is
  one-sided and the report's growth clause has no producer. -/
  alen_ge : G.ndst0 ≤ C.alen
  /-- The extents are in document order. -/
  spans_order : C.spans.Pairwise (fun r s => r.1 + r.2 ≤ s.1)
  /-- Every extent ends inside the document. -/
  spans_inside : ∀ r ∈ C.spans, r.1 + r.2 ≤ G.n
  /-- The record in flight reserves the arena at the cursor, inside the document:
  at most one record is being assembled, and its reservation is the cursor's own
  offset. -/
  pending_at : ∀ p off len, C.pending = some (p, off, len) → off = C.alen ∧ p < G.n
  /-- **The record in flight is a token of the document.**  Its entry position
  plus its extent is inside the document, which is the fact `z_arena_reserve`'s
  check needs: the entry stream's positions are strictly increasing and every
  position is inside the document (`WalkGeom.order`, `WalkGeom.inside`), so the
  extent `entry[k+1] - entry[k] - 1` ends at `entry[k+1] - 1 < n`.  The extent is
  carried rather than recomputed because the entry stream's index is not part of
  the carry either: `pending`'s first component is the position, and the extent
  is the predicate's third. -/
  pending_len : ∀ p off len, C.pending = some (p, off, len) → p + len ≤ G.n
  /-- **The record in flight is inside the arena's room at its entry position.**
  `z_arena_reserve` checks `alen + len + 64` against the arena's capacity before
  it decodes an entry's body, where `len` is the entry's own document extent and
  `alen` the cursor before that body.  The check's conclusion needs the cursor to
  be no further than the staging's offset plus the entry's position: the body
  then fits the document's own room (`G.entries`' positions are inside it), so
  `ndst0 + n + 64 ≤ dstcap` covers the sum.  This is the clause the **arena
  reserve's trap** (`if.end.i83`) reads; without it `alen` may be at `ndst0 + n`
  while a positive-length token is still to be decoded, and the trap is reachable
  under the invariant as it stood.

  Its only production is the merge's, through `pending`: a block that advances
  `alen` (`if.else285.i`) must keep the record's offset equal to the new cursor
  (`pending_at`) and re-prove the bound, and the merge that carries the next
  entry's position in is where the clause is first established for a body.  With
  `pending_len` beside it the clause set is the whole of the check's premises:
  `walkArenaReserve_clear` reads the three at one `pending` and needs nothing
  from outside the invariant. -/
  pending_cursor : ∀ p off len, C.pending = some (p, off, len) → C.alen ≤ G.ndst0 + p
  /-- The refusal offset is inside the document. -/
  eoff_le : C.eoff ≤ G.n
  /-- **The inner component is inside the iteration's budget.**  The component is
  the remaining budget a whole iteration draws on, so this says a scan step's
  decrement never needs more than was handed out, and it is the clause the outer
  arm's strictness reads: an iteration advances `k` by one and refills `inner` to
  at most `walkInnerCap G`, so the radix `cap + 1` makes the outer term fall by at
  least one even when the inner component is refilled to its cap.  It cannot be
  derived from the register bounds the scans carry — those bound a scan's own
  bound register by `2 ^ 64` — which is why it is a field here and its production
  at the loop head is stated with the seed. -/
  inner_cap : C.inner ≤ walkInnerCap G
  /-- **The nesting depth is inside the container stacks' capacity.**  `if.end24.i`
  writes `%ctype.i[sp]` and `%cst.i[sp]`, so the depth must index inside the
  stacks' staged extent; a push raises it by one and a pop lowers it, so the
  carried value is at most `stage2StackExtent`.  It is not `519`: that is the
  `MAXD` check's bound, the *arm's* guard, and a push at `519` carries `520` out
  of `if.end24.i` — the check is what refuses the next push. -/
  depth_cap : C.sp ≤ stage2StackExtent
  /-- **The depth register at the carried block.**  `%sp.i.0248` is rebound only
  at the loop head's `phi`; every block of the dispatch reads it, and the merge at
  `cleanup478.i` moves the next value into `%sp.i.1` instead.  The clause is the
  depth's counterpart of `blockIndex`, and it is why an arm that leaves the depth
  alone carries it in one step. -/
  depth_reg : lookupName s.env "%sp.i.0248" = some (.int 32 (BitVec.ofNat 32 C.sp))
  /-- **The pointer registers the dispatch's blocks read.**  `while.body.i` reads
  `%3`, `%5` and `%k11.i`, and `if.end24.i` indexes `%ctype.i`/`%cst.i` and reads
  the log's hash word through `%hash1.i.i`; a block's `denoteCode` needs those
  bindings before its edge can be a step, and the invariant names them at the
  addresses the staging fixed (`WalkPtrs`). -/
  ptrs : WalkPtrs G C s.env
  /-- **The log's hash word is the initialisation's zero.**  `if.end24.i` reads
  the four bytes at `%z + 32` (`%10 = load i32, ptr %hash1.i.i`) and branches on
  the word: `entry`'s `llvm.memset` over the sixteen bytes at `%z + 24` is what
  makes it zero, and no block of the walk writes that half of the hash state —
  `if.then.i.i` writes `%z + 24` only.  This is the one clause the two container
  stacks' push path reads from memory, and it is what makes the block's branch a
  *fact* rather than an assumed guard. -/
  log_hash : readBytes s.mem (C.stage.z + 32) 4 = some (natToBytes 0 4)
  /-- **The log's event length is the carried event cursor.**  `out_reserve`'s
  check reads the word at `%z + 8` (`%len`) against the word at `%z + 16`, and the
  walk's event writes advance it by the record's own width — one, nine or
  thirteen, the sum `evlen_eq` names; the staging fixes the field at `%z + 8`, so
  the reserve is about the cursor the carry names rather than about an unread
  word.  The `gep` is `JsonStage2IR`'s (`entry`'s `%len = %z + 8`). -/
  log_len : readBytes s.mem (C.stage.z + 8) 8 = some (wordBytes 8 C.evlen)
  /-- **The log's event capacity is the staged one** (the word at `%z + 16`,
  `%cap`). -/
  log_cap : readBytes s.mem (C.stage.z + 16) 8 = some (wordBytes 8 G.evcap)
  /-- **The log's arena cursor is the carried arena cursor.**  `z_arena_reserve`
  reads the word at `%z + 48` (`%alen`) and adds the body's length and the
  decoder's slack to it; `if.end256.i` compares that sum against `%z + 56`. -/
  log_alen : readBytes s.mem (C.stage.z + 48) 8 = some (wordBytes 8 C.alen)
  /-- **The log's arena capacity is the staged one** (the word at `%z + 56`,
  `%acap`).  With `log_alen` this is the clause `if.end256.i` needs: the word the
  reserve compares against is `dstcap`, not an unconstrained memory cell. -/
  log_acap : readBytes s.mem (C.stage.z + 56) 8 = some (wordBytes 8 G.dstcap)
  /-- **Presence over the objects the caller staged**, at the extents it staged
  them (`walkStaged`): the arena's window, the two cursor slots, the refusal slot,
  the seven appended objects and `%d.i`'s slot.  Every extent is a constant of the
  geometry, so a step carries this clause with one monotonicity: a store only adds
  cells.

  The four stack objects are deliberately absent.  Their bytes are written by the
  helper calls, and nothing makes them present before that, so a presence claim
  over them is false at the loop head — which is exactly why the claim below is
  silence and not ownership. -/
  owned : ∀ r ∈ walkStaged G C, HasBytes s.mem r.1 r.2
  /-- **Silence outside the region the walk writes** (`walkWide`): the arena's
  decoded prefix and the event stream's prefix at the carried cursors, the seven
  appended objects, `%d.i`, and the body's four stack slots at `G.next0`.

  The list is the run's whole touched extent, and it grows with the cursors: a
  store into the arena or the event stream at the new cursor is inside it.  The
  four stack slots are in it because the helpers store through them — a claim
  that stopped at the seven was false of `s2_init`, `s2_string_body` and
  `num_fast_el1` — and they are *fresh* by `G.watermark`, which is what lets the
  document's and the entry stream's reads below conclude a byte outside this
  whole list.

  This is the half the report's frame reads (`stage2ReportFrame`), and the half
  the two prefix reads read; nothing else consumes it. -/
  frame : UnchangedOutside m0 s.mem (walkWide G C)
  /-- The block-local facts the measure is read from. -/
  blockLocal : WalkLocal C s

namespace WalkInv

variable {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}

/-- The arena's bound, from the carried extents: this is
`Stage2SpansInside`'s content and `arenaLe_of_spans`'s conclusion, so the report's
`alen ≤ ndst0 + n` is downstream of the carry rather than assumed. -/
theorem alen_le (h : WalkInv G C s) : C.alen ≤ G.ndst0 + G.n :=
  arenaLe_of_spans h.spans_order h.spans_inside h.alen_le_sum

/-- The event cursor's bound, from the trace's widths, one record per entry and the
entry count: the width sum is at most thirteen times the trace's length, and the
length is at most the entries consumed. -/
theorem evlen_le (h : WalkInv G C s) : C.evlen ≤ G.nev0 + stage2RecordBytes * G.n := by
  have hsum := EventRecord.sum_encodedSize_le C.events
  have hlen : C.events.length ≤ G.n :=
    le_trans h.events_le (le_trans h.k_le G.nep_le)
  have hmul : stage2RecordBytes * C.events.length ≤ stage2RecordBytes * G.n :=
    Nat.mul_le_mul_left _ hlen
  rw [h.evlen_eq]
  omega

/-- The block-local facts at the latch: the invariant implies them, and the arm's
lemma takes them explicitly so its `WalkInv` hypothesis is not unpacked twice. -/
theorem forInc {h : WalkInv G C s} (hblock : C.block = "for.inc.i.i") :
    ∃ i c : Nat, c - i ≤ C.inner ∧ i < c ∧ c < 2 ^ 64 ∧
      lookupName s.env "%i.029.i.i" = some (.int 64 (BitVec.ofNat 64 i)) ∧
      lookupName s.env "%cond.i.i" = some (.int 64 (BitVec.ofNat 64 c)) := by
  simpa [WalkLocal, hblock] using h.blockLocal

end WalkInv

/-! ### The seed: the invariant at the loop head

The seed is not a step but a value: at the loop head the dispatch has not run, so
the carry's `inner` is the whole allowance, not a reading of a register.  The
state it is read at is what the initialisation hands the loop — the header's
`phi` selecting the first position, and the staged cursors — and
`WalkSeedState`'s three clauses are exactly that handoff.  The region claim is a
seed hypothesis rather than a consequence of `WalkGeom`, and that is the
initialisation's first obligation: see *The entry loop's first obligation*. -/

/-- The loop head's carry: the initial entry index, the staged cursors, no
records, no extents, no record in flight, no refusal, no nesting depth, and the
whole dispatch's inner allowance. -/
def walkSeed {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) : WalkCarry G where
  k := 0
  alen := G.ndst0
  evlen := G.nev0
  events := []
  spans := []
  pending := none
  refusal := false
  eoff := 0
  block := "NodeBlock21"
  inner := walkInnerCap G
  sp := 0
  stage := S

/-- The state the initialisation hands the loop: the header's block after its two
`phi`s selected the first entry position and the empty nesting, the two cursors
as the caller staged them, and the log's four fields as the staging fixed them
(the initialisation's `entry` stores `z->ev.b/len/cap` and `z->ar/alen/acap`). -/
def WalkSeedState {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State) : Prop :=
  s.pc = "NodeBlock21" ∧
    lookupName s.env "%k.0.i249" = some (.int 64 (BitVec.ofNat 64 0)) ∧
    lookupName s.env "%sp.i.0248" = some (.int 32 (BitVec.ofNat 32 0)) ∧
    WalkPtrs G (walkSeed G S) s.env ∧
    readBytes s.mem (S.z + 32) 4 = some (natToBytes 0 4) ∧
    (∀ r ∈ walkStaged G (walkSeed G S), HasBytes s.mem r.1 r.2) ∧
    UnchangedOutside m0 s.mem (walkWide G (walkSeed G S)) ∧
    readBytes s.mem (S.z + 8) 8 = some (wordBytes 8 G.nev0) ∧
    readBytes s.mem (S.z + 16) 8 = some (wordBytes 8 G.evcap) ∧
    readBytes s.mem (S.z + 48) 8 = some (wordBytes 8 G.ndst0) ∧
    readBytes s.mem (S.z + 56) 8 = some (wordBytes 8 G.dstcap)

/-- **The cap at the seed is the allowance itself**, so the clause that the outer
arm's strictness reads is satisfied by construction rather than by a register
bound. -/
theorem walkSeed_inner_cap {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) :
    (walkSeed G S).inner ≤ walkInnerCap G :=
  Nat.le_refl _

/-- **The depth at the seed is zero, and zero indexes the stacks.**  The loop
head's `phi` takes the constant `0` from `while.body.i.lr.ph`, which is
`WalkSeedState`'s third clause; the capacity clause is the stacks' extent. -/
theorem walkSeed_depth_cap {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) :
    (walkSeed G S).sp ≤ stage2StackExtent := by
  simp [walkSeed, stage2StackExtent]

/-- **The invariant at the loop head.**  `walkSeed` satisfies every clause of
`WalkInv` at a `WalkSeedState`, so the seed's production is the initialisation's
facts and nothing else. -/
theorem walkSeed_invariant {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) {s : State}
    (h : WalkSeedState G S s) : WalkInv G (walkSeed G S) s := by
  obtain ⟨hpc, hk, hsp, hptrs, hhash, hown, hframe, hlen, hcap, halen, hacap⟩ := h
  refine
    { pc_eq := hpc
      blockIndex := hk
      k_le := Nat.zero_le _
      events_le := Nat.zero_le _
      evlen_eq := by simp [walkSeed]
      evBytes := rfl
      alen_le_sum := by simp [walkSeed]
      alen_ge := Nat.le_refl _
      spans_order := by simp [walkSeed]
      spans_inside := by simp [walkSeed]
      pending_at := ?_
      pending_cursor := ?_
      pending_len := ?_
      eoff_le := Nat.zero_le _
      inner_cap := walkSeed_inner_cap G S
      depth_cap := walkSeed_depth_cap G S
      depth_reg := hsp
      ptrs := hptrs
      log_hash := hhash
      log_len := hlen
      log_cap := hcap
      log_alen := halen
      log_acap := hacap
      owned := hown
      frame := hframe
      blockLocal := ?_ }
  · intro p off len hp
    simp [walkSeed] at hp
  · intro p off len hp
    simp [walkSeed] at hp
  · intro p off len hp
    simp [walkSeed] at hp
  · simp [WalkLocal, walkSeed]

/-! ### The measure -/

/-- **The measure**, as one `Nat`: the remaining entries radix the remaining inner
budget.  The outer term decreases by at least one per entry; the inner term by
exactly one per inner iteration; the radix is `cap + 1` so an outer step is strict
even when the inner component is refilled to its cap. -/
def walkMeasure {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) : Nat :=
  (G.nep - C.k) * (walkInnerCap G + 1) + C.inner

/-- The latch's own guard: the exit test is false, so the back edge — not
`for.end.i.i` — is the one the latch takes.  It is the only fact the arm needs
beside the invariant, because the invariant's block-local clause is what names the
registers the guard is about. -/
def ForIncGuard {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) : Prop :=
  ∃ i c : Nat, c - i ≤ C.inner ∧ i + 1 < c ∧ c < 2 ^ 64 ∧
    lookupName s.env "%i.029.i.i" = some (.int 64 (BitVec.ofNat 64 i)) ∧
    lookupName s.env "%cond.i.i" = some (.int 64 (BitVec.ofNat 64 c))

/-! ### The arm: `for.inc.i.i → for.body.i.i` -/

/-- The latch: `%inc.i.i = %i.029.i.i + 1`, the exit test `eq %inc.i.i,
%cond.i.i`, and the back edge to the header.  Two instructions, no memory. -/
def forIncBlock : Block :=
  { name := "for.inc.i.i",
    instrs := [
      Instr.binop "%inc.i.i" BinOp.add 64 (Operand.reg "%i.029.i.i")
        (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.icmp "%exitcond.not.i.i" IPred.eq 64 (Operand.reg "%inc.i.i")
        (Operand.reg "%cond.i.i")],
    term := Term.condbr (Operand.reg "%exitcond.not.i.i") "for.end.i.i" "for.body.i.i" }

/-- The latch is the pinned body's block: the arm's proof is about `stage2Body`,
not about a transcription of it. -/
theorem forInc_find : stage2Body.findBlock "for.inc.i.i" = some forIncBlock := by
  simp [stage2Body, Function.findBlock, findBlockList, forIncBlock]

/-- `%d = add i64 %a, 1` at the state's own environment.  `BlockEval`'s step is
stated at `stateAt env s`; this is the same step at `s`, which is the shape the
arm's state has. -/
theorem denoteCode_add_one (calls : Calls) (s : State) (d a : String) {x : BitVec 64}
    (ha : lookupName s.env a = some (.int 64 x)) (is : List Instr) :
    denoteCode calls (.binop d .add 64 (.reg a) (.imm (.int 64 (BitVec.ofNat 64 1))) :: is) s =
      denoteCode calls is (s.bind d (.int 64 (x + BitVec.ofNat 64 1))) := by
  simpa only [stateAt, State.bind] using
    (denoteCode_add_imm (calls := calls) (env := s.env) (s := s) (d := d) (a := a)
      (x := x) (c := BitVec.ofNat 64 1) ha is)

/-- `%d = icmp eq i64 %a, %b` at the state's own environment. -/
theorem denoteCode_icmp_eq (calls : Calls) (s : State) (d a b : String) {x y : BitVec 64}
    (ha : lookupName s.env a = some (.int 64 x))
    (hb : lookupName s.env b = some (.int 64 y)) (is : List Instr) :
    denoteCode calls (.icmp d .eq 64 (.reg a) (.reg b) :: is) s =
      denoteCode calls is (s.bind d (.int 1 (evalICmp .eq x y))) := by
  simpa only [stateAt, State.bind] using
    (denoteCode_icmp_eq_reg (calls := calls) (env := s.env) (s := s) (d := d) (a := a)
      (b := b) (x := x) (y := y) ha hb is)

/-- One step of the latch, at the state its back edge carries. -/
theorem forInc_denote {calls : Calls} (s : State) (i c : Nat)
    (hi : lookupName s.env "%i.029.i.i" = some (.int 64 (BitVec.ofNat 64 i)))
    (hc : lookupName s.env "%cond.i.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hlt : i + 1 < c) (hcw : c < 2 ^ 64) :
    denoteCode calls
      [Instr.binop "%inc.i.i" BinOp.add 64 (Operand.reg "%i.029.i.i")
         (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
       Instr.icmp "%exitcond.not.i.i" IPred.eq 64 (Operand.reg "%inc.i.i")
         (Operand.reg "%cond.i.i")] s =
      some (s.bind "%inc.i.i" (.int 64 (BitVec.ofNat 64 (i + 1)))
            |>.bind "%exitcond.not.i.i" (.int 1 (0 : BitVec 1))) := by
  rw [denoteCode_add_one calls s "%inc.i.i" "%i.029.i.i" (x := BitVec.ofNat 64 i) hi]
  rw [denoteCode_icmp_eq calls
      (s.bind "%inc.i.i" (.int 64 (BitVec.ofNat 64 i + BitVec.ofNat 64 1)))
      "%exitcond.not.i.i" "%inc.i.i" "%cond.i.i"
      (x := BitVec.ofNat 64 i + BitVec.ofNat 64 1) (y := BitVec.ofNat 64 c)
      (by simp only [State.bind, lookupName_cons_self])
      (by
        simp only [State.bind]
        rw [lookupName_cons_ne _ _ (by decide)]
        exact hc)]
  have hadd : BitVec.ofNat 64 i + BitVec.ofNat 64 1 = BitVec.ofNat 64 (i + 1) := by
    rw [← BitVec.ofNat_add (n := 64) i 1]
  have hne : BitVec.ofNat 64 (i + 1) ≠ BitVec.ofNat 64 c := by
    intro heq
    have h1 : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by
      rw [BitVec.toNat_ofNat]
      omega
    have h2 : (BitVec.ofNat 64 c).toNat = c := by
      rw [BitVec.toNat_ofNat]
      omega
    rw [heq, h2] at h1
    omega
  simp only [hadd]
  rw [show evalICmp IPred.eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c) = 0 from
    (evalICmp_eq_zero_iff _ _).mpr hne]
  simp only [denoteCode, denoteRun, State.bindAll]

/-- The latch's terminator: at a clear exit test it jumps to the header and
records the latch as the predecessor. -/
theorem forInc_term {calls : Calls} (s : State) (i c : Nat)
    (hpc : s.pc = "for.inc.i.i")
    (hi : lookupName s.env "%i.029.i.i" = some (.int 64 (BitVec.ofNat 64 i)))
    (hc : lookupName s.env "%cond.i.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hlt : i + 1 < c) (hcw : c < 2 ^ 64) :
    step calls stage2Body s =
      .jump { (s.bind "%inc.i.i" (.int 64 (BitVec.ofNat 64 (i + 1)))).bind
                "%exitcond.not.i.i" (.int 1 (0 : BitVec 1)) with
              pc := "for.body.i.i"
              pre := some "for.inc.i.i" } := by
  simp only [step, hpc, forInc_find, forIncBlock]
  rw [forInc_denote s i c hi hc hlt hcw]
  dsimp only
  rw [execTerm_condbr_zero _ _ _ _ _
      (by simp only [State.bind, evalOperand, lookupName_cons_self]) rfl]
  simp only [State.bind, hpc]

/-- **The smallest arm.**  From the invariant at the latch, one control step
reaches the header with the invariant preserved and the measure strictly smaller:
`k` is unchanged and the inner component goes from `c - i` to `c - (i + 1)`.

This is the feasibility test the scope asks for: the invariant is preserved field
for field (the block, the index, the cursors, the extents, the record in flight,
the refusal offset, the memory claim, and the local facts at the landing block),
and the measure's decrease is the arm's own arithmetic, not a hypothesis. -/
theorem forInc_step {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (i c : Nat)
    (hInv : WalkInv G C s) (hblock : C.block = "for.inc.i.i")
    (hi : lookupName s.env "%i.029.i.i" = some (.int 64 (BitVec.ofNat 64 i)))
    (hc : lookupName s.env "%cond.i.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hinner : c - i ≤ C.inner) (hlt : i + 1 < c) (hcw : c < 2 ^ 64) :
    ∃ (e : State) (C' : WalkCarry G),
      step calls stage2Body s = .jump e ∧
      WalkInv G C' e ∧
      C'.block = "for.body.i.i" ∧
      walkMeasure G C' < walkMeasure G C ∧
      ∀ k, runFuel calls (1 + k) stage2Body s = runFuel calls k stage2Body e := by
  -- the landing state and the carried data one inner iteration later
  let e : State :=
    { s.bind "%inc.i.i" (.int 64 (BitVec.ofNat 64 (i + 1)))
      |>.bind "%exitcond.not.i.i" (.int 1 (0 : BitVec 1)) with
      pc := "for.body.i.i"
      pre := some "for.inc.i.i" }
  let C' : WalkCarry G := { C with block := "for.body.i.i", inner := C.inner - 1 }
  have hpc : s.pc = "for.inc.i.i" := by rw [hInv.pc_eq, hblock]
  have hstep : step calls stage2Body s = .jump e := forInc_term s i c hpc hi hc hlt hcw
  have hk : lookupName e.env "%k.0.i249" = lookupName s.env "%k.0.i249" := by
    dsimp only [e, State.bind]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
  have hsp : lookupName e.env "%sp.i.0248" = lookupName s.env "%sp.i.0248" := by
    dsimp only [e, State.bind]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
  refine ⟨e, C', hstep, ?_, rfl, ?_, ?_⟩
  · refine
      { pc_eq := rfl
        blockIndex := by rw [hk]; exact hInv.blockIndex
        k_le := hInv.k_le
        events_le := hInv.events_le
        evlen_eq := hInv.evlen_eq
        evBytes := hInv.evBytes
        alen_le_sum := hInv.alen_le_sum
        alen_ge := hInv.alen_ge
        spans_order := hInv.spans_order
        spans_inside := hInv.spans_inside
        pending_at := hInv.pending_at
        pending_cursor := hInv.pending_cursor
        pending_len := hInv.pending_len
        eoff_le := hInv.eoff_le
        inner_cap := by
          show C.inner - 1 ≤ walkInnerCap G
          have := hInv.inner_cap
          omega
        depth_cap := hInv.depth_cap
        depth_reg := by rw [hsp]; exact hInv.depth_reg
        ptrs := by
          dsimp only [e, State.bind]
          exact hInv.ptrs.bind_pair
            (a := "%inc.i.i") (b := "%exitcond.not.i.i")
            ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
            ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
        log_hash := by dsimp only [e]; exact hInv.log_hash
        log_len := hInv.log_len
        log_cap := hInv.log_cap
        log_alen := hInv.log_alen
        log_acap := hInv.log_acap
        owned := hInv.owned
        frame := hInv.frame
        blockLocal := ?_ }
    dsimp only [WalkLocal, C']
    rw [if_neg (by decide), if_pos rfl]
    refine Or.inl ⟨i + 1, c, ?_, hlt, hcw, rfl, ?_⟩
    · show c - (i + 1) ≤ C.inner - 1
      omega
    dsimp only [e, State.bind]
    refine ⟨?_, ?_⟩
    · rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
    · rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      exact hc
  · dsimp only [walkMeasure, C']
    exact Nat.add_lt_add_left (by omega) _
  · intro k
    rw [show 1 + k = k + 1 from by omega]
    simp only [runFuel, hstep]

/-- **The arm at its front door.**  Beside `WalkInv` the only hypothesis is the
latch's guard: no register read and no counter value is assumed.  The guard's
`i + 1 < c` is what `forInc_step` turns into the branch and the decrease. -/
theorem forInc_arm {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "for.inc.i.i")
    (hguard : ForIncGuard C s) :
    ∃ (e : State) (C' : WalkCarry G),
      step calls stage2Body s = .jump e ∧
      WalkInv G C' e ∧
      C'.block = "for.body.i.i" ∧
      walkMeasure G C' < walkMeasure G C ∧
      ∀ k, runFuel calls (1 + k) stage2Body s = runFuel calls k stage2Body e := by
  obtain ⟨i, c, hinner, hlt, hcw, hi, hc⟩ := hguard
  exact forInc_step G C s i c hInv hblock hi hc hinner hlt hcw

/-! ### The four scans

Each scan's back edge has the same shape, and it is the smallest shape in the
body after the literal comparison: a latch that steps a counter by one, tests it
for equality against the scan's own bound, and — when the test is clear — jumps
back to the block that holds the counter's `phi`.  `while.body370.i → land.rhs.i`
(the whitespace skip), `while.body.i104 → land.rhs.i103` (the string scan),
`while.body76.i → land.rhs71.i` (the escape scan) and `while.body462.i →
land.rhs457.i` (the extra-token scan) are that block at four sets of names.

They read staged memory — each landing block loads a document byte — but none
writes it, so the memory claim is carried through unchanged, and the step is the
two instructions at the state's own environment.  The measure's outer factor is
the same on both sides because `k` is not read; the inner component falls by one.
-/

/-- A scan's latch, as a block: the counter steps by one, the bound is tested for
equality, and a clear test takes the back edge to `land`.  The `exit` arm is what
the test takes when the counter reaches the bound, and it is a different block in
each scan, so both successors are the edge's names. -/
def scanBlock (src inc phi test cond exit land : String) : Block :=
  { name := src,
    instrs := [
      Instr.binop inc BinOp.add 64 (Operand.reg phi)
        (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.icmp test IPred.eq 64 (Operand.reg inc) (Operand.reg cond)],
    term := Term.condbr (Operand.reg test) exit land }

/-- The whitespace skip's latch is the pinned body's block. -/
theorem scanWhitespace_find :
    stage2Body.findBlock "while.body370.i" =
      some (scanBlock "while.body370.i" "%inc371.i" "%ee.0.i238" "%exitcond.not"
        "%cond350.i" "if.end372.i" "land.rhs.i") := by
  simp [stage2Body, Function.findBlock, findBlockList, scanBlock]

/-- The string scan's latch is the pinned body's block. -/
theorem scanString_find :
    stage2Body.findBlock "while.body.i104" =
      some (scanBlock "while.body.i104" "%inc.i105" "%ee.011.i" "%exitcond.not.i"
        "%cond.i" "cleanup474.i" "land.rhs.i103") := by
  simp [stage2Body, Function.findBlock, findBlockList, scanBlock]

/-- The escape scan's latch is the pinned body's block. -/
theorem scanEscape_find :
    stage2Body.findBlock "while.body76.i" =
      some (scanBlock "while.body76.i" "%inc77.i" "%s2.020.i" "%exitcond24.not.i"
        "%cond.i" "while.end78.i" "land.rhs71.i") := by
  simp [stage2Body, Function.findBlock, findBlockList, scanBlock]

/-- The extra-token scan's latch is the pinned body's block. -/
theorem scanExtraToken_find :
    stage2Body.findBlock "while.body462.i" =
      some (scanBlock "while.body462.i" "%inc463.i" "%q.0.i246" "%exitcond298.not"
        "%cond350.i" "if.end473.i" "land.rhs457.i") := by
  simp [stage2Body, Function.findBlock, findBlockList, scanBlock]

/-- The landing block's leading `phi`, read out of the pinned body, and the
operand it selects from the latch.  The outer `none` is a missing block or a
first instruction that is not a `phi`; the inner one is a predecessor the block
does not list.  The `#guard`s below are the instrument: each evaluates the body,
so a landing fact written for a predecessor or an increment the body does not
list fails at elaboration instead of being assumed. -/
def scanLandSelect (land src : String) : Option (Option Operand) :=
  match stage2Body.findBlock land with
  | none => none
  | some b =>
      match b.instrs.head? with
      | some (.phi _ _ inc) => some (phiIncoming src inc)
      | _ => none

-- The whitespace skip lands on a `phi` that selects `%inc371.i` from
-- `while.body370.i`.
#guard scanLandSelect "land.rhs.i" "while.body370.i" = some (some (.reg "%inc371.i"))

-- The string scan lands on a `phi` that selects `%inc.i105` from
-- `while.body.i104`.
#guard scanLandSelect "land.rhs.i103" "while.body.i104" = some (some (.reg "%inc.i105"))

-- The escape scan lands on a `phi` that selects `%inc77.i` from `while.body76.i`.
#guard scanLandSelect "land.rhs71.i" "while.body76.i" = some (some (.reg "%inc77.i"))

-- The extra-token scan lands on a `phi` that selects `%inc463.i` from
-- `while.body462.i`.
#guard scanLandSelect "land.rhs457.i" "while.body462.i" = some (some (.reg "%inc463.i"))

/-! #### `WalkLocal` at the scans' blocks

Each unfolding names the branch `WalkLocal` takes at that block, so an arm reads
its register facts from the invariant and writes the landing facts back into it
without unfolding the whole chain. -/

/-- `WalkLocal` at the whitespace skip's latch. -/
theorem WalkLocal.whitespace {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : C.block = "while.body370.i") :
    WalkLocal C s = ScanCount s "%ee.0.i238" "%cond350.i" C.inner := by
  simp [WalkLocal, h]

/-- `WalkLocal` at the whitespace skip's landing block. -/
theorem WalkLocal.whitespaceLanded {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (h : C.block = "land.rhs.i") :
    WalkLocal C s = (ScanLanded s "while.body370.i" "%inc371.i" "%cond350.i" C.inner ∨
      ScanEntered s "land.rhs.i.preheader" "%idxprom.i" "%cond350.i" C.inner) := by
  simp [WalkLocal, h]

/-- `WalkLocal` at the string scan's latch. -/
theorem WalkLocal.stringScan {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : C.block = "while.body.i104") :
    WalkLocal C s = ScanCount s "%ee.011.i" "%cond.i" C.inner := by
  simp [WalkLocal, h]

/-- `WalkLocal` at the string scan's landing block. -/
theorem WalkLocal.stringScanLanded {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (h : C.block = "land.rhs.i103") :
    WalkLocal C s = (ScanLanded s "while.body.i104" "%inc.i105" "%cond.i" C.inner ∨
      ScanEntered s "cond.end.i96" "%idxprom.i" "%cond.i" C.inner) := by
  simp [WalkLocal, h]

/-- `WalkLocal` at the escape scan's latch. -/
theorem WalkLocal.escape {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : C.block = "while.body76.i") :
    WalkLocal C s = ScanCount s "%s2.020.i" "%cond.i" C.inner := by
  simp [WalkLocal, h]

/-- `WalkLocal` at the escape scan's landing block. -/
theorem WalkLocal.escapeLanded {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : C.block = "land.rhs71.i") :
    WalkLocal C s = (ScanLanded s "while.body76.i" "%inc77.i" "%cond.i" C.inner ∨
      ScanEntered s "if.end67.i" "%ee.0.lcssa.i" "%cond.i" C.inner) := by
  simp [WalkLocal, h]

/-- `WalkLocal` at the extra-token scan's latch. -/
theorem WalkLocal.extraToken {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : C.block = "while.body462.i") :
    WalkLocal C s = ScanCount s "%q.0.i246" "%cond350.i" C.inner := by
  simp [WalkLocal, h]

/-- `WalkLocal` at the extra-token scan's landing block. -/
theorem WalkLocal.extraTokenLanded {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (h : C.block = "land.rhs457.i") :
    WalkLocal C s = (ScanLanded s "while.body462.i" "%inc463.i" "%cond350.i" C.inner ∨
      ScanEntered s "if.then447.i" "%ee.1.i" "%cond350.i" C.inner) := by
  simp [WalkLocal, h]

/-- The whitespace skip's register facts, out of the invariant. -/
theorem WalkInv.whitespace {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkInv G C s) (hblock : C.block = "while.body370.i") :
    ScanCount s "%ee.0.i238" "%cond350.i" C.inner := by
  simpa [WalkLocal.whitespace hblock] using h.blockLocal

/-- The string scan's register facts, out of the invariant. -/
theorem WalkInv.stringScan {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkInv G C s) (hblock : C.block = "while.body.i104") :
    ScanCount s "%ee.011.i" "%cond.i" C.inner := by
  simpa [WalkLocal.stringScan hblock] using h.blockLocal

/-- The escape scan's register facts, out of the invariant. -/
theorem WalkInv.escape {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkInv G C s) (hblock : C.block = "while.body76.i") :
    ScanCount s "%s2.020.i" "%cond.i" C.inner := by
  simpa [WalkLocal.escape hblock] using h.blockLocal

/-- The extra-token scan's register facts, out of the invariant. -/
theorem WalkInv.extraToken {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkInv G C s) (hblock : C.block = "while.body462.i") :
    ScanCount s "%q.0.i246" "%cond350.i" C.inner := by
  simpa [WalkLocal.extraToken hblock] using h.blockLocal

/-! #### The scans' steps -/

/-- A scan's step, at the state's own environment: the counter increments and the
bound is tested for equality.  The equality is false because the counter is still
short of the bound, so the latch's test is clear and its back edge is the edge it
takes. -/
theorem scan_denote (calls : Calls) (s : State) (inc phi test cond : String) (i c : Nat)
    (hinc_cond : inc ≠ cond)
    (hi : lookupName s.env phi = some (.int 64 (BitVec.ofNat 64 i)))
    (hc : lookupName s.env cond = some (.int 64 (BitVec.ofNat 64 c)))
    (hlt : i + 1 < c) (hcw : c < 2 ^ 64) :
    denoteCode calls
      [Instr.binop inc BinOp.add 64 (Operand.reg phi)
         (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
       Instr.icmp test IPred.eq 64 (Operand.reg inc) (Operand.reg cond)] s =
      some ((s.bind inc (.int 64 (BitVec.ofNat 64 (i + 1)))).bind
        test (.int 1 (0 : BitVec 1))) := by
  rw [denoteCode_add_one calls s inc phi (x := BitVec.ofNat 64 i) hi]
  rw [denoteCode_icmp_eq calls
      (s.bind inc (.int 64 (BitVec.ofNat 64 i + BitVec.ofNat 64 1)))
      test inc cond
      (x := BitVec.ofNat 64 i + BitVec.ofNat 64 1) (y := BitVec.ofNat 64 c)
      (by simp only [State.bind, lookupName_cons_self])
      (by
        simp only [State.bind]
        rw [lookupName_cons_ne _ _ hinc_cond]
        exact hc)]
  have hadd : BitVec.ofNat 64 i + BitVec.ofNat 64 1 = BitVec.ofNat 64 (i + 1) := by
    rw [← BitVec.ofNat_add (n := 64) i 1]
  have hne : BitVec.ofNat 64 (i + 1) ≠ BitVec.ofNat 64 c := by
    intro heq
    have h1 : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by
      rw [BitVec.toNat_ofNat]
      omega
    have h2 : (BitVec.ofNat 64 c).toNat = c := by
      rw [BitVec.toNat_ofNat]
      omega
    rw [heq, h2] at h1
    omega
  simp only [hadd]
  rw [show evalICmp IPred.eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c) = 0 from
    (evalICmp_eq_zero_iff _ _).mpr hne]
  simp only [denoteCode, denoteRun, State.bindAll]

/-- A scan's terminator: a clear test jumps to the landing block, binding the
increment and naming the latch as the predecessor. -/
theorem scan_term {calls : Calls} (s : State) (i c : Nat)
    (src land phi inc test cond exit : String)
    (hpc : s.pc = src)
    (hfind : stage2Body.findBlock src = some (scanBlock src inc phi test cond exit land))
    (hinc_cond : inc ≠ cond)
    (hi : lookupName s.env phi = some (.int 64 (BitVec.ofNat 64 i)))
    (hc : lookupName s.env cond = some (.int 64 (BitVec.ofNat 64 c)))
    (hlt : i + 1 < c) (hcw : c < 2 ^ 64) :
    step calls stage2Body s =
      .jump { ((s.bind inc (.int 64 (BitVec.ofNat 64 (i + 1)))).bind
                test (.int 1 (0 : BitVec 1))) with
              pc := land
              pre := some src } := by
  simp only [step, hpc, hfind, scanBlock]
  rw [scan_denote calls s inc phi test cond i c hinc_cond hi hc hlt hcw]
  dsimp only
  rw [execTerm_condbr_zero _ _ _ _ _
      (by simp only [State.bind, evalOperand, lookupName_cons_self]) rfl]
  simp only [State.bind, hpc]

/-- **A scan's arm.**  From the invariant at a scan's latch, one control step
reaches that scan's landing block with every carried field preserved, the extents
and the memory untouched, and the measure strictly smaller: `k` is unchanged, so
the outer factor is the same, and the inner component falls from `c - i` to
`c - (i + 1)`.

The landing block's local facts are the last hypothesis' content: the caller
supplies them from the landing block's own `WalkLocal` branch, so the arm is
about the block the body jumps to and not about an assumed landing. -/
theorem scan_step {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (i c : Nat) (src land phi inc test cond exit : String)
    (hInv : WalkInv G C s) (hblock : C.block = src)
    (hfind : stage2Body.findBlock src = some (scanBlock src inc phi test cond exit land))
    (hinc_cond : inc ≠ cond) (htest_cond : test ≠ cond) (htest_inc : test ≠ inc)
    (hinc_k : inc ≠ "%k.0.i249") (htest_k : test ≠ "%k.0.i249")
    (hinc_sp : inc ≠ "%sp.i.0248") (htest_sp : test ≠ "%sp.i.0248")
    (hincN : ¬ inc = "%3" ∧ ¬ inc = "%5" ∧ ¬ inc = "%k11.i" ∧ ¬ inc = "%ctype.i"
      ∧ ¬ inc = "%cst.i" ∧ ¬ inc = "%hash1.i.i")
    (htestN : ¬ test = "%3" ∧ ¬ test = "%5" ∧ ¬ test = "%k11.i" ∧ ¬ test = "%ctype.i"
      ∧ ¬ test = "%cst.i" ∧ ¬ test = "%hash1.i.i")
    (hi : lookupName s.env phi = some (.int 64 (BitVec.ofNat 64 i)))
    (hc : lookupName s.env cond = some (.int 64 (BitVec.ofNat 64 c)))
    (hinner : c - i ≤ C.inner) (hlt : i + 1 < c) (hcw : c < 2 ^ 64)
    (hland : ∀ (e : State), e.pre = some src →
      lookupName e.env inc = some (.int 64 (BitVec.ofNat 64 (i + 1))) →
      lookupName e.env cond = some (.int 64 (BitVec.ofNat 64 c)) →
      WalkLocal (G := G) { C with block := land, inner := C.inner - 1 } e) :
    ∃ (e : State),
      step calls stage2Body s = .jump e ∧
      WalkInv G { C with block := land, inner := C.inner - 1 } e ∧
      walkMeasure G { C with block := land, inner := C.inner - 1 } < walkMeasure G C ∧
      ∀ k, runFuel calls (1 + k) stage2Body s = runFuel calls k stage2Body e := by
  have hpc : s.pc = src := by rw [hInv.pc_eq, hblock]
  let e : State :=
    { ((s.bind inc (.int 64 (BitVec.ofNat 64 (i + 1)))).bind
        test (.int 1 (0 : BitVec 1))) with
      pc := land
      pre := some src }
  have hstep : step calls stage2Body s = .jump e :=
    scan_term s i c src land phi inc test cond exit hpc hfind hinc_cond hi hc hlt hcw
  have hinc : lookupName e.env inc = some (.int 64 (BitVec.ofNat 64 (i + 1))) := by
    dsimp only [e, State.bind]
    rw [lookupName_cons_ne _ _ htest_inc, lookupName_cons_self]
  have hcond : lookupName e.env cond = some (.int 64 (BitVec.ofNat 64 c)) := by
    dsimp only [e, State.bind]
    rw [lookupName_cons_ne _ _ htest_cond, lookupName_cons_ne _ _ hinc_cond]
    exact hc
  have hk : lookupName e.env "%k.0.i249" = lookupName s.env "%k.0.i249" := by
    dsimp only [e, State.bind]
    rw [lookupName_cons_ne _ _ htest_k, lookupName_cons_ne _ _ hinc_k]
  have hsp : lookupName e.env "%sp.i.0248" = lookupName s.env "%sp.i.0248" := by
    dsimp only [e, State.bind]
    rw [lookupName_cons_ne _ _ htest_sp, lookupName_cons_ne _ _ hinc_sp]
  refine ⟨e, hstep, ?_, ?_, ?_⟩
  · refine
      { pc_eq := rfl
        blockIndex := ?_
        k_le := hInv.k_le
        events_le := hInv.events_le
        evlen_eq := hInv.evlen_eq
        evBytes := hInv.evBytes
        alen_le_sum := hInv.alen_le_sum
        alen_ge := hInv.alen_ge
        spans_order := hInv.spans_order
        spans_inside := hInv.spans_inside
        pending_at := hInv.pending_at
        pending_cursor := hInv.pending_cursor
        pending_len := hInv.pending_len
        eoff_le := hInv.eoff_le
        inner_cap := by
          show C.inner - 1 ≤ walkInnerCap G
          have := hInv.inner_cap
          omega
        depth_cap := hInv.depth_cap
        depth_reg := by rw [hsp]; exact hInv.depth_reg
        ptrs := by
          dsimp only [e, State.bind]
          exact hInv.ptrs.bind_pair (a := inc) (b := test) hincN htestN
        log_hash := by dsimp only [e]; exact hInv.log_hash
        log_len := hInv.log_len
        log_cap := hInv.log_cap
        log_alen := hInv.log_alen
        log_acap := hInv.log_acap
        owned := by dsimp only [e]; exact hInv.owned
        frame := ?_
        blockLocal := ?_ }
    · rw [hk]; exact hInv.blockIndex
    · dsimp only [e]; exact hInv.frame
    · exact hland e rfl hinc hcond
  · dsimp only [walkMeasure]
    exact Nat.add_lt_add_left (by omega) _
  · intro k
    rw [show 1 + k = k + 1 from by omega]
    simp only [runFuel, hstep]

/-! #### The four arms -/

/-- **The whitespace skip's back edge**, `while.body370.i → land.rhs.i`.  The
counter `%ee.0.i238` goes from `i` to `i + 1` and the test `%inc371.i =
%cond350.i` is clear because `i + 1 < c`; the measure keeps its outer factor and
loses one from the inner component. -/
theorem whitespace_scan {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "while.body370.i")
    (hguard : ScanGuard s "%ee.0.i238" "%cond350.i" C.inner) :
    ∃ (e : State) (C' : WalkCarry G),
      step calls stage2Body s = .jump e ∧
      WalkInv G C' e ∧ C'.block = "land.rhs.i" ∧
      walkMeasure G C' < walkMeasure G C ∧
      ∀ k, runFuel calls (1 + k) stage2Body s = runFuel calls k stage2Body e := by
  obtain ⟨i, c, hinner, -, hcw, hi, hc⟩ := WalkInv.whitespace hInv hblock
  have hnext : i + 1 < c := hguard i c hinner hi hc
  obtain ⟨e, hstep, hinv, hmeas, hrun⟩ :=
    scan_step G C s i c "while.body370.i" "land.rhs.i" "%ee.0.i238" "%inc371.i"
      "%exitcond.not" "%cond350.i" "if.end372.i" hInv hblock scanWhitespace_find
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (hincN := by decide) (htestN := by decide)
      hi hc hinner hnext hcw
      (by
        intro e hpre hinc hcond
        rw [WalkLocal.whitespaceLanded rfl]
        exact Or.inl ⟨i + 1, c, (by show c - (i + 1) ≤ C.inner - 1; omega), hnext, hcw, hpre, hinc, hcond⟩)
  exact ⟨e, _, hstep, hinv, rfl, hmeas, hrun⟩

/-- **The string scan's back edge**, `while.body.i104 → land.rhs.i103`.  The
counter `%ee.011.i` goes from `i` to `i + 1` and the test `%inc.i105 = %cond.i`
is clear because `i + 1 < c`; the latch's exit arm is `cleanup474.i` and it is not
the edge taken.  The measure keeps its outer factor and loses one from the inner
component. -/
theorem string_scan {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "while.body.i104")
    (hguard : ScanGuard s "%ee.011.i" "%cond.i" C.inner) :
    ∃ (e : State) (C' : WalkCarry G),
      step calls stage2Body s = .jump e ∧
      WalkInv G C' e ∧ C'.block = "land.rhs.i103" ∧
      walkMeasure G C' < walkMeasure G C ∧
      ∀ k, runFuel calls (1 + k) stage2Body s = runFuel calls k stage2Body e := by
  obtain ⟨i, c, hinner, -, hcw, hi, hc⟩ := WalkInv.stringScan hInv hblock
  have hnext : i + 1 < c := hguard i c hinner hi hc
  obtain ⟨e, hstep, hinv, hmeas, hrun⟩ :=
    scan_step G C s i c "while.body.i104" "land.rhs.i103" "%ee.011.i" "%inc.i105"
      "%exitcond.not.i" "%cond.i" "cleanup474.i" hInv hblock scanString_find
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (hincN := by decide) (htestN := by decide)
      hi hc hinner hnext hcw
      (by
        intro e hpre hinc hcond
        rw [WalkLocal.stringScanLanded rfl]
        exact Or.inl ⟨i + 1, c, (by show c - (i + 1) ≤ C.inner - 1; omega), hnext, hcw, hpre, hinc, hcond⟩)
  exact ⟨e, _, hstep, hinv, rfl, hmeas, hrun⟩

/-- **The escape scan's back edge**, `while.body76.i → land.rhs71.i`.  The counter
`%s2.020.i` goes from `i` to `i + 1` and the test `%inc77.i = %cond.i` is clear
because `i + 1 < c`; the measure keeps its outer factor and loses one from the
inner component. -/
theorem escape_scan {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "while.body76.i")
    (hguard : ScanGuard s "%s2.020.i" "%cond.i" C.inner) :
    ∃ (e : State) (C' : WalkCarry G),
      step calls stage2Body s = .jump e ∧
      WalkInv G C' e ∧ C'.block = "land.rhs71.i" ∧
      walkMeasure G C' < walkMeasure G C ∧
      ∀ k, runFuel calls (1 + k) stage2Body s = runFuel calls k stage2Body e := by
  obtain ⟨i, c, hinner, -, hcw, hi, hc⟩ := WalkInv.escape hInv hblock
  have hnext : i + 1 < c := hguard i c hinner hi hc
  obtain ⟨e, hstep, hinv, hmeas, hrun⟩ :=
    scan_step G C s i c "while.body76.i" "land.rhs71.i" "%s2.020.i" "%inc77.i"
      "%exitcond24.not.i" "%cond.i" "while.end78.i" hInv hblock scanEscape_find
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (hincN := by decide) (htestN := by decide)
      hi hc hinner hnext hcw
      (by
        intro e hpre hinc hcond
        rw [WalkLocal.escapeLanded rfl]
        exact Or.inl ⟨i + 1, c, (by show c - (i + 1) ≤ C.inner - 1; omega), hnext, hcw, hpre, hinc, hcond⟩)
  exact ⟨e, _, hstep, hinv, rfl, hmeas, hrun⟩

/-- **The extra-token scan's back edge**, `while.body462.i → land.rhs457.i`.  The
counter `%q.0.i246` goes from `i` to `i + 1` and the test `%inc463.i =
%cond350.i` is clear because `i + 1 < c`; the measure keeps its outer factor and
loses one from the inner component. -/
theorem extraToken_scan {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "while.body462.i")
    (hguard : ScanGuard s "%q.0.i246" "%cond350.i" C.inner) :
    ∃ (e : State) (C' : WalkCarry G),
      step calls stage2Body s = .jump e ∧
      WalkInv G C' e ∧ C'.block = "land.rhs457.i" ∧
      walkMeasure G C' < walkMeasure G C ∧
      ∀ k, runFuel calls (1 + k) stage2Body s = runFuel calls k stage2Body e := by
  obtain ⟨i, c, hinner, -, hcw, hi, hc⟩ := WalkInv.extraToken hInv hblock
  have hnext : i + 1 < c := hguard i c hinner hi hc
  obtain ⟨e, hstep, hinv, hmeas, hrun⟩ :=
    scan_step G C s i c "while.body462.i" "land.rhs457.i" "%q.0.i246" "%inc463.i"
      "%exitcond298.not" "%cond350.i" "if.end473.i" hInv hblock scanExtraToken_find
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (hincN := by decide) (htestN := by decide)
      hi hc hinner hnext hcw
      (by
        intro e hpre hinc hcond
        rw [WalkLocal.extraTokenLanded rfl]
        exact Or.inl ⟨i + 1, c, (by show c - (i + 1) ≤ C.inner - 1; omega), hnext, hcw, hpre, hinc, hcond⟩)
  exact ⟨e, _, hstep, hinv, rfl, hmeas, hrun⟩

/-! ### The exit

Both exit shapes store the walk's report to the caller's slots: `s2_walk.exit`
writes `ndst ← alen` and `nev ← evlen` and returns `1`; `if.then` writes the same
two and `err ← eoff` and returns `0`.  Those stores are the wrapper's and are
pinned in `JsonStage2IR`; `JsonStage2Body`'s `stage2Report` and
`stage2Run_boundary` are their effect.  What the exits read off the loop is the
report's clauses, and `WalkInv.report` is those clauses at the carry — the same
statement at both shapes, because the shapes differ in the wrapper's stores and
not in what the walk left.

The two clauses below that the invariant did not carry are `alen_ge` (the report's
`arenaGe`, the append-only half of the arena cursor) and, before this slice,
`inner_cap`.  Both are stated where their value is produced — the arena appends
and the loop head — and both are preserved by every arm that leaves the field
alone. -/

/-- A byte inside a present region is present. -/
theorem present_of_hasBytes {m : Mem} {a n x : Nat} (h : HasBytes m a n)
    (hlo : a ≤ x) (hhi : x < a + n) : present m x := by
  obtain ⟨vs, hvs⟩ := h
  have := LeanLLVM.readBytes_some_present m a n vs hvs (x - a) (by omega)
  simpa [show a + (x - a) = x by omega] using this

/-- **The report's clauses, read off the invariant.**  The seven numbers and the
two halves of the memory claim `Stage2Run` records from `arenaGe` onwards: both
cursors and their two-sided growth bounds, the last reserve's slack, the refusal
offset, presence at `stage2ReportPresent` (the extents the run leaves written), and
silence outside `stage2ReportFrame` (those extents plus the four stack objects).

Presence comes from `WalkInv.owned` by coverage: the staged extents the run
carries are the geometry's, and `alen ≤ ndst0 + n`, `evlen ≤ evcap` put the
report's two prefixes inside them.  Silence comes from `WalkInv.frame` by
`UnchangedOutside.of_covered`: every entry of the walk's list lies inside an entry
of the report's, which is the loosening a wider frame is. -/
theorem WalkInv.report {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkInv G C s) :
    G.ndst0 ≤ C.alen ∧
      C.alen ≤ G.ndst0 + G.n ∧
      G.nev0 ≤ C.evlen ∧
      C.evlen ≤ G.nev0 + stage2RecordBytes * G.n ∧
      C.alen + stage2ArenaReserve ≤ G.dstcap ∧
      C.eoff ≤ G.n ∧
      (∀ a, inRegions (stage2ReportPresent G.dst C.alen
        G.ev C.evlen G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst
        C.stage.tok C.stage.s C.stage.z C.stage.e C.stage.d) a → present s.mem a) ∧
      UnchangedOutside m0 s.mem
        (stage2ReportFrame G.dst C.alen G.ev C.evlen G.ndst
          G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok C.stage.s
          C.stage.z C.stage.e C.stage.d G.next0) := by
  have hle : C.alen ≤ G.ndst0 + G.n := h.alen_le
  have hev : C.evlen ≤ G.nev0 + stage2RecordBytes * G.n := h.evlen_le
  have hevcap : C.evlen ≤ G.evcap := le_trans hev G.evRoom
  have hstage : ∀ r ∈ walkStaged G C, HasBytes s.mem r.1 r.2 := h.owned
  have hroom := G.arenaRoom
  refine ⟨h.alen_ge, hle, ?_, hev, by omega, h.eoff_le, ?_, ?_⟩
  · rw [h.evlen_eq]
    exact Nat.le_add_right _ _
  · intro a ha
    obtain ⟨r, hr, hlo, hhi⟩ := ha
    have hcov : ∃ q ∈ walkStaged G C, q.1 ≤ a ∧ a < q.1 + q.2 := by
      simp only [stage2ReportPresent, stage2Writes, stage2ReportScratch] at hr
      rcases List.mem_append.mp hr with hr | hr
      · rcases List.mem_cons.mp hr with rfl | hr1
        · exact ⟨(G.dst, G.ndst0 + G.n + stage2ArenaReserve),
            by simp [walkStaged], by omega, by omega⟩
        · rcases List.mem_cons.mp hr1 with rfl | hr2
          · exact ⟨(G.ndst, 8), by simp [walkStaged], hlo, hhi⟩
          · rcases List.mem_cons.mp hr2 with rfl | hr3
            · exact ⟨(G.ev, G.evcap), by simp [walkStaged], hlo, by omega⟩
            · rcases List.mem_cons.mp hr3 with rfl | hr4
              · exact ⟨(G.nev, 8), by simp [walkStaged], hlo, hhi⟩
              · rcases List.mem_cons.mp hr4 with rfl | hnil
                · exact ⟨(G.err, 8), by simp [walkStaged], hlo, hhi⟩
                · exact absurd hnil (by simp)
      · exact ⟨r, by simp [walkStaged, stage2ReportScratch, hr], hlo, hhi⟩
    obtain ⟨q, hq, hqlo, hqhi⟩ := hcov
    exact present_of_hasBytes (hstage q hq) hqlo hqhi
  · refine UnchangedOutside.of_covered h.frame ?_
    intro r hr
    simp only [walkWide, stage2ReportFrame, stage2ReportPresent, stage2Writes,
      stage2ReportScratch] at hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · rcases List.mem_cons.mp hr with rfl | hr1
        · exact ⟨(G.dst, C.alen + stage2ArenaReserve),
            by simp [stage2ReportFrame, stage2ReportPresent, stage2Writes],
            le_rfl, by omega⟩
        · rcases List.mem_cons.mp hr1 with rfl | hnil
          · exact ⟨(G.ev, C.evlen),
              by simp [stage2ReportFrame, stage2ReportPresent, stage2Writes],
              le_rfl, le_rfl⟩
          · exact absurd hnil (by simp)
      · exact ⟨r, List.mem_append_left _ (List.mem_append_right _ hr), le_rfl, le_rfl⟩
    · exact ⟨r, List.mem_append_right _ hr, le_rfl, le_rfl⟩

/-! ### The loop's forward stores, and the region they need

The entry loop's arm is the dispatch: `while.body.i` reads the entry stream and the
document, the switch tree classifies the byte, and one of the arms assembles a
record or refuses.  The edge that closes the iteration is proved (`walkBack_step`:
the merge at `cleanup478.i`, its two `phi`s, the exit test, and the budget refill),
and the iteration's forward edges are not; the obstruction to those is not the
nesting state, either reserve, or a refusal path: it is the first store the loop
executes, before any of them.

`while.body.i` stores the advanced index to the caller's cursor record,
`store i64 %inc.i, %k11.i` with `%k11.i = %c.i + 32` (`while.body.i.lr.ph`'s
`gep`), and `if.end207.i` does the same for the two-entry advance.  The
initialisation writes the record's other fields (`%c.i + 0/8/16/24`, and
`%c.i + 1112` for `%e`), and the walk writes the two container stacks
`%ctype.i`/`%cst.i` at `%sp.i.0248`, the log's `%z + 0/8/16/24/40/48/56`, `%s`'s
three fields, `%e + 8`, and `%t352.i`.  None of those addresses is staged by
`WalkGeom`, which is `stage2Pre` unpacked, and `stage2Pre` names only the thirteen
ABI objects — the staging is at the adapter (`stage2StagedPre`), and the record's
frame at `stage2WalkWrites`; both are `JsonStage2Contract`'s, and the next
paragraphs say what they buy and what they cannot yet.

The invariant's region claim is the walk's frame, and the two paragraphs that
follow record what the widening cost and what it bought, because both were
record-level questions and neither was an arm's.

**The narrow claim, and why it was false.**  Before this widening the claim was
`Owns (inRegions [(dst, alen), (ev, evlen)])`.  `Owns`'s unchanged half is a
statement about *every address outside* the region, so a store outside it
contradicts the claim unless the bytes happen to agree —
`owns_writeBytes_outside` is that argument — and only a store whose whole range is
inside it is admitted (`owns_writeBytes_inside`).  The loop's first store is to
`%c.i + 32`, which is outside both extents in the emitted pipeline, where the
cursor record is an object of its own; nothing in `WalkGeom` places it inside
them, so the narrow claim was not preserved one step into the loop.  The seed's
claim failed the same way, one step earlier: `entry`'s own stores (`%s +
56/72/80`, `%z + 0/8/16/24/40/48/56`, `%c.i + 0/8/16/24/1112`, and the `memset`
over `%c.i + 40`) are to the same unstaged objects, which is why `WalkSeedState`
takes the claim as a hypothesis rather than deriving it.

**The split, and where it had to begin.**  Presence is monotone in its region
and silence is anti-monotone: an `Owns` claim over one list is not the claim
over another, so the two are carried separately (`WalkInv.owned` and
`WalkInv.frame`) and handed to the record as two clauses through `WalkInv.report`,
which feeds `Stage2Run`, which `stage2Run_boundary` turns into
`stage2Boundary`'s post.  The post is at the ABI's thirteen arguments and the
seven appended objects are the *body's* parameters, so the post is where they
become nameable: `stage2Boundary` now carries them as witnesses (their extents
are `stage2StagedWrites`, the numbers `JsonStage2IR`'s `lifetimeExtents` guards
read off the pinned AST) together with `DisjointRegions
(stage2StagedRegions …)`.  `Stage2Run` carries the same seven, the caller's two
count slots and that separation; `WalkInv.owned`/`WalkInv.frame` are the
record's two region clauses at the run's cursors; `WalkInv.report` gives them back
at `alen + 64` (`Stage2Run.walkPresent_of_written` and
`Stage2Run.walkFrame_of_written`, whose staging separation places the seven and
whose watermark places the four stack objects).  So the loop's stores at `%c.i +
32` (`while.body.i`, `if.end207.i`), at `%ctype.i[sp]`/`%cst.i[sp]` (`if.end24.i`),
at `%z + 0/8/16/24/40/48/56`, `%s + 56/72/80` and `%e + 8` all land inside the
claim, and `walkStaged_write`/`walkFrame_write_inside` admit them.  The two
forward stores are `WalkInv.frame_cursorK` and `WalkInv.frame_stack` below.
`WalkSeedState`'s own claim is widened the same way; it is the initialisation's
promise, and it is the one clause of the loop head that is a hypothesis rather
than a reading of `WalkGeom`.

**What the widening costs its consumers, and which clause is pending.**  The
pipeline's tail read "the two count slots and the two streams are unchanged" off
the post, and unchanged-outside-a-wider-region does not yield
unchanged-outside-a-narrower one.  Of its four transport pairs, the two streams
(`S.ep`, `S.xp`) follow from the post's staging separation, because both are
stage-2 *arguments* and the staging names them at the counts the call carried
(the post carries `nep < 2 ^ 64` and `nxp < 2 ^ 64` so its counts are the
arguments' words' values — `one word with two widths is one number`, the same
move the two capacities make).  The two count slots (`S.nk`, `S.nxp`) do not:
they are the pipeline's, not stage-2's arguments, and no clause of the record can
name them.  `PipelineDischarge.Stage2SlotKeeps` is that statement, taken as a
hypothesis and documented as the model's missing stack discipline; it is the
composite's only frame-wise conditional clause.  `JsonPipelineSpec.SigmaFrame` is
no longer a premise beside it: it is a *definition* now — a `CallerView` naming the
caller's thirteen regions, with the seven staged objects existentially bound — so
the finalisation derives it rather than assuming it.  An existential footprint
does not by itself say the document is untouched, which is the limit
`SigmaFrame`'s own docstring records.

**The nesting clause is carried.**  `WalkInv.depth_reg` names the register —
`%sp.i.0248` holds the carry's `sp` — and `WalkInv.depth_cap` bounds it by
`stage2StackExtent`, so `if.end24.i`'s two stack stores index inside their staged
extents.  The `519` of `if.end.i`'s `%cmp19.i` is the *arm's* guard (`NestGuard`),
not the invariant's bound: a push at `519` carries `520` out of `if.end24.i`, and
the check is what refuses the next push.  Every arm that touches the depth carries
it: the seed sets it to zero (`walkSeed_depth_cap`, and `WalkSeedState`'s third
clause is the loop head's `phi` reading `0`), the five proved arms leave it alone
and carry the register through their binds, and `walkBack_step` carries it across
`cleanup478.i`'s merge, which moves the next depth into `%sp.i.1` instead of
`%sp.i.0248`.  What the clause does not say is the stacks' *contents* — the
push/pop discipline `%ctype.i[i]`/`%cst.i[i]` and `s2_value_pos` maintain — because
that is the dispatch's, and the dispatch's forward edges are what remains.

Two structural facts about the edge are worth recording beside it.  First, the
header's leading `phi` rebinds `%k.0.i249` inside the block, not on the edge, so
the outer arm is the two-block step `cleanup478.i → while.body.i → NodeBlock21`:
the carry's `k` advances only when the header's own instructions run, which is why
the strict decrease is `walkMeasure_step`'s (the header's block) and not the
edge's.  Second, the header's `phi` takes `%k.2.i` from `cleanup478.i`, whose
incoming value is the dispatch's, so the edge's guard is that merge's own — the
carry does not record it, and the dispatch to `while.body.i` needs the ten
predecessors' register facts at `cleanup478.i`'s two `phi`s. -/

/-- A block's store destinations, in text order, with the stored types. -/
def storeTargets (f : Function) (name : String) : List (String × Ty) :=
  match f.findBlock name with
  | none => []
  | some b =>
      b.instrs.filterMap fun i =>
        match i with
        | .store ty _ (.reg p) => some (p, ty)
        | _ => none

/-- The base register and displacement of a named `gep` in a block: the address
the store above is computed from. -/
def gepDef (f : Function) (name dst : String) : Option (String × Nat) :=
  match f.findBlock name with
  | none => none
  | some b =>
      (b.instrs.filterMap fun i =>
        match i with
        | .gep d _ (.reg base) (.imm (.int _ off)) =>
            if d = dst then some (base, off.toNat) else none
        | _ => none).head?

-- The loop head's first write is the cursor record's `k` field, and the field is
-- `%c.i + 32`; the store is eight bytes wide.
#guard storeTargets stage2Body "while.body.i" = [("%k11.i", Ty.int 64)]
#guard gepDef stage2Body "while.body.i.lr.ph" "%k11.i" = some ("%c.i", 32)

-- The two-entry advance writes the same field with the same width.
#guard storeTargets stage2Body "if.end207.i" = [("%k11.i", Ty.int 64)]

-- The nesting arm's stores are the two container stacks, at the running depth.
#guard storeTargets stage2Body "if.end24.i" =
  [("%arrayidx30.i", Ty.int 8), ("%arrayidx32.i", Ty.int 8)]

-- The hash update and the event reserve's two stores, in the order the record
-- path reaches them.
#guard storeTargets stage2Body "if.then.i.i" = [("%h1.i.i.i51", Ty.int 64)]
#guard storeTargets stage2Body "out_reserve.exit.i.i" =
  [("%add.ptr.i.i", Ty.int 8), ("%len", Ty.int 64)]

/-- **A write whose whole range is inside the owned region preserves the region
claim.**  The unchanged half is about the addresses outside the region, so a range
inside it asks nothing of them — at an address below the range or above it the
bytes are untouched (`readByte_writeBytes_outside`) — and the presence half holds
of the written bytes because a write adds presence. -/
theorem owns_writeBytes_inside {P : Nat → Prop} {mem m : Mem} {w : Nat} {v : List UInt8}
    (h : Owns P mem m) (hw : ∀ k, k < v.length → P (w + k)) :
    Owns P mem (writeBytes m w v) := by
  refine ⟨?_, ?_⟩
  · intro a ha
    by_cases hbelow : a < w
    · exact (readByte_writeBytes_outside m v (Or.inl hbelow)).trans (h.unchanged a ha)
    · by_cases habove : w + v.length ≤ a
      · exact (readByte_writeBytes_outside m v (Or.inr habove)).trans (h.unchanged a ha)
      · exfalso
        apply ha
        have hk : a - w < v.length := by omega
        have hP := hw (a - w) hk
        rwa [show w + (a - w) = a by omega] at hP
  · intro a ha
    exact present_writeBytes m w v (h.present a ha)

/-- **A write outside the owned region breaks the claim.**  If the write changes
the byte at an address the region excludes, no `Owns` at that region survives it:
the unchanged half demands that byte agree with the pre-state, and the store is
exactly what makes it not.  This is why the loop's first store is a record
question and not a detail of an arm: a frame that omits `%c.i` cannot survive
`while.body.i`, however the arm is proved. -/
theorem owns_writeBytes_outside {P : Nat → Prop} {mem m : Mem} {w : Nat} {v : List UInt8}
    (hw : ¬ P w) (hdiff : readByte (writeBytes m w v) w ≠ readByte mem w) :
    ¬ Owns P mem (writeBytes m w v) := by
  intro h
  exact hdiff (h.unchanged w hw)

/-! ### The forward stores the record now admits

The loop's forward edges write four things before any reserve is checked: the
cursor record's `k` field (`while.body.i`, and again at `if.end207.i` for the
two-entry advance), and the two container stacks at the running depth
(`if.end24.i`).  Each is inside an extent `stage2StagedWrites` names, so
`owns_writeBytes_inside` keeps the walk's region claim across it — which is the
whole of what the record change buys, and what the narrow frame could not do at
any price.  The instances below are stated at the record's own region list, so an
invariant that carries `stage2WalkFrame` discharges them without a side condition.

The depth bound is the `MAXD` check's `519`, and it is stated here rather than in
`WalkInv`: a push at `519` carries `520` out of `if.end24.i`, which is why the
invariant bounds the depth by the stacks' extent and the *check* bounds the index. -/

/-- The `MAXD` check's bound: the depth at which `if.end24.i` still indexes the
stacks.  This is the arm's guard, not the invariant's clause. -/
def NestGuard (sp : Nat) : Prop := sp ≤ 519

/-- A region list's tail denotes a sub-predicate of the whole. -/
theorem inRegions_append_right {rs ss : List (Nat × Nat)} {a : Nat}
    (h : inRegions ss a) : inRegions (rs ++ ss) a := by
  obtain ⟨r, hr, hi⟩ := h
  exact ⟨r, List.mem_append_right _ hr, hi⟩

/-- The loop head's store target: byte `j` of the eight-byte `%k11.i` store at
`%c.i + 32` is inside the cursor record's extent. -/
theorem cursorK_inside {c ctype cst tok s z e j : Nat} (hj : j < 8) :
    inRegions (stage2StagedWrites c ctype cst tok s z e) (c + 32 + j) :=
  ⟨(c, stage2CursorExtent),
    by simp [stage2StagedWrites], by omega, by simp [stage2CursorExtent]; omega⟩

/-- The nesting arm's type-stack store at the depth the check admits is inside the
type stack's extent. -/
theorem ctype_inside {c ctype cst tok s z e sp : Nat} (h : NestGuard sp) :
    inRegions (stage2StagedWrites c ctype cst tok s z e) (ctype + sp) :=
  ⟨(ctype, stage2StackExtent), by simp [stage2StagedWrites], Nat.le_add_right _ _,
    by have := h; simp only [NestGuard] at this; simp [stage2StackExtent]; omega⟩

/-- The nesting arm's state-stack store at the same index is inside its extent. -/
theorem cst_inside {c ctype cst tok s z e sp : Nat} (h : NestGuard sp) :
    inRegions (stage2StagedWrites c ctype cst tok s z e) (cst + sp) :=
  ⟨(cst, stage2StackExtent), by simp [stage2StagedWrites], Nat.le_add_right _ _,
    by have := h; simp only [NestGuard] at this; simp [stage2StackExtent]; omega⟩

/-- **The loop head's store preserves the walk's frame.**  `while.body.i` writes
eight bytes at `%c.i + 32`; every written byte is inside the cursor record's
extent, which is one of the seven staged objects the frame's list names. -/
theorem walkFrame_cursorK {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {m : Mem}
    {v : List UInt8} (hv : v.length ≤ 8) (h : UnchangedOutside m0 m (walkWide G C)) :
    UnchangedOutside m0 (writeBytes m (C.stage.c + 32) v) (walkWide G C) :=
  h.write_inside (fun k hk => walkWide_of_seven
    (cursorK_inside (j := k) (by omega)))

/-- **The nesting arm's type-stack store preserves the frame.** -/
theorem walkFrame_ctype {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {m : Mem}
    {v : List UInt8} (hv : v.length ≤ 1) (hsp : NestGuard C.sp)
    (h : UnchangedOutside m0 m (walkWide G C)) :
    UnchangedOutside m0 (writeBytes m (C.stage.ctype + C.sp) v) (walkWide G C) :=
  h.write_inside (fun k hk => by
    have hk0 : k = 0 := by omega
    subst hk0
    exact walkWide_of_seven (ctype_inside hsp))

/-- **The nesting arm's state-stack store preserves the frame.** -/
theorem walkFrame_cst {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {m : Mem}
    {v : List UInt8} (hv : v.length ≤ 1) (hsp : NestGuard C.sp)
    (h : UnchangedOutside m0 m (walkWide G C)) :
    UnchangedOutside m0 (writeBytes m (C.stage.cst + C.sp) v) (walkWide G C) :=
  h.write_inside (fun k hk => by
    have hk0 : k = 0 := by omega
    subst hk0
    exact walkWide_of_seven (cst_inside hsp))

/-- **The loop head's store, at the invariant.**  `while.body.i` writes the
advanced index to `%c.i + 32`; the store is inside the cursor record's extent, so
the invariant's own frame survives it. -/
theorem WalkInv.frame_cursorK {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (h : WalkInv G C s) {v : List UInt8} (hv : v.length ≤ 8) :
    UnchangedOutside m0 (writeBytes s.mem (C.stage.c + 32) v) (walkWide G C) :=
  walkFrame_cursorK hv h.frame

/-- **The nesting arm's two stack stores, at the invariant.**  `if.end24.i` writes
`%ctype.i[sp]` and `%cst.i[sp]`; both are inside the stacks' staged extents at the
depth the `MAXD` check admits (`NestGuard`, the arm's guard — not the invariant's
`depth_cap`), so the invariant's frame survives them. -/
theorem WalkInv.frame_stack {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (h : WalkInv G C s) {cv sv : List UInt8}
    (hcv : cv.length ≤ 1) (hsv : sv.length ≤ 1) (hsp : NestGuard C.sp) :
    UnchangedOutside m0
      (writeBytes (writeBytes s.mem (C.stage.ctype + C.sp) cv)
        (C.stage.cst + C.sp) sv) (walkWide G C) :=
  walkFrame_cst hsv hsp (walkFrame_ctype hcv hsp h.frame)

-- The three store families' provenance, off the pinned body: the cursor field's
-- `gep` at the loop entry, and the two stack stores at the `zext` of the depth.
#guard gepDef stage2Body "while.body.i.lr.ph" "%k11.i" = some ("%c.i", 32)
#guard storeTargets stage2Body "if.end24.i" =
  [("%arrayidx30.i", Ty.int 8), ("%arrayidx32.i", Ty.int 8)]

-- The `MAXD` check the indexing bound comes from, and the two `gep`s it guards.
#guard (stage2Body.blocks.flatMap (·.instrs)).any (fun i =>
  match i with
  | .icmp _ .ugt 32 (.reg "%sp.i.0248") (.imm (.int 32 (BitVec.ofNat 32 519))) => true
  | _ => false) = true

-- The two reserves read the log's own fields: the arena's cursor and capacity at
-- `%z + 48`/`%z + 56`, the event stream's length and capacity at
-- `%z + 8`/`%z + 16`.  The checks themselves write no memory; the cursor moves in
-- the store after them.
#guard gepDef stage2Body "entry" "%alen" = some ("%z", 48)
#guard gepDef stage2Body "entry" "%acap" = some ("%z", 56)
#guard gepDef stage2Body "entry" "%len" = some ("%z", 8)
#guard gepDef stage2Body "entry" "%cap" = some ("%z", 16)
#guard storeTargets stage2Body "if.end.i.i" = []

/-! #### What resists, in order

Three things stand between this invariant and the dispatch, and **none of them is
one of the three the lead named** — the nesting and the two reserves are all
*downstream* of the first:

1. **The register facts the dispatch reads.**  The log's four fields are a clause
   of the invariant (`log_len`, `log_cap`, `log_alen`, `log_acap`), read at
   `%z + 8/16/48/56` with the `#guard`s above as the addresses' provenance, so
   `if.end256.i`'s `%add.i82 = (%add.i) + %z.val36` compares `alen + len + 64`
   against the word the staging fixed as `dstcap`; they were **measured** from
   the run's cursors rather than assumed.  The six pointer registers the header
   and the nesting arm read are now carried too, by `WalkPtrs`: `%3` and `%5`
   (the document and entry stream bases, loaded in `entry`), `%k11.i`
   (`%c.i + 32`), `%ctype.i`/`%cst.i` as pointers, and `%hash1.i.i`.  They are
   bindings of the emitted body rather than clauses of the walk's memory, but a
   block's `denoteCode` needs them before its edge can be a step, so they are
   fields of the invariant: produced at the seed (`WalkSeedState` carries them)
   and preserved by `forInc_step`, `scan_step` and `walkBack_step` through
   `WalkPtrs.bind`.  `WalkInv.log_hash` carries the last memory clause the
   nesting arm reads, the zeroed hash word at `%z + 32`.  Two registers are read
   by a proved block and not carried: `%ar` (`%z + 40`), which no proved block
   reads yet, and `%8`, the document byte the header loads.  `%8` is the one
   register fact `ifEnd24_step` takes as a hypothesis rather than from the
   invariant, because its value is the header's read of the document at the
   entry's position — `whileBodyOut` binds it — and that is a fact about the
   dispatch's data flow rather than about the walk's carry.
2. **The dispatch's own completion**, which is where the nesting and both reserves
   are decided; `WalkLocal` is `True` at every block between them.  The *frame*
   question no longer lands here: `WalkInv.frame` is the record's own write
   extent and `WalkInv.frame_cursorK`/`WalkInv.frame_stack` are the two forward
   stores preserved at it.  The two blocks whose edges were named are steps now
   (`whileBody_step`, `ifEnd24_step`), and the trace they belong to is stated
   (`WalkLink`/`WalkChain`, with `WalkLink.whileBody` and `WalkLink.ifEnd24` its
   two proved links).  What remains is the ten predecessors' `phi` facts at
   `cleanup478.i` and the links between the arms.
3. **The six sub-unit contracts.**  `s2_init`, `s2_value_pos`, `s2_after_value`,
   `s2_string_body`, `od_scalar_value` and `num_fast_el1` all fall through
   `stage2Calls` to the parameter `sub`, and the `#guard` in `JsonStage2IR` pins
   that list.  `stage2SubCalls` (`JsonStage2Body`) answers all six from their
   bodies in `kernel/json/stage2.c`, so a selection answering `none` at `s2_init`
   is no longer the only choice: the six calls of the pinned body have a model,
   and `stage2Calls_s2_init` … `stage2Calls_num_fast_el1` are the reductions from
   the walk's environment to it.

So `Stage2WalkObligation` is stated and not inhabited, and its *post* half is now
statable at a region that is true of the body: `WalkInv.report` yields
`stage2WalkFrame`'s claim, `Stage2Run` carries the seven and the staging, and
`stage2Run_boundary` turns the report into `stage2Boundary` at the ABI's thirteen
arguments.  The assembly point is `JsonStage2Body.stage2WalkObligation_at_subCalls`
(completion beside the post) and
`JsonStage2IR.stage2WalkObligation_iff_completion` (the same at the adapter's
record).  What is missing is the obligation's completion conjunct,
`JsonStage2Body.Stage2WalkCompletes`: a budget at which the pinned body returns.
This module states the object that conjunct is a `WalkChain` from the loop head to
a returning last state, proves that a chain *is* such a run at its own step count
(`WalkChain.completes`) and that it carries the measure bound
(`WalkChain.measure_le`), and supplies two of its links — the header's block and
the nesting arm's.  What it does not supply is the chain itself: the links between
the arms, which are per-block `denoteCode` traces at blocks `WalkLocal` is still
`True` at, and the step count against `stage2Budget`.  No well-foundedness claim is
made here: the five proved arms, the closed back edge and the two dispatch steps
are exactly the edges whose measures are shown, and `WalkLocal`'s `True` elsewhere
is the statement of what is not.
-/

/-! ### The back edge: `cleanup478.i`'s merge

The edge's own block is the merge and the exit test: the depth and the index the
dispatch left, and the unsigned test against the entry count.  It writes no
memory, so the region claim and the carried extents are untouched, and its effect
on the carry is the reset — the next iteration's dispatch has spent nothing, so
`inner` is the whole allowance again.  The index does not advance here: the
header's leading `phi` rebinds `%k.0.i249` inside `while.body.i`, which is why the
strict decrease is the next block's (`walkMeasure_step`) and not this edge's. -/

/-- The merge's depth `phi`, as the pinned body writes it. -/
def cleanupSpIncoming : List (String × Operand) :=
  [("if.end473.i", .reg "%sp.i.0248"), ("if.end150.i", .reg "%sp.i.0248"),
   ("if.end162.i", .reg "%sp.i.0248"), ("if.end195.i", .reg "%sp.i.0248"),
   ("if.else334.i", .reg "%sp.i.0248"), ("if.then330.i", .reg "%sp.i.0248"),
   ("if.then.i.i", .reg "%inc33.i"), ("out_reserve.exit.i.i", .reg "%inc33.i"),
   ("if.then.i.i50", .reg "%sub.i"), ("out_reserve.exit.i.i60", .reg "%sub.i")]

/-- The merge's index `phi`, as the pinned body writes it. -/
def cleanupKIncoming : List (String × Operand) :=
  [("if.end473.i", .reg "%inc.i"), ("if.end150.i", .reg "%inc.i"),
   ("if.end162.i", .reg "%inc.i"), ("if.end195.i", .reg "%inc.i"),
   ("if.else334.i", .reg "%inc208.i"), ("if.then330.i", .reg "%inc208.i"),
   ("if.then.i.i", .reg "%inc.i"), ("out_reserve.exit.i.i", .reg "%inc.i"),
   ("if.then.i.i50", .reg "%inc.i"), ("out_reserve.exit.i.i60", .reg "%inc.i")]

/-- `cleanup478.i`: the merge and the unsigned test against the entry count. -/
def cleanup478Block : Block :=
  { name := "cleanup478.i",
    instrs := [
      Instr.phi "%sp.i.1" (Ty.int 32) cleanupSpIncoming,
      Instr.phi "%k.2.i" (Ty.int 64) cleanupKIncoming,
      Instr.icmp "%cmp.i" IPred.ult 64 (Operand.reg "%k.2.i") (Operand.reg "%nep")],
    term := Term.condbr (Operand.reg "%cmp.i") "while.body.i" "if.then485.i" }

/-- The merge is the pinned body's block: the arm is about `stage2Body`, not a
transcription of it. -/
theorem cleanup478_find :
    stage2Body.findBlock "cleanup478.i" = some cleanup478Block := by
  simp [stage2Body, Function.findBlock, findBlockList, cleanup478Block,
    cleanupSpIncoming, cleanupKIncoming]

/-- The merge's two `phi`s and the test, at the state's own environment: the
bindings are the two selected values, and the test's bit is one because the
dispatch's index is still short of the entry count. -/
theorem cleanup478_denote (calls : Calls) (s : State) (p : String)
    {spv k2 : Nat} {spOp kOp : Operand} {nepv : BitVec 64}
    (hpre : s.pre = some p)
    (hsp : phiIncoming p cleanupSpIncoming = some spOp)
    (hspv : evalOperand s spOp = some (.int 32 (BitVec.ofNat 32 spv)))
    (hk : phiIncoming p cleanupKIncoming = some kOp)
    (hkv : evalOperand s kOp = some (.int 64 (BitVec.ofNat 64 k2)))
    (hnep : lookupName s.env "%nep" = some (.int 64 nepv))
    (hguard : k2 < nepv.toNat) :
    denoteCode calls cleanup478Block.instrs s =
      some (((s.bind "%sp.i.1" (.int 32 (BitVec.ofNat 32 spv))).bind
        "%k.2.i" (.int 64 (BitVec.ofNat 64 k2))).bind
        "%cmp.i" (.int 1 (1 : BitVec 1))) := by
  have hult : evalICmp .ult (BitVec.ofNat 64 k2) nepv = (1 : BitVec 1) := by
    have hlt : (BitVec.ofNat 64 k2).toNat < nepv.toNat := by
      rw [BitVec.toNat_ofNat]
      omega
    rw [show evalICmp .ult (BitVec.ofNat 64 k2) nepv
          = BitVec.ofBool (BitVec.ult (BitVec.ofNat 64 k2) nepv) from rfl]
    rw [show BitVec.ult (BitVec.ofNat 64 k2) nepv = true from
      (BitVec.ult_iff_toNat_lt).2 hlt]
    rfl
  have hsel : PhiSelects s p
      [{ dst := "%sp.i.1", ty := Ty.int 32, incoming := cleanupSpIncoming },
       { dst := "%k.2.i", ty := Ty.int 64, incoming := cleanupKIncoming }]
      [("%sp.i.1", .int 32 (BitVec.ofNat 32 spv)),
       ("%k.2.i", .int 64 (BitVec.ofNat 64 k2))] :=
    PhiSelects.cons hsp hspv (PhiSelects.cons hk hkv PhiSelects.nil)
  have hspecs : cleanup478Block.instrs =
      ([{ dst := "%sp.i.1", ty := Ty.int 32, incoming := cleanupSpIncoming },
        { dst := "%k.2.i", ty := Ty.int 64, incoming := cleanupKIncoming }].map
          PhiSpec.instr) ++
        [Instr.icmp "%cmp.i" IPred.ult 64 (Operand.reg "%k.2.i")
          (Operand.reg "%nep")] := by
    simp [cleanup478Block, PhiSpec.instr]
  rw [hspecs, denoteCode_phiRun (specs :=
      [{ dst := "%sp.i.1", ty := Ty.int 32, incoming := cleanupSpIncoming },
       { dst := "%k.2.i", ty := Ty.int 64, incoming := cleanupKIncoming }])
      (vs := [("%sp.i.1", .int 32 (BitVec.ofNat 32 spv)),
              ("%k.2.i", .int 64 (BitVec.ofNat 64 k2))])
      (rest := [Instr.icmp "%cmp.i" IPred.ult 64 (Operand.reg "%k.2.i")
        (Operand.reg "%nep")]) hpre hsel (by rfl)]
  rw [show s.bindAll [("%sp.i.1", .int 32 (BitVec.ofNat 32 spv)),
        ("%k.2.i", .int 64 (BitVec.ofNat 64 k2))] =
      stateAt (("%k.2.i", .int 64 (BitVec.ofNat 64 k2)) ::
        ("%sp.i.1", .int 32 (BitVec.ofNat 32 spv)) :: s.env) s from rfl]
  rw [denoteCode_icmp_ult_reg (x := BitVec.ofNat 64 k2) (y := nepv)
    calls _ s "%cmp.i" "%k.2.i" "%nep"
    (by simp only [lookupName_cons_self])
    (by
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      exact hnep)
    []]
  rw [hult]
  rfl

/-- **The back edge, at the invariant.**  From `WalkInv` at `cleanup478.i`, whose
merge selects the dispatch's depth and index and whose test is clear, one control
step lands at `while.body.i` with every clause preserved and the inner component
reset to the allowance. -/
theorem walkBack_step {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "cleanup478.i")
    {p : String} {spv k2 : Nat} {spOp kOp : Operand} {nepv : BitVec 64}
    (hpre : s.pre = some p)
    (hsp : phiIncoming p cleanupSpIncoming = some spOp)
    (hspv : evalOperand s spOp = some (.int 32 (BitVec.ofNat 32 spv)))
    (hk : phiIncoming p cleanupKIncoming = some kOp)
    (hkv : evalOperand s kOp = some (.int 64 (BitVec.ofNat 64 k2)))
    (hnep : lookupName s.env "%nep" = some (.int 64 nepv))
    (hguard : k2 < nepv.toNat) :
    ∃ e : State,
      step calls stage2Body s = .jump e ∧
      WalkInv G { C with block := "while.body.i", inner := walkInnerCap G } e ∧
      ∀ k, runFuel calls (1 + k) stage2Body s = runFuel calls k stage2Body e := by
  have hpc : s.pc = "cleanup478.i" := by rw [hInv.pc_eq, hblock]
  let e : State :=
    { ((s.bind "%sp.i.1" (.int 32 (BitVec.ofNat 32 spv))).bind
        "%k.2.i" (.int 64 (BitVec.ofNat 64 k2))).bind
        "%cmp.i" (.int 1 (1 : BitVec 1)) with
      pc := "while.body.i"
      pre := some "cleanup478.i" }
  have hden := cleanup478_denote calls s p hpre hsp hspv hk hkv hnep hguard
  have hterm : cleanup478Block.term =
      Term.condbr (Operand.reg "%cmp.i") "while.body.i" "if.then485.i" := rfl
  have hstep : step calls stage2Body s = .jump e := by
    have hfind : stage2Body.findBlock s.pc = some cleanup478Block := by
      rw [hpc, cleanup478_find]
    simp only [step, hfind, hden, hterm]
    dsimp only [e, State.bind]
    simp only [execTerm, evalOperand, lookupName_cons_self, hpc]
    simp
  refine ⟨e, hstep, ?_, ?_⟩
  · refine
      { pc_eq := rfl
        blockIndex := ?_
        k_le := hInv.k_le
        events_le := hInv.events_le
        evlen_eq := hInv.evlen_eq
        evBytes := hInv.evBytes
        alen_le_sum := hInv.alen_le_sum
        alen_ge := hInv.alen_ge
        spans_order := hInv.spans_order
        spans_inside := hInv.spans_inside
        pending_at := hInv.pending_at
        pending_cursor := hInv.pending_cursor
        pending_len := hInv.pending_len
        eoff_le := hInv.eoff_le
        inner_cap := Nat.le_refl _
        depth_cap := hInv.depth_cap
        depth_reg := by
          dsimp only [e, State.bind]
          rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
            lookupName_cons_ne _ _ (by decide)]
          exact hInv.depth_reg
        ptrs := by
          dsimp only [e, State.bind]
          have h1 := hInv.ptrs.bind_pair (a := "%sp.i.1") (b := "%k.2.i")
            (va := .int 32 (BitVec.ofNat 32 spv))
            (vb := .int 64 (BitVec.ofNat 64 k2))
            ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
            ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
          exact h1.bind (d := "%cmp.i") (v := .int 1 (1 : BitVec 1))
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        log_hash := by dsimp only [e]; exact hInv.log_hash
        log_len := hInv.log_len
        log_cap := hInv.log_cap
        log_alen := hInv.log_alen
        log_acap := hInv.log_acap
        owned := by dsimp only [e, State.bind]; exact hInv.owned
        frame := by dsimp only [e, State.bind]; exact hInv.frame
        blockLocal := by simp [WalkLocal] }
    dsimp only [e, State.bind]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact hInv.blockIndex
  · intro k
    rw [show 1 + k = k + 1 from by omega]
    simp only [runFuel, hstep]

/-! ### The outer iteration's arithmetic

The entry loop's back edge (`walkBack_step`) resets `inner` to the next dispatch's
work; the index advances at the header's `phi`, which `while.body.i` binds from
`%k.2.i` inside the block rather than on the edge.  So the iteration is the
two-block step `cleanup478.i → while.body.i → NodeBlock21`: its reset is the
edge's, its advance is the header's block's, and the cap is what makes the reset
survive the radix.  `walkMeasure_step` is the strict decrease, and it is the only
place the cap's value is consumed. -/

/-- **An iteration that advances the index and stays inside the cap is strict.**
`k' ≥ k + 1` takes at least one whole radix off the outer term, and `inner' ≤ cap`
is smaller than the radix that was removed, so the inner component's reset cannot
give it back. -/
theorem walkMeasure_step {m0 : Mem} (G : WalkGeom m0) (C C' : WalkCarry G)
    (hk : C.k < C'.k) (hk' : C'.k ≤ G.nep)
    (hinner : C'.inner ≤ walkInnerCap G) :
    walkMeasure G C' < walkMeasure G C := by
  have hsplit : G.nep - C.k = (G.nep - C'.k) + (C'.k - C.k) := by omega
  have hstep : 1 ≤ C'.k - C.k := by omega
  have hmul : (G.nep - C.k) * (walkInnerCap G + 1)
      = (G.nep - C'.k) * (walkInnerCap G + 1) + (C'.k - C.k) * (walkInnerCap G + 1) := by
    rw [hsplit, Nat.add_mul]
  have hradix : walkInnerCap G + 1 ≤ (C'.k - C.k) * (walkInnerCap G + 1) := by
    simpa using Nat.mul_le_mul_right (walkInnerCap G + 1) hstep
  simp only [walkMeasure]
  rw [hmul]
  omega

/-- **The iteration's measure, from the two halves.**  The edge resets `inner`
(`walkBack_step`) and the header's block advances `k`; the carry with both applied
is the one above, and its decrease is `walkMeasure_step` with the cap holding by
`Nat.le_refl`.  This is the arithmetic the header's block still owes: prove it
lands with the index advanced, and the decrease is this. -/
theorem walkIter_measure {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (k2 : Nat)
    (hk : C.k < k2) (hk' : k2 ≤ G.nep) :
    walkMeasure G { C with k := k2, inner := walkInnerCap G } < walkMeasure G C :=
  walkMeasure_step G C { C with k := k2, inner := walkInnerCap G } hk hk'
    (Nat.le_refl _)

/-! ### The instrument -/

/-- info: 'LeanLLVM.Refinement.WalkGeom.nonempty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkGeom.nonempty

/-- info: 'LeanLLVM.Refinement.WalkInv.alen_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkInv.alen_le

/-- info: 'LeanLLVM.Refinement.WalkInv.evlen_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkInv.evlen_le

/-- info: 'LeanLLVM.Refinement.EventRecord.encodedSize_number' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.EventRecord.encodedSize_number

/-- info: 'LeanLLVM.Refinement.EventRecord.encodedSize_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.EventRecord.encodedSize_le

/-- info: 'LeanLLVM.Refinement.EventRecord.sum_encodedSize_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.EventRecord.sum_encodedSize_le

/-- info: 'LeanLLVM.Refinement.forInc_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.forInc_find

/-- info: 'LeanLLVM.Refinement.forInc_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.forInc_step

/-- info: 'LeanLLVM.Refinement.WalkGeom.nep_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkGeom.nep_le

/-- info: 'LeanLLVM.Refinement.WalkInv.forInc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkInv.forInc

/-- info: 'LeanLLVM.Refinement.denoteCode_add_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.denoteCode_add_one

/-- info: 'LeanLLVM.Refinement.denoteCode_icmp_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.denoteCode_icmp_eq

/-- info: 'LeanLLVM.Refinement.forInc_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.forInc_denote

/-- info: 'LeanLLVM.Refinement.forInc_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.forInc_term

/-- info: 'LeanLLVM.Refinement.forInc_arm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.forInc_arm

/-- info: 'LeanLLVM.Refinement.scanWhitespace_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.scanWhitespace_find

/-- info: 'LeanLLVM.Refinement.scanString_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.scanString_find

/-- info: 'LeanLLVM.Refinement.scanEscape_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.scanEscape_find

/-- info: 'LeanLLVM.Refinement.scanExtraToken_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.scanExtraToken_find

/-- info: 'LeanLLVM.Refinement.WalkLocal.whitespace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkLocal.whitespace

/-- info: 'LeanLLVM.Refinement.WalkLocal.whitespaceLanded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkLocal.whitespaceLanded

/-- info: 'LeanLLVM.Refinement.WalkLocal.stringScan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkLocal.stringScan

/-- info: 'LeanLLVM.Refinement.WalkLocal.stringScanLanded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkLocal.stringScanLanded

/-- info: 'LeanLLVM.Refinement.WalkLocal.escape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkLocal.escape

/-- info: 'LeanLLVM.Refinement.WalkLocal.escapeLanded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkLocal.escapeLanded

/-- info: 'LeanLLVM.Refinement.WalkLocal.extraToken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkLocal.extraToken

/-- info: 'LeanLLVM.Refinement.WalkLocal.extraTokenLanded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkLocal.extraTokenLanded

/-- info: 'LeanLLVM.Refinement.WalkInv.whitespace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkInv.whitespace

/-- info: 'LeanLLVM.Refinement.WalkInv.stringScan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkInv.stringScan

/-- info: 'LeanLLVM.Refinement.WalkInv.escape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkInv.escape

/-- info: 'LeanLLVM.Refinement.WalkInv.extraToken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkInv.extraToken

/-- info: 'LeanLLVM.Refinement.scan_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.scan_denote

/-- info: 'LeanLLVM.Refinement.scan_term' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.scan_term

/-- info: 'LeanLLVM.Refinement.scan_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.scan_step

/-- info: 'LeanLLVM.Refinement.whitespace_scan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.whitespace_scan

/-- info: 'LeanLLVM.Refinement.string_scan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.string_scan

/-- info: 'LeanLLVM.Refinement.escape_scan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.escape_scan

/-- info: 'LeanLLVM.Refinement.extraToken_scan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.extraToken_scan

/-- info: 'LeanLLVM.Refinement.walkSeed_inner_cap' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.walkSeed_inner_cap

/-- info: 'LeanLLVM.Refinement.walkSeed_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.walkSeed_invariant

/-- info: 'LeanLLVM.Refinement.WalkInv.report' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkInv.report

/-- info: 'LeanLLVM.Refinement.owns_writeBytes_inside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.owns_writeBytes_inside

/-- info: 'LeanLLVM.Refinement.owns_writeBytes_outside' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.owns_writeBytes_outside

/-- info: 'LeanLLVM.Refinement.walkMeasure_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.walkMeasure_step

/-- info: 'LeanLLVM.Refinement.cleanup478_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.cleanup478_find

/-- info: 'LeanLLVM.Refinement.cleanup478_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.cleanup478_denote

/-- info: 'LeanLLVM.Refinement.walkBack_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.walkBack_step

/-- info: 'LeanLLVM.Refinement.walkIter_measure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.walkIter_measure

/-- info: 'LeanLLVM.Refinement.walkSeed_depth_cap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.walkSeed_depth_cap

/-- info: 'LeanLLVM.Refinement.cursorK_inside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.cursorK_inside

/-- info: 'LeanLLVM.Refinement.ctype_inside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.ctype_inside

/-- info: 'LeanLLVM.Refinement.cst_inside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.cst_inside

end LeanLLVM.Refinement
/-! ### Steps at the two blocks' widths -/

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.BlockEval


theorem sExt_ofNat64 {j : Nat} (hj : j < 2 ^ 63) :
    ((BitVec.ofNat 64 j).signExtend 64).toNat = j := by
  simp [BitVec.toNat_ofNat, BitVec.signExtend]
  omega

theorem walkToNat_ofNat64 {j : Nat} (hj : j < 2 ^ 64) :
    (BitVec.ofNat 64 j).toNat = j := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj]

theorem walkToNat_ofNat32 {j : Nat} (hj : j < 2 ^ 32) :
    (BitVec.ofNat 32 j).toNat = j := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj]

theorem bytesToNat_singleton (b : UInt8) : bytesToNat [b] = b.toNat := by
  simp [bytesToNat]

theorem bytesToNat_lt_32 {bs : List UInt8} (h : bs.length = 4) :
    bytesToNat bs < 2 ^ 32 := by
  have h' := bytesToNat_lt bs
  rw [h, show (256 : Nat) ^ 4 = 2 ^ 32 from by decide] at h'
  exact h'

theorem bytesToNat_lt_8 {bs : List UInt8} (h : bs.length = 1) :
    bytesToNat bs < 256 := by
  have h' := bytesToNat_lt bs
  rw [h] at h'
  exact h'

/-- **A write outside a read's range leaves the read alone.** -/
theorem walkReadBytes_writeBytes_outside {m : Mem} {v : List UInt8} :
    ∀ {start addr n : Nat}, addr + n ≤ start ∨ start + v.length ≤ addr →
      readBytes (writeBytes m start v) addr n = readBytes m addr n
  | start, addr, 0, _ => by simp [readBytes]
  | start, addr, n + 1, h => by
      have hhead : addr < start ∨ start + v.length ≤ addr := by omega
      have htail : addr + 1 + n ≤ start ∨ start + v.length ≤ addr + 1 := by omega
      rw [readBytes, readBytes, readByte_writeBytes_outside m v hhead,
        walkReadBytes_writeBytes_outside (m := m) (v := v) (start := start)
          (addr := addr + 1) (n := n) htail]

/-- A one-byte read from a present byte. -/
theorem walkReadBytes_one_of_readByte {m : Mem} {a : Nat} {b : UInt8}
    (h : readByte m a = some b) : readBytes m a 1 = some [b] := by
  simp only [readBytes, h]

theorem walkReadBytes_length {m : Mem} {addr : Nat} :
    ∀ {n : Nat} {bs : List UInt8}, readBytes m addr n = some bs → bs.length = n
  | 0, bs, h => by
      simp only [readBytes, Option.some.injEq] at h
      subst h; rfl
  | n + 1, bs, h => by
      simp only [readBytes] at h
      split at h
      · cases h
      · rename_i b hb
        split at h
        · cases h
        · rename_i bs' hbs
          cases h
          simp only [List.length_cons]
          rw [walkReadBytes_length hbs]

theorem readLanes32_nth {m : Mem} {addr : Nat} :
    ∀ {n : Nat} {l : List Nat}, readLanes32 m addr n = some l →
      l.length = n ∧ ∀ j, j < n →
        ∃ q bs, l[j]? = some q ∧ readBytes m (addr + 4 * j) 4 = some bs ∧ bytesToNat bs = q
  | 0, l, h => by
      simp only [readLanes32, Option.some.injEq] at h
      subst h
      exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | n + 1, l, h => by
      simp only [readLanes32] at h
      cases hb : readBytes m addr 4 with
      | none => rw [hb] at h; cases h
      | some bs =>
          rw [hb] at h
          cases hr : readLanes32 m (addr + 4) n with
          | none => rw [hr] at h; cases h
          | some tl =>
              rw [hr] at h
              simp only [Option.map_some, Option.bind_some, Option.some.injEq] at h
              subst h
              obtain ⟨hlen, hget⟩ := readLanes32_nth (m := m) (addr := addr + 4) hr
              refine ⟨by simp [hlen], ?_⟩
              intro j hj
              cases j with
              | zero => exact ⟨bytesToNat bs, bs, by simp, by simpa using hb, rfl⟩
              | succ i =>
                  obtain ⟨q, bs', hq, hread, hval⟩ := hget i (by omega)
                  exact ⟨q, bs', by simp [hq], by
                    rw [show addr + 4 * (i + 1) = addr + 4 + 4 * i from by omega]
                    exact hread, hval⟩

-- `denoteCode` chain steps: the same shapes `BlockEval` has, at the widths and
-- the `ofNat` values the two blocks use.

theorem denoteCode_zext32_64_ofNat (calls : Calls) (env : Env) (s : State)
    (d v : String) {q : Nat}
    (hv : lookupName env v = some (.int 32 (BitVec.ofNat 32 q)))
    (hq : q < 2 ^ 32) (is : List Instr) :
    denoteCode calls (.zext d 32 64 (.reg v) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 64 (BitVec.ofNat 64 q)) :: env) s) := by
  rw [denoteCode_zext calls env s d v 32 64 (x := BitVec.ofNat 32 q) hv is,
    walkToNat_ofNat32 hq]

theorem denoteCode_gep8_ofNat (calls : Calls) (env : Env) (s : State)
    (d base off : String) {a j : Nat}
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 (BitVec.ofNat 64 j)))
    (hj : j < 2 ^ 63) (is : List Instr) :
    denoteCode calls (.gep d (.int 8) (.reg base) (.reg off) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .ptr (a + j)) :: env) s) := by
  have hs := sExt_ofNat64 hj
  rw [denoteCode_gep8_reg calls env s d base off hb ho (by rw [hs]; exact hj) is, hs]

theorem denoteCode_gep32_ofNat (calls : Calls) (env : Env) (s : State)
    (d base off : String) {a j : Nat}
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 (BitVec.ofNat 64 j)))
    (hj : j < 2 ^ 63) (is : List Instr) :
    denoteCode calls (.gep d (.int 32) (.reg base) (.reg off) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .ptr (a + j * 4)) :: env) s) := by
  have hs := sExt_ofNat64 hj
  have hsize : (Ty.int 32).sizeBytes = 4 := by decide
  rw [denoteCode_cons_of _ _ _ _ _ (by
    rw [evalInstr_gep (s := stateAt env s) (elemTy := .int 32)
      (hb := evalOperand_reg_of env s base (.ptr a) hb)
      (ho := evalOperand_reg_of env s off (.int 64 (BitVec.ofNat 64 j)) ho)
      (hpos := by rw [hs]; exact hj)])]
  simp only [stateAt, State.bind, hs, hsize]

theorem denoteCode_load32 (calls : Calls) (env : Env) (s : State) (d p : String)
    {a q : Nat} {bs : List UInt8}
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 4 = some bs) (hbs : bytesToNat bs = q) (is : List Instr) :
    denoteCode calls (.load d (.int 32) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 32 (BitVec.ofNat 32 q)) :: env) s) := by
  have hv' : loadValue (stateAt env s).mem (.int 32) a
      = some (.int 32 (BitVec.ofNat 32 q)) := by
    show loadValue s.mem (.int 32) a = _
    simp only [loadValue, show (32 + 7) / 8 = 4 from rfl,
      ite_eq_right (by decide : ¬ (32 = 0)), hv, hbs]
  rw [denoteCode_cons_of _ _ _ _ _ (by
    rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_load (s := stateAt env s)
      (hp := evalOperand_reg_of env s p (.ptr a) hp) (hv := hv')])]
  simp only [stateAt, State.bind]

theorem denoteCode_load8 (calls : Calls) (env : Env) (s : State) (d p : String)
    {a q : Nat} {bs : List UInt8}
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 1 = some bs) (hbs : bytesToNat bs = q) (is : List Instr) :
    denoteCode calls (.load d (.int 8) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 8 (BitVec.ofNat 8 q)) :: env) s) := by
  have hv' : loadValue (stateAt env s).mem (.int 8) a
      = some (.int 8 (BitVec.ofNat 8 q)) := by
    show loadValue s.mem (.int 8) a = _
    simp only [loadValue, show (8 + 7) / 8 = 1 from rfl,
      ite_eq_right (by decide : ¬ (8 = 0)), hv, hbs]
  rw [denoteCode_cons_of _ _ _ _ _ (by
    rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_load (s := stateAt env s)
      (hp := evalOperand_reg_of env s p (.ptr a) hp) (hv := hv')])]
  simp only [stateAt, State.bind]

theorem denoteCode_load8_single (calls : Calls) (env : Env) (s : State) (d p : String)
    {a : Nat} {b : UInt8}
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 1 = some [b]) (is : List Instr) :
    denoteCode calls (.load d (.int 8) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 8 (BitVec.ofNat 8 b.toNat)) :: env) s) :=
  denoteCode_load8 calls env s d p (q := b.toNat) hp hv (bytesToNat_singleton b) is

theorem denoteCode_store64_ofNat (calls : Calls) (env : Env) (s : State)
    (v p : String) {a j : Nat}
    (hv : lookupName env v = some (.int 64 (BitVec.ofNat 64 j)))
    (hj : j < 2 ^ 64) (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store (.int 64) (.reg v) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is (stateAt env { s with mem := writeBytes s.mem a (wordBytes 8 j) }) := by
  rw [denoteCode_store64 calls env s v p (x := BitVec.ofNat 64 j) hv hp is,
    walkToNat_ofNat64 hj]
  rfl

theorem denoteCode_store8 (calls : Calls) (env : Env) (s : State) (v p : String)
    {x : BitVec 8} {a : Nat}
    (hv : lookupName env v = some (.int 8 x))
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store (.int 8) (.reg v) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 1) }) := by
  have hs : storeValue (stateAt env s) (.int 8) (.int 8 x) a
      = some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 1) }) := by
    simp [storeValue, stateAt, show (8 + 7) / 8 = 1 from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (by
    rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_store (s := stateAt env s)
      (vv := .int 8 x) (a := a)
      (s' := stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 1) })
      (hv := evalOperand_reg_of env s v (.int 8 x) hv)
      (hp := evalOperand_reg_of env s p (.ptr a) hp) (hs := hs)])]

theorem denoteCode_store8_imm (calls : Calls) (env : Env) (s : State) (x : BitVec 8)
    (p : String) {a : Nat} (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store (.int 8) (.imm (.int 8 x)) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 1) }) := by
  have hs : storeValue (stateAt env s) (.int 8) (.int 8 x) a
      = some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 1) }) := by
    simp [storeValue, stateAt, show (8 + 7) / 8 = 1 from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (by
    rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_store (s := stateAt env s)
      (vv := .int 8 x) (a := a)
      (s' := stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 1) })
      (hv := evalOperand_lit_of (stateAt env s) 8 x)
      (hp := evalOperand_reg_of env s p (.ptr a) hp) (hs := hs)])]

theorem denoteCode_icmp_eq_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) (is : List Instr) :
    denoteCode calls (.icmp d .eq w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp .eq x c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (by
    rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_icmp (s := stateAt env s)
      (ha := evalOperand_reg_of env s a (.int w x) ha)
      (hb := evalOperand_lit_of (stateAt env s) w c)])]
  simp only [stateAt, State.bind]

theorem walkDenoteCode_add_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) (is : List Instr) :
    denoteCode calls (.binop d .add w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (x + c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (by
    rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_binop (s := stateAt env s)
      (r := (x + c).toNat)
      (ha := evalOperand_reg_of env s a (.int w x) ha)
      (hb := evalOperand_lit_of (stateAt env s) w c)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])])]
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]

theorem denoteCode_add_one_ofNat (calls : Calls) (env : Env) (s : State)
    (d a : String) (w : Nat) {j : Nat}
    (ha : lookupName env a = some (.int w (BitVec.ofNat w j))) (is : List Instr) :
    denoteCode calls
        (.binop d .add w (.reg a) (.imm (.int w (BitVec.ofNat w 1))) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (BitVec.ofNat w (j + 1))) :: env) s) := by
  rw [walkDenoteCode_add_imm_w calls env s d a w (x := BitVec.ofNat w j)
    (c := BitVec.ofNat w 1) ha is, ← BitVec.ofNat_add]

theorem denoteCode_select_imm_imm_w (calls : Calls) (env : Env) (s : State)
    (d c : String) (w : Nat) {bb : BitVec 1} {x y : BitVec w}
    (hc : lookupName env c = some (.int 1 bb)) (is : List Instr) :
    denoteCode calls
        (.select d (.int w) (.reg c) (.imm (.int w x)) (.imm (.int w y)) :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (if bb = 1 then x else y)) :: env) s) := by
  rcases bitVec1_eq_zero_or_one bb with h | h
  · subst h
    rw [ite_eq_right (by decide : ¬ ((0 : BitVec 1) = 1))]
    rw [denoteCode_cons_of _ _ _ _ _ (by
      rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_select_false (s := stateAt env s)
        (hc := evalOperand_reg_of env s c (.int 1 (0 : BitVec 1)) hc)
        (ha := evalOperand_lit_of (stateAt env s) w x)
        (hb := evalOperand_lit_of (stateAt env s) w y)])]
    simp only [stateAt, State.bind]
  · subst h
    rw [ite_eq_left rfl]
    rw [denoteCode_cons_of _ _ _ _ _ (by
      rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_select_true (s := stateAt env s)
        (hc := evalOperand_reg_of env s c (.int 1 (1 : BitVec 1)) hc)
        (ha := evalOperand_lit_of (stateAt env s) w x)
        (hb := evalOperand_lit_of (stateAt env s) w y)])]
    simp only [stateAt, State.bind]

/-- One instruction of the two blocks: the chain step whose shape matches. -/
macro "walk_step" : tactic => `(tactic|
  (first
   | rw [denoteCode_zext32_64_ofNat _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_gep8_ofNat _ _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_gep32_ofNat _ _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_load32 _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_load8_single _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_load8 _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_store64_ofNat _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_store8 _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_store8_imm _ _ _ _ _ ?_ _]
   | rw [denoteCode_icmp_eq_imm_w _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_add_one_ofNat _ _ _ _ _ _ ?_ _]
   | rw [walkDenoteCode_add_imm_w _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_select_imm_imm_w _ _ _ _ _ _ ?_ _]
   | block_step))

/-- A whole block with the two blocks' further shapes. -/
macro "walk_block_eval" : tactic => `(tactic|
  (repeat walk_step
   block_close
   all_goals (try omega)))

end LeanLLVM.Refinement

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.BlockEval

/-- The header's instruction list, as the pinned body writes it. -/
def whileBodyInstrs : List Instr := [
  Instr.phi "%k.0.i249" (Ty.int 64)
    [("while.body.i.lr.ph", .imm (.int 64 (BitVec.ofNat 64 0))),
     ("cleanup478.i", .reg "%k.2.i")],
  Instr.phi "%sp.i.0248" (Ty.int 32)
    [("while.body.i.lr.ph", .imm (.int 32 (BitVec.ofNat 32 0))),
     ("cleanup478.i", .reg "%sp.i.1")],
  Instr.binop "%inc.i" BinOp.add 64 (.reg "%k.0.i249") (.imm (.int 64 (BitVec.ofNat 64 1))),
  Instr.gep "%arrayidx.i" (Ty.int 32) (.reg "%5") (.reg "%k.0.i249"),
  Instr.load "%7" (Ty.int 32) (.reg "%arrayidx.i"),
  Instr.zext "%idxprom.i" 32 64 (.reg "%7"),
  Instr.gep "%arrayidx10.i" (Ty.int 8) (.reg "%3") (.reg "%idxprom.i"),
  Instr.load "%8" (Ty.int 8) (.reg "%arrayidx10.i"),
  Instr.store (Ty.int 64) (.reg "%inc.i") (.reg "%k11.i")]

/-- The header, as a block: the pin the chain is proved about. -/
def whileBodyBlock : Block :=
  { name := "while.body.i", instrs := whileBodyInstrs, term := Term.br "NodeBlock21" }

theorem whileBody_find : stage2Body.findBlock "while.body.i" = some whileBodyBlock := by
  simp [stage2Body, Function.findBlock, findBlockList, whileBodyBlock, whileBodyInstrs]

macro "walk_close" : tactic => `(tactic|
  (all_goals (try (simp (config := { failIfUnchanged := false })
    only [cells, evalOperand, denoteCode, State.bindAll]))
   all_goals (try rfl)
   all_goals (try assumption)
   all_goals (try block_lk)
   all_goals (try (simp only [phiIncoming]; rfl))
   all_goals (try rfl)
   all_goals (try (exact evalOperand_lit_of _ _ _))
   all_goals (try rfl)))

macro "walk_eval" : tactic => `(tactic|
  (repeat walk_step
   walk_close
   all_goals (try omega)))

/-- The state seen as its own environment's builder is itself. -/
@[simp] theorem stateAt_self (s : State) : stateAt s.env s = s := rfl

/-- The header's outgoing environment: its cells newest first. -/
def whileBodyOut (env : Env) (k sp b ep c q : Nat) (bt : UInt8) : Env :=
  cells [("%8", .int 8 (BitVec.ofNat 8 bt.toNat)),
         ("%arrayidx10.i", .ptr (b + q)),
         ("%idxprom.i", .int 64 (BitVec.ofNat 64 q)),
         ("%7", .int 32 (BitVec.ofNat 32 q)),
         ("%arrayidx.i", .ptr (ep + k * 4)),
         ("%inc.i", .int 64 (BitVec.ofNat 64 (k + 1))),
         ("%sp.i.0248", .int 32 (BitVec.ofNat 32 sp)),
         ("%k.0.i249", .int 64 (BitVec.ofNat 64 k))] env

/-- **`WalkPtrs` survives a run of binds at other names.** -/
theorem WalkPtrs.cells_of {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {env : Env}
    (h : WalkPtrs G C env) (cs : List (String × Value))
    (hne : ∀ c ∈ cs, c.1 ≠ "%3" ∧ c.1 ≠ "%5" ∧ c.1 ≠ "%k11.i" ∧ c.1 ≠ "%ctype.i"
      ∧ c.1 ≠ "%cst.i" ∧ c.1 ≠ "%hash1.i.i") :
    WalkPtrs G C (BlockEval.cells cs env) := by
  induction cs with
  | nil => exact h
  | cons c cs ih =>
      obtain ⟨h3, h5, hk, hc, hs, hh⟩ := hne c (by simp)
      exact (ih (fun c' hc' => hne c' (by simp [hc']))).bind
        (d := c.1) (v := c.2) h3 h5 hk hc hs hh

example (env : Env) (k sp b ep c q : Nat) (bt : UInt8) :
    lookupName (whileBodyOut env k sp b ep c q bt) "%k.0.i249" =
      some (.int 64 (BitVec.ofNat 64 k)) := by
  simp [whileBodyOut, cells, lookupName]

/-- **The header's chain.** -/
theorem whileBody_denote {calls : Calls} (env : Env) (s : State)
    {k sp ep b c q : Nat} {bs : List UInt8} {bt : UInt8}
    (h5 : lookupName env "%5" = some (.ptr ep))
    (h3 : lookupName env "%3" = some (.ptr b))
    (hK : lookupName env "%k11.i" = some (.ptr (c + 32)))
    (hk2 : lookupName env "%k.2.i" = some (.int 64 (BitVec.ofNat 64 k)))
    (hsp1 : lookupName env "%sp.i.1" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hpre : s.pre = some "cleanup478.i")
    (hread : readBytes s.mem (ep + k * 4) 4 = some bs) (hbs : bytesToNat bs = q)
    (hdoc : readBytes s.mem (b + q) 1 = some [bt])
    (hq : q < 2 ^ 32) (hk63 : k < 2 ^ 63) (hk64 : k + 1 < 2 ^ 64) :
    denoteCode calls whileBodyInstrs (stateAt env s) =
      some (stateAt (whileBodyOut env k sp b ep c q bt)
        { s with mem := writeBytes s.mem (c + 32) (wordBytes 8 (k + 1)) }) := by
  simp only [whileBodyInstrs, whileBodyOut]
  walk_eval

/-- **The header's terminator**: `br NodeBlock21`, at the state its chain leaves. -/
theorem whileBody_term {calls : Calls} (s : State)
    {k sp ep b c q : Nat} {bs : List UInt8} {bt : UInt8}
    (hpc : s.pc = "while.body.i")
    (h5 : lookupName s.env "%5" = some (.ptr ep))
    (h3 : lookupName s.env "%3" = some (.ptr b))
    (hK : lookupName s.env "%k11.i" = some (.ptr (c + 32)))
    (hk2 : lookupName s.env "%k.2.i" = some (.int 64 (BitVec.ofNat 64 k)))
    (hsp1 : lookupName s.env "%sp.i.1" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hpre : s.pre = some "cleanup478.i")
    (hread : readBytes s.mem (ep + k * 4) 4 = some bs) (hbs : bytesToNat bs = q)
    (hdoc : readBytes s.mem (b + q) 1 = some [bt])
    (hq : q < 2 ^ 32) (hk63 : k < 2 ^ 63) (hk64 : k + 1 < 2 ^ 64) :
    step calls stage2Body s =
      .jump { (stateAt (whileBodyOut s.env k sp b ep c q bt)
          { s with mem := writeBytes s.mem (c + 32) (wordBytes 8 (k + 1)) }) with
        pc := "NodeBlock21", pre := some "while.body.i" } := by
  have hden := whileBody_denote (calls := calls) (env := s.env) (s := s)
    h5 h3 hK hk2 hsp1 hpre hread hbs hdoc hq hk63 hk64
  simp only [step, hpc, whileBody_find, whileBodyBlock]
  rw [show denoteCode calls whileBodyInstrs s =
      some (stateAt (whileBodyOut s.env k sp b ep c q bt)
        { s with mem := writeBytes s.mem (c + 32) (wordBytes 8 (k + 1)) }) from by
    rw [← stateAt_self s]; exact hden]
  simp only [execTerm, hpc]
  rfl

end LeanLLVM.Refinement

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.BlockEval

/-! ### Separation, for the two steps' memory and log claims -/

theorem pairwise_of_mem_ne {l : List (Nat × Nat)}
    (h : List.Pairwise (fun r s => r.1 + r.2 ≤ s.1 ∨ s.1 + s.2 ≤ r.1) l)
    {r s : Nat × Nat} (hr : r ∈ l) (hs : s ∈ l) (hne : r ≠ s) :
    r.1 + r.2 ≤ s.1 ∨ s.1 + s.2 ≤ r.1 := by
  induction l with
  | nil => exact absurd hr (by simp)
  | cons x xs ih =>
      rw [List.pairwise_cons] at h
      obtain ⟨hx, hxs⟩ := h
      rcases List.mem_cons.mp hr with rfl | hr'
      · rcases List.mem_cons.mp hs with rfl | hs'
        · exact absurd rfl hne
        · exact hx s hs'
      · rcases List.mem_cons.mp hs with rfl | hs'
        · rcases hx r hr' with h' | h'
          · exact Or.inr h'
          · exact Or.inl h'
        · exact ih hxs hr' hs'

/-- Two members of the walk's staged list are separated. -/
theorem staged_pair {b n ep nep xp nxp dst ndst0 ev evcap ndst nev err
    c ctype cst tok sv z e nkSlot nxpSlot : Nat}
    (h : DisjointRegions (stage2StagedRegions b n ep nep xp nxp dst ndst0 ev evcap
      ndst nev err c ctype cst tok sv z e nkSlot nxpSlot))
    {r q : Nat × Nat}
    (hr : r ∈ stage2WalkRegions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err
      c ctype cst tok sv z e)
    (hq : q ∈ stage2WalkRegions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err
      c ctype cst tok sv z e) (hne : r ≠ q) :
    r.1 + r.2 ≤ q.1 ∨ q.1 + q.2 ≤ r.1 := by
  have h' : (stage2WalkRegions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err
      c ctype cst tok sv z e).Pairwise
      (fun r s => r.1 + r.2 ≤ s.1 ∨ s.1 + s.2 ≤ r.1) := by
    unfold DisjointRegions at h
    rw [stage2StagedRegions] at h
    exact (List.pairwise_append.mp h).1
  exact pairwise_of_mem_ne h' hr hq hne

/-- **The cursor record and the log are separate**, read off the staging. -/
theorem cursor_log_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkInv G C s) :
    C.stage.c + stage2CursorExtent ≤ C.stage.z ∨
      C.stage.z + stage2LogExtent ≤ C.stage.c := by
  have hmem : ∀ r ∈ stage2StagedWrites C.stage.c C.stage.ctype C.stage.cst
      C.stage.tok C.stage.s C.stage.z C.stage.e,
      r ∈ stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
        G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst
        C.stage.tok C.stage.s C.stage.z C.stage.e :=
    fun r hr => List.mem_append_right _ hr
  exact staged_pair C.stage.separate
    (hmem (C.stage.c, stage2CursorExtent) (by simp [stage2StagedWrites]))
    (hmem (C.stage.z, stage2LogExtent) (by simp [stage2StagedWrites]))
    (by simp [stage2CursorExtent, stage2LogExtent])

/-- **The type stack and the log are separate.** -/
theorem ctype_log_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkInv G C s) :
    C.stage.ctype + stage2StackExtent ≤ C.stage.z ∨
      C.stage.z + stage2LogExtent ≤ C.stage.ctype := by
  have hmem : ∀ r ∈ stage2StagedWrites C.stage.c C.stage.ctype C.stage.cst
      C.stage.tok C.stage.s C.stage.z C.stage.e,
      r ∈ stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
        G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst
        C.stage.tok C.stage.s C.stage.z C.stage.e :=
    fun r hr => List.mem_append_right _ hr
  exact staged_pair C.stage.separate
    (hmem (C.stage.ctype, stage2StackExtent) (by simp [stage2StagedWrites]))
    (hmem (C.stage.z, stage2LogExtent) (by simp [stage2StagedWrites]))
    (by simp [stage2StackExtent, stage2LogExtent])

/-- **The state stack and the log are separate.** -/
theorem cst_log_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkInv G C s) :
    C.stage.cst + stage2StackExtent ≤ C.stage.z ∨
      C.stage.z + stage2LogExtent ≤ C.stage.cst := by
  have hmem : ∀ r ∈ stage2StagedWrites C.stage.c C.stage.ctype C.stage.cst
      C.stage.tok C.stage.s C.stage.z C.stage.e,
      r ∈ stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
        G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst
        C.stage.tok C.stage.s C.stage.z C.stage.e :=
    fun r hr => List.mem_append_right _ hr
  exact staged_pair C.stage.separate
    (hmem (C.stage.cst, stage2StackExtent) (by simp [stage2StagedWrites]))
    (hmem (C.stage.z, stage2LogExtent) (by simp [stage2StagedWrites]))
    (by simp [stage2StackExtent, stage2LogExtent])

/-- **A write into the cursor record leaves the log alone.** -/
theorem readBytes_log_of_cursor_write {m : Mem} {c z : Nat} {v : List UInt8}
    (hcz : c + stage2CursorExtent ≤ z ∨ z + stage2LogExtent ≤ c)
    (hv : v.length ≤ 8) {off len : Nat} (hoff : off + len ≤ stage2LogExtent) :
    readBytes (writeBytes m (c + 32) v) (z + off) len = readBytes m (z + off) len := by
  refine walkReadBytes_writeBytes_outside (start := c + 32) ?_
  rcases hcz with hcz | hcz
  · right
    simp only [stage2CursorExtent, stage2LogExtent] at *
    omega
  · left
    simp only [stage2CursorExtent, stage2LogExtent] at *
    omega

/-- **A write into a container stack at a depth inside it leaves the log alone.** -/
theorem readBytes_log_of_stack_write {m : Mem} {base z : Nat} {v : List UInt8} {sp : Nat}
    (hbz : base + stage2StackExtent ≤ z ∨ z + stage2LogExtent ≤ base)
    (hsp : sp < stage2StackExtent) (hv : v.length ≤ 1)
    {off len : Nat} (hoff : off + len ≤ stage2LogExtent) :
    readBytes (writeBytes m (base + sp) v) (z + off) len = readBytes m (z + off) len := by
  refine walkReadBytes_writeBytes_outside (start := base + sp) ?_
  rcases hbz with hbz | hbz
  · right
    simp only [stage2StackExtent, stage2LogExtent] at *
    omega
  · left
    simp only [stage2StackExtent, stage2LogExtent] at *
    omega

end LeanLLVM.Refinement

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.BlockEval

end LeanLLVM.Refinement
namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.BlockEval

/-- **Two staged ABI objects, by index, are separate.**  The list is a literal, so
a position names an object without needing the pair's own disequality. -/
theorem stage2Regions_sep {b n ep nep xp nxp dst ndst0 ev evcap ndst nev err : Nat}
    (h : DisjointRegions (stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err))
    {i j : Nat} (hi : i < (stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err).length)
    (hj : j < (stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err).length)
    (hij : i < j) :
    ((stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err)[i]).1 +
        ((stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err)[i]).2 ≤
        ((stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err)[j]).1 ∨
      ((stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err)[j]).1 +
        ((stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err)[j]).2 ≤
        ((stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err)[i]).1 :=
  (List.pairwise_iff_getElem.mp h) i j hi hj hij

/-- **A byte range separated from the walk's write families is outside its write
extents.**  The arena's prefix and the event stream's prefix are sub-intervals of
the staged arena and event entries; the seven are separated by the staging's own
list; and `%d.i`'s slot by the adapter's separation of it. -/
theorem walkPresent_outside {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkInv G C s) {a m : Nat}
    (hArena : a + m ≤ G.dst ∨ G.dst + (G.ndst0 + G.n + stage2ArenaReserve) ≤ a)
    (hEv : a + m ≤ G.ev ∨ G.ev + G.evcap ≤ a)
    (hSeven : ∀ r ∈ stage2StagedWrites C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e, r.1 + r.2 ≤ a ∨ a + m ≤ r.1)
    (hD : C.stage.d + 8 ≤ a ∨ a + m ≤ C.stage.d)
    {e : Nat} (ha : a ≤ e) (he : e < a + m) :
    ¬ inRegions (walkPresent G C) e := by
  have halen := h.alen_le
  have hev := h.evlen_le
  have hevroom := G.evRoom
  rintro ⟨r, hr, hlo, hhi⟩
  simp only [walkPresent, stage2ReportScratch] at hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_cons.mp hr with rfl | hr
    · rcases hArena with h' | h' <;> omega
    · rcases List.mem_cons.mp hr with rfl | hr
      · rcases hEv with h' | h' <;> omega
      · exact absurd hr (by simp)
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hSeven r hr with h' | h' <;> omega
    · rcases List.mem_cons.mp hr with rfl | hnil
      · rcases hD with h' | h' <;> omega
      · exact absurd hnil (by simp)

/-- **The entry stream is outside the walk's write extents.** -/
theorem WalkInv.entry_present_outside {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (h : WalkInv G C s) {e : Nat}
    (ha : G.ep ≤ e) (he : e < G.ep + 4 * G.nep) :
    ¬ inRegions (walkPresent G C) e := by
  have hsep := disjointRegions_staged_prefix C.stage.separate
  have h13 := stage2Regions_sep hsep (i := 1) (j := 3)
    (by simp [stage2Regions]) (by simp [stage2Regions]) (by decide)
  have h14 := stage2Regions_sep hsep (i := 1) (j := 4)
    (by simp [stage2Regions]) (by simp [stage2Regions]) (by decide)
  simp only [stage2Regions, List.getElem_cons_zero, List.getElem_cons_succ] at h13 h14
  refine walkPresent_outside h (a := G.ep) (m := 4 * G.nep) (e := e) ?_ ?_ ?_ ?_ ha he
  · omega
  · omega
  · intro r hr
    exact stage2StagedWrites_against C.stage.separate
      (a := G.ep) (m := 4 * G.nep) (by simp [stage2Regions]) r hr
  · rcases C.stage.dSep (G.ep, 4 * G.nep)
      (by simp [stage2WalkRegions, stage2Regions]) with hd | hd
    · exact Or.inr hd
    · exact Or.inl hd

/-- **The document's bytes are outside the walk's write extents.** -/
theorem WalkInv.doc_present_outside {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (h : WalkInv G C s) {e : Nat}
    (ha : G.b ≤ e) (he : e < G.b + G.n) :
    ¬ inRegions (walkPresent G C) e := by
  have hsep := disjointRegions_staged_prefix C.stage.separate
  have h03 := stage2Regions_sep hsep (i := 0) (j := 3)
    (by simp [stage2Regions]) (by simp [stage2Regions]) (by decide)
  have h04 := stage2Regions_sep hsep (i := 0) (j := 4)
    (by simp [stage2Regions]) (by simp [stage2Regions]) (by decide)
  simp only [stage2Regions, List.getElem_cons_zero, List.getElem_cons_succ] at h03 h04
  refine walkPresent_outside h (a := G.b) (m := G.n) (e := e) ?_ ?_ ?_ ?_ ha he
  · omega
  · omega
  · intro r hr
    have hout := stage2StagedWrites_against C.stage.separate
      (a := G.b) (m := G.n + stage2ReadTail) (by simp [stage2Regions]) r hr
    rcases hout with h' | h' <;> omega
  · rcases C.stage.dSep (G.b, G.n + stage2ReadTail)
      (by simp [stage2WalkRegions, stage2Regions]) with hd | hd
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)

/-- **The entry stream's bytes are outside the walk's whole frame.**  The write
extents are excluded above; the four stack slots by the watermark, since the byte
is inside an entry that ends at or below the cursor. -/
theorem WalkInv.entry_outside {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (h : WalkInv G C s) {e : Nat}
    (ha : G.ep ≤ e) (he : e < G.ep + 4 * G.nep) :
    ¬ inRegions (walkWide G C) e := by
  have hp := h.entry_present_outside ha he
  have hlt : e < G.next0 :=
    Nat.lt_of_lt_of_le he (G.watermark (G.ep, 4 * G.nep) (by simp [stage2Regions]))
  intro hw
  obtain ⟨r, hr, hlo, hhi⟩ := hw
  rcases List.mem_append.mp hr with hr | hr
  · exact hp ⟨r, hr, hlo, hhi⟩
  · exact not_walkAlloca_of_lt hlt ⟨r, hr, hlo, hhi⟩

/-- **The document's bytes are outside the walk's whole frame.** -/
theorem WalkInv.doc_outside {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (h : WalkInv G C s) {e : Nat}
    (ha : G.b ≤ e) (he : e < G.b + G.n) :
    ¬ inRegions (walkWide G C) e := by
  have hp := h.doc_present_outside ha he
  have hlt : e < G.next0 :=
    Nat.lt_of_lt_of_le (by omega)
      (G.watermark (G.b, G.n + stage2ReadTail) (by simp [stage2Regions]))
  intro hw
  obtain ⟨r, hr, hlo, hhi⟩ := hw
  rcases List.mem_append.mp hr with hr | hr
  · exact hp ⟨r, hr, hlo, hhi⟩
  · exact not_walkAlloca_of_lt hlt ⟨r, hr, hlo, hhi⟩

/-- **A write into the cursor record leaves the event stream's trace alone.** -/
theorem readBytes_ev_of_cursor_write {m : Mem} {c ev nev0 evcap N : Nat} {v : List UInt8}
    (hcev : c + stage2CursorExtent ≤ ev ∨ ev + evcap ≤ c) (hv : v.length ≤ 8)
    (hN : nev0 + N ≤ evcap) :
    readBytes (writeBytes m (c + 32) v) (ev + nev0) N = readBytes m (ev + nev0) N := by
  have hv' : stage2CursorExtent = 1192 := rfl
  refine walkReadBytes_writeBytes_outside (start := c + 32) ?_
  rcases hcev with hcev | hcev
  · right
    omega
  · left
    omega

/-- The event stream's staged entry is a member of the ABI list. -/
theorem stage2Regions_mem_ev {b n ep nep xp nxp dst ndst0 ev evcap ndst nev err : Nat} :
    (ev, evcap) ∈ stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err := by
  unfold stage2Regions
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self)))

/-- **The header's step**: one control step from the invariant at the header,
into `NodeBlock21`, with the index advanced, the depth read from the merge, the
invariant preserved and the measure strictly smaller. -/
theorem whileBody_step {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "while.body.i")
    {k sp : Nat}
    (hpre : s.pre = some "cleanup478.i")
    (hk2 : lookupName s.env "%k.2.i" = some (.int 64 (BitVec.ofNat 64 k)))
    (hsp1 : lookupName s.env "%sp.i.1" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hkge : C.k < k) (hklt : k < G.nep) (hspc : sp ≤ stage2StackExtent) :
    ∃ e : State,
      step calls stage2Body s = .jump e ∧
      WalkInv G { C with block := "NodeBlock21", k := k, sp := sp } e ∧
      walkMeasure G { C with block := "NodeBlock21", k := k, sp := sp } < walkMeasure G C ∧
      ∀ n, runFuel calls (1 + n) stage2Body s = runFuel calls n stage2Body e := by
  have hpc : s.pc = "while.body.i" := by rw [hInv.pc_eq, hblock]
  obtain ⟨h3, h5, hK, hct, hcst, hhash⟩ := hInv.ptrs
  -- the entry stream's lane, which is the next position
  obtain ⟨-, hget⟩ := readLanes32_nth (m := m0) (addr := G.ep) (n := G.nep)
    (l := G.ent) G.entries
  obtain ⟨q, bs, hqmem, hread0, hbs0⟩ := hget k hklt
  have hqin : q ∈ G.ent := List.mem_of_getElem? hqmem
  have hqn : q < G.n := G.inside q hqin
  -- its read at the run's memory, and the document's byte at that position
  have hread : readBytes s.mem (G.ep + k * 4) 4 = some bs := by
    rw [show G.ep + k * 4 = G.ep + 4 * k from by rw [Nat.mul_comm]]
    rw [readBytes_eq_of_UnchangedOn (mem := m0) (m := s.mem)
      (unchangedOutside_iff_inRegions.mp hInv.frame)
      (a := G.ep + 4 * k) (n := 4)
      (fun i hi => hInv.entry_outside (by omega) (by omega))]
    exact hread0
  have hdocr : readBytes m0 (G.b + q) 1 = some [G.bs.getD q 0] :=
    walkReadBytes_one_of_readByte (readByte_of_readBytes G.doc (k := q) hqn)
  have hdoc : readBytes s.mem (G.b + q) 1 = some [G.bs.getD q 0] := by
    rw [readBytes_eq_of_UnchangedOn (mem := m0) (m := s.mem)
      (unchangedOutside_iff_inRegions.mp hInv.frame)
      (a := G.b + q) (n := 1)
      (fun i hi => hInv.doc_outside (by omega) (by omega))]
    exact hdocr
  have hq32 : q < 2 ^ 32 := by
    rw [← hbs0]
    exact bytesToNat_lt_32 (walkReadBytes_length hread0)
  have hmax : G.n ≤ 2 ^ 32 := G.maxDoc
  have hk63 : k < 2 ^ 63 := by have h := G.nep_le; omega
  have hk64 : k + 1 < 2 ^ 64 := by have h := G.nep_le; omega
  -- the log's fields are untouched by the cursor store, and so is the trace
  have hcz := cursor_log_sep hInv
  have hcev : C.stage.c + stage2CursorExtent ≤ G.ev ∨ G.ev + G.evcap ≤ C.stage.c := by
    have h := stage2StagedWrites_against C.stage.separate
      (a := G.ev) (m := G.evcap) (stage2Regions_mem_ev)
      (r := (C.stage.c, stage2CursorExtent)) (by simp [stage2StagedWrites])
    simpa using h
  have hN : G.nev0 + (C.events.map EventRecord.encodedBytes).flatten.length ≤ G.evcap := by
    have hsum := EventRecord.sum_encodedSize_le C.events
    simp only [stage2RecordBytes] at hsum
    have h4' := G.evRoom
    simp only [stage2RecordBytes] at h4'
    have hlen : (C.events.map EventRecord.encodedBytes).flatten.length =
        (C.events.map EventRecord.encodedSize).sum := by
      simp only [List.length_flatten, List.map_map]
      rfl
    have h1 := hInv.events_le
    have h2 := hInv.k_le
    have h3 := G.nep_le
    omega
  let e : State :=
    { (stateAt (whileBodyOut s.env k sp G.b G.ep C.stage.c q (G.bs.getD q 0))
        { s with mem := writeBytes s.mem (C.stage.c + 32) (wordBytes 8 (k + 1)) }) with
      pc := "NodeBlock21"
      pre := some "while.body.i" }
  have hstep : step calls stage2Body s = .jump e :=
    whileBody_term (calls := calls) (s := s) hpc h5 h3 hK hk2 hsp1 hpre
      hread hbs0 hdoc hq32 hk63 hk64
  refine ⟨e, hstep, ?_, ?_, ?_⟩
  · refine
      { pc_eq := rfl
        blockIndex := ?_
        k_le := le_of_lt hklt
        events_le := le_trans hInv.events_le (le_of_lt hkge)
        evlen_eq := hInv.evlen_eq
        evBytes := ?_
        alen_le_sum := hInv.alen_le_sum
        alen_ge := hInv.alen_ge
        spans_order := hInv.spans_order
        spans_inside := hInv.spans_inside
        pending_at := hInv.pending_at
        pending_cursor := hInv.pending_cursor
        pending_len := hInv.pending_len
        eoff_le := hInv.eoff_le
        inner_cap := hInv.inner_cap
        depth_cap := hspc
        depth_reg := ?_
        ptrs := ?_
        log_hash := ?_
        log_len := ?_
        log_cap := ?_
        log_alen := ?_
        log_acap := ?_
        owned := walkStaged_write rfl hInv.owned
        frame := ?_
        blockLocal := ?_ }
    · dsimp only [e, stateAt, whileBodyOut, cells]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
    · dsimp only [e, stateAt]
      rw [readBytes_ev_of_cursor_write (c := C.stage.c) (ev := G.ev) (nev0 := G.nev0)
        (evcap := G.evcap) (N := (C.events.map EventRecord.encodedBytes).flatten.length)
        hcev (by simp [wordBytes, natToBytes_length]) hN]
      exact hInv.evBytes
    · dsimp only [e, stateAt, whileBodyOut, cells]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
        lookupName_cons_self]
    · dsimp only [e, stateAt]
      exact hInv.ptrs.cells_of _
        (fun c hc => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    · dsimp only [e, stateAt]
      rw [readBytes_log_of_cursor_write (c := C.stage.c) (z := C.stage.z) hcz
        (by simp [wordBytes, natToBytes_length]) (off := 32) (len := 4) (by decide)]
      exact hInv.log_hash
    · dsimp only [e, stateAt]
      rw [readBytes_log_of_cursor_write (c := C.stage.c) (z := C.stage.z) hcz
        (by simp [wordBytes, natToBytes_length]) (off := 8) (len := 8) (by decide)]
      exact hInv.log_len
    · dsimp only [e, stateAt]
      rw [readBytes_log_of_cursor_write (c := C.stage.c) (z := C.stage.z) hcz
        (by simp [wordBytes, natToBytes_length]) (off := 16) (len := 8) (by decide)]
      exact hInv.log_cap
    · dsimp only [e, stateAt]
      rw [readBytes_log_of_cursor_write (c := C.stage.c) (z := C.stage.z) hcz
        (by simp [wordBytes, natToBytes_length]) (off := 48) (len := 8) (by decide)]
      exact hInv.log_alen
    · dsimp only [e, stateAt]
      rw [readBytes_log_of_cursor_write (c := C.stage.c) (z := C.stage.z) hcz
        (by simp [wordBytes, natToBytes_length]) (off := 56) (len := 8) (by decide)]
      exact hInv.log_acap
    · dsimp only [e]
      exact walkFrame_cursorK (G := G) (C := C)
        (v := wordBytes 8 (k + 1)) (by simp [wordBytes, natToBytes_length]) hInv.frame
    · dsimp only [e]
      unfold WalkLocal
      simp
  · exact walkMeasure_step G C _ hkge (le_of_lt hklt) hInv.inner_cap
  · intro n
    rw [show 1 + n = n + 1 from by omega]
    simp only [runFuel, hstep]

end LeanLLVM.Refinement

/-! ### The header step's footprints, measured

Each is `#print axioms` on the declaration itself.  The three that read a
`String` register name — `whileBody_find`, its chain and its terminator — carry
`Classical.choice` beside `propext` and `Quot.sound`, which is the ceiling the
file's other pinned declarations report; the binding lemmas and the reads are at
or below `[propext, Quot.sound]`. -/

/-- info: 'LeanLLVM.Refinement.WalkPtrs.bind' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkPtrs.bind

/-- info: 'LeanLLVM.Refinement.WalkPtrs.cells_of' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkPtrs.cells_of

/-- info: 'LeanLLVM.Refinement.walkReadBytes_writeBytes_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.walkReadBytes_writeBytes_outside

/-- info: 'LeanLLVM.Refinement.readLanes32_nth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.readLanes32_nth

/-- info: 'LeanLLVM.Refinement.stage2Regions_sep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.stage2Regions_sep

/-- info: 'LeanLLVM.Refinement.WalkInv.entry_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkInv.entry_outside

/-- info: 'LeanLLVM.Refinement.WalkInv.doc_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkInv.doc_outside

/-- info: 'LeanLLVM.Refinement.whileBody_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.whileBody_find

/-- info: 'LeanLLVM.Refinement.whileBody_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.whileBody_denote

/-- info: 'LeanLLVM.Refinement.whileBody_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.whileBody_term

/-- info: 'LeanLLVM.Refinement.whileBody_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.whileBody_step
namespace LeanLLVM.Refinement
namespace WalkScope

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.BlockEval

/-! ## A: the append lemma for phi-free runs -/

theorem walkDenoteRun_append_of {calls : Calls} :
    ∀ (is : List Instr) (pend : List (String × Value)) (js : List Instr) (s : State),
      is.any Instr.isPhi = false → startsWithPhi js = false →
      denoteRun calls pend (is ++ js) s
        = (denoteRun calls pend is s).bind (denoteRun calls [] js)
  | [], pend, js, s, _, hjs => by
      simp only [List.nil_append, denoteRun, Option.bind_some]
      exact denoteRun_nil_pend hjs
  | i :: is, pend, js, s, h, hjs => by
      have hi : i.isPhi = false := by
        simpa using List.any_eq_false.mp h i (by simp)
      have htail : is.any Instr.isPhi = false := by
        rw [List.any_eq_false] at h ⊢
        exact fun j hj => h j (by simp [hj])
      rw [show (i :: is) ++ js = i :: (is ++ js) from rfl,
          denoteRun_cons_of (calls := calls) (pend := pend) hi,
          denoteRun_cons_of (calls := calls) (pend := pend) hi]
      cases evalInstr calls (s.bindAll pend) i with
      | none => rfl
      | some s' => exact walkDenoteRun_append_of is [] js s' htail hjs

theorem walkDenoteCode_append_some {calls : Calls} {is js : List Instr} {s s' : State}
    (his : is.any Instr.isPhi = false) (hjs : startsWithPhi js = false)
    (h : denoteCode calls is s = some s') :
    denoteCode calls (is ++ js) s = denoteCode calls js s' := by
  rw [denoteCode] at h ⊢
  rw [walkDenoteRun_append_of (calls := calls) is [] js s his hjs, h]
  rfl




/-! ## C: the nesting arm's block -/

theorem walkEvalICmp_eq_self {w : Nat} (a : BitVec w) : evalICmp .eq a a = 1 := by
  simp [evalICmp]

/-- A bind at a name the list does not carry leaves a lookup alone. -/
theorem walkLookup_cells_ne (env : Env) (n : String) {v : Value}
    (h : lookupName env n = some v) (cs : List (String × Value))
    (hne : ∀ c ∈ cs, c.1 ≠ n) : lookupName (cells cs env) n = some v := by
  induction cs with
  | nil => exact h
  | cons c rest ih =>
      simp only [cells, lookupName_cons_ne c.2 (cells rest env) (hne c (by simp))]
      exact ih (fun c' hc' => hne c' (by simp [hc']))

/-- The chain's first nine instructions. -/
def ifEnd24Head : List Instr := [
  Instr.icmp "%cmp26.i" IPred.eq 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 123))),
  Instr.select "%conv28.i" (Ty.int 8) (.reg "%cmp26.i")
    (.imm (.int 8 (BitVec.ofNat 8 1))) (.imm (.int 8 (BitVec.ofNat 8 2))),
  Instr.zext "%idxprom29.i" 32 64 (.reg "%sp.i.0248"),
  Instr.gep "%arrayidx30.i" (Ty.int 8) (.reg "%ctype.i") (.reg "%idxprom29.i"),
  Instr.store (Ty.int 8) (.reg "%conv28.i") (.reg "%arrayidx30.i"),
  Instr.gep "%arrayidx32.i" (Ty.int 8) (.reg "%cst.i") (.reg "%idxprom29.i"),
  Instr.store (Ty.int 8) (.imm (.int 8 (BitVec.ofNat 8 0))) (.reg "%arrayidx32.i"),
  Instr.binop "%inc33.i" BinOp.add 32 (.reg "%sp.i.0248")
    (.imm (.int 32 (BitVec.ofNat 32 1))),
  Instr.select "%conv42.i" (Ty.int 8) (.reg "%cmp26.i")
    (.imm (.int 8 (BitVec.ofNat 8 1))) (.imm (.int 8 (BitVec.ofNat 8 3)))]

/-- The chain's last two instructions, written by hand. -/
def ifEnd24Tail : List Instr := [
  Instr.load "%10" (Ty.int 32) (.reg "%hash1.i.i"),
  Instr.icmp "%tobool.not.i.i" IPred.eq 32 (.reg "%10")
    (.imm (.int 32 (BitVec.ofNat 32 0)))]

def ifEnd24Instrs : List Instr := ifEnd24Head ++ ifEnd24Tail

theorem ifEnd24Instrs_split : ifEnd24Instrs = ifEnd24Head ++ ifEnd24Tail := rfl

def ifEnd24Block : Block :=
  { name := "if.end24.i", instrs := ifEnd24Instrs,
    term := Term.condbr (.reg "%tobool.not.i.i") "if.end.i.i" "if.then.i.i" }

theorem ifEnd24_find : stage2Body.findBlock "if.end24.i" = some ifEnd24Block := by
  simp [stage2Body, Function.findBlock, findBlockList, ifEnd24Block, ifEnd24Instrs,
    ifEnd24Head, ifEnd24Tail]

/-- `%cmp26.i`: the test the arm's two selects read. -/
def ifEnd24Test (b : BitVec 8) : BitVec 1 :=
  evalICmp .eq b (BitVec.ofNat 8 123)

/-- `%conv28.i`, the byte the type stack receives. -/
def ifEnd24Ty (b : BitVec 8) : BitVec 8 :=
  if ifEnd24Test b = 1 then 1 else 2

/-- `%conv42.i`, the byte the state stack receives. -/
def ifEnd24St (b : BitVec 8) : BitVec 8 :=
  if ifEnd24Test b = 1 then 1 else 3

/-- The head's cells, newest first. -/
def ifEnd24HeadCells (sp ctype cst : Nat) (b : BitVec 8) : List (String × Value) :=
  [("%conv42.i", .int 8 (ifEnd24St b)),
   ("%inc33.i", .int 32 (BitVec.ofNat 32 (sp + 1))),
   ("%arrayidx32.i", .ptr (cst + sp)),
   ("%arrayidx30.i", .ptr (ctype + sp)),
   ("%idxprom29.i", .int 64 (BitVec.ofNat 64 sp)),
   ("%conv28.i", .int 8 (ifEnd24Ty b)),
   ("%cmp26.i", .int 1 (ifEnd24Test b))]

/-- The tail's cells, newest first. -/
def ifEnd24TailCells : List (String × Value) :=
  [("%tobool.not.i.i", .int 1 (evalICmp .eq (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))),
   ("%10", .int 32 (BitVec.ofNat 32 0))]

def ifEnd24Mid (env : Env) (sp ctype cst : Nat) (b : BitVec 8) : Env :=
  cells (ifEnd24HeadCells sp ctype cst b) env

def ifEnd24Out (env : Env) (sp ctype cst : Nat) (b : BitVec 8) : Env :=
  cells ifEnd24TailCells (ifEnd24Mid env sp ctype cst b)

theorem ifEnd24Head_denote {calls : Calls} (env : Env) (s : State)
    {sp ctype cst : Nat} {b : BitVec 8}
    (h8 : lookupName env "%8" = some (.int 8 b))
    (hspv : lookupName env "%sp.i.0248" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hct : lookupName env "%ctype.i" = some (.ptr ctype))
    (hcs : lookupName env "%cst.i" = some (.ptr cst))
    (hsp32 : sp < 2 ^ 32) :
    denoteCode calls ifEnd24Head (stateAt env s) =
      some (stateAt (ifEnd24Mid env sp ctype cst b)
        { s with mem := writeBytes (writeBytes s.mem (ctype + sp)
            (natToBytes (ifEnd24Ty b).toNat 1)) (cst + sp) (natToBytes 0 1) }) := by
  simp only [ifEnd24Head, ifEnd24Mid, ifEnd24HeadCells]
  walk_eval

/-- The last two instructions, written by hand: the hash word's load and the
branch test it feeds. -/
theorem ifEnd24Tail_denote {calls : Calls} (env : Env) (s : State) {z : Nat}
    (hhash : lookupName env "%hash1.i.i" = some (.ptr (z + 32)))
    (hread : readBytes s.mem (z + 32) 4 = some (natToBytes 0 4)) :
    denoteCode calls ifEnd24Tail (stateAt env s) =
      some (stateAt (cells ifEnd24TailCells env) s) := by
  simp only [ifEnd24Tail, ifEnd24TailCells]
  rw [denoteCode_load32 calls env s "%10" "%hash1.i.i" hhash hread (q := 0) (by rfl) _]
  rw [denoteCode_icmp_eq_imm_w calls (("%10", .int 32 (BitVec.ofNat 32 0)) :: env) s
    "%tobool.not.i.i" "%10" 32 (x := BitVec.ofNat 32 0) (c := BitVec.ofNat 32 0)
    (by rfl) []]
  rfl

theorem ifEnd24_denote {calls : Calls} (env : Env) (s : State)
    {sp ctype cst z : Nat} {b : BitVec 8}
    (h8 : lookupName env "%8" = some (.int 8 b))
    (hspv : lookupName env "%sp.i.0248" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hct : lookupName env "%ctype.i" = some (.ptr ctype))
    (hcs : lookupName env "%cst.i" = some (.ptr cst))
    (hhash : lookupName env "%hash1.i.i" = some (.ptr (z + 32)))
    (hsp : sp < stage2StackExtent)
    (hcz : ctype + stage2StackExtent ≤ z ∨ z + stage2LogExtent ≤ ctype)
    (hsz : cst + stage2StackExtent ≤ z ∨ z + stage2LogExtent ≤ cst)
    (hread : readBytes s.mem (z + 32) 4 = some (natToBytes 0 4)) :
    denoteCode calls ifEnd24Instrs (stateAt env s) =
      some (stateAt (ifEnd24Out env sp ctype cst b)
        { s with mem := writeBytes (writeBytes s.mem (ctype + sp)
            (natToBytes (ifEnd24Ty b).toNat 1)) (cst + sp) (natToBytes 0 1) }) := by
  have hsp32 : sp < 2 ^ 32 := by
    have h520 : stage2StackExtent = 520 := rfl
    omega
  have hread' : readBytes (writeBytes (writeBytes s.mem (ctype + sp)
      (natToBytes (ifEnd24Ty b).toNat 1)) (cst + sp) (natToBytes 0 1))
      (z + 32) 4 = some (natToBytes 0 4) := by
    rw [readBytes_log_of_stack_write (base := cst) (v := natToBytes 0 1) hsz
      (sp := sp) hsp (by simp [natToBytes]) (off := 32) (len := 4) (by decide)]
    rw [readBytes_log_of_stack_write (base := ctype)
      (v := natToBytes (ifEnd24Ty b).toNat 1) hcz
      (sp := sp) hsp (by simp [natToBytes]) (off := 32) (len := 4) (by decide)]
    exact hread
  rw [ifEnd24Instrs_split]
  rw [walkDenoteCode_append_some (calls := calls) (is := ifEnd24Head) (js := ifEnd24Tail)
    (s := stateAt env s)
    (s' := stateAt (ifEnd24Mid env sp ctype cst b)
      { s with mem := writeBytes (writeBytes s.mem (ctype + sp)
          (natToBytes (ifEnd24Ty b).toNat 1)) (cst + sp) (natToBytes 0 1) })
    (by decide) (by decide)
    (ifEnd24Head_denote (calls := calls) env s h8 hspv hct hcs hsp32)]
  exact ifEnd24Tail_denote (calls := calls) (ifEnd24Mid env sp ctype cst b) _ hhash hread'




/-! ### The event stream and the two stacks' separation -/

theorem ctype_ev_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (_h : WalkInv G C s) :
    C.stage.ctype + stage2StackExtent ≤ G.ev ∨ G.ev + G.evcap ≤ C.stage.ctype := by
  have hpair : (stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e).Pairwise
      (fun r q => r.1 + r.2 ≤ q.1 ∨ q.1 + q.2 ≤ r.1) := by
    have hsep := C.stage.separate
    unfold DisjointRegions at hsep
    rw [stage2StagedRegions] at hsep
    exact (List.pairwise_append.mp hsep).1
  have hlen : (stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e).length = 15 := by
    simp [stage2WalkRegions, stage2Regions, stage2StagedWrites]
  have h' := List.pairwise_iff_getElem.mp hpair 4 9 (by omega) (by omega) (by omega)
  simpa [stage2WalkRegions, stage2Regions, stage2StagedWrites] using h'.symm

theorem cst_ev_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (_h : WalkInv G C s) :
    C.stage.cst + stage2StackExtent ≤ G.ev ∨ G.ev + G.evcap ≤ C.stage.cst := by
  have hpair : (stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e).Pairwise
      (fun r q => r.1 + r.2 ≤ q.1 ∨ q.1 + q.2 ≤ r.1) := by
    have hsep := C.stage.separate
    unfold DisjointRegions at hsep
    rw [stage2StagedRegions] at hsep
    exact (List.pairwise_append.mp hsep).1
  have hlen : (stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e).length = 15 := by
    simp [stage2WalkRegions, stage2Regions, stage2StagedWrites]
  have h' := List.pairwise_iff_getElem.mp hpair 4 10 (by omega) (by omega) (by omega)
  simpa [stage2WalkRegions, stage2Regions, stage2StagedWrites] using h'.symm

theorem readBytes_ev_of_stack_write {m : Mem} {base ev evcap nev0 N : Nat}
    {v : List UInt8} {sp : Nat}
    (hbev : base + stage2StackExtent ≤ ev ∨ ev + evcap ≤ base)
    (hsp : sp < stage2StackExtent) (hv : v.length ≤ 1) (hN : nev0 + N ≤ evcap) :
    readBytes (writeBytes m (base + sp) v) (ev + nev0) N = readBytes m (ev + nev0) N := by
  refine walkReadBytes_writeBytes_outside (start := base + sp) ?_
  rcases hbev with hbev | hbev
  · right
    simp only [stage2StackExtent] at *
    omega
  · left
    omega

/-! ### The nesting arm's terminator -/

theorem ifEnd24Out_branch (s : State) {env : Env} {sp ctype cst : Nat} {b : BitVec 8} :
    evalOperand (stateAt (ifEnd24Out env sp ctype cst b) s) (.reg "%tobool.not.i.i")
      = some (.int 1 1) := by
  dsimp only [stateAt, evalOperand, ifEnd24Out, ifEnd24TailCells, cells]
  rw [lookupName_cons_self]
  simp [walkEvalICmp_eq_self]

theorem ifEnd24_term {calls : Calls} (s : State)
    {sp ctype cst z : Nat} {b : BitVec 8}
    (hpc : s.pc = "if.end24.i")
    (h8 : lookupName s.env "%8" = some (.int 8 b))
    (hspv : lookupName s.env "%sp.i.0248" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hct : lookupName s.env "%ctype.i" = some (.ptr ctype))
    (hcs : lookupName s.env "%cst.i" = some (.ptr cst))
    (hhash : lookupName s.env "%hash1.i.i" = some (.ptr (z + 32)))
    (hsp : sp < stage2StackExtent)
    (hcz : ctype + stage2StackExtent ≤ z ∨ z + stage2LogExtent ≤ ctype)
    (hsz : cst + stage2StackExtent ≤ z ∨ z + stage2LogExtent ≤ cst)
    (hread : readBytes s.mem (z + 32) 4 = some (natToBytes 0 4)) :
    step calls stage2Body s =
      .jump { (stateAt (ifEnd24Out s.env sp ctype cst b)
          { s with mem := writeBytes (writeBytes s.mem (ctype + sp)
              (natToBytes (ifEnd24Ty b).toNat 1)) (cst + sp) (natToBytes 0 1) }) with
        pc := "if.end.i.i", pre := some "if.end24.i" } := by
  have hden := ifEnd24_denote (calls := calls) (env := s.env) (s := s)
    h8 hspv hct hcs hhash hsp hcz hsz hread
  simp only [step, hpc, ifEnd24_find, ifEnd24Block]
  rw [show denoteCode calls ifEnd24Instrs s =
      some (stateAt (ifEnd24Out s.env sp ctype cst b)
        { s with mem := writeBytes (writeBytes s.mem (ctype + sp)
            (natToBytes (ifEnd24Ty b).toNat 1)) (cst + sp) (natToBytes 0 1) }) from by
    rw [← stateAt_self s]; exact hden]
  dsimp only
  unfold execTerm
  dsimp only
  rw [ifEnd24Out_branch]
  simp [hpc, stateAt]




/-- **The nesting arm's step**: one control step from the invariant at
`if.end24.i` into `if.end.i.i`, the branch the log's zeroed hash word fixes, with
the two container stacks written at the carried depth, every clause preserved and
the measure unchanged (this block advances neither the entry index nor the inner
work). -/
theorem ifEnd24_step {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.end24.i")
    {b : BitVec 8} (h8 : lookupName s.env "%8" = some (.int 8 b))
    (hguard : NestGuard C.sp) :
    ∃ e : State,
      step calls stage2Body s = .jump e ∧
      WalkInv G { C with block := "if.end.i.i" } e ∧
      walkMeasure G { C with block := "if.end.i.i" } = walkMeasure G C ∧
      ∀ n, runFuel calls (1 + n) stage2Body s = runFuel calls n stage2Body e := by
  have hpc : s.pc = "if.end24.i" := by rw [hInv.pc_eq, hblock]
  obtain ⟨h3, h5, hK, hct, hcst, hhash⟩ := hInv.ptrs
  have hspv := hInv.depth_reg
  have hspExt : C.sp < stage2StackExtent := by
    have h520 : stage2StackExtent = 520 := rfl
    have := hguard
    simp only [NestGuard] at this
    omega
  have hcz := ctype_log_sep hInv
  have hsz := cst_log_sep hInv
  have hcev := ctype_ev_sep hInv
  have hsev := cst_ev_sep hInv
  have hN : G.nev0 + (C.events.map EventRecord.encodedBytes).flatten.length ≤ G.evcap := by
    have hsum := EventRecord.sum_encodedSize_le C.events
    simp only [stage2RecordBytes] at hsum
    have h4' := G.evRoom
    simp only [stage2RecordBytes] at h4'
    have hlen : (C.events.map EventRecord.encodedBytes).flatten.length =
        (C.events.map EventRecord.encodedSize).sum := by
      simp only [List.length_flatten, List.map_map]
      rfl
    have h1 := hInv.events_le
    have h2 := hInv.k_le
    have h3 := G.nep_le
    omega
  let e : State :=
    { (stateAt (ifEnd24Out s.env C.sp C.stage.ctype C.stage.cst b)
        { s with mem := writeBytes (writeBytes s.mem (C.stage.ctype + C.sp)
            (natToBytes (ifEnd24Ty b).toNat 1)) (C.stage.cst + C.sp) (natToBytes 0 1) }) with
      pc := "if.end.i.i"
      pre := some "if.end24.i" }
  have hstep : step calls stage2Body s = .jump e :=
    ifEnd24_term (calls := calls) (s := s) hpc h8 hspv hct hcst hhash hspExt hcz hsz
      hInv.log_hash
  refine ⟨e, hstep, ?_, ?_, ?_⟩
  · refine
      { pc_eq := rfl
        blockIndex := ?_
        k_le := hInv.k_le
        events_le := hInv.events_le
        evlen_eq := hInv.evlen_eq
        evBytes := ?_
        alen_le_sum := hInv.alen_le_sum
        alen_ge := hInv.alen_ge
        spans_order := hInv.spans_order
        spans_inside := hInv.spans_inside
        pending_at := hInv.pending_at
        pending_cursor := hInv.pending_cursor
        pending_len := hInv.pending_len
        eoff_le := hInv.eoff_le
        inner_cap := hInv.inner_cap
        depth_cap := hInv.depth_cap
        depth_reg := ?_
        ptrs := ?_
        log_hash := ?_
        log_len := ?_
        log_cap := ?_
        log_alen := ?_
        log_acap := ?_
        owned := walkStaged_write rfl (walkStaged_write rfl hInv.owned)
        frame := ?_
        blockLocal := ?_ }
    · dsimp only [e, stateAt]
      exact walkLookup_cells_ne _ "%k.0.i249"
        (walkLookup_cells_ne s.env "%k.0.i249" hInv.blockIndex _
          (by
            intro c hc
            simp only [ifEnd24HeadCells, List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
        _
        (by
          intro c hc
          simp only [ifEnd24TailCells, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl <;> simp)
    · dsimp only [e, stateAt]
      rw [readBytes_ev_of_stack_write (base := C.stage.cst) (v := natToBytes 0 1) hsev
        (sp := C.sp) hspExt (by simp [natToBytes]) (ev := G.ev) (evcap := G.evcap)
        (nev0 := G.nev0) (N := (C.events.map EventRecord.encodedBytes).flatten.length) hN]
      rw [readBytes_ev_of_stack_write (base := C.stage.ctype)
        (v := natToBytes (ifEnd24Ty b).toNat 1) hcev (sp := C.sp) hspExt
        (by simp [natToBytes]) (ev := G.ev) (evcap := G.evcap) (nev0 := G.nev0)
        (N := (C.events.map EventRecord.encodedBytes).flatten.length) hN]
      exact hInv.evBytes
    · dsimp only [e, stateAt]
      exact walkLookup_cells_ne _ "%sp.i.0248"
        (walkLookup_cells_ne s.env "%sp.i.0248" hInv.depth_reg _
          (by
            intro c hc
            simp only [ifEnd24HeadCells, List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
        _
        (by
          intro c hc
          simp only [ifEnd24TailCells, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl <;> simp)
    · dsimp only [e, stateAt]
      exact (hInv.ptrs.cells_of (ifEnd24HeadCells C.sp C.stage.ctype C.stage.cst b)
        (by
          intro c hc
          simp only [ifEnd24HeadCells, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            exact ⟨by simp, by simp, by simp, by simp, by simp, by simp⟩)).cells_of
        ifEnd24TailCells
        (by
          intro c hc
          simp only [ifEnd24TailCells, List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl <;>
            exact ⟨by simp, by simp, by simp, by simp, by simp, by simp⟩)
    · dsimp only [e, stateAt]
      rw [readBytes_log_of_stack_write (base := C.stage.cst) (v := natToBytes 0 1) hsz
        (sp := C.sp) hspExt (by simp [natToBytes]) (off := 32) (len := 4) (by decide)]
      rw [readBytes_log_of_stack_write (base := C.stage.ctype)
        (v := natToBytes (ifEnd24Ty b).toNat 1) hcz (sp := C.sp) hspExt
        (by simp [natToBytes]) (off := 32) (len := 4) (by decide)]
      exact hInv.log_hash
    · dsimp only [e, stateAt]
      rw [readBytes_log_of_stack_write (base := C.stage.cst) (v := natToBytes 0 1) hsz
        (sp := C.sp) hspExt (by simp [natToBytes]) (off := 8) (len := 8) (by decide)]
      rw [readBytes_log_of_stack_write (base := C.stage.ctype)
        (v := natToBytes (ifEnd24Ty b).toNat 1) hcz (sp := C.sp) hspExt
        (by simp [natToBytes]) (off := 8) (len := 8) (by decide)]
      exact hInv.log_len
    · dsimp only [e, stateAt]
      rw [readBytes_log_of_stack_write (base := C.stage.cst) (v := natToBytes 0 1) hsz
        (sp := C.sp) hspExt (by simp [natToBytes]) (off := 16) (len := 8) (by decide)]
      rw [readBytes_log_of_stack_write (base := C.stage.ctype)
        (v := natToBytes (ifEnd24Ty b).toNat 1) hcz (sp := C.sp) hspExt
        (by simp [natToBytes]) (off := 16) (len := 8) (by decide)]
      exact hInv.log_cap
    · dsimp only [e, stateAt]
      rw [readBytes_log_of_stack_write (base := C.stage.cst) (v := natToBytes 0 1) hsz
        (sp := C.sp) hspExt (by simp [natToBytes]) (off := 48) (len := 8) (by decide)]
      rw [readBytes_log_of_stack_write (base := C.stage.ctype)
        (v := natToBytes (ifEnd24Ty b).toNat 1) hcz (sp := C.sp) hspExt
        (by simp [natToBytes]) (off := 48) (len := 8) (by decide)]
      exact hInv.log_alen
    · dsimp only [e, stateAt]
      rw [readBytes_log_of_stack_write (base := C.stage.cst) (v := natToBytes 0 1) hsz
        (sp := C.sp) hspExt (by simp [natToBytes]) (off := 56) (len := 8) (by decide)]
      rw [readBytes_log_of_stack_write (base := C.stage.ctype)
        (v := natToBytes (ifEnd24Ty b).toNat 1) hcz (sp := C.sp) hspExt
        (by simp [natToBytes]) (off := 56) (len := 8) (by decide)]
      exact hInv.log_acap
    · dsimp only [e, stateAt]
      exact walkFrame_cst (G := G) (C := C) (v := natToBytes 0 1)
        (by simp [natToBytes]) hguard
        (walkFrame_ctype (G := G) (C := C) (v := natToBytes (ifEnd24Ty b).toNat 1)
          (by simp [natToBytes]) hguard hInv.frame)
    · dsimp only [e, stateAt]
      simp [WalkLocal]
  · rfl
  · intro n
    rw [show 1 + n = n + 1 from by omega]
    simp only [runFuel, hstep]




/-! ### The dispatch's trace

The trace the obligation's completion conjunct is: a chain of the walk's own
control steps, each of which preserves `WalkInv` and does not raise
`walkMeasure`.  The chain is what an induction over the dispatch produces, block
by block; this section states it, proves that it carries the invariant and the
measure, and gives it the links the module has proved: the header's block, the
nesting arm, the latch, the four scan headers, and the censused classes A, B and
B′, the eighteen refusal stores of C, class D's ten stores, the two entry links,
class E's twelve merges and twelve of class G's fourteen reads — a hundred and
thirty-eight blocks in all.  The links between them are the 27 rows of the census's
remainder, and they are not supplied. -/

/-- **One link of the dispatch's trace**: a control step that preserves
`WalkInv` and does not raise the measure. -/
structure WalkLink (calls : Calls) {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (C' : WalkCarry G) (s' : State) : Prop where
  /-- The invariant holds at the link's source. -/
  inv : WalkInv G C s
  /-- The step is a control step into the link's target. -/
  step : step calls stage2Body s = .jump s'
  /-- The invariant holds at the link's target. -/
  inv' : WalkInv G C' s'
  /-- The measure does not rise across the link. -/
  mono : walkMeasure G C' ≤ walkMeasure G C

/-- **A trace**: a chain of links, from the invariant at its head to the invariant
at its tail. -/
inductive WalkChain (calls : Calls) {m0 : Mem} (G : WalkGeom m0) :
    WalkCarry G → State → WalkCarry G → State → Prop
  | nil {C : WalkCarry G} {s : State} (h : WalkInv G C s) :
      WalkChain calls G C s C s
  | tail {C C' C'' : WalkCarry G} {s s' s'' : State}
      (hl : WalkLink calls G C s C' s')
      (ht : WalkChain calls G C' s' C'' s'') :
      WalkChain calls G C s C'' s''

/-- A link's step, at `runFuel`: one control step is one fuel unit. -/
theorem walkLink_runFuel {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C C' : WalkCarry G} {s s' : State} (hl : WalkLink calls G C s C' s') (n : Nat) :
    runFuel calls (1 + n) stage2Body s = runFuel calls n stage2Body s' := by
  have hs : step calls stage2Body s = .jump s' := WalkLink.step hl
  rw [show 1 + n = n + 1 from by omega]
  simp only [runFuel, hs]

/-- **The trace carries the measure bound.**  Every link is non-increasing, so the
tail's measure is at most the head's. -/
theorem WalkChain.measure_le {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C C' : WalkCarry G} {s s' : State} (h : WalkChain calls G C s C' s') :
    walkMeasure G C' ≤ walkMeasure G C := by
  induction h with
  | nil => exact Nat.le_refl _
  | tail hl _ ih => exact le_trans ih hl.mono

/-- **The trace is a run.**  A chain of `k` links runs for `k` steps of fuel and
leaves exactly the fuel the tail needs, so a trace's end state is the run's state
at the head's fuel plus `k`. -/
theorem WalkChain.steps {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C C' : WalkCarry G} {s s' : State} (h : WalkChain calls G C s C' s') :
    ∃ k, ∀ n, runFuel calls (k + n) stage2Body s = runFuel calls n stage2Body s' := by
  induction h with
  | nil => exact ⟨0, fun n => by simp⟩
  | tail hl _ ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + 1, fun n => by
        rw [show k + 1 + n = 1 + (k + n) from by omega, walkLink_runFuel hl, hk]⟩

/-- **The trace to a return completes.**  At a state whose step returns, the chain
from the head gives the run's outcome: the completion conjunct, at the trace's own
step count. -/
theorem WalkChain.completes {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C C' : WalkCarry G} {s s' sret : State} {v : Value}
    (h : WalkChain calls G C s C' s') (hret : step calls stage2Body s' = .ret v sret) :
    ∃ k, runFuel calls k stage2Body s = some (.ret v sret.mem) := by
  obtain ⟨k, hk⟩ := h.steps
  refine ⟨k + 1, ?_⟩
  rw [hk 1]
  simp only [runFuel, hret]

/-- **The trace's first proved link: the header's block.**  `while.body.i` advances
the entry index and strictly lowers the measure. -/
theorem WalkLink.whileBody {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "while.body.i")
    {k sp : Nat}
    (hpre : s.pre = some "cleanup478.i")
    (hk2 : lookupName s.env "%k.2.i" = some (.int 64 (BitVec.ofNat 64 k)))
    (hsp1 : lookupName s.env "%sp.i.1" = some (.int 32 (BitVec.ofNat 32 sp)))
    (hkge : C.k < k) (hklt : k < G.nep) (hspc : sp ≤ stage2StackExtent) :
    ∃ s', WalkLink calls G C s { C with block := "NodeBlock21", k := k, sp := sp } s' := by
  obtain ⟨e, hstep, hinv, hmono, -⟩ :=
    whileBody_step (calls := calls) G C s hInv hblock hpre hk2 hsp1 hkge hklt hspc
  exact ⟨e, ⟨hInv, hstep, hinv, le_of_lt hmono⟩⟩

/-- **The trace's second proved link: the nesting arm.**  `if.end24.i` writes the
two container stacks and branches on the log's zeroed hash word, with the measure
unchanged.  Its `%8` binding is the caller's: the header loaded the document byte
at the entry's position, and the invariant does not carry it. -/
theorem WalkLink.ifEnd24 {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.end24.i")
    {b : BitVec 8} (h8 : lookupName s.env "%8" = some (.int 8 b))
    (hguard : NestGuard C.sp) :
    ∃ s', WalkLink calls G C s { C with block := "if.end.i.i" } s' := by
  obtain ⟨e, hstep, hinv, hmono, -⟩ := ifEnd24_step G C s hInv hblock h8 hguard
  exact ⟨e, ⟨hInv, hstep, hinv, le_of_eq hmono⟩⟩




/-! ## The middle's two classes

`WalkLink` is what the dispatch's trace is made of, and the two links above are
hand-written: a block's `denoteCode`, its terminator, and the twenty-two clauses
of `WalkInv` re-established one at a time.  At that price the ~140 blocks between
the arms are not writable, so the middle is classified instead, and each class is
one lemma whose instances differ only in the block's text.

## The census

The classification is a census of the pinned body's 165 blocks by the shape that
decides what a link proof costs.  The shape is the opcode sequence, because a
block's `denoteCode` is one step per instruction and what a step costs is set by
the instruction's constructor, not by the block's name.

| class | shape | blocks | proved |
|---|---|---:|---|
| A | one `icmp` and a `condbr` on its result | 60 | 60 |
| B | no instructions and a `br` | 9 | 9 |
| B′ | no instructions and a `condbr` on a carried bit | 1 | 1 |
| C | the refusal store: `gep %e+8`, `store i64`, `br` | 18 | 18 |
| D | other `store` shapes | 11 | 11 |
| E | a `phi`-headed block | 15 | 15 |
| F | a block that calls | 19 | 9 |
| G | `load` and compare | 14 | 14 |
| H1 | the arithmetic latch: `add` + `icmp` + `condbr` | 10 | 10 |
| H2 | `while.body.i.lr.ph` (five `gep`) and `if.then281.i` (`add`/`zext`/`or`) | 2 | 2 |
| — | `entry`, `if.end`, four `unreachable` traps | 6 | 0 |

**A hundred and forty-nine of the 165 blocks are links**, and the table's proved
column is the decomposition: 60 + 9 + 1 + 18 (A, B, B′, C) + 11 (D) + 15 (E) +
14 (G) + 10 (H1) + 2 (H2's `while.body.i.lr.ph` and `if.then281.i`) + 9 (F's
`JsonStage2WalkCall`) = 149, with the five measure arms among those classes rather
than beside them.  The remaining 16 are named below with their obstruction, one
row each; six of them are not links at all — the seed, the return, and the four
`unreachable` arms.

**The call census, measured.**  The F row's 19 is the number of blocks between the
arms whose instruction list contains an `Instr.call` or `Instr.callVoid`, read off
`stage2Body`'s own block list.  The callee of a value-returning call is the
instruction's *third* field: the first quoted string of `Instr.call "%call14.i"
(Ty.int 32) "s2_value_pos" [...]` is the destination register, and enumerating
calls by the first quoted string instead reports those blocks under a register
name.  Measured that way the body has **25** call-containing blocks: `entry` (11
calls, `s2_init` among them), `if.end` (3 `lifetime.end`), the four `unreachable`
arms, and the 19 class F rows — so the table's 19 is right and an earlier
enumeration of "22 blocks, 16 F rows" undercounted F by three, all of them
`lifetime.end`-only blocks near the body's end (`cleanup474.i`, `s2_walk.exit`,
`if.then`).  Of the 19, **13 write only inside the present frame** (the three
`s2_value_pos` callers, the eight `lifetime`-only blocks, `if.then25.i` and
`if.then425.i`'s `od_scalar_value`, whose three-footprint union is the log's
cursor word, the event stream and the refusal record) and **6 need the frame
widening** — `if.then109.i`, `if.else334.i` and `if.then447.i` through
`s2_after_value`'s `%root_done.i`, `z_arena_reserve.exit` through
`s2_string_body`'s `%xj.i`/`%outn.i`, `if.then19.i` through `num_fast_el1`'s
`%d.i`/`%ei.i`, and `if.end256.i`'s own zero store to `%outn.i`.

The count that mattered was the number of classes, not of blocks.  A, B and B′ are
70 blocks between them and need no memory reasoning at all: none touches memory
and none rebinds a register the invariant carries, so each link is one
`lookupName_cons_ne` per carried register and nothing else.  Two more classes
close the same way once their own small gap is filled — H1's five `LeafBlock`s
need one `add` of a negative literal before the comparison, and H2's two are five
`getelementptr`s and three arithmetic instructions.  Class C's eighteen were the
same bargain at a larger scale: one address the invariant does not bind, one
clause it does not carry, and one lemma.

## What each class needs

**C, the refusal store (18) — proved.**  The shape is `%off1.i.iNN =
getelementptr inbounds i8, ptr %e, i64 8; store i64 <reg>, %off1.i.iNN; br label
%if.then` (fifteen) or `%cleanup474.i` (three).  `WalkInv` has four clauses for the
log's fields and none for the refusal record's, so the store has no `readBytes`
clause to preserve; `WalkLink.refusalStore` therefore takes `%e`'s binding and the
stored value's bound as hypotheses, exactly as class A takes the compared
register's, and the link it builds is `{ C with block := t, eoff := j, refusal :=
true }`.  `eoff_le` is the caller's `j ≤ G.n`; `owned` and `frame` survive by
`walkStaged_write` and `walkFrame_write_inside` at `eoff_inside`; and the six memory clauses survive
because the record is a region of its own — `e_z_sep` and `e_ev_sep` are the
staging's separation read at indices 13/14 and 4/14, and
`walkReadBytes_log_of_eoff_write` and `walkReadBytes_ev_of_eoff_write` turn them
into the six equalities.  Nothing in `WalkInv` was weakened, and nothing was
added: the clause the arm is missing is still missing, and it is now a hypothesis
on the eighteen instances rather than a wall.

**D, the other stores (11) — proved (`JsonStage2WalkStore`).**  Ten shapes, one
each: the hash word at `%z + 24` (`if.then.i.i`, `if.then.i.i50` — six
instructions of `xor`, `mul`, `add` over the mask constants, and the invariant has
no clause for that word); the event stream's byte and its length
(`out_reserve.exit.i.i`, `.i60` — two stores that move `evlen`, and so the carry's
`events`, `evlen_eq` and `evBytes` all three); the container-stack byte at
`%cst.i + idxprom` (`if.end150.i`, `if.end162.i`, `if.end195.i`); the cursor's `k`
field (`if.end207.i`, at `%k11.i`, which is `WalkPtrs`' own address); the arena
cursor (`if.else285.i`, at `%alen`); and the state stack at `cst + sp - 1`
(`if.then330.i`).  None is a class — ten addresses with ten clause preservations
behind them — so the module proves one transfer per shape (a container-stack byte,
the hash word, the event stream's tag-and-length pair, the cursor's `k`, the arena
cursor) and one instance per block.  The addresses the invariant does not bind are
the caller's, as class C takes `%e`'s, and the two cursor moves are the carry's:
`events`/`evlen` for the event stream, `alen`/`spans` for the arena, the latter
with `pending` cleared (the merge that reserves the next record re-establishes
it).

**E, the `phi` run (15) — proved.**
The run reads `s.pre`, which the invariant does not constrain beyond the block it
is at (`denoteCode_phiRun` is the mechanism).  The four `land.rhs*` blocks are the
important ones: each selects the scan's counter and then loads the document byte at
it, so each is where a scan's `%NN` — class A's compared register — is produced, and
each is on the path between a scan header and the comparison that ends the scan.
`if.end372.i`, `while.end.i`, `while.end78.i`, `if.end245.i` and `if.end290.i` are
merges whose incoming values are the previous arm's registers, so their links are
one `PhiSelects` per incoming edge.  `cond.end.i96` is the string scan's entry and
`if.end48.i` the literal comparison's; their links are `JsonStage2WalkEntry`'s,
together with the landing facts that `land.rhs.i.preheader`'s and `if.end67.i`'s
links take as arguments.  The rest of the class is `JsonStage2WalkPhi`: the four
landing blocks are one lemma's instances (`WalkLink.scanLanding`), the pure merges
are `pureCore`/`pureJumpCore` over their `PhiSelects` runs, `for.body.i.i` builds
its `for.inc.i.i` guard from the disjunctive landing fact, and the three store
blocks are hand-rebuilt — `if.end372.i` at the token's end slot (no clause names
 and `if.then57.i`/`while.end78.i` with class C's
`eoff`/`refusal` carry update.  `if.end290.i`'s first `phi` takes `%32` — the
arena reserve's decoded length, loaded from `%outn.i` — as the caller's fact; its
*production* is `s2_string_body`'s write (`s2StringBody_outn_le`), the F datum the
merge's edge reads.

**F, the calls (19; nine proved).**  Every call has to resolve through
`stage2Calls`, and what it leaves is a `CallOutcome`: the
`lifetime.start`/`lifetime.end` markers (twelve and twenty-one of them,
`JsonStage2IR`'s guards) and the two `memset`s are resolved there and leave memory
alone, `@llvm.trap` is the reserve's refusal arm, and `s2_init`, `s2_value_pos`,
`s2_after_value`, `s2_string_body`, `num_fast_el1` and `od_scalar_value` are the
`sub` parameter.  So each of these links is a contract question — the callee's post
at the caller's staging — and `JsonStage2WalkCall` is where the walk's selection is
fixed (`stage2Calls stage2SubCalls`, the selection the six proved contracts are
stated at) and where the step is: `walkDenoteCode_call`/`walkDenoteCode_callVoid`
are the `denoteCode` steps of a call at an arbitrary argument list, and
`walkArgs_*` are the six helpers' argument lists read off the pinned body.

Nine of the nineteen are closed there.  Four are marker blocks
(`cleanup339.critedge.i`, `if.end67.critedge.i`, `if.end473.i`, `cleanup474.i`):
`walkDenoteCode_lifetimeEnd` is the marker's step — the state it was handed — so
each link is a pure run.  Four call a helper through the contract:
`if.then.i` and `if.then219.i` call `s2_value_pos`, whose footprint is empty and
whose memory is the caller's, so their links are `WalkLink.pureCore` at the two
returns; `if.else334.i` and `if.then447.i` call `s2_after_value`, whose model writes
one of two places (`stage2AfterValue_form`), and `walkAfterValue_facts` is the
frame, presence, log and trace at that write.  The depth-zero arm's root slot
(`%root_done.i`, the second `alloca` at `G.next0 + 8`) misses the log and the
stream, and that is now *structural* rather than a hypothesis beside the two
links: `WalkStage.sevenEnd` is the adapter's watermark at the seven appended
objects — every one of them ends at or below the call's cursor, which is the same
clause `Γ_stage2.pre` states for its thirteen — and `WalkStage.rootSlot_log` and
`WalkStage.rootSlot_ev` read it (`%d.i`'s and the stream's entries come from
`WalkGeom.watermark`).  The fact lives in the run's staging record because the
adapter's `stage2StagedPre` does not carry the call's `next`, which is the run's.

`if.end256.i` is the ninth, and it is the arena's reservation itself: the token's
extent, the marker, the zero store at `%outn.i`, the two log words and the check.
Its run is where class F's step vocabulary gains a literal store
(`walkDenoteCode_store64_imm` — the tree's store steps all take a register) and
where the two log words are read out of the invariant's `log_alen`/`log_acap`
rather than from a caller's fact.  The branch is stated at the bit the run
computed, so it composes with the trap verdict (`walkArenaReserve_clear`, which is
now a theorem of the invariant) instead of assuming it.

What remains is ten.  `if.then109.i` (`s2_after_value`), `cond.end349.i` (a
marker and two token stores), `if.then413.i` (`s2_value_pos` after a token store),
`if.then19.i`/`if.then25.i` (`num_fast_el1` and the refusal store that follows it)
need `WalkLink.callQuiet`, whose four memory facts (`JsonStage2WalkCall`'s transfer)
the caller supplies at the callee's footprint; three move a cursor the carry names —
`z_arena_reserve.exit` (the decoded body's prefix in the arena, which the frame's
arena extent at `C.alen` does not yet cover), `if.then328.i` (a thirteen-byte event
record, so the carry's trace advances) and `if.then425.i` (`od_scalar_value`'s
appended record, whose model the contract's post does not unfold) — so their links
are the carry's; and two finalise the caller's slots (`s2_walk.exit`, `if.then`),
whose stores go to `%ndst`, `%nev` and `%err`, three of the ABI's objects the
frame's list does not include.

**G, `load` and compare (14; all proved).**  Each reads a word the invariant does not
bind.  `if.end.i.i` and `if.end.i.i55` read `%len` and `%cap` — which `log_len` and
`log_cap` *do* bind, so these two are the closest of the fourteen; the rest read a
container-stack byte at `idxprom` or `sp - 1`, the document byte at `%cond350.i`
(`land.lhs.true357.i`), `%root_done.i`'s alloca (`if.end490.i`), or the document
byte at `%idxprom.i` (`if.end.i97`).  Each instance is `JsonStage2WalkPure`'s: the
block's run written out as a `denoteCode` equality and handed to its edge's
transfer — `pureCore` for a bit the block computes, `pureCoreCarried` for
`if.end74.i`'s carried bit, `pureJumpCore` for the four jump shapes — with the
`getelementptr` at a computed index its own step (`denoteCode_gep8_ofNat`).
The four rows that read a container-stack byte through `sp - 1`
(`if.end179.i`, `land.lhs.true.i`, `if.end133.i`, `if.end59.i`) failed the
kernel's type-checker when their runs were written at the block's literal
instruction list with the outgoing environment duplicated in the hypothesis
types: a deep-recursion error, not a depth limit (`maxRecDepth 50000` does not
help), while the statement alone and each proof term's parts type-check.
Stating the run at the block's *variables* and supplying each block by `rfl` —
`WalkLink.addImmBr`'s device — closes the two five-instruction rows
(`WalkLink.if_end179_i`, `WalkLink.land_lhs_true_i`); the other two are closed by
naming the seven- and eight-cell environment **once** as a parameter
(`env' : Env` with an equation `env' = walkPairEnv …`/`walkSelectEnv …`) so the
statement never contains it twice: `WalkLink.if_end133_i` and
`WalkLink.if_end59_i`.  The measurement that forced that shape: with the
environment written into the two `WalkLocal` hypotheses, the pair's declaration
alone reached 7.8 GB resident under a 6 GB cap (the marker's 1.7 GB).

**H1's five `LeafBlock`s — proved.**  `%.off = add i8 %NN, -9; %SwitchLeafNN =
icmp ule i8 %.off, 1`.  Two instructions and no memory: `walkDenoteCode_add_imm_w`
at a negative constant, then class A's terminator.  The compared byte is the
loaded document byte, which is the same caller-supplied fact class A takes; what
stopped them was that `WalkLink.icmpBr`'s `hinstrs` is a singleton, and
`WalkLink.addImmBr` (`JsonStage2WalkRest`) is the pair's own class lemma.  The five
links are `WalkLink.LeafBlock33`, `…43`, `…64`, `…85` and `…96`.

**H2.**  `while.body.i.lr.ph` binds five `getelementptr`s — `%c.i + 32`,
`%z + 24`, `%t352.i + 20`, `+ 8`, `+ 16` — of which only the first is in
`WalkPtrs`, so its link needs four more fixed addresses (and `%t352.i` itself is
not a `WalkPtrs` register).  `if.then281.i` is `add i32 %7, 1`, a `zext`, and an
`or` with the top bit set; it needs `%7`'s value, which is `if.then328.i`'s
`%conv286.i.sink`, and it carries `inner` untouched.

**The six that are not links.**  `entry` is the initialisation and its obligation
is `WalkSeedState`, already stated.  `if.end` returns: `walkIfEnd_step`
(`JsonStage2WalkCall`) is its step at either arm's `phi` value, and
`WalkChain.finalisation` composes a chain to `s2_walk.exit` with the exit's jump
(`walkExitBlock_denote`) and that return into a completion, without demanding a
`WalkLink` of either — the exit's stores are the record's, outside the walk's
frame by design.  `if.then`'s refusal copy still owes its three instructions; its
live-range prefix is `walkExitBlock_denote` at the same nine.  The four
`unreachable` blocks are `@llvm.trap` arms: a link
cannot enter one without concluding the run does not complete — `walkTrap_noStep`
(`JsonStage2WalkCall`) is that fact, since `stage2Calls` answers `none` at the trap
— so their obligation is the guard before them — `if.end.i.i`'s and
`if.end.i.i55`'s event reserve, `if.end256.i`'s arena reserve, `if.end290.i`'s
thirteen-byte reserve — never failing.

Three of the four guards are excluded by the invariant plus the loop head's own
guard (`C.k < G.nep`, the strictness `whileBody_step` already takes): the event
cursor is `nev0 + sum(events)`, at most `nev0 + 13·k ≤ nev0 + 13·nep ≤ evcap`, and
`k ≤ nep - 1 ≤ n - 1` leaves twelve bytes of slack at the widest record, so the
`len + 1 > cap` and `len + 13 > cap` tests are clear; `walkEventReserve_clear`
(`JsonStage2WalkRest`) is that arithmetic, stated at the invariant.  The **arena
trap** (`if.end.i83`) is excluded by `walkArenaReserve_clear`
(`JsonStage2WalkCall`), and the exclusion is now a theorem *of the invariant*: the
record in flight is a triple `(p, off, len)`, `pending_at` fixes its offset at the
cursor, `pending_cursor` bounds the cursor by the staging's offset plus `p`, and
`pending_len` places `p + len` inside the document.  The three are the whole of
the check's premises — `alen + len + 64 ≤ dstcap` follows from them and
`G.arenaRoom` — so no hypothesis sits beside the invariant.  The test is
`alen + (entry[k+1] - entry[k] - 1) + 64 > dstcap`, and `len` is exactly that
extent.  What remains is not the clause but its **production**: no link sets
`pending` to `some` yet — the merge at `cleanup478.i` is where the next entry's
position and extent are read from the entry stream — so the three clauses are
vacuously true today and the exclusion is a stated consequence rather than one a
traversal consumes.  That production is the record's assembly (the D/F work).  The class of the finding is in `JsonStage2WalkRest`'s
header, with the arithmetic.

## The remainder, named

The census's rows outside classes A, B, B′, `entry`, `if.end` and the four traps:
16 blocks still without a link, and 149 already closed.  `class` is the census's;
`what a link needs` is the block's own instance of the class's obstruction, naming
the register or address that is missing, and for a closed row the link that closed
it.

| # | block | class | what a link needs |
|---:|---|---|---|
| 1 | `entry` | seed | the initialisation, 58 instructions |
| 2 | `while.body.i.lr.ph` | H2 | five `gep`s — proved (`WalkLink.while_body_i_lr_ph`) |
| 17 | `if.then.i` | F | calls `@s2_value_pos` — proved (`WalkLink.if_then_i`) |
| 22 | `if.then.i.i` | D | the hash word at `%z + 24` — proved (`WalkLink.if_then_i_i`) |
| 23 | `if.end.i.i` | G | the two log words — proved (`WalkLink.if_end_i_i`) |
| 24 | `if.end.i.i.i` | trap | `@llvm.trap`, `unreachable` |
| 25 | `out_reserve.exit.i.i` | D | the tag byte and the cursor — proved (`WalkLink.out_reserve_exit_i_i`) |
| 28 | `if.end59.i` | G | the type stack's byte — proved (`WalkLink.if_end59_i`) |
| 30 | `if.end74.i` | G | the state stack's byte, carried bit — proved (`WalkLink.if_end74_i`) |
| 37 | `if.then109.i` | F | calls `@s2_after_value`; its `phi` run is the remaining need |
| 38 | `if.then.i.i50` | D | the hash word at `%z + 24` — proved (`WalkLink.if_then_i_i50`) |
| 39 | `if.end.i.i55` | G | the two log words — proved (`WalkLink.if_end_i_i55`) |
| 40 | `if.end.i.i.i64` | trap | `@llvm.trap`, `unreachable` |
| 41 | `out_reserve.exit.i.i60` | D | the tag byte and the cursor — proved (`WalkLink.out_reserve_exit_i_i60`) |
| 44 | `if.end133.i` | G | both stacks' bytes at `sp - 1` — proved (`WalkLink.if_end133_i`) |
| 47 | `if.end150.i` | D | the state stack's byte — proved (`WalkLink.if_end150_i`) |
| 50 | `if.end162.i` | D | the state stack's byte — proved (`WalkLink.if_end162_i`) |
| 53 | `if.end179.i` | G | the type stack's byte — proved (`WalkLink.if_end179_i`) |
| 54 | `lor.lhs.false.i` | G | the state stack's byte — proved (`WalkLink.lor_lhs_false_i`) |
| 56 | `if.end195.i` | D | the state stack's byte — proved (`WalkLink.if_end195_i`) |
| 59 | `if.end207.i` | D | the cursor record's `k` — proved (`WalkLink.if_end207_i`) |
| 61 | `if.then219.i` | F | calls `@s2_value_pos` — proved (`WalkLink.if_then219_i`) |
| 62 | `land.lhs.true.i` | G | the type stack's byte — proved (`WalkLink.land_lhs_true_i`) |
| 63 | `if.then231.i` | G | the state stack's masked byte — proved (`WalkLink.if_then231_i`) |
| 64 | `if.end245.i` | E | the `phi` run `%key.1.i` and the callee's return — proved (`WalkLink.if_end245_i`) |
| 66 | `if.end256.i` | F | the arena check — proved (`WalkLink.if_end256_i`) |
| 67 | `if.end.i83` | trap | `@llvm.trap`, `unreachable` |
| 68 | `z_arena_reserve.exit` | F | calls `@s2_string_body` |
| 71 | `if.then281.i` | H2 | `add`/`zext`/`or` — proved (`WalkLink.if_then281_i`) |
| 72 | `if.else285.i` | D | the arena cursor and the span — proved (`WalkLink.if_else285_i`) |
| 73 | `if.end290.i` | E | the two `phi`s and the thirteen-byte reserve — proved (`WalkLink.if_end290_i`); `%32` is `s2_string_body`'s write, the F datum the edge reads |
| 74 | `if.end.i86` | trap | `@llvm.trap`, `unreachable` |
| 75 | `if.then328.i` | F | calls `@llvm.lifetime.end.p0` |
| 76 | `if.then330.i` | D | the state stack's byte — proved (`WalkLink.if_then330_i`) |
| 77 | `if.else334.i` | F | calls `@s2_after_value` — proved (`WalkLink.if_else334_i`) |
| 78 | `cleanup339.critedge.i` | F | calls `@llvm.lifetime.end.p0` — proved (`WalkLink.cleanup339_critedge_i`) |
| 80 | `cond.true345.i` | G | the stream's next lane — proved (`WalkLink.cond_true345_i`) |
| 81 | `cond.end349.i` | F | calls `@llvm.lifetime.start.p0` |
| 82 | `land.lhs.true357.i` | G | the document byte at the bound — proved (`WalkLink.land_lhs_true357_i`) |
| 87 | `LeafBlock33` | H1 | `add` + `icmp` latch — proved (`WalkLink.LeafBlock33`) |
| 89 | `land.rhs.i` | E | the counter `phi` and the document byte — proved (`WalkLink.land_rhs_i`) |
| 94 | `LeafBlock43` | H1 | `add` + `icmp` latch — proved (`WalkLink.LeafBlock43`) |
| 96 | `if.end372.i` | E | the end `phi` and the token's end slot — proved (`WalkLink.if_end372_i`) |
| 106 | `if.then413.i` | F | calls `@s2_value_pos` |
| 108 | `if.then425.i` | F | calls `@od_scalar_value` |
| 110 | `cond.true.i106` | G | the stream's bound lane — proved (`WalkLink.cond_true_i106`) |
| 111 | `cond.end.i96` | E | the bound `phi` and the entry test — proved (`WalkLink.cond_end_i96`) |
| 112 | `land.rhs.i103` | E | the counter `phi` and the document byte — proved (`WalkLink.land_rhs_i103`) |
| 117 | `LeafBlock64` | H1 | `add` + `icmp` latch — proved (`WalkLink.LeafBlock64`) |
| 119 | `while.end.i` | E | the landing `phi` and the exit test — proved (`WalkLink.while_end_i`) |
| 120 | `if.end.i97` | G | the byte after the scan — proved (`WalkLink.if_end_i97`) |
| 121 | `if.then19.i` | F | calls `@llvm.lifetime.start.p0`, `@num_fast_el1` |
| 122 | `if.then25.i` | F | calls `@llvm.lifetime.end.p0` |
| 132 | `if.end48.i` | E | the two `phi`s, `min`, and the entry test — proved (`WalkLink.if_end48_i`) |
| 133 | `for.body.i.i` | E | the `phi` run and the `for.inc.i.i` guard — proved (`WalkLink.for_body_i_i`) |
| 136 | `if.then57.i` | E | the `phi`, the `add`, and the refusal store — proved (`WalkLink.if_then57_i`) |
| 137 | `if.end67.critedge.i` | F | calls `@llvm.lifetime.end.p0` — proved (`WalkLink.if_end67_critedge_i`) |
| 139 | `land.rhs71.i` | E | the counter `phi` and the document byte — proved (`WalkLink.land_rhs71_i`) |
| 144 | `LeafBlock85` | H1 | `add` + `icmp` latch — proved (`WalkLink.LeafBlock85`) |
| 146 | `while.end78.i` | E | the landing `phi` and the refusal store — proved (`WalkLink.while_end78_i`) |
| 147 | `if.then447.i` | F | calls `@s2_after_value` — proved (`WalkLink.if_then447_i`) |
| 148 | `land.rhs457.i` | E | the counter `phi` and the document byte — proved (`WalkLink.land_rhs457_i`) |
| 153 | `LeafBlock96` | H1 | `add` + `icmp` latch — proved (`WalkLink.LeafBlock96`) |
| 156 | `if.end473.i` | F | calls `@llvm.lifetime.end.p0` — proved (`WalkLink.if_end473_i`) |
| 157 | `cleanup474.i` | F | calls `@llvm.lifetime.end.p0` — proved (`WalkLink.cleanup474_i`) |
| 158 | `cleanup478.i` | E | the depth and index `phi`s — proved (`WalkLink.cleanup478_i`) |
| 161 | `if.end490.i` | G | the `%root_done.i` slot — proved (`WalkLink.if_end490_i`) |
| 163 | `s2_walk.exit` | F | the terminal step — proved (`walkExitBlock_denote`, `WalkChain.finalisation`) |
| 164 | `if.then` | F | the refusal copy: three instructions after its live-range prefix (`walkExitBlock_denote` at the same nine) |
| 165 | `if.end` | ret | the return — proved as the terminal step (`walkIfEnd_step`, `WalkChain.finalisation`) |

## Whether the chain closes

It does not, and this slice does not claim it.  `Stage2WalkCompletes` is not
inhabited, and the exact missing conjunct is *that* proposition — the completion
half of `Stage2WalkObligation` at `stage2Budget` (`stage2WalkObligation_iff_completion`
is the equivalence, so nothing else is wanted).  Read as a proof obligation it is
four pieces, in order:

1. **sixteen links** — the ten class F blocks the table names plus `entry`,
   `if.end`, and the four `unreachable` arms (whose verdicts are proved:
   `walkTrap_noStep`, `walkEventReserve_clear`, `walkArenaReserve_clear`), so the
   traversal has no gap;
2. **the seed** — `WalkSeedState` at `entry`'s handoff, which is the
   initialisation's own obligation: `walkSeed_invariant` turns it into the
   invariant at the loop head, and what `entry`'s 58 instructions must show is
   that state (the two `phi` values, the six pointer bindings, the log's four
   fields and the staging's presence);
3. **the return** — *stated and composed*: `walkIfEnd_step` is `if.end`'s step at
   either arm's `phi` value, `walkExitBlock_denote` is the exit's jump, and
   `WalkChain.finalisation` turns a chain to `s2_walk.exit` plus those two steps
   into the completion.  What remains of the return is `if.then`'s refusal copy
   (the three instructions after the live-range prefix); the returning arm
   (`s2_walk.exit`) needs nothing further; and
4. **the count** — `WalkChain.steps` composed over the assembled chain to give a
   step count at or below `stage2Budget`, which is the one place the 22-and-six
   readings of *The budget, counted* are spent.

Two of the sixteen cannot be links under the record's post as it stands, and the
reason is the same in both cases: the walk's frame is a *prefix* of the record's
(`walkFrame_reportFrame_coverage` maps `(dst, alen)` into `(dst, alen + 64)`, and
`err_not_in_walkFrame` places the refusal slot *outside* it), so widening the
walk's frame widens the record's.  `z_arena_reserve.exit` writes the decoded body
at `G.dst + C.alen` before `if.else285.i` advances the cursor two blocks later, so
the write is inside neither the source nor the target carry's arena entry; the
staged window `(G.dst, ndst0 + n + 64)` covers it, and that window is not inside
`(dst, alen + 64)`.  `s2_walk.exit` and `if.then` store to `%ndst`, `%nev` and
`%err`, which the report's post proves *itself* from `err_not_in_walkFrame` and
the wrapper's `frameSlots` — a walk frame that covered the three would make
`errAccept` unprovable.  Both are decisions about `stage2Boundary`, for the record
that owns it; inside this module the honest statement is the obstruction.  The
`if.then425.i` third is closed at the contract: `s2ScalarValuePost` now carries a
second conjunct naming the record an emitting arm appended (`s2ScalarValueAppend`
at an `EventRecord`), so the carry's trace can advance from the call's own post.
What that link still needs is the log's buffer-pointer word at `%z` (the
invariant binds the four fields from `%z + 8` on, not `%z`'s first field) and the
carry advance itself, which is the same composition `if.then328.i` owes.

`JsonStage2WalkRest` supplies H1's five `LeafBlock` links (its class lemma reads the
`add`'s literal at the instruction's own width) and `if.then281.i`, and states the
three transfers the rest of the pure classes share: `WalkLink.pureCore` (a run that
binds no carried register and whose edge is a carried or computed bit),
`WalkLink.pureJumpCore` and `WalkLink.pureCoreCarried`.  What remains absent, with
the reason in each row, is ten of the nineteen call blocks
(`JsonStage2WalkCall` closes the other nine); classes D, E and G are
`JsonStage2WalkStore`, `JsonStage2WalkPhi` and `JsonStage2WalkPure`, the last with
four of its fourteen rows obstructed by a kernel recursion.

The scan entries are links, and the measure is what made them.  `for.body.i.i` is
reached from `if.end48.i` as well as from `for.inc.i.i`, and its landing fact is the
disjunction `ScanLanded ∨ (the phi's zero)` (`WalkLocal` and the four `land.rhs*`
landing facts are disjunctive for the same reason — their preheaders are second
predecessors).  The entry disjunct reads `C.inner`, so an entry edge that *reset* it
to the new scan's remaining work would raise the measure whenever a later scan has
more work than the earlier one left.  The measure's inner component is therefore the
iteration's **shared budget** (`walkInnerCap G = 4 * n + 5`, `JsonStage2WalkEntry`),
an entry edge leaves it where it is and shows only that the budget covers the scan
it enters, and the refill at the loop head is paid for by the outer factor.  Under
that measure `if.end48.i` and `cond.end.i96`, and the two landed links whose landing
fact was an argument (`land.rhs.i.preheader`, `if.end67.i`), are links; the escape
scan's entry (`if.then447.i`) is a call block and stays F's.  The landing blocks'
own `phi` runs and the rest of E's merges are `JsonStage2WalkPhi`'s, and what is
left below is the calls' contract gap.

The arena guard's remaining need and F's gap are the same kind of statement.  Each
of the nineteen call blocks needs its callee's `CallOutcome` at the caller's
staging; `stage2Calls` resolves the lifetime markers and `@llvm.trap` and leaves
`s2_init`, `s2_value_pos`, `s2_after_value`, `s2_string_body`, `num_fast_el1` and
`od_scalar_value` to the `sub` parameter, so a call block's link is a contract
question.  The blocks that read a returned word (`if.end256.i` reads
`%call272.i`'s successors, `if.then328.i` reads `%outn.i`) need the callee's frame
as well as its post, and `z_arena_reserve.exit` needs the arena's reservation to
be the cursor's — the same datum `pending_cursor` reads.  No link in this module is
proved against a `CallOutcome` that the `sub` parameter's contract does not state,
which is why F is reported as a contract gap rather than closed here.

The step count is likewise not established, but the two numbers it is compared
against now are.  `WalkChain.steps` reads a chain as a run, and a chain with 16 of
its links missing has no step count to compare against `stage2Budget`.  What the
budget's arithmetic needs is one link per block the dispatch traverses, and *The
budget, counted* below takes that path off the pinned AST: the dispatch's longest
path is 22 blocks against `stage2EntryAllowance` 32, and the widest scan step is
six blocks against `stage2ByteAllowance` 8.  What is still open is the chain's own
count — whether a 165-block dispatch spends exactly those allowances over a
completed traversal — which is the completed chain's answer and not the census's.-/

/-- **A comparison**, at a state rather than at a builder and at arbitrary operands:
the step `denoteCode_icmp_eq_imm_w` is its `eq`-with-literal case, and the
dispatch's binary search uses `slt`, `ult`, `ule` and `eq` over both registers and
literals indifferently. -/
theorem walkDenoteCode_icmp {calls : Calls} (env : Env) (s : State) (d : String)
    (w : Nat) (p : IPred) {oa ob : Operand} {x y : BitVec w}
    (ha : evalOperand (stateAt env s) oa = some (.int w x))
    (hb : evalOperand (stateAt env s) ob = some (.int w y)) (is : List Instr) :
    denoteCode calls (.icmp d p w oa ob :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp p x y)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (by
    rw [LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_icmp (s := stateAt env s) ha hb])]
  simp only [stateAt, State.bind]

/-- **A `condbr` on a one-bit register** takes the edge its bit names.  `execTerm`
answers `ub` on a bit that is neither zero nor one, and a `BitVec 1` has no third
value, so the edge is total. -/
theorem walkExecTerm_condbr {s : State} {d tl fl : String} {bit : BitVec 1}
    (hd : lookupName s.env d = some (.int 1 bit)) :
    execTerm s (Term.condbr (.reg d) tl fl) =
      .jump { s with pc := (if bit = 1 then tl else fl), pre := some s.pc } := by
  simp only [execTerm, evalOperand, hd]
  rcases bitVec1_eq_zero_or_one bit with h | h
  · rw [h]; simp
  · rw [h]; simp

/-- **Class A: one comparison and a branch.**  The block reads two operands at one
width, binds the one-bit result and branches on it.  Nothing else in the
environment moves, so the six pointer registers, the entry index and the depth
register survive a `lookupName_cons_ne` each, the memory is untouched, and the
measure does not move because the block advances neither the entry index nor the
inner work.

The operands are the caller's: `%8` is the document byte `while.body.i` loaded,
`%sp.i.0248` is the depth the invariant carries, and `%35`, `%ee.0.i238` and their
siblings are a scan's counters.  What the block *does* with the answer is the edge
it takes, which is why the target block is the bit's own value.

The block-local clause is taken at the two edges rather than at the test, because
the test is a `BitVec` comparison the lemma cannot decide: a caller with a literal
target discharges each by `simp [WalkLocal]`. -/
theorem WalkLink.icmpBr {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    {B : Block} (hfind : stage2Body.findBlock C.block = some B)
    {d tl fl : String} {p : IPred} {w : Nat} {oa ob : Operand} {x y : BitVec w}
    (hinstrs : B.instrs = [Instr.icmp d p w oa ob])
    (hterm : B.term = Term.condbr (.reg d) tl fl)
    (ha : evalOperand s oa = some (.int w x)) (hb : evalOperand s ob = some (.int w y))
    (hk : d ≠ "%k.0.i249") (hsp : d ≠ "%sp.i.0248")
    (h3 : d ≠ "%3") (h5 : d ≠ "%5") (hkk : d ≠ "%k11.i")
    (hc : d ≠ "%ctype.i") (hs : d ≠ "%cst.i") (hh : d ≠ "%hash1.i.i")
    (hl : WalkLocal { C with block := tl }
      { stateAt ((d, .int 1 (evalICmp p x y)) :: s.env) s with pc := tl, pre := some s.pc })
    (hf : WalkLocal { C with block := fl }
      { stateAt ((d, .int 1 (evalICmp p x y)) :: s.env) s with
        pc := fl, pre := some s.pc }) :
    ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp p x y = 1 then tl else fl) } s' := by
  have hpc : s.pc = C.block := hInv.pc_eq
  have hden : denoteCode calls B.instrs s =
      some (stateAt ((d, .int 1 (evalICmp p x y)) :: s.env) s) := by
    rw [hinstrs, ← stateAt_self s]
    exact walkDenoteCode_icmp (calls := calls) s.env s d w p ha hb []
  let s' : State :=
    { stateAt ((d, .int 1 (evalICmp p x y)) :: s.env) s with pc := (if evalICmp p x y = 1 then tl else fl), pre := some s.pc }
  have hstep : LeanLLVM.step calls stage2Body s = Ctrl.jump s' := by
    simp only [LeanLLVM.step, hpc, hfind, hden, hterm]
    exact walkExecTerm_condbr (d := d) (tl := tl) (fl := fl)
      (bit := evalICmp p x y) (by simp only [stateAt, lookupName_cons_self])
  refine ⟨s', ⟨hInv, hstep, ?_, ?_⟩⟩
  · refine
      { pc_eq := rfl
        blockIndex := ?_
        k_le := hInv.k_le
        events_le := hInv.events_le
        evlen_eq := hInv.evlen_eq
        evBytes := ?_
        alen_le_sum := hInv.alen_le_sum
        alen_ge := hInv.alen_ge
        spans_order := hInv.spans_order
        spans_inside := hInv.spans_inside
        pending_at := hInv.pending_at
        pending_cursor := hInv.pending_cursor
        pending_len := hInv.pending_len
        eoff_le := hInv.eoff_le
        inner_cap := hInv.inner_cap
        depth_cap := hInv.depth_cap
        depth_reg := ?_
        ptrs := ?_
        log_hash := hInv.log_hash
        log_len := hInv.log_len
        log_cap := hInv.log_cap
        log_alen := hInv.log_alen
        log_acap := hInv.log_acap
        owned := hInv.owned
        frame := hInv.frame
        blockLocal := ?_ }
    · dsimp only [s', stateAt]
      rw [lookupName_cons_ne _ _ hk]
      exact hInv.blockIndex
    · dsimp only [s', stateAt]
      exact hInv.evBytes
    · dsimp only [s', stateAt]
      rw [lookupName_cons_ne _ _ hsp]
      exact hInv.depth_reg
    · dsimp only [s', stateAt]
      exact hInv.ptrs.bind h3 h5 hkk hc hs hh
    · dsimp only [s']
      by_cases ht : evalICmp p x y = 1
      · rw [ite_eq_left ht]; exact hl
      · rw [ite_eq_right ht]; exact hf
  · rfl

/-! ### Class C: the refusal store

Eighteen blocks of the dispatch write the refusal record's offset and leave for
the refusal's exit: `%off1.i.iNN = getelementptr inbounds i8, ptr %e, i64 8;
store i64 <reg>, %off1.i.iNN; br label %if.then` — fifteen of them to `if.then`
and three to `cleanup474.i`.  The stored register is the block's own: thirteen
store `%idxprom.i`, four store `%4`, and one stores `%q.0.i246`.

What the invariant gives is everything except the offset's own bound.  The store's
address is fixed by the staging (`C.stage.e + 8`), so the only register fact the
block needs is `%e`'s binding — which `WalkPtrs` does not carry, exactly as it does
not carry `%8`.  The values stored are entry positions and the document's length,
so `eoff_le` follows from the caller's `≤ G.n`; nothing in `WalkInv` produces it,
which is the clause the refusal arm is missing. -/

/-- The refusal record's `%e + 8` field is inside its staged extent. -/
theorem eoff_inside {c ctype cst tok s z e k : Nat} (hk : k < 8) :
    inRegions (stage2StagedWrites c ctype cst tok s z e) (e + 8 + k) :=
  ⟨(e, stage2ErrorExtent), by simp [stage2StagedWrites], by omega,
    by simp [stage2ErrorExtent]; omega⟩

/-- The refusal record and the log are separate regions of the staging. -/
theorem e_z_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (_h : WalkInv G C s) :
    C.stage.e + stage2ErrorExtent ≤ C.stage.z ∨
      C.stage.z + stage2LogExtent ≤ C.stage.e := by
  have hpair : (stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e).Pairwise
      (fun r q => r.1 + r.2 ≤ q.1 ∨ q.1 + q.2 ≤ r.1) := by
    have hsep := C.stage.separate
    unfold DisjointRegions at hsep
    rw [stage2StagedRegions] at hsep
    exact (List.pairwise_append.mp hsep).1
  have hlen : (stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e).length = 15 := by
    simp [stage2WalkRegions, stage2Regions, stage2StagedWrites]
  have h' := List.pairwise_iff_getElem.mp hpair 13 14 (by omega) (by omega) (by omega)
  simpa [stage2WalkRegions, stage2Regions, stage2StagedWrites] using h'.symm

/-- The refusal record and the event stream are separate regions of the
staging. -/
theorem e_ev_sep {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (_h : WalkInv G C s) :
    C.stage.e + stage2ErrorExtent ≤ G.ev ∨ G.ev + G.evcap ≤ C.stage.e := by
  have hpair : (stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e).Pairwise
      (fun r q => r.1 + r.2 ≤ q.1 ∨ q.1 + q.2 ≤ r.1) := by
    have hsep := C.stage.separate
    unfold DisjointRegions at hsep
    rw [stage2StagedRegions] at hsep
    exact (List.pairwise_append.mp hsep).1
  have hlen : (stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0 G.ev
      G.evcap G.ndst G.nev G.err C.stage.c C.stage.ctype C.stage.cst C.stage.tok
      C.stage.s C.stage.z C.stage.e).length = 15 := by
    simp [stage2WalkRegions, stage2Regions, stage2StagedWrites]
  have h' := List.pairwise_iff_getElem.mp hpair 4 14 (by omega) (by omega) (by omega)
  simpa [stage2WalkRegions, stage2Regions, stage2StagedWrites] using h'.symm

/-- **A write to the refusal's offset leaves the log alone.**  Every log field is
an `off` and a width inside the log's extent, and the record is a separate region,
so the eight bytes at `%e + 8` miss it. -/
theorem walkReadBytes_log_of_eoff_write {m : Mem} {e z off j N : Nat}
    (hez : e + stage2ErrorExtent ≤ z ∨ z + stage2LogExtent ≤ e)
    (hoff : off + N ≤ stage2LogExtent) :
    readBytes (writeBytes m (e + 8) (wordBytes 8 j)) (z + off) N = readBytes m (z + off) N := by
  refine walkReadBytes_writeBytes_outside (start := e + 8) (addr := z + off) (n := N) ?_
  have hw : (wordBytes 8 j).length = 8 := by simp [wordBytes, natToBytes_length]
  rcases hez with hez | hez
  · refine Or.inr ?_
    have h1 := hez
    simp only [stage2ErrorExtent] at h1
    rw [hw]; omega
  · refine Or.inl ?_
    have h1 := hez
    simp only [stage2LogExtent] at h1
    omega

/-- **A write to the refusal's offset leaves the event stream alone.** -/
theorem walkReadBytes_ev_of_eoff_write {m : Mem} {e ev evcap nev0 j N : Nat}
    (hev : e + stage2ErrorExtent ≤ ev ∨ ev + evcap ≤ e) (hN : nev0 + N ≤ evcap) :
    readBytes (writeBytes m (e + 8) (wordBytes 8 j)) (ev + nev0) N =
      readBytes m (ev + nev0) N := by
  refine walkReadBytes_writeBytes_outside (start := e + 8) (addr := ev + nev0) (n := N) ?_
  have hw : (wordBytes 8 j).length = 8 := by simp [wordBytes, natToBytes_length]
  rcases hev with hev | hev
  · refine Or.inr ?_
    have h1 := hev
    simp only [stage2ErrorExtent] at h1
    rw [hw]; omega
  · refine Or.inl ?_
    omega

/-- An `i8` `getelementptr` at a literal offset. -/
theorem walkEvalInstr_gep8_imm (calls : Calls) (s : State) (d base : String)
    (a c : Nat) (hb : lookupName s.env base = some (.ptr a)) (hc : c < 2 ^ 63) :
    evalInstr calls s (.gep d (.int 8) (.reg base) (.imm (.int 64 (BitVec.ofNat 64 c)))) =
      some (s.bind d (.ptr (a + c))) := by
  have hs := sExt_ofNat64 hc
  have hpos : (BitVec.ofNat 64 c).toNat < 2 ^ 63 := by
    rw [walkToNat_ofNat64 (by omega)]; exact hc
  have hmod : c % 2 ^ 64 = c := Nat.mod_eq_of_lt (by omega)
  simp only [evalInstr, evalOperand, Const.toValue, hb, hs,
    show (8 + 7) / 8 = 1 from rfl, Ty.sizeBytes]
  rw [ite_eq_left hc]
  simp

/-- A `getelementptr i8` at a literal offset, in the chain's shape. -/
theorem walkDenoteCode_gep8_imm {calls : Calls} (s : State) (d base : String)
    {a c : Nat} (hb : lookupName s.env base = some (.ptr a)) (hc : c < 2 ^ 63)
    (is : List Instr) :
    denoteCode calls
        (.gep d (.int 8) (.reg base) (.imm (.int 64 (BitVec.ofNat 64 c))) :: is) s =
      denoteCode calls is (s.bind d (.ptr (a + c))) :=
  denoteCode_cons_of _ _ _ _ _ (walkEvalInstr_gep8_imm calls s d base a c hb hc)

/-- **Class C: the refusal store.**  One `getelementptr` at `%e + 8`, one
eight-byte store, and the edge to the refusal's exit.  The memory clauses that
survive are the ones whose addresses lie outside those eight bytes; `e_z_sep` and
`e_ev_sep` are what say so, and `frame` survives by `eoff_inside`. -/
theorem WalkLink.refusalStore {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    {B : Block} (hfind : stage2Body.findBlock C.block = some B)
    {d v t : String} {j : Nat}
    (hinstrs : B.instrs =
      [Instr.gep d (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
       Instr.store (.int 64) (.reg v) (.reg d)])
    (hterm : B.term = Term.br t)
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hv : lookupName s.env v = some (.int 64 (BitVec.ofNat 64 j)))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    (hvd : d ≠ v)
    (hd : d ≠ "%k.0.i249") (hds : d ≠ "%sp.i.0248")
    (h3 : d ≠ "%3") (h5 : d ≠ "%5") (hkk : d ≠ "%k11.i")
    (hc : d ≠ "%ctype.i") (hs : d ≠ "%cst.i") (hh : d ≠ "%hash1.i.i")
    (hloc : WalkLocal { C with block := t, eoff := j, refusal := true }
      { stateAt ((d, .ptr (C.stage.e + 8)) :: s.env)
          { s with mem := writeBytes s.mem (C.stage.e + 8) (wordBytes 8 j) } with
        pc := t, pre := some s.pc }) :
    ∃ s', WalkLink calls G C s { C with block := t, eoff := j, refusal := true } s' := by
  have hpc : s.pc = C.block := hInv.pc_eq
  let m' : Mem := writeBytes s.mem (C.stage.e + 8) (wordBytes 8 j)
  let s' : State :=
    { stateAt ((d, .ptr (C.stage.e + 8)) :: s.env) { s with mem := m' } with pc := t, pre := some s.pc }
  have hden : denoteCode calls B.instrs s =
      some (stateAt ((d, .ptr (C.stage.e + 8)) :: s.env) { s with mem := m' }) := by
    rw [hinstrs,
      walkDenoteCode_gep8_imm (calls := calls) s d "%e" he (by decide)
        [Instr.store (.int 64) (.reg v) (.reg d)]]
    exact denoteCode_store64_ofNat (calls := calls)
      (env := (d, .ptr (C.stage.e + 8)) :: s.env) s v d
      (by rw [lookupName_cons_ne _ _ hvd]; exact hv) hj64
      (lookupName_cons_self d (.ptr (C.stage.e + 8)) s.env) []
  have hfind' : stage2Body.findBlock s.pc = some B := by rw [hpc]; exact hfind
  have hstep : LeanLLVM.step calls stage2Body s = Ctrl.jump s' := by
    simp only [LeanLLVM.step, hfind', hden, hterm, execTerm]
    dsimp only [s', m', stateAt]
  refine ⟨s', ⟨hInv, hstep, ?_, ?_⟩⟩
  · refine
      { pc_eq := rfl
        blockIndex := ?_
        k_le := hInv.k_le
        events_le := hInv.events_le
        evlen_eq := hInv.evlen_eq
        evBytes := ?_
        alen_le_sum := hInv.alen_le_sum
        alen_ge := hInv.alen_ge
        spans_order := hInv.spans_order
        spans_inside := hInv.spans_inside
        pending_at := hInv.pending_at
        pending_cursor := hInv.pending_cursor
        pending_len := hInv.pending_len
        eoff_le := hj
        inner_cap := hInv.inner_cap
        depth_cap := hInv.depth_cap
        depth_reg := ?_
        ptrs := ?_
        log_hash := ?_
        log_len := ?_
        log_cap := ?_
        log_alen := ?_
        log_acap := ?_
        owned := by dsimp only [s', stateAt, m']; exact walkStaged_write rfl hInv.owned
        frame := ?_
        blockLocal := hloc }
    · dsimp only [s', stateAt, m']
      rw [lookupName_cons_ne _ _ hd]
      exact hInv.blockIndex
    · have hlen : (C.events.map EventRecord.encodedBytes).flatten.length =
          (C.events.map EventRecord.encodedSize).sum := by
        simp only [List.length_flatten, List.map_map]; rfl
      have hsum := EventRecord.sum_encodedSize_le C.events
      simp only [stage2RecordBytes] at hsum
      have hroom := G.evRoom
      simp only [stage2RecordBytes] at hroom
      have hN : G.nev0 + (C.events.map EventRecord.encodedBytes).flatten.length ≤ G.evcap := by
        have h1 := hInv.events_le
        have h2 := hInv.k_le
        have h3 := G.nep_le
        rw [hlen]; omega
      dsimp only [s', stateAt, m']
      rw [walkReadBytes_ev_of_eoff_write (e := C.stage.e) (ev := G.ev) (evcap := G.evcap)
        (nev0 := G.nev0) (j := j) (N := _) (e_ev_sep hInv) hN]
      exact hInv.evBytes
    · dsimp only [s', stateAt, m']
      rw [lookupName_cons_ne _ _ hds]
      exact hInv.depth_reg
    · dsimp only [s', stateAt, m']
      exact hInv.ptrs.bind h3 h5 hkk hc hs hh
    · dsimp only [s', stateAt, m']
      rw [walkReadBytes_log_of_eoff_write (e := C.stage.e) (z := C.stage.z) (off := 32)
        (j := j) (N := 4) (e_z_sep hInv) (by decide)]
      exact hInv.log_hash
    · dsimp only [s', stateAt, m']
      rw [walkReadBytes_log_of_eoff_write (e := C.stage.e) (z := C.stage.z) (off := 8)
        (j := j) (N := 8) (e_z_sep hInv) (by decide)]
      exact hInv.log_len
    · dsimp only [s', stateAt, m']
      rw [walkReadBytes_log_of_eoff_write (e := C.stage.e) (z := C.stage.z) (off := 16)
        (j := j) (N := 8) (e_z_sep hInv) (by decide)]
      exact hInv.log_cap
    · dsimp only [s', stateAt, m']
      rw [walkReadBytes_log_of_eoff_write (e := C.stage.e) (z := C.stage.z) (off := 48)
        (j := j) (N := 8) (e_z_sep hInv) (by decide)]
      exact hInv.log_alen
    · dsimp only [s', stateAt, m']
      rw [walkReadBytes_log_of_eoff_write (e := C.stage.e) (z := C.stage.z) (off := 56)
        (j := j) (N := 8) (e_z_sep hInv) (by decide)]
      exact hInv.log_acap
    · dsimp only [s', stateAt, m']
      refine walkFrame_write_inside hInv.frame ?_
      intro k hk
      have hw : (wordBytes 8 j).length = 8 := by simp [wordBytes, natToBytes_length]
      exact walkWide_of_seven
        (eoff_inside (c := C.stage.c) (ctype := C.stage.ctype) (cst := C.stage.cst)
          (tok := C.stage.tok) (s := C.stage.s) (z := C.stage.z) (e := C.stage.e)
          (k := k) (by omega))
  · rfl

/-! ### Class C's eighteen instances

Each is the body's own text, transcribed, with its `findBlock` proof beside it.
The instance differs from the last only in the stored register, the `gep`'s name
and the exit block — fifteen exit to `if.then` and three to `cleanup474.i` — and
the proof is one `WalkLink.refusalStore` application in each. -/

/-- `if.then16.i`: the refusal's offset store, of `%idxprom.i`. -/
def walkIf_then16_i : Block :=
  { name := "if.then16.i",
    instrs := [Instr.gep "%off1.i.i" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%idxprom.i") (.reg "%off1.i.i")],
    term := Term.br "if.then" }

theorem walkIf_then16_i_find : stage2Body.findBlock "if.then16.i" = some walkIf_then16_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then16_i]

theorem WalkLink.if_then16_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then16.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "if.then", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then16_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by simp [WalkLocal])

/-- `if.then21.i`: the refusal's offset store, of `%idxprom.i`. -/
def walkIf_then21_i : Block :=
  { name := "if.then21.i",
    instrs := [Instr.gep "%off1.i.i38" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%idxprom.i") (.reg "%off1.i.i38")],
    term := Term.br "if.then" }

theorem walkIf_then21_i_find : stage2Body.findBlock "if.then21.i" = some walkIf_then21_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then21_i]

theorem WalkLink.if_then21_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then21.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "if.then", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then21_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by simp [WalkLocal])

/-- `if.then56.i`: the refusal's offset store, of `%idxprom.i`. -/
def walkIf_then56_i : Block :=
  { name := "if.then56.i",
    instrs := [Instr.gep "%off1.i.i41" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%idxprom.i") (.reg "%off1.i.i41")],
    term := Term.br "if.then" }

theorem walkIf_then56_i_find : stage2Body.findBlock "if.then56.i" = some walkIf_then56_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then56_i]

theorem WalkLink.if_then56_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then56.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "if.then", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then56_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by simp [WalkLocal])

/-- `if.then71.i`: the refusal's offset store, of `%idxprom.i`. -/
def walkIf_then71_i : Block :=
  { name := "if.then71.i",
    instrs := [Instr.gep "%off1.i.i43" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%idxprom.i") (.reg "%off1.i.i43")],
    term := Term.br "if.then" }

theorem walkIf_then71_i_find : stage2Body.findBlock "if.then71.i" = some walkIf_then71_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then71_i]

theorem WalkLink.if_then71_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then71.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "if.then", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then71_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by simp [WalkLocal])

/-- `cleanup104.i`: the refusal's offset store, of `%idxprom.i`. -/
def walkCleanup104_i : Block :=
  { name := "cleanup104.i",
    instrs := [Instr.gep "%off1.i.i45" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%idxprom.i") (.reg "%off1.i.i45")],
    term := Term.br "if.then" }

theorem walkCleanup104_i_find : stage2Body.findBlock "cleanup104.i" = some walkCleanup104_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkCleanup104_i]

theorem WalkLink.cleanup104_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "cleanup104.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "if.then", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkCleanup104_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by simp [WalkLocal])

/-- `if.then130.i`: the refusal's offset store, of `%idxprom.i`. -/
def walkIf_then130_i : Block :=
  { name := "if.then130.i",
    instrs := [Instr.gep "%off1.i.i66" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%idxprom.i") (.reg "%off1.i.i66")],
    term := Term.br "if.then" }

theorem walkIf_then130_i_find : stage2Body.findBlock "if.then130.i" = some walkIf_then130_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then130_i]

theorem WalkLink.if_then130_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then130.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "if.then", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then130_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by simp [WalkLocal])

/-- `if.then147.i`: the refusal's offset store, of `%idxprom.i`. -/
def walkIf_then147_i : Block :=
  { name := "if.then147.i",
    instrs := [Instr.gep "%off1.i.i68" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%idxprom.i") (.reg "%off1.i.i68")],
    term := Term.br "if.then" }

theorem walkIf_then147_i_find : stage2Body.findBlock "if.then147.i" = some walkIf_then147_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then147_i]

theorem WalkLink.if_then147_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then147.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "if.then", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then147_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by simp [WalkLocal])

/-- `if.then159.i`: the refusal's offset store, of `%idxprom.i`. -/
def walkIf_then159_i : Block :=
  { name := "if.then159.i",
    instrs := [Instr.gep "%off1.i.i70" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%idxprom.i") (.reg "%off1.i.i70")],
    term := Term.br "if.then" }

theorem walkIf_then159_i_find : stage2Body.findBlock "if.then159.i" = some walkIf_then159_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then159_i]

theorem WalkLink.if_then159_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then159.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "if.then", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then159_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by simp [WalkLocal])

/-- `if.then176.i`: the refusal's offset store, of `%idxprom.i`. -/
def walkIf_then176_i : Block :=
  { name := "if.then176.i",
    instrs := [Instr.gep "%off1.i.i72" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%idxprom.i") (.reg "%off1.i.i72")],
    term := Term.br "if.then" }

theorem walkIf_then176_i_find : stage2Body.findBlock "if.then176.i" = some walkIf_then176_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then176_i]

theorem WalkLink.if_then176_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then176.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "if.then", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then176_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by simp [WalkLocal])

/-- `if.then192.i`: the refusal's offset store, of `%idxprom.i`. -/
def walkIf_then192_i : Block :=
  { name := "if.then192.i",
    instrs := [Instr.gep "%off1.i.i74" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%idxprom.i") (.reg "%off1.i.i74")],
    term := Term.br "if.then" }

theorem walkIf_then192_i_find : stage2Body.findBlock "if.then192.i" = some walkIf_then192_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then192_i]

theorem WalkLink.if_then192_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then192.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "if.then", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then192_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by simp [WalkLocal])

/-- `if.then205.i`: the refusal's offset store, of `%4`. -/
def walkIf_then205_i : Block :=
  { name := "if.then205.i",
    instrs := [Instr.gep "%off1.i.i76" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%4") (.reg "%off1.i.i76")],
    term := Term.br "if.then" }

theorem walkIf_then205_i_find : stage2Body.findBlock "if.then205.i" = some walkIf_then205_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then205_i]

theorem WalkLink.if_then205_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then205.i")
    {j : Nat} (hv : evalOperand s (.reg "%4") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "if.then", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then205_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by simp [WalkLocal])

/-- `if.then214.i`: the refusal's offset store, of `%4`. -/
def walkIf_then214_i : Block :=
  { name := "if.then214.i",
    instrs := [Instr.gep "%off1.i.i78" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%4") (.reg "%off1.i.i78")],
    term := Term.br "if.then" }

theorem walkIf_then214_i_find : stage2Body.findBlock "if.then214.i" = some walkIf_then214_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then214_i]

theorem WalkLink.if_then214_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then214.i")
    {j : Nat} (hv : evalOperand s (.reg "%4") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "if.then", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then214_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by simp [WalkLocal])

/-- `if.then249.i`: the refusal's offset store, of `%idxprom.i`. -/
def walkIf_then249_i : Block :=
  { name := "if.then249.i",
    instrs := [Instr.gep "%off1.i.i80" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%idxprom.i") (.reg "%off1.i.i80")],
    term := Term.br "if.then" }

theorem walkIf_then249_i_find : stage2Body.findBlock "if.then249.i" = some walkIf_then249_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then249_i]

theorem WalkLink.if_then249_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then249.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "if.then", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then249_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by simp [WalkLocal])

/-- `if.then418.i`: the refusal's offset store, of `%idxprom.i`. -/
def walkIf_then418_i : Block :=
  { name := "if.then418.i",
    instrs := [Instr.gep "%off1.i.i91" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%idxprom.i") (.reg "%off1.i.i91")],
    term := Term.br "cleanup474.i" }

theorem walkIf_then418_i_find : stage2Body.findBlock "if.then418.i" = some walkIf_then418_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then418_i]

theorem WalkLink.if_then418_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then418.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "cleanup474.i", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then418_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by simp [WalkLocal])

/-- `if.else43.i`: the refusal's offset store, of `%idxprom.i`. -/
def walkIf_else43_i : Block :=
  { name := "if.else43.i",
    instrs := [Instr.gep "%off1.i129.i" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%idxprom.i") (.reg "%off1.i129.i")],
    term := Term.br "cleanup474.i" }

theorem walkIf_else43_i_find : stage2Body.findBlock "if.else43.i" = some walkIf_else43_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_else43_i]

theorem WalkLink.if_else43_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.else43.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "cleanup474.i", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_else43_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by simp [WalkLocal])

/-- `if.then467.i`: the refusal's offset store, of `%q.0.i246`. -/
def walkIf_then467_i : Block :=
  { name := "if.then467.i",
    instrs := [Instr.gep "%off1.i.i113" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%q.0.i246") (.reg "%off1.i.i113")],
    term := Term.br "cleanup474.i" }

theorem walkIf_then467_i_find : stage2Body.findBlock "if.then467.i" = some walkIf_then467_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then467_i]

theorem WalkLink.if_then467_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then467.i")
    {j : Nat} (hv : evalOperand s (.reg "%q.0.i246") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "cleanup474.i", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then467_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by simp [WalkLocal])

/-- `if.then488.i`: the refusal's offset store, of `%4`. -/
def walkIf_then488_i : Block :=
  { name := "if.then488.i",
    instrs := [Instr.gep "%off1.i.i115" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%4") (.reg "%off1.i.i115")],
    term := Term.br "if.then" }

theorem walkIf_then488_i_find : stage2Body.findBlock "if.then488.i" = some walkIf_then488_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then488_i]

theorem WalkLink.if_then488_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then488.i")
    {j : Nat} (hv : evalOperand s (.reg "%4") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "if.then", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then488_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by simp [WalkLocal])

/-- `if.then492.i`: the refusal's offset store, of `%4`. -/
def walkIf_then492_i : Block :=
  { name := "if.then492.i",
    instrs := [Instr.gep "%off1.i.i117" (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
               Instr.store (.int 64) (.reg "%4") (.reg "%off1.i.i117")],
    term := Term.br "if.then" }

theorem walkIf_then492_i_find : stage2Body.findBlock "if.then492.i" = some walkIf_then492_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then492_i]

theorem WalkLink.if_then492_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then492.i")
    {j : Nat} (hv : evalOperand s (.reg "%4") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ s', WalkLink calls G C s
      { C with block := "if.then", eoff := j, refusal := true } s' := by
  exact WalkLink.refusalStore (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then492_i_find) rfl rfl he hv hj hj64 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by simp [WalkLocal])

/-- **Class B′: no instructions and a branch on a carried bit.**  The block binds
nothing; the bit is one the previous block's comparison left behind, and the edge
it names is the edge taken.  Every clause of the invariant is the one it had. -/
theorem WalkLink.condBr {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    {B : Block} (hfind : stage2Body.findBlock C.block = some B)
    (hinstrs : B.instrs = []) {d tl fl : String} {bit : BitVec 1}
    (hterm : B.term = Term.condbr (.reg d) tl fl)
    (hd : lookupName s.env d = some (.int 1 bit))
    (hl : WalkLocal { C with block := tl } { s with pc := tl, pre := some s.pc })
    (hf : WalkLocal { C with block := fl } { s with pc := fl, pre := some s.pc }) :
    ∃ s', WalkLink calls G C s
      { C with block := (if bit = 1 then tl else fl) } s' := by
  have hpc : s.pc = C.block := hInv.pc_eq
  let s' : State := { s with pc := (if bit = 1 then tl else fl), pre := some s.pc }
  have hden : denoteCode calls B.instrs s = some s := by rw [hinstrs]; rfl
  have hstep : LeanLLVM.step calls stage2Body s = Ctrl.jump s' := by
    simp only [LeanLLVM.step, hpc, hfind, hden, hterm]
    exact walkExecTerm_condbr (bit := bit) hd
  refine ⟨s', ⟨hInv, hstep, ?_, ?_⟩⟩
  · refine
      { pc_eq := rfl
        blockIndex := hInv.blockIndex
        k_le := hInv.k_le
        events_le := hInv.events_le
        evlen_eq := hInv.evlen_eq
        evBytes := hInv.evBytes
        alen_le_sum := hInv.alen_le_sum
        alen_ge := hInv.alen_ge
        spans_order := hInv.spans_order
        spans_inside := hInv.spans_inside
        pending_at := hInv.pending_at
        pending_cursor := hInv.pending_cursor
        pending_len := hInv.pending_len
        eoff_le := hInv.eoff_le
        inner_cap := hInv.inner_cap
        depth_cap := hInv.depth_cap
        depth_reg := hInv.depth_reg
        ptrs := hInv.ptrs
        log_hash := hInv.log_hash
        log_len := hInv.log_len
        log_cap := hInv.log_cap
        log_alen := hInv.log_alen
        log_acap := hInv.log_acap
        owned := hInv.owned
        frame := hInv.frame
        blockLocal := ?_ }
    · dsimp only [s']
      by_cases ht : bit = 1
      · rw [ite_eq_left ht]; exact hl
      · rw [ite_eq_right ht]; exact hf
  · rfl

/-- `if.then432.i`: the block `if.then425.i`'s clear test enters, and its branch is
`%cmp343.i`'s answer — the same bit `if.end133.i` computed. -/
def walkIf_then432_i : Block :=
  { name := "if.then432.i", instrs := [],
    term := Term.condbr (.reg "%cmp343.i") "cond.true.i106" "cond.end.i96" }

theorem walkIf_then432_i_find :
    stage2Body.findBlock "if.then432.i" = some walkIf_then432_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then432_i]

theorem WalkLink.if_then432_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then432.i")
    {x : BitVec 1} (h1 : evalOperand s (.reg "%cmp343.i") = some (.int 1 x))
    : ∃ s', WalkLink calls G C s
      { C with block := (if x = 1 then "cond.true.i106" else "cond.end.i96") } s' := by
  exact WalkLink.condBr (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then432_i_find) rfl rfl h1
    (by simp [WalkLocal]) (by simp [WalkLocal])

/-- **Class B: no instructions and a jump.**  The block binds nothing, so every
clause of the invariant is the one it had and the only change is the block the run
is at. -/
theorem WalkLink.br {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    {B : Block} (hfind : stage2Body.findBlock C.block = some B)
    (hinstrs : B.instrs = []) {t : String} (hterm : B.term = Term.br t)
    (hloc : WalkLocal { C with block := t } { s with pc := t, pre := some s.pc }) :
    ∃ s', WalkLink calls G C s { C with block := t } s' := by
  have hpc : s.pc = C.block := hInv.pc_eq
  let s' : State := { s with pc := t, pre := some s.pc }
  have hden : denoteCode calls B.instrs s = some s := by rw [hinstrs]; rfl
  have hstep : LeanLLVM.step calls stage2Body s = Ctrl.jump s' := by
    simp only [LeanLLVM.step, hpc, hfind, hden, hterm, execTerm, s']
  refine ⟨s', ⟨hInv, hstep, ?_, ?_⟩⟩
  · refine
      { pc_eq := rfl
        blockIndex := hInv.blockIndex
        k_le := hInv.k_le
        events_le := hInv.events_le
        evlen_eq := hInv.evlen_eq
        evBytes := hInv.evBytes
        alen_le_sum := hInv.alen_le_sum
        alen_ge := hInv.alen_ge
        spans_order := hInv.spans_order
        spans_inside := hInv.spans_inside
        pending_at := hInv.pending_at
        pending_cursor := hInv.pending_cursor
        pending_len := hInv.pending_len
        eoff_le := hInv.eoff_le
        inner_cap := hInv.inner_cap
        depth_cap := hInv.depth_cap
        depth_reg := hInv.depth_reg
        ptrs := hInv.ptrs
        log_hash := hInv.log_hash
        log_len := hInv.log_len
        log_cap := hInv.log_cap
        log_alen := hInv.log_alen
        log_acap := hInv.log_acap
        owned := hInv.owned
        frame := hInv.frame
        blockLocal := hloc }
  · rfl


/-! ### The four scan headers, as links

The four scans are the inner measure's engine: each of their headers increments
its counter and takes the back edge while the counter is short of the bound, so
`scan_step` gives the step, the invariant and a strictly smaller measure.  These
four wrappers are that arm as a link, for the trace to use: the strictness is
dropped to `WalkLink`'s non-increase, and the landing carry the arm builds is
existential there (`scan_step`'s own shape), so the target block is named beside
it.

The target's `inner` is `c - (i + 1)`, which is the arm's own reading of the
scan's two registers; the caller reaches it through the `ScanLanded` fact the
landing block's `WalkLocal` carries, not by naming it here. -/

/-- **The literal comparison's latch as a link.**  `for.inc.i.i` is `forInc_step`
without the strictness: the measure falls by one, so it does not rise. -/
theorem WalkLink.forInc {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "for.inc.i.i") (hguard : ForIncGuard C s) :
    ∃ s' C', WalkLink calls G C s C' s' ∧ C'.block = "for.body.i.i" := by
  obtain ⟨i, c, hinner, hlt, hcw, hi, hc⟩ := hguard
  obtain ⟨e, C', hstep, hinv, hland, hmeas, -⟩ :=
    forInc_step G C s i c hInv hblock hi hc hinner hlt hcw
  exact ⟨e, C', ⟨hInv, hstep, hinv, le_of_lt hmeas⟩, hland⟩

theorem WalkLink.whileBody370 {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "while.body370.i")
    (hguard : ScanGuard s "%ee.0.i238" "%cond350.i" C.inner) :
    ∃ s' C', WalkLink calls G C s C' s' ∧ C'.block = "land.rhs.i" := by
  obtain ⟨e, C', hstep, hinv, hland, hmeas, -⟩ :=
    whitespace_scan (calls := calls) G C s hInv hblock hguard
  exact ⟨e, C', ⟨hInv, hstep, hinv, le_of_lt hmeas⟩, hland⟩

theorem WalkLink.whileBodyI104 {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "while.body.i104")
    (hguard : ScanGuard s "%ee.011.i" "%cond.i" C.inner) :
    ∃ s' C', WalkLink calls G C s C' s' ∧ C'.block = "land.rhs.i103" := by
  obtain ⟨e, C', hstep, hinv, hland, hmeas, -⟩ :=
    string_scan (calls := calls) G C s hInv hblock hguard
  exact ⟨e, C', ⟨hInv, hstep, hinv, le_of_lt hmeas⟩, hland⟩

theorem WalkLink.whileBody76 {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "while.body76.i")
    (hguard : ScanGuard s "%s2.020.i" "%cond.i" C.inner) :
    ∃ s' C', WalkLink calls G C s C' s' ∧ C'.block = "land.rhs71.i" := by
  obtain ⟨e, C', hstep, hinv, hland, hmeas, -⟩ :=
    escape_scan (calls := calls) G C s hInv hblock hguard
  exact ⟨e, C', ⟨hInv, hstep, hinv, le_of_lt hmeas⟩, hland⟩

theorem WalkLink.whileBody462 {calls : Calls} {m0 : Mem} (G : WalkGeom m0)
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "while.body462.i")
    (hguard : ScanGuard s "%q.0.i246" "%cond350.i" C.inner) :
    ∃ s' C', WalkLink calls G C s C' s' ∧ C'.block = "land.rhs457.i" := by
  obtain ⟨e, C', hstep, hinv, hland, hmeas, -⟩ :=
    extraToken_scan (calls := calls) G C s hInv hblock hguard
  exact ⟨e, C', ⟨hInv, hstep, hinv, le_of_lt hmeas⟩, hland⟩

/-! ### Class A's sixty instances

Each is the pinned body's own text, transcribed, with the `findBlock` proof beside
it: `#guard decide (firstFunction stage2Src = some stage2Body)` in
`JsonStage2IR` is what makes the transcription the body's block rather than a
paraphrase of the fixture.  The instances differ only in the comparison, its
width, and the two edges — the proof is one `WalkLink.icmpBr` application in each.

Eight of them branch into one of the ten scan blocks, where `WalkLocal` is not
`True`; those eight carry the block-local clause at that edge as a hypothesis,
because the reset that establishes it is the edge's own work and not this
block's. -/

/-- `NodeBlock21`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock21 : Block :=
  { name := "NodeBlock21",
    instrs := [Instr.icmp "%Pivot22" IPred.slt 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 91)))],
    term := Term.condbr (.reg "%Pivot22") "NodeBlock5" "NodeBlock19" }

theorem walkNodeBlock21_find : stage2Body.findBlock "NodeBlock21" = some walkNodeBlock21 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock21]

theorem WalkLink.NodeBlock21 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock21")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 91) = 1 then "NodeBlock5" else "NodeBlock19") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock21_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock19`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock19 : Block :=
  { name := "NodeBlock19",
    instrs := [Instr.icmp "%Pivot20" IPred.slt 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 123)))],
    term := Term.condbr (.reg "%Pivot20") "NodeBlock11" "NodeBlock17" }

theorem walkNodeBlock19_find : stage2Body.findBlock "NodeBlock19" = some walkNodeBlock19 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock19]

theorem WalkLink.NodeBlock19 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock19")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 123) = 1 then "NodeBlock11" else "NodeBlock17") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock19_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock17`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock17 : Block :=
  { name := "NodeBlock17",
    instrs := [Instr.icmp "%Pivot18" IPred.slt 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 125)))],
    term := Term.condbr (.reg "%Pivot18") "LeafBlock13" "LeafBlock15" }

theorem walkNodeBlock17_find : stage2Body.findBlock "NodeBlock17" = some walkNodeBlock17 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock17]

theorem WalkLink.NodeBlock17 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock17")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 125) = 1 then "LeafBlock13" else "LeafBlock15") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock17_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock15`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock15 : Block :=
  { name := "LeafBlock15",
    instrs := [Instr.icmp "%SwitchLeaf16" IPred.eq 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 125)))],
    term := Term.condbr (.reg "%SwitchLeaf16") "if.then53.i" "sw.default.i" }

theorem walkLeafBlock15_find : stage2Body.findBlock "LeafBlock15" = some walkLeafBlock15 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock15]

theorem WalkLink.LeafBlock15 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock15")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 125) = 1 then "if.then53.i" else "sw.default.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock15_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock13`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock13 : Block :=
  { name := "LeafBlock13",
    instrs := [Instr.icmp "%SwitchLeaf14" IPred.eq 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 123)))],
    term := Term.condbr (.reg "%SwitchLeaf14") "if.then.i" "sw.default.i" }

theorem walkLeafBlock13_find : stage2Body.findBlock "LeafBlock13" = some walkLeafBlock13 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock13]

theorem WalkLink.LeafBlock13 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock13")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 123) = 1 then "if.then.i" else "sw.default.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock13_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock11`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock11 : Block :=
  { name := "NodeBlock11",
    instrs := [Instr.icmp "%Pivot12" IPred.slt 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 93)))],
    term := Term.condbr (.reg "%Pivot12") "LeafBlock7" "LeafBlock9" }

theorem walkNodeBlock11_find : stage2Body.findBlock "NodeBlock11" = some walkNodeBlock11 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock11]

theorem WalkLink.NodeBlock11 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock11")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 93) = 1 then "LeafBlock7" else "LeafBlock9") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock11_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock9`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock9 : Block :=
  { name := "LeafBlock9",
    instrs := [Instr.icmp "%SwitchLeaf10" IPred.eq 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 93)))],
    term := Term.condbr (.reg "%SwitchLeaf10") "if.then53.i" "sw.default.i" }

theorem walkLeafBlock9_find : stage2Body.findBlock "LeafBlock9" = some walkLeafBlock9 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock9]

theorem WalkLink.LeafBlock9 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock9")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 93) = 1 then "if.then53.i" else "sw.default.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock9_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock7`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock7 : Block :=
  { name := "LeafBlock7",
    instrs := [Instr.icmp "%SwitchLeaf8" IPred.eq 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 91)))],
    term := Term.condbr (.reg "%SwitchLeaf8") "if.then.i" "sw.default.i" }

theorem walkLeafBlock7_find : stage2Body.findBlock "LeafBlock7" = some walkLeafBlock7 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock7]

theorem WalkLink.LeafBlock7 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock7")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 91) = 1 then "if.then.i" else "sw.default.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock7_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock5`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock5 : Block :=
  { name := "NodeBlock5",
    instrs := [Instr.icmp "%Pivot6" IPred.slt 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 44)))],
    term := Term.condbr (.reg "%Pivot6") "LeafBlock" "NodeBlock" }

theorem walkNodeBlock5_find : stage2Body.findBlock "NodeBlock5" = some walkNodeBlock5 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock5]

theorem WalkLink.NodeBlock5 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock5")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 44) = 1 then "LeafBlock" else "NodeBlock") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock5_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock : Block :=
  { name := "NodeBlock",
    instrs := [Instr.icmp "%Pivot" IPred.slt 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 58)))],
    term := Term.condbr (.reg "%Pivot") "LeafBlock1" "LeafBlock3" }

theorem walkNodeBlock_find : stage2Body.findBlock "NodeBlock" = some walkNodeBlock := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock]

theorem WalkLink.NodeBlock {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 58) = 1 then "LeafBlock1" else "LeafBlock3") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock3`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock3 : Block :=
  { name := "LeafBlock3",
    instrs := [Instr.icmp "%SwitchLeaf4" IPred.eq 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 58)))],
    term := Term.condbr (.reg "%SwitchLeaf4") "if.then173.i" "sw.default.i" }

theorem walkLeafBlock3_find : stage2Body.findBlock "LeafBlock3" = some walkLeafBlock3 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock3]

theorem WalkLink.LeafBlock3 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock3")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 58) = 1 then "if.then173.i" else "sw.default.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock3_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock1`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock1 : Block :=
  { name := "LeafBlock1",
    instrs := [Instr.icmp "%SwitchLeaf2" IPred.eq 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 44)))],
    term := Term.condbr (.reg "%SwitchLeaf2") "if.then127.i" "sw.default.i" }

theorem walkLeafBlock1_find : stage2Body.findBlock "LeafBlock1" = some walkLeafBlock1 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock1]

theorem WalkLink.LeafBlock1 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock1")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 44) = 1 then "if.then127.i" else "sw.default.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock1_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock : Block :=
  { name := "LeafBlock",
    instrs := [Instr.icmp "%SwitchLeaf" IPred.eq 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 34)))],
    term := Term.condbr (.reg "%SwitchLeaf") "sw.bb202.i" "sw.default.i" }

theorem walkLeafBlock_find : stage2Body.findBlock "LeafBlock" = some walkLeafBlock := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock]

theorem WalkLink.LeafBlock {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 34) = 1 then "sw.bb202.i" else "sw.default.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `if.end.i`: the dispatch's comparison `icmp .ugt i32` and the edge its bit names. -/
def walkIf_end_i : Block :=
  { name := "if.end.i",
    instrs := [Instr.icmp "%cmp19.i" IPred.ugt 32 (.reg "%sp.i.0248") (.imm (.int 32 (BitVec.ofNat 32 519)))],
    term := Term.condbr (.reg "%cmp19.i") "if.then21.i" "if.end24.i" }

theorem walkIf_end_i_find : stage2Body.findBlock "if.end.i" = some walkIf_end_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_end_i]

theorem WalkLink.if_end_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end.i")
    {x1 : BitVec 32} (h1 : evalOperand s (.reg "%sp.i.0248") = some (.int 32 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .ugt x1 (BitVec.ofNat 32 519) = 1 then "if.then21.i" else "if.end24.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkIf_end_i_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `if.then53.i`: the dispatch's comparison `icmp .eq i32` and the edge its bit names. -/
def walkIf_then53_i : Block :=
  { name := "if.then53.i",
    instrs := [Instr.icmp "%cmp54.i" IPred.eq 32 (.reg "%sp.i.0248") (.imm (.int 32 (BitVec.ofNat 32 0)))],
    term := Term.condbr (.reg "%cmp54.i") "if.then56.i" "if.end59.i" }

theorem walkIf_then53_i_find : stage2Body.findBlock "if.then53.i" = some walkIf_then53_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then53_i]

theorem WalkLink.if_then53_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then53.i")
    {x1 : BitVec 32} (h1 : evalOperand s (.reg "%sp.i.0248") = some (.int 32 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 32 0) = 1 then "if.then56.i" else "if.end59.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkIf_then53_i_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock27`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock27 : Block :=
  { name := "NodeBlock27",
    instrs := [Instr.icmp "%Pivot28" IPred.slt 8 (.reg "%15") (.imm (.int 8 (BitVec.ofNat 8 3)))],
    term := Term.condbr (.reg "%Pivot28") "LeafBlock23" "LeafBlock25" }

theorem walkNodeBlock27_find : stage2Body.findBlock "NodeBlock27" = some walkNodeBlock27 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock27]

theorem WalkLink.NodeBlock27 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock27")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%15") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 3) = 1 then "LeafBlock23" else "LeafBlock25") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock27_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock25`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock25 : Block :=
  { name := "LeafBlock25",
    instrs := [Instr.icmp "%SwitchLeaf26" IPred.eq 8 (.reg "%15") (.imm (.int 8 (BitVec.ofNat 8 3)))],
    term := Term.condbr (.reg "%SwitchLeaf26") "if.then109.i" "cleanup104.i" }

theorem walkLeafBlock25_find : stage2Body.findBlock "LeafBlock25" = some walkLeafBlock25 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock25]

theorem WalkLink.LeafBlock25 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock25")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%15") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 3) = 1 then "if.then109.i" else "cleanup104.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock25_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock23`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock23 : Block :=
  { name := "LeafBlock23",
    instrs := [Instr.icmp "%SwitchLeaf24" IPred.eq 8 (.reg "%15") (.imm (.int 8 (BitVec.ofNat 8 0)))],
    term := Term.condbr (.reg "%SwitchLeaf24") "if.then109.i" "cleanup104.i" }

theorem walkLeafBlock23_find : stage2Body.findBlock "LeafBlock23" = some walkLeafBlock23 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock23]

theorem WalkLink.LeafBlock23 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock23")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%15") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 0) = 1 then "if.then109.i" else "cleanup104.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock23_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `cond.end.i`: the dispatch's comparison `icmp .ult i8` and the edge its bit names. -/
def walkCond_end_i : Block :=
  { name := "cond.end.i",
    instrs := [Instr.icmp "%16" IPred.ult 8 (.reg "%15") (.imm (.int 8 (BitVec.ofNat 8 2)))],
    term := Term.condbr (.reg "%16") "if.then109.i" "cleanup104.i" }

theorem walkCond_end_i_find : stage2Body.findBlock "cond.end.i" = some walkCond_end_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkCond_end_i]

theorem WalkLink.cond_end_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "cond.end.i")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%15") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .ult x1 (BitVec.ofNat 8 2) = 1 then "if.then109.i" else "cleanup104.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkCond_end_i_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `if.then127.i`: the dispatch's comparison `icmp .eq i32` and the edge its bit names. -/
def walkIf_then127_i : Block :=
  { name := "if.then127.i",
    instrs := [Instr.icmp "%cmp128.i" IPred.eq 32 (.reg "%sp.i.0248") (.imm (.int 32 (BitVec.ofNat 32 0)))],
    term := Term.condbr (.reg "%cmp128.i") "if.then130.i" "if.end133.i" }

theorem walkIf_then127_i_find : stage2Body.findBlock "if.then127.i" = some walkIf_then127_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then127_i]

theorem WalkLink.if_then127_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then127.i")
    {x1 : BitVec 32} (h1 : evalOperand s (.reg "%sp.i.0248") = some (.int 32 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 32 0) = 1 then "if.then130.i" else "if.end133.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkIf_then127_i_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `if.then141.i`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkIf_then141_i : Block :=
  { name := "if.then141.i",
    instrs := [Instr.icmp "%cmp145.not.i" IPred.eq 8 (.reg "%22") (.imm (.int 8 (BitVec.ofNat 8 3)))],
    term := Term.condbr (.reg "%cmp145.not.i") "if.end150.i" "if.then147.i" }

theorem walkIf_then141_i_find : stage2Body.findBlock "if.then141.i" = some walkIf_then141_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then141_i]

theorem WalkLink.if_then141_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then141.i")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%22") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 3) = 1 then "if.end150.i" else "if.then147.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkIf_then141_i_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `if.else153.i`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkIf_else153_i : Block :=
  { name := "if.else153.i",
    instrs := [Instr.icmp "%cmp157.not.i" IPred.eq 8 (.reg "%22") (.imm (.int 8 (BitVec.ofNat 8 1)))],
    term := Term.condbr (.reg "%cmp157.not.i") "if.end162.i" "if.then159.i" }

theorem walkIf_else153_i_find : stage2Body.findBlock "if.else153.i" = some walkIf_else153_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_else153_i]

theorem WalkLink.if_else153_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.else153.i")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%22") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 1) = 1 then "if.end162.i" else "if.then159.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkIf_else153_i_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `if.then173.i`: the dispatch's comparison `icmp .eq i32` and the edge its bit names. -/
def walkIf_then173_i : Block :=
  { name := "if.then173.i",
    instrs := [Instr.icmp "%cmp174.i" IPred.eq 32 (.reg "%sp.i.0248") (.imm (.int 32 (BitVec.ofNat 32 0)))],
    term := Term.condbr (.reg "%cmp174.i") "if.then176.i" "if.end179.i" }

theorem walkIf_then173_i_find : stage2Body.findBlock "if.then173.i" = some walkIf_then173_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then173_i]

theorem WalkLink.if_then173_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then173.i")
    {x1 : BitVec 32} (h1 : evalOperand s (.reg "%sp.i.0248") = some (.int 32 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 32 0) = 1 then "if.then176.i" else "if.end179.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkIf_then173_i_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `sw.bb202.i`: the dispatch's comparison `icmp .ult i64` and the edge its bit names. -/
def walkSw_bb202_i : Block :=
  { name := "sw.bb202.i",
    instrs := [Instr.icmp "%cmp203.not.i" IPred.ult 64 (.reg "%inc.i") (.reg "%nep")],
    term := Term.condbr (.reg "%cmp203.not.i") "if.end207.i" "if.then205.i" }

theorem walkSw_bb202_i_find : stage2Body.findBlock "sw.bb202.i" = some walkSw_bb202_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkSw_bb202_i]

theorem WalkLink.sw_bb202_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "sw.bb202.i")
    {x1 : BitVec 64} (h1 : evalOperand s (.reg "%inc.i") = some (.int 64 x1))
    {x2 : BitVec 64} (h2 : evalOperand s (.reg "%nep") = some (.int 64 x2))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .ult x1 x2 = 1 then "if.end207.i" else "if.then205.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkSw_bb202_i_find) rfl rfl h1 h2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock31`: the dispatch's comparison `icmp .slt i32` and the edge its bit names. -/
def walkNodeBlock31 : Block :=
  { name := "NodeBlock31",
    instrs := [Instr.icmp "%Pivot32" IPred.slt 32 (.reg "%call272.i") (.imm (.int 32 (BitVec.ofNat 32 1)))],
    term := Term.condbr (.reg "%Pivot32") "cleanup339.critedge.i" "LeafBlock29" }

theorem walkNodeBlock31_find : stage2Body.findBlock "NodeBlock31" = some walkNodeBlock31 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock31]

theorem WalkLink.NodeBlock31 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock31")
    {x1 : BitVec 32} (h1 : evalOperand s (.reg "%call272.i") = some (.int 32 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 32 1) = 1 then "cleanup339.critedge.i" else "LeafBlock29") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock31_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock29`: the dispatch's comparison `icmp .eq i32` and the edge its bit names. -/
def walkLeafBlock29 : Block :=
  { name := "LeafBlock29",
    instrs := [Instr.icmp "%SwitchLeaf30" IPred.eq 32 (.reg "%call272.i") (.imm (.int 32 (BitVec.ofNat 32 1)))],
    term := Term.condbr (.reg "%SwitchLeaf30") "if.then281.i" "if.else285.i" }

theorem walkLeafBlock29_find : stage2Body.findBlock "LeafBlock29" = some walkLeafBlock29 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock29]

theorem WalkLink.LeafBlock29 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock29")
    {x1 : BitVec 32} (h1 : evalOperand s (.reg "%call272.i") = some (.int 32 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 32 1) = 1 then "if.then281.i" else "if.else285.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock29_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `sw.default.i`: the dispatch's comparison `icmp .ult i64` and the edge its bit names. -/
def walkSw_default_i : Block :=
  { name := "sw.default.i",
    instrs := [Instr.icmp "%cmp343.i" IPred.ult 64 (.reg "%inc.i") (.reg "%nep")],
    term := Term.condbr (.reg "%cmp343.i") "cond.true345.i" "cond.end349.i" }

theorem walkSw_default_i_find : stage2Body.findBlock "sw.default.i" = some walkSw_default_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkSw_default_i]

theorem WalkLink.sw_default_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "sw.default.i")
    {x1 : BitVec 64} (h1 : evalOperand s (.reg "%inc.i") = some (.int 64 x1))
    {x2 : BitVec 64} (h2 : evalOperand s (.reg "%nep") = some (.int 64 x2))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .ult x1 x2 = 1 then "cond.true345.i" else "cond.end349.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkSw_default_i_find) rfl rfl h1 h2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock41`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock41 : Block :=
  { name := "NodeBlock41",
    instrs := [Instr.icmp "%Pivot42" IPred.slt 8 (.reg "%35") (.imm (.int 8 (BitVec.ofNat 8 13)))],
    term := Term.condbr (.reg "%Pivot42") "LeafBlock33" "NodeBlock39" }

theorem walkNodeBlock41_find : stage2Body.findBlock "NodeBlock41" = some walkNodeBlock41 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock41]

theorem WalkLink.NodeBlock41 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock41")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%35") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 13) = 1 then "LeafBlock33" else "NodeBlock39") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock41_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock39`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock39 : Block :=
  { name := "NodeBlock39",
    instrs := [Instr.icmp "%Pivot40" IPred.slt 8 (.reg "%35") (.imm (.int 8 (BitVec.ofNat 8 32)))],
    term := Term.condbr (.reg "%Pivot40") "LeafBlock35" "LeafBlock37" }

theorem walkNodeBlock39_find : stage2Body.findBlock "NodeBlock39" = some walkNodeBlock39 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock39]

theorem WalkLink.NodeBlock39 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock39")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%35") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 32) = 1 then "LeafBlock35" else "LeafBlock37") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock39_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock37`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock37 : Block :=
  { name := "LeafBlock37",
    instrs := [Instr.icmp "%SwitchLeaf38" IPred.eq 8 (.reg "%35") (.imm (.int 8 (BitVec.ofNat 8 32)))],
    term := Term.condbr (.reg "%SwitchLeaf38") "land.rhs.i.preheader" "if.end372.i" }

theorem walkLeafBlock37_find : stage2Body.findBlock "LeafBlock37" = some walkLeafBlock37 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock37]

theorem WalkLink.LeafBlock37 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock37")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%35") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 32) = 1 then "land.rhs.i.preheader" else "if.end372.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock37_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock35`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock35 : Block :=
  { name := "LeafBlock35",
    instrs := [Instr.icmp "%SwitchLeaf36" IPred.eq 8 (.reg "%35") (.imm (.int 8 (BitVec.ofNat 8 13)))],
    term := Term.condbr (.reg "%SwitchLeaf36") "land.rhs.i.preheader" "if.end372.i" }

theorem walkLeafBlock35_find : stage2Body.findBlock "LeafBlock35" = some walkLeafBlock35 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock35]

theorem WalkLink.LeafBlock35 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock35")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%35") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 13) = 1 then "land.rhs.i.preheader" else "if.end372.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock35_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock52`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock52 : Block :=
  { name := "NodeBlock52",
    instrs := [Instr.icmp "%Pivot53" IPred.slt 8 (.reg "%36") (.imm (.int 8 (BitVec.ofNat 8 13)))],
    term := Term.condbr (.reg "%Pivot53") "LeafBlock43" "NodeBlock50" }

theorem walkNodeBlock52_find : stage2Body.findBlock "NodeBlock52" = some walkNodeBlock52 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock52]

theorem WalkLink.NodeBlock52 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock52")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%36") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 13) = 1 then "LeafBlock43" else "NodeBlock50") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock52_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock50`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock50 : Block :=
  { name := "NodeBlock50",
    instrs := [Instr.icmp "%Pivot51" IPred.slt 8 (.reg "%36") (.imm (.int 8 (BitVec.ofNat 8 32)))],
    term := Term.condbr (.reg "%Pivot51") "LeafBlock46" "LeafBlock48" }

theorem walkNodeBlock50_find : stage2Body.findBlock "NodeBlock50" = some walkNodeBlock50 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock50]

theorem WalkLink.NodeBlock50 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock50")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%36") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 32) = 1 then "LeafBlock46" else "LeafBlock48") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock50_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock48`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock48 : Block :=
  { name := "LeafBlock48",
    instrs := [Instr.icmp "%SwitchLeaf49" IPred.eq 8 (.reg "%36") (.imm (.int 8 (BitVec.ofNat 8 32)))],
    term := Term.condbr (.reg "%SwitchLeaf49") "if.end372.i" "while.body370.i" }

theorem walkLeafBlock48_find : stage2Body.findBlock "LeafBlock48" = some walkLeafBlock48 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock48]

theorem WalkLink.LeafBlock48 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock48")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%36") = some (.int 8 x1))
    (hf : WalkLocal { C with block := "while.body370.i" }
      { stateAt (("%SwitchLeaf49", .int 1 (evalICmp .eq x1 (BitVec.ofNat 8 32))) :: s.env) s with pc := "while.body370.i", pre := some s.pc })
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 32) = 1 then "if.end372.i" else "while.body370.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock48_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) hf

/-- `LeafBlock46`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock46 : Block :=
  { name := "LeafBlock46",
    instrs := [Instr.icmp "%SwitchLeaf47" IPred.eq 8 (.reg "%36") (.imm (.int 8 (BitVec.ofNat 8 13)))],
    term := Term.condbr (.reg "%SwitchLeaf47") "if.end372.i" "while.body370.i" }

theorem walkLeafBlock46_find : stage2Body.findBlock "LeafBlock46" = some walkLeafBlock46 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock46]

theorem WalkLink.LeafBlock46 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock46")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%36") = some (.int 8 x1))
    (hf : WalkLocal { C with block := "while.body370.i" }
      { stateAt (("%SwitchLeaf47", .int 1 (evalICmp .eq x1 (BitVec.ofNat 8 13))) :: s.env) s with pc := "while.body370.i", pre := some s.pc })
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 13) = 1 then "if.end372.i" else "while.body370.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock46_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) hf

/-- `NodeBlock62`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock62 : Block :=
  { name := "NodeBlock62",
    instrs := [Instr.icmp "%Pivot63" IPred.slt 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 110)))],
    term := Term.condbr (.reg "%Pivot63") "LeafBlock54" "NodeBlock60" }

theorem walkNodeBlock62_find : stage2Body.findBlock "NodeBlock62" = some walkNodeBlock62 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock62]

theorem WalkLink.NodeBlock62 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock62")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 110) = 1 then "LeafBlock54" else "NodeBlock60") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock62_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock60`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock60 : Block :=
  { name := "NodeBlock60",
    instrs := [Instr.icmp "%Pivot61" IPred.slt 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 116)))],
    term := Term.condbr (.reg "%Pivot61") "LeafBlock56" "LeafBlock58" }

theorem walkNodeBlock60_find : stage2Body.findBlock "NodeBlock60" = some walkNodeBlock60 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock60]

theorem WalkLink.NodeBlock60 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock60")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 116) = 1 then "LeafBlock56" else "LeafBlock58") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock60_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock58`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock58 : Block :=
  { name := "LeafBlock58",
    instrs := [Instr.icmp "%SwitchLeaf59" IPred.eq 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 116)))],
    term := Term.condbr (.reg "%SwitchLeaf59") "if.then413.i" "if.else405.i" }

theorem walkLeafBlock58_find : stage2Body.findBlock "LeafBlock58" = some walkLeafBlock58 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock58]

theorem WalkLink.LeafBlock58 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock58")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 116) = 1 then "if.then413.i" else "if.else405.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock58_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock56`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock56 : Block :=
  { name := "LeafBlock56",
    instrs := [Instr.icmp "%SwitchLeaf57" IPred.eq 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 110)))],
    term := Term.condbr (.reg "%SwitchLeaf57") "if.then403.i" "if.else405.i" }

theorem walkLeafBlock56_find : stage2Body.findBlock "LeafBlock56" = some walkLeafBlock56 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock56]

theorem WalkLink.LeafBlock56 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock56")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 110) = 1 then "if.then403.i" else "if.else405.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock56_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock54`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock54 : Block :=
  { name := "LeafBlock54",
    instrs := [Instr.icmp "%SwitchLeaf55" IPred.eq 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 102)))],
    term := Term.condbr (.reg "%SwitchLeaf55") "if.then397.i" "if.else405.i" }

theorem walkLeafBlock54_find : stage2Body.findBlock "LeafBlock54" = some walkLeafBlock54 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock54]

theorem WalkLink.LeafBlock54 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock54")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 102) = 1 then "if.then397.i" else "if.else405.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock54_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock73`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock73 : Block :=
  { name := "NodeBlock73",
    instrs := [Instr.icmp "%Pivot74" IPred.slt 8 (.reg "%40") (.imm (.int 8 (BitVec.ofNat 8 13)))],
    term := Term.condbr (.reg "%Pivot74") "LeafBlock64" "NodeBlock71" }

theorem walkNodeBlock73_find : stage2Body.findBlock "NodeBlock73" = some walkNodeBlock73 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock73]

theorem WalkLink.NodeBlock73 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock73")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%40") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 13) = 1 then "LeafBlock64" else "NodeBlock71") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock73_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock71`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock71 : Block :=
  { name := "NodeBlock71",
    instrs := [Instr.icmp "%Pivot72" IPred.slt 8 (.reg "%40") (.imm (.int 8 (BitVec.ofNat 8 32)))],
    term := Term.condbr (.reg "%Pivot72") "LeafBlock67" "LeafBlock69" }

theorem walkNodeBlock71_find : stage2Body.findBlock "NodeBlock71" = some walkNodeBlock71 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock71]

theorem WalkLink.NodeBlock71 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock71")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%40") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 32) = 1 then "LeafBlock67" else "LeafBlock69") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock71_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock69`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock69 : Block :=
  { name := "LeafBlock69",
    instrs := [Instr.icmp "%SwitchLeaf70" IPred.eq 8 (.reg "%40") (.imm (.int 8 (BitVec.ofNat 8 32)))],
    term := Term.condbr (.reg "%SwitchLeaf70") "while.end.i" "while.body.i104" }

theorem walkLeafBlock69_find : stage2Body.findBlock "LeafBlock69" = some walkLeafBlock69 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock69]

theorem WalkLink.LeafBlock69 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock69")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%40") = some (.int 8 x1))
    (hf : WalkLocal { C with block := "while.body.i104" }
      { stateAt (("%SwitchLeaf70", .int 1 (evalICmp .eq x1 (BitVec.ofNat 8 32))) :: s.env) s with pc := "while.body.i104", pre := some s.pc })
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 32) = 1 then "while.end.i" else "while.body.i104") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock69_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) hf

/-- `LeafBlock67`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock67 : Block :=
  { name := "LeafBlock67",
    instrs := [Instr.icmp "%SwitchLeaf68" IPred.eq 8 (.reg "%40") (.imm (.int 8 (BitVec.ofNat 8 13)))],
    term := Term.condbr (.reg "%SwitchLeaf68") "while.end.i" "while.body.i104" }

theorem walkLeafBlock67_find : stage2Body.findBlock "LeafBlock67" = some walkLeafBlock67 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock67]

theorem WalkLink.LeafBlock67 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock67")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%40") = some (.int 8 x1))
    (hf : WalkLocal { C with block := "while.body.i104" }
      { stateAt (("%SwitchLeaf68", .int 1 (evalICmp .eq x1 (BitVec.ofNat 8 13))) :: s.env) s with pc := "while.body.i104", pre := some s.pc })
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 13) = 1 then "while.end.i" else "while.body.i104") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock67_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) hf

/-- `NodeBlock83`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock83 : Block :=
  { name := "NodeBlock83",
    instrs := [Instr.icmp "%Pivot84" IPred.slt 8 (.reg "%41") (.imm (.int 8 (BitVec.ofNat 8 110)))],
    term := Term.condbr (.reg "%Pivot84") "LeafBlock75" "NodeBlock81" }

theorem walkNodeBlock83_find : stage2Body.findBlock "NodeBlock83" = some walkNodeBlock83 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock83]

theorem WalkLink.NodeBlock83 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock83")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%41") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 110) = 1 then "LeafBlock75" else "NodeBlock81") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock83_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock81`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock81 : Block :=
  { name := "NodeBlock81",
    instrs := [Instr.icmp "%Pivot82" IPred.slt 8 (.reg "%41") (.imm (.int 8 (BitVec.ofNat 8 116)))],
    term := Term.condbr (.reg "%Pivot82") "LeafBlock77" "LeafBlock79" }

theorem walkNodeBlock81_find : stage2Body.findBlock "NodeBlock81" = some walkNodeBlock81 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock81]

theorem WalkLink.NodeBlock81 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock81")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%41") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 116) = 1 then "LeafBlock77" else "LeafBlock79") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock81_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock79`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock79 : Block :=
  { name := "LeafBlock79",
    instrs := [Instr.icmp "%SwitchLeaf80" IPred.eq 8 (.reg "%41") (.imm (.int 8 (BitVec.ofNat 8 116)))],
    term := Term.condbr (.reg "%SwitchLeaf80") "if.end48.i" "if.else43.i" }

theorem walkLeafBlock79_find : stage2Body.findBlock "LeafBlock79" = some walkLeafBlock79 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock79]

theorem WalkLink.LeafBlock79 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock79")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%41") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 116) = 1 then "if.end48.i" else "if.else43.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock79_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock77`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock77 : Block :=
  { name := "LeafBlock77",
    instrs := [Instr.icmp "%SwitchLeaf78" IPred.eq 8 (.reg "%41") (.imm (.int 8 (BitVec.ofNat 8 110)))],
    term := Term.condbr (.reg "%SwitchLeaf78") "if.then42.i" "if.else43.i" }

theorem walkLeafBlock77_find : stage2Body.findBlock "LeafBlock77" = some walkLeafBlock77 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock77]

theorem WalkLink.LeafBlock77 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock77")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%41") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 110) = 1 then "if.then42.i" else "if.else43.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock77_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock75`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock75 : Block :=
  { name := "LeafBlock75",
    instrs := [Instr.icmp "%SwitchLeaf76" IPred.eq 8 (.reg "%41") (.imm (.int 8 (BitVec.ofNat 8 102)))],
    term := Term.condbr (.reg "%SwitchLeaf76") "if.then37.i" "if.else43.i" }

theorem walkLeafBlock75_find : stage2Body.findBlock "LeafBlock75" = some walkLeafBlock75 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock75]

theorem WalkLink.LeafBlock75 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock75")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%41") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 102) = 1 then "if.then37.i" else "if.else43.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock75_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `for.end.i.i`: the dispatch's comparison `icmp .eq i64` and the edge its bit names. -/
def walkFor_end_i_i : Block :=
  { name := "for.end.i.i",
    instrs := [Instr.icmp "%cmp11.not.i.i" IPred.eq 64 (.reg "%sub54.i") (.reg "%ln.0.i")],
    term := Term.condbr (.reg "%cmp11.not.i.i") "if.end67.i" "if.then57.i" }

theorem walkFor_end_i_i_find : stage2Body.findBlock "for.end.i.i" = some walkFor_end_i_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkFor_end_i_i]

theorem WalkLink.for_end_i_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "for.end.i.i")
    {x1 : BitVec 64} (h1 : evalOperand s (.reg "%sub54.i") = some (.int 64 x1))
    {x2 : BitVec 64} (h2 : evalOperand s (.reg "%ln.0.i") = some (.int 64 x2))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 x2 = 1 then "if.end67.i" else "if.then57.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkFor_end_i_i_find) rfl rfl h1 h2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `if.end67.i`: the dispatch's comparison `icmp .ult i64` and the edge its bit names. -/
def walkIf_end67_i : Block :=
  { name := "if.end67.i",
    instrs := [Instr.icmp "%cmp6919.i" IPred.ult 64 (.reg "%ee.0.lcssa.i") (.reg "%cond.i")],
    term := Term.condbr (.reg "%cmp6919.i") "land.rhs71.i" "while.end78.i" }

theorem walkIf_end67_i_find : stage2Body.findBlock "if.end67.i" = some walkIf_end67_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_end67_i]

theorem WalkLink.if_end67_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end67.i")
    {x1 : BitVec 64} (h1 : evalOperand s (.reg "%ee.0.lcssa.i") = some (.int 64 x1))
    {x2 : BitVec 64} (h2 : evalOperand s (.reg "%cond.i") = some (.int 64 x2))
    (hl : WalkLocal { C with block := "land.rhs71.i" }
      { stateAt (("%cmp6919.i", .int 1 (evalICmp .ult x1 x2)) :: s.env) s with pc := "land.rhs71.i", pre := some s.pc })
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .ult x1 x2 = 1 then "land.rhs71.i" else "while.end78.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkIf_end67_i_find) rfl rfl h1 h2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hl (by simp [WalkLocal])

/-- `NodeBlock94`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock94 : Block :=
  { name := "NodeBlock94",
    instrs := [Instr.icmp "%Pivot95" IPred.slt 8 (.reg "%46") (.imm (.int 8 (BitVec.ofNat 8 13)))],
    term := Term.condbr (.reg "%Pivot95") "LeafBlock85" "NodeBlock92" }

theorem walkNodeBlock94_find : stage2Body.findBlock "NodeBlock94" = some walkNodeBlock94 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock94]

theorem WalkLink.NodeBlock94 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock94")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%46") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 13) = 1 then "LeafBlock85" else "NodeBlock92") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock94_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock92`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock92 : Block :=
  { name := "NodeBlock92",
    instrs := [Instr.icmp "%Pivot93" IPred.slt 8 (.reg "%46") (.imm (.int 8 (BitVec.ofNat 8 32)))],
    term := Term.condbr (.reg "%Pivot93") "LeafBlock88" "LeafBlock90" }

theorem walkNodeBlock92_find : stage2Body.findBlock "NodeBlock92" = some walkNodeBlock92 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock92]

theorem WalkLink.NodeBlock92 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock92")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%46") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 32) = 1 then "LeafBlock88" else "LeafBlock90") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock92_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock90`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock90 : Block :=
  { name := "LeafBlock90",
    instrs := [Instr.icmp "%SwitchLeaf91" IPred.eq 8 (.reg "%46") (.imm (.int 8 (BitVec.ofNat 8 32)))],
    term := Term.condbr (.reg "%SwitchLeaf91") "while.body76.i" "while.end78.i" }

theorem walkLeafBlock90_find : stage2Body.findBlock "LeafBlock90" = some walkLeafBlock90 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock90]

theorem WalkLink.LeafBlock90 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock90")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%46") = some (.int 8 x1))
    (hl : WalkLocal { C with block := "while.body76.i" }
      { stateAt (("%SwitchLeaf91", .int 1 (evalICmp .eq x1 (BitVec.ofNat 8 32))) :: s.env) s with pc := "while.body76.i", pre := some s.pc })
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 32) = 1 then "while.body76.i" else "while.end78.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock90_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hl (by simp [WalkLocal])

/-- `LeafBlock88`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock88 : Block :=
  { name := "LeafBlock88",
    instrs := [Instr.icmp "%SwitchLeaf89" IPred.eq 8 (.reg "%46") (.imm (.int 8 (BitVec.ofNat 8 13)))],
    term := Term.condbr (.reg "%SwitchLeaf89") "while.body76.i" "while.end78.i" }

theorem walkLeafBlock88_find : stage2Body.findBlock "LeafBlock88" = some walkLeafBlock88 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock88]

theorem WalkLink.LeafBlock88 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock88")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%46") = some (.int 8 x1))
    (hl : WalkLocal { C with block := "while.body76.i" }
      { stateAt (("%SwitchLeaf89", .int 1 (evalICmp .eq x1 (BitVec.ofNat 8 13))) :: s.env) s with pc := "while.body76.i", pre := some s.pc })
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 13) = 1 then "while.body76.i" else "while.end78.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock88_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hl (by simp [WalkLocal])

/-- `NodeBlock105`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock105 : Block :=
  { name := "NodeBlock105",
    instrs := [Instr.icmp "%Pivot106" IPred.slt 8 (.reg "%47") (.imm (.int 8 (BitVec.ofNat 8 13)))],
    term := Term.condbr (.reg "%Pivot106") "LeafBlock96" "NodeBlock103" }

theorem walkNodeBlock105_find : stage2Body.findBlock "NodeBlock105" = some walkNodeBlock105 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock105]

theorem WalkLink.NodeBlock105 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock105")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%47") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 13) = 1 then "LeafBlock96" else "NodeBlock103") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock105_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock103`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock103 : Block :=
  { name := "NodeBlock103",
    instrs := [Instr.icmp "%Pivot104" IPred.slt 8 (.reg "%47") (.imm (.int 8 (BitVec.ofNat 8 32)))],
    term := Term.condbr (.reg "%Pivot104") "LeafBlock99" "LeafBlock101" }

theorem walkNodeBlock103_find : stage2Body.findBlock "NodeBlock103" = some walkNodeBlock103 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock103]

theorem WalkLink.NodeBlock103 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock103")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%47") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 32) = 1 then "LeafBlock99" else "LeafBlock101") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock103_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock101`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock101 : Block :=
  { name := "LeafBlock101",
    instrs := [Instr.icmp "%SwitchLeaf102" IPred.eq 8 (.reg "%47") (.imm (.int 8 (BitVec.ofNat 8 32)))],
    term := Term.condbr (.reg "%SwitchLeaf102") "while.body462.i" "if.then467.i" }

theorem walkLeafBlock101_find : stage2Body.findBlock "LeafBlock101" = some walkLeafBlock101 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock101]

theorem WalkLink.LeafBlock101 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock101")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%47") = some (.int 8 x1))
    (hl : WalkLocal { C with block := "while.body462.i" }
      { stateAt (("%SwitchLeaf102", .int 1 (evalICmp .eq x1 (BitVec.ofNat 8 32))) :: s.env) s with pc := "while.body462.i", pre := some s.pc })
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 32) = 1 then "while.body462.i" else "if.then467.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock101_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hl (by simp [WalkLocal])

/-- `LeafBlock99`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock99 : Block :=
  { name := "LeafBlock99",
    instrs := [Instr.icmp "%SwitchLeaf100" IPred.eq 8 (.reg "%47") (.imm (.int 8 (BitVec.ofNat 8 13)))],
    term := Term.condbr (.reg "%SwitchLeaf100") "while.body462.i" "if.then467.i" }

theorem walkLeafBlock99_find : stage2Body.findBlock "LeafBlock99" = some walkLeafBlock99 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock99]

theorem WalkLink.LeafBlock99 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock99")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%47") = some (.int 8 x1))
    (hl : WalkLocal { C with block := "while.body462.i" }
      { stateAt (("%SwitchLeaf100", .int 1 (evalICmp .eq x1 (BitVec.ofNat 8 13))) :: s.env) s with pc := "while.body462.i", pre := some s.pc })
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 13) = 1 then "while.body462.i" else "if.then467.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock99_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hl (by simp [WalkLocal])

/-- `if.then485.i`: the dispatch's comparison `icmp .eq i32` and the edge its bit names. -/
def walkIf_then485_i : Block :=
  { name := "if.then485.i",
    instrs := [Instr.icmp "%48" IPred.eq 32 (.reg "%sp.i.1") (.imm (.int 32 (BitVec.ofNat 32 0)))],
    term := Term.condbr (.reg "%48") "if.end490.i" "if.then488.i" }

theorem walkIf_then485_i_find : stage2Body.findBlock "if.then485.i" = some walkIf_then485_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then485_i]

theorem WalkLink.if_then485_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then485.i")
    {x1 : BitVec 32} (h1 : evalOperand s (.reg "%sp.i.1") = some (.int 32 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 32 0) = 1 then "if.end490.i" else "if.then488.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkIf_then485_i_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-! ### Class B's ten instances -/

/-- `cond.true.i`: no instructions, and the edge it takes. -/
def walkCond_true_i : Block :=
  { name := "cond.true.i", instrs := [], term := Term.br "NodeBlock27" }

theorem walkCond_true_i_find : stage2Body.findBlock "cond.true.i" = some walkCond_true_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkCond_true_i]

theorem WalkLink.cond_true_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "cond.true.i")
    : ∃ s', WalkLink calls G C s { C with block := "NodeBlock27" } s' := by
  exact WalkLink.br (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkCond_true_i_find) rfl rfl (by simp [WalkLocal])

/-- `land.rhs.i.preheader`: no instructions, and the edge it takes. -/
def walkLand_rhs_i_preheader : Block :=
  { name := "land.rhs.i.preheader", instrs := [], term := Term.br "land.rhs.i" }

theorem walkLand_rhs_i_preheader_find : stage2Body.findBlock "land.rhs.i.preheader" = some walkLand_rhs_i_preheader := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLand_rhs_i_preheader]

theorem WalkLink.land_rhs_i_preheader {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "land.rhs.i.preheader")
    (hloc : WalkLocal { C with block := "land.rhs.i" } { s with pc := "land.rhs.i", pre := some s.pc })
    : ∃ s', WalkLink calls G C s { C with block := "land.rhs.i" } s' := by
  exact WalkLink.br (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkLand_rhs_i_preheader_find) rfl rfl hloc

/-- `if.else387.i`: no instructions, and the edge it takes. -/
def walkIf_else387_i : Block :=
  { name := "if.else387.i", instrs := [], term := Term.br "NodeBlock62" }

theorem walkIf_else387_i_find : stage2Body.findBlock "if.else387.i" = some walkIf_else387_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_else387_i]

theorem WalkLink.if_else387_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.else387.i")
    : ∃ s', WalkLink calls G C s { C with block := "NodeBlock62" } s' := by
  exact WalkLink.br (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_else387_i_find) rfl rfl (by simp [WalkLocal])

/-- `if.then397.i`: no instructions, and the edge it takes. -/
def walkIf_then397_i : Block :=
  { name := "if.then397.i", instrs := [], term := Term.br "if.then413.i" }

theorem walkIf_then397_i_find : stage2Body.findBlock "if.then397.i" = some walkIf_then397_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then397_i]

theorem WalkLink.if_then397_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then397.i")
    : ∃ s', WalkLink calls G C s { C with block := "if.then413.i" } s' := by
  exact WalkLink.br (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then397_i_find) rfl rfl (by simp [WalkLocal])

/-- `if.then403.i`: no instructions, and the edge it takes. -/
def walkIf_then403_i : Block :=
  { name := "if.then403.i", instrs := [], term := Term.br "if.then413.i" }

theorem walkIf_then403_i_find : stage2Body.findBlock "if.then403.i" = some walkIf_then403_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then403_i]

theorem WalkLink.if_then403_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then403.i")
    : ∃ s', WalkLink calls G C s { C with block := "if.then413.i" } s' := by
  exact WalkLink.br (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then403_i_find) rfl rfl (by simp [WalkLocal])

/-- `if.else405.i`: no instructions, and the edge it takes. -/
def walkIf_else405_i : Block :=
  { name := "if.else405.i", instrs := [], term := Term.br "if.then413.i" }

theorem walkIf_else405_i_find : stage2Body.findBlock "if.else405.i" = some walkIf_else405_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_else405_i]

theorem WalkLink.if_else405_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.else405.i")
    : ∃ s', WalkLink calls G C s { C with block := "if.then413.i" } s' := by
  exact WalkLink.br (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_else405_i_find) rfl rfl (by simp [WalkLocal])

/-- `if.else.i`: no instructions, and the edge it takes. -/
def walkIf_else_i : Block :=
  { name := "if.else.i", instrs := [], term := Term.br "NodeBlock83" }

theorem walkIf_else_i_find : stage2Body.findBlock "if.else.i" = some walkIf_else_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_else_i]

theorem WalkLink.if_else_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.else.i")
    : ∃ s', WalkLink calls G C s { C with block := "NodeBlock83" } s' := by
  exact WalkLink.br (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_else_i_find) rfl rfl (by simp [WalkLocal])

/-- `if.then37.i`: no instructions, and the edge it takes. -/
def walkIf_then37_i : Block :=
  { name := "if.then37.i", instrs := [], term := Term.br "if.end48.i" }

theorem walkIf_then37_i_find : stage2Body.findBlock "if.then37.i" = some walkIf_then37_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then37_i]

theorem WalkLink.if_then37_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then37.i")
    : ∃ s', WalkLink calls G C s { C with block := "if.end48.i" } s' := by
  exact WalkLink.br (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then37_i_find) rfl rfl (by simp [WalkLocal])

/-- `if.then42.i`: no instructions, and the edge it takes. -/
def walkIf_then42_i : Block :=
  { name := "if.then42.i", instrs := [], term := Term.br "if.end48.i" }

theorem walkIf_then42_i_find : stage2Body.findBlock "if.then42.i" = some walkIf_then42_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then42_i]

theorem WalkLink.if_then42_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then42.i")
    : ∃ s', WalkLink calls G C s { C with block := "if.end48.i" } s' := by
  exact WalkLink.br (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then42_i_find) rfl rfl (by simp [WalkLocal])


/-! ### The budget, counted

`stage2Budget` is `stage2EntryAllowance * nep + stage2ByteAllowance * n +
stage2PositionAllowance * nxp + stage2FinalisationAllowance` with the constants
32, 8, 32 and 32 (`JsonStage2Contract`).  Two of the four are readings of the
pinned body rather than choices, and this section takes them.

**The per-entry allowance.**  One iteration of the entry loop is the whole
dispatch, and the dispatch's own price is the longest path from its head
(`while.body.i`) to the merge that closes the iteration (`cleanup478.i`), over the
graph with the five scans' repeated visits removed: what is left is a path through
the switch, the nesting arm, the record's write and the two container arms.
`walkDispatchPrice` is that path over `stage2Body`'s own block list and
terminators, and it is **22 blocks** — ten inside the allowance's 32.  The
allowance's remainder is not slack the dispatch spends: the head's own `phi` run,
the merge's two `phi`s and the retest are steps of blocks already counted, and a
`WalkLink` per block is the one step the trace charges.

The path is `while.body.i → NodeBlock21 → … → if.end473.i → cleanup478.i`; the
scans' *exits* (`while.end.i`, `while.end78.i`, `if.end372.i`, `if.end290.i`) are on
it, and their repeated *visits* are not — they are charged to a document byte.

**The per-byte allowance.**  A scan's repeated visit is one step of the scan, and a
scan step stays inside its own block set: the header, the landing block, and the
two switch levels between the landing and the header.  `walkScanStepSets` is the
five sets as the body's own names; the widest is six blocks (the four token scans
have two switch levels with two leaves each), so one byte's visit is at most six
steps — inside the allowance's 8.  The literal comparison's set is two, and its
own count is bounded by `min (ee - idx) ln` with `ln ≤ 5` at `if.end48.i`'s phi, so
its five bytes are five byte-allowances.

**The per-position allowance.**  32 is the expander's `(nps + 1) * 3` scan and its
`(nps + 1) * decodeIterCost` walk, counted per escape position by
`escapeExpandBudget`; nothing in this module reads it, and the decoder's own cost
is the `n / 64` term the byte allowance covers sixty-four times over.

What the count does not do is *compose*.  `walkMeasure`'s decrease is one step per
link and a chain's step count is the number of links it contains
(`WalkChain.steps`), so the comparison of that count against `stage2Budget` is the
completed chain's work; this section fixes the two numbers the comparison needs and
reads them off the pinned AST rather than asserting them. -/

set_option maxRecDepth 100000

/-- The ten blocks the five scans visit repeatedly: each scan's header and its
landing block.  A visit to one of them is charged to a document byte
(`stage2ByteAllowance`), not to an entry. -/
def walkScanBlocks : List String :=
  ["for.body.i.i", "for.inc.i.i", "land.rhs.i", "while.body370.i",
   "land.rhs.i103", "while.body.i104", "land.rhs71.i", "while.body76.i",
   "land.rhs457.i", "while.body462.i"]

/-- The five scans' own block sets, at the body's names: the header, the landing
block, the switch levels between the landing and the header, and the switch's
leaves.  A scan step stays inside its set, so the set's size bounds one byte's
visit. -/
def walkScanStepSets : List (List String) :=
  [ -- the literal comparison's latch
    ["for.body.i.i", "for.inc.i.i"],
   -- the whitespace scan
    ["while.body370.i", "land.rhs.i", "NodeBlock52", "NodeBlock50", "LeafBlock46",
     "LeafBlock48"],
   -- the string scan
    ["while.body.i104", "land.rhs.i103", "NodeBlock73", "NodeBlock71",
     "LeafBlock67", "LeafBlock69"],
   -- the escape scan
    ["while.body76.i", "land.rhs71.i", "NodeBlock94", "NodeBlock92", "LeafBlock88",
     "LeafBlock90"],
   -- the extra-token scan
    ["while.body462.i", "land.rhs457.i", "NodeBlock105", "NodeBlock103",
     "LeafBlock99", "LeafBlock101"]]

/-- A block's successors, at its own terminator: the body's control flow as the
pinned AST states it. -/
def walkSucc (n : String) : List String :=
  match stage2Body.findBlock n with
  | none => []
  | some b =>
      match b.term with
      | .br t => [t]
      | .condbr _ t e => [t, e]
      | .ret _ _ => []
      | .unreachable => []

/-- **The longest path between two blocks**, over the graph with `banned`
removed, at a fuel that bounds the search.  `none` is "no path": a branch that
does not reach the target contributes nothing, which is what keeps a path that
leaves the loop (`if.then`, `s2_walk.exit`) out of the count. -/
def walkLongest (fuel : Nat) (banned : List String) (s t : String) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if s = t then some 0
      else
        ((walkSucc s).filter (fun u => !banned.contains u)).foldr
          (fun u acc =>
            match walkLongest fuel banned u t with
            | none => acc
            | some d => max (some (d + 1)) acc)
          none

/-- **The dispatch's price**: the longest path from the loop head to the merge
that closes an iteration, with the scans' repeated visits removed. -/
def walkDispatchPrice : Option Nat :=
  walkLongest 40 walkScanBlocks "while.body.i" "cleanup478.i"

#guard walkScanBlocks.all (fun n => (stage2Body.findBlock n).isSome) = true

#guard walkScanBlocks.length = 10
#guard walkScanBlocks.eraseDups.length = 10

#guard walkScanStepSets.all (fun xs => xs.all (fun n => (stage2Body.findBlock n).isSome)) = true
#guard walkScanStepSets.all (fun xs => xs.eraseDups.length = xs.length) = true
#guard walkScanStepSets.foldr (fun xs acc => max xs.length acc) 0 = 6

#guard walkDispatchPrice = some 22

/-- **The dispatch's own path is 22 blocks, and the per-entry allowance covers
it.**  The allowance is 32; the ten not spent are the head's `phi` run and the
merge's two `phi`s and retest, which are steps of blocks the path already counts,
and the entry's own record write, which is a block of the path. -/
theorem walkDispatch_le_entryAllowance :
    ∃ d, walkDispatchPrice = some d ∧ d ≤ stage2EntryAllowance := by
  refine ⟨22, by decide, by decide⟩

/-- **A byte's visit is inside the byte allowance.**  The widest scan step is six
blocks and the allowance is 8. -/
theorem walkScanStep_width_le_byteAllowance :
    walkScanStepSets.foldr (fun xs acc => max xs.length acc) 0 ≤ stage2ByteAllowance := by
  decide

/-- **The budget, as the four allowances read the arguments.**  This is the term
`stage2Budget` states, with the two counted factors named beside their values. -/
theorem walkBudget_count (nep n nxp : Nat) :
    stage2EntryAllowance * nep + stage2ByteAllowance * n +
        stage2PositionAllowance * nxp + stage2FinalisationAllowance =
      32 * nep + 8 * n + 32 * nxp + 32 := rfl

/-- info: 'LeanLLVM.Refinement.WalkScope.walkDispatch_le_entryAllowance' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_le_entryAllowance

/-- info: 'LeanLLVM.Refinement.WalkScope.walkScanStep_width_le_byteAllowance' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkScanStep_width_le_byteAllowance

/-- info: 'LeanLLVM.Refinement.WalkScope.walkBudget_count' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkBudget_count

end WalkScope

end LeanLLVM.Refinement

/-! ### The nesting arm's and the trace's footprints, measured

Each is `#print axioms` on the declaration itself, and each is at or below the
`[propext, Classical.choice, Quot.sound]` ceiling the file's other pinned
declarations report.  The append lemma and the trace's arithmetic are below it —
`[propext, Quot.sound]` — because they read no `String` register name; the block's
pin, chain, terminator and step, and the two links that wrap them, do. -/

/-- info: 'LeanLLVM.Refinement.WalkScope.walkDenoteCode_append_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkDenoteCode_append_some

/-- info: 'LeanLLVM.Refinement.WalkScope.ifEnd24_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.ifEnd24_find

/-- info: 'LeanLLVM.Refinement.WalkScope.ifEnd24_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.ifEnd24_denote

/-- info: 'LeanLLVM.Refinement.WalkScope.ifEnd24_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.ifEnd24_term

/-- info: 'LeanLLVM.Refinement.WalkScope.ifEnd24_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.ifEnd24_step

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkChain.measure_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkChain.measure_le

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkChain.steps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkChain.steps

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkChain.completes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkChain.completes

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.whileBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.whileBody

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.ifEnd24' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.ifEnd24

/-! ### The middle's class lemmas and two instances, measured

The two general lemmas and one instance of each class, at `#print axioms`: each is
at the `[propext, Classical.choice, Quot.sound]` ceiling the file's other pinned
declarations report.  The rest of the instances are the same application of the
same lemmas, so a per-instance reading adds nothing; what it would add is the
`decide` on the eight disequalities, which reads no axiom beyond `propext`. -/

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.icmpBr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.icmpBr

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.br' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.br

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.NodeBlock21' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.NodeBlock21

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.condBr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.condBr

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.refusalStore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.refusalStore

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.if_then16_i' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then16_i

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.cond_true_i' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.cond_true_i

/-- info: 'LeanLLVM.Refinement.WalkScope.walkDenoteCode_icmp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkDenoteCode_icmp


/-- info: 'LeanLLVM.Refinement.WalkScope.walkExecTerm_condbr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkExecTerm_condbr
