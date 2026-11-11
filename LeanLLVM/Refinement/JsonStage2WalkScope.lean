/-
The stage-2 walk's loop invariants, its measure, and its six back edges.

`Stage2WalkObligation` (`JsonStage2IR`) is `Satisfies` for the pinned 165-block
body, and its first conjunct is completion at `stage2Budget`
(`stage2WalkObligation_iff_completion`).  `runFuel` is fuel-indexed, so the proof
that resists is the loop: an invariant preserved by every arm, and a measure that
decreases on every iteration.  This module scopes that proof.  It discharges the
literal comparison's arm and the four scans', five edges that decrease the measure
at the edge itself; the entry loop's edge (the merge at `cleanup478.i`, its two
`phi`s, the exit test, and the inner reset), which preserves the invariant and
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
* `records : Nat` — the event records emitted, with `evlen = nev0 + 13 * records`
  and `records ≤ k`.  Thirteen bytes per record is the body's own store
  (`out_reserve(&z->ev, 13)` and `len += 13`), and at most one record per entry is
  the count `Stage2OneRecordPerEntry` needs;
* `k : Nat` — the block index into the entry stream, at the phi the loop reads
  (`%k.0.i249`);
* `alen` and `evlen` — the two cursors;
* `pending : Option (Nat × Nat)` — the record in flight: the entry position and
  the arena offset reserved for its decoded body, `none` between records;
* `refusal : Bool` and `eoff : Nat` — the refusal bit and the offset it stores,
  the two clauses nothing in `Stage2Run`'s vocabulary names at the refusal arm;
* `block : String` — the block the run is at;
* `inner : Nat` — the remaining inner work at the block, the measure's second
  component.

`WalkGeom` is `stage2Pre`'s staging, named field for field.  A geometry is not
assumed: `WalkGeom.nonempty` unpacks any `Γ_stage2.pre` into one, so the invariant
is not vacuous at a caller the record admits.

The memory half is `Owns (inRegions [(dst, alen), (ev, evlen)]) m0 s.mem`: the
walk owns the arena and event prefixes it has written, changes nothing outside
them, and they are present in the memory it produced.  The report's `Owns` clause
at `alen + 64` follows from this and the staged capacity
(`owns_reserve_of_owns_extent`, `JsonStage2Body`).

## The measure

The measure is a `Nat`, not a pair:

    walkMeasure G C = (G.nep - C.k) * (walkInnerCap G + 1) + C.inner
    walkInnerCap G  = G.n + 5

The pair is `(remaining entries, inner work)`, encoded lexicographically with the
inner component's bound as the radix.  `n + 5` is the bound on the inner work at
any back edge: the scans `land.rhs.i`, `land.rhs.i103`, `land.rhs71.i` and
`land.rhs457.i` walk the document, so at most `n`; the literal comparison
`for.body.i.i` is bounded by `min (ee - idx) ln` with `ln` four or five at
`if.end48.i`'s phi, so at most `n + 5`.

The four scans' arms show the decrease and not the cap, and the difference
matters.  Each of them decreases `inner` by one at a fixed `k`, so the radix plays
no part on those edges.  `inner ≤ walkInnerCap G` is not a consequence of the
register bounds the scans carry — `WalkInv` bounds each scan's own bound register
only by `2 ^ 64` — so it is a field of the invariant, `WalkInv.inner_cap`, and
every arm that resets the inner component must re-establish it (the two proved
below do, because they lower it).  Its production is the seed's: the loop head
carries the whole dispatch's allowance, `walkSeed G` sets `inner` to
`walkInnerCap G`, and `walkSeed_invariant` is the invariant at the loop head.
The bound is the right value, and the reason is in the body: each scan's bound is
one of two words.  `%cond350.i` is either `%4` — the word `entry` loads from the
state's own slot at offset 8 — or `%conv347.i`, a `zext` of a 32-bit lane of the
entry stream read at `%inc.i`; `%cond.i` is either `%4` or `%conv.i`, the same
lane read.  A lane is an entry position, and every entry position is below `n`
(`WalkGeom.inside`), while `nep ≤ n` (`WalkGeom.nep_le`) is what puts the lane's
index inside the stream.  So a scan's remaining work is `c - i` with `c` an entry
position — at most `n`, inside `n + 5` with five to spare.  The slot `%4` is read
is where `s2_init` leaves the document length, and that layout is not part of
`WalkGeom`: it is the seeding edges' work, and it is why the seed's inner value is
the allowance rather than a reading of the register.  The outer arm is strict on
the factor because `inner` resets to at most the cap, which is why the radix is
`cap + 1`.

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
merge, the exit test, and the inner reset at the invariant — but the iteration
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
iteration's strict decrease (`walkMeasure_step`), and the entry loop's back edge
itself (`walkBack_step`: `cleanup478.i`'s merge, the exit test, and the inner
reset).  The entry loop's arm — the dispatch the edge closes over — does not
close, and *The entry loop's first obligation*, below, records what it needs and
why: the loop's first store is to the caller's cursor record, the objects the
flattening appends are staged by neither `WalkGeom` nor `Γ_stage2at`'s
precondition, and `Owns` cannot survive a store outside the region it claims.  The
`#guard`s beside `storeTargets` read the store addresses off the pinned body.
`WalkLocal` is still `True` at every block outside the ten the five arms reach, so
well-foundedness over the whole control flow is not established; the seed, the
back edge and the exit establish the invariant at the ends of the walk and across
its one edge, not over the dispatch between them.

The cap is a clause and not an arm, and it is now carried: `WalkInv.inner_cap`
bounds the inner component by `walkInnerCap G`, the two arms that reset it
re-establish it because they lower it, and the seed satisfies it by construction
(`walkSeed_inner_cap`).  The value `n + 5` is justified by the scan bounds above
and exceeded by none of them.  `WalkInv.alen_ge` is the second clause the exit
needed and the invariant did not carry: the report's `arenaGe`, the append-only
half of the arena cursor.
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

/-- **The staging is inhabited at every caller the record admits.**  `WalkGeom`
is `stage2Pre` unpacked, so a walk inside `Γ_stage2.pre` has a geometry to carry;
without this the invariant would be satisfiable only by a caller the record
refuses, which is the vacuity the completion conjunct exists to exclude. -/
theorem WalkGeom.nonempty {args : List Value} {m0 : Mem} {next : Nat}
    (h : Γ_stage2.pre args m0 next) : Nonempty (WalkGeom m0) := by
  have h' : stage2Pre args m0 next := h
  obtain ⟨b, n, ep, nep, xp, nxp, dst, dstcap, ndst, ev, evcap, nev, err, bs, ent,
    ndst0, nev0, -, doc, tail, entries, order, inside, esc, arenaCap, arenaRoom,
    evCap, evRoom, ndstRead, nevRead, errBytes, maxDoc, separate⟩ := h'
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
  }⟩

/-- The entry count is at most the document's: the stream's positions are
strictly increasing and inside the document.  `Stage2Run.nep_le` is the same fact
at the report; the loop needs it at the staging. -/
theorem WalkGeom.nep_le {m0 : Mem} (G : WalkGeom m0) : G.nep ≤ G.n := by
  rw [← readLanes32_length m0 G.ep G.nep G.ent G.entries]
  exact length_le_of_pairwise_lt G.order G.inside

/-! ### The carry and the invariant -/

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
  /-- The event records emitted, thirteen bytes each. -/
  records : Nat
  /-- The decoded bodies' document extents, in document order. -/
  spans : List (Nat × Nat)
  /-- The record in flight: its entry position and its reserved arena offset. -/
  pending : Option (Nat × Nat)
  /-- The refusal bit. -/
  refusal : Bool
  /-- The refusal offset. -/
  eoff : Nat
  /-- The block the run is at. -/
  block : String
  /-- The remaining inner work at that block. -/
  inner : Nat

/-- A scan's counter at a block that reads it: the counter register holds `i`,
the scan's own bound register holds `c`, and the remaining inner work is `c - i`.
Every scan tests its counter for equality with that bound, so the two registers
are what both its guard and its measure are read from. -/
def ScanCount (s : State) (phi cond : String) (inner : Nat) : Prop :=
  ∃ i c : Nat, inner = c - i ∧ i < c ∧ c < 2 ^ 64 ∧
    lookupName s.env phi = some (.int 64 (BitVec.ofNat 64 i)) ∧
    lookupName s.env cond = some (.int 64 (BitVec.ofNat 64 c))

/-- The same at a scan's landing block.  The counter is the increment the latch
wrote — `BlockEval`'s `phi` selects it because the predecessor names the latch —
and the bound register is the one the latch read. -/
def ScanLanded (s : State) (src inc cond : String) (inner : Nat) : Prop :=
  ∃ i c : Nat, inner = c - i ∧ i < c ∧ c < 2 ^ 64 ∧
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
  ∀ i c : Nat, inner = c - i →
    lookupName s.env phi = some (.int 64 (BitVec.ofNat 64 i)) →
    lookupName s.env cond = some (.int 64 (BitVec.ofNat 64 c)) →
    i + 1 < c

/-- A bound on the inner work at any back edge: the scans are bounded by the
document, and the literal comparison by its own five-byte cap.  It is the
radix's base in `walkMeasure` and the value the invariant's `inner_cap` clause
bounds the inner component by, which is why it is stated before both. -/
def walkInnerCap {m0 : Mem} (G : WalkGeom m0) : Nat := G.n + 5

/-- The block-local half of the invariant: the inner component and the registers
it is read from, at the ten blocks the five proved arms reach — the literal
comparison's two and each of the four scans' latch and landing.  At every other
block it is `True`; pinning it there is the remaining arm's work (the entry
loop's), and the module docstring says so rather than claiming a bound it does
not have. -/
def WalkLocal {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) : Prop :=
  if C.block = "for.inc.i.i" then
    ∃ i c : Nat, C.inner = c - i ∧ i < c ∧ c < 2 ^ 64 ∧
      lookupName s.env "%i.029.i.i" = some (.int 64 (BitVec.ofNat 64 i)) ∧
      lookupName s.env "%cond.i.i" = some (.int 64 (BitVec.ofNat 64 c))
  else if C.block = "for.body.i.i" then
    ∃ i c : Nat, C.inner = c - i ∧ i < c ∧ c < 2 ^ 64 ∧
      s.pre = some "for.inc.i.i" ∧
      lookupName s.env "%inc.i.i" = some (.int 64 (BitVec.ofNat 64 i)) ∧
      lookupName s.env "%cond.i.i" = some (.int 64 (BitVec.ofNat 64 c))
  else if C.block = "while.body370.i" then
    ScanCount s "%ee.0.i238" "%cond350.i" C.inner
  else if C.block = "land.rhs.i" then
    ScanLanded s "while.body370.i" "%inc371.i" "%cond350.i" C.inner
  else if C.block = "while.body.i104" then
    ScanCount s "%ee.011.i" "%cond.i" C.inner
  else if C.block = "land.rhs.i103" then
    ScanLanded s "while.body.i104" "%inc.i105" "%cond.i" C.inner
  else if C.block = "while.body76.i" then
    ScanCount s "%s2.020.i" "%cond.i" C.inner
  else if C.block = "land.rhs71.i" then
    ScanLanded s "while.body76.i" "%inc77.i" "%cond.i" C.inner
  else if C.block = "while.body462.i" then
    ScanCount s "%q.0.i246" "%cond350.i" C.inner
  else if C.block = "land.rhs457.i" then
    ScanLanded s "while.body462.i" "%inc463.i" "%cond350.i" C.inner
  else True

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
  /-- At most one record per entry. -/
  records_le : C.records ≤ C.k
  /-- The event cursor is exactly thirteen bytes per record. -/
  evlen_eq : C.evlen = G.nev0 + stage2RecordBytes * C.records
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
  pending_at : ∀ p off, C.pending = some (p, off) → off = C.alen ∧ p < G.n
  /-- The refusal offset is inside the document. -/
  eoff_le : C.eoff ≤ G.n
  /-- **The inner component is inside the dispatch's allowance.**  This is the
  clause the outer arm's strictness reads: an iteration advances `k` by one and
  resets `inner` to at most `walkInnerCap G`, so the radix `cap + 1` makes the
  outer term fall by at least one even when the inner component resets to its
  cap.  It cannot be derived from the register bounds the scans carry — those
  bound a scan's own bound register by `2 ^ 64` — which is why it is a field
  here and its production at the loop head is stated with the seed. -/
  inner_cap : C.inner ≤ walkInnerCap G
  /-- The walk owns the two prefixes it has written: changes only inside them,
  and they are present in the memory the run has produced.  The claim runs from
  the staged memory to the run's own, which is the direction `Owns`'s presence
  half is about and the direction the report's region clause reads. -/
  owning : Owns (inRegions [(G.dst, C.alen), (G.ev, C.evlen)]) m0 s.mem
  /-- The block-local facts the measure is read from. -/
  blockLocal : WalkLocal C s

namespace WalkInv

variable {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}

/-- The arena's bound, from the carried extents: this is
`Stage2SpansInside`'s content and `arenaLe_of_spans`'s conclusion, so the report's
`alen ≤ ndst0 + n` is downstream of the carry rather than assumed. -/
theorem alen_le (h : WalkInv G C s) : C.alen ≤ G.ndst0 + G.n :=
  arenaLe_of_spans h.spans_order h.spans_inside h.alen_le_sum

/-- The event cursor's bound, from one record per entry and the entry count. -/
theorem evlen_le (h : WalkInv G C s) : C.evlen ≤ G.nev0 + stage2RecordBytes * G.n := by
  have h1 : stage2RecordBytes * C.records ≤ stage2RecordBytes * G.n :=
    Nat.mul_le_mul_left _ (le_trans h.records_le (le_trans h.k_le G.nep_le))
  rw [h.evlen_eq]
  omega

/-- The block-local facts at the latch: the invariant implies them, and the arm's
lemma takes them explicitly so its `WalkInv` hypothesis is not unpacked twice. -/
theorem forInc {h : WalkInv G C s} (hblock : C.block = "for.inc.i.i") :
    ∃ i c : Nat, C.inner = c - i ∧ i < c ∧ c < 2 ^ 64 ∧
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
records, no extents, no record in flight, no refusal, and the whole dispatch's
inner allowance. -/
def walkSeed {m0 : Mem} (G : WalkGeom m0) : WalkCarry G where
  k := 0
  alen := G.ndst0
  evlen := G.nev0
  records := 0
  spans := []
  pending := none
  refusal := false
  eoff := 0
  block := "NodeBlock21"
  inner := walkInnerCap G

/-- The state the initialisation hands the loop: the header's block after its
`phi` selected the first entry position, and the two cursors as the caller staged
them. -/
def WalkSeedState {m0 : Mem} (G : WalkGeom m0) (s : State) : Prop :=
  s.pc = "NodeBlock21" ∧
    lookupName s.env "%k.0.i249" = some (.int 64 (BitVec.ofNat 64 0)) ∧
    Owns (inRegions [(G.dst, G.ndst0), (G.ev, G.nev0)]) m0 s.mem

/-- **The cap at the seed is the allowance itself**, so the clause that the outer
arm's strictness reads is satisfied by construction rather than by a register
bound. -/
theorem walkSeed_inner_cap {m0 : Mem} (G : WalkGeom m0) :
    (walkSeed G).inner ≤ walkInnerCap G :=
  Nat.le_refl _

/-- **The invariant at the loop head.**  `walkSeed` satisfies every clause of
`WalkInv` at a `WalkSeedState`, so the seed's production is the initialisation's
three facts and nothing else. -/
theorem walkSeed_invariant {m0 : Mem} (G : WalkGeom m0) {s : State}
    (h : WalkSeedState G s) : WalkInv G (walkSeed G) s := by
  obtain ⟨hpc, hk, hown⟩ := h
  refine
    { pc_eq := hpc
      blockIndex := hk
      k_le := Nat.zero_le _
      records_le := Nat.zero_le _
      evlen_eq := rfl
      alen_le_sum := by simp [walkSeed]
      alen_ge := Nat.le_refl _
      spans_order := by simp [walkSeed]
      spans_inside := by simp [walkSeed]
      pending_at := ?_
      eoff_le := Nat.zero_le _
      inner_cap := walkSeed_inner_cap G
      owning := hown
      blockLocal := ?_ }
  · intro p off hp
    simp [walkSeed] at hp
  · simp [WalkLocal, walkSeed]

/-! ### The measure -/

/-- **The measure**, as one `Nat`: the remaining entries radix the remaining inner
work.  The outer term decreases by at least one per entry; the inner term by
exactly one per inner iteration; the radix is `cap + 1` so an outer step is strict
even when the inner component resets to its cap. -/
def walkMeasure {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) : Nat :=
  (G.nep - C.k) * (walkInnerCap G + 1) + C.inner

/-- The latch's own guard: the exit test is false, so the back edge — not
`for.end.i.i` — is the one the latch takes.  It is the only fact the arm needs
beside the invariant, because the invariant's block-local clause is what names the
registers the guard is about. -/
def ForIncGuard {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State) : Prop :=
  ∃ i c : Nat, C.inner = c - i ∧ i + 1 < c ∧ c < 2 ^ 64 ∧
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
    (hinner : C.inner = c - i) (hlt : i + 1 < c) (hcw : c < 2 ^ 64) :
    ∃ (e : State) (C' : WalkCarry G),
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
  let C' : WalkCarry G := { C with block := "for.body.i.i", inner := c - (i + 1) }
  have hpc : s.pc = "for.inc.i.i" := by rw [hInv.pc_eq, hblock]
  have hstep : step calls stage2Body s = .jump e := forInc_term s i c hpc hi hc hlt hcw
  have hk : lookupName e.env "%k.0.i249" = lookupName s.env "%k.0.i249" := by
    dsimp only [e, State.bind]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
  refine ⟨e, C', ?_, rfl, ?_, ?_⟩
  · refine
      { pc_eq := rfl
        blockIndex := by rw [hk]; exact hInv.blockIndex
        k_le := hInv.k_le
        records_le := hInv.records_le
        evlen_eq := hInv.evlen_eq
        alen_le_sum := hInv.alen_le_sum
        alen_ge := hInv.alen_ge
        spans_order := hInv.spans_order
        spans_inside := hInv.spans_inside
        pending_at := hInv.pending_at
        eoff_le := hInv.eoff_le
        inner_cap := by
          have hcap : c - i ≤ G.n + 5 := by
            simpa only [walkInnerCap] using hinner ▸ hInv.inner_cap
          show c - (i + 1) ≤ G.n + 5
          omega
        owning := hInv.owning
        blockLocal := ?_ }
    dsimp only [WalkLocal, C']
    rw [if_neg (by decide), if_pos rfl]
    refine ⟨i + 1, c, rfl, hlt, hcw, rfl, ?_⟩
    dsimp only [e, State.bind]
    refine ⟨?_, ?_⟩
    · rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
    · rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      exact hc
  · dsimp only [walkMeasure, C']
    rw [hinner]
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
    WalkLocal C s = ScanLanded s "while.body370.i" "%inc371.i" "%cond350.i" C.inner := by
  simp [WalkLocal, h]

/-- `WalkLocal` at the string scan's latch. -/
theorem WalkLocal.stringScan {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : C.block = "while.body.i104") :
    WalkLocal C s = ScanCount s "%ee.011.i" "%cond.i" C.inner := by
  simp [WalkLocal, h]

/-- `WalkLocal` at the string scan's landing block. -/
theorem WalkLocal.stringScanLanded {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (h : C.block = "land.rhs.i103") :
    WalkLocal C s = ScanLanded s "while.body.i104" "%inc.i105" "%cond.i" C.inner := by
  simp [WalkLocal, h]

/-- `WalkLocal` at the escape scan's latch. -/
theorem WalkLocal.escape {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : C.block = "while.body76.i") :
    WalkLocal C s = ScanCount s "%s2.020.i" "%cond.i" C.inner := by
  simp [WalkLocal, h]

/-- `WalkLocal` at the escape scan's landing block. -/
theorem WalkLocal.escapeLanded {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : C.block = "land.rhs71.i") :
    WalkLocal C s = ScanLanded s "while.body76.i" "%inc77.i" "%cond.i" C.inner := by
  simp [WalkLocal, h]

/-- `WalkLocal` at the extra-token scan's latch. -/
theorem WalkLocal.extraToken {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : C.block = "while.body462.i") :
    WalkLocal C s = ScanCount s "%q.0.i246" "%cond350.i" C.inner := by
  simp [WalkLocal, h]

/-- `WalkLocal` at the extra-token scan's landing block. -/
theorem WalkLocal.extraTokenLanded {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} (h : C.block = "land.rhs457.i") :
    WalkLocal C s = ScanLanded s "while.body462.i" "%inc463.i" "%cond350.i" C.inner := by
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
    (hi : lookupName s.env phi = some (.int 64 (BitVec.ofNat 64 i)))
    (hc : lookupName s.env cond = some (.int 64 (BitVec.ofNat 64 c)))
    (hinner : C.inner = c - i) (hlt : i + 1 < c) (hcw : c < 2 ^ 64)
    (hland : ∀ (e : State), e.pre = some src →
      lookupName e.env inc = some (.int 64 (BitVec.ofNat 64 (i + 1))) →
      lookupName e.env cond = some (.int 64 (BitVec.ofNat 64 c)) →
      WalkLocal (G := G) { C with block := land, inner := c - (i + 1) } e) :
    ∃ (e : State),
      step calls stage2Body s = .jump e ∧
      WalkInv G { C with block := land, inner := c - (i + 1) } e ∧
      walkMeasure G { C with block := land, inner := c - (i + 1) } < walkMeasure G C ∧
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
  refine ⟨e, hstep, ?_, ?_, ?_⟩
  · refine
      { pc_eq := rfl
        blockIndex := ?_
        k_le := hInv.k_le
        records_le := hInv.records_le
        evlen_eq := hInv.evlen_eq
        alen_le_sum := hInv.alen_le_sum
        alen_ge := hInv.alen_ge
        spans_order := hInv.spans_order
        spans_inside := hInv.spans_inside
        pending_at := hInv.pending_at
        eoff_le := hInv.eoff_le
        inner_cap := by
          have hcap : c - i ≤ G.n + 5 := by
            simpa only [walkInnerCap] using hinner ▸ hInv.inner_cap
          show c - (i + 1) ≤ G.n + 5
          omega
        owning := ?_
        blockLocal := ?_ }
    · rw [hk]; exact hInv.blockIndex
    · dsimp only [e]; exact hInv.owning
    · exact hland e rfl hinc hcond
  · dsimp only [walkMeasure]
    rw [hinner]
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
      WalkInv G C' e ∧ C'.block = "land.rhs.i" ∧
      walkMeasure G C' < walkMeasure G C ∧
      ∀ k, runFuel calls (1 + k) stage2Body s = runFuel calls k stage2Body e := by
  obtain ⟨i, c, hinner, -, hcw, hi, hc⟩ := WalkInv.whitespace hInv hblock
  have hnext : i + 1 < c := hguard i c hinner hi hc
  obtain ⟨e, -, hinv, hmeas, hrun⟩ :=
    scan_step G C s i c "while.body370.i" "land.rhs.i" "%ee.0.i238" "%inc371.i"
      "%exitcond.not" "%cond350.i" "if.end372.i" hInv hblock scanWhitespace_find
      (by decide) (by decide) (by decide) (by decide) (by decide) hi hc hinner hnext hcw
      (by
        intro e hpre hinc hcond
        rw [WalkLocal.whitespaceLanded rfl]
        exact ⟨i + 1, c, rfl, hnext, hcw, hpre, hinc, hcond⟩)
  exact ⟨e, _, hinv, rfl, hmeas, hrun⟩

/-- **The string scan's back edge**, `while.body.i104 → land.rhs.i103`.  The
counter `%ee.011.i` goes from `i` to `i + 1` and the test `%inc.i105 = %cond.i`
is clear because `i + 1 < c`; the latch's exit arm is `cleanup474.i` and it is not
the edge taken.  The measure keeps its outer factor and loses one from the inner
component. -/
theorem string_scan {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "while.body.i104")
    (hguard : ScanGuard s "%ee.011.i" "%cond.i" C.inner) :
    ∃ (e : State) (C' : WalkCarry G),
      WalkInv G C' e ∧ C'.block = "land.rhs.i103" ∧
      walkMeasure G C' < walkMeasure G C ∧
      ∀ k, runFuel calls (1 + k) stage2Body s = runFuel calls k stage2Body e := by
  obtain ⟨i, c, hinner, -, hcw, hi, hc⟩ := WalkInv.stringScan hInv hblock
  have hnext : i + 1 < c := hguard i c hinner hi hc
  obtain ⟨e, -, hinv, hmeas, hrun⟩ :=
    scan_step G C s i c "while.body.i104" "land.rhs.i103" "%ee.011.i" "%inc.i105"
      "%exitcond.not.i" "%cond.i" "cleanup474.i" hInv hblock scanString_find
      (by decide) (by decide) (by decide) (by decide) (by decide) hi hc hinner hnext hcw
      (by
        intro e hpre hinc hcond
        rw [WalkLocal.stringScanLanded rfl]
        exact ⟨i + 1, c, rfl, hnext, hcw, hpre, hinc, hcond⟩)
  exact ⟨e, _, hinv, rfl, hmeas, hrun⟩

/-- **The escape scan's back edge**, `while.body76.i → land.rhs71.i`.  The counter
`%s2.020.i` goes from `i` to `i + 1` and the test `%inc77.i = %cond.i` is clear
because `i + 1 < c`; the measure keeps its outer factor and loses one from the
inner component. -/
theorem escape_scan {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "while.body76.i")
    (hguard : ScanGuard s "%s2.020.i" "%cond.i" C.inner) :
    ∃ (e : State) (C' : WalkCarry G),
      WalkInv G C' e ∧ C'.block = "land.rhs71.i" ∧
      walkMeasure G C' < walkMeasure G C ∧
      ∀ k, runFuel calls (1 + k) stage2Body s = runFuel calls k stage2Body e := by
  obtain ⟨i, c, hinner, -, hcw, hi, hc⟩ := WalkInv.escape hInv hblock
  have hnext : i + 1 < c := hguard i c hinner hi hc
  obtain ⟨e, -, hinv, hmeas, hrun⟩ :=
    scan_step G C s i c "while.body76.i" "land.rhs71.i" "%s2.020.i" "%inc77.i"
      "%exitcond24.not.i" "%cond.i" "while.end78.i" hInv hblock scanEscape_find
      (by decide) (by decide) (by decide) (by decide) (by decide) hi hc hinner hnext hcw
      (by
        intro e hpre hinc hcond
        rw [WalkLocal.escapeLanded rfl]
        exact ⟨i + 1, c, rfl, hnext, hcw, hpre, hinc, hcond⟩)
  exact ⟨e, _, hinv, rfl, hmeas, hrun⟩

/-- **The extra-token scan's back edge**, `while.body462.i → land.rhs457.i`.  The
counter `%q.0.i246` goes from `i` to `i + 1` and the test `%inc463.i =
%cond350.i` is clear because `i + 1 < c`; the measure keeps its outer factor and
loses one from the inner component. -/
theorem extraToken_scan {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "while.body462.i")
    (hguard : ScanGuard s "%q.0.i246" "%cond350.i" C.inner) :
    ∃ (e : State) (C' : WalkCarry G),
      WalkInv G C' e ∧ C'.block = "land.rhs457.i" ∧
      walkMeasure G C' < walkMeasure G C ∧
      ∀ k, runFuel calls (1 + k) stage2Body s = runFuel calls k stage2Body e := by
  obtain ⟨i, c, hinner, -, hcw, hi, hc⟩ := WalkInv.extraToken hInv hblock
  have hnext : i + 1 < c := hguard i c hinner hi hc
  obtain ⟨e, -, hinv, hmeas, hrun⟩ :=
    scan_step G C s i c "while.body462.i" "land.rhs457.i" "%q.0.i246" "%inc463.i"
      "%exitcond298.not" "%cond350.i" "if.end473.i" hInv hblock scanExtraToken_find
      (by decide) (by decide) (by decide) (by decide) (by decide) hi hc hinner hnext hcw
      (by
        intro e hpre hinc hcond
        rw [WalkLocal.extraTokenLanded rfl]
        exact ⟨i + 1, c, rfl, hnext, hcw, hpre, hinc, hcond⟩)
  exact ⟨e, _, hinv, rfl, hmeas, hrun⟩

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

/-- **The report's clauses, read off the invariant.**  The seven numbers and the
region claim `Stage2Run` records from `arenaGe` onwards: both cursors and their
two-sided growth bounds, the last reserve's slack, the refusal offset, and the
region at `alen + 64`.  It is the exit's whole content: the wrapper's three
stores and `stage2Run_boundary` turn it into `Γ_stage2`'s post. -/
theorem WalkInv.report {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (h : WalkInv G C s) :
    G.ndst0 ≤ C.alen ∧
      C.alen ≤ G.ndst0 + G.n ∧
      G.nev0 ≤ C.evlen ∧
      C.evlen ≤ G.nev0 + stage2RecordBytes * G.n ∧
      C.alen + stage2ArenaReserve ≤ G.dstcap ∧
      C.eoff ≤ G.n ∧
      Owns (inRegions [(G.dst, C.alen + stage2ArenaReserve), (G.ev, C.evlen)]) m0 s.mem := by
  have hle : C.alen ≤ G.ndst0 + G.n := h.alen_le
  have hev : C.evlen ≤ G.nev0 + stage2RecordBytes * G.n := h.evlen_le
  have hroom : G.ndst0 + G.n + stage2ArenaReserve ≤ G.dstcap := G.arenaRoom
  have hevcap : C.evlen ≤ G.evcap := le_trans hev G.evRoom
  have hsep := stage2Regions_arena_ev G.separate
  refine ⟨h.alen_ge, hle, ?_, hev, by omega, h.eoff_le, ?_⟩
  · rw [h.evlen_eq]
    exact Nat.le_add_right _ _
  · refine owns_reserve_of_owns_extent h.owning G.arenaCap (by omega) ?_
    rcases hsep with hsep | hsep
    · left; omega
    · right; omega

/-! ### The entry loop's first obligation

The entry loop's arm is the dispatch: `while.body.i` reads the entry stream and the
document, the switch tree classifies the byte, and one of the arms assembles a
record or refuses.  The edge that closes the iteration is proved (`walkBack_step`:
the merge at `cleanup478.i`, its two `phi`s, the exit test, and the inner reset),
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
ABI objects.

The invariant's region claim is `Owns (inRegions [(dst, alen), (ev, evlen)])`, and
`Owns`'s unchanged half is a statement about *every address outside* the region.
So a store outside it contradicts the claim unless the bytes happen to agree —
`owns_writeBytes_outside` below is that argument — and only a store whose whole
range is inside it is admitted (`owns_writeBytes_inside`).  The loop's first store
is to `%c.i + 32`, which is outside both extents in the emitted pipeline, where the
cursor record is an object of its own; nothing in `WalkGeom` places it inside them,
so the invariant as stated is not preserved one step into the loop.  The seed's
region claim fails the same way, one step earlier: `entry`'s own stores
(`%s + 56/72/80`, `%z + 0/8/16/24/40/48/56`, `%c.i + 0/8/16/24/1112`, and the
`memset` over `%c.i + 40`) are to the same unstaged objects, which is why
`WalkSeedState` takes the claim as a hypothesis rather than deriving it.

**The obligation, then, is a statement change and not an arm**: the walk's region
must name the appended objects it writes — `%c.i`, `%ctype.i`, `%cst.i`,
`%t352.i`, `%s`, `%z`, `%e` (`%d.i` is staged but the pinned body neither reads
nor writes it) — at the extents the body writes, with their presence staged
(`HasBytes` at each extent) and their separation from the arena and event
extents, and the record's `stage2Frame` must name them too, because the post's
`Owns` is a claim about the whole run.  `Γ_stage2at`'s precondition says nothing
about those objects (`stage2Args` appends them and `Γ_stage2at.pre` constrains
none), so neither the loop's invariant nor the report's region clause can be
derived at that record for a placement that puts any of them outside the frame —
and no clause places them inside it.  The obligation precedes the dispatch's three
named obligations: the nesting state is first *written* at `if.end24.i`
(`%ctype.i`/`%cst.i`), the arena's reserve is first *checked* at `if.end256.i`
(`%add.i82` against `%acap`, with the cursor updated at `if.else285.i`), and the
event reserve is first checked at `if.end.i.i`, all of them around stores to the
same unstaged objects.

Two structural facts about the edge are worth recording beside it.  First, the
header's leading `phi` rebinds `%k.0.i249` inside the block, not on the edge, so
the outer arm is the two-block step `cleanup478.i → while.body.i → NodeBlock21`:
the carry's `k` advances only when the header's own instructions run, which is why
the strict decrease is `walkMeasure_step`'s (the header's block) and not the
edge's.  Second, the header's `phi` takes `%k.2.i` from `cleanup478.i`, whose
incoming value is the dispatch's, so the edge's guard is that merge's own — the
carry does not record it, and the dispatch to `while.body.i` needs the ten
predecessors' register facts at `cleanup478.i`'s two `phi`s.

Behind the region claim sits the second clause the dispatch needs and the
invariant does not carry: **the nesting state**.  `WalkInv` names no register for
the depth `%sp.i.0248`, the container-type stack `%ctype.i`, the container-state
stack `%cst.i`, or their bound, so `if.end24.i`'s `sp > 519` refusal, its
`ctype[sp]`/`cst[sp]` stores and its `%inc33.i` advance have nothing to preserve,
and a refusal arm's `%idxprom.i` offset is a register the carry's `eoff` is not
tied to.  The clause is the same shape as the cap's: the depth is seeded at zero
by the loop head's `phi` (`%sp.i.0248` takes the constant `0` from
`while.body.i.lr.ph`), the stacks are the two ABI objects `%ctype.i`/`%cst.i` with
`entry`'s `memset` over the cursor record's `%c.i + 40` beside them, the bound is
the `MAXD` check the arm reads (`%cmp19.i`'s `519`), and the depth moves by one per
push and per pop.  It belongs where its value is produced — the loop head's `phi`
and `entry`'s initialisation — and, like the cap, it is a clause and not an arm. -/

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
exactly what makes it not.  This is why the loop's first store is the entry
loop's first obligation rather than a detail of its arms. -/
theorem owns_writeBytes_outside {P : Nat → Prop} {mem m : Mem} {w : Nat} {v : List UInt8}
    (hw : ¬ P w) (hdiff : readByte (writeBytes m w v) w ≠ readByte mem w) :
    ¬ Owns P mem (writeBytes m w v) := by
  intro h
  exact hdiff (h.unchanged w hw)

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
        records_le := hInv.records_le
        evlen_eq := hInv.evlen_eq
        alen_le_sum := hInv.alen_le_sum
        alen_ge := hInv.alen_ge
        spans_order := hInv.spans_order
        spans_inside := hInv.spans_inside
        pending_at := hInv.pending_at
        eoff_le := hInv.eoff_le
        inner_cap := Nat.le_refl _
        owning := by dsimp only [e, State.bind]; exact hInv.owning
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

/-- info: 'LeanLLVM.Refinement.forInc_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.forInc_find

/-- info: 'LeanLLVM.Refinement.forInc_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.forInc_step

/-- info: 'LeanLLVM.Refinement.WalkGeom.nep_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkGeom.nep_le

/-- info: 'LeanLLVM.Refinement.WalkInv.forInc' depends on axioms: [propext] -/
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


end LeanLLVM.Refinement
