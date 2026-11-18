import LeanLLVM.Refinement.JsonStage2WalkScopeGeom

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.BlockEval

/-! ### The record in flight

The walk appends at most one event record per entry, and every append happens
inside one iteration: `k` moves only at the header's pass (`while.body.i →
NodeBlock21`), while the three records are written before the merge — the string
record at `if.then328.i`, the scalar value's at `if.then425.i`, and the tag stores
that land on `cleanup478.i`.  So between an append and the next pass the trace is
one record ahead of `C.k`, and after the pass the entries and the records agree
again.

`WalkInv.events_le` names that difference by the *block* rather than by a second
counter: `walkEmitC` is one on the stretch from an append's target to the pass and
zero before the append, and the clause reads `length ≤ k + walkEmitC block`.  The
stretch is the only place the allowance is one, and the pass is the only edge out
of it — the one link that moves `k` — which is what makes the clause preserved
rather than assumed.  It is also why the clause cannot be stated with a uniform
allowance: the append at `if.then425.i` must re-establish it at the same `k`, and
a uniform `k + 1` would need `length ≤ k` at the append's own block, which no
uniform form supplies.

`walkEmitC` is a `Nat` because both bounds it feeds (`events_le` and `evlen_le`)
are arithmetic; its values are one and zero, and `walkEmitC_le_one` is that fact. -/

/-- The blocks the walk reaches only after the current entry's record is appended:
the three appends' targets and everything downstream of them until the header's
pass.  `while.body.i` is in the stretch and `NodeBlock21` — the pass's target —
is not, because the pass is the step that advances `k`.

The three appends are `if.then328.i`'s string record (landing on `if.then330.i` or
`if.else334.i`), `if.then425.i`'s scalar value (landing on `if.then447.i`), and the
tag stores of `if.then.i.i`, `out_reserve.exit.i.i`, `if.then.i.i50` and
`out_reserve.exit.i.i60` (landing on `cleanup478.i`).  **A new step that appends a
record and lands outside this set is a defect**: the block-keyed allowance would
then claim one record fewer than the trace holds, and `events_le` — not this
definition — is where it would surface, far from the emit.  Conversely a block
listed here that no append reaches only weakens the clause by one record; the
check `walkEmitC_condbr_edges`/`walkEmitC_br_edges` holds the set to the body. -/
def walkEmitBlocks : List String :=
  ["if.then330.i", "if.else334.i",
   "if.then447.i", "land.rhs457.i", "NodeBlock105", "NodeBlock103",
   "LeafBlock96", "LeafBlock99", "LeafBlock101", "while.body462.i",
   "if.then467.i", "if.end473.i", "cleanup474.i", "cleanup478.i", "while.body.i",
   "if.then485.i", "if.then488.i", "if.end490.i", "if.then492.i", "s2_walk.exit",
   "if.then", "if.end"]

/-- One on the stretch above, zero before the current entry's append. -/
def walkEmitC (b : String) : Nat := if walkEmitBlocks.contains b then 1 else 0

/-- The record in flight is one record. -/
theorem walkEmitC_le_one (b : String) : walkEmitC b ≤ 1 := by
  unfold walkEmitC
  split <;> omega

/-- The allowance at a block inside the stretch. -/
theorem walkEmitC_of_contains {b : String} (h : walkEmitBlocks.contains b = true) :
    walkEmitC b = 1 := by
  unfold walkEmitC
  rw [h]
  rfl

/-- The allowance at a block before the current entry's append. -/
theorem walkEmitC_of_not_contains {b : String} (h : walkEmitBlocks.contains b = false) :
    walkEmitC b = 0 := by
  unfold walkEmitC
  rw [h]
  rfl

/-- A block found by name carries that name. -/
theorem findBlockList_name {bs : List Block} {n : String} {b : Block}
    (h : findBlockList bs n = some b) : b.name = n := by
  induction bs with
  | nil => simp [findBlockList] at h
  | cons b' rest ih =>
      simp only [findBlockList] at h
      split at h
      · cases h; assumption
      · exact ih h

/-- **The phase never tightens along a branch of the walk's body.**  Every block
that branches hands both its arms the allowance its own block has: no arm leaves
the stretch for the append-free region.  Checked over the body's own block list —
the check is closed, so it is a computation rather than an enumeration by hand. -/
theorem walkEmitC_condbr_edges :
    (stage2Body.blocks.all (fun B =>
      match B.term with
      | Term.condbr _ tl fl =>
          walkEmitC B.name ≤ walkEmitC tl ∧ walkEmitC B.name ≤ walkEmitC fl
      | _ => True)) = true := by decide

/-- **The phase never tightens along a jump either**, with one edge: the header's
pass `while.body.i → NodeBlock21`.  That edge leaves the stretch because it is the
step that advances `k` (`whileBody_step`), and it is not one of the links this
lemma is used by — a link at `while.body.i` takes it as `WalkLink.whileBody`. -/
theorem walkEmitC_br_edges :
    ((stage2Body.blocks.filter (fun B => B.name != "while.body.i")).all (fun B =>
      match B.term with
      | Term.br t => walkEmitC B.name ≤ walkEmitC t
      | _ => True)) = true := by decide

/-- The branch case of the phase check, at the block a link's own `findBlock`
names. -/
theorem walkEmitC_condbr_le {B : Block} (hB : B ∈ stage2Body.blocks)
    {d : Operand} {tl fl : String} (hterm : B.term = Term.condbr d tl fl) :
    walkEmitC B.name ≤ walkEmitC tl ∧ walkEmitC B.name ≤ walkEmitC fl := by
  have hall := List.all_eq_true.mp walkEmitC_condbr_edges
  have h := hall B hB
  rw [hterm] at h
  exact of_decide_eq_true h

/-- The jump case of the phase check, away from the header's pass. -/
theorem walkEmitC_br_le {B : Block} (hB : B ∈ stage2Body.blocks)
    (hne : B.name ≠ "while.body.i") {t : String} (hterm : B.term = Term.br t) :
    walkEmitC B.name ≤ walkEmitC t := by
  have hall := List.all_eq_true.mp walkEmitC_br_edges
  have hmem : B ∈ stage2Body.blocks.filter (fun B => B.name != "while.body.i") := by
    rw [List.mem_filter]
    exact ⟨hB, by simpa using hne⟩
  have h := hall B hmem
  rw [hterm] at h
  exact of_decide_eq_true h

/-- **The walk's invariant.**  Everything the loop carries, at the block it is at,
and the memory it has written.  This is the predicate every arm must preserve;
`forInc_step` proves the literal comparison's arm does, and the scans' visits are
the guard-free rounds of `JsonStage2WalkRevolutionScanRound`. -/
structure WalkInv {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) : Prop where
  /-- The run is at the carried block. -/
  pc_eq : s.pc = C.block
  /-- The entry index is the phi the outer loop reads. -/
  blockIndex : lookupName s.env "%k.0.i249" = some (.int 64 (BitVec.ofNat 64 C.k))
  /-- **The header's increment at the carried index.**  `%inc.i` is `%k.0.i249 + 1`
  (the header's first instruction), read at `blockIndex`'s value.  Nothing else
  rebinds it, and the back edge (`walkBack_step`) advances neither `C.k` nor
  `%inc.i`, so `%inc.i = C.k + 1` holds at every block — `while.body.i` included —
  and needs no side condition on `C.block`.  The one rebind is the header's own pass
  (`whileBody_step`), which moves the register and the carry together (`%k.2.i`
  becomes the carry and `%inc.i` its successor), so the clause is produced there
  and preserved everywhere else.  A block-keyed alternative — `ofNat C.k` at
  `while.body.i` — is refuted: the back edge leaves the carry unadvanced while the
  register already holds `C.k + 1`, so such a clause would demand
  `C.k = %k.2.i`, against `walkBack_step`'s carry and `whileBody_step`'s
  `hkge : C.k < %k.2.i`. -/
  inc_reg : lookupName s.env "%inc.i" = some (.int 64 (BitVec.ofNat 64 (C.k + 1)))
  /-- **The entry's index at the carried index.**  `%idxprom.i` is `%7`'s zero
  extension (`while.body.i`'s second instruction), so its word is this entry's
  position in the entry stream, `entryPos G C.k`.  Only the header binds it — every
  other read of the name is a store of its value — so the clause is `inc_reg`'s
  shape: produced by the header's own pass from the lane it just read (`reg7`),
  preserved by every other block, and keyed on the carried index because the lane
  is.  `WalkIter.regarr` carries the token's *address* `G.b + entryPos G C.k`, not
  the index word, which is what makes this a clause beside it rather than a
  consequence of it. -/
  idx_reg : lookupName s.env "%idxprom.i" =
    some (.int 64 (BitVec.ofNat 64 (entryPos G C.k)))
  /-- The index has not passed the stream. -/
  k_le : C.k ≤ G.nep
  /-- **At most one record per entry consumed**, plus the record in flight.  The
  walk appends one record per emitting entry, before the merge's `phi` advances
  the index, so the trace is the entries consumed plus the record of the current
  entry when that record has been appended and `k` has not moved
  (`walkEmitC`).  The block names which side of the append the state is on; it is
  not a second counter, because the stretch is a region of the dispatch and the
  pass out of it is the only step that changes `k`.

  Two facts follow and are what the consumers read: at a block before the append
  the bound is the entries consumed (`WalkInv.events_le_of_tight`), and the width
  sum is inside the entry count's room at every state (`WalkInv.evlen_le`, through
  the trace's bound by the entry count, `events_nep`). -/
  events_le : C.events.length ≤ C.k + walkEmitC C.block
  /-- **The trace is at most the entry count.**  One record per entry, and the
  entry stream has `G.nep` entries, so no state's trace can be longer — the
  in-flight record included.  This is the clause the room bound reads
  (`WalkInv.evlen_le`): the width sum is at most thirteen times the trace's length,
  and `G.nep ≤ G.n`.  It is stated beside `events_le` rather than derived from it
  because the block-keyed clause's allowance turns `k ≤ nep` into `k + 1 ≤ nep + 1`,
  which is one record too many.

  Its only production that is not the source's own is the append's, which needs
  `C.k < G.nep` — an entry still to be accounted for — and that is the same
  hypothesis the append's room reads. -/
  events_nep : C.events.length ≤ G.nep
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
  /-- **Every extent ends at or before the arena cursor.**  The extents are the
  bodies the arena has decoded, so their ends are the cursor's own progress: a
  body's window is reserved at the cursor before it is decoded, and the cursor
  never moves back.  This is what lets a block that writes inside a reserved
  window (`z_arena_reserve.exit`) place the write inside `walkWide`'s arena entry
  at the carried cursor, which is `(G.dst, C.alen)`. -/
  spans_end : ∀ r ∈ C.spans, r.1 + r.2 ≤ C.alen
  /-- The record in flight reserves the arena at or below the cursor, inside the
  document: at most one record is being assembled, and its reservation is an offset
  the cursor has already reached.  The inequality rather than the equality is what
  the walking carry needs: the cursor that has decoded a body does not move back,
  and the record in flight is the one the next reservation is made for. -/
  pending_at : ∀ p off len, C.pending = some (p, off, len) → off ≤ C.alen ∧ p < G.n
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
  `alen` (`z_arena_reserve.exit`) must keep the record's offset at or below the new
  cursor (`pending_at`) and re-prove the bound, and the merge that carries the next
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
  /-- **The register's depth is inside the written mark.**  A pop lowers `sp` but
  not the mark, so the depth is at most the mark and a push at `sp` stores at an
  index the carried map already covers. -/
  sp_le_wlen : C.sp ≤ C.wlen
  /-- **The written mark is inside the two stacks' staged extent**, so a push at
  the mark writes inside the object the caller staged. -/
  wlen_cap : C.wlen ≤ stage2StackExtent
  /-- **The type stack's contents are the carried map.**  The bytes at
  `%ctype.i`'s first `wlen` indices are `tyMap`, so the byte a block reads at
  `sp - 1` is the value the carry kept after the depth that produced it moved.
  `walkStack_valuePos` is what turns the two clauses into the helper's answer. -/
  tyBytes : WalkStackBytes s.mem C.stage.ctype C.tyMap C.wlen
  /-- **The state stack's contents are the carried map.**  The state twin of
  `tyBytes`; `if.end24.i` advances both maps and the class-D stores rewrite one
  entry of `stMap` where they write. -/
  stBytes : WalkStackBytes s.mem C.stage.cst C.stMap C.wlen
  /-- **The pointer registers the dispatch's blocks read.**  `while.body.i` reads
  `%3`, `%5` and `%k11.i`, and `if.end24.i` indexes `%ctype.i`/`%cst.i` and reads
  the log's hash word through `%hash1.i.i`; a block's `denoteCode` needs those
  bindings before its edge can be a step, and the invariant names them at the
  addresses the staging fixed (`WalkPtrs`). -/
  ptrs : WalkPtrs G C s.env
  /-- **The static carrier.**  The thirty-six registers `walkStaticRegs` names
  hold the values the staging fixes for them; the seed produces them and every
  dispatch block's run leaves them alone (`WalkRegs.cons`, `WalkRegs.cells_of`).
  `%nep`, `%c.i`, `%z`, `%xp` and `%nxp` are among them: the entry binds the five
  and no block of the walk rebinds any, and so are `%4`, `%t352.i` and `%e`, the
  three the last entry's merge and tails read, and `%s`, `%ndst`, `%nev` and
  `%err`, whose values `WalkFinalEnv` reads off this clause. -/
  regs : WalkRegs G C s.env
  /-- **The per-iteration carrier.**  `%7`, `%8` and `%arrayidx10.i` are the lane,
  the document byte and the token's position address at the carried index; the
  header's step is what produces them (`whileBody_step`), and every other block's
  run leaves them alone (`WalkIter.bind`, `WalkIter.cells_of`). -/
  iter : WalkIter G C.k s.env
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
  /-- **The log's arena cursor is at most the carried arena cursor.**  `z_arena_reserve`
  reads the word at `%z + 48` (`%alen`) and adds the body's length and the
  decoder's slack to it; `if.end256.i` compares that sum against `%z + 56`.  The
  word is read as an *inequality* rather than an equality because the carry
  reserves a body's window before the block that writes the word back:
  `z_arena_reserve.exit` decodes the body at the carried cursor and the reserve is
  the carry's (`spans_end`), while `if.else285.i` is where `%alen` receives the
  decoded prefix -- `old + %32` -- which is at most the window's end.  Between the
  two the memory's word is short of the carry by the part of the window the
  decoder has not filled, and `logArena_le` below recovers the bound a caller
  needs.

  The word is also bounded *below*, at the arena's staged cursor: it starts there
  (the initialisation stores `%ndst`'s word at `%z + 48`) and the one block that
  writes it writes a sum with the old word as an addend, so it never goes back
  below the staging.  That is the clause the post's `ndst0 ≤ ndst'` reads.

  The two numbers are the *same* number seen at different moments, not two
  cursors: `arenaAppend` advances the carried cursor by the decoded length as it
  writes the body, and the block that writes the word back (`if.else285.i`) stores
  the same decoded length.  So the inequality is a lag inside one iteration — the
  carry is ahead of the memory between the append and the write-back — and at the
  loop head, after the write-back, the two are equal.  That equality is what the
  exit's slot copy needs, and it is the dispatch's to produce. -/
  log_alen : ∃ a, G.ndst0 ≤ a ∧ a ≤ C.alen ∧
    readBytes s.mem (C.stage.z + 48) 8 = some (wordBytes 8 a)
  /-- **The log's arena capacity is the staged one** (the word at `%z + 56`,
  `%acap`).  With `log_alen` this is the clause `if.end256.i` needs: the word the
  reserve compares against is `dstcap`, not an unconstrained memory cell. -/
  log_acap : readBytes s.mem (C.stage.z + 56) 8 = some (wordBytes 8 G.dstcap)
  /-- **The log's base word is the event stream's base.**  The word at `%z + 0` is
  `%ev`: the initialisation stores the staging's `%ev` there (`entry`'s `%z ← %ev`
  in `JsonStage2IR`), and no block of the walk writes it — the dispatched blocks
  write `%z + 8`, the sixteen-byte `memset` at `%z + 24` and `%z + 48` only.
  `if.then328.i` loads it as `%33` and `if.end256.i` adds it to the arena's offset,
  so it is the word an event record is written through.

  It is a clause rather than a frame lemma for `log_hash`'s reason: `%z`'s first
  eight bytes lie *inside* `walkWideAt`'s log entry, where the frame is silent, and
  `WalkInv.owned` gives the object's presence rather than the value it holds. -/
  log_base : readBytes s.mem C.stage.z 8 = some (wordBytes 8 G.ev)
  /-- **The log's arena-base word is the arena's base.**  The word at `%z + 40` is
  `%ar`, which `z_arena_reserve.exit` reads and `if.end256.i`'s `%sub260.i`
  subtracts from the cursor: the initialisation stores the staging's `%dst` there
  (`entry`'s `%ar ← %dst` in `JsonStage2IR`) and no block of the walk writes it, so
  the word names the arena the offsets are measured in.

  A clause for `log_base`'s reason: the bytes at `%z + 40` are inside the log
  entry's extent (`stage2LogExtent` is sixty-four), so `WalkInv.frame` says nothing
  about them. -/
  log_dst : readBytes s.mem (C.stage.z + 40) 8 = some (wordBytes 8 G.dst)
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
  /-- **The root-done slot is present.**  `entry` allocates `%root_done.i` at
  `G.next0 + 8` and its second store writes the slot's four bytes, so the slot is
  present from the seed on; the only later writes through it are the depth-zero
  arm of `s2_after_value`, which stores a four-byte flag inside the same slot, and
  no block of the walk writes it.

  It is a clause of its own because `owned` deliberately omits the four `alloca`
  slots: `%ei.i`, `%xj.i` and `%outn.i` are not present at the loop head, so a
  presence claim over the four would be false there.  The root slot is the one
  that is present, and the finalisation's root-done test (`if.end490.i`) reads it,
  so its presence is what makes that read a word rather than an unreadable cell. -/
  root_slot : HasBytes s.mem (G.next0 + 8) 4
  /-- **The allocator cursor has passed the initialisation's four slots.**  `entry`
  allocates `%ei.i`, `%root_done.i`, `%xj.i` and `%outn.i` at `G.next0`, advancing
  the cursor by `8 + 4 + 8 + 8`.  The model's allocator is monotone (`Semantics`,
  `.alloca` always advances), so every later cursor is at least there.  The clause
  is what makes the cursor's interval (`walkWideAt`'s second entry) contain the
  four slots, and it is why a frame at that interval is a claim about the run's
  own stack writes rather than about an empty interval.

  It is an inequality rather than the equality `s.next = G.next0 + 28`, because a
  helper call moves the cursor past it: the equality would need the run's whole
  call accounting, and the inequality is what the interval's coverage reads. -/
  next_ge : G.next0 + stage2BootstrapExtent ≤ s.next
  /-- **Silence outside the region the walk writes, at its own cursor**
  (`walkWideAt`): the arena's decoded prefix and the event stream's prefix at the
  carried cursors, the seven appended objects, `%d.i`, and the interval from
  `G.next0` to the run's cursor `s.next`.

  The list is the run's whole touched extent and it grows with the cursors: a
  store into the arena or the event stream at the new cursor is inside it, and a
  helper call's allocation extends the interval.  The stack part is the *interval*
  rather than the fixed five slots for the reason `stage2BootstrapExtent` records:
  the allocator advances, so a second allocating call writes above
  `G.next0 + 36`, where the fixed list stops.  At the seed the interval is the
  four slots (`next_ge`), and its bytes are the ones the initialisation's own
  stores leave inside it.

  The bytes below `G.next0` are the staged objects' and `walkPresent`'s; the
  document's and the entry stream's reads (`doc_outside`, `entry_outside`) use the
  watermark to place them below the interval. -/
  frame : UnchangedOutside m0 s.mem (walkWideAt G C (s.next - G.next0))
  /-- The block-local facts the measure is read from. -/
  blockLocal : WalkLocal C s

namespace WalkInv

variable {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}

/-- **The loop head's guard, read off the block-local clause.**  `WalkLocal` states
`C.k < G.nep` at `NodeBlock21`, so a state at the loop head has an entry left.  This is
the clause `WalkInv.k_le` does not give (it bounds the index by the count, not below it),
and it is what turns the consumer's `¬ (C.k + 1 < G.nep)` into the last entry's index
`C.k + 1 = G.nep`. -/
theorem head_lt (h : WalkInv G C s) (hhead : C.block = "NodeBlock21") : C.k < G.nep := by
  have hb : WalkLocal C s := h.blockLocal
  unfold WalkLocal at hb
  rw [hhead] at hb
  repeat rw [ite_eq_right (by decide)] at hb
  exact hb

/- The pin is sited with its theorem rather than in the instrument section: an
in-module `#print axioms` walks the elaborated proof, while an imported
declaration is read from the array its own module exported, and `WalkInv` is one
whose two readings differ — `[propext]` here, `[]` when imported.  A pin in a
later module would assert the weaker of the two. -/
/-- info: 'LeanLLVM.Refinement.WalkInv.head_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkInv.head_lt

/-- The arena's bound, from the carried extents: this is
`Stage2SpansInside`'s content and `arenaLe_of_spans`'s conclusion, so the report's
`alen ≤ ndst0 + n` is downstream of the carry rather than assumed. -/
theorem alen_le (h : WalkInv G C s) : C.alen ≤ G.ndst0 + G.n :=
  arenaLe_of_spans h.spans_order h.spans_inside h.alen_le_sum

/-- **The trace's bound before the current entry's append.**  `events_le`'s
allowance is zero at such a block, so the trace is the entries consumed. -/
theorem events_le_of_tight (h : WalkInv G C s) (hb : walkEmitC C.block = 0) :
    C.events.length ≤ C.k := by
  have h' := h.events_le
  rw [hb] at h'
  simpa using h'

/-- **The trace's bound inside the stretch**, one record past the entries
consumed. -/
theorem events_le_of_emit (h : WalkInv G C s) (hb : walkEmitC C.block = 1) :
    C.events.length ≤ C.k + 1 := by
  have h' := h.events_le
  rw [hb] at h'
  simpa using h'

/-- The event cursor's bound, from the trace's widths, one record per entry and the
entry count: the width sum is at most thirteen times the trace's length, the length
is at most the entry count (`events_nep`), and the count is at most the document's
bytes. -/
theorem evlen_le (h : WalkInv G C s) :
    C.evlen ≤ G.nev0 + stage2RecordBytes * G.n := by
  have hsum := EventRecord.sum_encodedSize_le C.events
  have hEv := h.events_nep
  have hmul : stage2RecordBytes * C.events.length ≤ stage2RecordBytes * G.n :=
    Nat.mul_le_mul_left _ (le_trans hEv G.nep_le)
  rw [h.evlen_eq]
  omega

/-- **The arena word a block loads is at most the carried cursor.**  `log_alen`
states the log's `%alen` word as some `a ≤ C.alen`; a block that loads the word as a
`BitVec` (`A`, at the `natToBytes` its load produces) therefore gets
`A.toNat ≤ C.alen`.  The two readings agree below `2^64` --- `A.toNat` is already
below it and `natToBytes` keeps only the residue --- so the inequality is the word's
own content and not a fresh hypothesis. -/
theorem logArena_le (h : WalkInv G C s) {A : BitVec 64}
    (hA : readBytes s.mem (C.stage.z + 48) 8 = some (natToBytes A.toNat 8)) :
    A.toNat ≤ C.alen := by
  obtain ⟨a, -, ha, hr⟩ := h.log_alen
  have heq : natToBytes A.toNat 8 = natToBytes a 8 :=
    Option.some.inj (hA.symm.trans hr)
  have hb : bytesToNat (natToBytes A.toNat 8) = bytesToNat (natToBytes a 8) := by
    rw [heq]
  rw [natToBytes_toNat, natToBytes_toNat] at hb
  have hAm : A.toNat % 256 ^ 8 = A.toNat := by
    rw [show (256 : Nat) ^ 8 = 2 ^ 64 from by decide, Nat.mod_eq_of_lt A.isLt]
  have ham : a % 256 ^ 8 ≤ a := Nat.mod_le _ _
  omega

/-- The block-local facts at the latch: the invariant implies them, and the arm's
lemma takes them explicitly so its `WalkInv` hypothesis is not unpacked twice. -/
theorem forInc {h : WalkInv G C s} (hblock : C.block = "for.inc.i.i") :
    ∃ i c : Nat, c - i ≤ C.inner ∧ i < c ∧ c < 2 ^ 64 ∧
      lookupName s.env "%i.029.i.i" = some (.int 64 (BitVec.ofNat 64 i)) ∧
      lookupName s.env "%cond.i.i" = some (.int 64 (BitVec.ofNat 64 c)) := by
  simpa [WalkLocal, hblock] using h.blockLocal

end WalkInv

/-! ### The carried maps across a step

The four stack clauses are carried by every step, and each step's evidence is one
of six shapes: the memory is unchanged; the write is inside a staged object other
than the two stacks; the write is inside one of the thirteen ABI objects; the
write is inside the body's four `alloca`s; the write is inside `%d.i`; or the
write is a stack store itself.  The lemmas below state the first five as
`WalkStackBytes` transfers; the sixth is `WalkStackBytes.pushAt`/`storeAt` and the
block's own index, at the site.

Every one of them reads the staging's separation and the watermark, so no site
re-derives the arrangement of the objects. -/

/-- Two distinct members of a `DisjointRegions` list are separated. -/
theorem disjointRegions_pair_of_mem {rs : List (Nat × Nat)} (h : DisjointRegions rs)
    {r t : Nat × Nat} (hr : r ∈ rs) (ht : t ∈ rs) (hne : r ≠ t) :
    r.1 + r.2 ≤ t.1 ∨ t.1 + t.2 ≤ r.1 := by
  unfold DisjointRegions at h
  induction rs with
  | nil => simp at hr
  | cons x xs ih =>
      rw [List.pairwise_cons] at h
      obtain ⟨hx, hxs⟩ := h
      rcases List.mem_cons.mp hr with hrx | hrx
      · subst hrx
        rcases List.mem_cons.mp ht with htx | htx
        · subst htx; exact absurd rfl hne
        · exact hx t htx
      · rcases List.mem_cons.mp ht with htx | htx
        · subst htx; exact Or.symm (hx r hrx)
        · exact ih hxs hrx htx

/-- The seven staged objects are separated from each other. -/
theorem WalkStage.writes_separate {m0 : Mem} {G : WalkGeom m0} (S : WalkStage G) :
    DisjointRegions (stage2StagedWrites S.c S.ctype S.cst S.tok S.s S.z S.e) := by
  have h := S.separate
  unfold DisjointRegions at h
  rw [stage2StagedRegions, stage2WalkRegions, List.append_assoc] at h
  exact (List.pairwise_append.mp (List.pairwise_append.mp h).2.1).1

/-- The walk's region list is separated from itself, with the caller's two count
slots set aside. -/
theorem WalkStage.walk_separate {m0 : Mem} {G : WalkGeom m0} (S : WalkStage G) :
    DisjointRegions (stage2WalkRegions G.b G.n G.ep G.nep G.xp G.nxp G.dst G.ndst0
      G.ev G.evcap G.ndst G.nev G.err S.c S.ctype S.cst S.tok S.s S.z S.e) := by
  have h := S.separate
  unfold DisjointRegions at h
  rw [stage2StagedRegions] at h
  exact (List.pairwise_append.mp h).1


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
  wlen := 0
  tyMap := fun _ => 0
  stMap := fun _ => 0
  stage := S

/-- The state the initialisation hands the loop: the header's block after its two
`phi`s selected the first entry position and the empty nesting, the two cursors
as the caller staged them, and the log's seven fields as the staging fixed them
(the initialisation's `entry` stores `z->ev.b`, `z->len`, `z->cap`, the zeroed
hash state, and `z->ar`, `z->alen`, `z->acap`).
The four parameters the string path's links read — the two staging records
`%c.i` and `%z`, and `%xp` with `%nxp` — are the entry's, and no layer of the
run rebinds them, so they are clauses here beside `WalkRegs`, whose list names
them.  The last clause is the header's own zero extension: the seed's state is
the header's *first pass*, so `%idxprom.i` already holds the first entry's
position, which is `WalkInv.idx_reg`'s clause at index zero. -/
def WalkSeedState {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State) : Prop :=
  s.pc = "NodeBlock21" ∧
    lookupName s.env "%k.0.i249" = some (.int 64 (BitVec.ofNat 64 0)) ∧
    lookupName s.env "%sp.i.0248" = some (.int 32 (BitVec.ofNat 32 0)) ∧
    lookupName s.env "%inc.i" = some (.int 64 (BitVec.ofNat 64 (0 + 1))) ∧
    WalkPtrs G (walkSeed G S) s.env ∧
    WalkRegs G (walkSeed G S) s.env ∧
    WalkIter G (walkSeed G S).k s.env ∧
    lookupName s.env "%c.i" = some (.ptr S.c) ∧
    lookupName s.env "%z" = some (.ptr S.z) ∧
    lookupName s.env "%xp" = some (.ptr G.xp) ∧
    lookupName s.env "%nxp" = some (.int 64 (BitVec.ofNat 64 G.nxp)) ∧
    readBytes s.mem (S.z + 32) 4 = some (natToBytes 0 4) ∧
    (∀ r ∈ walkStaged G (walkSeed G S), HasBytes s.mem r.1 r.2) ∧
    HasBytes s.mem (G.next0 + 8) 4 ∧
    G.next0 + stage2BootstrapExtent ≤ s.next ∧
    UnchangedOutside m0 s.mem (walkWideAt G (walkSeed G S) (s.next - G.next0)) ∧
    readBytes s.mem (S.z + 8) 8 = some (wordBytes 8 G.nev0) ∧
    readBytes s.mem (S.z + 16) 8 = some (wordBytes 8 G.evcap) ∧
    readBytes s.mem (S.z + 48) 8 = some (wordBytes 8 G.ndst0) ∧
    readBytes s.mem (S.z + 56) 8 = some (wordBytes 8 G.dstcap) ∧
    readBytes s.mem S.z 8 = some (wordBytes 8 G.ev) ∧
    readBytes s.mem (S.z + 40) 8 = some (wordBytes 8 G.dst) ∧
    lookupName s.env "%idxprom.i" = some (.int 64 (BitVec.ofNat 64 (entryPos G 0)))

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
    (h : WalkSeedState G S s) (hpos : 0 < G.nep) : WalkInv G (walkSeed G S) s := by
  obtain ⟨hpc, hk, hsp, hinc0, hptrs, hregs, hiter, -, -, -, -, hhash, hown, hroot,
    hge, hframe, hlen, hcap, halen, hacap, hbase, hdst, hidx0⟩ := h
  refine
    { pc_eq := hpc
      blockIndex := hk
      inc_reg := hinc0
      idx_reg := hidx0
      k_le := Nat.zero_le _
      events_le := by
        show (0 : Nat) ≤ 0 + walkEmitC "NodeBlock21"
        have h : walkEmitC "NodeBlock21" = 0 := walkEmitC_of_not_contains (by decide)
        omega
      events_nep := Nat.zero_le _
      evlen_eq := by simp [walkSeed]
      evBytes := rfl
      alen_le_sum := by simp [walkSeed]
      alen_ge := Nat.le_refl _
      spans_order := by simp [walkSeed]
      spans_end := by simp [walkSeed]
      spans_inside := by simp [walkSeed]
      pending_at := ?_
      pending_cursor := ?_
      pending_len := ?_
      eoff_le := Nat.zero_le _
      inner_cap := walkSeed_inner_cap G S
      depth_cap := walkSeed_depth_cap G S
      depth_reg := hsp
      sp_le_wlen := Nat.zero_le _
      wlen_cap := Nat.zero_le _
      tyBytes := WalkStackBytes.empty
      stBytes := WalkStackBytes.empty
      ptrs := hptrs
      regs := hregs
      iter := hiter
      log_hash := hhash
      log_len := hlen
      log_cap := hcap
      log_alen := ⟨G.ndst0, Nat.le_refl _, Nat.le_refl _, halen⟩
      log_acap := hacap
      log_base := hbase
      log_dst := hdst
      owned := hown
      root_slot := hroot
      next_ge := hge
      frame := hframe
      blockLocal := ?_ }
  · intro p off len hp
    simp [walkSeed] at hp
  · intro p off len hp
    simp [walkSeed] at hp
  · intro p off len hp
    simp [walkSeed] at hp
  · simp [WalkLocal, walkSeed]
    exact hpos

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

end LeanLLVM.Refinement
