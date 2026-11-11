/-
The stage-2 unit's record, `Γ_stage2`.

`kernel/json/stage2.h` declares one entry point, `leanllvm_json_stage2`, and
`kernel/json/stage2.c` is its body: `s2_walk`'s per-entry dispatch over the entry
stream, one scope stack of container type and state per depth, the string bodies
decoded through the escape unit's entry point, and the event stream and first
error offset written into the caller's buffers.  This module states the record
that entry point satisfies — the seventh callee of `JsonPipelineIR.censusSymbols`
and the one the pipeline's tail is pinned at.  It states the record only: the
body is not in this tree, so `stage2_satisfies` (C96) is not here either, and
nothing below claims a refinement it cannot exhibit.

The register of names matters here, because both a unit and the pipeline carry
records about the same buffers:

* `Γ_stage2` is the *unit's* record, at `stage2.h:90-95`'s thirteen arguments:
  `b, n, ep, nep, xp, nxp, dst, dstcap, ndst, ev, evcap, nev, err`.  The argument
  types are the ones `JsonPipelineIR`'s `pipelineAbi` already checks every call
  site against (`JsonPipelineIR.lean:1090-1092`: `.int 64` return, the thirteen
  argument types `[.ptr, .int 64, .ptr, .int 64, .ptr, .int 64, .ptr, .int 64,
  .ptr, .ptr, .int 64, .ptr, .ptr]`), so the pattern below and the census are the
  same ABI read twice;
* `Γ_pipeline_units` (`JsonPipelineContract.lean`) is the assembled pipeline's
  boundary record, whose post's clauses about `dst`, `ndst`, `ev`, `nev` and
  `err` are facts about the memory a *stage-2 run* leaves.  It is what
  `PipelineBodyFacts.exit` consumes, and why the tail is stated at an arbitrary
  slot until this record exists: no arbitrary record implies them.  The
  docstrings in `JsonPipelineRefine.lean` and `PipelineBodyFacts.lean` call that
  deferral "deferred, not missing"; this module is the record that ends it.

`Sigma_pipeline` (the pipeline's specification, `JsonPipelineSpec.lean`) is *not*
this record's post.  `Γ_stage2` says what the run leaves at the caller's staging:
a verdict word, the two cursors it owns, the arena and event prefixes, the
refusal slot, and the frame.  It says nothing about JSON: whether the verdict,
the record stream and the offset are the reference parser's is `Sigma_pipeline`'s
claim, and the gap between the two is named there and in `EventStreamRel`
(C95).  A semantic clause here would be a second, silently divergent
specification of one stream.

# The ABI, clause by clause

The caller stages every buffer and no modelled run allocates (`stage2.h:11-24`).
That paragraph is the whole of the pre's shape: `dst` with capacity `dstcap` and
cursor `*ndst`, `ev` with capacity `evcap` and cursor `*nev`, both append-only, so
a record's arena offset is an offset into `dst` and every cursor movement is
reported back.  The measured walk grew both buffers by reallocation
(`s2port.h`'s `ZOut`); here that growth is the caller's promise, and a reserve
that would exceed a capacity is `__builtin_trap()` (`stage2.c`'s
`z_arena_reserve`, `out_reserve`) — a loud failure on a violated promise, never a
behaviour the record models, and never the refusal channel, which is a *parse*
refusal (`stage2.h:21-24`).

## The precondition

* **the argument shape** — `stage2.h:90-95`, the thirteen slots in order;
* **the document** `b .. b+n-1` — `stage2.h:56`: `readBytes mem b n = some bs`,
  which is also how `bs.length = n` enters the statement — **and its readable
  tail**: `HasBytes mem (b + n) 32`.  The tail is the decoder's own read-past.
  The walk hands each escaped body to `leanllvm_json_escape_expand`, whose record
  requires thirty-two readable bytes past its body
  (`Γ_escape_expand.pre`'s `HasBytes mem (b + n) 32`, `JsonEscapeSteps.lean`),
  and a body's last byte is at most the document's last, so the document carries
  that tail.  The walk's own scans need no more: every `b[q]` it reads has
  `q < n`, and the number path's eight-byte load is guarded by `i + 8 ≤ n`
  inside the token (`num_d8_el1`).  The clause is the *input window* and it is
  not free — see the derivation note below;
* **the document fits its 32-bit entry positions** — `stage2.h:56-58` and `:91`:
  the entry stream's positions are `uint32_t` values, so a document longer than
  `2 ^ 32` bytes has positions no entry can name; the plain-string record also
  carries `p + 1` in the low 63 bits of its span field (`stage2.h:71-73`), so the
  document end is inside that field as well.  The pipeline's staging carries the
  stronger `64 * pipelineBlocks n + 63 < 2 ^ 32` (`pipelineStaging`), so this
  clause is met at the pipeline's call site;
* **the entry stream** — `stage2.h:56-58`: `ep` with count `nep` holds the entry
  positions in document order, one 32-bit word each, so
  `readLanes32 mem ep nep = some ent` (the `JsonEntryIR` reader the pipeline's
  post also uses) and two content clauses the walk's own reads need:
  `ent.Pairwise (· < ·)` (document order, and distinct — two entries at one
  position do not exist) and `∀ q ∈ ent, q < n` (the walk reads `b[q]`, the
  closing quote's index and the first-whitespace scan, all inside the document).
  These are *safety* clauses, not a description of the stream: a caller whose
  entry stream held a position outside the document, or two positions out of
  order, would drive reads outside the region it staged and a `close - p - 1`
  that underflows.  The number token is **not** bounded here: the conversion
  reads at most 768 significant digits and records the rest in one sticky bit, so
  a token's length is the document's and not a clause of the record;
* **the escape-position list** — `stage2.h:58-60`: `xp` with count `nxp`, read by
  the decoder through `4 * nxp` bytes, so `HasBytes mem xp (4 * nxp)`.  A
  document with no escapes passes `nxp = 0`, which this admits (`4 * 0 = 0`).
  **The list's contents are deliberately not stated here.**  What the decoder
  needs of a list is that its entries inside a body's window are that body's
  escape positions (`Γ_escape_expand.pre`'s
  `ps.map (fun q => q - pos0) = escapePositionsFrom body st`); the walk selects
  the entries inside `[pos0, pos0 + len)` and passes them rebased, so that
  correspondence is established *at the call site* from the list the caller
  staged, not restated as this record's promise about the document;
* **the arena** — `stage2.h:13-24` and `:49-52`: `HasBytes mem dst dstcap`, and
  the reserve the decoder reaches: a body of `len` bytes reserves
  `alen + len + US_SLACK` before writing (`stage2.c`'s
  `z_arena_reserve(z, len + US_SLACK)`, `US_SLACK = 64` at the measured
  `US_EMIT4=1`), and the decoded bytes of all bodies are at most the document's,
  so the single promise that covers every call is
  `ndst0 + n + 64 ≤ dstcap` — the same number `pipelineStaging` states (C126);
* **the event stream** — `stage2.h:13-24` and `:68-75`, with `stage2.c`'s
  `out_reserve(&z->ev, 13)` and `z->ev.len += 13`: presence at the caller's
  capacity, `HasBytes mem ev evcap`, and the written-buffer promise at the
  encoding's worst case, `nev0 + 13 * n ≤ evcap` — at most one record per input
  byte and at most thirteen bytes per record (a key/string record's tag, four
  length bytes and eight span-or-arena bytes).  **This is the clause
  `pipelineStaging` already carries**, stated here at the same numbers because it
  is this unit's own boundary: the pipeline's copy is read off its staging, and
  the unit's copy is where the trap it avoids is described;
* **the two cursors** — `stage2.h:13-16`: `readBytes mem ndst 8 = some (wordBytes
  8 ndst0)` and the same at `nev` for `nev0`: the walk reads both in and reports
  both back;
* **the refusal slot** — `stage2.h:60-61`: `*err` is the first error offset on
  refusal and is not written on acceptance, so the caller stages eight bytes,
  `HasBytes mem err 8`.  It is written only through `if (!r) *err = e.off;`
  (`stage2.c:948`), and it is a real caller object (`pipeline.h` names `*err`),
  not the wrap around the document;
* **the staged objects are separate** — `DisjointRegions` over
  `stage2Regions`: the document, the entry stream, the escape list, the arena's
  reserve, the event stream's capacity and the three slots.  A run that wrote the
  arena over its own entry stream would satisfy every byte claim while destroying
  the caller's staging, so the separation is part of the pre rather than a hope
  about the body.

# The post

The clauses are the ones the pipeline's post and the tail consume, and nothing
else:

* **the verdict is the ABI's word** — `stage2.h:76-77` and `stage2.c`'s
  `return r ? 1 : 0`: `verdict = 0 ∨ verdict = 1`.  This is the clause
  `stage2_verdict_bounded` below reads, which is why it is a conjunct of the
  record and not a companion hypothesis;
* **the two cursors this unit owns**, reported back —
  `readBytes m ndst 8 = some (wordBytes 8 ndst')` and the same at `nev`.  The
  pipeline's post names four cursors: these two are stage 2's, and `nk`/`nxp`
  are the loop's (they are not this ABI's arguments), so they are absent here
  rather than restated as facts this run cannot have.  The cursors only append
  (`stage2.h:15-16`), so `ndst0 ≤ ndst'` and `nev0 ≤ nev'`; and the growth is the
  encoding's: `ndst' ≤ ndst0 + n` (a decoded body is never longer than its
  bytes, so the arena's growth is at most the document's) and
  `nev' ≤ nev0 + 13 * n` (at most one record per entry, thirteen bytes each, and
  at most one entry per input byte — the pre's `ent.Pairwise (· < ·)` and
  `∀ q ∈ ent, q < n` give `ent.length ≤ n`).  `ndst' + 64 ≤ dstcap` is the
  reserve's own consequence: the last reserve check leaves sixty-four bytes past
  the appended extent;
* **the prefixes at the boundary** — the pipeline's post reads
  `readBytes m dst ndst'` and `readBytes m ev nev'`, so this record says both are
  readable and names them `arena`/`evs`.  Their *contents* are the encoder's, and
  relating them to the parser's tokens is `EventStreamRel`'s job (C95), not this
  record's;
* **the refusal word, written exactly on refusal and unchanged on acceptance** —
  `stage2.h:60-61`: on refusal `∃ e, e ≤ n ∧ readBytes m err 8 = some (wordBytes
  8 e)`; the bound `e ≤ n` is `s2_walk`'s own — every `od_fail`/`err_set` offset
  is an entry position `p`, a position `t.pos + ei` with `ei ≤ t.end - t.pos ≤
  ip`, or `n` itself for the end-of-stream rules (`unterminated`, `unclosed
  container`, `no value`).  On acceptance the slot is **not written**, so
  `readBytes m err 8 = readBytes mem err 8`: the refusal channel is the only
  writer, and a caller that reads `*err` after an acceptance reads what it
  staged;
* **the frame, as a region claim** — `Owns (stage2Frame dst ndst' ev nev' ndst
  nev err) mem m`, from `LeanLLVM/FramePredicate.lean`.  The frame vocabulary is
  used here rather than a region list because this is exactly the defect class it
  exists for: `Owns` is a structure whose presence field is over the *same*
  predicate as its unchanged field, so a post cannot name the reserve and leave
  its presence out, and an extent narrower than the writes is refuted at the byte
  the run wrote (`narrowExtent_refuted`, `not_owns_of_changed_outside`).  The
  record's siblings carried the list form; this one states `Owns` and *derives*
  the list form for its consumer below (`stage2Post_unchangedOutside`), so there
  is one object and a projection rather than two regions that can drift.  The
  region is the run's whole touched extent, reserve included:
  `(dst, ndst' + 64)` for the decoder's slack, `(ev, nev')`, and the three slots
  (`ndst`, `nev`, `err`).  `b`, `ep` and `xp` are absent from the region, which
  is the statement that **the unit does not modify its inputs** — the clause
  every other record carries and the one a caller would notice first if it moved.

`.ub` is refused by the `match` (`False` at `.ub`), as every record in this tree
does; a void return or a non-`i64` return is outside the shape the ABI pins, and
`stage2Boundary` says so by its `v = .int 64 verdict` conjunct.

# What the pre does not promise, and why

* **a capacity that a record's numbers exceed** — outside the domain: the caller
  that under-reserves reaches the trap, and the record says so rather than
  describing it (`stage2.h:13-24`);
* **the escape list's correspondence to the document** — the escape unit's post
  (`escapePositionsPost`) is where the list's contents are stated; this record
  promises the bytes are there and the decoder's clause is established at the
  call site.  Stating it here would make the record *unmeetable at its own call
  site* — neither `pipelineStaging` nor the pipeline's post pins the list's
  contents — which is a defect in the other direction;
* **any JSON question** — acceptance, the record stream's meaning, and the
  offset's relation to a refusal constructor are `Sigma_pipeline`'s and
  `EventStreamRel`'s.  This record's verdict is two-valued and nothing more.

# The budget

`stage2Budget` names the walk's own fuel term over the arguments it can see: one
allowance per entry (the switch arm and the record write), one per document byte
(the gap and body scans, whose intervals partition the document, so the sum of
the per-entry scans is at most `n`), one per escape position (the expander's
`(nps + 1) * decodeIterCost` terms, which are counted per position, not per
byte), and the initialisation and finalisation blocks.  The memory parameter is
not read, for `escapeExpandBudget`'s recorded reason: a budget that read the
memory would have to agree with the record's own `readBytes` witnesses about
bytes the run itself writes.  The constants are *allowances* — each covers the
per-stage factor it names, with `decodeIterCost n = 16 + (n / 64 + 2)`
(`JsonEscapeDecodeRun.lean:154`) as the largest factor summed over bodies — and
the inequality `runFuel … ≤ stage2Budget` is C96's to prove at them; a factor
that turns out too small is a number in this term, not a clause of the record.

# What the pin is, and what it is not

`pipeline_satisfies_of_units` takes the tail bundle at an arbitrary record `Γ2`.
Substituting `Γ_stage2` for that parameter is this module's
`pipeline_satisfies_at_stage2`, and it needs nothing new: `PipelineBodyFacts`'s
fields are all `pipelineBody` facts (`pipelineBodyFacts_of_record` shows the
parameter is phantom in them), and the one clause the bundle used to take as a
hypothesis — the verdict's range — is now proved from this record's own post
(`stage2_verdict_bounded`), which is what `pipelineUnits_at_stage2` records.  So
**the pin does not remove `hbody`**, and it cannot: `hbody` supplies the loop
instance, the seed and the tail, which are proofs about `pipelineBody`'s own
three tail blocks and about the loop induction, none of which is a fact the
stage-2 record states.  What the pin does remove is `PipelineUnits`'s
`stage2_verdict_bounded` hypothesis; what it does not supply is the stage-2
selection `CallSatisfies s2 Γ_stage2 stage2Sym`, because that needs
`stage2Body`/`stage2Calls` and a `stage2_satisfies` instance (C96), and neither
is in this tree.

## What a pipeline call site derives, and what it does not

Four of the pre's five groups are consequences of the pipeline's own staging, by
projection: `HasBytes` and the two capacities are `pipelineStaging`'s clauses at
the same numbers (including `nev0 + 13 * n ≤ evcap`, verbatim), the document
window and `n ≤ 2 ^ 32` follow from its `64 * pipelineBlocks n + 63 < 2 ^ 32`, the
cursor slots from its two reads, and `DisjointRegions` from its
`pipelineRegions`/`DisjointRegions` once the stage-2 extents are seen to be
sub-extents (`ep`'s lanes inside `64 * blocks` by `S.k ≤ 64 * S.i`, and
`nxp ≤ xpExtent = xn0 + 64 * blocks + 8` by `S.xn ≤ S.xn0 + 64 * S.i`).

**The document's read-past tail is now staged.**  `Γ_stage2.pre` needs
`HasBytes mem (b + n) stage2ReadTail`, and `pipelineStaging` states
`HasBytes mem (base + 64 * pipelineBlocks bs.length) 32`: the padded window is a
prefix of the tail's extent, so the clause is the staging's own read at
`base + n`.  The `#guard` below is the arithmetic that made it a clause — a
sixty-four-byte document stages one block, and the decoder's read-past reaches
`b + 94`, which the window alone does not cover — not a gap the record leaves.

**The entry stream is carried, with both bounds.**  `Γ_stage2.pre` needs
`readLanes32 mem ep nep = some ent` with `ent` strictly increasing and inside the
document.  The loop's invariant carries the read at `S.k` lanes, the order and the
*block* bound `∀ q ∈ S.ent, q < 64 * S.i`
(`PipelineBodyFacts.pipelineLoopInv`), and the staging pins the count slot to the
empty stream, so the read is the emitters' appended part and nothing below it.
The document bound `∀ q ∈ S.ent, q < S.n.toNat` is the arms' — it is
`streamDocBound_append`, from the last block's entry word — and `pipelineLoopExit`
carries it beside the block bound, so the tail's derivation of this call's pre
reads both off the exit state it is handed rather than assuming either.  Dropping
the clause instead would make the record false of a caller whose entry stream
named a byte outside the document it staged, which is the defect the clause
exists to exclude.
-/
import LeanLLVM.FramePredicate
import LeanLLVM.Refinement.PipelineBodyFacts

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)
open LeanLLVM.Refinement.JsonEntrySteps (readBytes_writeBytes_frame)

/-! ### The walk's own numbers, named where the record uses them -/

/-- The decoder's slack past the arena cursor: `stage2.c`'s `US_SLACK` (line 52),
sixty-four bytes at the measured `US_EMIT4=1`, which `stage2.h:49-52` states as
part of the capacity promise. -/
def stage2ArenaReserve : Nat := 64

/-- One event record's widest encoding (`stage2.h:68-75`): a tag byte, four
length bytes and eight span-or-arena bytes for a key or a string
(`stage2.c:837-841`); a number's nine and a structural byte's one are narrower. -/
def stage2RecordBytes : Nat := 13

/-- The document fits its 32-bit entry positions (`stage2.h:56-58`, `:91`). -/
def stage2MaxDocument : Nat := 2 ^ 32

/-- The readable tail past the document.  The walk hands each escaped string body
to `leanllvm_json_escape_expand`, whose record reads thirty-two bytes past its
body (`Γ_escape_expand.pre`'s `HasBytes mem (b + n) 32`, `JsonEscapeSteps.lean`),
and a body's last byte is at most the document's — so the document must carry
thirty-two readable bytes past its end.  The walk's own scans need no more: every
`b[q]` it reads has `q < n`, and the number path's eight-byte load is guarded by
`i + 8 ≤ n` within the token (`num_d8_el1`). -/
def stage2ReadTail : Nat := 32

/-! ### The staged extents and the frame -/

/-- The objects the caller stages, each at the extent the run's reads or writes
reach: the document *with its read-past tail*, the entry and escape streams, the
arena's reserve from its cursor, the event stream's capacity, and the three
slots.  The document's entry is `n + stage2ReadTail` because the decoder reads
past the last body, and a write into those bytes would destroy the decoder's own
input — the separation is what excludes it.  The arena's entry is
`ndst0 + n + 64` rather than `dstcap`, so the region is the one the caller's
promise is about; the event stream's is its capacity, which is the staging
`pipelineStaging` already separates. -/
def stage2Regions (b n ep nep xp nxp dst ndst0 ev evcap ndst nev err : Nat) :
    List (Nat × Nat) :=
  [(b, n + stage2ReadTail), (ep, 4 * nep), (xp, 4 * nxp),
   (dst, ndst0 + n + stage2ArenaReserve), (ev, evcap), (ndst, 8), (nev, 8), (err, 8)]

/-- The extents the run writes, as a region list: the arena's decoded prefix plus
the decoder's slack, the event stream's prefix, and the three slots it stores
back.  The document (its read-past tail included), the entry stream and the
escape list are absent, which is the statement that the unit does not modify its
inputs — the clause a caller would notice first if it moved. -/
def stage2Writes (dst ndst' ev nev' ndst nev err : Nat) : List (Nat × Nat) :=
  [(dst, ndst' + stage2ArenaReserve), (ndst, 8), (ev, nev'), (nev, 8), (err, 8)]

/-- The frame as a predicate on locations, so the post's memory clause can be the
region claim `Owns` rather than a list beside a second list.

**Its scope is the ABI's five write regions, and that is a fact about the wrapper,
not about the flattened walk.**  `stage2Run_boundary` produces it from the walk's
report at the extents the wrapper itself stores; the flattened body additionally
writes the seven appended objects, whose frame is `stage2WalkFrame`.  So this
frame is **not** the frame of `stage2Body`: an `Owns` at it does not survive the
loop's first store (`%c.i + 32`).  Naming the seven here is blocked, not
overlooked: the post is at the ABI's thirteen arguments, and the seven are the
body's own parameters, so `stage2Boundary` has no witness for them and
`Γ_stage2.pre` cannot stage them (`stage2StagedPre` states that staging at the
adapter, `Γ_stage2at`).  `satisfies_calls_stage2` therefore yields the walk's
record only under a caller-supplied staging of the seven, and the pipeline's
staging does not name them — the separation of its own count slots from the walk's
scratch is the missing clause, and it is one step outside this record. -/
def stage2Frame (dst ndst' ev nev' ndst nev err : Nat) : Nat → Prop :=
  inRegions (stage2Writes dst ndst' ev nev' ndst nev err)

/-! ### The appended objects the walk writes

`stage2.h` declares thirteen slots and the emitted body takes twenty-one: the
flattening appends eight staging objects (`stage2StagingArgs`), and the walk
writes seven of them.  They are the **cursor record** `%c.i` (the five scalar
fields at `+0/8/16/24/32`, the `memset` over `+40` and the `%e` pointer at
`+1112`), the **two container stacks** `%ctype.i`/`%cst.i` (one byte per depth,
bounded by the `MAXD` check's `519`), the **token** `%t352.i` (the position, the
end, the kind and the gap), the **decoder state** `%s` (`%nep`, `%xp`, `%nxp` at
`+56/72/80`), the **log** `%z` (the event pointer, its length and capacity, the
hash, the arena's pointer, cursor and capacity) and the **error record** `%e`
(the refusal offset at `+8`).  `%d.i` is appended too and written by neither the
walk nor the initialisation.

The extents below are the body's own `llvm.lifetime.start` sizes, read off the
pinned AST by the `#guard`s in `JsonStage2IR`.  A frame that stops at
`stage2Writes` omits every one of these objects, so no `Owns` at that frame
survives the loop's first store — `while.body.i`'s write of its advanced index to
`%c.i + 32`.  `stage2WalkFrame` is the frame that names them; `stage2Frame` is its
prefix, which is why the record's post is a projection of the walk's claim and not
a second region that can drift from it. -/

/-- The cursor record `%c.i`. -/
def stage2CursorExtent : Nat := 1192

/-- Each container stack `%ctype.i`/`%cst.i`. -/
def stage2StackExtent : Nat := 520

/-- The token `%t352.i`. -/
def stage2TokenExtent : Nat := 24

/-- The decoder state `%s`. -/
def stage2StateExtent : Nat := 120

/-- The log `%z`. -/
def stage2LogExtent : Nat := 64

/-- The error record `%e`. -/
def stage2ErrorExtent : Nat := 24

/-- The seven appended objects the walk writes, at their extents, in the order
`stage2StagingArgs` receives them. -/
def stage2StagedWrites (c ctype cst tok s z e : Nat) : List (Nat × Nat) :=
  [(c, stage2CursorExtent), (ctype, stage2StackExtent), (cst, stage2StackExtent),
   (tok, stage2TokenExtent), (s, stage2StateExtent), (z, stage2LogExtent),
   (e, stage2ErrorExtent)]

/-- **The walk's whole touched extent**: the ABI's five write regions and the seven
appended objects.  This is the extent the loop's region claim is about. -/
def stage2WalkWrites (dst ndst' ev nev' ndst nev err c ctype cst tok s z e : Nat) :
    List (Nat × Nat) :=
  stage2Writes dst ndst' ev nev' ndst nev err ++
    stage2StagedWrites c ctype cst tok s z e

/-- **The walk's frame**: the region claim's predicate at the run's whole touched
extent.  `stage2Frame` is its prefix (`stage2Writes_subset_walkWrites`).

**Why the seven are in the frame, and why that is the correct statement rather
than a widening that suits a proof.**  The eight appended parameters exist in the
pinned text because the flattening turned structures and arrays into parameters:
in the emitted `s2_walk` they are **stack slots**, and the caller never sees them.
So the ABI's five regions are the caller's objects and the seven are the walk's own
work space.  A frame that names both is **true of the pinned text** — the text
really does store to `%c.i + 32`, `%ctype.i[sp]`, `%z + 8` and the rest — and
**conservative about the source**, where those stores are to a frame the caller
cannot observe either way.  The narrow frame is not "smaller"; it is false of the
text it is stated about. -/
def stage2WalkFrame (dst ndst' ev nev' ndst nev err c ctype cst tok s z e : Nat) :
    Nat → Prop :=
  inRegions (stage2WalkWrites dst ndst' ev nev' ndst nev err c ctype cst tok s z e)

/-- The staged objects of `Γ_stage2at`: the thirteen ABI objects of
`stage2Regions` and the seven appended ones.  Every pair is separate, which is
what makes the walk's writes to the seven miss the arena and the event stream (and
each other), and what keeps the document, the entry stream and the escape list
readable while the walk writes. -/
def stage2WalkRegions (b n ep nep xp nxp dst ndst0 ev evcap ndst nev err
    c ctype cst tok s z e : Nat) : List (Nat × Nat) :=
  stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err ++
    stage2StagedWrites c ctype cst tok s z e

/-- **The staging the flattened body's precondition asks of the appended
objects**: the seven the walk writes are present at their extents, and every
staged object — the thirteen ABI objects and the seven — is separate from every
other.  It is stated at the argument list the record receives, so the numbers are
the record's own; `ndst0` is read from the arena's cursor slot, exactly as
`stage2Pre` reads it. -/
def stage2StagedPre (args : List Value) (mem : Mem) (c ctype cst tok s z e : Nat) : Prop :=
  (∀ r ∈ stage2StagedWrites c ctype cst tok s z e, HasBytes mem r.1 r.2) ∧
  match args with
  | [.ptr b, .int 64 n, .ptr ep, .int 64 nep, .ptr xp, .int 64 nxp, .ptr dst,
     .int 64 _, .ptr ndst, .ptr ev, .int 64 evcap, .ptr nev, .ptr err] =>
      ∃ ndst0, readBytes mem ndst 8 = some (wordBytes 8 ndst0) ∧
        DisjointRegions
          (stage2WalkRegions b n.toNat ep nep.toNat xp nxp.toNat dst ndst0
            ev evcap.toNat ndst nev err c ctype cst tok s z e)
  | _ => False

/-- The ABI frame is a prefix of the walk's. -/
theorem stage2Writes_subset_walkWrites {dst ndst' ev nev' ndst nev err
    c ctype cst tok s z e : Nat} :
    ∀ r ∈ stage2Writes dst ndst' ev nev' ndst nev err,
      r ∈ stage2WalkWrites dst ndst' ev nev' ndst nev err c ctype cst tok s z e :=
  fun _ hr => List.mem_append_left _ hr

/-- **A listed extent is present under the region claim.**  This is the only
projection a region claim admits: presence is monotone in the region, so a listed
interval's bytes are present; the unchanged half is *not* monotone in either
direction, which is exactly why the record's frame had to be widened rather than
projected.  `Owns (stage2WalkFrame …)` does **not** yield
`Owns (stage2Frame …)`: the walk changes the seven appended objects, and those lie
outside the narrow frame's unchanged half. -/
theorem owns_extent_present {mem m : Mem} {rs : List (Nat × Nat)} {r : Nat × Nat}
    (h : Owns (inRegions rs) mem m) (hr : r ∈ rs) : HasBytes m r.1 r.2 :=
  readBytes_of_hasBytes m r.1 r.2 fun k hk =>
    h.present (r.1 + k) ⟨r, hr, Nat.le_add_right _ _, Nat.add_lt_add_left hk _⟩

/-- The seven staged objects' extents are the ones the record names, so a caller
that has the staging has presence at each of them. -/
theorem stage2StagedPre_present {args : List Value} {mem : Mem}
    {c ctype cst tok s z e : Nat} (h : stage2StagedPre args mem c ctype cst tok s z e) :
    HasBytes mem c stage2CursorExtent ∧ HasBytes mem ctype stage2StackExtent ∧
      HasBytes mem cst stage2StackExtent ∧ HasBytes mem tok stage2TokenExtent ∧
      HasBytes mem s stage2StateExtent ∧ HasBytes mem z stage2LogExtent ∧
      HasBytes mem e stage2ErrorExtent := by
  obtain ⟨hpres, -⟩ := h
  have hc : (c, stage2CursorExtent) ∈ stage2StagedWrites c ctype cst tok s z e := by
    simp [stage2StagedWrites]
  have hctype : (ctype, stage2StackExtent) ∈ stage2StagedWrites c ctype cst tok s z e := by
    simp [stage2StagedWrites]
  have hcst : (cst, stage2StackExtent) ∈ stage2StagedWrites c ctype cst tok s z e := by
    simp [stage2StagedWrites]
  have htok : (tok, stage2TokenExtent) ∈ stage2StagedWrites c ctype cst tok s z e := by
    simp [stage2StagedWrites]
  have hst : (s, stage2StateExtent) ∈ stage2StagedWrites c ctype cst tok s z e := by
    simp [stage2StagedWrites]
  have hz : (z, stage2LogExtent) ∈ stage2StagedWrites c ctype cst tok s z e := by
    simp [stage2StagedWrites]
  have he : (e, stage2ErrorExtent) ∈ stage2StagedWrites c ctype cst tok s z e := by
    simp [stage2StagedWrites]
  exact ⟨hpres _ hc, hpres _ hctype, hpres _ hcst, hpres _ htok, hpres _ hst,
    hpres _ hz, hpres _ he⟩

/-! ### The budget -/

/-- One entry's allowance: the switch arm, the event record's thirteen bytes and
the per-body constants of the decoder's call. -/
def stage2EntryAllowance : Nat := 32

/-- One document byte's allowance: the gap and body scans, and the decoder's
`n / 64` per-body term, which one byte's allowance covers sixty-four times over. -/
def stage2ByteAllowance : Nat := 8

/-- One escape position's allowance: the expander's `(nps + 1) * 3` scan and its
`(nps + 1) * decodeIterCost` walk, which are counted per position. -/
def stage2PositionAllowance : Nat := 32

/-- The initialisation, the end-of-stream checks and the wrapper's stores. -/
def stage2FinalisationAllowance : Nat := 32

/-- The walk's fuel, as a term of the arguments the ABI carries: one allowance per
entry, per document byte and per escape position, plus the finalisation blocks.
See the module docstring for why the memory parameter is not read. -/
def stage2Budget (args : List Value) (_mem : Mem) : Nat :=
  match args with
  | [.ptr _, .int 64 n, .ptr _, .int 64 nep, .ptr _, .int 64 nxp, .ptr _, .int 64 _,
     .ptr _, .ptr _, .int 64 _, .ptr _, .ptr _] =>
      stage2EntryAllowance * nep.toNat + stage2ByteAllowance * n.toNat +
        stage2PositionAllowance * nxp.toNat + stage2FinalisationAllowance
  | _ => 0

/-! ### The precondition -/

/-- The caller's staging for the stage-2 unit, at `stage2.h`'s thirteen
arguments.  Every clause is read from a sentence of the header or from the body's
own reads; the module docstring walks them in order. -/
def stage2Pre (args : List Value) (mem : Mem) (_next : Nat) : Prop :=
  ∃ (b n ep nep xp nxp dst dstcap ndst ev evcap nev err : Nat)
    (bs : List UInt8) (ent : List Nat) (ndst0 nev0 : Nat),
    args = [.ptr b, .int 64 (BitVec.ofNat 64 n), .ptr ep,
            .int 64 (BitVec.ofNat 64 nep), .ptr xp, .int 64 (BitVec.ofNat 64 nxp),
            .ptr dst, .int 64 (BitVec.ofNat 64 dstcap), .ptr ndst, .ptr ev,
            .int 64 (BitVec.ofNat 64 evcap), .ptr nev, .ptr err] ∧
    -- the document (`stage2.h:56`)
    readBytes mem b n = some bs ∧
    -- and the readable tail the decoder's read-past needs
    -- (`Γ_escape_expand.pre`, `stage2ReadTail`)
    HasBytes mem (b + n) stage2ReadTail ∧
    -- the entry stream: 32-bit positions, in document order, inside the document
    -- (`stage2.h:56-58`, `:91`)
    readLanes32 mem ep nep = some ent ∧
    ent.Pairwise (· < ·) ∧
    (∀ q ∈ ent, q < n) ∧
    -- the escape-position list's bytes (`stage2.h:58-60`)
    HasBytes mem xp (4 * nxp) ∧
    -- the arena: capacity and the decoder's reserve (`stage2.h:13-24`, `:49-52`)
    HasBytes mem dst dstcap ∧
    ndst0 + n + stage2ArenaReserve ≤ dstcap ∧
    -- the event stream: capacity and write room (`stage2.h:13-24`, `:68-75`)
    HasBytes mem ev evcap ∧
    nev0 + stage2RecordBytes * n ≤ evcap ∧
    -- the two cursors, read in (`stage2.h:13-16`)
    readBytes mem ndst 8 = some (wordBytes 8 ndst0) ∧
    readBytes mem nev 8 = some (wordBytes 8 nev0) ∧
    -- the refusal slot (`stage2.h:60-61`)
    HasBytes mem err 8 ∧
    -- the document's positions are 32-bit (`stage2.h:56-58`, `:71-73`)
    n ≤ stage2MaxDocument ∧
    -- every staged object is a separate region
    DisjointRegions
      (stage2Regions b n ep nep xp nxp dst ndst0 ev evcap ndst nev err)

/-! ### The post -/

/-- The boundary projection of a stage-2 run at a return value: the verdict's
range, the two cursors it owns (as read in and as reported back, with their
growth bounds), the arena and event prefixes, the refusal word's two sides, and
the frame as a region claim.

The semantic content — whether the verdict is the reference parser's, what the
record stream means, which refusal constructor an offset belongs to — is
`Sigma_pipeline`'s and `EventStreamRel`'s, and is deliberately absent.

The two capacities are stated as 64-bit numbers, and the event extent as lying
inside its capacity.  The ABI carries each capacity as an eight-byte word, so a
call site's number is the word's value below `2 ^ 64`; with the reserve clause
this places the arena's write extent inside the arena and the event extent
inside the event stream, which is what a consumer composing this post with the
caller's staging of the two buffers needs.  It also makes the reported extents
below the word's width, the bound `pipelineOutputExtents` reads. -/
def stage2Boundary (args : List Value) (mem m : Mem) (v : Value) : Prop :=
  ∃ (b n ep nep xp nxp dst dstcap ndst ev evcap nev err : Nat)
    (verdict : BitVec 64) (ndst0 nev0 ndst' nev' : Nat) (arena evs : List UInt8),
    args = [.ptr b, .int 64 (BitVec.ofNat 64 n), .ptr ep,
            .int 64 (BitVec.ofNat 64 nep), .ptr xp, .int 64 (BitVec.ofNat 64 nxp),
            .ptr dst, .int 64 (BitVec.ofNat 64 dstcap), .ptr ndst, .ptr ev,
            .int 64 (BitVec.ofNat 64 evcap), .ptr nev, .ptr err] ∧
    -- the return carries the ABI's verdict word and no other value
    v = .int 64 verdict ∧
    -- the ABI's verdict (`stage2.h:76-77`)
    (verdict = 0 ∨ verdict = 1) ∧
    -- the cursors as the caller staged them (`stage2.h:13-16`)
    readBytes mem ndst 8 = some (wordBytes 8 ndst0) ∧
    readBytes mem nev 8 = some (wordBytes 8 nev0) ∧
    -- and as the run reports them back, append-only
    readBytes m ndst 8 = some (wordBytes 8 ndst') ∧
    readBytes m nev 8 = some (wordBytes 8 nev') ∧
    ndst0 ≤ ndst' ∧ ndst' ≤ ndst0 + n ∧
    nev0 ≤ nev' ∧ nev' ≤ nev0 + stage2RecordBytes * n ∧
    -- **The reported extents are below the word's width, and the capacities say
    -- so.**  `ndst'` and `nev'` are what a consumer reads back through the two
    -- eight-byte slots, and a slot word alone leaves its value free modulo
    -- `2 ^ 64`, so a consumer that must name the extents (`pipelineOutputExtents`)
    -- needs each below the width.  The two bounds are stated here, at the clause
    -- that produces them, and through the numbers the run names: the decoder's
    -- reserve and the event extent both lie inside their capacities, and an ABI
    -- capacity argument is a 64-bit word, so `dstcap < 2 ^ 64` gives
    -- `ndst' < 2 ^ 64` by the reserve clause below and `nev' ≤ evcap < 2 ^ 64`
    -- gives the other.  The width is the smaller change: stating `ndst' < 2 ^ 64`
    -- and `nev' < 2 ^ 64` directly would state the consequence twice and leave a
    -- consumer unable to place either write extent inside the staging the call
    -- was made at, while a width of the capacity is what identifies the
    -- capacity — two 64-bit numbers with one word are one number.  Without the
    -- width the record is `2 ^ 64`-periodic in these numbers and the bounds are
    -- not derivable at all.
    dstcap < 2 ^ 64 ∧ evcap < 2 ^ 64 ∧ nev' ≤ evcap ∧
    -- the decoder's reserve is still inside the capacity (`stage2.h:49-52`)
    ndst' + stage2ArenaReserve ≤ dstcap ∧
    -- the prefixes the pipeline's post reads
    readBytes m dst ndst' = some arena ∧
    readBytes m ev nev' = some evs ∧
    -- the refusal word: written exactly on refusal (`stage2.h:60-61`)
    (verdict = 0 →
      ∃ e : Nat, e ≤ n ∧ readBytes m err 8 = some (wordBytes 8 e)) ∧
    -- and unchanged on acceptance, because nothing writes it
    (verdict = 1 → readBytes m err 8 = readBytes mem err 8) ∧
    -- the region the run touched, owned: presence and the frame together
    Owns (stage2Frame dst ndst' ev nev' ndst nev err) mem m

/-- What the stage-2 run leaves at the caller's staging, at the outcome it
produces.  `.ub` is refused by the match, and a return that carries no value or
a value of another shape is outside `stage2Boundary`'s `v = .int 64 verdict`. -/
def stage2Post (args : List Value) (mem : Mem) (_next : Nat) (o : Outcome) : Prop :=
  match o with
  | .ub => False
  | .ret (some v) m => stage2Boundary args mem m v
  | .ret none _ => False

/-! ### The record -/

/-- **The stage-2 unit's boundary record**, `Γ_stage2`: the staging above, the
walk's fuel term, and the boundary projection of the run's outcome.  It is the
record `JsonPipelineIR.pipelineCalls`'s seventh slot is pinned at and the one
`PipelineBodyFacts.exit` consumes. -/
def Γ_stage2 : MemContract where
  budget := stage2Budget
  pre := stage2Pre
  post := stage2Post

/-! ### What the post hands its consumer

The pipeline's post is a region list, so the frame claim is projected to that
form once here rather than restated in the record. -/

/-- **The post's frame, as the list form the pipeline's post speaks.**  A reader
of `Γ_pipeline_units.post` sees `UnchangedOutside`; this is where it comes from. -/
theorem stage2Post_unchangedOutside {dst ndst' ev nev' ndst nev err : Nat}
    {mem m : Mem} (h : Owns (stage2Frame dst ndst' ev nev' ndst nev err) mem m) :
    UnchangedOutside mem m (stage2Writes dst ndst' ev nev' ndst nev err) := by
  rw [unchangedOutside_iff_inRegions]
  exact h.unchanged

/-- **The arena extent is present, from the region claim.**  The presence half of
`Owns` is over the same predicate as the frame, so the decoder's reserve is
present without a second clause (`escapeFrame_owns_reserve`'s move at this
record's frame). -/
theorem stage2Frame_arena_present {dst ndst' ev nev' ndst nev err : Nat}
    {mem m : Mem} (h : Owns (stage2Frame dst ndst' ev nev' ndst nev err) mem m) :
    HasBytes m dst (ndst' + stage2ArenaReserve) :=
  readBytes_of_hasBytes m dst (ndst' + stage2ArenaReserve) fun k hk =>
    h.present (dst + k) ⟨(dst, ndst' + stage2ArenaReserve), List.mem_cons_self ..,
      by omega, by omega⟩

/-- **The event prefix is present, from the region claim.** -/
theorem stage2Frame_event_present {dst ndst' ev nev' ndst nev err : Nat}
    {mem m : Mem} (h : Owns (stage2Frame dst ndst' ev nev' ndst nev err) mem m) :
    HasBytes m ev nev' :=
  readBytes_of_hasBytes m ev nev' fun k hk =>
    h.present (ev + k) ⟨(ev, nev'), by simp [stage2Writes], by omega, by omega⟩

/-- The record refuses `ub`: the post is `False` there, so `Satisfies`'s
completion conjunct and `runFuel_outcome_unique` are what exclude it, exactly as
the sibling records do. -/
theorem stage2Post_ub_false (args : List Value) (mem : Mem) (next : Nat) :
    ¬ Γ_stage2.post args mem next .ub :=
  fun h => h

/-- **The verdict clause, from the record itself.**  `PipelineUnits`'s
`stage2_verdict_bounded` was a hypothesis while the stage-2 record did not exist;
at `Γ_stage2` it is a projection of the post, so the bundle loses that hypothesis
(`pipelineUnits_at_stage2` below). -/
theorem stage2_verdict_bounded :
    ∀ (args : List Value) (mem : Mem) (next : Nat) (v : Value) (m : Mem),
      Γ_stage2.post args mem next (.ret (some v) m) →
      ∃ k : BitVec 64, v = .int 64 k ∧ (k = 0 ∨ k = 1) := by
  intro args mem next v m h
  simp only [Γ_stage2, stage2Post] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, k, _, _, _, _, _, _, _hargs, hveq,
    hv, -⟩ := h
  exact ⟨k, hveq, hv⟩

/-! ### Consequences of the pre

Two facts the pre's own clauses carry, stated once so that a call site does not
re-derive them: the cursors are inside their capacities, and the entry stream's
count is at most the document's — which is what turns the event-stream promise
into a bound at the document. -/

/-- A `readLanes32` read of `k` lanes returns a list of `k` entries. -/
theorem readLanes32_length (m : Mem) (addr k : Nat) :
    ∀ (l : List Nat), readLanes32 m addr k = some l → l.length = k := by
  induction k generalizing addr with
  | zero =>
      intro l h
      simp only [readLanes32, Option.some.injEq] at h
      subst h
      rfl
  | succ k ih =>
      intro l h
      cases hb : readBytes m addr 4 with
      | none => simp [readLanes32, hb] at h
      | some bs =>
          cases hr : readLanes32 m (addr + 4) k with
          | none => simp [readLanes32, hb, hr] at h
          | some rest =>
              have hl : l = bytesToNat bs :: rest := by
                simp only [readLanes32, hb, hr, Option.bind_some, Option.map_some,
                  Option.some.injEq] at h
                exact h.symm
              subst hl
              simp only [List.length_cons]
              rw [ih (addr + 4) rest hr]

/-- **A strictly increasing list of positions below `n` has at most `n` entries**,
stated with a running lower bound so that the induction's tail can start at
`a + 1`: `Pairwise (· < ·)` makes the entries distinct, and the bound carries the
count.  The lower bound's own bound `a ≤ n` is a hypothesis because the empty
list constrains neither. -/
theorem length_add_le_of_pairwise_lt : ∀ {l : List Nat} {a n : Nat},
    l.Pairwise (· < ·) → (∀ q ∈ l, a ≤ q) → (∀ q ∈ l, q < n) → a ≤ n →
    l.length + a ≤ n
  | [], a, n, _, _, _, ha => by simpa using ha
  | q :: t, a, n, hp, hlo, hlt, _ha => by
      obtain ⟨hall, hpt⟩ := List.pairwise_cons.mp hp
      have hqa : a ≤ q := hlo q (List.mem_cons_self ..)
      have hqn : q < n := hlt q (List.mem_cons_self ..)
      have hlo' : ∀ r ∈ t, q + 1 ≤ r := by
        intro r hr
        have h1 : q < r := hall r hr
        omega
      have hlt' : ∀ r ∈ t, r < n := fun r hr => hlt r (List.mem_cons_of_mem q hr)
      have ih : t.length + (q + 1) ≤ n :=
        length_add_le_of_pairwise_lt hpt hlo' hlt' (by omega)
      simp only [List.length_cons]
      omega

/-- The count form the event-stream bound reads: a strictly increasing entry
stream whose positions lie inside the document has no more entries than the
document has bytes. -/
theorem length_le_of_pairwise_lt {l : List Nat} {n : Nat}
    (h : l.Pairwise (· < ·)) (hlt : ∀ q ∈ l, q < n) : l.length ≤ n := by
  have h0 : l.length + 0 ≤ n :=
    length_add_le_of_pairwise_lt h (fun q _ => Nat.zero_le q) hlt (Nat.zero_le n)
  omega

/-- A staged pre puts both cursors inside their capacities — the arena's cursor
because the reserve is, the event cursor because its promise is at the document —
and the entry count at most the document's length. -/
theorem stage2Pre_cursor_bounds {args : List Value} {mem : Mem} {next : Nat}
    (h : stage2Pre args mem next) :
    ∃ (n nep dstcap evcap ndst0 nev0 : Nat),
      ndst0 ≤ dstcap ∧ nev0 ≤ evcap ∧ nep ≤ n := by
  obtain ⟨b, n, ep, nep, xp, nxp, dst, dstcap, ndst, ev, evcap, nev, err, bs, ent,
    ndst0, nev0, _hargs, _hdoc, _htail, hent, horder, hlt, _hxp, _hdstpres,
    hdst, _hevpres, hev, _hndst, _hnev, _herr, _hmax, _hdisj⟩ := h
  refine ⟨n, nep, dstcap, evcap, ndst0, nev0, by omega, by omega, ?_⟩
  rw [← readLanes32_length mem ep nep ent hent]
  exact length_le_of_pairwise_lt horder hlt

/-! ### The record admits a staging

A record that admits nothing is vacuously true, so the pre is inhabited at a
concrete memory.  The empty document keeps the check honest without an encoder:
`readBytes mem b 0 = some []` and `readLanes32 mem ep 0 = some []` are the
zero-length cases, so the memory needs only the arena and the three slots. -/

/-- The witness memory: thirty-two document-tail bytes at zero, sixty-four arena
bytes at thirty-two, then the two cursor slots and the refusal slot, each eight
zero bytes. -/
def stage2Mem : Mem :=
  writeBytes (writeBytes (writeBytes (writeBytes (writeBytes [] 0
    (List.replicate stage2ReadTail 0)) 32 (List.replicate 64 0))
    96 (wordBytes 8 0)) 104 (wordBytes 8 0)) 112 (wordBytes 8 0)

/-- The document's read-past tail is readable at the witness memory. -/
theorem stage2Mem_tail :
    readBytes stage2Mem 0 stage2ReadTail = some (List.replicate stage2ReadTail 0) := by
  unfold stage2Mem
  rw [readBytes_writeBytes_frame _ _ 112 0 stage2ReadTail (by decide),
      readBytes_writeBytes_frame _ _ 104 0 stage2ReadTail (by decide),
      readBytes_writeBytes_frame _ _ 96 0 stage2ReadTail (by decide),
      readBytes_writeBytes_frame _ _ 32 0 stage2ReadTail (by decide)]
  exact readBytes_writeBytes_same [] (bs := List.replicate stage2ReadTail 0) (addr := 0)

/-- The arena bytes are readable at the witness memory. -/
theorem stage2Mem_arena : readBytes stage2Mem 32 64 = some (List.replicate 64 0) := by
  unfold stage2Mem
  rw [readBytes_writeBytes_frame _ _ 112 32 64 (by decide),
      readBytes_writeBytes_frame _ _ 104 32 64 (by decide),
      readBytes_writeBytes_frame _ _ 96 32 64 (by decide)]
  exact readBytes_writeBytes_same _ (bs := List.replicate 64 0) (addr := 32)

/-- The first cursor slot is readable at the witness memory. -/
theorem stage2Mem_ndst : readBytes stage2Mem 96 8 = some (wordBytes 8 0) := by
  unfold stage2Mem
  rw [readBytes_writeBytes_frame _ _ 112 96 8 (by decide),
      readBytes_writeBytes_frame _ _ 104 96 8 (by decide)]
  exact readBytes_writeBytes_same _ (bs := wordBytes 8 0) (addr := 96)

/-- The second cursor slot is readable at the witness memory. -/
theorem stage2Mem_nev : readBytes stage2Mem 104 8 = some (wordBytes 8 0) := by
  unfold stage2Mem
  rw [readBytes_writeBytes_frame _ _ 112 104 8 (by decide)]
  exact readBytes_writeBytes_same _ (bs := wordBytes 8 0) (addr := 104)

/-- The refusal slot is readable at the witness memory. -/
theorem stage2Mem_err : readBytes stage2Mem 112 8 = some (wordBytes 8 0) := by
  unfold stage2Mem
  exact readBytes_writeBytes_same _ (bs := wordBytes 8 0) (addr := 112)

/-- The witness staging's objects are separate. -/
theorem stage2Mem_disjoint :
    DisjointRegions
      (stage2Regions 0 0 0 0 0 0 32 0 0 0 96 104 112) := by
  simp only [DisjointRegions, stage2Regions, stage2ArenaReserve, stage2ReadTail]
  decide

/-- **Control (i): the record's pre is inhabited.**  The empty document at the
witness memory: every extent has the length the pre asks, the entry stream is
empty so its two content clauses are vacuous, the document's read-past tail is
staged, and the cursors read zero.  The record therefore promises something
rather than refusing every caller. -/
theorem stage2_pre_inhabited :
    Γ_stage2.pre
      [.ptr 0, .int 64 0, .ptr 0, .int 64 0, .ptr 0, .int 64 0, .ptr 32,
       .int 64 64, .ptr 96, .ptr 0, .int 64 0, .ptr 104, .ptr 112]
      stage2Mem 1 := by
  refine ⟨0, 0, 0, 0, 0, 0, 32, 64, 96, 0, 0, 104, 112, [], [], 0, 0, rfl,
    rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨List.replicate stage2ReadTail 0, stage2Mem_tail⟩
  · simp
  · simp
  · exact ⟨[], rfl⟩
  · exact ⟨List.replicate 64 0, stage2Mem_arena⟩
  · decide
  · exact ⟨[], rfl⟩
  · decide
  · exact stage2Mem_ndst
  · exact stage2Mem_nev
  · exact ⟨wordBytes 8 0, stage2Mem_err⟩
  · decide
  · exact stage2Mem_disjoint

/-! ### The tail's pin

`PipelineBodyFacts` is parameterised by the stage-2 record.  The two facts below
are the pin's whole content: the parameter is phantom in the bundle's fields, so
substituting `Γ_stage2` is a rename; and the verdict clause the bundle used to
take as a hypothesis is now proved, so a `Γ_stage2` bundle needs only the
selection. -/

/-- **The tail's stage-2 parameter is phantom.**  Every field of
`PipelineBodyFacts` is a statement about `pipelineCalls tab base s2` and
`pipelineBody` — the loop instance, its bound and cost, the seed and the tail —
so a bundle at one stage-2 record is a bundle at another by structure alone.  That
is why pinning `Γ2 := Γ_stage2` is a one-line instantiation, and also why it
cannot supply the bundle: none of the fields is a fact about the stage-2 run.

A structure transport rather than a theorem, because its type is a structure. -/
def pipelineBodyFacts_of_record {tab base : Nat} {s2 : Calls}
    {Γ2 Γ2' : MemContract} {args : List Value} {mem : Mem} {next : Nat}
    (F : PipelineBodyFacts tab base s2 Γ2 args mem next) :
    PipelineBodyFacts tab base s2 Γ2' args mem next where
  loop := F.loop
  N_eq := F.N_eq
  cost_le := F.cost_le
  seed := F.seed
  exit := F.exit

/-- **The units bundle at `Γ_stage2`.**  `pipelineUnits_of_records` took the
verdict clause as a hypothesis; at this record it is `stage2_verdict_bounded`, so
the only hypothesis left is the stage-2 selection itself — the body this tree
does not hold. -/
theorem pipelineUnits_at_stage2 {tab base : Nat} {s2 : Calls}
    (h2 : CallSatisfies s2 Γ_stage2 JsonPipelineIR.stage2Sym) :
    JsonPipelineIR.PipelineUnits tab base s2 Γ_stage2 :=
  JsonPipelineIR.pipelineUnits_of_records tab base s2 Γ_stage2 h2
    stage2_verdict_bounded

/-- **Pinning the tail's `Γ2` at `Γ_stage2`.**  The pipeline's unit-level record
follows from the stage-2 selection and the tail bundle, which is
`pipeline_satisfies_of_units` at `Γ2 := Γ_stage2`: the bundle is built by
`pipelineUnits_at_stage2`, so the verdict clause that used to be a hypothesis is
gone, and `h2` and `hbody` are what remain.  `hbody` is not removable from this
record: its fields are the pipeline's loop instance, seed and tail, and the tail's
`exit` runs `pipelineBody` from a loop-exit state.  What `Γ_stage2` changes about
that field is that `Γ_pipeline_units.post`'s clauses about `dst`/`ndst`/`ev`/
`nev`/`err` are now statable from a record with content, and what it does not is
produce the run's memory: that is the body analysis's.  The footprint carries the
unit records' `Classical.choice` through `pipelineUnits_at_stage2`, as
`JsonPipelineRefine`'s axiom section records for the same bundle. -/
theorem pipeline_satisfies_at_stage2 (tab : Nat) (s2 : Calls)
    (h2 : CallSatisfies s2 Γ_stage2 JsonPipelineIR.stage2Sym)
    (hbody : ∀ (base : Nat) (args : List Value) (mem : Mem) (next : Nat),
      (Γ_pipeline_units tab base).pre args mem next →
      JsonPipelineIR.PipelineUnits tab base s2 Γ_stage2 →
      PipelineBodyFacts tab base s2 Γ_stage2 args mem next) :
    ∀ base, Satisfies (JsonPipelineIR.pipelineCalls tab base s2)
      JsonPipelineIR.pipelineBody (Γ_pipeline_units tab base) :=
  pipeline_satisfies_of_units tab s2 Γ_stage2 (fun _ => pipelineUnits_at_stage2 h2) hbody

/-! ### Sanity checks on the statement's shapes -/

-- The ABI projection: thirteen arguments, in `stage2.h`'s order.
#guard ([.ptr 0, .int 64 7, .ptr 8, .int 64 5, .ptr 16, .int 64 3, .ptr 32,
  .int 64 4096, .ptr 40, .ptr 48, .int 64 4096, .ptr 56, .ptr 64] : List Value).length = 13

-- The encoding's numbers and the staged region list.
#guard stage2RecordBytes = 13
#guard stage2ArenaReserve = 64
#guard stage2ReadTail = 32
#guard (stage2Regions 0 0 0 0 0 0 32 0 0 0 96 104 112).length = 8

-- The read-past tail is not free at the pipeline's staging: a sixty-four-byte
-- document is staged as one sixty-four-byte block, and the decoder's thirty-two
-- bytes past a body ending at 62 reach `b + 94`.
#guard decide (64 * pipelineBlocks 64 < 64 + stage2ReadTail)

/-! ### Axiom footprints

Every declaration above is at `[propext, Quot.sound]` or below except the two that
carry `Classical.choice` — and neither adds it.  `pipelineUnits_at_stage2`
inherits it from the unit records through `pipelineUnits_of_records`, exactly as
`JsonPipelineRefine`'s axiom section records for the bundle it builds: the
carrier is the five unit `Satisfies` theorems, not this module.
`pipeline_satisfies_at_stage2` calls `pipelineUnits_at_stage2` for its `Γ2`
bundle, so it carries the same set rather than one step below it.  What that set
rests on are the extraction steps' lemmas — `String.ofList_injective`,
`BitVec.signExtend_eq`, `Nat.and_two_pow_sub_one_eq_mod`,
`Nat.testBit_two_pow_sub_one`, `List.getElem_mapIdx` and the two
`BitVec.msb_*` order lemmas — and the list modules' `lstWhileBody_run` and
`lstIfEnd4_run`. -/

/-- info: 'LeanLLVM.Refinement.stage2ArenaReserve' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2ArenaReserve

/-- info: 'LeanLLVM.Refinement.stage2RecordBytes' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2RecordBytes

/-- info: 'LeanLLVM.Refinement.stage2MaxDocument' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2MaxDocument

/-- info: 'LeanLLVM.Refinement.stage2ReadTail' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2ReadTail

/-- info: 'LeanLLVM.Refinement.stage2Regions' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2Regions

/-- info: 'LeanLLVM.Refinement.stage2Writes' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2Writes

/-- info: 'LeanLLVM.Refinement.stage2Frame' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2Frame

/-- info: 'LeanLLVM.Refinement.stage2EntryAllowance' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2EntryAllowance

/-- info: 'LeanLLVM.Refinement.stage2ByteAllowance' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2ByteAllowance

/-- info: 'LeanLLVM.Refinement.stage2PositionAllowance' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2PositionAllowance

/-- info: 'LeanLLVM.Refinement.stage2FinalisationAllowance' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2FinalisationAllowance

/-- info: 'LeanLLVM.Refinement.stage2Budget' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stage2Budget

/-- info: 'LeanLLVM.Refinement.stage2Pre' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2Pre

/-- info: 'LeanLLVM.Refinement.stage2Boundary' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2Boundary

/-- info: 'LeanLLVM.Refinement.stage2Post' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2Post

/-- info: 'LeanLLVM.Refinement.Γ_stage2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Γ_stage2

/-- info: 'LeanLLVM.Refinement.stage2Post_unchangedOutside' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stage2Post_unchangedOutside

/-- info: 'LeanLLVM.Refinement.stage2Frame_arena_present' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2Frame_arena_present

/-- info: 'LeanLLVM.Refinement.stage2Frame_event_present' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2Frame_event_present

/-- info: 'LeanLLVM.Refinement.stage2Post_ub_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stage2Post_ub_false

/-- info: 'LeanLLVM.Refinement.stage2_verdict_bounded' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stage2_verdict_bounded

/-- info: 'LeanLLVM.Refinement.readLanes32_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readLanes32_length

/-- info: 'LeanLLVM.Refinement.length_add_le_of_pairwise_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms length_add_le_of_pairwise_lt

/-- info: 'LeanLLVM.Refinement.length_le_of_pairwise_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms length_le_of_pairwise_lt

/-- info: 'LeanLLVM.Refinement.stage2Pre_cursor_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2Pre_cursor_bounds

/-- info: 'LeanLLVM.Refinement.stage2Mem' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2Mem

/-- info: 'LeanLLVM.Refinement.stage2Mem_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2Mem_tail

/-- info: 'LeanLLVM.Refinement.stage2Mem_arena' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2Mem_arena

/-- info: 'LeanLLVM.Refinement.stage2Mem_ndst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2Mem_ndst

/-- info: 'LeanLLVM.Refinement.stage2Mem_nev' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2Mem_nev

/-- info: 'LeanLLVM.Refinement.stage2Mem_err' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2Mem_err

/-- info: 'LeanLLVM.Refinement.stage2Mem_disjoint' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2Mem_disjoint

/-- info: 'LeanLLVM.Refinement.stage2_pre_inhabited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2_pre_inhabited

/-- info: 'LeanLLVM.Refinement.pipelineBodyFacts_of_record' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pipelineBodyFacts_of_record

/-- info: 'LeanLLVM.Refinement.pipelineUnits_at_stage2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pipelineUnits_at_stage2

/-- info: 'LeanLLVM.Refinement.pipeline_satisfies_at_stage2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pipeline_satisfies_at_stage2

/-- info: 'LeanLLVM.Refinement.stage2StagedWrites' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2StagedWrites

/-- info: 'LeanLLVM.Refinement.stage2WalkWrites' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2WalkWrites

/-- info: 'LeanLLVM.Refinement.stage2WalkFrame' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2WalkFrame

/-- info: 'LeanLLVM.Refinement.stage2WalkRegions' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2WalkRegions

/-- info: 'LeanLLVM.Refinement.stage2StagedPre' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stage2StagedPre

/-- info: 'LeanLLVM.Refinement.stage2Writes_subset_walkWrites' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2Writes_subset_walkWrites

/-- info: 'LeanLLVM.Refinement.owns_extent_present' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms owns_extent_present

/-- info: 'LeanLLVM.Refinement.stage2StagedPre_present' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stage2StagedPre_present

end LeanLLVM.Refinement
