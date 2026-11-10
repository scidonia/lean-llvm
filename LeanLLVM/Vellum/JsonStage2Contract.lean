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
  post also uses) and three content clauses the walk's own reads need:
  `ent.Pairwise (· < ·)` (document order, and distinct — two entries at one
  position do not exist), `∀ q ∈ ent, q < n` (the walk reads `b[q]`, the closing
  quote's index and the first-whitespace scan, all inside the document), and the
  number-token domain below.  These are *safety* clauses, not a description of
  the stream: a caller whose entry stream held a position outside the document,
  or two positions out of order, would drive reads outside the region it staged
  and a `close - p - 1` that underflows;
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

## A number token longer than the slow path's copy is outside the domain

`stage2.h:26-38` states the limit and this record states it as a clause: the
walk's number conversion ends in the reference's `num_scan`/`to_double`, which
copies the token into `measured/p6.c`'s `char tmp[64]` under its `n < sizeof tmp`
test and allocates when the token does not fit.  A memory map with no heap models
neither the allocation nor the `exit` on exhaustion, so **number tokens shorter
than sixty-four bytes** are the domain — and the clause is stated as the token's
own length (`Stage2NumbersFit`), read from the document's bytes at staging time.

**The gap between entries is not the token's length, and a clause stated over it
is false of an ordinary document.**  `[1` followed by a hundred spaces and `,]`
puts entries at `0, 1, 102, 103`: the number-start entry at `1` has a distance of
`101` to the next entry while its token is the single byte `1`.  A promise that
the distance to the next entry is below sixty-four therefore refuses a document
the walk reads, and no staging can make it true of every document a caller
stages — so it would have excluded the ordinary case rather than the model's
edge.  The document is `stage2GapDoc` below, with its two numbers executed beside
the clause.

What the number scan actually needs is the token's reach: it stops at the first
byte that ends a scalar — whitespace or a structural byte (`stage2.c`'s
`od_scalar_value` scan, and `num_scan`'s copy) — and the bytes after that stop
are never read.  `stage2NumberLen` is that length for the bytes at an entry, so
the clause is statable at staging time over the document and the entry positions
together, and its threshold is the same `stage2NumberCopy = 64` the fallback's
own `tmp[64]` uses: the unit's domain edge and the pipeline's staging domain are
one condition rather than two that could drift.  The clause is over the entries
whose first byte is a number start (`-` or a digit, `od_scalar_value`'s test); it
says nothing about what the number *means*.

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

## The one clause of the pre a pipeline call site cannot derive yet

Four of the pre's five groups are consequences of the pipeline's own staging, by
projection: `HasBytes` and the two capacities are `pipelineStaging`'s clauses at
the same numbers (including `nev0 + 13 * n ≤ evcap`, verbatim), the document
window and `n ≤ 2 ^ 32` follow from its `64 * pipelineBlocks n + 63 < 2 ^ 32`, the
cursor slots from its two reads, and `DisjointRegions` from its
`pipelineRegions`/`DisjointRegions` once the stage-2 extents are seen to be
sub-extents (`nep ≤ nk0 + 64 * blocks` and `nxp ≤ xpExtent = xn0 + 64 * blocks +
8`, both carried by the loop invariant).

**The entry stream's contents are not.**  `Γ_stage2.pre` needs
`readLanes32 mem ep nep = some ent` with `ent` in document order, inside the
document, and with the number-token distances below the copy's size — the three
clauses the walk's own reads make safety conditions.  `pipelineUnitsPost` states
`readLanes32 m ep nk' = some ent` with `ent` existential and nothing said about
it, and `pipelineLoopInv` carries `S.doc`, the two counts and their `HasBytes`/
`DisjointRegions` extents but not the stream's bytes.  So the tail's derivation of
this call's pre needs those three clauses carried by the loop's invariant, where
the entry emitters' own posts (`entryPos8Post`, `entryB8Post`:
`readLanes32 m (o + 4 * k) (k' - k) = streamPrefix ent blk0 nblk`) can supply
them; that is `PipelineBodyFacts.lean`/`PipelineBodyStep.lean` work and not this
record's.  The alternative — dropping the clauses here — would make the record
false of a caller whose entry stream named a byte outside the document it staged,
which is the defect the clauses exist to exclude.

**And the document's read-past tail is one clause the staging does not always
carry.**  `pipelineStaging` stages the document as
`readBytes mem base (64 * pipelineBlocks n) = some (bs ++ padding)`, so the
presence it gives past the document is `64 * pipelineBlocks n - n` bytes, which
is any value in `0 … 63`.  `Γ_stage2.pre` needs thirty-two.  A sixty-four-byte
document whose last string body ends at byte 62 is the witness: one block gives
64 staged bytes and the decoder's read-past reaches `b + 94` (the `#guard` below
is that arithmetic, executed).  Closing it is a staging change — the window at
`64 * pipelineBlocks n + 32`, or a `HasBytes mem (base + 64 * pipelineBlocks n)
32` clause — in `JsonPipelineContract.lean`'s `pipelineStaging`, which this slice
does not own; narrowing this clause instead would be false of the body.
-/
import LeanLLVM.FramePredicate
import LeanLLVM.Vellum.PipelineBodyFacts

set_option autoImplicit false

namespace LeanLLVM.Vellum

open LeanLLVM
open LeanLLVM.Vellum.JsonEntryIR (readLanes32)
open LeanLLVM.Vellum.JsonEntrySteps (readBytes_writeBytes_frame)

/-! ### The walk's own numbers, named where the record uses them -/

/-- The decoder's slack past the arena cursor: `stage2.c`'s `US_SLACK` (line 52),
sixty-four bytes at the measured `US_EMIT4=1`, which `stage2.h:49-52` states as
part of the capacity promise. -/
def stage2ArenaReserve : Nat := 64

/-- One event record's widest encoding (`stage2.h:68-75`): a tag byte, four
length bytes and eight span-or-arena bytes for a key or a string
(`stage2.c:837-841`); a number's nine and a structural byte's one are narrower. -/
def stage2RecordBytes : Nat := 13

/-- The slow path's stack copy: `measured/p6.c`'s `char tmp[64]` under its
`n < sizeof tmp` test, the limit `stage2.h:26-38` states.  A token at or beyond
it can allocate, which the memory map does not model. -/
def stage2NumberCopy : Nat := 64

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

/-! ### The number-token domain

The walk's token for an entry is bounded by the next entry's position
(`stage2.c`'s `t.end`/`ip`), so the caller's promise is a statement about the
entry stream's consecutive distances — the only place the token's length is
visible before the run. -/

/-- Whether a byte begins a number token: `od_scalar_value`'s test,
`c == '-' || ('0' <= c && c <= '9')`. -/
def stage2IsNumberStart (c : UInt8) : Bool :=
  decide (c = 0x2D) || (decide (0x30 ≤ c) && decide (c ≤ 0x39))

/-- Whether a byte ends a scalar token: whitespace, or one of the structural
bytes the walk's switch takes its own arm for (`stage2.c`'s `od_scalar_value`
scan stops there, and `num_scan` copies no further). -/
def stage2EndsNumber (c : UInt8) : Bool :=
  decide (c = 0x20) || decide (c = 0x09) || decide (c = 0x0A) ||
    decide (c = 0x0D) || decide (c = 0x2C) || decide (c = 0x3A) ||
    decide (c = 0x7B) || decide (c = 0x7D) || decide (c = 0x5B) || decide (c = 0x5D)

/-- The number token's length at `p`: the run of bytes from `p` up to the first
byte that ends a scalar, or the document's end.  This is the length the fallback
copies into `tmp[64]`, read from the document rather than from the distance to
the next entry. -/
def stage2NumberLen (bs : List UInt8) (p : Nat) : Nat :=
  ((bs.drop p).takeWhile (fun c => !stage2EndsNumber c)).length

/-- The counterexample the gap promise fails on: `[1`, a hundred spaces, `,]`.
Its entries are `0, 1, 102, 103`; the number-start entry at `1` is one byte long
and a hundred and one bytes from the next entry. -/
def stage2GapDoc : List UInt8 :=
  [0x5B, 0x31] ++ List.replicate 100 0x20 ++ [0x2C, 0x5D]

theorem stage2GapDoc_length : stage2GapDoc.length = 104 := by decide

/-- The document's byte at `1` is the number start `1`, and its token is that one
byte — the two numbers the gap promise and the token-length promise disagree
about. -/
theorem stage2GapDoc_token :
    stage2GapDoc[1]? = some 0x31 ∧ stage2IsNumberStart 0x31 = true ∧
      stage2NumberLen stage2GapDoc 1 = 1 ∧ 102 - 1 = 101 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

-- The two promises, at the counterexample: the token is one byte and the gap is
-- a hundred and one, so the gap promise would refuse this document and the
-- token-length promise admits it.  Executed, not asserted in prose.
#guard decide (stage2NumberLen stage2GapDoc 1 < stage2NumberCopy)
#guard decide (¬ (102 - 1 < stage2NumberCopy))
#guard decide (stage2NumberLen stage2GapDoc 0 = 0)

/-- **Every number token in the document fits the walk's slow-path copy**
(`stage2.h:26-38`): for each entry whose first byte is a number start, the token
that begins there is shorter than `stage2NumberCopy`.

The bound is the token's own length (`stage2NumberLen`), which is what the
fallback copies into `tmp[64]`: the scan stops at the first whitespace or
structural byte and never reads past it.  It is *not* the distance to the next
entry — `stage2GapDoc` is the witness, an ordinary document whose number-start
entry has a hundred-and-one-byte gap and a one-byte token — so a promise stated
over entry distances would refuse documents the walk reads.  A number's internal
bytes are not entries (`stage2.h:56-58`), which is why the entry list alone cannot
name the token: the clause reads the document's bytes at the entry position. -/
def Stage2NumbersFit (bs : List UInt8) (ent : List Nat) : Prop :=
  ∀ (i p : Nat) (c : UInt8),
    ent[i]? = some p → bs[p]? = some c → stage2IsNumberStart c = true →
      stage2NumberLen bs p < stage2NumberCopy

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
region claim `Owns` rather than a list beside a second list. -/
def stage2Frame (dst ndst' ev nev' ndst nev err : Nat) : Nat → Prop :=
  inRegions (stage2Writes dst ndst' ev nev' ndst nev err)

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
    -- and the number-token domain (`stage2.h:26-38`)
    Stage2NumbersFit bs ent ∧
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
`Sigma_pipeline`'s and `EventStreamRel`'s, and is deliberately absent. -/
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
    ndst0, nev0, _hargs, _hdoc, _htail, hent, horder, hlt, _hfit, _hxp, _hdstpres,
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
empty so the two content clauses and the number-token domain are vacuous, the
document's read-past tail is staged, and the cursors read zero.  The record
therefore promises something rather than refusing every caller. -/
theorem stage2_pre_inhabited :
    Γ_stage2.pre
      [.ptr 0, .int 64 0, .ptr 0, .int 64 0, .ptr 0, .int 64 0, .ptr 32,
       .int 64 64, .ptr 96, .ptr 0, .int 64 0, .ptr 104, .ptr 112]
      stage2Mem 1 := by
  refine ⟨0, 0, 0, 0, 0, 0, 32, 64, 96, 0, 0, 104, 112, [], [], 0, 0, rfl,
    rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨List.replicate stage2ReadTail 0, stage2Mem_tail⟩
  · simp
  · simp
  · simp [Stage2NumbersFit]
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
      (Γ_pipeline_units base).pre args mem next →
      JsonPipelineIR.PipelineUnits tab base s2 Γ_stage2 →
      PipelineBodyFacts tab base s2 Γ_stage2 args mem next) :
    ∀ base, Satisfies (JsonPipelineIR.pipelineCalls tab base s2)
      JsonPipelineIR.pipelineBody (Γ_pipeline_units base) :=
  pipeline_satisfies_of_units tab s2 Γ_stage2 (fun _ => pipelineUnits_at_stage2 h2) hbody

/-! ### Sanity checks on the statement's shapes -/

-- The ABI projection: thirteen arguments, in `stage2.h`'s order.
#guard ([.ptr 0, .int 64 7, .ptr 8, .int 64 5, .ptr 16, .int 64 3, .ptr 32,
  .int 64 4096, .ptr 40, .ptr 48, .int 64 4096, .ptr 56, .ptr 64] : List Value).length = 13

-- A number start is `-` or a digit, and a structural byte is neither.
#guard stage2IsNumberStart 0x2D = true
#guard stage2IsNumberStart 0x30 = true
#guard stage2IsNumberStart 0x39 = true
#guard stage2IsNumberStart 0x7B = false
#guard stage2IsNumberStart 0x2B = false

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

/-- info: 'LeanLLVM.Vellum.stage2ArenaReserve' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2ArenaReserve

/-- info: 'LeanLLVM.Vellum.stage2RecordBytes' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2RecordBytes

/-- info: 'LeanLLVM.Vellum.stage2NumberCopy' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2NumberCopy

/-- info: 'LeanLLVM.Vellum.stage2MaxDocument' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2MaxDocument

/-- info: 'LeanLLVM.Vellum.stage2ReadTail' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2ReadTail

/-- info: 'LeanLLVM.Vellum.stage2IsNumberStart' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2IsNumberStart

/-- info: 'LeanLLVM.Vellum.Stage2NumbersFit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Stage2NumbersFit

/-- info: 'LeanLLVM.Vellum.stage2EndsNumber' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2EndsNumber

/-- info: 'LeanLLVM.Vellum.stage2NumberLen' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2NumberLen

/-- info: 'LeanLLVM.Vellum.stage2GapDoc' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2GapDoc

/-- info: 'LeanLLVM.Vellum.stage2GapDoc_token' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stage2GapDoc_token

/-- info: 'LeanLLVM.Vellum.Stage2NumbersFit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Stage2NumbersFit

/-- info: 'LeanLLVM.Vellum.stage2Regions' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2Regions

/-- info: 'LeanLLVM.Vellum.stage2Writes' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2Writes

/-- info: 'LeanLLVM.Vellum.stage2Frame' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2Frame

/-- info: 'LeanLLVM.Vellum.stage2EntryAllowance' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2EntryAllowance

/-- info: 'LeanLLVM.Vellum.stage2ByteAllowance' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2ByteAllowance

/-- info: 'LeanLLVM.Vellum.stage2PositionAllowance' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2PositionAllowance

/-- info: 'LeanLLVM.Vellum.stage2FinalisationAllowance' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2FinalisationAllowance

/-- info: 'LeanLLVM.Vellum.stage2Budget' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stage2Budget

/-- info: 'LeanLLVM.Vellum.stage2Pre' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stage2Pre

/-- info: 'LeanLLVM.Vellum.stage2Boundary' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2Boundary

/-- info: 'LeanLLVM.Vellum.stage2Post' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2Post

/-- info: 'LeanLLVM.Vellum.Γ_stage2' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Γ_stage2

/-- info: 'LeanLLVM.Vellum.stage2Post_unchangedOutside' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stage2Post_unchangedOutside

/-- info: 'LeanLLVM.Vellum.stage2Frame_arena_present' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2Frame_arena_present

/-- info: 'LeanLLVM.Vellum.stage2Frame_event_present' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2Frame_event_present

/-- info: 'LeanLLVM.Vellum.stage2Post_ub_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stage2Post_ub_false

/-- info: 'LeanLLVM.Vellum.stage2_verdict_bounded' depends on axioms: [propext] -/
#guard_msgs in
#print axioms stage2_verdict_bounded

/-- info: 'LeanLLVM.Vellum.readLanes32_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms readLanes32_length

/-- info: 'LeanLLVM.Vellum.length_add_le_of_pairwise_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms length_add_le_of_pairwise_lt

/-- info: 'LeanLLVM.Vellum.length_le_of_pairwise_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms length_le_of_pairwise_lt

/-- info: 'LeanLLVM.Vellum.stage2Pre_cursor_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2Pre_cursor_bounds

/-- info: 'LeanLLVM.Vellum.stage2Mem' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2Mem

/-- info: 'LeanLLVM.Vellum.stage2Mem_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2Mem_tail

/-- info: 'LeanLLVM.Vellum.stage2Mem_arena' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2Mem_arena

/-- info: 'LeanLLVM.Vellum.stage2Mem_ndst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2Mem_ndst

/-- info: 'LeanLLVM.Vellum.stage2Mem_nev' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2Mem_nev

/-- info: 'LeanLLVM.Vellum.stage2Mem_err' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2Mem_err

/-- info: 'LeanLLVM.Vellum.stage2Mem_disjoint' does not depend on any axioms -/
#guard_msgs in
#print axioms stage2Mem_disjoint

/-- info: 'LeanLLVM.Vellum.stage2_pre_inhabited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2_pre_inhabited

/-- info: 'LeanLLVM.Vellum.pipelineBodyFacts_of_record' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pipelineBodyFacts_of_record

/-- info: 'LeanLLVM.Vellum.pipelineUnits_at_stage2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pipelineUnits_at_stage2

/-- info: 'LeanLLVM.Vellum.pipeline_satisfies_at_stage2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pipeline_satisfies_at_stage2

end LeanLLVM.Vellum
