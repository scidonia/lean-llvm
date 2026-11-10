/-
The assembled pipeline's unit-level record.

`kernel/json/pipeline.c` is the caller the five stage-1 units were hoisted for:
its ABI is `kernel/json/pipeline.h`'s twenty arguments, its body is the pinned
AST `JsonPipelineIR.pipelineBody`, and its call census is
`JsonPipelineIR.censusSymbols` — the mask unit, both entry emitters, UTF-8, the
escape list and the stage-2 slot, six symbols at the pipeline's own ABI (the
escape expander is reached one level down inside stage 2, so it is not a
pipeline call site).

**This module states the record the body satisfies, `Γ_pipeline_units`, and not
the specification record.** The specification record is a separate object with
its own module and its own post: `Σ_pipeline` is the reference parser's
predicate at `LeanLLVM.JSON.Limits.default`, stated in `JsonPipelineSpec` (D1),
and the composition from this record's post to that one is `Satisfies.mono`
applied to the finalisation lemma — D2. Keeping the two apart is deliberate: the
body's record is an object with a definition, a budget and a post about the
buffers the run leaves, while a record whose post were `Σ_pipeline` would make
the pipeline's proof depend on a predicate nothing in this module constrains.
A reader who meets `Γ_pipeline` elsewhere should read it as the specification
record and `Γ_pipeline_units` as this one.

The clauses below are not new promises: each is the caller-side staging clause
of one of the six unit records, read at the arguments this body passes, with the
census fixing which records are consumed and where. Their sources are named at
each clause. Two clauses are the pipeline's own and have no unit counterpart:
the padded input window the last partial block needs, and the entry-table region
`pipeline.h` does not carry but the initialiser fills and the pos8 emitter reads.
-/
import LeanLLVM.Vellum.JsonPipelineIR
import LeanLLVM.Vellum.JsonEscapeSteps
import LeanLLVM.JSON.Parse

namespace LeanLLVM.Vellum

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Vellum.JsonS1MasksIR
open LeanLLVM.Vellum.JsonEntryIR
open LeanLLVM.Vellum.JsonEntrySteps

/-! ### The budget and the block count -/

/-- The document's block count.  The mask unit runs on one 64-byte block per
iteration, and the last block is padded to 64 bytes, so the count is the
document length rounded up, exactly as `%n`'s loop bound forms it. -/
def pipelineBlocks (n : Nat) : Nat := (n + 63) / 64

/-- One iteration's control-step allowance.  `runFuel` counts one step per basic
block (`step` executes a block's instructions and terminator together), and the
emission's loop body is a single block that branches to itself — so an iteration
is one step, and the four here cover the arm-selection entry blocks the pinned
body visits once per document plus slack.  This is a bound and not a count:
`runFuel_mono_le` lifts the loop's actual count to it. -/
def pipelineBlockAllowance : Nat := 4

/-- The tail's control-step allowance: the entry and arm-selection blocks, the
once-only UTF-8 call, the exit tests and the final stage-2 call with its stores,
all among the pinned body's twelve blocks; sixteen covers them with slack. -/
def pipelineFinalisationAllowance : Nat := 16

/-- The pipeline's own fuel, an arguments-only counted bound
`pipelineBlockAllowance * blocks + pipelineFinalisationAllowance`, derived from
the document length the ABI already carries.  It is arguments-only because the
pipeline's per-block cost is a uniform allowance; the B8 slot's budget folds
over memory-read word values instead, which is why that record's budget uses the
memory argument and this one ignores it. -/
def pipelineBudget (args : List Value) (_mem : Mem) : Nat :=
  match args with
  | [_, .int 64 n, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] =>
      pipelineBlockAllowance * pipelineBlocks n.toNat + pipelineFinalisationAllowance
  | _ => 0

/-! ### The read set -/

/-- The extents the run reads, as the union of the units' own read clauses at
the arguments this body passes, plus the regions the pipeline's staging owns
(the padded window and the table; the document's read-past tail is the staging's
own clause beside this list):

* the document at `b`, padded to its block count — the mask unit reads each
  64-byte block (`Γ_masks.pre`), the UTF-8 stage its window (`Γ_utf8.pre`), and
  stage 2 the document itself.  The listed extent is the UTF-8 window's, because
  it is the widest of the two windows: `utf8Window bs n nb = [0, 0, 0] ++ bs ++
  padding` is read at `b - 3` for `3 + 64 * nb` bytes, so the three bytes below
  the document are part of the region and the mask unit's blocks are inside it.
  The decoder's read-past tail is not summed into this entry: the list is the
  units' read clauses at the padded window, and the tail is a presence promise
  no unit clause names, so it is the staging's own `HasBytes` clause beside this
  list at the extent `Γ_stage2.pre` asks of the call site;
* the pos8 table at `tab`, all 8 KiB — `Γ_entry_pos8.pre` reads
  `readBytes mem tab 8192 = some pos8Table`;
* the mask unit's carry slot `sc` (24 bytes, `Γ_masks.pre`) and its mask slot
  `mk` (48 bytes, read back by the pipeline's own loads at
  `json-pipeline.candidate.ll:77`);
* the entry word `entw` (8 bytes, read by the entry emitter at `:100/:135/:176`);
* the entry stream's prefix and its cursor `nk` (the fixture loads `nk` at
  `:54`), the escape list's prefix and its count slot `nxp` (loaded at `:233`),
  and the escape list's carry slot `xcarry` (16 bytes, `Γ_escape_positions.pre`);
* the cursor slots and the refusal slot `ndst`, `nev`, `err` — the stage-2 slot
  reads and writes its cursors, and `pipeline.h` names `*err` as the refusal
  output.

The entry table appears once, under the two names the sources use for the same
region: `tab`'s 8 KiB in `Γ_entry_pos8` (the capture appended the static table
as a parameter, §15.41) and the 1024-`u64` `xl_pos8` the caller initialises in
§15.51.  They are the same 8192 bytes holding `pos8Table`, so the region is
listed once with its extent.  `HasBytes` is the promise a caller can make about
a region in this memory model; an extent the proof needs and this list omits
would be an unreadable read, which is the F2-class defect §15.15 records. -/
def pipelineReads (base tab nk0 nxp0 : Nat) (args : List Value) : List (Nat × Nat) :=
  match args with
  | [.ptr _, .int 64 n, .ptr sc, .ptr mk, .ptr entw, .ptr ep, .int 64 _,
     .ptr nk, .ptr xp, .int 64 _, .ptr nxp, .ptr xcarry, .ptr _, .int 64 _,
     .ptr ndst, .ptr _, .int 64 _, .ptr nev, .ptr err, .int 64 _] =>
      [(base - 3, 3 + 64 * pipelineBlocks n.toNat), (tab, 8192), (sc, 24), (mk, 48),
       (entw, 8), (ep, 4 * (nk0 + 64 * pipelineBlocks n.toNat + 9)), (nk, 8),
       (xp, 4 * (nxp0 + 64 * pipelineBlocks n.toNat + 8)), (nxp, 8),
       (xcarry, 16), (ndst, 8), (nev, 8), (err, 8)]
  | _ => []

/-! ### The staged objects and their separation -/

/-- The objects the caller stages, each at the extent the record claims about
it.  The entry stream's and escape list's extents are the windows the units
write, not their full capacities: a caller is not asked to keep bytes apart that
no clause reaches.  The document's entry is the UTF-8 window's extent, and the
pair beside it is the read-past tail the staging's `HasBytes` clause claims: the
decoder reads those thirty-two bytes, so no writable object may be staged there,
which is what the separate pair states rather than widening the window's. -/
def pipelineRegions (base tab nk0 nxp0 ndst0 : Nat) (args : List Value) : List (Nat × Nat) :=
  match args with
  | [.ptr _, .int 64 n, .ptr sc, .ptr mk, .ptr entw, .ptr ep, .int 64 _,
     .ptr nk, .ptr xp, .int 64 _, .ptr nxp, .ptr xcarry, .ptr dst, .int 64 _,
     .ptr ndst, .ptr ev, .int 64 evcap, .ptr nev, .ptr err, .int 64 _] =>
      [(base - 3, 3 + 64 * pipelineBlocks n.toNat), (base + 64 * pipelineBlocks n.toNat, 32),
       (tab, 8192), (sc, 24), (mk, 48),
       (entw, 8), (ep, 4 * (nk0 + 64 * pipelineBlocks n.toNat + 9)), (nk, 8),
       (xp, 4 * (nxp0 + 64 * pipelineBlocks n.toNat + 8)), (nxp, 8),
       (xcarry, 16), (dst, ndst0 + n.toNat + 64), (ndst, 8),
       (ev, evcap.toNat), (nev, 8), (err, 8)]
  | _ => []

/-- Every listed object is a separate region: no byte of one is a byte of
another.  This is the composition of the pairwise exclusions the unit records
demand at this body's arguments — `Γ_masks.pre`'s three disjunctions over the
input block, the carry and the mask slot; the entry emitters' entry-word and
table exclusions against the entry stream; `Γ_escape_positions.pre`'s count
against the stream and the carry — together with `pipeline.h`'s statement that
the four scratch objects are real caller-sized memory objects.  The stage-2
slot's own exclusions and the document's read-past tail are the pipeline's: the
tail's pair above is separated from every writable object, and the remaining
stage-2 extents (`stage2Regions`) are separated once they are seen to be these
objects' sub-extents. -/
def DisjointRegions (rs : List (Nat × Nat)) : Prop :=
  rs.Pairwise fun r s => r.1 + r.2 ≤ s.1 ∨ s.1 + s.2 ≤ r.1

/-! ### The cursors' room

The two per-block units that advance a cursor — POS8's entry emitter and the
escape list — each state their 64-bit domain as a clause of their own `pre`:
`k + 64 * ent.length + 9 < 2 ^ 63` and `xn0 < 2 ^ 63`.  Both are the same
arithmetic at the same document, so they are stated here once, as the room a
cursor needs to survive the whole document's growth.  A call site that carries
`cursorRoom count blocks reserve` reads either unit's clause off
`cursorRoom_bounds` and does not restate the other unit's sum.
-/

/-- A cursor that starts at `count`, advances by at most one block's sixty-four
lanes per block, and has `reserve` slots past the last true value stays inside
the 64-bit address domain. -/
def cursorRoom (count blocks reserve : Nat) : Prop :=
  count + 64 * blocks + reserve < 2 ^ 63

/-- **One room clause, both units' cursor preconditions.**  A call at block `i`
that covers `nblk` more blocks receives a count at most `count + 64 * i`; POS8's
`pre` asks `k + 64 * nblk + 9 < 2 ^ 63` of it, and the escape list's asks
`xn0 < 2 ^ 63` with no reserve.  Both follow from the same room clause, which is
why the staging states the room and not either record's sum. -/
theorem cursorRoom_bounds {count blocks reserve i nblk : Nat}
    (h : cursorRoom count blocks reserve) (hin : i + nblk ≤ blocks)
    (hres : 9 ≤ reserve) :
    count + 64 * i + 64 * nblk + 9 < 2 ^ 63 ∧ count + 64 * i < 2 ^ 63 := by
  have hroom : count + 64 * blocks + reserve < 2 ^ 63 := h
  have hroom' : count + (64 * blocks + reserve) < 2 ^ 63 := by
    simpa only [Nat.add_assoc] using hroom
  have hmul : 64 * (i + nblk) ≤ 64 * blocks := Nat.mul_le_mul_left 64 hin
  have hsum : 64 * i + 64 * nblk + 9 ≤ 64 * blocks + reserve := by
    calc
      64 * i + 64 * nblk + 9 = 64 * (i + nblk) + 9 := by rw [Nat.mul_add]
      _ ≤ 64 * blocks + 9 := Nat.add_le_add_right hmul 9
      _ ≤ 64 * blocks + reserve := Nat.add_le_add_left hres _
  have hpos8 : count + (64 * i + 64 * nblk + 9) < 2 ^ 63 :=
    Nat.lt_of_le_of_lt (Nat.add_le_add_left hsum count) hroom'
  have hi : i ≤ blocks := Nat.le_trans (Nat.le_add_right i nblk) hin
  have hmi : 64 * i ≤ 64 * blocks := Nat.mul_le_mul_left 64 hi
  have hesc : count + 64 * i < 2 ^ 63 :=
    Nat.lt_of_le_of_lt
      (Nat.le_trans (Nat.add_le_add_left hmi count) (Nat.le_add_right _ reserve))
      hroom
  exact ⟨by simpa only [Nat.add_assoc] using hpos8, hesc⟩

/-! ### The staging precondition -/

/-- The caller's staging promise, at the pipeline's twenty-argument ABI.  Each
clause names the unit record it is read from:

* the argument shape is `pipeline.h`'s ABI and `pipelineBody.params`;
* the document and its padded window are the mask record's 64-byte block read
  lifted over the whole run, and the bound is `Limits.default.maxInput`, the
  limit `Σ_pipeline` is stated at (`Parse.lean:34`);
* the document's read-past tail is the escape expander's `HasBytes mem (b + n)
  32` (`Γ_escape_expand.pre`, read one level below at stage 2's `b + n`), staged
  at the padded window's end because the block window alone leaves fewer than
  thirty-two bytes past a document whose length is a multiple of sixty-four; it
  is presence only — no clause reads those bytes — so it is stated as a
  `HasBytes` clause and not as a wider window, which the mask and UTF-8 calls
  read block for block;
* the three bytes below the document are the UTF-8 stage's window, which
  `Γ_utf8.pre` reads at `b - 3` as `[0, 0, 0] ++ bs ++ padding`; and the document
  is non-empty because that record's `pre` and post both require `0 < n`, while
  the entry test sends a zero-length document past the loop to the stage — so the
  empty document is outside this record's domain, not a case on which a verdict
  is promised;
* the entry table is `Γ_entry_pos8.pre`'s `pos8Table` clause, the same region
  §15.51 gives the caller to initialise.  Its address is the parameter `tab`,
  not a witness: `pipelineCalls tab base` appends the table to the POS8 call's
  arguments, so the staging must name the address the call environment reads —
  an existential here would promise a table at some address while the entry call
  reads another, and the entry record's `pre` would be unsatisfiable at every
  memory that staged the table somewhere else;
* the carry slots are the inputs the mask and escape-list records read for a
  document's first block (`pipeline.h`: both zero);
* the counts are the records' cursor slots, read in;
* the entry-stream capacity is `Γ_entry_pos8.pre`'s `k + 64 * nblk + 9 ≤ outCap`
  at one block per iteration and at most sixty-four entries per block;
* the escape-list capacity is `Γ_escape_positions.pre`'s `HasBytes` clause at
  the last block's incoming count plus the batch reserve;
* the arena capacity is the `ndst0 + n + 64` extent the expander reaches from its
  cursor (C126), and the event stream is the caller's `ev` at its ABI capacity
  **and its write room**: presence alone is not what stage 2's append needs, so
  the clause is the header's written-buffer promise at the encoding's worst
  case, `nev0 + 13 * bs.length ≤ evcap` (`stage2.h:13-21`), and it lives here:
  the specification's pre reads it off this staging rather than repeating it;
* the 64-bit domains are the units' own, stated once: `cursorRoom` bounds both
  growing cursors over the whole document, so POS8's
  `k + 64 * ent.length + 9 < 2 ^ 63` and the escape list's `xn0 < 2 ^ 63` follow
  by `cursorRoom_bounds` rather than being restated here; the entry position base
  is a `uint32` that does not truncate;
* the arm word is a selector, and its reserved bits are zero (`pipeline.h`).
-/
def pipelineStaging (tab base : Nat) (args : List Value) (mem : Mem) : Prop :=
  ∃ (sc mk entw ep nk xp nxp xcarry dst ndst ev nev err nk0 nxp0 ndst0
      nev0 : Nat)
    (n epcap xpcap dstcap evcap arm : BitVec 64) (bs : List UInt8),
    args = [.ptr base, .int 64 n, .ptr sc, .ptr mk, .ptr entw, .ptr ep, .int 64 epcap,
      .ptr nk, .ptr xp, .int 64 xpcap, .ptr nxp, .ptr xcarry, .ptr dst,
      .int 64 dstcap, .ptr ndst, .ptr ev, .int 64 evcap, .ptr nev, .ptr err,
      .int 64 arm] ∧
    -- the document, its limit, and the zero-padded window the last block reads
    n.toNat = bs.length ∧
    bs.length ≤ (Limits.default).maxInput ∧
    readBytes mem base (64 * pipelineBlocks bs.length) =
      some (bs ++ List.replicate (64 * pipelineBlocks bs.length - bs.length) 0) ∧
    -- the document's read-past tail.  The last read past the document is the
    -- escape expander's, `HasBytes mem (b + n) 32` (`Γ_escape_expand.pre`), so
    -- a body ending at the document's last byte needs thirty-two readable bytes
    -- past it.  The padded window above does not carry them: it ends at
    -- `64 * pipelineBlocks bs.length`, and `#guard decide (64 * pipelineBlocks 64
    -- < 64 + 32)` holds, so a sixty-four-byte document stages one block and the
    -- decoder reads past its end.  This is the reserve window's defect class in
    -- the other direction — a region the body touches and the staging left
    -- unstaged — so it is staged here rather than narrowed out of the unit's
    -- clause.  The number is `JsonStage2Contract`'s `stage2ReadTail`; that
    -- module imports this one, so the extent is written out rather than read
    -- through the import, and the two `#guard`s beside each definition keep them
    -- equal.  It is a presence promise and not a wider read window: the window
    -- is what the mask and UTF-8 calls read, block for block, and its last block
    -- is `bs ++ padding` exactly; no clause reads these bytes' contents.
    HasBytes mem (base + 64 * pipelineBlocks bs.length) 32 ∧
    -- the UTF-8 stage's window begins three bytes below the document, and those
    -- bytes are zero: `Γ_utf8.pre` stages
    -- `readBytes mem (base - 3) (3 + 64 * nb) = some (utf8Window bs n nb)` and
    -- `utf8Window bs n nb` is `[0, 0, 0] ++ bs ++ padding`, so this clause and
    -- the document window above are that one window byte for byte
    3 ≤ base ∧
    readBytes mem (base - 3) 3 = some (List.replicate 3 0) ∧
    -- the stage is not defined on an empty document: `Γ_utf8.pre` requires
    -- `0 < n` and its post requires it too, while the entry test
    -- (`%cmp79.not = (n + 63) < 64`) sends a zero-length document straight past
    -- the loop to `for.cond.cleanup`, where the stage is called all the same.
    -- **The consequence is part of the clause.**  The empty document is outside
    -- this record's domain, so nothing is claimed about it: neither acceptance
    -- nor refusal at length zero is covered, and a reader who takes a refusal at
    -- zero as promised by `Γ_pipeline_units` is reading the record wrong.  The
    -- bound is `Γ_utf8`'s and the pipeline's staging carries it because the call
    -- site needs it; if that record widens to admit `n = 0`, this clause goes
    -- rather than standing as a limit the pipeline no longer has.
    0 < bs.length ∧
    -- the entry table: 8 KiB = 1024 u64 words, `pos8Table`
    readBytes mem tab 8192 = some pos8Table ∧
    -- the two carry slots, all zero for the document's first block; the escape
    -- list's is `carryPair`, the same definition the mask unit's `%sc` slot names
    -- at its first two words
    readBytes mem sc 24 = some (carrySlot false false false) ∧
    carryPair mem xcarry ⟨false, false⟩ false false ∧
    -- the counts, read in by the pipeline and by the escape list
    readBytes mem nk 8 = some (wordBytes 8 nk0) ∧
    readBytes mem nxp 8 = some (wordBytes 8 nxp0) ∧
    -- the entry stream's capacity, lifted over the whole document
    nk0 + 64 * pipelineBlocks bs.length + 9 ≤ epcap.toNat ∧
    -- the escape list's capacity, with the batch reserve at every block
    HasBytes mem xp (4 * (nxp0 + 64 * pipelineBlocks bs.length + 8)) ∧
    -- the arena the expander reaches and the event stream the caller sizes,
    -- each from its own cursor
    ndst0 + n.toNat + 64 ≤ dstcap.toNat ∧
    HasBytes mem dst (ndst0 + n.toNat + 64) ∧
    -- the event stream's presence *and* its room.  Presence alone admits a
    -- caller whose `evcap` is smaller than the stream stage 2 would append, and
    -- the measured body traps on that rather than overrunning; so the staging
    -- carries the header's written-buffer promise at the encoding's worst case
    -- — at most one record per input byte, at most thirteen bytes per record —
    -- and it lives here, so the specification's pre reads it off this staging
    -- rather than restating it.
    HasBytes mem ev evcap.toNat ∧
    nev0 + 13 * bs.length ≤ evcap.toNat ∧
    -- the stage-2 cursors, read in (the refusal slot is in the read set below)
    readBytes mem ndst 8 = some (wordBytes 8 ndst0) ∧
    readBytes mem nev 8 = some (wordBytes 8 nev0) ∧
    -- the two growing cursors' 64-bit room over the whole document.  The
    -- initial cursors' own bounds do not survive the growth: with `nk0 < 2 ^ 63`
    -- and a capacity at `2 ^ 63 + 100`, one block already hands POS8 a count of
    -- `2 ^ 63 + 63` — the witness beside this record.  The room is what the
    -- next iteration's calls consume, and both units' clauses read it through
    -- `cursorRoom_bounds`.
    cursorRoom nk0 (pipelineBlocks bs.length) 9 ∧
    cursorRoom nxp0 (pipelineBlocks bs.length) 9 ∧
    64 * pipelineBlocks bs.length + 63 < 2 ^ 32 ∧
    -- the arm selector, bits three and above reserved and zero
    arm.toNat < 8 ∧
    -- the read set, and the staged objects' separation
    (∀ r ∈ pipelineReads base tab nk0 nxp0 args, HasBytes mem r.1 r.2) ∧
    DisjointRegions (pipelineRegions base tab nk0 nxp0 ndst0 args)

/-! ### The room clause's witness

Kept beside the staging rather than in a later module, because it is the reason
the clause is written the way it is: the clauses the staging used to state about
the entry count admitted a state whose second iteration hands POS8 a count at or
above `2 ^ 63`.  The state below satisfies the initial-cursor bound, the block
count's `uint32` bound and the capacity clause, and fails the room.
-/

/-- **The room clause is not implied by the staging's other count clauses.**  A
one-block document with `nk0 = 2 ^ 63 - 1` and a capacity at `2 ^ 63 + 100`
satisfies `nk0 < 2 ^ 63`, `64 * blocks + 63 < 2 ^ 32` and
`nk0 + 64 * blocks + 9 ≤ epcap.toNat`, and the count the next block's POS8 call
receives is at or above `2 ^ 63`, which its `pre` refuses.  The same arithmetic
applies to the escape count with `nxp0` in place of `nk0`, which is why the
staging states the room for both. -/
theorem cursorRoom_not_implied_by_old_staging :
    ∃ (nk0 blocks : Nat) (epcap : BitVec 64),
      nk0 < 2 ^ 63 ∧ 64 * blocks + 63 < 2 ^ 32 ∧
      nk0 + 64 * blocks + 9 ≤ epcap.toNat ∧
      ¬ cursorRoom nk0 blocks 9 := by
  refine ⟨2 ^ 63 - 1, 1, BitVec.ofNat 64 (2 ^ 63 + 100), ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)]
    decide
  · have hlt : ¬ (2 ^ 63 - 1 + 64 * 1 + 9 < 2 ^ 63) := by
      have h72 : 2 ^ 63 - 1 + 64 * 1 + 9 = 2 ^ 63 + 72 := by decide
      rw [h72]
      exact Nat.not_lt_of_ge (Nat.le_add_right _ 72)
    simpa only [cursorRoom] using hlt

/-! ### The post -/

/-- The boundary projection of the loop-exit invariant and the tail's per-unit
facts, at the outcome the run returns.

On return the verdict is the ABI's accept/refuse word and the caller observes,
at its own buffers, what the units left there: the four cursors advance, the
entry stream, the escape list, the decoded arena and the event stream hold their
prefixes, the refusal word is written exactly when the run refuses, and no byte
outside the extents the run wrote has moved.  Those are the loop's exit state
counts and prefixes and the tail units' own post shapes, read at this body's
arguments; the semantic content — that the stream decodes to `decodeTape`'s
value, that the verdict is `parseBytes`'s — is `Σ_pipeline`'s and deliberately
not restated here.  `.ub` is refused by the `match`, and a non-`i64` return or a
void return is outside the shape `retsValued pipelineBody` pins.

**The unchanged extents are the units' whole touched extents, reserve included.**
A callee that stores eight entries past the count it reports, or a vector past
the decoded extent, has written those bytes whatever it reports, and a frame
naming only the counted extent is false exactly where a reserve is written: it
would leave a byte the run moved outside every extent the post names.  So each of
the three extents below is the unit's own width and not a figure chosen here:
the entry emitter's frame reaches `o + 4 * (k' + 8)`
(`JsonEntrySteps.lean:31-34`, where the eight is its sentinel lane), giving
`(ep, 4 * (nk' + 8))`; the escape batch reserves eight entries past its block's
count (`batchReserve`, the same `8` its post's `4 * blockMax xn0` is built from),
and because a block writes at most from its incoming count through its outgoing
count plus that reserve while the counts only grow, the run's writes reach at
most `nxp' + 8` entries, giving `(xp, 4 * (nxp' + batchReserve))`; and the
decoder writes `US_SLACK`, sixty-four bytes, past the decoded extent
(`kernel/json/stage2.h`), giving `(dst, ndst' + 64)`.

**The pattern the two widened records share, named where a reader meets its
members.**  `pipelineStaging` above stated the event stream's presence
(`HasBytes mem ev evcap.toNat`) without the room stage 2 appends into;
`escapePositionsPost` named the batch's whole extent in its exclusion while
declining to describe it, so its own successor had no presence to stand on, and
its post carries `HasBytes m xp (4 * blockMax xn0)` as the other half of that
exclusion; and the extents below were the counted output rather than the touched
region.  **Every region a record names is the callee's whole touched extent,
including its reserve, and every staging a record requires is presence *and* room
to write.**  A reader about to narrow one of these regions to the count a callee
returns should read the other two first: that narrowing is exactly the defect
each of them carried. -/
def pipelineUnitsPost (args : List Value) (mem : Mem) (_next : Nat)
    (o : Outcome) : Prop :=
  match o with
  | .ub => False
  | .ret (some (.int 64 verdict)) m =>
      match args with
      | [.ptr _, .int 64 _, .ptr sc, .ptr mk, .ptr entw, .ptr ep, .int 64 _,
         .ptr nk, .ptr xp, .int 64 _, .ptr nxp, .ptr xcarry, .ptr dst, .int 64 _,
         .ptr ndst, .ptr ev, .int 64 _, .ptr nev, .ptr err, .int 64 _] =>
          (verdict = 0 ∨ verdict = 1) ∧
          ∃ (nk' nxp' ndst' nev' : Nat) (ent : List Nat) (ps : List Nat)
            (out evs : List UInt8),
            readBytes m nk 8 = some (wordBytes 8 nk') ∧
            readBytes m nxp 8 = some (wordBytes 8 nxp') ∧
            readBytes m ndst 8 = some (wordBytes 8 ndst') ∧
            readBytes m nev 8 = some (wordBytes 8 nev') ∧
            readLanes32 m ep nk' = some ent ∧
            readBytes m xp (4 * nxp') = some (positionsBytes 4 ps) ∧
            readBytes m dst ndst' = some out ∧
            readBytes m ev nev' = some evs ∧
            (verdict = 0 →
              ∃ e : Nat, readBytes m err 8 = some (wordBytes 8 e)) ∧
            (verdict = 1 → readBytes m err 8 = readBytes mem err 8) ∧
            UnchangedOutside mem m
              [(sc, 24), (mk, 48), (entw, 8), (ep, 4 * (nk' + 8)), (nk, 8),
               (xp, 4 * (nxp' + batchReserve)), (nxp, 8), (xcarry, 16),
               (dst, ndst' + 64), (ndst, 8), (ev, nev'), (nev, 8), (err, 8)]
      | _ => False
  | _ => False

/-! ### The record -/

/-- The assembled pipeline's unit-level record: the staging above, the
arguments-only counted budget, and the boundary projection of the loop-exit
invariant with the tail's per-unit facts.  It is `Γ_pipeline_units`, not the
specification record; see the module docstring.

Both the table and the document are parameters because `Satisfies` fixes the
call environment before it quantifies over arguments: `pipelineCalls tab base`
chooses the POS8 table and the escape record's base, so the pre must promise the
table at that `tab`, and the staging now names it. -/
def Γ_pipeline_units (tab base : Nat) : MemContract where
  budget := pipelineBudget
  pre := fun args mem _ => pipelineStaging tab base args mem
  post := pipelineUnitsPost

/-! ### Sanity checks on the statement's arithmetic -/

-- A block count rounds up and a zero-length document is one no-op block.
#guard decide (pipelineBlocks 0 = 0 ∧ pipelineBlocks 1 = 1 ∧
  pipelineBlocks 64 = 1 ∧ pipelineBlocks 65 = 2)

-- A shaped argument list gives the thirteen regions, including the entry
-- table once at 8 KiB; an unshaped one gives none.
#guard (pipelineReads 0 1024 0 0
  [.ptr 0, .int 64 1, .ptr 8, .ptr 32, .ptr 80, .ptr 88, .int 64 256,
   .ptr 120, .ptr 128, .int 64 256, .ptr 160, .ptr 168, .ptr 184,
   .int 64 4096, .ptr 208, .ptr 216, .int 64 4096, .ptr 240, .ptr 248,
   .int 64 0]).length == 13
#guard (pipelineReads 0 1024 0 0 []).length == 0

-- The staged document is two adjacent extents: the UTF-8 window's padded block,
-- ending at `base + 64 * blocks`, and the read-past tail that begins there.  At
-- `base = 64` and a sixty-four-byte document the window is `61 .. 128` and the
-- tail `128 .. 160`, which is where the decoder's read past the padded window
-- lands — the arithmetic the staging's `HasBytes` clause stages.
#guard decide ((pipelineRegions 64 4096 0 0 0
  [.ptr 0, .int 64 64, .ptr 8, .ptr 32, .ptr 80, .ptr 88, .int 64 256,
   .ptr 120, .ptr 128, .int 64 256, .ptr 160, .ptr 168, .ptr 184,
   .int 64 4096, .ptr 208, .ptr 216, .int 64 4096, .ptr 240, .ptr 248,
   .int 64 0]).take 2 = [(61, 67), (128, 32)])
#guard (pipelineRegions 64 4096 0 0 0
  [.ptr 0, .int 64 1, .ptr 8, .ptr 32, .ptr 80, .ptr 88, .int 64 256,
   .ptr 120, .ptr 128, .int 64 256, .ptr 160, .ptr 168, .ptr 184,
   .int 64 4096, .ptr 208, .ptr 216, .int 64 4096, .ptr 240, .ptr 248,
   .int 64 0]).length == 16

/-! ### Axiom footprints

The room derivation carries no axioms, and the witness only `propext` (its
`decide` closes a closed comparison).
-/

/-- info: 'LeanLLVM.Vellum.cursorRoom' does not depend on any axioms -/
#guard_msgs in
#print axioms cursorRoom

/-- info: 'LeanLLVM.Vellum.cursorRoom_bounds' does not depend on any axioms -/
#guard_msgs in
#print axioms cursorRoom_bounds

/-- info: 'LeanLLVM.Vellum.cursorRoom_not_implied_by_old_staging' depends on axioms: [propext] -/
#guard_msgs in
#print axioms cursorRoom_not_implied_by_old_staging

end LeanLLVM.Vellum
