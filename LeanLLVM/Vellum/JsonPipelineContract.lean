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
the arguments this body passes, plus the two regions the pipeline's staging owns:

* the document at `b`, padded to its block count — the mask unit reads each
  64-byte block (`Γ_masks.pre`), the UTF-8 stage its window (`Γ_utf8.pre`), and
  stage 2 the document itself;
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
def pipelineReads (tab nk0 nxp0 : Nat) (args : List Value) : List (Nat × Nat) :=
  match args with
  | [.ptr b, .int 64 n, .ptr sc, .ptr mk, .ptr entw, .ptr ep, .int 64 _,
     .ptr nk, .ptr xp, .int 64 _, .ptr nxp, .ptr xcarry, .ptr _, .int 64 _,
     .ptr ndst, .ptr _, .int 64 _, .ptr nev, .ptr err, .int 64 _] =>
      [(b, 64 * pipelineBlocks n.toNat), (tab, 8192), (sc, 24), (mk, 48),
       (entw, 8), (ep, 4 * (nk0 + 64 * pipelineBlocks n.toNat + 9)), (nk, 8),
       (xp, 4 * (nxp0 + 64 * pipelineBlocks n.toNat + 8)), (nxp, 8),
       (xcarry, 16), (ndst, 8), (nev, 8), (err, 8)]
  | _ => []

/-! ### The staged objects and their separation -/

/-- The objects the caller stages, each at the extent the record claims about
it.  The entry stream's and escape list's extents are the windows the units
write, not their full capacities: a caller is not asked to keep bytes apart that
no clause reaches. -/
def pipelineRegions (tab nk0 nxp0 ndst0 : Nat) (args : List Value) : List (Nat × Nat) :=
  match args with
  | [.ptr b, .int 64 n, .ptr sc, .ptr mk, .ptr entw, .ptr ep, .int 64 _,
     .ptr nk, .ptr xp, .int 64 _, .ptr nxp, .ptr xcarry, .ptr dst, .int 64 _,
     .ptr ndst, .ptr ev, .int 64 evcap, .ptr nev, .ptr err, .int 64 _] =>
      [(b, 64 * pipelineBlocks n.toNat), (tab, 8192), (sc, 24), (mk, 48),
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
slot's own exclusions are consumed from the pipeline's staging when `Γ_stage2`
lands; the regions above are the caller's promise this record can make now. -/
def DisjointRegions (rs : List (Nat × Nat)) : Prop :=
  rs.Pairwise fun r s => r.1 + r.2 ≤ s.1 ∨ s.1 + s.2 ≤ r.1

/-! ### The staging precondition -/

/-- The caller's staging promise, at the pipeline's twenty-argument ABI.  Each
clause names the unit record it is read from:

* the argument shape is `pipeline.h`'s ABI and `pipelineBody.params`;
* the document and its padded window are the mask record's 64-byte block read
  lifted over the whole run, and the bound is `Limits.default.maxInput`, the
  limit `Σ_pipeline` is stated at (`Parse.lean:34`);
* the entry table is `Γ_entry_pos8.pre`'s `pos8Table` clause, the same region
  §15.51 gives the caller to initialise;
* the carry slots are the inputs the mask and escape-list records read for a
  document's first block (`pipeline.h`: both zero);
* the counts are the records' cursor slots, read in;
* the entry-stream capacity is `Γ_entry_pos8.pre`'s `k + 64 * nblk + 9 ≤ outCap`
  at one block per iteration and at most sixty-four entries per block;
* the escape-list capacity is `Γ_escape_positions.pre`'s `HasBytes` clause at
  the last block's incoming count plus the batch reserve;
* the arena capacity is the `ndst0 + n + 64` extent the expander reaches from its
  cursor (C126), and the event stream is the caller's `ev` at its ABI capacity;
* the 64-bit domains are the records' own: the escape list's cursor is
  sign-extended into an address (`xn0 < 2 ^ 63`), and the entry position base is
  a `uint32` that does not truncate;
* the arm word is a selector, and its reserved bits are zero (`pipeline.h`).
-/
def pipelineStaging (args : List Value) (mem : Mem) : Prop :=
  ∃ (b sc mk entw ep nk xp nxp xcarry dst ndst ev nev err tab nk0 nxp0 ndst0
      nev0 : Nat)
    (n epcap xpcap dstcap evcap arm : BitVec 64) (bs : List UInt8),
    args = [.ptr b, .int 64 n, .ptr sc, .ptr mk, .ptr entw, .ptr ep, .int 64 epcap,
      .ptr nk, .ptr xp, .int 64 xpcap, .ptr nxp, .ptr xcarry, .ptr dst,
      .int 64 dstcap, .ptr ndst, .ptr ev, .int 64 evcap, .ptr nev, .ptr err,
      .int 64 arm] ∧
    -- the document, its limit, and the zero-padded window the last block reads
    n.toNat = bs.length ∧
    bs.length ≤ (Limits.default).maxInput ∧
    readBytes mem b (64 * pipelineBlocks bs.length) =
      some (bs ++ List.replicate (64 * pipelineBlocks bs.length - bs.length) 0) ∧
    -- the entry table: 8 KiB = 1024 u64 words, `pos8Table`
    readBytes mem tab 8192 = some pos8Table ∧
    -- the two carry slots, all zero for the document's first block
    readBytes mem sc 24 = some (carrySlot false false false) ∧
    readBytes mem xcarry 16 = some (flagBytes false ++ flagBytes false) ∧
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
    HasBytes mem ev evcap.toNat ∧
    -- the stage-2 cursors, read in (the refusal slot is in the read set below)
    readBytes mem ndst 8 = some (wordBytes 8 ndst0) ∧
    readBytes mem nev 8 = some (wordBytes 8 nev0) ∧
    -- the units' 64-bit domains
    nk0 < 2 ^ 63 ∧
    nxp0 < 2 ^ 63 ∧
    64 * pipelineBlocks bs.length + 63 < 2 ^ 32 ∧
    -- the arm selector, bits three and above reserved and zero
    arm.toNat < 8 ∧
    -- the read set, and the staged objects' separation
    (∀ r ∈ pipelineReads tab nk0 nxp0 args, HasBytes mem r.1 r.2) ∧
    DisjointRegions (pipelineRegions tab nk0 nxp0 ndst0 args)

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
void return is outside the shape `retsValued pipelineBody` pins. -/
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
              [(sc, 24), (mk, 48), (entw, 8), (ep, 4 * nk'), (nk, 8),
               (xp, 4 * nxp'), (nxp, 8), (xcarry, 16), (dst, ndst'), (ndst, 8),
               (ev, nev'), (nev, 8), (err, 8)]
      | _ => False
  | _ => False

/-! ### The record -/

/-- The assembled pipeline's unit-level record: the staging above, the
arguments-only counted budget, and the boundary projection of the loop-exit
invariant with the tail's per-unit facts.  It is `Γ_pipeline_units`, not the
specification record; see the module docstring. -/
def Γ_pipeline_units : MemContract where
  budget := pipelineBudget
  pre := fun args mem _ => pipelineStaging args mem
  post := pipelineUnitsPost

/-! ### Sanity checks on the statement's arithmetic -/

-- A block count rounds up and a zero-length document is one no-op block.
#guard decide (pipelineBlocks 0 = 0 ∧ pipelineBlocks 1 = 1 ∧
  pipelineBlocks 64 = 1 ∧ pipelineBlocks 65 = 2)

-- A shaped argument list gives the thirteen regions, including the entry
-- table once at 8 KiB; an unshaped one gives none.
#guard (pipelineReads 1024 0 0
  [.ptr 0, .int 64 1, .ptr 8, .ptr 32, .ptr 80, .ptr 88, .int 64 256,
   .ptr 120, .ptr 128, .int 64 256, .ptr 160, .ptr 168, .ptr 184,
   .int 64 4096, .ptr 208, .ptr 216, .int 64 4096, .ptr 240, .ptr 248,
   .int 64 0]).length == 13
#guard (pipelineReads 1024 0 0 []).length == 0

end LeanLLVM.Vellum
