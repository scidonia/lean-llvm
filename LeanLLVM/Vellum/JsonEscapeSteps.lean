/-
The escape unit's boundary records, at its two entry points.

The unit answers two questions and this module states what a caller may rely on for
each: the position list a block's masks give (`leanllvm_json_escape_list`), and the
decode of a string body against such a list
(`leanllvm_json_escape_expand`).  `Γ_escape` is the pair's collective name; the
records are separate because `Satisfies` is read at one body, and the two entry
points have different argument lists and different claims.

Three things are stated here and nothing else:

* The two `pre`s.  Every clause is an obligation **the caller** carries, and each
  one is named where it is written.  The expander's `pre` carries the three the
  measurement of the unit forced: the list is exactly this body's
  `escapePositions` — not a buffer of that capacity, because the list-driven path
  does not range-test an entry against its cursor and an entry inside an escape the
  previous one consumed underflows the run length; **thirty-two readable bytes past
  `b + n`**, because the run copy's first load is unconditional; and the
  destination extent, **sixty-four bytes past the decoded extent**, because the
  stored form writes a whole vector there.  It also carries the escape table the
  rewritten body reads: the fragment has no globals, so the table base is a ninth
  argument and the clause promises its content at `unescapeTable`, the rule's own
  table rather than a transcription.

* The two `post`s.  The list's is the clause the entry point itself runs: the
  count advances by this body's escape positions and those positions are written at
  the caller's stream cursor.  It is stated without a gate arm, because the entry
  point has **no gate input** — the density gate is the pipeline's staging, supplied
  there rather than computed here.  There is deliberately no suppressed clause in
  this record: the measurement of the unit refutes "a document with a suppressed
  list carries no escape" on seven of twenty-one documents, and the pinned body
  emits for a block whose escape word is non-zero whatever the gate class, so a
  clause asserting the count unchanged is false of the measured code.  The
  expander's names the decoded bytes, the list cursor it leaves, and — on a refusal
  — the body-relative offset, which is a stated outcome rather than an absence.

* The unchanged conjunct, as the *extent* the run writes and no wider.  The
  measured eight-entry batch stores past the true count, so those bytes are inside
  the extent and this conjunct is silent about their values; `pre` separately tells
  the caller not to read them.

Each record takes its `budget` as a parameter.  The fuel is the run's own step
count, which is read off the pinned body of the unit; it is not a constant of the
contract, and a number written here before the body exists would be a promise with
nothing behind it.

The bodies are pinned in `JsonEscapeIR`: the list entry point, the expander's entry
point, the decoder it calls and the batch the list calls, all four compared whole
against `probes/install/ir/json-escape.candidate.ll` by `#guard`.  The `Satisfies`
instances that read these records at those bodies are **not** stated in this module
yet; the pin is what lets such an instance name the measured body rather than an
authored one, and the records above are stated at the corrected boundary — the
list's stream claim at `xp + 4 * xn0` with the block base added, and the expander's
ninth argument with the table clause — so that an instance proved at the pinned body
is a statement about the measured unit.
-/
import LeanLLVM.Vellum.JsonEscapeIR
import LeanLLVM.Vellum.JsonEscapeBatch
import LeanLLVM.Vellum.JsonEscapeSpec
import LeanLLVM.Vellum.JsonS1MasksIR
import LeanLLVM.Vellum.Refinement
import LeanLLVM.Vellum.JsonEscapeListInvariant

namespace LeanLLVM.Vellum

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Vellum.JsonS1MasksIR
open LeanLLVM.Vellum.JsonScanSpec

/-! ### Reading a store region -/

/-- The bytes at `a … a + k` are present in the caller's store.  This is the form a
capacity or an extent obligation takes in this memory model: a write replaces a cell
that is there and extends the map when it is not, so what a caller can promise about
a region it hands over is that the region exists. -/
def HasBytes (mem : Mem) (a k : Nat) : Prop :=
  ∃ vs, readBytes mem a k = some vs

/-- Every byte outside `regions` reads as it did before the run.  A region is an
address and a length; the extent a run wrote is the list of regions it names, and a
byte the store reached is inside one of them. -/
def UnchangedOutside (mem m : Mem) (regions : List (Nat × Nat)) : Prop :=
  ∀ a, (∀ r ∈ regions, ¬ (r.1 ≤ a ∧ a < r.1 + r.2)) → readByte m a = readByte mem a

/-- A boolean flag as the eight bytes a caller's carry slot holds. -/
def flagBytes (b : Bool) : List UInt8 := natToBytes (if b then 1 else 0) 8

/-- The reserve the measured batch writes past the true count: eight entries of
four bytes. -/
def batchReserve : Nat := 8

/-- One block's positions occupy at most sixty-four entries. -/
def blockMax (xn0 : Nat) : Nat := xn0 + 64 + batchReserve

/-- The positions a block's run emits, as the store holds them: the block's own
escape positions, in order, lifted to the document by the position base.  The
specification is about the block (`escapePositionsFrom`), so the lift is the
record's, where the ABI's address is. -/
def blockPositions (blk0 : BitVec 64) (lo hi : Block32) (st : ClassState) : List Nat :=
  (escapePositionsFrom (block64 lo hi) st).map fun k => blockAddr blk0 + k

/-- The escape table the rewritten decoder reads: `UJ_UNESC`'s reading of a byte,
stated from the escape rule rather than transcribed.  A byte an escape can stand
for maps to the byte it means, and every other byte maps to `0xFF`, which the
decoder's signed test reads as "not a two-character escape".  Derived from
`simpleEscape`, so the table and the rule cannot drift. -/
def unescapeTable : List UInt8 :=
  (List.range 256).map fun c => (simpleEscape (UInt8.ofNat c)).getD 0xFF

-- The table has one entry per byte.
#guard unescapeTable.length = 256

-- Each of the eight escape characters maps to the byte it stands for.
#guard unescapeTable[0x22]? = some 0x22
#guard unescapeTable[0x5C]? = some 0x5C
#guard unescapeTable[0x2F]? = some 0x2F
#guard unescapeTable[0x62]? = some 0x08
#guard unescapeTable[0x66]? = some 0x0C
#guard unescapeTable[0x6E]? = some 0x0A
#guard unescapeTable[0x72]? = some 0x0D
#guard unescapeTable[0x74]? = some 0x09

-- The control's own affirmative control, in the same run: a byte that is not an
-- escape character maps to `0xFF`, which the decoder's signed test reads as "not
-- a two-character escape".  `u`, `0` and `A` are each handled by another rule —
-- the hex form and the refusal — and none of them may be met by the table.
#guard unescapeTable[0x75]? = some 0xFF
#guard unescapeTable[0x30]? = some 0xFF
#guard unescapeTable[0x41]? = some 0xFF
#guard unescapeTable[0x01]? = some 0xFF

/-! ### The position list's record

One record, one clause: the entry point has no gate input, so the clause is the one
its body runs.  The gate a caller may apply is that caller's staging, not a
parameter of this record. -/

/-- The list's claim about the memory it leaves: the eight-entry
reserve the first batch writes is at `xp + 4 * xn0`, so the entries the run *claims*
start where the caller's count says the stream ends.  The positions are the block's
own, lifted by `blockAddr blk0`, because the store's positions are document offsets
and the specification's are block lanes.

The unchanged conjunct is over the extent the run wrote, which includes the batch
reserve the run touched. -/
def escapePositionsPost (args : List Value) (mem m : Mem) : Prop :=
  ∃ (xp xn carry : Nat) (blk0 : BitVec 64) (bs ctl im : BitVec 64) (lo hi : Block32)
    (st : ClassState) (prevb prevs : Bool) (xn0 : Nat),
    args = [.int 64 bs, .int 64 ctl, .int 64 im, .int 64 blk0, .ptr xp, .ptr xn,
      .ptr carry] ∧
    readBytes mem (blockAddr blk0) 64 = some (block64 lo hi) ∧
    bs = specBackslash64 lo hi st ∧ ctl = specControl64 lo hi st ∧
    im = specInString64 lo hi st ∧
    st.oddRun = (prevb && prevs) ∧
    readBytes mem carry 16 = some (flagBytes prevb ++ flagBytes prevs) ∧
    readBytes mem xn 8 = some (wordBytes 8 xn0) ∧
    readBytes m xn 8 = some (wordBytes 8 (xn0 +
      (escapePositionsFrom (block64 lo hi) st).length)) ∧
    readBytes m (xp + 4 * xn0) (4 * (escapePositionsFrom (block64 lo hi) st).length) =
      some (positionsBytes 4 (blockPositions blk0 lo hi st)) ∧
    UnchangedOutside mem m [(xp, 4 * (blockMax xn0)), (xn, 8), (carry, 16)]

/-- The position list's boundary record.

There is no arm: the pinned entry point has no gate input, so this record is the one
clause its body runs, and the gate a caller may apply is that caller's own staging.
Its `pre` is the caller's staging: the three masks are the block's classifier
words, the carry slot holds the pair the previous block left with the run parity
they spell, and the stream has room for the block's maximum plus the batch reserve.
The count is read in and out of its own slot; the reserve is inside the capacity and
outside the stream, so `pre` promises the room and `post` claims nothing about the
reserve's values.

The block itself is named in the caller's store because the claim is about **that**
block's positions, and the specification reads them off its bytes; the entry point
does not read the block, so this clause is not a readability obligation the body
has.

**The count's slot is disjoint from the other two, and the exclusion is partial on
purpose.** The body stores the outgoing carry at `carry` and `carry + 8` before it
reads the count, and the batch loop both reads the count and writes the stream, so a
count slot that is also the carry slot is overwritten by the carry's first store — the
value `if.end.i4` then reads is not the caller's count — and a count slot inside the
stream's capacity is overwritten by a batch. **`carry` versus `xp` needs no clause**:
the carry's stores precede every batch store, and every byte the claim names is
rewritten by a batch afterwards, so a shared byte carries the batch's value and not
the carry's. **The block versus `xp` needs none either**: the positions are a function
of the block in the caller's *input* memory, and the run's memory is never read for
it. The clause is the minimum that makes `post` true rather than the full pairwise
exclusion, because a staging promise the proof does not need is a caller obligation
that should not be asked for; it is stated here, with the two exclusions that are not
made and their reasons, so that a later reader does not uniformise it.

**The count is a pointer-arith obligation, not a capacity one.** `if.end.i4` forms
`%xp + 4 * %xn` with a `getelementptr`, whose 64-bit index the model sign-extends
and accepts on its forward arm only below `2 ^ 63`; a count with the high bit set
would take the backward arm or be refused, so the record requires
`xn0 < 2 ^ 63` and the clause sits with `pre`'s other domain promises. The
capacity side is the separate `HasBytes mem xp (4 * blockMax xn0)` clause, which
the bound does not touch. A pipeline that starts each block's count at zero and
advances it by at most sixty-four never approaches this bound.

The staged input is otherwise the caller's: the unit is not defined on overlapping
slots, and the record says so rather than modelling the alias. -/
def Γ_escape_positions (budget : List Value → Mem → Nat) : MemContract where
  budget := budget
  pre := fun args mem _ =>
    ∃ (xp xn carry : Nat) (blk0 : BitVec 64) (bs ctl im : BitVec 64) (lo hi : Block32)
      (st : ClassState) (prevb prevs : Bool) (xn0 : Nat),
      args = [.int 64 bs, .int 64 ctl, .int 64 im, .int 64 blk0, .ptr xp, .ptr xn,
        .ptr carry] ∧
      -- the three masks are this block's classifier words
      readBytes mem (blockAddr blk0) 64 = some (block64 lo hi) ∧
      bs = specBackslash64 lo hi st ∧ ctl = specControl64 lo hi st ∧
      im = specInString64 lo hi st ∧
      -- the carry pair, and the parity the block's first lane is entered with
      st.oddRun = (prevb && prevs) ∧
      readBytes mem carry 16 = some (flagBytes prevb ++ flagBytes prevs) ∧
      -- the count in, and the capacity: this block's sixty-four lanes plus the
      -- eight-entry batch reserve
      readBytes mem xn 8 = some (wordBytes 8 xn0) ∧
      -- the count is a cursor the body sign-extends into an address: the first
      -- batch computes `%xp + 4 * %xn`, and the model's `getelementptr` accepts
      -- a 64-bit index only below `2 ^ 63` on the forward arm, so a count with
      -- the high bit set is outside the unit's defined domain rather than a
      -- staging this record admits
      xn0 < 2 ^ 63 ∧
      -- the count's slot is disjoint from the stream's capacity and from the
      -- carry: the carry's stores and the batch's stores would otherwise
      -- overwrite the count the body reads back
      (xn + 8 ≤ xp ∨ xp + 4 * blockMax xn0 ≤ xn) ∧
      (carry + 16 ≤ xn ∨ xn + 8 ≤ carry) ∧
      HasBytes mem xp (4 * blockMax xn0) ∧
      -- the position base is a `uint32` that does not truncate
      blk0.toNat * 64 + 64 < 2 ^ 32
  post := fun args mem _ o =>
    match o with
    | .ub => False
    | .ret _ m => escapePositionsPost args mem m

/-- The list record refuses `ub`: its `post` is `False` at that outcome, so "the
record forbids undefined behaviour" is a proposition. -/
theorem escape_positions_ub_false (budget : List Value → Mem → Nat)
    (args : List Value) (mem : Mem) (next : Nat) :
    ¬ (Γ_escape_positions budget).post args mem next .ub := by
  intro h; exact h

/-- The list record's guarantee ignores the returned value, because the entry point
returns `void` and everything it says is about the memory it leaves. -/
theorem escape_positions_valueIrrelevant (budget : List Value → Mem → Nat) :
    ValueIrrelevant (Γ_escape_positions budget) := by
  intro args mem next v v' m
  rfl

/-! ### The expander's record -/

/-- The decode's answer, in the two outcomes the measured signature distinguishes:
the decoded bytes with the cursor, or a refusal at a body-relative offset with the
same cursor.

**The walk is the resumable one, because the ABI carries the cursor in.**  `*xj` is
the caller's position index, and the body starts its walk there: a staging with
`k0 > 0` copies the bytes before the first unprocessed position raw and decodes from
that position onward.  `escapeDecodeGo body 0 k0 (positions.drop k0) []` is exactly
that walk, and the count it returns is the `k0 + (positions this call took)` that
`*xj` leaves — so a fresh call is the `k0 = 0` case of this clause and not the
definition the clause is written at. -/
def escapeExpandPost (args : List Value) (mem m : Mem) (v : Value) : Prop :=
  ∃ (b n dst err xp xj : Nat) (nps pos0 tab : Nat) (body : List UInt8) (ps : List Nat)
    (err0 : Nat) (k0 : Nat),
    args = [.ptr b, .int 64 (BitVec.ofNat 64 n), .ptr dst, .ptr err, .ptr xp,
      .ptr xj, .int 64 (BitVec.ofNat 64 nps), .int 64 (BitVec.ofNat 64 pos0),
      .ptr tab] ∧
    readBytes mem b n = some body ∧
    readBytes mem xp (4 * nps) = some (positionsBytes 4 ps) ∧
    readBytes mem err 8 = some (wordBytes 8 err0) ∧
    readBytes mem xj 8 = some (wordBytes 8 k0) ∧
    k0 ≤ nps ∧
    (match escapeDecodeGo body 0 k0 ((ps.map fun q => q - pos0).drop k0) [] with
     | .decoded out k =>
         v = .int 64 (BitVec.ofNat 64 out.length) ∧
         readBytes m dst out.length = some out ∧
         readBytes m xj 8 = some (wordBytes 8 k) ∧
         readBytes m err 8 = some (wordBytes 8 err0) ∧
         UnchangedOutside mem m [(dst, n + 64), (xp, 4 * nps), (xj, 8), (err, 8)]
     | .refused off k =>
         v = .int 64 (BitVec.allOnes 64) ∧
         readBytes m err 8 = some (wordBytes 8 off) ∧
         readBytes m xj 8 = some (wordBytes 8 k) ∧
         UnchangedOutside mem m [(dst, n + 64), (xp, 4 * nps), (xj, 8), (err, 8)])

/-- The expander's boundary record.

Its `pre` is the caller's staging and carries all three obligations the measurement
of this unit forced, and the escape table the rewritten body reads.  The list clause
is the exact one: `xp` holds this body's `escapePositions`, in order, and `*xj` is a
cursor into it.  Readability reaches thirty-two bytes past `b + n`.

**The ninth argument is the table base, and it is a parameter rather than a
constant.** The fixture has no module-level globals, so the capture appends `%tab`
to the bodies that read it: the decoder dereferences `tab + e` for every byte after
a backslash, *before* it decides whether that byte is a two-character escape.  An
eight-argument call leaves the parameter unbound and every body containing an escape
is `ub`, which is why the record names it and promises the table's content —
`unescapeTable`, stated from `simpleEscape`, so the table the body reads and the
rule `escapeDecode` applies cannot disagree.  The pipeline supplies that table at
its call site; a mismatched table is then a failed `pre` rather than a silently
wrong decode.

The destination's extent is `dst` through the decoded length plus sixty-four bytes,
and the record asks for `dst + n + 64`: the number `kernel/json/escape.h` promises
the caller allocates, and not a bound the caller chooses.  That number is the extent
the body reaches only because a decode never writes more than the body holds: a raw
copy writes exactly the bytes it advances past, and every escape form is at most as
long as the bytes it consumes, so the written length is at most `n` for a resumed
call as well as a fresh one.  The fresh call's form of that inequality is
`escapeDecode_length_le` under the spacing `Spaced`, and the spacing argument is
local to each position, so which positions the call starts at does not enter it.

**The spacing is derived, and `escapeExpand_spaced` is the witness.** A body's
own position list is spaced, which is what makes `escapeDecode_length_le` apply to
the fresh call's decode: no byte between a position and the bytes its escape
consumes is a control byte or a run-starting backslash — the escape character is one
of `"\/bfnrtu`, all above `0x1F`, and where it is a backslash its predecessor was
one too, so the run parity refuses it; the hexadecimal digits are `0-9A-Fa-f`, none
of them either; and the only position inside a surrogate pair's twelve bytes is the
second `\u` at `q + 6`, which the walk drops.  Stating `n + 64` rather than a
smaller, caller-chosen extent is deliberate: a contract narrower than the store the
body reaches is the one defect no `post` can repair, so the clause is stated at the
ABI's boundary and the derivation carries the proof, not a narrower claim.

The store regions are also stated apart from the body, because a decode that wrote
over its own input would satisfy the byte claims while destroying the caller's
document.

**Four further exclusions were added by executing the body, not by reading it.**
A staging the earlier `pre` admitted was run on the pinned body and the `post` was
false at it: `tab` inside the destination extent (the raw copy's sixty-four-byte
write reaches the table entry a later `\"` escape reads), `err` inside it (the copy
overwrites the offset the `post` claims unchanged), `err` and `xj` the same slot
(the trailing cursor store overwrites the caller's offset), and `xj` inside the
claimed prefix (the cursor store is the last write of every successful path, so it
overwrites decoded bytes and no ordering saves the pair).  The clauses are stated
over the extents the body touches — `tab + 256`, `err + 8`, `xj + 8` and
`dst + n + 64` — rather than the base pointers, because an overlap of the bases
alone changes nothing; what matters is whether the written window reaches a region
the body later reads or the `post` reads back.  The falsifying stagings are the
rows of `tests/escape-expand-matrix.lean`.  Strengthening a `pre` is safe for a
consumer that proves `pre → …`, but every place that *constructs* this `pre` must
discharge the new clauses: the pipeline's call site does so when it stages the
destination, the table, the offset slot and the cursor as disjoint extents, and a
caller that does not is outside the record rather than silently admitted.

**`pos0` stays in the boundary.** The list clause is a relation between the
caller's list and the body: every entry of `ps` lies inside `[pos0, pos0 + n)`, and
`ps` with `pos0` subtracted is exactly the body's `escapePositions`. That covers any
offset the ABI admits — a document-level list at a block offset is a `pre` this
record admits, not a caller outside it — and it discharges at `pos0 = 0` as its own
special case. `escapeDecode` stays free of `pos0`, because the body's positions are
what the specification is about; the offset is the caller's, and this clause is
where it is stated.

The range condition is also what keeps the measured list-driven path's underflow out
of the contract: an entry inside an escape the previous one consumed would be an
entry the rebased list does not have, so the clause refuses that staging rather than
the proof having to notice it.

**The end offset fits the position width: `pos0 + n ≤ 2 ^ 32`.** The body forms
`%add = pos0 + n` with a 64-bit add and reads each position through a `uint32` load,
while this record's `n`, `pos0` and `nps` are Nats used untruncated. One bound
settles all of it: the add cannot wrap, every entry is below `2 ^ 32` because
`pos0 ≤ q < pos0 + n`, and `n`, `pos0` and `nps` are the canonical arguments (`nps`
too, since `ps.length = (escapePositionsFrom body st).length ≤ n`). Without it a
caller could stage a position the body reads truncated or an end offset the add
wraps, and the walk the record claims would not be the walk the body takes — the
same defect the list record's `blk0 * 64 + 64 < 2 ^ 32` excludes from the list side.
A pipeline that walks blocks in order satisfies it at every call: its `pos0` is the
list's block base and `n` is at most the block's sixty-four bytes.
-/
def Γ_escape_expand (budget : List Value → Mem → Nat) : MemContract where
  budget := budget
  pre := fun args mem _ =>
    ∃ (b n dst err xp xj : Nat) (nps pos0 tab : Nat) (body : List UInt8) (ps : List Nat)
      (err0 : Nat) (k0 : Nat),
      args = [.ptr b, .int 64 (BitVec.ofNat 64 n), .ptr dst, .ptr err, .ptr xp,
        .ptr xj, .int 64 (BitVec.ofNat 64 nps), .int 64 (BitVec.ofNat 64 pos0),
        .ptr tab] ∧
      -- the body
      readBytes mem b n = some body ∧
      -- the list is exactly this body's escape positions, rebased onto the body:
      -- every entry inside the body's window, and what is left after subtracting
      -- the window's offset is the body's own position list
      readBytes mem xp (4 * nps) = some (positionsBytes 4 ps) ∧
      nps = ps.length ∧
      (∀ q ∈ ps, pos0 ≤ q ∧ q < pos0 + n) ∧
      ps.map (fun q => q - pos0) = escapePositionsFrom body ⟨true, false⟩ ∧
      -- the body's end offset fits the position width: `%add = pos0 + n` is a
      -- 64-bit add and every position is read through a `uint32` load, so this
      -- one bound makes the add unwrap, every entry fit its word, and `n`,
      -- `pos0` and `nps` canonical Nat arguments.  The list record's
      -- `blk0 * 64 + 64 < 2 ^ 32` is the same fact from the list side.
      pos0 + n ≤ 2 ^ 32 ∧
      -- the cursor is a cursor
      readBytes mem xj 8 = some (wordBytes 8 k0) ∧ k0 ≤ nps ∧
      readBytes mem err 8 = some (wordBytes 8 err0) ∧
      -- the escape table the rewritten decoder reads, at the rule's own table
      readBytes mem tab 256 = some unescapeTable ∧
      -- thirty-two readable bytes past the body
      HasBytes mem (b + n) 32 ∧
      -- the destination extent: the body's length plus sixty-four bytes, which is
      -- the number the header promises the caller allocates
      HasBytes mem dst (n + 64) ∧
      -- and the store regions apart from the body and from the list
      (b + n + 32 ≤ dst ∨ dst + n + 64 ≤ b) ∧
      (xp + 4 * nps ≤ dst ∨ dst + n + 64 ≤ xp) ∧
      -- the table, the offset slot and the cursor, apart from the destination
      -- extent: each of these rows was executed on the pinned body at a staging
      -- the earlier `pre` admitted, and the `post` was false at it
      (tab + 256 ≤ dst ∨ dst + n + 64 ≤ tab) ∧
      (err + 8 ≤ dst ∨ dst + n + 64 ≤ err) ∧
      (err + 8 ≤ xj ∨ xj + 8 ≤ err) ∧
      (xj + 8 ≤ dst ∨ dst + n + 64 ≤ xj)
  post := fun args mem _ o =>
    match o with
    | .ret (some v) m => escapeExpandPost args mem m v
    | _ => False

/-- The expander's record refuses `ub`: its `post` is `False` at that outcome. -/
theorem escape_expand_ub_false (budget : List Value → Mem → Nat) (args : List Value)
    (mem : Mem) (next : Nat) :
    ¬ (Γ_escape_expand budget).post args mem next .ub := by
  intro h; exact h

/-- The expander's record is **not** value-irrelevant: the decoded length, or the
refusal marker, is the return value.  That is what tells the two entry points apart
in the bridges — the list's record takes the void bridge and this one the value
bridge. -/
theorem escape_expand_post_value {args : List Value} {mem m : Mem} {v : Value}
    (h : escapeExpandPost args mem m v) :
    ∃ (b n dst err xp xj nps pos0 tab : Nat) (body : List UInt8),
      args = [.ptr b, .int 64 (BitVec.ofNat 64 n), .ptr dst, .ptr err, .ptr xp,
        .ptr xj, .int 64 (BitVec.ofNat 64 nps), .int 64 (BitVec.ofNat 64 pos0),
        .ptr tab] ∧
      readBytes mem b n = some body := by
  obtain ⟨b, n, dst, err, xp, xj, nps, pos0, tab, body, ps, err0, k0, hargs, hbody, _⟩ := h
  exact ⟨b, n, dst, err, xp, xj, nps, pos0, tab, body, hargs, hbody⟩

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Vellum.escape_positions_ub_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escape_positions_ub_false

/-- info: 'LeanLLVM.Vellum.escape_positions_valueIrrelevant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escape_positions_valueIrrelevant

/-- info: 'LeanLLVM.Vellum.escape_expand_ub_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms escape_expand_ub_false

/-- info: 'LeanLLVM.Vellum.escape_expand_post_value' depends on axioms: [propext] -/
#guard_msgs in
#print axioms escape_expand_post_value

/-- info: 'LeanLLVM.Vellum.unescapeTable' does not depend on any axioms -/
#guard_msgs in
#print axioms unescapeTable

/-- info: 'LeanLLVM.Vellum.blockPositions' depends on axioms: [propext] -/
#guard_msgs in
#print axioms blockPositions


/-! ### The spacing of a body's own position list

`escapeDecode_length_le` bounds a decode's output by the body's length only when the
position list is spaced, and the expander's record leans on that bound for the
destination extent.  This section derives the spacing for a body's own
`escapePositionsFrom … ⟨true, false⟩`: the escape at each position fixes where the
next position can be, so the list never steps inside an escape it has not consumed.
The analysis is by the escape's shape (`escapeAt_cases`), and the position list is
put in a cursor form (`escAt`) so the induction can say where it resumes.

The cursor form and the cursor lemmas are stated here because they are the
instrument the derivation needs; nothing outside this section reads them.
-/

-- The escape-shape inversion nests deeply enough that the kernel's default
-- recursion budget is not sufficient for its own reduction.
set_option maxRecDepth 8000 in
theorem isControlB_false_of_not_le {d : UInt8} (h : ¬ d ≤ 0x1F) : IsControlB d = false := by
  simp [IsControlB, h]

theorem isBackslashB_false_of_ne {d : UInt8} (h : d ≠ 0x5C) : IsBackslashB d = false := by
  simp [IsBackslashB, h]

theorem isQuoteB_false_of_ne {d : UInt8} (h : d ≠ 0x22) : IsQuoteB d = false := by
  simp [IsQuoteB, h]

theorem hexDigit_bounds {d : UInt8} {v : Nat} (h : hexDigit d = some v) :
    (48 ≤ d.toNat ∧ d.toNat ≤ 57) ∨ (65 ≤ d.toNat ∧ d.toNat ≤ 70) ∨
      (97 ≤ d.toNat ∧ d.toNat ≤ 102) := by
  unfold hexDigit at h
  split at h
  · rename_i hb
    refine Or.inl ⟨?_, ?_⟩
    · have := UInt8.le_iff_toNat_le.mp hb.1
      rwa [show (0x30 : UInt8).toNat = 48 from rfl] at this
    · have := UInt8.le_iff_toNat_le.mp hb.2
      rwa [show (0x39 : UInt8).toNat = 57 from rfl] at this
  · split at h
    · rename_i hb
      refine Or.inr (Or.inl ⟨?_, ?_⟩)
      · have := UInt8.le_iff_toNat_le.mp hb.1
        rwa [show (0x41 : UInt8).toNat = 65 from rfl] at this
      · have := UInt8.le_iff_toNat_le.mp hb.2
        rwa [show (0x46 : UInt8).toNat = 70 from rfl] at this
    · split at h
      · rename_i hb
        refine Or.inr (Or.inr ⟨?_, ?_⟩)
        · have := UInt8.le_iff_toNat_le.mp hb.1
          rwa [show (0x61 : UInt8).toNat = 97 from rfl] at this
        · have := UInt8.le_iff_toNat_le.mp hb.2
          rwa [show (0x66 : UInt8).toNat = 102 from rfl] at this
      · simp at h

theorem hexDigit_not_control {d : UInt8} {v : Nat} (h : hexDigit d = some v) :
    IsControlB d = false := by
  apply isControlB_false_of_not_le
  intro hle
  have hd : d.toNat ≤ 0x1F := UInt8.le_iff_toNat_le.mp hle
  have hb := hexDigit_bounds h
  rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

theorem hexDigit_not_backslash {d : UInt8} {v : Nat} (h : hexDigit d = some v) :
    IsBackslashB d = false := by
  apply isBackslashB_false_of_ne
  intro hd
  subst hd
  have hb := hexDigit_bounds h
  rw [show (0x5C : UInt8).toNat = 92 from rfl] at hb
  rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

theorem hexDigit_not_quote {d : UInt8} {v : Nat} (h : hexDigit d = some v) :
    IsQuoteB d = false := by
  apply isQuoteB_false_of_ne
  intro hd
  subst hd
  have hb := hexDigit_bounds h
  rw [show (0x22 : UInt8).toNat = 34 from rfl] at hb
  rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

theorem hex4_lt {bs : List UInt8} {k cp : Nat} (h : hex4 bs k = some cp) :
    k + 4 ≤ bs.length := by
  unfold hex4 at h
  split at h
  · rename_i d0 d1 d2 d3 h0 h1 h2 h3
    have := lt_length_of_getElem?_eq_some h0
    have := lt_length_of_getElem?_eq_some h3
    omega
  · simp at h

theorem hex4_bytes {bs : List UInt8} {k cp : Nat} (h : hex4 bs k = some cp) :
    ∃ (d0 d1 d2 d3 : UInt8) (v0 v1 v2 v3 : Nat),
      bs[k]? = some d0 ∧ bs[k+1]? = some d1 ∧ bs[k+2]? = some d2 ∧ bs[k+3]? = some d3 ∧
      hexDigit d0 = some v0 ∧ hexDigit d1 = some v1 ∧ hexDigit d2 = some v2 ∧
      hexDigit d3 = some v3 := by
  unfold hex4 at h
  split at h
  · rename_i d0 d1 d2 d3 h0 h1 h2 h3
    split at h
    · rename_i v0 v1 v2 v3 g0 g1 g2 g3
      exact ⟨d0, d1, d2, d3, v0, v1, v2, v3, h0, h1, h2, h3, g0, g1, g2, g3⟩
    · simp at h
  · simp at h

theorem surrogateTail_snd {bs : List UInt8} {q cp cp' a : Nat}
    (h : surrogateTail bs q cp = some (cp', a)) : a = 12 := by
  unfold surrogateTail at h
  split at h
  · split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact h.2.symm
      · cases h
    · cases h
  · cases h

theorem surrogateTail_bounds {bs : List UInt8} {q cp cp' a : Nat}
    (h : surrogateTail bs q cp = some (cp', a)) : q + 12 ≤ bs.length := by
  unfold surrogateTail at h
  split at h
  · rename_i hc
    exact hc.2.2.1
  · simp at h

theorem surrogateTail_bytes {bs : List UInt8} {q cp cp' a : Nat}
    (h : surrogateTail bs q cp = some (cp', a)) :
    bs[q+6]? = some 0x5C ∧ bs[q+7]? = some 0x75 ∧ ∃ lo, hex4 bs (q+8) = some lo := by
  unfold surrogateTail at h
  split at h
  · rename_i hc
    obtain ⟨h6, h7⟩ : bs[q+6]? = some 0x5C ∧ bs[q+7]? = some 0x75 :=
      ⟨hc.2.2.2.1, hc.2.2.2.2⟩
    refine ⟨h6, h7, ?_⟩
    split at h
    · rename_i lo hl
      exact ⟨lo, hl⟩
    · cases h
  · simp at h

theorem classStep_inside_of_not_quote {st : ClassState} {b : UInt8}
    (h : IsQuoteB b = false) : (classStep st b).inside = st.inside := by
  simp [classStep, inStringAfter, isUnescapedQuote, h]

theorem classStep_odd_of_backslash {st : ClassState} {b : UInt8}
    (h : IsBackslashB b = true) : (classStep st b).oddRun = !st.oddRun := by
  simp [classStep, h]

theorem classStep_odd_of_not_backslash {st : ClassState} {b : UInt8}
    (h : IsBackslashB b = false) : (classStep st b).oddRun = false := by
  simp [classStep, h]

theorem utf8Encode_length_le_six (c : Nat) : (utf8Encode c).length ≤ 6 := by
  by_cases h1 : c < 0x80
  · rw [utf8Encode_eq_one h1]; simp
  · by_cases h2 : c < 0x800
    · rw [utf8Encode_eq_two h1 h2]; simp
    · by_cases h3 : c < 0x10000
      · rw [utf8Encode_eq_three h1 h2 h3]; simp
      · rw [utf8Encode_eq_four h1 h2 h3]; simp



def laneAt (bs : List UInt8) (st : ClassState) (k : Nat) : Bool :=
  match bs[k]? with
  | some b => IsEscapeLane (classCarryAt bs st k) b
  | none => false



theorem lane_false_of {st : ClassState} {b : UInt8}
    (hc : IsControlB b = false) (hq : IsBackslashB b = false) :
    IsEscapeLane st b = false := by
  simp [IsEscapeLane, hc, hq]

theorem lane_false_of_odd {st : ClassState} {b : UInt8}
    (hc : IsControlB b = false) (ho : st.oddRun = true) :
    IsEscapeLane st b = false := by
  simp [IsEscapeLane, hc, ho]

/-- A position whose byte is not a control byte is a backslash run start: the
byte is `0x5C`, the run parity on entry is even, and the lane is inside a
string. -/
theorem lane_backslash_of {bs : List UInt8} {st : ClassState} {q : Nat} {b : UInt8}
    (hb : bs[q]? = some b) (hq : laneAt bs st q = true) (hnc : IsControlB b = false) :
    b = 0x5C ∧ (classCarryAt bs st q).oddRun = false ∧ (classCarryAt bs st q).inside = true := by
  unfold laneAt at hq
  rw [hb] at hq
  unfold IsEscapeLane at hq
  rw [Bool.and_eq_true] at hq
  obtain ⟨hins, hrest⟩ := hq
  rw [hnc, Bool.false_or, Bool.and_eq_true] at hrest
  obtain ⟨hbs, hodd⟩ := hrest
  have hbeq : b = 0x5C := by simpa [IsBackslashB] using hbs
  have hodd' : (classCarryAt bs st q).oddRun = false := by
    cases h : (classCarryAt bs st q).oddRun <;> simp_all
  have hins' : (classCarryAt bs st q).inside = true := by
    unfold inStringAfter at hins
    rw [hbeq] at hins
    simpa [isUnescapedQuote, IsQuoteB] using hins
  exact ⟨hbeq, hodd', hins'⟩

/-- After a run-starting backslash, the next lane is not a position: the run
parity is odd there. -/
theorem lane_next_of_backslash {bs : List UInt8} {st : ClassState} {q : Nat}
    (hb : bs[q]? = some 0x5C) (hodd : (classCarryAt bs st q).oddRun = false)
    (hq1 : bs[q+1]? = some 0x5C) : laneAt bs st (q + 1) = false := by
  have hstep : classCarryAt bs st (q + 1) = classStep (classCarryAt bs st q) 0x5C := by
    rw [classCarryAt_succ, hb]
  have hodd1 : (classCarryAt bs st (q + 1)).oddRun = true := by
    rw [hstep, classStep_odd_of_backslash (by decide), hodd]
    simp
  unfold laneAt
  rw [hq1]
  exact lane_false_of_odd (by decide) hodd1

/-- A hexadecimal digit is not a position. -/
theorem lane_of_hex {bs : List UInt8} {st : ClassState} {k : Nat} {d : UInt8} {v : Nat}
    (hb : bs[k]? = some d) (hg : hexDigit d = some v) : laneAt bs st k = false := by
  unfold laneAt
  rw [hb]
  exact lane_false_of (hexDigit_not_control hg) (hexDigit_not_backslash hg)

/-- The `u` of a `\u` escape is not a position. -/
theorem lane_of_u {bs : List UInt8} {st : ClassState} {k : Nat}
    (hb : bs[k]? = some 0x75) : laneAt bs st k = false := by
  unfold laneAt
  rw [hb]
  exact lane_false_of (by decide) (by decide)

/-- Four hexadecimal digits are four lanes, none of them a position. -/
theorem hex4_lane_false {bs : List UInt8} {st : ClassState} {k0 cp : Nat}
    (h : hex4 bs k0 = some cp) {k : Nat} (h1 : k0 ≤ k) (h2 : k < k0 + 4) :
    laneAt bs st k = false := by
  obtain ⟨d0, d1, d2, d3, v0, v1, v2, v3, hb0, hb1, hb2, hb3, hg0, hg1, hg2, hg3⟩ :=
    hex4_bytes h
  rcases (show k = k0 ∨ k = k0 + 1 ∨ k = k0 + 2 ∨ k = k0 + 3 from by omega) with
    rfl | rfl | rfl | rfl
  · exact lane_of_hex hb0 hg0
  · exact lane_of_hex hb1 hg1
  · exact lane_of_hex hb2 hg2
  · exact lane_of_hex hb3 hg3



theorem simpleEscape_literal {c b : UInt8} (h : simpleEscape c = some b) :
    c = 0x22 ∨ c = 0x5C ∨ c = 0x2F ∨ c = 0x62 ∨ c = 0x66 ∨ c = 0x6E ∨ c = 0x72 ∨
      c = 0x74 := by
  unfold simpleEscape at h
  split at h
  · rename_i hc; exact Or.inl hc
  · split at h
    · rename_i hc; exact Or.inr (Or.inl hc)
    · split at h
      · rename_i hc; exact Or.inr (Or.inr (Or.inl hc))
      · split at h
        · rename_i hc; exact Or.inr (Or.inr (Or.inr (Or.inl hc)))
        · split at h
          · rename_i hc; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc))))
          · split at h
            · rename_i hc; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc)))))
            · split at h
              · rename_i hc; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc))))))
              · split at h
                · rename_i hc; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hc))))))
                · simp at h

theorem simpleEscape_not_control {c b : UInt8} (h : simpleEscape c = some b) :
    IsControlB c = false := by
  rcases simpleEscape_literal h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- At the sixth byte of a surrogate pair's first half, the lane is a position:
the run parity has been reset by the intervening digits and the string state has
not flipped. -/
theorem lane_pair_sixth {bs : List UInt8} {st : ClassState} {q cp : Nat}
    (hbq : bs[q]? = some 0x5C)
    (hins : (classCarryAt bs st q).inside = true)
    (hb1 : bs[q+1]? = some 0x75)
    (hx : hex4 bs (q+2) = some cp)
    (h6 : bs[q+6]? = some 0x5C) :
    laneAt bs st (q + 6) = true := by
  obtain ⟨d0, d1, d2, d3, v0, v1, v2, v3, hb2, hb3, hb4, hb5, hg0, hg1, hg2, hg3⟩ := hex4_bytes hx
  have h1 : classCarryAt bs st (q + 1) = classStep (classCarryAt bs st q) 0x5C := by
    rw [classCarryAt_succ, hbq]
  have h2 : classCarryAt bs st (q + 2) = classStep (classCarryAt bs st (q + 1)) 0x75 := by
    rw [show q + 2 = (q + 1) + 1 from by omega, classCarryAt_succ, hb1]
  have h3 : classCarryAt bs st (q + 3) = classStep (classCarryAt bs st (q + 2)) d0 := by
    rw [show q + 3 = (q + 2) + 1 from by omega, classCarryAt_succ, hb2]
  have h4 : classCarryAt bs st (q + 4) = classStep (classCarryAt bs st (q + 3)) d1 := by
    rw [show q + 4 = (q + 3) + 1 from by omega, classCarryAt_succ, hb3]
  have h5 : classCarryAt bs st (q + 5) = classStep (classCarryAt bs st (q + 4)) d2 := by
    rw [show q + 5 = (q + 4) + 1 from by omega, classCarryAt_succ, hb4]
  have h6c : classCarryAt bs st (q + 6) = classStep (classCarryAt bs st (q + 5)) d3 := by
    rw [show q + 6 = (q + 5) + 1 from by omega, classCarryAt_succ, hb5]
  have hodd6 : (classCarryAt bs st (q + 6)).oddRun = false := by
    rw [h6c, classStep_odd_of_not_backslash (hexDigit_not_backslash hg3)]
  have hins6 : (classCarryAt bs st (q + 6)).inside = true := by
    rw [h6c, h5, h4, h3, h2, h1]
    rw [classStep_inside_of_not_quote (hexDigit_not_quote hg3),
      classStep_inside_of_not_quote (hexDigit_not_quote hg2),
      classStep_inside_of_not_quote (hexDigit_not_quote hg1),
      classStep_inside_of_not_quote (hexDigit_not_quote hg0),
      classStep_inside_of_not_quote (by decide : IsQuoteB (0x75 : UInt8) = false),
      classStep_inside_of_not_quote (by decide : IsQuoteB (0x5C : UInt8) = false),
      hins]
  unfold laneAt
  rw [h6]
  unfold IsEscapeLane inStringAfter isUnescapedQuote
  rw [hins6, hodd6]
  decide

/-- A two-character escape's second byte is not a position. -/
theorem no_lane_simple {bs : List UInt8} {st : ClassState} {q : Nat} {c1 b : UInt8}
    (hbq : bs[q]? = some 0x5C) (hodd : (classCarryAt bs st q).oddRun = false)
    (h1 : bs[q+1]? = some c1) (hs : simpleEscape c1 = some b) :
    laneAt bs st (q + 1) = false := by
  by_cases hc : c1 = 0x5C
  · subst hc
    exact lane_next_of_backslash hbq hodd h1
  · unfold laneAt
    rw [h1]
    exact lane_false_of (simpleEscape_not_control hs) (isBackslashB_false_of_ne hc)

/-- A `\u` escape's four digits are not positions. -/
theorem no_lane_six {bs : List UInt8} {st : ClassState} {q cp : Nat}
    (hb1 : bs[q+1]? = some 0x75) (hx : hex4 bs (q+2) = some cp) :
    ∀ k, q + 1 ≤ k → k < q + 6 → laneAt bs st k = false := by
  intro k hk1 hk2
  rcases Nat.eq_or_lt_of_le hk1 with heq | hlt
  · rw [← heq]
    exact lane_of_u hb1
  · exact hex4_lane_false hx (by omega) (by omega)

/-- In a surrogate pair, the only position strictly inside the twelve bytes is
the second escape's backslash at `q + 6`. -/
theorem no_lane_twelve {bs : List UInt8} {st : ClassState} {q cp cp' a : Nat}
    (hb1 : bs[q+1]? = some 0x75) (hx : hex4 bs (q+2) = some cp)
    (ht : surrogateTail bs q cp = some (cp', a)) :
    ∀ k, q + 1 ≤ k → k < q + 12 → k ≠ q + 6 → laneAt bs st k = false := by
  intro k hk1 hk2 hkne
  obtain ⟨h6, h7, lo, hy⟩ := surrogateTail_bytes ht
  rcases Nat.lt_or_ge k (q + 6) with hlt | hge
  · rcases Nat.eq_or_lt_of_le hk1 with heq | hlt2
    · rw [← heq]
      exact lane_of_u hb1
    · exact hex4_lane_false hx (by omega) (by omega)
  · have hgt : q + 6 < k := Nat.lt_of_le_of_ne hge (fun h => hkne h.symm)
    have hle : q + 7 ≤ k := Nat.succ_le_of_lt hgt
    rcases Nat.eq_or_lt_of_le hle with heq | hlt2
    · rw [← heq]
      exact lane_of_u h7
    · exact hex4_lane_false hy (by omega) (by omega)
def escAt (bs : List UInt8) (st : ClassState) (i : Nat) : List Nat :=
  (List.range bs.length).filter fun k => decide (i ≤ k) && laneAt bs st k

/-- The cursor predicate is the lane decision once the cursor is behind it. -/
theorem pred_lane_of {bs : List UInt8} {st : ClassState} {i k : Nat} (h : i ≤ k) :
    (decide (i ≤ k) && laneAt bs st k) = laneAt bs st k := by
  rw [decide_eq_true h, Bool.true_and]

/-- The cursor predicate is false in front of the cursor. -/
theorem pred_false_of {bs : List UInt8} {st : ClassState} {i k : Nat} (h : ¬ (i ≤ k)) :
    (decide (i ≤ k) && laneAt bs st k) = false := by
  rw [decide_eq_false h, Bool.false_and]

theorem escapePositionsFrom_eq_escAt (bs : List UInt8) (st : ClassState) :
    escapePositionsFrom bs st = escAt bs st 0 := rfl

theorem mem_escAt {bs : List UInt8} {st : ClassState} {i k : Nat} :
    k ∈ escAt bs st i ↔ i ≤ k ∧ k < bs.length ∧ laneAt bs st k = true := by
  unfold escAt laneAt
  rw [List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hlt, hp⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    refine ⟨hp.1, hlt, ?_⟩
    cases hb : bs[k]? with
    | none => simp [hb] at hp
    | some b => simpa [hb] using hp.2
  · rintro ⟨hik, hlt, hp⟩
    refine ⟨hlt, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hik, ?_⟩
    cases hb : bs[k]? with
    | none => simp [hb] at hp
    | some b => simpa [hb] using hp

theorem escAt_head_lt {bs : List UInt8} {st : ClassState} {i q : Nat} {qs : List Nat}
    (h : escAt bs st i = q :: qs) : q < bs.length := by
  have : q ∈ escAt bs st i := by rw [h]; exact List.mem_cons_self ..
  exact (mem_escAt.mp this).2.1

theorem escAt_head_ge {bs : List UInt8} {st : ClassState} {i q : Nat} {qs : List Nat}
    (h : escAt bs st i = q :: qs) : i ≤ q := by
  have : q ∈ escAt bs st i := by rw [h]; exact List.mem_cons_self ..
  exact (mem_escAt.mp this).1

theorem escAt_head_lane {bs : List UInt8} {st : ClassState} {i q : Nat} {qs : List Nat}
    (h : escAt bs st i = q :: qs) : laneAt bs st q = true := by
  have : q ∈ escAt bs st i := by rw [h]; exact List.mem_cons_self ..
  exact (mem_escAt.mp this).2.2


/-- The range is strictly increasing. -/
theorem range_pairwise_lt (n : Nat) : List.Pairwise (fun x y => x < y) (List.range n) := by
  induction n with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
      rw [List.range_succ, List.pairwise_append]
      refine ⟨ih, by simp, ?_⟩
      intro a ha b hb
      simp at hb
      subst hb
      rw [List.mem_range] at ha
      omega

/-- A filter whose predicate fails everywhere is empty. -/
theorem filter_eq_nil_mpr {α : Type} {p : α → Bool} {l : List α}
    (h : ∀ x ∈ l, ¬ p x = true) : List.filter p l = [] := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      rw [List.filter_cons_of_neg (h a (by simp))]
      exact ih (fun x hx => h x (by simp [hx]))

/-- A filter over a list with no positive element before `a`, with `a` positive,
is `a` and then the filter of the rest. -/
theorem filter_append_cons {α : Type} {p : α → Bool} {l₁ l₂ : List α} {a : α}
    {as : List α} (hneg : ∀ x ∈ l₁, ¬ p x = true) (hp : p a = true)
    (hfl : List.filter p l₂ = as) :
    List.filter p (l₁ ++ a :: l₂) = a :: as := by
  rw [List.filter_append, filter_eq_nil_mpr hneg, List.nil_append,
    List.filter_cons_of_pos hp, hfl]

/-- In a strictly increasing list, the tail of a filter after its head is the
filter of the elements above the head.  The head is the least element, so the
only thing the tail loses is the head itself. -/
theorem filter_tail_eq {l : List Nat} {p : Nat → Bool} {q : Nat} {qs : List Nat}
    (hpw : List.Pairwise (fun x y => x < y) l) (h : List.filter p l = q :: qs) :
    qs = List.filter (fun k => p k && decide (q < k)) l := by
  induction l with
  | nil => simp at h
  | cons a as ih =>
      rw [List.pairwise_cons] at hpw
      obtain ⟨halt, hpwas⟩ := hpw
      by_cases hpa : p a = true
      · rw [List.filter_cons_of_pos hpa] at h
        simp only [List.cons.injEq] at h
        obtain ⟨hqa, hqs⟩ := h
        subst hqa
        have hneg1 : ¬ (fun k => p k && decide (a < k)) a = true := by
          show ¬ (p a && decide (a < a)) = true
          rw [hpa, decide_eq_false (show ¬ a < a from by omega), Bool.and_false]
          simp
        rw [← hqs, List.filter_cons_of_neg (p := fun k => p k && decide (a < k))
          (a := a) (l := as) hneg1]
        apply List.filter_congr
        intro x hx
        have hax : a < x := halt x hx
        rw [decide_eq_true hax, Bool.and_true]
      · have hpa' : p a = false := by
          cases hp : p a <;> simp_all
        rw [List.filter_cons_of_neg hpa] at h
        have hneg2 : ¬ (fun k => p k && decide (q < k)) a = true := by
          show ¬ (p a && decide (q < a)) = true
          rw [hpa', Bool.false_and]
          simp
        rw [ih hpwas h, List.filter_cons_of_neg (p := fun k => p k && decide (q < k))
          (a := a) (l := as) hneg2]

/-- The range splits at a lane: everything below it, the lane, and everything
above it. -/
theorem range_eq_split {n q : Nat} (h : q < n) :
    List.range n = List.range q ++ q ::
      List.map (fun i => q + 1 + i) (List.range (n - (q + 1))) := by
  have hn : n = (q + 1) + (n - (q + 1)) := by omega
  conv => lhs; rw [hn]
  rw [List.range_add, List.range_succ, List.append_assoc]
  rfl

/-- The tail of the cursor list after a head is the cursor list at the next
lane.  The head is the least element at or past the cursor, so nothing in
between is a position and the two filters agree. -/
theorem escAt_tail {bs : List UInt8} {st : ClassState} {i q : Nat} {qs : List Nat}
    (h : escAt bs st i = q :: qs) : qs = escAt bs st (q + 1) := by
  have hiq : i ≤ q := escAt_head_ge h
  have h' : List.filter (fun k => decide (i ≤ k) && laneAt bs st k) (List.range bs.length)
      = q :: qs := h
  have hD := filter_tail_eq (l := List.range bs.length)
    (p := fun k => decide (i ≤ k) && laneAt bs st k) (range_pairwise_lt bs.length) h'
  rw [hD]
  unfold escAt
  apply List.filter_congr
  intro k hk
  rw [List.mem_range] at hk
  by_cases hlk : laneAt bs st k = true
  · rw [hlk, Bool.and_true, Bool.and_true]
    by_cases hqk : q < k
    · rw [decide_eq_true hqk, decide_eq_true (show i ≤ k from by omega),
        decide_eq_true (show q + 1 ≤ k from by omega)]
      simp
    · rw [decide_eq_false hqk, decide_eq_false (show ¬ (q + 1 ≤ k) from by omega)]
      simp
  · have hlk' : laneAt bs st k = false := by
      cases h : laneAt bs st k <;> simp_all
    rw [hlk', Bool.and_false, Bool.false_and, Bool.and_false]

/-- Between two cursors with no position in the interval, the cursor list is the
same. -/
theorem escAt_congr {bs : List UInt8} {st : ClassState} {a b : Nat} (hab : a ≤ b)
    (hnone : ∀ k, a ≤ k → k < b → laneAt bs st k = false) :
    escAt bs st a = escAt bs st b := by
  unfold escAt
  apply List.filter_congr
  intro k hk
  rw [List.mem_range] at hk
  by_cases hb : b ≤ k
  · have ha : a ≤ k := by omega
    rw [pred_lane_of (i := a) ha, pred_lane_of (i := b) hb]
  · by_cases ha : a ≤ k
    · have hlane : laneAt bs st k = false := hnone k ha (by omega)
      rw [pred_lane_of (i := a) ha, pred_false_of (i := b) hb, hlane]
    · rw [pred_false_of (i := a) ha, pred_false_of (i := b) hb]

/-- Between two cursors with exactly one position in the interval, the cursor
list is that position and then the later cursor list. -/
theorem escAt_cons {bs : List UInt8} {st : ClassState} {a b q6 : Nat}
    (haq : a ≤ q6) (hq6b : q6 < b) (hq6 : laneAt bs st q6 = true)
    (hnone : ∀ k, a ≤ k → k < b → k ≠ q6 → laneAt bs st k = false) :
    escAt bs st a = q6 :: escAt bs st b := by
  have hq6len : q6 < bs.length := by
    unfold laneAt at hq6
    split at hq6
    · rename_i bb hb
      exact lt_length_of_getElem?_eq_some hb
    · simp at hq6
  have hp_a : (decide (a ≤ q6) && laneAt bs st q6) = true := by
    rw [pred_lane_of haq, hq6]
  have hneg : ∀ x ∈ List.range q6, ¬ (decide (a ≤ x) && laneAt bs st x) = true := by
    intro x hx
    rw [List.mem_range] at hx
    by_cases hax : a ≤ x
    · have hl : laneAt bs st x = false := hnone x hax (by omega) (by omega)
      have hfalse : (decide (a ≤ x) && laneAt bs st x) = false := by
        rw [pred_lane_of hax, hl]
      rw [hfalse]; simp
    · have hfalse : (decide (a ≤ x) && laneAt bs st x) = false := pred_false_of hax
      rw [hfalse]; simp
  have hfl : List.filter (fun k => decide (a ≤ k) && laneAt bs st k)
        (List.map (fun i => q6 + 1 + i) (List.range (bs.length - (q6 + 1))))
      = escAt bs st b := by
    unfold escAt
    have hq6false : (decide (b ≤ q6) && laneAt bs st q6) = false :=
      pred_false_of (by omega)
    have h1 : List.filter (fun k => decide (b ≤ k) && laneAt bs st k) (List.range q6) = [] := by
      apply filter_eq_nil_mpr
      intro x hx
      rw [List.mem_range] at hx
      have hfalse := pred_false_of (bs := bs) (st := st) (i := b) (k := x) (by omega)
      rw [hfalse]; simp
    have h2 : List.filter (fun k => decide (b ≤ k) && laneAt bs st k)
          (q6 :: List.map (fun i => q6 + 1 + i) (List.range (bs.length - (q6 + 1))))
        = List.filter (fun k => decide (b ≤ k) && laneAt bs st k)
          (List.map (fun i => q6 + 1 + i) (List.range (bs.length - (q6 + 1)))) :=
      List.filter_cons_of_neg (p := fun k => decide (b ≤ k) && laneAt bs st k)
        (a := q6) (by simpa using hq6false)
    have hR : List.filter (fun k => decide (b ≤ k) && laneAt bs st k) (List.range bs.length)
        = List.filter (fun k => decide (b ≤ k) && laneAt bs st k)
          (List.map (fun i => q6 + 1 + i) (List.range (bs.length - (q6 + 1)))) := by
      rw [range_eq_split hq6len, List.filter_append, h1, h2]
      simp
    rw [hR]
    apply List.filter_congr
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    have hax : a ≤ q6 + 1 + j := by omega
    by_cases hxb : b ≤ q6 + 1 + j
    · rw [pred_lane_of hax, pred_lane_of (i := b) hxb]
    · have hl : laneAt bs st (q6 + 1 + j) = false :=
        hnone (q6 + 1 + j) hax (by omega) (by omega)
      rw [pred_lane_of hax, pred_false_of (i := b) hxb, hl]
  unfold escAt
  have hmain : List.filter (fun k => decide (a ≤ k) && laneAt bs st k) (List.range bs.length)
      = q6 :: escAt bs st b := by
    conv => lhs; rw [range_eq_split hq6len]
    exact filter_append_cons hneg hp_a hfl
  exact hmain

-- The escape-shape inversion nests deeply enough that the kernel's default
-- recursion budget does not suffice for its own reduction.
set_option maxRecDepth 8000 in
/-- The escape at a position has one of the three measured shapes: a
two-character escape, a `\u` escape that reads as its own code unit, or a
surrogate pair.  Each case names the bytes the body holds at the positions the
shape consumes. -/
theorem escapeAt_cases {bs : List UInt8} {q : Nat} {bytes : List UInt8} {adv : Nat}
    (h : escapeAt bs q = some (bytes, adv)) :
    (∃ (c1 b : UInt8), bs[q+1]? = some c1 ∧ simpleEscape c1 = some b ∧
        bytes = [b] ∧ adv = 2)
    ∨ (∃ (cp : Nat), bs[q+1]? = some 0x75 ∧ hex4 bs (q+2) = some cp ∧
        surrogateTail bs q cp = none ∧ bytes = utf8Encode cp ∧ adv = 6)
    ∨ (∃ (cp cp' a : Nat), bs[q+1]? = some 0x75 ∧ hex4 bs (q+2) = some cp ∧
        surrogateTail bs q cp = some (cp', a) ∧ bytes = utf8Encode cp' ∧ adv = a) := by
  rw [escapeAt.eq_def] at h
  split at h
  · simp at h
  · rename_i c1 hq1
    split at h
    · rename_i b hs1
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact Or.inl ⟨c1, b, hq1, hs1, h.1.symm, h.2.symm⟩
    · rename_i hs1
      split at h
      · rename_i hc
        split at h
        · simp at h
        · rename_i cp hx
          split at h
          · rename_i cp' a hy
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            exact Or.inr (Or.inr ⟨cp, cp', a, by rw [hq1, hc], hx, hy, h.1.symm, h.2.symm⟩)
          · rename_i hy
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            exact Or.inr (Or.inl ⟨cp, by rw [hq1, hc], hx, hy, h.1.symm, h.2.symm⟩)
      · simp at h

/-- Every cursor list is spaced: the body's position list, read from any cursor,
has the spacing the length bound uses.  The induction is on the distance still to
run, and at each step the escape at the head fixes where the next position can
be: a two-character escape, a `\u` escape's four digits, and the second `\u` of a
surrogate pair. -/
theorem escAt_spaced (bs : List UInt8) (st : ClassState) :
    ∀ (n i : Nat), bs.length - i ≤ n → Spaced bs i (escAt bs st i) := by
  intro n
  induction n with
  | zero =>
    intro i hi
    have hnil : escAt bs st i = [] := by
      unfold escAt
      apply filter_eq_nil_mpr
      intro k hk
      rw [List.mem_range] at hk
      have hfalse : (decide (i ≤ k) && laneAt bs st k) = false := pred_false_of (by omega)
      rw [hfalse]
      simp
    rw [hnil]
    exact Spaced.nil i
  | succ n ih =>
    intro i hi
    cases hcons : escAt bs st i with
    | nil =>
        exact Spaced.nil i
    | cons q qs =>
        have hiq : i ≤ q := escAt_head_ge hcons
        have hqlen : q < bs.length := escAt_head_lt hcons
        have hq : laneAt bs st q = true := escAt_head_lane hcons
        have htail : qs = escAt bs st (q + 1) := escAt_tail hcons
        cases hb : bs[q]? with
        | none => simp [laneAt, hb] at hq
        | some b =>
          have hq' : IsEscapeLane (classCarryAt bs st q) b = true := by
            simpa [laneAt, hb] using hq
          by_cases hctl : IsControlB b = true
          · exact Spaced.control i q qs b hiq hb hctl
          · have hctl' : IsControlB b = false := by
              cases h : IsControlB b <;> simp_all
            obtain ⟨hbeq, hodd, hins⟩ := lane_backslash_of hb hq hctl'
            have hbq5C : bs[q]? = some 0x5C := by rw [hb, hbeq]
            cases hesc : escapeAt bs q with
            | none =>
                exact Spaced.refuse i q qs hiq hqlen hesc
            | some p =>
              obtain ⟨bytes, adv⟩ := p
              rcases escapeAt_cases hesc with hc1 | hc2 | hc3
              · obtain ⟨c1, b', h1, hs, hbytes, hadv⟩ := hc1
                subst hbytes
                subst hadv
                refine Spaced.step i q qs 2 [b'] b hiq hb hctl' hesc ?_ ?_ ?_
                · simp
                · have := lt_length_of_getElem?_eq_some h1
                  omega
                · rw [if_neg (by decide), htail]
                  have hcongr : escAt bs st (q + 1) = escAt bs st (q + 2) :=
                    escAt_congr (by omega) (by
                      intro k hk1 hk2
                      have hk : k = q + 1 := by omega
                      subst hk
                      exact no_lane_simple hbq5C hodd h1 hs)
                  rw [hcongr]
                  exact ih (q + 2) (by omega)
              · obtain ⟨cp, hb1, hx, ht, hbytes, hadv⟩ := hc2
                subst hbytes
                subst hadv
                refine Spaced.step i q qs 6 (utf8Encode cp) b hiq hb hctl' hesc ?_ ?_ ?_
                · exact utf8Encode_length_le_six cp
                · have := hex4_lt hx
                  omega
                · rw [if_neg (by decide), htail]
                  have hcongr : escAt bs st (q + 1) = escAt bs st (q + 6) :=
                    escAt_congr (by omega) (no_lane_six hb1 hx)
                  rw [hcongr]
                  exact ih (q + 6) (by omega)
              · obtain ⟨cp, cp', a, hb1, hx, ht, hbytes, hadv⟩ := hc3
                subst hbytes
                have ha12 : a = 12 := surrogateTail_snd ht
                subst ha12
                subst hadv
                obtain ⟨h6c, h7c, lo, hy⟩ := surrogateTail_bytes ht
                refine Spaced.step i q qs 12 (utf8Encode cp') b hiq hb hctl' hesc ?_ ?_ ?_
                · have := utf8Encode_length_le_six cp'
                  omega
                · exact surrogateTail_bounds ht
                · rw [if_pos rfl, htail]
                  have hpair : escAt bs st (q + 1) = (q + 6) :: escAt bs st (q + 12) :=
                    escAt_cons (by omega) (by omega) (lane_pair_sixth hbq5C hins hb1 hx h6c)
                      (no_lane_twelve hb1 hx ht)
                  rw [hpair]
                  simp only [List.drop_succ_cons, List.drop_zero]
                  exact ih (q + 12) (by omega)

/-- A body's own escape positions are spaced: this is the witness
`escapeDecode_length_le` needs, so the bound applies to every body. -/
theorem escapePositionsFrom_spaced (bs : List UInt8) :
    Spaced bs 0 (escapePositionsFrom bs ⟨true, false⟩) := by
  rw [escapePositionsFrom_eq_escAt]
  exact escAt_spaced bs ⟨true, false⟩ bs.length 0 (by omega)

/-- **The cursor list after a prefix is the cursor list at a later cursor.**  A
drop of the filtered list is the same filter read from the entry it stops at: the
tail after a head is the cursor list at `q + 1` (`escAt_tail`), so dropping one
entry moves the cursor to the next lane and the induction is that fact. -/
theorem escAt_drop_exists (bs : List UInt8) (st : ClassState) :
    ∀ (i k : Nat), ∃ i' : Nat, (escAt bs st i).drop k = escAt bs st i' := by
  intro i k
  induction k generalizing i with
  | zero => exact ⟨i, rfl⟩
  | succ k ih =>
      cases h : escAt bs st i with
      | nil => exact ⟨i, by simp [h]⟩
      | cons q qs =>
          have htail : qs = escAt bs st (q + 1) := escAt_tail h
          obtain ⟨i', hi'⟩ := ih (q + 1)
          refine ⟨i', ?_⟩
          rw [List.drop_succ_cons, htail]
          exact hi'

/-- **The walk's remaining positions are spaced.**  The staging decodes
`(ps.map …).drop k0` — the position list after its first `k0` entries — and
`Spaced` is not suffix-closed on the nose: a `control` or `refuse` constructor's
tail is unconstrained, so the suffix of a spaced list need not be spaced by `Spaced`
alone.  What carries the spacing across the drop is that the list is the body's own
position list: every cursor list is spaced (`escAt_spaced`), and a drop of one is
the cursor list at a later lane (`escAt_drop_exists`).  The prefix monoticity that
turns the later cursor into the resumed walk's own — the walk's byte cursor starts
at zero regardless of how many positions the caller has already consumed — is
`Spaced.mono`.

This is the fact the final copy needs: without it the copy's destinations are not
confined to the record's `dst + n + 64` extent, because the resumed walk's decoded
prefix could be longer than the byte cursor it resumes at. -/
theorem escAt_drop_spaced (bs : List UInt8) (st : ClassState) (i k : Nat) :
    Spaced bs 0 ((escAt bs st i).drop k) := by
  obtain ⟨i', hi'⟩ := escAt_drop_exists bs st i k
  rw [hi']
  exact Spaced.mono (escAt_spaced bs st (bs.length - i') i' (Nat.le_refl _))
    (Nat.zero_le _)

/-- Every `(body, ps)` the expander's record admits is spaced: the record's list
clause identifies the decode's position list with the body's own, so the length
bound covers the decode the record claims. -/
theorem escapeExpand_spaced {body : List UInt8} {ps : List Nat} {pos0 : Nat}
    (h : ps.map (fun q => q - pos0) = escapePositionsFrom body ⟨true, false⟩) :
    Spaced body 0 (ps.map (fun q => q - pos0)) := by
  rw [h]
  exact escapePositionsFrom_spaced body

/-- **The resumed walk's spacing**, from the record's list clause.  A call that
resumes at position cursor `k0` decodes the caller's list after its first `k0`
entries, and that suffix is spaced for the same reason the whole list is: the entries
are the body's own lanes.  Stated at the invariant's own classifier state, because
`DecodeInv`'s walk is written at `escAt body st 0`. -/
theorem escapeExpand_spaced_drop {body : List UInt8} {ps : List Nat} {pos0 : Nat}
    {st : ClassState}
    (h : ps.map (fun q => q - pos0) = escapePositionsFrom body st) (k : Nat) :
    Spaced body 0 ((ps.map (fun q => q - pos0)).drop k) := by
  rw [h]
  exact escAt_drop_spaced body st 0 k

-- The spacing is stated from the body's own position rule, so its footprint is the
-- standard one: no carrier beyond `propext` and `Quot.sound`.
/-- info: 'LeanLLVM.Vellum.escapePositionsFrom_spaced' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapePositionsFrom_spaced

/-- info: 'LeanLLVM.Vellum.escAt_drop_exists' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escAt_drop_exists

/-- info: 'LeanLLVM.Vellum.escAt_drop_spaced' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escAt_drop_spaced

/-- info: 'LeanLLVM.Vellum.escapeExpand_spaced' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapeExpand_spaced

/-- info: 'LeanLLVM.Vellum.escapeExpand_spaced_drop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapeExpand_spaced_drop

/-- info: 'LeanLLVM.Vellum.escapeAt_cases' depends on axioms: [propext] -/
#guard_msgs in
#print axioms escapeAt_cases


end LeanLLVM.Vellum
