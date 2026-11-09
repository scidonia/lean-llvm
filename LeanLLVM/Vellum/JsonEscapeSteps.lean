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

* The two `post`s.  The list's pairs with the arm the caller chose — and the arm is
  a *selection between two clauses*, never a claim about a document's escapes: the
  suppressed arm says the count is zero and claims no position, and it says
  **nothing** about whether the document carries an escape.  The measurement of the
  unit refutes that reading on seven documents, so a record that assumed it would
  be false of the measured code.  The expander's names the decoded bytes, the list
  cursor it leaves, and — on a refusal — the body-relative offset, which is a stated
  outcome rather than an absence.

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
import LeanLLVM.Vellum.JsonEscapeSpec
import LeanLLVM.Vellum.JsonS1MasksIR
import LeanLLVM.Vellum.Refinement

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

/-- A little-endian array of positions, one `w`-byte entry each: the bytes a
position stream occupies. -/
def positionsBytes (w : Nat) (ps : List Nat) : List UInt8 :=
  (ps.map fun p => natToBytes p w).flatten

/-- An unsigned word as the bytes a slot holds. -/
def wordBytes (w : Nat) (v : Nat) : List UInt8 := natToBytes v w

/-- A boolean flag as the eight bytes a caller's carry slot holds. -/
def flagBytes (b : Bool) : List UInt8 := natToBytes (if b then 1 else 0) 8

/-- The document offset of a block's first byte: the position base the list entry
point is given, `blk0 << 6`. -/
def blockAddr (blk0 : BitVec 64) : Nat := blk0.toNat * 64

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

Two arms, one record: the arm is a parameter, so the clause a run must meet is
chosen by the caller and the difference between the arms is the contract's content
rather than a case analysis buried in a proof. -/

/-- The list's claim about the memory it leaves, in the built arm: the eight-entry
reserve the first batch writes is at `xp + 4 * xn0`, so the entries the run *claims*
start where the caller's count says the stream ends.  The positions are the block's
own, lifted by `blockAddr blk0`, because the store's positions are document offsets
and the specification's are block lanes.

The unchanged conjunct is over the extent the run wrote, which includes the batch
reserve the run touched. -/
def escapePositionsBuiltPost (args : List Value) (mem m : Mem) : Prop :=
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

/-- The list's claim in the suppressed arm: the count is zero and no position is
claimed.  It says **nothing** about the document's bytes, and that silence is a
clause: a record that asserted the document carries no escape would be false of the
measured code, which suppresses the list for documents that do carry one. -/
def escapePositionsSuppressedPost (args : List Value) (mem m : Mem) : Prop :=
  ∃ (xp xn carry : Nat) (blk0 : BitVec 64) (bs ctl im : BitVec 64) (xn0 : Nat),
    args = [.int 64 bs, .int 64 ctl, .int 64 im, .int 64 blk0, .ptr xp, .ptr xn,
      .ptr carry] ∧
    readBytes mem xn 8 = some (wordBytes 8 xn0) ∧
    readBytes m xn 8 = some (wordBytes 8 xn0) ∧
    UnchangedOutside mem m [(xp, 4 * (blockMax xn0)), (carry, 16)]

/-- The position list's boundary record, at an arm the caller chose.

Its `pre` is the caller's staging: the three masks are the block's classifier
words, the carry slot holds the pair the previous block left with the run parity
they spell, and the stream has room for the block's maximum plus the batch reserve.
The count is read in and out of its own slot; the reserve is inside the capacity and
outside the stream, so `pre` promises the room and `post` claims nothing about the
reserve's values.

The block itself is named in the caller's store because the claim is about **that**
block's positions, and the specification reads them off its bytes; the entry point
does not read the block, so this clause is not a readability obligation the body
has. -/
def Γ_escape_positions (budget : List Value → Mem → Nat) (arm : Bool) : MemContract where
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
      HasBytes mem xp (4 * blockMax xn0) ∧
      -- the position base is a `uint32` that does not truncate
      blk0.toNat * 64 + 64 < 2 ^ 32
  post := fun args mem _ o =>
    match o with
    | .ub => False
    | .ret _ m =>
        if arm then escapePositionsBuiltPost args mem m
        else escapePositionsSuppressedPost args mem m

/-- The list record refuses `ub` in both arms: its `post` is `False` at that
outcome, so "the record forbids undefined behaviour" is a proposition. -/
theorem escape_positions_ub_false (budget : List Value → Mem → Nat) (arm : Bool)
    (args : List Value) (mem : Mem) (next : Nat) :
    ¬ (Γ_escape_positions budget arm).post args mem next .ub := by
  intro h; exact h

/-- The list record's guarantee ignores the returned value, because the entry point
returns `void` and everything it says is about the memory it leaves. -/
theorem escape_positions_valueIrrelevant (budget : List Value → Mem → Nat) (arm : Bool) :
    ValueIrrelevant (Γ_escape_positions budget arm) := by
  intro args mem next v v' m
  cases arm <;> rfl

/-- The suppressed arm's clause leaves the count where the caller put it: no
position is appended, which is the whole of the arm's claim about the stream. -/
theorem escape_positions_suppressed_count {args : List Value} {mem m : Mem}
    (h : escapePositionsSuppressedPost args mem m) :
    ∃ (xn : Nat) (xn0 : Nat), readBytes m xn 8 = some (wordBytes 8 xn0) := by
  obtain ⟨xp, xn, carry, blk0, bs, ctl, im, xn0, _, _, hcount, _⟩ := h
  exact ⟨xn, xn0, hcount⟩

/-! ### The expander's record -/

/-- The decode's answer, in the two outcomes the measured signature distinguishes:
the decoded bytes with the cursor, or a refusal at a body-relative offset with the
same cursor. -/
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
    (match escapeDecode body (ps.map fun q => q - pos0) with
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
the body reaches only because a decode never writes more than the body holds, which
is `escapeDecode_length_le` under the spacing `Spaced`.

**The spacing itself is not yet derived, and this clause leans on it.** What is
missing is `Spaced body 0 (escapePositionsFrom body ⟨true, false⟩)`, and it needs the
escape-span analysis: no byte between a position and the bytes its escape consumes is
a control byte or a run-starting backslash — the escape character is one of
`"\/bfnrtu`, all above `0x1F`, and where it is a backslash its predecessor was one
too, so the run parity refuses it; the hexadecimal digits are `0-9A-Fa-f`, none of
them either; and the only position inside a surrogate pair's twelve bytes is the
second `\u` at `q + 6`, which the walk drops.  Stating `n + 64` rather than a
smaller, caller-chosen extent is deliberate: a contract narrower than the store the
body reaches is the one defect no `post` can repair, so the clause is stated at the
ABI's boundary and the derivation is owed as a proof, not as a narrower claim.

The store regions are also stated apart from the body, because a decode that wrote
over its own input would satisfy the byte claims while destroying the caller's
document.

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
      (xp + 4 * nps ≤ dst ∨ dst + n + 64 ≤ xp)
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

/-- info: 'LeanLLVM.Vellum.escape_positions_suppressed_count' does not depend on any axioms -/
#guard_msgs in
#print axioms escape_positions_suppressed_count

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

end LeanLLVM.Vellum
