# Entry positions: the `ent` word and the two position emitters

The entry unit is measured code, and what this file claims is about the object
the measurement compiled: for a stream of 64-bit entry masks and a starting
cursor it writes each mask's set lanes, as positions, into a caller's buffer.
The headline theorems are stated over the emitted texts
`probes/install/ir/json-entry.candidate.ll`, pinned to hand-written ASTs:
`entry_pos8_refines` in `LeanLLVM/Vellum/JsonEntrySteps.lean`, and
`entry_b8_refines`, `entry_pos8_b8_agree` and `entry_b8_undefined_of_no_read` in
`LeanLLVM/Vellum/JsonB8Steps.lean`; `LeanLLVM/Vellum/JsonEntryIR.lean` holds the
fixture pin, `entryCalls`, the `pos8Table` definition and `entry_tail_eq`.  These
scenarios are the other half of that claim, where the subject is reached from
outside rather than read as a proposition.

There are two actors both outside the subject:

* the object arm — `probes/json/entry_driver.c`, a separate executable that calls
  `leanllvm_json_entry_pos8` and `leanllvm_json_entry_b8` through the compiled
  object and prints what the object wrote.  It calls `leanllvm_json_entry_table`
  once before the first row, because the table the POS8 body reads is filled by
  the unit's own `xl_pos8_init` and nothing else calls it;
* the runner `leanllvm-json-entry`, which executes the pinned ASTs through
  `runFuel` and prints what the bodies wrote.

One row is one `(mask stream, blk0, nblk, k)` call under one kernel.  Both
actors print a row as

```
<source>\t<label>\t<kernel>\t<count>\t<words>\t<multi>\t<sentinel>
```

`source` is the corpus path as given, or `arm:<arm>`; `label` names the row;
`kernel` is `p` for POS8 and `b` for B8; `count` is the returned cursor `k'`;
`words` is the first `k'` `i32` words, `0x` and exactly eight lowercase hex
digits each, comma-separated, or `-` when `k'` is `0`; `multi` is `1` when a
block of the stream has more than eight set lanes; and `sentinel` is the word at
lane `k'+8`, the first lane neither kernel writes.  Two columns are
scaffolding, admitted for the reason this record gives: `multi` because JE3's
set assertion must name the rows a cut tail loop can move, and `sentinel`
because the bound clause is otherwise unobservable from the row stream.
Neither is trusted: `check.sh` derives both from the corpus bytes and from each
arm's label, and asserts them.

Every output buffer is pre-filled with `0xA5`, so a store the body does not
make — and the word at `k'+8` — read back as `0xa5a5a5a5`; a row whose cursor
starts at `k` therefore begins with `k` sentinel words.  The region `[k', k'+8)`
is deliberately **not** compared: POS8 stores eight lanes per group
unconditionally, so its last store, at the final cursor, reaches `k'+7`, while
B8's eight fixed slots per block reach `k'+6`; those lanes hold table-row
padding and block bases rather than positions.  The sentinel at `k'+8` is what
proves the body stopped inside that bound.

The Lean files are

    nix develop -c lake env lean tests/vector-entry.lean
    nix develop -c lake env lean tests/json-entry.lean

and the route is

    nix develop -c bash tests/json-entry/check.sh

The first imports `LeanLLVM` only and holds JE1's parser half; the second
imports `LeanLLVM.Vellum.JsonEntryIR` and holds the fixture pin, JE2 and JE3,
including the four clause witnesses.  Every observation is a `#guard`, so a
failed one stops elaboration with a nonzero exit status.  The Lean files reach
no compiler, proof checker, service, clock or network; `check.sh` invokes
`clang` on committed sources into a private temporary directory, reads the
committed corpus, and regenerates the fixture from the kernel source with the
repository's capture script, restoring the committed bytes on exit.

### JE1 — the admitted spellings parse, and their neighbours are refused by name

The admission set here is the instruction inventory the entry emission actually
has, plus the store the model already writes but the parser refused: today the
parser refuses a vector `store` at any width but `<n x i1>`, and its intrinsic
check — `checkIntrinsicShape`, five families, `pshuf.b`, `pclmulqdq`, `pext.64`,
`pdep.64` and `ctlz.i64`, each at symbol, arity, operand-type and immediate
positions — does not cover `ctpop.*` or `cttz.i64`, so an intrinsic in those two
families parses with the wrong arity, width or flag.  Those are the two holes
this scenario states; the second is closed by extending the checker with two
families, not by adding a checker.

- **Actor:** the parser, given one function text per construct.
- **Boundary:** `parseModule` on a text.  The parser is a separate unit from both
  the producer (`clang`) and the body (the AST), so "accepted" and "refused" are
  its two external outcomes.  Nothing is run.
- **Given:** six **accepted** and nine **refused** function texts, in
  `tests/vector-entry.lean`.
  Accepted, one text each:
  1. `tail call i32 @llvm.ctpop.i32(i32 %x)` — the seven count sites a block's
     group bytes need;
  2. `tail call i64 @llvm.ctpop.i64(i64 %x)` — the block's own population count;
  3. `tail call i64 @llvm.cttz.i64(i64 %x, i1 true)` — every observed site's
     flag, the poison-carrying one;
  4. the same at `i1 false` — the flag is admitted at both values;
  5. `store <8 x i32> %v, ptr %p` — POS8's whole table-row store;
  6. `phi i64 [ 0, %a ], [ 1, %b ]` — an already-modelled control, so a failure
     elsewhere is not a failure of the harness.
  Refused, each the nearest spelling that is **not** modelled:
  1. `@llvm.ctpop.i16` — a width that is not the symbol's;
  2. `@llvm.cttz.i32` — the sibling width, likewise not the symbol's;
  3. `@llvm.ctpop.i32` with two arguments;
  4. `@llvm.cttz.i64` with no flag operand;
  5. `@llvm.cttz.i64(i64 %x, i64 0)` — the flag at the wrong type;
  6. `@llvm.ctlz.i64(i64 %x, i1 true)` — not observed, and no clause bounds its
     poison;
  7. `store <5 x i1> %c, ptr %p` — a total width that is not a whole number of
     bytes, refused by the width rule in both states;
  8. `store <8 x i32> %q, ptr %p` where `%q` is an `i64` — the written value's
     shape and the operand's disagree.  **Today** it is refused by the width
     rule, which admits a vector `store` only at `<n x i1>`, so its guards pass
     for a reason that is about to change; **after the widening** it is refused
     by the value-operand check: the register the function defines must match the
     store's written type, read through `Function.regType`.  The guards are the
     same either way and do not distinguish the two reasons;
  9. `store <8 x i64> %v, ptr %p` where `%v` is an `<8 x i32>` — a whole-byte
     total width, a disagreeing shape.  Same history as 8: refused today by the
     width rule, refused after the widening by the same value-operand check
     against `regType`.  It is the text that separates a widening which validates
     width only from one which validates the operand's type as well.
- **When:** `parseModule` is applied to each text.
- **Then:** each accepted text is `.ok`; each refused text is `.error` **and**
  its message contains the construct's own name — `ctpop`, `cttz`, `ctlz`,
  `store` — asserted as a second, separate guard so a failure says which half
  failed.  A refusal names the construct or the token it refused; the guard asks
  only that the name is present, never that it is the whole message.
- **Expected failure, as observed.**  Taken on the unfixed tree at `ad188ad`,
  and it was the red the record predicted: **eleven of the file's twenty-four
  guards failed** — the accepted vector `store`, and both guards of each of the
  five intrinsic neighbours the parser accepts today (`ctpop.i16`, `cttz.i32`,
  the two-argument `ctpop.i32`, `cttz` with no flag, `cttz` with `i64 0` as its
  flag).  The first failing guard was `accepted okStoreVec`, the parser
  answering `store of the vector value <8 x i32> is not modelled`; the ten
  naming/refusal guards then failed because `checkIntrinsicShape` has no
  `ctpop` or `cttz` family, so those five texts parsed unvalidated and there was
  no message to name anything.  The guards for `ctlz` with `i1 true` and for the
  three refused stores passed then and pass now, which is the direction they
  assert: those refusals predate the change.  For the two value-mismatch stores
  the reason is not the same in the two states — the width rule refuses them
  before the widening and the value-operand type check refuses them after it — so
  their passing is not evidence about which check is doing the work, only that
  the text is refused.
  Once the widening and the intrinsic validation land, the same twenty-four
  guards pass; the red stands in the run history, not in the tree.
  This is why the file imports `LeanLLVM` only and not the fixture module — so
  the red was an assertion rather than an unresolved import.
- **Not claimed:** that every unmodelled spelling is refused; that a message
  names *only* the construct; that the accepted texts are the only shapes the
  emission contains; anything about a body's meaning.
- **Where it lives:** `tests/vector-entry.lean`, which imports `LeanLLVM` only.
  The fixture-pin half — the text parses, `firstFunction` of it is exactly
  `entryPos8Function`, and the module's two functions are `entryPos8Function`
  and `entryB8Function` — stays in `tests/json-entry.lean`, which imports the
  module and is therefore reachable only after the pinned AST exists.  Two
  files, one record.

### JE2 — the POS8 object and the Lean body emit the same positions, row for row

- **Actor:** `probes/json/entry_driver.c`, linked against the object built from
  `kernel/json/entry.c`, and the runner `leanllvm-json-entry`.
- **Boundary:** the C ABI call — `leanllvm_json_entry_pos8(ent, blk0, nblk, out,
  k)` over the compiled object — and, on the other side, `runFuel entryCalls …`
  on the pinned AST.  A `When` that named `s1f_ke_pos8` or either body's blocks
  would be a unit test in scenario clothing.
- **Given:** committed mask streams derived from the corpus's block bytes
  (`tests/json-entry/corpus/*.json`, ten masks over six files, one stream staged
  at a nonzero `blk0` and one at a nonzero cursor); the 64 single-lane masks, one
  per lane, for placement; the 256 masks that set one group's byte to each of the
  256 values, so every table row is read and the table's *content* is compared
  rather than assumed; a fixed-seed arm of 65,536 masks; an empty-mask and a
  full-mask row; and one long-loop stream of 1025 masks — more blocks than a
  caller's chunk, all in one call, so the kernel's own loop runs long (`S1F_CHUNK`
  is the caller's chunk size and is not this unit's).  Every output buffer is pre-filled with `0xA5`.
- **When:** both actors are run over the same corpus files and the same arms, and
  the runner is also run with `--expect` over a tampered copy of its own rows.
- **Then:** for every row the returned count equals, the first `k'` words equal,
  and the word at lane `k'+8` — the first lane neither kernel writes — is still
  the sentinel in both actors.  The region `[k', k'+8)` is not compared (the
  overshoot bound: POS8 reaches `k'+7`, B8 `k'+6`); a body that wrote into lane
  `k'+8` would be outside its bound and shows there.  The row count is
  asserted, not printed: `2 * (corpus files + 65859)`, where 65859 is the arm
  streams 64 + 256 + 65536 + 2 + 1.  In the same run, each row's count and words
  are compared against the positions its own masks define — computed by the
  route from the committed bytes and from the arm's label — so agreement of the
  two actors is a second, independent layer rather than the only one; `multi`
  and the sentinel are derived and asserted the same way.  **One exception, named
  where the claim is made:** the 1025-mask `nblk` row's count, `multi` and
  sentinel are derived from the corpus bytes and asserted, but its words are
  covered only by the two actors agreeing.  Its expected word list runs to about
  65,600 words, and deriving it through the route's own `awk` to buy one row is
  the wrong trade; the row's masks are the corpus's own, and the corpus rows'
  words are derived and asserted, so what the exception gives up is bounded.  The
  committed fixture is regenerated from the same C at the pinned flags and
  byte-compared, a difference being a setup failure (exit 3) rather than an
  assertion result.
- **Expected failure:** the staged cut this record defines — the entry object
  replaced by a stub that returns `k` and writes nothing — measured once its
  subject exists, before the theorem is accepted.  At the base
  revision the object, the driver and the runner do not exist, so the route
  exits 3 (a setup state) and this scenario's red is not claimed here; that is
  recorded below and in `docs/json-route-evidence.md`, which the cut's
  observation reaches.
- **Why:** the theorem's subject is a body; the object is what a caller links.  A
  body that is right and an object that is not would leave the milestone's claim
  about the wrong artefact.
- **Not claimed:** anything about mask streams the arms and the corpus do not
  contain; the overshoot region's contents; the driver's or runner's row order
  beyond the two actors agreeing on it; the `nblk` row's words, as the Then
  states (its count, `multi` and sentinel are derived and asserted); the
  pipeline that calls this unit, and the selection between the two kernels.
- **Where it lives:** `tests/json-entry.lean` (the Lean-side half, which asserts
  one row's count, words and sentinel by hand rather than by comparison) and
  `tests/json-entry/check.sh` (the route).

### JE3 — the two kernels write one stream

- **Actor:** both objects through the driver, and both ASTs through the runner.
- **Boundary:** the same two C ABI calls and the same two `runFuel` applications
  as JE2, at the same rows.
- **Given:** the same mask streams, the same staging, and output buffers filled
  with the same sentinel.
- **When:** both kernels are run over each stream and their rows are read.
- **Then:** at every row both kernels return the same count and the same first
  `k'` words, and leave the same sentinel at `k'+8` — the one lane neither of
  them writes, so this is a claim about the shared untouched lane rather than
  about a lane one kernel writes and the other does not (POS8 reaches `k'+7`, B8
  `k'+6`); the header's claim that they "write the same position stream" is the
  assertion.  Their overshoot regions are not compared.
- **Expected failure:** the staged cut that replaces B8's object with a stub
  returning `k` — which moves every row a B8 body with more than eight set lanes
  reaches and no other.  Like JE2's, it is measured once its subject exists,
  before the theorem is accepted; at the base revision the actors are absent, so
  no red is claimed here.
- **Why:** a milestone that proved both kernels but shipped one of them wrong
  would satisfy the theorems and violate the interface the header states.
- **Not claimed:** that the two kernels are interchangeable in cost or in the
  overshoot they write; anything about which kernel a document is given.
- **Where it lives:** `tests/json-entry.lean` (the Lean-side half) and
  `tests/json-entry/check.sh` (the route).

## The red, as observed

`JE1`'s parser half produced the assertion-level red the record predicted.  On
the parser at `ad188ad`:

    nix develop -c lake env lean tests/vector-entry.lean
    exit 1

with eleven failed guards, the first being

    tests/vector-entry.lean:121:0: error: Expression
      accepted okStoreVec
    did not evaluate to `true`

and the other ten being the refusal and naming guards for `ctpop.i16`,
`cttz.i32`, the two-argument `ctpop.i32`, `cttz` with no flag and `cttz` with
`i64 0` as its flag, at `:218`–`:227`.  A one-off probe of the same parser on the
same texts confirmed the two causes: the vector store was refused with

    store of the vector value <8 x i32> is not modelled: the modelled vector
    store is an '<n x i1>' mask whose total width is a whole number of bytes

and `tail call i16 @llvm.ctpop.i16(i16 %x)` was accepted, `checkIntrinsicShape`
covering five intrinsic families and not `ctpop`.  The parser's rules have yet
to land; when they do, the same twenty-four guards pass, and this red stands in
the run history rather than in the tree.

`JE2` and `JE3` claim no pre-fix red, and the base revision does not offer one:
their subject — the entry object, the driver, the runner and
`LeanLLVM/Vellum/JsonEntryIR.lean` — does not exist at `ad188ad`.  The Lean file
therefore fails at its unresolved import, and the route exits 3, which are setup
states and not evidence:

    nix develop -c lake env lean tests/json-entry.lean
    tests/json-entry.lean:27:0: error: object file
      '…/.lake/build/lib/lean/LeanLLVM/Vellum/JsonEntryIR.olean' of module
      LeanLLVM.Vellum.JsonEntryIR does not exist
    exit 1

    nix develop -c bash tests/json-entry/check.sh
    SETUP: absent: …/probes/install/ir/json-entry.candidate.ll
    exit 3

Their red is the staged cut this record defines, and it can only be measured
once its subject exists — before the theorem is accepted.  The
durable record of that observation — the command, the build status, the first
failing row and the no-other-route condition — is `docs/json-route-evidence.md`.

## The corpus and its derivation

Each corpus file is one mask stream derived from a committed JSON document's
block bytes, not written by hand.  The documents are the stage-1 route's own
corpus, `tests/json-s1-masks/corpus/*.json`.  Each is partitioned into
consecutive 64-byte blocks — the unit `S1F_DEFINE_KERNEL` advances `blk0` by —
and the mask word's lane `i` is set iff the block's byte `i` is one of the eight
structural bytes `IsStructuralB` reads: `"` `0x22`, `\` `0x5c`, `:` `0x3a`,
`,` `0x2c`, `{` `0x7b`, `}` `0x7d`, `[` `0x5b`, `]` `0x5d`.  That is the
`S1F_GRAIN=1` structural granularity the measured header documents, so the
stream is a real entry-shaped input rather than arbitrary data; lanes past the
document's end are clear.

|File|Document|Bytes|Masks|`blk0`|`k`|
|---|---|---|---|---|---|
|`boundary-63.json`|`boundary-63.json`|63|1|0|0|
|`boundary-64.json`|`boundary-64.json`|64|1|0|0|
|`boundary-65.json`|`boundary-65.json`|65|2|0|0|
|`mixed.json`|`mixed.json`|98|2|0|0|
|`nested.json`|`nested.json`|81|2|3|0|
|`strings.json`|`strings.json`|93|2|0|5|

`blk0` and `k` are staging parameters: one stream is staged at a nonzero block
base and one at a nonzero cursor, so neither is assumed zero, and the sentinel
words at indices below `k` are visible in the row.

The six streams' masks contain no byte equal to `0x2c`, which is why the table
detector's set is carried by the generated group-byte arm: the 256 masks that set
one group's byte to each value are what guarantees every table row is read,
`0x2C`'s among them.

## The route's detectors

Two defect objects are built from `kernel/json/entry.c` itself, at the same
flags, in the same run, and each must disagree with the Lean body on exactly its
own set:

* **the table defect** gives `xl_pos8_init`'s row for mask `0x2C` first entry
  `1` where the measured rule gives `2` (`0x2C`'s set lanes are 2, 3 and 5).  The
  disagreement set is exactly the POS8 rows whose stream has a byte equal to
  `0x2c`, named by a predicate over the row's label, and no other row moves;
* **the B8 defect** cuts `s1f_ke_b8`'s tail loop, the epilogue that emits the
  positions past the eight fixed slots.  The disagreement set is exactly the B8
  rows whose stream has a block with more than eight set lanes, and no other
  row moves.

The first differing row is named and is the same row on two runs.  Both
mutations are textual, count the substitutions that land, and fail as setup
faults (exit 3) if the measured text they locate is not there exactly once — so
a source that drifted is refused rather than silently passing.

## Which artefact the route compiles

`check.sh` compiles `kernel/json/entry.c` with the pinned compiler line and calls
that object: the fixture's table base is a parameter (the capture rewrites
`@xl_pos8`'s GEPs to `%tab`), so an object built from the fixture would read a
table the caller does not own, and the object's own array is the thing the
route's claim is about.  The fixture is not ignored, though: in the same run it
is regenerated from that same C at those same flags and compared with the
committed bytes, and a difference is a setup failure (exit 3), not an assertion
failure.  The fixture is the theorem's subject; the source is the object's.

## Prerequisites

The route is runnable once its inputs exist; until then `check.sh` exits 3 with a
line naming the absent artefact, and a `FAIL` is never produced.  The inputs are:

- `kernel/json/entry.c` and `kernel/json/entry.h` — the extracted unit and the
  ABI header it publishes;
- `probes/install/ir/capture-entry.sh` — the capture that regenerates the
  fixture from that source at the pinned flags;
- `probes/install/ir/json-entry.candidate.ll` — the committed fixture, and at
  the same time the thing the capture must reproduce;
- `probes/json/entry_driver.c` — the object-side actor;
- `lakefile.toml`'s `lean_exe` stanza for `leanllvm-json-entry`, and the binary
  `lake build leanllvm-json-entry` writes at
  `.lake/build/bin/leanllvm-json-entry`;
- `LeanLLVM/Vellum/JsonEntryIR.lean` — the module that pins the ASTs, which
  `tests/json-entry.lean` imports and which nothing else in the tree provides.
