# Stage-1 classification masks

The stage-1 kernel is measured code, and what this file claims is about the
object the measurement compiled: for one 64-byte block and one inbound carry it
computes six mask words and the outgoing carry.  The theorem in
`LeanLLVM/Vellum/JsonS1MasksIR.lean` is stated over the emitted text
`probes/install/ir/json-s1-masks.candidate.ll`, pinned to a hand-written AST;
these scenarios are the other half of that claim, where the subject is reached
from outside rather than read as a proposition.

There are two actors both outside the subject:

* the object arm — `probes/json/s1_masks_driver.c`, a separate executable that
  calls `leanllvm_json_s1_masks` through the compiled object and prints what the
  object wrote.  It restates the ABI rather than including `s1_block.h`, so a
  changed header cannot make the driver agree with itself;
* the runner `leanllvm-json-s1-masks`, which executes the pinned AST through
  `runFuel` and prints what the body wrote.

One row is: 64 block bytes, one inbound carry state, six mask words, three
outgoing carry words.  Both actors print a row as

```
<source>\t<label>\t<open>\t<ppar>\t<inside>\t<comma>\t<quote>\t<delim>\t<in_string>\t<ws>\t<backslash>\t<ctl>\t<esc_open>\t<esc_ppar>\t<im_carry>
```

`open`, `ppar`, `inside` and `comma` are `0` or `1`; the nine words are
`0x` and exactly sixteen lowercase hex digits.  `comma` is `1` when any lane of
the block is `0x2C`: it is the signal `JS5` uses to name the row set a table
byte for the comma class may move, and no other column is derived from the
block's content.  The inbound carry is the
kernel's three words: `open` is the run-open bit, `ppar` the run parity, and
`inside` is `im_carry` normalised to `0` or all-ones.  The state a row is run
under is `4*open + 2*ppar + inside`, so state `0` is clean, state `1` is inside
a string, and state `6` is an odd run open.  `ppar` is `1` in states 2, 3, 6
and 7.  With `open = 0` (states 2 and 3) it is indistinguishable from
`ppar = 0`, because the kernel's carry is the pair and the specification's is
`oddRun = open ∧ ppar`; those two rows are therefore redundant duplicates of
states 0 and 1, not distinct states.

Rows, in the order both actors print them:

1. the mixed 64-byte block, once per carry state, `source` = `mixed`, `label` =
   the state number;
2. `tests/json-s1-masks/corpus/*.json`, window by window and offset ascending,
   once per carry state, `source` = the path as given, `label` = the offset;
3. `source` = `arm:byte`: for each state, byte position `0…63` and value
   `0…255`, `label` = `pos<position>/val<two hex digits>/carry<state>`;
4. `source` = `arm:alphabet`: for each state, every 4-byte sequence over the
   sixteen-symbol class alphabet below, `label` = `<eight hex digits>/carry<state>`;
5. `source` = `arm:random`: for each state, 4096 blocks from a fixed seed,
   `label` = `idx<decimal>/carry<state>`.

The class alphabet is class-complete and boundary-complete:
`{0x00, 0x09, 0x0A, 0x0D, 0x1F, 0x20, 0x22, 0x2C, 0x3A, 0x5B, 0x5C, 0x5D,
0x7B, 0x7D, 0x61, 0x80}` — the control bytes at both ends of the control
range, all four whitespace bytes, the space, the quote, the comma, the colon,
the four brackets and braces, the backslash, an ordinary byte, and `0x80`, the
first non-ASCII byte.  Each 4-byte sequence is written at lanes 0–3 of a block
whose other 60 lanes are `0x78`.  The random arm is splitmix64 seeded at
`0x243F6A8885A308D3`, block `i` formed from the eight 64-bit words starting at
`seed + i * 0x9E3779B97F4A7C15`, each word little-endian.

Every window is staged at **offset 1** of a 96-byte buffer, so the object is
called on a misaligned pointer; the output slot is 48 bytes pre-filled with
`0xA5`, so a store the body does not make shows as a sentinel word rather than
as a stale value.

The Lean files are

    nix develop -c lake env lean tests/json-s1-parser.lean
    nix develop -c lake env lean tests/json-s1-masks.lean

and the route is

    nix develop -c bash tests/json-s1-masks/check.sh

The first imports `LeanLLVM` only and holds JS1's parser half; the second imports
the fixture module and holds JS1's pin, JS2 and JS3.  Every parser, block and
body assertion is a `#guard`, so a failed observation stops elaboration with a
nonzero exit status.  No compiler, proof checker, service, clock or network is
reached by the Lean files; `check.sh` invokes `clang` on committed sources into a
private temporary directory, reads the committed corpus, and regenerates the
fixture from the kernel source with the repository's capture script, restoring
the committed bytes on exit.

### JS1 — the admitted spellings parse, and their neighbours are refused by name

The admission set here is the inventory the emission actually has, not the
seven-form closure an earlier draft assumed — that closure was falsified by the
emission itself.  The fixture's text contains `shufflevector`, a vector `store`,
a non-mask vector `bitcast` at equal total width, the two-argument `pshuf.b`,
`pclmulqdq` at immediate 0, `pext.64`, `pdep.64`, `ctlz.i64` with `i1 false`,
and a vector `lshr`; vector `shl` is admitted as the widening's other direction
and is exercised as an accepted test text in `tests/json-s1-parser.lean`, not
emitted by this body.  The refused texts are the neighbouring unmodelled
spellings, one per form — vector `ashr` among them.  Changing element size is
**not** a refusal here: the emitted widening changes element size
(`<4 x i64>` → `<32 x i8>`) and equal *total* width is the criterion, so
refusing a changed element size would refuse the emitted form itself.

- **Actor:** the parser, given one function text per construct.
- **Boundary:** `parseModule` on a text.  The parser is a separate unit from
  both the producer (clang) and the body (the AST), so "accepted" and "refused"
  are its two external outcomes.  Nothing is run.
- **Given:** eleven **accepted** and thirteen **refused** function texts, in
  `tests/json-s1-parser.lean`.
  Accepted, one text each:
  1. `shufflevector <4 x i64> %a, %b, <8 x i32> <i32 0, i32 1, …, i32 7>` — a
     defined static permutation;
  2. `store <64 x i1> %m, ptr %p` — the vector store a packed mask needs;
  3. `bitcast <4 x i64> %v to <32 x i8>` — equal total width, changed element
     size;
  4. `call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8>, <32 x i8>)` — **two**
     arguments, the declaration's own arity;
  5. `call <2 x i64> @llvm.x86.pclmulqdq(<2 x i64>, <2 x i64>, i8 0)`;
  6. `call i64 @llvm.x86.bmi.pext.64(i64, i64)`;
  7. `call i64 @llvm.x86.bmi.pdep.64(i64, i64)`;
  8. `call i64 @llvm.ctlz.i64(i64, i1 false)`;
  9. `lshr <16 x i16> %a, splat (i16 4)`;
  10. `shl <16 x i16> %a, splat (i16 4)`;
  11. `icmp ult <64 x i8> %a, splat (i8 32)` — already modelled.
  Refused, each the nearest spelling that is *not* modelled:
  1. the same `shufflevector` with a mask entry at `2n` (`i32 8` at
     `<4 x i64>`);
  2. the same with an `undef` entry in the mask;
  3. `store <5 x i1> %m, ptr %p` — a total width that is not a whole number of
     bytes;
  4. `bitcast <4 x i64> %v to <16 x i8>` — unequal total width;
  5. `bitcast <4 x i64> %v to <8 x ptr>` — a vector of non-integer elements;
  6. `pshuf.b` with three arguments;
  7. `pclmulqdq` at `i8 1`;
  8. `pext.32`;
  9. `pdep.32`;
  10. `ctlz … i1 true`;
  11. `umin <32 x i8> %a, %a` — the emission contains no `umin`;
  12. `umax <32 x i8> %a, %a` — its sibling, likewise absent;
  13. `ashr <16 x i16> %a, splat (i16 4)` — the signed shift the widening does
      not admit.
- **When:** `parseModule` is applied to each text.
- **Then:** each accepted text is `.ok`, and each refused text is `.error`
  **and** its message names what it refused — asserted separately from the
  refusal, so a failure says which half failed.  The rule is that a refusal
  names the construct or the token it refused: `shufflevector`, `store`,
  `bitcast`, `pshuf.b`, `pclmulqdq`, `pext`, `pdep`, `ctlz`, `umin`, `umax`,
  `ashr`.  For `bitcast <4 x i64> %v to <8 x ptr>` the refusal is the
  destination *type*, refused at `Parser.lean:218`, so the message carrying
  `bitcast` **or** the refused element token `ptr` satisfies the guard; that
  text is a refusal witness, not a bitcast-naming one.
- **Expected failure:** two, both observed, and the first has since been
  discharged.  (i) An **assertion-level red**: **fifteen of the file's
  thirty-seven guards failed** on the parser as it stood before the closure
  landed (the red section below), and none was a scaffolding failure: five
  accepted controls — `shufflevector`, the vector `store`, the non-mask
  `bitcast`, and the two vector shifts — and five refused texts accepted as
  generic calls — three-argument `pshuf.b`, `pclmulqdq` at `i8 1`, `pext.32`,
  `pdep.32`, `ctlz … i1 true` — each failing both its refusal and its naming
  guard.  The parser's rules have landed, so the same thirty-seven guards pass
  with exit 0; that red stands in the run history, not in the tree.  That is why this
  half imports `LeanLLVM` only and not the fixture module — so the red was an
  assertion rather than an unresolved import; the module exists now.  (ii) Two
  **staged cuts** for the refusals, both observed: each was reached by this
  scenario file's own documented command and failed at that file's own
  assertions, with the unmodified tree at exit 0 as the control.  **Cut 1**
  removed `shufflevector`'s dispatch case (34 lines); the build then fails first
  at `JsonS1MasksIR`'s two **fixture pins** — collateral, not the red, because
  the committed fixture's text contains a `shufflevector`, so a parser that
  refuses it cannot parse that fixture.  With those two fixture pins dropped in
  the copy (never a scenario's bytes), the scenario fails at exactly one guard,
  `tests/json-s1-parser.lean:178`, `accepted okShuffle did not evaluate to
  true`, the parser answering `unsupported instruction 'shufflevector'`; the two
  refused `shufflevector` texts keep passing, because the catch-all still names
  the construct — the cut removed the *admission*, not the *naming*.  **Cut 2**
  replaced the refusal with `| "umax" => parseBinop dst .add`: the build is
  green, and `badUmax`'s two guards fire — at `:347` the refusal guard fails
  because the text now parses, and at `:348` the naming guard fails because
  there is no longer a message to name `umax` — with nothing else moved; the
  clean cut, kept beside the one that needs an explanation.  The pair is what
  the record says: **a build failure is not an assertion failure**, so the cut
  carrying collateral states which part was collateral and which was the red.
- **Why:** the theorem's subject is a text the parser accepts.  A silently
  accepted spelling is a body with a different instruction — exactly how the
  earlier record's three-argument `pshuf.b` and its `shufflevector` refusal went
  wrong.
- **Not claimed:** that every unmodelled spelling is refused; that a message
  names *only* the construct; anything about the body's meaning.
- **Where it lives:** the parser half is `tests/json-s1-parser.lean`, which
  imports `LeanLLVM` only, so five of its eleven accepted controls failed at
  their own assertion on the parser as it stood before the closure, instead of
  the file stopping at an unresolved import; the other six passed, five of them
  vacuously.  All eleven pass now.  The
  fixture-pin half — the text parses and `firstFunction` of it is exactly
  `s1MasksFunction`, with name `leanllvm_json_s1_masks`, return `void` and
  parameters `[("%p", ptr), ("%c", ptr), ("%o", ptr)]` — stays in
  `tests/json-s1-masks.lean`, which imports the module and is therefore
  reachable only after the pinned AST exists.  Two files, one record.

### JS2 — the body returns the hand-written six masks and carry for a mixed block under three carry states

- **Actor:** `runFuel`, running `s1MasksFunction` — the AST pinned from the
  fixture — under the repository's semantics.
- **Given:** a hand-written 64-byte block `blockBytes` whose bytes interleave
  quotes (unescaped and escaped), backslash runs of length one, two and three,
  all six delimiter classes, all four whitespace bytes, control bytes that are
  and are not whitespace, `0x7F`, and ordinary content; laid out as 64 bytes at
  address `8193` (offset 1 of the 96-byte buffer starting at `8192`), with the
  24-byte carry slot at `9200` and the 48-byte output slot at `9400` all
  pre-filled with `0xA5` except the three carry words.  Three carry states:
  clean (`open = ppar = inside = false`), inside a string (`inside = true`), and
  an odd run open (`open = ppar = true`).
- **When:** `runFuel s1Calls 10000 s1MasksFunction` is applied to that state —
  **not `noCalls`**: the body contains the five intrinsic calls, so `noCalls`
  answers `none` and every row is `ub`.  The environment is `JsonS1MasksIR`'s,
  the same one the theorem uses.
- **Then:** for each state the run returns, and, asserted separately per state
  so a failure names the state:
  1. the 48 output bytes are exactly the little-endian encoding of the six
     hand-written words, in the ABI's order — quote, delimiter, in-string,
     whitespace, backslash, control.  For the clean state these are
     `0x0401000490052001`, `0x00201E8800F84090`, `0xFC00FFFC70031FFF`,
     `0x0380601001000720`, `0x400E002120001804`, `0x1300401006000700`; for the
     inside-a-string state the third word is `0x03FF00038FFCE000` and the rest
     are unchanged; for the odd-run state the first word is
     `0x0401000490052000`, the third `0x03FF00038FFCE000`, and the rest are
     unchanged.  Every word is written out; none is read back from
     `classMask64` or `specQuote64`;
  2. the 24 carry-slot bytes are `0x0`, `0x0` and `0xFFFFFFFFFFFFFFFF` for the
     clean state, and `0x0`, `0x0`, `0x0` for the other two — the body leaves
     the string state open after the clean block and closed after the others;
  3. no byte outside the carry and output slots changed.
- **And three clause witnesses, each a separate `#guard` over an edited
  expectation**, so a failure names the clause:
  1. `quote_witness` — the first word complemented.  The run differs from it in
     **all three states**, so the output clause does not hold for a complemented
     quote word whichever carry enters;
  2. `delimiter_witness` — the delimiter word a body whose comma-class table
     bit is missing would report: every comma lane cleared.  The block's commas
     sit at lanes 4, 23, 35 and 53, so the clean state's hand-written
     `0x00201E8800F84090` becomes `0x00001E8000784080`, and the run differs from
     that expectation in the delimiter word.  The witness names that body, not
     an arbitrary perturbation;
  3. `carry_witness` — the in-string word with the inbound carry XORed in a
     second time.  In the **clean** state the carry is zero, so the witness is
     the unmodified expectation and the run *equals* it; in the **inside** state
     the carry is all-ones, so the witness is the word a carry-ignoring body
     would produce and the run *differs* from it.  The pair is the assertion: a
     witness that differed in both states would show only that the word can be
     perturbed, not that the clause depends on the carry.
- **Expected failure:** observed, as a staged cut.  In a throwaway copy of the
  tree, `s1MasksFunction`'s table entry for the comma class — `loTab`'s offset
  12, in both copies of the duplicated table — was cleared and the module
  rebuilt (`lake build LeanLLVM.Vellum.JsonS1MasksIR`, exit 0).  The scenario
  then exits 1.  The first failure is collateral: the scenario's own fixture pin
  at `tests/json-s1-masks.lean:38` fails, because the cut body no longer equals
  the committed text — the pin doing its job, not the red.  The scenario's own
  equality guards fail at `:157` (clean state), `:160` (inside a string) and
  `:163` (odd run open), each of the form
  `masksOf s1MasksFunction blockBytes <state> = some (slotBytes …, slotBytes …)`
  against its state's six words; at `:243` the `delimiter_witness` guard,
  because the cut body now produces exactly the witness word
  `0x00001E8000784080` — the witness refusing the body it names; and at `:252`
  the clean half of `carry_witness`, because the clean state's delimiter word
  moved.  The quote witness and the inside half of the carry witness keep
  passing, which is the direction they assert: this cut moves the delimiter word
  and nothing else.  The unmodified tree exits 0.
- **Why:** the theorem says the body computes the specification's masks; this
  scenario says the body computes the numbers a reader can check by hand, and
  the carry states are what separate a body that consults the inbound carry
  from one that does not.  Writing the expectations out is what keeps the
  assertion from being a restatement of the specification.
- **Not claimed:** the body on any block other than this one, and nothing about
  the kernel's aggregate over a stream of blocks.

### JS3 — the block layer's mask over the same block is the union of five hand-written words

- **Actor:** the block layer's own folds, `maskOfList` and `mask64`.
- **Given:** the same 64-byte block as JS2, split into its low and high 32-byte
  halves.
- **When:** `mask64 (maskOfList lo) (maskOfList hi)` is evaluated.
- **Then:** it equals the union of five hand-written 64-bit words —
  the unescaped-quote word, the escaped-quote word, the delimiter word, the
  backslash word and the whitespace word — namely
  `0x0401000490052001`, `0x8010004000000008`, `0x00201E8800F84090`,
  `0x400E002120001804` and `0x0380601001000720`, whose union is
  `0xC7BF7EFDB1FD7FBD`.  The five operands are asserted against the union in
  the same run, so the identity is between two written expressions and not
  between an expression and itself.
- **Post-fix invariant, not a red:** `maskOfList` and `mask64` predate the
  change, so this assertion also held at the base revision; passing there would
  be vacuous, and no pre-fix failure is claimed or available.  What the scenario
  buys is that the kernel's units are stated in the block layer's own
  vocabulary — the join of the two halves' `maskOfList` against the union of
  five written words — so a packing change on either side shows here rather than
  at a downstream consumer.
- **Why:** the kernel's result must be stated in `ScanBlock`'s vocabulary;
  if the kernel's words were packed differently from `maskOfList`, every
  downstream consumer of the block layer would be reading a mask the kernel
  never produced.
- **Not claimed:** that the body emits each of the five words (the carry-free
  ones are the body's stores, the escaped-quote word is derived), and nothing
  about `maskOfList` beyond this block.

### JS4 — the installed object agrees with the Lean body on every row

- **Actor:** `probes/json/s1_masks_driver.c`, linked against the object built
  from `kernel/json/s1_block.c`, and the runner `leanllvm-json-s1-masks`.
- **Given:** the committed corpus `tests/json-s1-masks/corpus/*.json`, the
  mixed block, and the three generated arms above, every window staged at
  offset 1 of a 96-byte buffer.
- **When:** both actors are run over the same corpus files and the same arms.
- **Then:** the two row streams are equal line for line, in order; the row
  count is asserted against the computed count
  `8 + 8 * corpus_windows + 131072 + 524288 + 32768`, where `corpus_windows` is
  computed from each file's size as `max(0, size - 63)` and the three
  boundary files are also asserted by name (63 → 0, 64 → 1, 65 → 2); and both
  actors' `--emit-block` outputs are the same 64 bytes, so the mixed block the
  two streams share is one block and not two.
- **Why:** the object is what a caller links; the proved body is what the
  theorem is about.  Agreement at the ABI, on a misaligned pointer, over every
  byte value in every lane position and every 4-byte class sequence, is what
  says the two are the same unit at the boundary a user reaches.
- **Not claimed:** anything about blocks the arms do not contain, and nothing
  about the pipeline that calls this unit.

### JS5 — the route's detectors bite

- **Actor:** `check.sh`, comparing the object's rows against the Lean body's
  rows, and the runner in `--expect` mode.
- **Given:** a control object built from `kernel/json/s1_block.c`, and a defect
  object built from a copy of that source with **bit 0 of `s1f_lo_tab[12]`
  flipped** — the entry for the low nibble of `,`, whose bit 0 only the comma
  class sets; and, separately, a tampered copy of the runner's own output.
- **When:** the defect object and the control object are each run over the
  corpus and the arms; and the runner is run with the tampered copy as its
  expectation.
- **Then:** the set of rows on which the defect disagrees with the control is
  **exactly** the set of rows whose `comma` column is `1` — every comma-carrying
  row moves and no comma-free row moves — the report names the first differing
  row, and two runs of the defect produce the same first differing row; and the
  tampered expectation exits nonzero,
  says `mismatch:` on stderr, names the row it disagrees with, and its stdout
  is byte-identical to the control's rows — so the disagreement is the
  expectation's, not the classification's.
- **Why:** a comparison that cannot fail is not evidence.  The defect moves the
  classification and the tamper moves only the expectation, so the two
  refusals cannot be produced by the same mistake.
- **Not claimed:** that the parameter *value* of any table entry is what the
  measured build writes; the defect's claim is only that the row set its bit 0
  can move is the comma set, which is what the assertion checks.  The corpus
  and random arms' bytes are not in their labels, so their comma column is
  verified only by the cross-actor comparison, not by the label-derived check
  that covers `arm:byte`, `arm:alphabet` and `mixed`.

## The red, as observed

`JS1`'s accepted half produced the assertion-level red the record predicted: on
the parser as it stood before the closure landed, **15 of the file's 37 guards
failed** — the five accepted controls the parser refused, and the five refused
texts it accepted as generic calls, each failing both its refusal and its naming
guard.  The parser's rules have since landed and the same 37 guards pass with
exit 0, so that red stands in the run history, not in the tree.

`JS2`, `JS4` and `JS5`'s red is the staged cut — `JS3` claims none, its subject
predating the change — and it was established rather than claimed.
In a throwaway copy, `kernel/json/identity/stub.c` was linked in place of the
kernel object — the cut's caller is the route's own driver, and nothing else
moved — and the route failed at its own comparison:

- **On the corpus arm, 288 of 288 rows differed** — the full route's count is in
  `docs/json-route-evidence.md` — the first differing row is row 1, and two runs
  of the cut produced identical output naming the same row.
- The cut tree's `tests/json-classify/check.sh` still exited 0, so no other
  route's outcome moved.
- At that row the defect arm's delimiter word is `0x00001e8000784080` — the word
  `JS2`'s `delimiter_witness` names as the one a body with the comma class's
  table bit cleared would produce.  The two scenarios corroborate each other:
  the object-level cut and the Lean-level witness disagree with the correct body
  at the same word.

The durable record of the cut — the command, the build status, the first failing
row and the no-other-route condition — is `docs/json-route-evidence.md`.

## Which artefact the route compiles

`check.sh` compiles `kernel/json/s1_block.c` with the pinned compiler line and
calls that object.  The object is not built from the fixture: the fixture's
loads carry no alignment operand (the capture drops `align 1`, and the parser's
`load` has no alignment field), so an object built from it inherits the type's
ABI alignment and the offset-1 staging the route requires is not reachable.
The kernel source keeps the measured C's alignment semantics, and
`ir-identity.sh` is what establishes that the two are the same code.

The fixture is not ignored, though: in the same run it is regenerated from that
same C at those same flags and compared with the committed bytes, and a
difference is a setup failure (exit 3), not an assertion failure.  The fixture
is the theorem's subject; the source is the object's.

## Prerequisites

The route is runnable once its inputs exist; until then `check.sh` exits 3 with
a line naming the absent artefact and a `FAIL` is never produced.  The inputs
are:

- `kernel/json/s1_block.c` and `kernel/json/s1_block.h` — the extracted kernel
  and the ABI header it publishes;
- `probes/install/ir/capture-s1-masks.sh` — the capture that regenerates the
  fixture from that source at the pinned flags;
- `probes/install/ir/json-s1-masks.candidate.ll` — the committed fixture, and
  at the same time the thing the capture must reproduce;
- `lakefile.toml`'s `lean_exe` stanza for `leanllvm-json-s1-masks`, and the
  binary `lake build leanllvm-json-s1-masks` writes at
  `.lake/build/bin/leanllvm-json-s1-masks` — both are prerequisites of the
  runner, and without them the runner's rows do not exist;
- `LeanLLVM/Vellum/JsonS1MasksIR.lean` — the module that pins the AST, which
  the Lean scenario imports and which nothing else in the tree provides.
