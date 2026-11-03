# JSON classifier

The classifier is emitted as LLVM IR and then has to be read back by the
parser, because the semantics and the refinement statements are about the
parsed form: a text the parser refuses is a body nothing downstream can be
proved about, and a parser that accepted a different shape would certify a
different program.  The refusal side is the same obligation from the other
direction: an unmodelled vector construct must be refused with a message that
names it, because a silent approximation would leave every other check green —
the committed classifier text contains none of the unmodelled constructs, so
nothing else in the tree would notice.

The accepted side is the committed fixture `probes/install/ir/json-classify.candidate.ll`,
read through `include_str`; the refused side is eight function texts written in
the scenario — six carrying one unmodelled vector construct each, one a splat
whose element type is not an integer, and one a splat whose element width
disagrees with the operand type's — with five controls in the same run (three
scalar forms and two splats whose type and width agree), which must each be
accepted.  The block-operation side is `scanBlock` and `maskOfList`, given a
mixed 32-byte block: a full block is classified and advances the cursor, a
block offered with one byte short produces no information, and the mask equals
a hand-written constant rather than `maskOf` read back.  The body side places
that same block in memory at a non-zero address and runs `classify32Function`
through `runFuel`: the returned `i32` equals the same hand-written constant, and
the returned memory reads back the same bytes.  The caller side stages four
`i64` words into its own locals and calls the seam: the returned `i32` is that
same style of hand-written mask under both the installed selection and the
reference selection, and a complementing body is distinguished both by the
complement it returns and by an inequality over `Option Outcome`.  Every
parser assertion is a `#guard` over `parseModule`, every block assertion a
`#guard` over `scanBlock`, and each body and caller assertion a `#guard` over
`runFuel`, so each observation is a closed decision about one call, and a
`#guard` that does not hold stops elaboration with a nonzero exit status.  No
compiler, proof checker, service, clock or network is reached.

    nix develop -c lake env lean tests/json-classify.lean

### JB1 — the emitted classifier fixture is what the parser must accept

- **Actor:** the parser, given a file's text.
- **Given:** the committed fixture
  `probes/install/ir/json-classify.candidate.ll`, read with `include_str`.
- **When:** `parseModule` is applied to that text.
- **Then:** it is `.ok m` and all of these hold, each its own assertion so a
  failure names which:
  1. `m.functions.length = 1` and `m.decls = []`;
  2. the function's name is `leanllvm_json_classify32`, its return type is
     `.int 32`, its parameter list is exactly `[("%arg", .ptr)]`;
  3. it has exactly one block, named `bb`, whose terminator is
     `.ret (.int 32) (some (.reg "%i23"))`;
  4. `b.instrs.length = 24`.
- **Why:** the plan's semantics fragment is sized from this text; if the parser
  does not accept it, nothing downstream can be proved about the compiled
  body, and a parser that accepted a *different* shape would silently certify
  the wrong program.
- **Not claimed:** nothing about the body's meaning, and the parsed
  *instruction shapes* are not asserted here: they are pinned in the library
  against the same fixture text, because the instruction constructors this file
  would name do not exist before the change.

### JB2 — unmodelled vector shapes are refused, and the refusal names the construct

- **Actor:** the parser, given a text with one unmodelled vector construct.
- **Given:** six function texts, one construct each, all inside an otherwise
  well-formed function:
  1. `%r = bitcast <32 x i8> %v to i32`
  2. `store <32 x i8> %v, ptr %p`
  3. `%p = alloca <32 x i8>`
  4. `%s = select <32 x i1> %c, <32 x i8> %a, <32 x i8> %b`
  5. `%r = icmp slt <32 x i8> %a, %b`
  6. a `splat` operand whose element is `zeroinitializer`
- **When:** `parseModule` is applied to each.
- **Then:** each is refused (`.error`), and the message **names the refused
  construct**: for (1) it must contain `bitcast` **and** a token of the source
  or destination type (e.g. `<32 x i8>` or `i32`); for (2) it must contain
  `store`; for (3) `alloca`; for (4) `select`; for (5) the predicate `slt` or
  the phrase naming the unmodelled vector comparison; for (6)
  `zeroinitializer`.  Refusal and the substring are asserted separately, so a
  failure says which half failed.
- **And:** an affirmative control in the same run — the scalar forms
  `store i32 %v, ptr %p`, `%p = alloca i32` and `%r = icmp slt i32 %a, %b` are
  each **accepted**, so the detector is not simply rejecting everything.
- **Why:** a parser that silently accepted any of these would leave every
  other committed check green, because the classifier fixture contains none of
  them; and a refusal that does not name the construct is the approximation the
  repository forbids.
- **Not claimed:** that every unmodelled vector construct is refused — only
  these six.

### JB6 — a splat's element is refused at the type and width positions, and each message names what it refused

- **Actor:** the parser, given a text carrying a splat whose element is refused
  at one of its positions.
- **Given:** two otherwise well-formed function texts, one per element position:
  1. `%i1 = icmp eq <32 x i8> %i, splat (ptr null)` — the element **type** is
     not an integer type;
  2. `%i1 = icmp eq <32 x i8> %i, splat (i32 5)` — the element **width**
     disagrees with the operand type's element width.
- **When:** `parseModule` is applied to each.
- **Then:** each is refused (`.error`), and each message **names what it
  refused**: for (1) it contains the refused type token `ptr`; for (2) it
  contains both width tokens `i32` (the element token's) and `i8` (the operand
  type's).  Refusal and the naming are asserted separately per text, so a
  failure says which half failed, and asserting tokens rather than sentences
  keeps the checks alive through rewording while a message that drops one of
  the widths fails.
- **And:** affirmative controls in the same run — `splat (i8 34)` at
  `<32 x i8>`, and `splat (i32 5)` inside a `<32 x i32>` operand, are each
  **accepted**, so the refusals are not the parser rejecting every `ptr` or
  every splat.
- **Why:** a splat carries its lane width and value, so an element type that is
  not an integer has no width to take, and one whose width disagrees with the
  operand type's would render text whose element type contradicts its
  instruction; a message that dropped the refused token or one of the widths
  would leave the reader unable to tell which side was wrong.
- **Not claimed:** the message wording beyond the asserted tokens, and nothing
  about the separate refusal of a splat element whose **value** is not an
  integer literal (`JB2` case 6), which is a different branch.

### JB3 — a full block is classified and advances the cursor, a short block reports no information, and the mask is the scalar decision per byte

- **Actor:** `scanBlock`, given a block and the number of bytes offered.
- **Given:** a 32-byte mixed block — structural bytes, JSON whitespace and
  ordinary content interleaved — whose byte 0 is `[` and whose byte 31 is `q`,
  offered at cursor position 7.  The mask the scalar transition must produce
  for it is the hand-written constant `0x7BD6F7B7`, in which bit 0 is set and
  bit 31 is clear, so a reversed bit order cannot satisfy the assertion.
- **When:** `scanBlock` is applied to that block with `valid = 32`, and again
  with `valid = 31`.
- **Then:** with `valid = 32` the status is `.ok` and the cursor is
  `pos + 32`; that half is definitional — it is the branch `scanBlock`'s `if`
  takes — and is asserted for clarity rather than as evidence.  The reported
  mask is exactly `0x7BD6F7B7`, written out rather than read back through
  `maskOf`, so the assertion is not a tautology.  With `valid = 31` the status
  is `.short`, the cursor is unchanged and the information is `0`.
- **Why:** a block operation that reported success on a partial block would
  carry bytes the caller never supplied as though they had been classified, and
  the mask is the scalar transition the emitted classifier body stands for, so
  reading it back out of `maskOf` would assert nothing about the transition.
- **Not claimed:** the compiled body's behaviour beyond these two inputs, and
  nothing about the cursor being carried correctly past this operation by its
  caller.

### JB4 — the staging caller returns the staged block's mask and memory under both the reference selection and the installed classifier body, and a complementing body is distinguishable

- **Actor:** the staging caller `scanCaller`, run under a call environment.
- **Given:** the same 32-byte `mixedBytes` block `JB3` classifies, staged by
  the caller's four little-endian `i64` stores.  The four words are derived
  from `mixedBytes` through the production `blockOf` encoding rather than
  retyped, and the derivation is asserted in the same run, so a fixture that
  failed to stage that block cannot make the mask assertion disagree with
  `JB3` silently.  Three selections are run at the same caller: the reference
  selection `envForMask`, the installed classifier body's selection
  `envForBodySym jsonSeamSymbol 10000 0 classify32Function`, and the
  complemented body's selection over `wrongMaskFunction`.  `mixedMask`'s
  hand-written provenance is established in `JB3`, where it is asserted
  against `mixedBytes` without reading `maskOfList` back; this scenario reuses
  that constant and does not recompute it.  The block's bytes are also
  cross-checked at build time against `tests/json-classify/mixed.block`, the
  fixture the executable's `--emit-block` writes, so a class-preserving drift
  between the scenario's copy of the block and the on-disk block is caught even
  though every mask assertion would still agree.
- **When:** `runFuel` is applied to `scanCaller` from `initState` with the four
  staged words, once per selection.
- **Then:** the caller returns, and separately, so a failure names which:
  1. under the installed classifier body's selection the caller's one outcome
     is `.ret (some (.int 32 mixedMask)) (stagedMem w0 w1 w2 w3)`, where
     `mixedMask` is the hand-written constant `0x7BD6F7B7` — the same constant
     `JB3` and `JB5` use, not a value read back out of `maskOfList` — and the
     memory is the one its four stores staged;
  2. the same value and memory hold under the reference selection `envForMask`
     — the two selections agree at the caller;
  3. under the complemented body's selection the caller returns the complement
     `mixedMask ^^^ -1`, and its whole run (`Option Outcome`) is an
     **inequality** against the classifier's run — the negative control over a
     type with `DecidableEq`;
  4. under the classifier's selection the caller's returned memory reads back
     the staged 32 bytes at address `1` (its first local), exactly
     `blockOf w0 w1 w2 w3`, so the mask is bound to the block that was
     staged.
- **Why:** the caller is where the seam's replacement is observed: the
  installed body and the reference selection must give the caller one outcome,
  and a body whose mask is complemented must give a different one, so the
  value clause is exercised rather than assumed.  Asserting the run inequality
  as well as the complement keeps the refusal observable even if the expected
  constant were written wrong, and the memory read-back ties the mask to the
  bytes actually written.
- **Not claimed:** the caller's behaviour for words other than those staging
  this block (that is the library theorem's statement), nor any difference
  between the runs beyond the returned value — both selections allocate
  nothing and return the caller's memory unchanged.

### JB5 — the classifier body, run from a memory holding the chosen block, returns the hand-written mask and leaves the caller's memory alone

- **Actor:** `runFuel`, running `classify32Function` — the AST pinned from
  `probes/install/ir/json-classify.candidate.ll` — under the repository's
  semantics.
- **Given:** the same 32-byte `mixedBytes` block `JB3` classifies, laid out in
  memory one cell per byte at the non-zero address `blockBase = 4096` (address
  `0` is reserved for `null` by `initState`), and initialised with that
  argument.
- **When:** `runFuel noCalls 10000 classify32Function` is applied to that state.
- **Then:** the run returns, and:
  1. the returned `i32` is exactly the hand-written constant
     `mixedMask` (`0x7BD6F7B7`) — the same constant `JB3` asserts for
     `scanBlock`, not a value read back out of `maskOf`;
  2. the returned memory, read back with `readBytes` at `blockBase` for 32
     bytes, is exactly `mixedBytes`.
- **Why:** `JB3` and this section read together as *body = hand value* and
  *`scanBlock` = hand value*, through two independent assertions, so neither
  reads its expectation out of `maskOf` and asserts a tautology.  The memory
  read-back is the body's purity: a store, an `alloca`, or a displaced address
  would change the caller's block, and the fixture body is supposed to execute
  neither `alloca` nor store.
- **Not claimed:** the body's behaviour on any block other than this one (that
  is the library theorem's statement), nor the packed value's agreement with
  the scalar transition beyond this block.


