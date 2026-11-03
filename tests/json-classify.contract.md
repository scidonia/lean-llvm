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
accepted.  Every assertion is a `#guard` over `parseModule`, so each observation
is a closed decision about one parse, and a `#guard` that does not hold stops
elaboration with a nonzero exit status.  No compiler, proof checker, service,
clock or network is reached.

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
