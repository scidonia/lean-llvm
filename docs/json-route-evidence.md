# Evidence for the JSON route scenarios

The JSON routes exist to make externally visible behaviour observable:
the API's accept/refuse outcomes, the tape's meaning, the corpus runner's
agreement with its oracle, and the two object-versus-body row comparisons — the
stage-1 classification masks and the entry position emitters. A green run alone
does not show that a route would
notice a wrong implementation, so each route carries a **staged cut**: a
deliberate divergence applied in a throwaway copy of the tree, built and run to
show which assertion fires.

Recorded at `ae58fbe`, Lean 4.35.0 and clang/LLVM 21.1.8 from the flake. Each
cut was made in its own copy under `mktemp -d`, built through
`probes/install/lake-locked.sh`, and the same command was run uncut as a
control.

## Method, and why it is not a mutation of the verified definitions

Mutating a definition that carries a proof falsifies that proof, so the module
stops building and the route stops at `import` — a setup failure, not a red.
Measured: replacing `numLexB` with a constant leaves 18 errors in its own
module, and a named span comparison in the decoder costs twelve proof-script
edits in `TapeCorrect.lean` plus thirteen in `Correct.lean`.

Where the defect class is *compiled artefact diverging from proven definition*,
the cut is therefore a runtime override — `@[implemented_by]` — in a copy.  The premise that a named
comparison would cost no proof changes was measured false for this module:
twelve `simp only` list additions in `TapeCorrect.lean` and thirteen sites in
`Correct.lean`, the tail equation lemmas and both seam theorems among them. The
definition, its statement and its proof are untouched; only the compiled body
differs. That is the class a certificate about a compiled unit has to care
about, and it is why these cuts are evidence about a runtime rather than about
the logic.

The corpus runner needs no such device: nothing in a proof eliminates on it, so
its cut is a source edit.

## The three cuts

| Route | Cut | Build | Scenario | Fired |
|---|---|---|---|---|
| `tests/json-api.lean` | `numLexB` overridden to accept every lexeme (`implemented_by`) | 820 jobs, exit 0 | exit 1 | eight guards: the `01` refusal and the `-`, `1.`, `1e`, `--1` refusals, plus `01` under three tight limits |
| `tests/json/check.sh` | the runner's mismatch test forced to a constant (`JsonMain.lean`) | exit 0 | exit 1 | `FAIL: the tampered manifest exited 0` |
| `tests/json-tape.lean` | `skipFrom` overridden to return `0` (`implemented_by`) | 820 jobs, exit 0 | exit 1 | six guards: `correctTape`, `correctTwoElemsTape`, `correctStringTape`, `correctObjectTape`, `emptyArrayOverSpace`, `numberSurrounded` |

Each cut was run uncut as a control: `tests/json-api.lean` exit 0,
`tests/json/check.sh` exit 0, `tests/json-tape.lean` exit 0 at `ae58fbe`.
Every cut tree built before its scenario ran: a cut that does not compile is a
setup failure and is not evidence.

## What each red does and does not show

- **The API route notices a wrong number grammar.** The cut reddens the `01`
  refusal among eight assertions, which is the intended one; it also reddens
  every other number refusal, because accepting every lexeme is a coarse
  divergence rather than a targeted one.
- **The corpus route notices a runner that cannot report a mismatch.** One
  assertion, and only it.
- **The tape route notices a decoder that reads positions wrongly.** Six
  guards fire, `correctTape` among them. It does **not** show that the
  span-mismatch refusals are individually sensitive: an identity override of
  `skipFrom` is inert for them (only the two whitespace tapes fire), and the
  refusals' sensitivity rests on their pairing with the affirmative controls
  and on `tape_valid`, not on a cut.
- One earlier observation is **withdrawn**: a tape red produced by restoring a
  stale `TapeCorrect.olean` next to a cut `Tape.olean` fired against an
  artefact that does not correspond to the source under test, which is worse
  than no red.

## What is not claimed

No route claims that a red was produced by mutating a verified definition — it
cannot be, as above. No route tests the proofs. The corpus oracle is
hand-written, one expected verdict per row, and the runner compares against it;
a manifest produced by the runner itself would be circular and is not used.

## The J2 cuts (`X1`–`X8`), observed at `d13d633`

The three cuts above were recorded at `ae58fbe` and are left exactly as they
were recorded; they were not re-run in this observation and are not counted
again. The cuts below belong to the JSON block classifier and were made at
`d13d633` (`d13d6337016af6c390179e2b2b69fcbfeb59c81e`, `main`), Lean 4.35.0 and
clang/LLVM 21.1.8 from the flake. The working tree carried two untracked files,
`tests/call-memory.lean` and `tests/call-memory.contract.md`; no cut touched
them.

Each cut was made in its own copy of the tree under `mktemp -d` and built with
`nix develop -c bash probes/install/lake-locked.sh build`; every cut tree built
(1633 jobs, exit 0) before its route ran. `X4` has no copy and no cut: its row
records the production tree, which was built the same way. `X5`'s copy is the
production tree as it stands. The uncut control is the same build and route
commands at `d13d633` on production: the build exits 0, and every route command
below exits 0 uncut. Line references are as observed on these bytes; an earlier
reading on different bytes gave `X8` as `:276`, and on these bytes its assertion
is `:280`.

| Cut | Cut applied in the copy | Build | Route command | Exit | Assertion that fired |
|---|---|---|---|---|---|
| `X1` fixture pin | `probes/install/ir/json-classify.candidate.ll`: `splat (i8 44)` → `splat (i8 45)` | exit 0 (the fixture is not a `lake build` input, `AGENTS.md`) | `nix develop -c lake env lean LeanLLVM/Refinement/JsonClassifyIR.lean` | 1 | `JsonClassifyIR.lean:93:0`, did not evaluate to `true` |
| `X2` corpus route | the same fixture mutation | exit 0 | `nix develop -c bash tests/json-classify/check.sh` | 1 | `FAIL: the installed object and the Lean body disagree`; diff `mixed.block 0 0x7bd6f7b7` → `0x7bd4f7a7` |
| `X3` `scanBlock`'s compiled body | `LeanLLVM/JSON/ScanBlock.lean`: `@[implemented_by] scanBlockImpl`, which ignores `valid` and returns `.ok` with `pos + 32` | exit 0 | `nix develop -c lake env lean tests/json-classify.lean` | 1 | `:340`, `:341`, `:342` (the three short-block assertions) |
| `X4` the relation's value clause | no staged cut: `wrongMask_not_refines` (proof) and `JB4`'s executable inequality | exit 0 | `nix develop -c lake env lean tests/json-classify.lean` | 0 | none: the theorem checks and both the equality and the complement inequality hold |
| `X5` parser no-regression | no divergent cut: production as it stands, built in a copy (the same build as production) | exit 0 | `nix develop -c bash tests/json/check.sh`; `nix develop -c lake env lean tests/json-api.lean`; `nix develop -c lake env lean tests/json-tape.lean` | 0, 0, 0 (at `d13d633`; see the note below) | none: `ok: the corpus agrees with the manifest; a tampered expectation is a mismatch`, then two silent exits |
| `X6` the packing the semantics applies | `LeanLLVM/Semantics.lean`: `@[implemented_by] lanesToNatImpl`, which packs lane `k` into bit `31 - k` | exit 0 | `nix develop -c lake env lean tests/json-classify.lean` | 1 | `:403`, `:411`, `:475` |
| `X7` the splat's width comparison | `LeanLLVM/Parser.lean`: the `if w' ≠ w then … else` guard removed from the splat branch | exit 0 | `nix develop -c lake env lean tests/json-classify.lean` | 1 | `:283`, `:284`, `:285` |
| `X8` the splat's element-type check | `LeanLLVM/Parser.lean`: the integer-type failure removed, falling back to the operand width, so the text reaches the shared value branch | exit 0 | `nix develop -c lake env lean tests/json-classify.lean` | 1 | `:280` only (`refusalNames splatTypeMismatch "ptr"`) |

The `X5` row's route commands and exits are the record of `d13d633`, the
revision they were observed at: that is the last revision at which this
document records the two `#guard` routes exiting 0, and their exits do not
extend past it. At `77abc35`, where `Bytes` becomes `ByteString`,
`tests/json-api.lean` and `tests/json-tape.lean` fail to elaborate — 46 and 53
errors, measured at that revision — because their byte literals still spell
bytes in the old list carrier. Both commands exit 1 at `77abc35`; what they do
not produce is the row's exit 0, and so neither is evidence there.
`tests/json/check.sh` is green at `77abc35`.
Restating the two files over the carrier restores both: at the revision that
carries that update, `nix develop -c lake env lean tests/json-api.lean` and the
same command for `tests/json-tape.lean` each exit 0 with no output, and the
corpus route prints its `ok` line and exits 0.

All of `X1`–`X3` and `X6`–`X8` were reproduced in this observation; none is an
inherited reading. `X1`, `X2`, `X3`, `X6`, `X7` and `X8` are **assertion reds**:
each reached its own assertion and failed there, on a tree that built. `X4`
owes no staged cut — it is evidenced by a proof and an executable inequality —
and is not counted as a red cut. `X5` is a no-regression control by definition:
its claim is that the parser routes stay green, so it cannot produce a red and
is not counted as one.

### What each cut shows, and what it does not

- **`X1` — the theorem is bound to the fixture's bytes.** The build is green
  because a fixture read through `include_str` is not a `lake build` input
  (`AGENTS.md`); the pin is exercised by re-elaborating the module from source,
  which fails at `:93`. Uncut, the same elaboration exits 0. It does **not**
  show that the theorem is sensitive to a semantic defect in a body that still
  parses and still returns the right mask; that rests on the statement being an
  equality with `maskOf block` for every block, a statement-level argument, not
  a cut. Had the mutated module elaborated, the pin would be decorative and
  that outcome would be a finding against the package, not a pass.
- **`X2` — the route notices the artifact's bytes.** With the committed fixture
  mutated and the Lean binary built from production, steps 0–2 pass (the
  failure is step 3's, so step 1's manifest control had already passed) and
  step 3 reports the one changed window: `mixed.block`, offset 0,
  `0x7bd6f7b7` from the Lean body against `0x7bd4f7a7` from the object built
  from the mutated fixture. All 70 corpus rows are unchanged; the mixed block
  is the sole discriminator for this defect, and
  `tests/json-classify/check.sh:56-60` records why: the removed comma class
  occurs only there, at bytes 4 and 17. The red is step 3's object-versus-Lean
  arm, not step 4's built-in defect detector: step 4
  derives its own defect from the same fixture, so a fixture already carrying
  the mutation makes that derivation a no-op (`SETUP`) — the external mutation
  cannot reach step 4, and step 3 is the arm that observes the committed
  fixture's bytes. The uncut control runs step 4 and prints `ok: the detector
  bites: … 0x7bd6f7b7 -> 0x7bd4f7a7`. It shows nothing about the proofs, and
  nothing about a defect the corpus never exercises; the transcript stays
  ancillary evidence, not an installation certificate.
- **`X3` — the short-block assertion depends on `scanBlock`'s compiled body.**
  The override leaves the definition, its statement and its proof untouched;
  the three short-block assertions fire (`:340` status, `:341` cursor,
  `:342` information) while the full-block and mixed-mask assertions (`:331`,
  `:332`, `:336`) hold in the same run. It does **not** show the definition or
  its proof is wrong — both are untouched — and says nothing about the LLVM
  body.
- **`X4` — the relation's value clause.** `wrongMask_not_refines` is a theorem
  and the complement inequality is executable in `JB4`; the scenario exits 0,
  so both hold. It does **not** show refusal of a body that differs only inside
  an empty frame — no such difference exists, because both selections allocate
  nothing and return the caller's memory unchanged.
- **`X5` — the parser routes stay green.** In a copy built at `d13d633`, and
  again on production afterwards, `tests/json/check.sh` printed its `ok` line
  and exited 0, and `tests/json-api.lean` and `tests/json-tape.lean` exited 0
  with no output. Both observations are of `d13d633`; the two `#guard` exits do
  not extend past it, as the note under the table records. There is no
  divergent cut here and no fired assertion; a green control is not an
  assertion red. It does **not** show that the parser
  routes through the candidate, and it does not: the transported caller is
  `scanCaller` (`LeanLLVM/Refinement/JsonSeam.lean`), which stages its own
  32 bytes from four `i64` words before calling the classifier, so the parser
  never reaches the classifier.
- **`X6` — the packing the semantics applies.** The reversing override builds,
  and `:403` (`JB4`'s equality), `:411` (`JB4`'s complement inequality) and
  `:475` (`JB5`'s mask equality) fire — three assertions, not the two recorded
  earlier. It **cannot** redden a theorem:
  `@[implemented_by]` changes compiled bodies, not definitions, so
  `scannerLLVM_refines` is untouched by construction, and the theorem's
  dependence on the packing is discharged by proof rather than by this cut. It
  does **not** show the artifact's bytes are what the assertion depends on —
  the body is untouched and only the semantics' packing differs; `X2` is the
  instrument for the artifact, and the two are not substitutes.
- **`X7` — the width branch exists.** With the guard removed, `splat (i32 5)`
  at `<32 x i8>` parses `5` at the operand width instead of being refused, so
  the width text's refusal and both naming assertions fire (`:283`, `:284`,
  `:285`). It does **not** show the refusal's message names both widths when
  the branch is present — the cut removes the branch, so it tests its
  existence, not its wording — and says nothing about the type or value
  positions, which are different branches.
- **`X8` — the type check produces the type message.** With the integer-type
  failure removed and the operand width used, exactly one assertion fires:
  `:280`, the naming half of `JB6`'s type text; `refused` itself (`:279`) still
  holds, because the text falls through to the shared value branch, which
  refuses `null` as a non-integer literal. The type position stops refusing
  *as a type*, but the text does not become acceptable. It does **not** show
  the text becomes acceptable without the check — it does not, and this cut
  does not claim it.

## The stage-1 mask route's cut (`Y1`)

`tests/json-s1-masks/check.sh` is the JSON route for the stage-1 classification
masks: the object built from `kernel/json/s1_block.c`, called through
`probes/json/s1_masks_driver.c`, against the Lean body `s1MasksFunction` that
`LeanLLVM/Refinement/JsonS1MasksIR.lean` pins from
`probes/install/ir/json-s1-masks.candidate.ll`. The two row streams must be
equal line for line; the assertion is that comparison, and the row count it
walks is asserted separately.

The cut is the kernel object replaced by a stub — `kernel/json/identity/stub.c`
defines the same ABI and writes six zero words, leaving the carry slot
untouched. It was built and run in a throwaway copy, with nothing else moved.

| Route | Cut | Build | Scenario | Fired |
|---|---|---|---|---|
| `tests/json-s1-masks/check.sh` | the kernel object replaced by `kernel/json/identity/stub.c`: `leanllvm_json_s1_masks` writes six zero words and leaves the carry slot | exit 0 | exit 1 | the row comparison: **675 048 of 688 824 rows differ**, first differing row **1**, byte-identical across two runs |

- **The 288-row arm is the mixed block plus `mixed.json` alone.** That is the
  row set the contract record (`tests/json-s1-masks.contract.md`, "The red, as
  observed") was taken on: the 8 mixed rows and `mixed.json`'s 35 windows at 8
  rows each — 288 rows, every one of which differed. The full arm is 688 824
  rows, and it is that 288 plus two additions: `mixed.json`'s five neighbours in
  the corpus — `boundary-63.json` 0 windows, `boundary-64.json` 1,
  `boundary-65.json` 2, `nested.json` 18 and `strings.json` 30, so 51 windows and
  408 rows — and the three generated arms (`arm:byte` 131 072 rows,
  `arm:alphabet` 524 288, `arm:random` 32 768). On that larger set 13 776 rows
  agree; the comparison is exact, so those are rows on which the stub and the
  body write the same bytes. The two numbers are one observation over two row
  sets; they do not disagree.
- **Nothing else moved.** The cut's caller is the route's own driver
  (`probes/json/s1_masks_driver.c`) — not a second harness, and not the Lean
  runner. No other route reads `kernel/json/s1_block.c`, and both other JSON
  routes, `tests/json-classify/check.sh` and `tests/json/check.sh`, exit 0 in the
  cut tree.
- **The same first row on two runs.** Two runs of the cut produced byte-identical
  output naming row 1, so the first failing row is a property of the cut and not
  of a run.
- **What it does not show.** A stub is not a semantic defect: it shows the
  comparison is live and that the first failing row is stable, not that the masks
  are right for any particular block. The object-versus-body agreement uncut is
  `JS4`'s claim, and the targeted comma-class defect is `JS5`'s.

Command: `nix develop -c bash tests/json-s1-masks/check.sh`.

## The entry route's cuts (`Z1`, `Z2`)

`tests/json-entry/check.sh` is the JSON route for the entry position emitters:
the object built from `kernel/json/entry.c`, called through
`probes/json/entry_driver.c`, against the Lean bodies `entryPos8Function` and
`entryB8Function` that `LeanLLVM/Refinement/JsonEntryIR.lean` pins from
`probes/install/ir/json-entry.candidate.ll`.  One row is one `(mask stream,
blk0, nblk, k)` call under one kernel; the route derives every row's count,
`multi` and sentinel — and, for every row but the one long `nblk` row, its words
— from the committed corpus bytes and from the arm's own label and asserts them,
asserts the row count, and then compares the two actors' streams line for line.
The row count is `2 * (6 corpus files + 65 859 arm streams)` = **131 730**.

Both are the staged cut `JE2` and `JE3` name in `tests/json-entry.contract.md`:
the entry unit's object is replaced by a stub that returns the cursor `k`
unchanged and writes nothing — `leanllvm_json_entry_pos8` and
`leanllvm_json_entry_b8` each discard their arguments and `return k` — while
`leanllvm_json_entry_table` keeps its production body, so the table the POS8
rows read stays the real one.  `Z1` stubs both kernels; `Z2` stubs B8 only,
which makes every POS8 row the production body's own and so separates "the
comparison is live" from "each kernel is compared separately".

The stub is compiled from a source in a throwaway copy of the tree and
substituted for the route's control object by a `clang` front end on `PATH` that
rewrites the one compile whose `-o` basename is `kernel.o`; the fixture capture's
compiles, the driver link, and the route's own two defect objects go to the real
compiler untouched.  The cut adds no file to the tree: the stub source and the
front end live outside it, and only the one compile of `kernel.o` is redirected.
`nix develop -c lake build leanllvm-json-entry` in the copy exits 0 (1660 jobs).  The
substituted objects are sha256 `611c9415…` (`Z1`) and `962c1eba…` (`Z2`) at the
route's measured compiler line, against the production object's `384f710b…`;
those hashes are the objects the compiles produced, so a substitution that
silently kept the production object would show as a hash.  Observed on the
working tree at `ad188ad` plus this change, Lean 4.35.0 and clang/LLVM 21.1.8
from the flake.

| Route | Cut | Build | Scenario | Fired |
|---|---|---|---|---|
| `tests/json-entry/check.sh` | the entry object replaced by a stub over both kernels (`Z1`) | exit 0 (1660 jobs) | exit 1 | `FAIL: the object and the Lean body disagree`, reached after the route's per-row derivation of the Lean actor's 131 730 rows had passed; the first differing row is **1**, whose count column is `0` and whose words are `-` |
| `tests/json-entry/check.sh` | the entry object replaced by a stub over B8 only (`Z2`) | exit 0 (1660 jobs) | exit 1 | the same assertion; the first stream's POS8 row is identical in both actors, and the first differing row is **2**, that stream's B8 row, at count `0` |

- **The two first differing rows are one stream's two kernels.** In `Z1` row 1
  is `boundary-63.json`, label `blk00/k0/masks1`, kernel `p`: the body returns
  36 and writes 36 positions, the stub returns 0 and writes nothing, so the
  object's row reads `… p 0 - 1 0xa5a5a5a5` against the body's 36 words.  In
  `Z2` that row is a context line — byte-identical in both actors — and row 2,
  the same stream's `b` row, is the first that differs, `… b 0 - 1
  0xa5a5a5a5` against the body's 36.  Both rows' streams carry 36 set lanes,
  which is the property the cut needs: the row is chosen to have a set bit, so
  a `0` in the count column is the stub's answer and not the stream's.
- **The stub's count is the starting cursor, not a constant zero.**  The
  `strings.json` stream is staged at `k = 5`, and under `Z1` its rows read
  count `5` with five sentinel words and no position, where the body's count is
  60.  A stub that returned a literal `0` would be a different divergence, and
  this row is what tells the two apart.
- **Nothing else moved.**  The cut's caller is the route's own driver
  (`probes/json/entry_driver.c`) — not a second harness, and not the Lean
  runner.  No other route reads `kernel/json/entry.c`: its other consumers are
  the unit's identity scripts under `kernel/json/identity/` and the paired
  benchmark `kernel/json/bench/paired.sh --unit entry`, neither of which is a
  route.  In the cut tree both other JSON routes,
  `tests/json-classify/check.sh` (exit 0, 71 windows agreeing; object sha256
  `95a38141…`) and `tests/json-s1-masks/check.sh` (exit 0, 688 824 rows
  agreeing; object sha256 `80d29a5b…`), are green.
- **The same first row on two runs.**  Both cuts were run twice, and each pair of
  outputs is identical once the unified diff's header — which carries the
  temporary directory and timestamps — is excluded: `Z1`'s first differing row
  is row 1 both times and `Z2`'s is row 2 both times.  The first failing row is
  a property of the cut, not of a run.
- **What it does not show.**  A stub is not a semantic defect: it shows the
  comparison is live and that the first failing row is stable, not that the
  positions are right for any block.  The object-versus-body agreement uncut is
  the route's own green assertion, and the targeted defects belong to the
  route's two detector arms, not to this cut.

Command: `nix develop -c bash tests/json-entry/check.sh`.

## The UTF-8 stage's route, observed at `8541d8f`

`tests/json-utf8/check.sh` is the UTF-8 stage's route. Three actors and a
scalar reference agree row for row over a counted corpus:

- **the object** — `kernel/json/utf8.c` compiled at the measured compiler line
  and called through `probes/json/utf8_driver.c`, which stages each row's
  window and prints the returned word;
- **the Lean body** — `utf8Function`, the AST `LeanLLVM/Refinement/JsonUtf8IR.lean`
  pins to `probes/install/ir/json-utf8.candidate.ll`, run by
  `leanllvm-json-utf8` through `runFuel` under the repository's semantics;
- **the measured statements** — `probes/json/utf8_measured.c`, which includes
  the vendored `s1fuse.h` at the measured `-D` set and calls the measured
  `s1f_build2`, reporting its `uerr`;
- and **the reference**, `utf8_driver.c`'s own scalar valid-prefix predicate in
  two forms: over the staged window — three prefix bytes, the document, zero
  padding to the block boundary — which is the expectation on every row, and
  over the document alone, whose disagreement with the window form is counted
  arm by arm.

A row is nine tab-separated columns — `source label n gate path word skip eval
padded` — and each actor is run twice, once per gate value, so one transcript
is one gate value throughout.  `path` is the effective path the actor used,
which for the measured actor is the TU-static `s1f_u8_ungated` read back after
`s1f_u8_decide`; `word` is the stage's error word, 0 accepted and 1 rejected.
`skip` and `eval` are **derived** from the staged window's bytes by
`probes/json/utf8_skip.h`'s one function (and by the same rule in Lean), never
read out of the code under test: the two arms' verdicts are equal on every
document of this matrix, so the counts are the gate's only per-document trace.

**One total, derived from the enumeration beside it.**  The corpus
`tests/json-utf8/corpus.tsv` holds 27 curated rows, re-derived by the script
from committed bytes: six documents' own first 64 bytes, fifteen high-byte
blocks of the committed `utf8-*.json` documents, the truncated-lead boundary at
63, 64 and 65 bytes, the prefix-flip pair, and the 200-byte document the gate's
skip count is about.  The arms are 1 empty + 256 one-byte + 65,536 two-byte + 486
three-byte + 5,103 four-byte + 1,671 tail + 18 prefix + 512 placement
= 73,583, so the route is 27 + 73,583 = **73,610 rows per gate value**.  The
counted matrix without the placement arm is 73,071 and the gate's coverage is
73,053 (73,071 less the 18 prefix variants, whose non-ASCII prefixes are
outside the staging obligation the gate's soundness is stated under).  The
script computes that total twice — from the formula and by enumerating every
row's identity in `awk` — and requires the transcript to match both.

Uncut, the route exits 0 and prints thirteen `ok` lines.  What it asserts, with
the numbers observed:

| Fact | Observed |
|---|---|
| rows per gate value | 73,610 = 27 corpus + 73,583 arm |
| word equals the window reference | 73,610 of 73,610 |
| document form against window form | 51 (one-byte arm), 7,744 (two-byte), 342 (tail, all in the `raw` layout), 0 (three-byte, four-byte, empty) |
| window accepts where document rejects | 0 |
| three-byte per-lead rejections | `E0` 69, `E1`/`EC`/`EE`/`EF` 45, `ED` 57, of 81 each |
| four-byte per-lead rejections | `F0` 585, `F1`/`F3` 513, `F4` 657, `F5`/`F7`/`FF` 729, of 729 each |
| gate-invariant words | 73,053 documents |
| documents whose verdict moves across the three prefix values | 2 |
| `ascii:200-c3a9` blocks | gated 3 skipped / 1 evaluated, ungated 0 / 4 |
| the tail at 63, 64, 65 bytes | rejected, accepted, rejected |
| the defect object moves | 144 rows, first `arm:tail/c0/pre/L1` |

These are the stage's measured behaviour matrix re-derived on every run, and
they are the route's numbers rather than recalled ones: the per-lead counts pin the nine
continuation values the three- and four-byte arms are built from, and the
51 / 7,744 / 342 split is the count of rows where the document ends inside a
character.

The timing arm beside it, `nix develop -c bash kernel/json/bench/paired.sh
--unit utf8`, exits 0 at the same revision: one binary holds the measured
statements and the extracted unit behind page-aligned probes, and every input is
within ±0.5 ns/block.  Its gated/ungated medians are printed as an observation
with those derived counts, and no gated-to-ungated delta is claimed — on
`arm:ascii-4096` the gated arm costs 0.72 ns/block against the ungated arm's
1.98 (64 blocks, 64 skipped by the gate), which is the gate doing something
rather than being harmless.

### The two cuts

| Cut | Assertion that fired | Rows that differ | First differing row | Repeat |
|---|---|---|---|---|
| `V1` the unit's object replaced by a stub returning a constant verdict | `FAIL: the lean actor and the object disagree at gate g` | 53,784 | row 11, `blk:utf8-ff/blk0` | two runs identical once the private work path is normalised |
| `V2` the measured probe built without the `dens_pick_u8(0, 0, 0, 0)` pre-binding | `FAIL: <work>/measured.u: row 1 path g, not u` | 1, in the `path` column; 0 `word` differences | row 1, `doc:boundary-63/blk0` | two runs identical once the private work path is normalised |

Both were made at `8541d8f` in their own copy of the tree — a `tar` of the
checkout without `.lake`, which is symlinked in, so the Lean runner is the
production binary — with the working tree carrying this change.  Each copy ran
`nix develop -c bash tests/json-utf8/check.sh` twice; uncut, the same command
exits 0 in the production tree.  Both cuts reached their assertion on a tree
that compiled: `V1`'s stub object compiles and links against the driver, and
`V2`'s two probe builds compile.

The three conditions:

- **the caller is the route's own driver.**  `V1` compiles the stub in place of
  the object `check.sh` links into `probes/json/utf8_driver.c`, so the first
  assertion to fire is the object-versus-body comparison and not one of the
  route's own detectors.  `V2` edits `probes/json/utf8_measured.c`, which is
  the measured actor and nothing else.
- **no other route's outcome moved.**  Neither cut touches a file another route
  reads: no other `check.sh` compiles `kernel/json/utf8.c` or
  `probes/json/utf8_measured.c` — the unit's other consumers are the identity
  scripts under `kernel/json/identity/` and
  `kernel/json/bench/paired.sh --unit utf8`, neither of which is a route.  In
  `V1`'s copy `tests/json/check.sh` exits 0 with its `ok` line, and in `V2`'s
  copy `tests/json-entry/check.sh` exits 0 with 131,730 rows agreeing (its
  object at kernel sha256 `384f710b…`).
- **two runs name the same first failing row.**  Each pair of runs is identical
  once the unified diff's header, which carries the temporary directory and
  timestamps, is normalised away.  The first failing row is a property of the
  cut, not of a run.

What each shows, and what it does not:

- **`V1` — the route notices an object that answers with a constant.**  The
  53,784 differing rows are exactly the rows whose reference verdict is a
  rejection, so the cut is invisible on the accepting rows: it shows the
  comparison is live and that its first differing row is stable, not that any
  row's verdict is *right*.  That is the reference's job, and the route's own
  defect control — the tail term cut from a copy of the unit's
  source — is the arm that pins a semantic defect to its row set.
- **`V2` — the effective-path field notices a probe that leaves the measured
  static at its default.**  `dens_u8_ungated` is process-wide and
  `s1f_build2`'s `dens_probe` re-sets it for every document with a block, so
  without the pre-binding only the short documents that precede the first
  block-bearing one carry the default: one row here, and the route's corpus
  order — a 63-byte document first — is what makes the cut measurable.  The
  second assertion the run prints (`counts 1/0, expected 0/1`) is a consequence
  and not an independent observation: the counts are derived from the reported
  path, so a wrong path moves them.  A probe that *ignored* the build and
  always reported one arm would fail on every row instead, which is the
  assertion's own claim.
- **The cut that is not here: the gated path's skip replaced by an
  unconditional evaluate.**  It is not observable at this boundary.  The ABI
  returns one error word, whose value is gate-invariant, so a verdict-preserving
  cut moves nothing the route prints; an "evaluated-block count" computed by any
  actor is derived from the document's bytes, so it does not move either; and
  there is no seam to instrument — `kl_err_vec_ld` is `static inline` in a
  read-only vendored header, and a counter in the unit's own text would be both
  a production backdoor and an emission difference `ir-identity.sh --unit utf8`
  would report.  The timing arm's gated/ungated medians are an observation with
  no band, so they are not a witness either.  The cut reopens if a later
  milestone adds a seam that reads the unit's own branch.

## The route boundary's controls (R1–R9)

The route scenario now compares the arena and event bytes as well as the
observation line, and the adapter reports a tagged result instead of clamping a
cursor.  A green run of that comparison shows nothing on its own — two empty
payloads agree however the object misbehaved — so each new check carries a cut
that makes it fail, and each cut was made in a scratch root holding only
`kernel/json`, `tests/json`, `probes/json/route` and `probes/install/ir` copied
from the working tree.  Nothing in the repository was moved, and no cut is part
of the change.

Observed on the working tree at `4f94295` plus this change, Lean 4.35.0 and
clang/LLVM 21.1.8 from the flake; `R10`–`R13` were observed later, when the
route's shell decided by the library's `admission` directly — the shell now
decides by the two-phase equivalent (the native phase-one verdict, with
`policyRefusal` only on a candidate, `admission` retained as the oracle), and
their uncut control is

```text
ok: 122 default-profile rows: 107 fast-path row(s) agree with the driver on the observation, arena and events (22 arena byte(s) over 9 row(s), 1125 event byte(s) over 69 row(s)); fast path accept 59, invalid 48; fallback refusals 14, fallback accepts 0; divergence 0; empty excluded 1; 8 non-default-profile rows skipped; depth 128 fast, 129/520/521 fall back with depthExceeded; 14 policy rows fall back with the reference reasons
```

`R1`–`R9`'s quoted reds belong to the earlier revision and to the row counts
that revision compared; they are not re-read here.  Every cut tree built with
exit 0 before its scenario ran, except `R5`, whose claim is the build's own
assertion.
| Cut | Applied in the copy | Build | Route command | Exit | Assertion that fired |
|---|---|---|---|---|---|
| `R1` arena value | `shim.c`: one arena byte flipped after the call, `ndst` and every other word untouched | 0 | `check.sh` | 1 | `FAIL: esc-quote.json: value disagreement: the arena streams first differ at byte 0: route 0x23, driver 0x22`; **19** value disagreements — one per row whose arena is non-empty — then three aggregate assertions |
| `R2` arena cursor | `pipeline.c`: `*ndst = dstcap + 1` after the call | 0 | `check.sh` | 1 | `FAIL: num-zero.json: the route reported an internal contract violation:`, then `route: internal contract violation: the arena's cursor: capacity 65, returned 66`; 120 assertions |
| `R3` native stack bound | `stage2.c`: `#define MAXD 520` → `128` | 0 | `check.sh` | 1 | `FAIL: depth 129: the object refused a document inside its 520-frame stack (verdict 0)`, the same at 520, and `FAIL: depth 521: the refusal offset is 128, not the 521st opener at 520`; 3 assertions |
| `R4` table never filled | `entry.c`: `xl_pos8_init` returns before filling the table | 0 | `check.sh` | 1 | `FAIL: esc-shorts.json: the object refused an accept row (verdict 0)`; 30 assertions |
| `R5` setup does not fill the table | `shim.c`: the `leanllvm_json_entry_table` call replaced by a no-op | 1 | — | — | `build: the adapter does not import leanllvm_json_entry_table` |
| `R6` buffer below its capacity | `RouteMain.lean`: the entry buffer sized `4 * epcap - 4` against the advertised `epcap` | 0 | `check.sh` | 1 | `FAIL: num-zero.json: the route exited 3`, then `route: unsupported domain: the entry stream's buffer at its capacity: expected 292, observed 288`; 122 assertions |
| `R7` allocation failure | `shim.c`: the 24-byte staging copy forced to fail | 0 | `check.sh` | 1 | `FAIL: num-zero.json: the route exited 4`, then `route: allocation failure: the adapter could not copy a 24-byte staging buffer`; 130 assertions |
| `R8` optimisation level | `build.sh`: `-O2` → `-O1` | — | `correspondence.sh` | 1 | `FAIL: build.sh carries '-O1' beyond the capture's flags; the relation is not -O2 against -O3 alone` |
| `R9` depth guard | a copy of `DomainCheck.lean` with the acceptance side's `128` → `129` | — | `lake env lean` | 1 | the `parseBytes` acceptance guard and the shell's admitted-decision guard did not evaluate to `true` |

The per-cut totals above are the run's own summary counts, and most of them are
aggregates: a row whose comparison fails is not counted in the class it would
have reached, so `R2`, `R4`, `R6` and `R7` also report the guards that no row
reached.  Only `R1`'s decomposition was read off the run: the 19 arena-carrying
rows each fail the value comparison — ten of them are policy-class rows, which
therefore never reach the policy accounting, so the run also reports the policy
class as 4 of 14 (the four `nc-raw-*` rows, whose arena is empty), the pinned
class diff, and the arena-arm vacuity guard.  The assertion named in each row is
the one that fires first and names the class.

What each shows, and what it does not:

- **`R1` — the payload comparison is live and metadata-preserving.** The cut
  moves one arena value while leaving the verdict, all four cursors and the
  lengths intact, so the failure comes from the byte comparison and names the
  byte; before the change this row was green under the first-line comparison.
  It does not show the *values* are right against the reference tape: the two
  callers run the same object, and reference-level value comparison is a
  separate requirement.
- **`R2` — an oversized cursor is reported, not clamped.** The adapter returns
  the internal-violation tag with the capacity and the returned count, exits 5,
  and prints no truncated observation.  The clamp this replaces would have
  reported `ndst = 65` for a document whose object said `66`, which is the
  corruption reported as a shorter, well-formed result.
- **`R3` — the depth arm depends on the native bound.** The cut lowers `MAXD`,
  so 129 and 520 are refused by the object and the 521st opener's offset moves
  to 128: the arm's three assertions are the ones that fire, and the corpus rows
  are untouched.
- **`R4`/`R5` — the POS8 table is initialised by the adapter's setup, and its
  absence is visible twice.** `R4` leaves the call in place and cuts the table's
  contents: the runtime red is the accept rows, refused.  `R5` removes the call:
  the compiler then drops the import, so the build's `nm` assertion fires before
  a scenario exists.  Neither shows that a table *value* is right; that is
  `tests/json-entry/check.sh`'s object-versus-body arm.
- **`R6`/`R7` — the two failure tags are reachable and distinguished.** A buffer
  shorter than its capacity word is caught before the native call (exit 3,
  expected and observed sizes), and a failed staging copy is its own tag (exit
  4).  They do not show that no *other* precondition is missing: the list is the
  ABI's, and the adapter checks the sizes and extents it is given.
- **`R8`/`R9` — the two boundary records are gated.** `R8` is the
  correspondence's flag relation, so a document that says "the levels are the
  only difference" cannot outlive a change to that difference.  `R9` is the
  reference's side of the depth boundary: `DomainCheck.lean`'s 128 guards fail
  when the acceptance side is moved onto the refusal side, so the 128/129 pair
  is a measured bound and not a comment.

## The shell's routing controls (`R10`–`R13`)

Observed while the route's document decision was the library's `admission`
predicate directly (the shell now uses the two-phase equivalent, with
`admission` as the suite's oracle).  Each cut was applied to `probes/json/route/RouteMain.lean`'s `run` in
a throwaway copy, the route was rebuilt with `build.sh`, and `check.sh` was run;
the tree was then restored from a saved copy, rebuilt, and the run quoted above
is the restored build's.  The cut is at the decision's consumer rather than in
`admission`, because the clause definitions carry the certificate's proofs:
removing a clause there is a build failure, not an assertion failure, and these
controls are about whether the scenario notices a document taking the wrong
path.

| Cut | Applied in the copy | Build | Route command | Exit | Assertion that fired |
|---|---|---|---|---|---|
| `R10` depth fallback | `.error (.depthBound _) => runFast …` in `run`'s match | 0 | `check.sh` | 1 | `FAIL: depth 129: expected the fallback's depthExceeded refusal (exit 0)`, the same at 520 and 521, and `FAIL: the opener-rich document was not the fallback's acceptance (exit 0)`; 4 assertions |
| `R11` policy fallback | `.error (.unpairedSurrogate _) \| .error (.noncharacter _) => runFast …` | 0 | `check.sh` | 1 | `FAIL: the fallback refuses a different policy class than the one pinned`, `FAIL: expected 14 policy refusals, saw 0`, and `FAIL: 14 default-profile rows still diverge from the reference: …`; 4 assertions |
| `R12` length fallback | `.error (.inputTooLong _) => runFast …` | 0 | `check.sh` | 1 | `FAIL: the over-bound document was not the fallback's refusal (exit 0)`; 1 assertion |
| `R13` fast path | `.ok () => … runFallback doc`, with `runFast` still referenced from a branch that cannot be taken | 0 | `check.sh` | 1 | `FAIL: the fast-path arm is empty (accept 0, invalid 0)`, `FAIL: the outcome arms are empty (fast 0, fallback refusals 62, fallback accepts 59)`, `FAIL: no compared row carried arena bytes; the value comparison is vacuous`, `FAIL: no compared row carried event bytes; the value comparison is vacuous`, and the depth-128 row losing its observation; 5 assertions |

What each shows, and what it does not:

- **`R10` — the depth clause's fallback is live.** The cut sends the class the
  depth clause excludes back to the object, so the depth probes and the
  opener-rich document lose their fallback answers at once.  It does not show
  the clause's *stated* bound is right (that is `depthExceeded_openers` and the
  `DomainCheck.lean` guards); it shows the shell's routing is what carries the
  bound to a caller.
- **`R11` — the policy class is what the fallback answers.** The cut sends the
  fourteen documents the object accepts back to the fast path: the pinned policy
  set empties, and the run's divergence count becomes exactly those fourteen.
  The cut does not show the *reason and byte* are right — `DomainCheck.lean`
  pins those against `parseBytes` — only that dropping the fallback for the
  class is visible.
- **`R12` — the input bound is answered by the fallback.** The cut admits the
  over-bound document to the object's path; the over-bound assertion is the one
  that fires, and nothing else moves.
- **`R13` — the fast path is distinguishable and non-empty.** Routing every
  admitted document to the fallback removes the fast-path arm; the run reports
  the empty arm directly, and the payload comparison is reported vacuous rather
  than silently passing.  The first attempt at this cut — routing *all*
  documents to the fallback — failed the build instead
  (`build: the executable does not define leanllvm_json_pipeline`), because
  Lean's compiler eliminated the unused extern; that is a scaffolding failure,
  not a red, which is why the recorded cut keeps a live `runFast` reference.
