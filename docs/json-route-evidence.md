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
decides by the two-phase equivalent (the native phase-one verdict, then the
native character-policy scan `policy.c` defines on a candidate, with `admission`
and the library's `policyRefusal` retained as the suite's oracles; `R14` and
`R15` are that scan's own controls), and their uncut control is

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
  the clause's *stated* bound is right — that is the library's certificate
  (`depth_measured_no_refusal`, `depth_refusal_deep`) and the gate
  `tests/json-depth-clause.lean` — and it is a cut of the *probe's* opener-count
  decision.  The library's clause now reads the measured nesting instead, so
  the opener-rich document is inside the domain there; the probe's own decision
  is probes-owned and unchanged, and its `DomainCheck.lean` guard for that
  document is the row that no longer matches the library's verdict.
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

## The native policy scan's controls (`R14`, `R15`)

Phase two of the route's document decision is the native character-policy scan
`probes/json/route/policy.c` defines, and the library's own `policyRefusal` is
the oracle `--admit` runs on the same bytes.  The gate's comparison is the reason
tag, and a policy refusal's reason carries the byte it is reported at
(`unpairedSurrogate@1`, `noncharacter@1`), so the gate compares the class and the
position.  Two cuts show that comparison notices each of them.  Each was applied
to `policy.c` in place, built into its own `BUILD_DIR`, and run with `ROUTE=`
pointing at that build, so the shipped build was never the one under test; the
tree was restored from a saved copy after each (`cmp` clean) and rebuilt, and the
green run is the restored build's: 137 rows agree, `policy candidate 59, policy
scan run 58; control failures 0`.

| Cut | Applied in the copy | Build | Route command | Exit | Assertion that fired |
|---|---|---|---|---|---|
| `R14` the surrogate class | `policy.c`: the high-surrogate branch's `if (cv >= 0xD800u && cv <= 0xDBFFu)` → `if (0)`, so a `\uD800` form is accepted as an ordinary character | 0 | `check.sh` | 1 | `FAIL: lone-d800.json: the two-phase decision and the certified predicate differ`, also `double-high`, `high-char`, and `pair-d834`/`pair-i-json` — a *valid* pair refused, because its low half is then read as unpaired — then `FAIL: expected 14 policy refusals, saw 11` and `FAIL: 3 default-profile rows still diverge from the reference: lone-d800.json double-high.json high-char.json`; 9 assertions |
| `R15` the refusal's byte | `policy.c`: `policy_refusal_pos` returns `i - s`, the body-relative offset, instead of `i` | 0 | `check.sh` | 1 | every one of the fourteen policy rows: `FAIL: <row>: the two-phase decision and the certified predicate differ`, and the row itself `policy_native=unpairedSurrogate@0 policy_oracle=unpairedSurrogate@1 … reason=unpairedSurrogate@0 certified_reason=unpairedSurrogate@1 agree=0`; 14 assertions |

What each shows, and what it does not:

- **`R14` — the scan's classes carry decisions.** With the high-surrogate branch
  gone, a lone `\uD800` is admitted and a well-formed pair is refused: the
  refusal class moves in both directions at once, and the gate reports both.  It
  does not show the class is the *reference's* — the oracle rows
  (`policy_oracle=…`) and the differential sweeps are what compare that.
- **`R15` — the byte is part of the compared value.** The wrong offset is a
  plausible near-miss: the same class at the same document for a class-name
  comparison, and a disagreement here only because the tag carries the byte.
  It does not show the *class* is right, which `R14` moves and the oracle rows
  check.

The gate's rows are the corpus and the boundary documents; a scan that agreed on
those and not on another shape would pass.  The two-phase section of
`probes/json/route/README.md` records the two differential sweeps that stand in
for a wider row set — 1547 documents drawn from the rule's branch bytes and 3618
that place every escape form at every offset across two block boundaries, both
against the library's `policyRefusal`, with zero disagreements at class and
byte — and they are readings, not a proof: this unit has no refinement theorem
and is not in `kernel/json/`.

## The depth clause's control (`R16`)

Phase one of the decision measures the depth clause's number: the maximum running
depth over the document's structural delimiter sequence, which is `docDepth`'s
rule.  `--admit` reports both numbers (`native_depth`, the adapter's accumulator;
`certified_depth`, the library's `docDepth`) and the gate compares them wherever
the walk ran, beside the verdict and the reason; the depth pass's header also
carries the proved counter's recombined final depth and the accumulator's own, and
the gate requires those equal on every row.

The cut restores the rule this change replaced — an opener-*byte* count over the
whole document, string bodies included — and leaves everything else in place: the
walk, its structural lane list and the proved counter still run, and only the
clause's number moves.  It was applied to `shim.c` in place, built with
`BUILD_DIR=/tmp/route-cut`, and run as
`ROUTE=/tmp/route-cut/leanllvm-json-route DRIVER=/tmp/route-cut/driver bash probes/json/route/check.sh`;
the tree was then restored from a saved copy (`cmp` clean) and rebuilt, and the
green run is the restored build's (265 rows agreeing, `control failures 0`).

| Cut | Applied in place | Build | Route command | Exit | Assertion that fired |
|---|---|---|---|---|---|
| `R16` the depth clause's number | `shim.c`: `depth_measure` keeps the walk and the lane list, and sets `f->max` to a count of `[`/`{` bytes over the whole document instead of the maximum it tracked | 0 | `check.sh` | 1 | `FAIL: the opener-rich document did not take the fast path (exit 0):` with `fallback=accepted tokens=1 decoded=true`; `FAIL: opener-rich: the two-phase decision and the certified predicate differ` with `native_depth=129 certified_depth=0`; the same for `siblings` (`201` against `2`), `escaped` (`201` against `1`), `straddle-body`, `straddle-quote`, `neg-prefix` (`2` against `0`) and 113 of the 120 swept rows; then the depth gate's own expectations, `FAIL: <row>: measured depth native=… certified=…, expected …`; **129 assertions** |

What it shows, and what it does not:

- **The depth clause's number is compared, not just its class.** `neg-prefix`
  (`]] [[`) is the row that says so: under the cut the native side measures 2 and
  the library 0, while the verdict and the reason agree on both sides (`1` /
  `none`) and the row's own `agree` flag reads 1.  The shell's comparison is what
  reddens it, because it reads the two depths out of the row.
- **The clause's documents are the ones that separate the rules.** The
  opener-rich string (129 `[` bytes, nesting 0), 200 sibling containers (401
  opener bytes, nesting 2) and the escaped-quote body (200 `[` bytes, nesting 1)
  are each admitted natively under the fix and refused under the cut, and the
  fast-path assertion fires because the route takes the fallback for a document
  `admission` admits.
- **What it does not show.** The cut moves one number; it does not show the walk
  is right for any shape outside the gate's rows.  That is the fixed-seed sweep's
  claim (120 documents, compared on verdict, reason and depth) and the hand-written
  rows' — 11 documents each asserted against a measurement written in `check.sh`
  as well as against `docDepth` — and both are observations, not a proof: the
  walk has no refinement theorem and is not in `kernel/json/`.  The *predicate* it
  measures is certified (`JsonKernelCertificate.depth_bridge_core`); the native
  measurement is not.
## The escape-list guard's control (`R17`)

The route's fast path takes the pipeline's arm word from the admission's own
native call: `probes/json/route/escape_guard.h` decides whether the document
carries no byte the stage-1 escape list can name — no `0x5C` and no byte at or
below `0x1F` — and bit 1 of the arm is cleared when it does, because the list
arm 2 would build is empty on every block.  `probes/json/route/guard.sh` is the
gate.  Its subject is the pair of calls on the same bytes and the same staging:
arm 2, and the arm the guard selects; the verdict, the four cursors, the error
offset, the arena bytes and the event bytes must agree wherever the guard fires,
and the arm-2 list must be empty there.

This control is not a staged cut of the shipped code: the arm word is the
probe's, and `guard_check.c` forces bit 1 clear on a document whose arm-2 list is
not empty.  That is a differential control, exercised on every run rather than
recorded once, and it fires on 48 of the 164 documents the scenario feeds:

| Control | Applied where | What must happen | Observed |
|---|---|---|---|
| `R17` the forced arm | `guard_check.c`: a third call at arm 0, on every document whose arm-2 list is not empty | the result must change; a forced arm that agreed would mean the guard's decision is not the claim under test | 48 of 48 diverge, named in the transcript (`fast-esc` first, then the escape unit's `short:backslash-n`, `short:raw-control` and the rest); `controls_fired=48` |

The rows, from the same run:

| Row class | Documents | What is asserted |
|---|---:|---|
| the guard fires | 112 | the arm-2 list is empty, and the guarded call agrees with arm 2 field for field |
| the guard declines, arm-2 list non-empty | 48 | the forced arm 0 changes the result |
| the guard declines, arm-2 list empty | 4 | nothing beyond the pair, which is the same call (`site/site-ctl` in the timing table) |

What it shows, and what it does not:

- **The list's emptiness is the claim, and it is observed on every firing
  document.**  A guard that fired on a document whose list was not empty is a
  red, even where the two outputs happened to agree, because the next arm's
  consumer would be reading a list the call claimed not to need.
- **The documents that make a backslash-only guard wrong are in the set.**  A
  raw control byte inside a string is a position too: `raw-lf.json` and its
  siblings in `tests/json/corpus`, and `short:raw-control` in the escape unit's
  rows, are documents with no backslash whose arm-2 list is not empty.  They
  are the 48-row control class's members that a "no backslash" guard would have
  skipped; the guard's second byte class is what keeps them on arm 2.
- **What it does not show.**  That the arm decision is right on a document
  outside the 164 rows — the class is checked as a relation over the rows the
  scenario feeds, not proved; and the timing of the decision, which is
  `probes/json/core-shape/shape.sh`'s paired table and not this gate's.

## The no-event entry's cuts, observed at `66159e24` with this change

`kernel/json/stage2_noevent.c` and `kernel/json/pipeline_noevent.c` are additive
units; their route is `tests/json-noevent/check.sh` over the committed corpus in
`tests/json-noevent/corpus`.  The readings below were made on a worktree built
at `66159e24b93d7f78139d08a8d1794f32ae12e777` with the additive files present,
Lean 4.35.0 and clang/LLVM 21.1.8 from the flake.  Each cut was applied to a
throwaway copy of the tree; every cut tree compiled (exit 0) before its route
ran, and the uncut, unmodified worktree reached exit 0 with every `ok` line.

Unlike the cuts above, these six are **rebuilt inside the route on every run**:
the route compiles each cut from a copy of the committed source in its temporary
directory and checks the firing assertion, so a green run exercises every
negative control without touching the tree.

| Cut | Cut applied in the copy | Build | Route exit | Assertion that fired |
|---|---|---|---|---|
| NE1 payload | the record payload omitted from the sum accumulator (`terms += tag + len`) | exit 0 | 1 | `FAIL: the driver exited 3 on the stage2/list route/arm`, then `FAIL … reading: reference 1/1/9223372036854775818, no-event 1/1/9` on `acc-string`, `acc-utf8-raw` and nine further accepted record-bearing documents |
| NE2 A tail list | the stage-2 tail's `xp, *nxp` → `xp, 0` | exit 0 | 1 | `FAIL: the driver exited 3 on the pipeline/list route/arm`, then `FAIL … reading: pipeline 1/1/214, no-event 1/1/9223372036854775819` on `acc-esc-string` and the other escape-bearing documents; no `nk:` or `nxp:` line fires |
| NE2 B pre-zero | the entry's three pre-zero stores deleted | exit 0 | 1 | `FAIL … refusal slots: expected zero, got 16045690984833335023/16045690984833335023/16045690984833335023` on `refuse-utf8-gate` only |
| NE3 refusal stores | the three refusal stores deleted | exit 0 | 1 | the same sentinel line on every refusing document |
| NE4 identity | one comment line appended to `kernel/json/stage2.c` | exit 0 | 1 | `kernel/json/stage2.c differs from 66159e24…`, `FAIL: a protected artefact differs from the base revision` |
| NE6 census | a `static`, `used` reference to `leanllvm_json_s1_masks` appended to `stage2_noevent.c` | exit 0 | 1 | the census prints `leanllvm_json_escape_expand` and `leanllvm_json_s1_masks`, then `FAIL: the no-event object's symbol census is not the declared one` |

What each shows, and what it does not:

- **NE1 — the reading is the certified fold's.** The cut moves the sum on the
  documents that carry a record and leaves every refusal and every number-only
  row green, so the comparison notices a wrong arithmetic in one assertion
  family. It does not show that the body refines the model: that is the walk
  obligation's subject, and the route samples a corpus.
- **NE2 A — the tail is wired to stage 1.** With the list dropped, `nk` and
  `nxp` still agree and the escape-bearing readings move, so the cut isolates the
  tail's use of the stage-1 list rather than the stage-1 outputs themselves.
- **NE2 B — the gate's refusal leaves a total post.** Deleting the entry's
  pre-zero surfaces the sentinel on the UTF-8 gate's document only, which is the
  one refusal that returns before the walk; every accepting row and every walk
  refusal stays green.
- **NE3 — the refusal words are written, not merely unread.** The sentinel
  pre-fill is what separates "wrote the declared zeros" from "never touched the
  slot"; the cut makes that difference visible.
- **NE4 — additive means additive.** The comparison passes trivially before the
  change, so the one-byte control, not the pass, is its evidence.
- **NE6 — the dependency set is the declared one.** The staged reference widens
  the undefined set and the same census reports it, so the clean object's
  one-symbol set is not vacuous.

### The route arm and the frozen event arm

The route boundary has its own arm, and it was observed on the worktree carrying
the change: `tests/json-noevent/check.sh` exits 0 with every `ok` line, over the
69-document corpus and the 183 base rows.  The observations the arm makes:

- **The two arms agree on every admitted document.**  The route's no-event arm
  (`--consume-noevent`) and the C caller (`driver --noevent`) print one identical
  `reading` line on all 68 admitted documents; the empty document is outside the
  arm and the caller refuses it at its own entry.  Each line's `verdict`, `nk`,
  `nxp` and `err` equal the certified event arm's observation of the same
  document, and on an acceptance its `tokens`, `values` and `sum` equal the
  unchanged consumer's fold of the certified stream.
- **Every refusal carries zero and the certified offset.**  A refusal leaves all
  three reading words zero, with `err` the manifest's pinned offset (the
  document's length for the UTF-8 gate's refusal).  The sentinel cut in NE3
  separates "wrote the zeros" from "never touched the slot".
- **The entries agree with the certified routes.**  Over the corpus, NE1 and NE2
  compare the two entries' readings with the certified entries' at the same
  documents and the final line reports the agreement; the sentinel, the
  dependency census and the byte identity are the other three boundaries the
  run prints.
- **The protected set is byte-identical to `66159e24…`.**  The six ABI artifacts
  (`kernel/json/stage2.c`, `stage2.h`, `pipeline.c`, `pipeline.h`,
  `probes/install/ir/stage2.candidate.ll`, `json-pipeline.candidate.ll`) are
  compared with that revision's blobs, and the NE4 one-byte control reddens the
  comparison.
- **The event arm is frozen against 183 base rows.**  `tests/json-noevent/
  base-event-rows.tsv` records base revision
  `691ca12dc1b6afa8e05ff5828003fdadd15c9c1c`, the base binary's SHA-256
  `86fbb06b…`, and one row per document: exit word, six observation words, the
  arena and event payload digests, the document's digest and the whole stdout's
  digest.  Every row is reproduced on the current tree.

Three cuts reach those assertions; each was applied to a throwaway copy of the
tree, rebuilt there, and the uncut control in the same command exited 0.

| Cut | Cut applied in the copy | Build | Route exit | Assertion that fired |
|---|---|---|---|---|
| NE7 zeros | the no-event arm's reading wired to zeros in `shim.c` | exit 0 | 1 | `FAIL: --consume-noevent exited 5 on documents/acc-empty-object`, then `an acceptance's reading is tokens=0 values=0; the two counts must agree and be non-zero` |
| NE7 offset | the arm's `tokens` and `values` each incremented in `shim.c` | exit 0 | 1 | `FAIL: the route and the C caller print different readings on documents/acc-empty-object`, with `tokens=3 values=3` against the driver's `tokens=2 values=2` |
| NE8 | the event arm's printed `nev` word changed in a copy of `RouteMain.lean` | exit 0 | 1 | `FAIL: tests/json/corpus/bom.json: the event arm's stdout digest bc50ca33… is not the base row's e6d851f1…` |

The cuts are independent at their own assertions: under NE7 zeros the event
arm still reproduces all 183 base rows with 0 mismatches, and under NE8 the route
and the C caller still print one identical reading on every admitted document.
NE7's zeros fires the arm's *own* exit-5 guard rather than the comparison, so the
guard and the comparison are both witnessed.

**An owed run.**  The lane used for the Lean evidence has no `xxd` in its dev
shell, so `tests/json-noevent/check.sh` exits 3 at its SETUP line there; the
event payload digests need it.  The run recorded here is the worktree's, with
every harness input's SHA-256 matching the lane's.  A C-observable run on a lane
that provides `xxd` remains owed, and the worktree run is the evidence until it
arrives.

The route does not prove the new body refines the model and says nothing about a
document the corpus does not carry; the walk obligation and the emitted literal
chain stay in the Lean development and are not what these cuts show.

## The restated record relation, and what the deployment half observes

The record relation now has two rows stated at readings a parsed document can
fill: a plain string or key record's body is the escape-aware scan of the
body's first document byte, and a number record's payload is
`strtodSpec` of `StrtodReader.reader`'s decimal of the span's lexeme, with the
lexeme normalised by the reader (`E`/`e`, an explicit `+`).  This section
records what the tree's executable instruments say at that relation, and where
the boundary between theorem and observation lies.

Observed at `e88ee2d` (`e88ee2d5b502b46ce7e1206ba54e972853fd1e3d`) with the
restatement present in the working tree, Lean 4.35.0, clang/LLVM 21.1.8 and
Linux 6.18.64 from the flake.  The tree's source manifest — `sha256sum` over
every tracked file and every untracked source file, sorted by path — was
`4a8f20eb8940bf26b363023e2e2d8d199c47f405d32d11103e7a52d1001ec6b8` when the
runs below were made (this section's own edit postdates it); `git rev-parse
HEAD` was `e88ee2d5…`, the branch was `main`, and the working tree had 21
tracked files modified and three files added.  Every command ran from the
checkout's root through `nix develop -c`; `nix develop -c lake build` (the
default targets) exits 0 at 2,514 jobs, and the route binary the no-event check runs was rebuilt at this tree by
`nix develop -c bash probes/json/route/build.sh`, which exits 0 and prints
`ok: …/probes/json/route/build/leanllvm-json-route` (sha256 `56291191…`;
adapter driver sha256 `d6b0d041…`).  The route's link carries the six kernel
units, the two no-event entries and the entry table: `nm` on the binary defines
`leanllvm_json_pipeline`, `leanllvm_json_pipeline_noevent`,
`leanllvm_json_stage2`, `leanllvm_json_stage2_noevent`,
`leanllvm_json_stage2_noevent_lib`, `leanllvm_json_entry_table`,
`leanllvm_json_entry_pos8`, `leanllvm_json_entry_b8`, `leanllvm_json_entry_b3`,
`leanllvm_json_s1_masks`, `leanllvm_json_escape_list`,
`leanllvm_json_escape_expand` and `leanllvm_json_utf8`; the adapter's undefined
project symbols are exactly `leanllvm_json_pipeline`,
`leanllvm_json_pipeline_noevent` and `leanllvm_json_entry_table`.

### What the tree proves, and what stands under it

For the admitted domain, given a caller's rows, the tree proves that the
no-event walk's returned word *is* the reference decoder's word, in both
directions and with the parser's own witness: one exactly where
`parseBytes Limits.default (ByteString.literal bs) = .ok t`, zero exactly where
it returns `.error e` (`stage2NoEventWalkAccepts_iff`,
`stage2NoEventWalkRefuses_iff`, from `stage2NoEventWalkDecisionWord`), at one
fuel inside the potential's credit and with the boundary stated at that word.
At an admitted document, with the rows, the word is one and no refusal exists
(`stage2NoEventWalkDecision_admitted`).  The accept arm's record supply exists
at every accepting parse (`stage2NoEventWalkRecordsSupply_of_parse`), at the
restated rows; the two count equations the acceptance carries are classified:
the length is relation-determined (`Stage2NoEvent.length_nonSeparators`), the
term sum is not (`countsTieDoc_terms_two_derivations` gives two `ArenaBound`
derivations at `"\/"` with equal lengths and term sums 6 and 7), and the tie is
exactly the pair of register-versus-data comparisons
(`stage2NoEventWalkAccept_counts_iff`).  The walk's accumulated output evidence
— the event list, the tokens, the derivation and the two counts — is the run's
own induction invariant, not a caller's witness: `Stage2NoEventWalkTrace_iff_report`
reduces it to a flat report plus the arena bound, `of_zeros` inhabits it at the
seed, `Stage2NoEventWalkTrace.step` extends it along each route, and the
terminal rebuilds it from the exit (`stage2NoEventWalkTrace_of_accept`,
`stage2NoEventWalkExit_trace`).

What that claim stands on, and does not include:

- **the installed artefacts implement the pinned IR.**  The C-to-IR step for a
  fixture and the IR-to-object step for the installed units are compiler
  correctness: assumed, not proved here.  The identity arms and the route checks
  below are evidence *for this assumption*, never part of the theorem.
- **the native admission agrees with `admission`** where the probe compares the
  two-phase decision, as its own agreement check states; that agreement is not
  modelled in Lean.
- **the rows' class producers and the seed head are produced by the caller.**  The
  per-class producers build the rows and the accept terminal is built at the
  reference parser's own tape.  The trace is **not** caller data: at the seed it
  is `Stage2NoEventWalkTrace.of_zeros`, along a segment the preceding segment's
  `trace'`, and at a terminal the exit's own report
  (`stage2NoEventWalkTrace_of_accept`, `stage2NoEventWalkExit_trace`), with
  `Stage2NoEventWalkTrace_iff_report` saying a trace is a flat report plus the
  arena bound and nothing else.  What no theorem supplies is the connection from
  the compiled entry's argument and memory words to the seed head and to the
  producers' rows.
- **the number payload's reading is the emitted scanner's.**  `StrtodReader`
  proves the reader's field extraction from a lexeme; that the C loops'
  accumulators (`ip`, `fr`, `idig`, `fdig`, `exp10`, the sticky window) hold the
  fields the reader returns is stated by that module as its own remaining
  assumption, not proved.

A green check is therefore evidence for the assumption, or an observation of the
C units, and never a piece of the theorem.

### The restatement's executable footprint

The restated rows are a change to a `Prop`-valued relation, so nothing in the C
routes reads them.  Three executable surfaces touch them at all:

- **The build's axiom pins.**  `LeanLLVM/Refinement/JsonStage2Spec.lean` pins
  `#print axioms` for `Stage2EventRel` and its constructors; the pins read
  `[propext, Quot.sound]` after the restatement (they read `[propext]` before
  it), because the reader's `Bytes`/`ByteString` layer carries `Quot.sound`.
  These pins are `#guard_msgs`, so `lake build` checks them; the build above is
  the observation.
- **`tests/json-noevent.lean`** pins relation instances only at the null and
  true-tag witnesses; its `#guard`s and theorems exit 0, and no str or number
  row is exercised there.
- **`tests/json-noevent/check.sh`'s `--value` arm (NE13)** is the only
  executable consumer of `StrtodReader.reader`: the line is
  `renderValue (canonValue v)`, and `canonValue` normalises each number lexeme
  through the reader.  Its corpus is `tests/json-value/corpus` (13 documents),
  and `numbers-noncanonical` (`[1.00,1e0,2.5E-3,0.5,-1,42]`) carries the forms
  the reader normalises.  This observes the reader, not the relation.

The stage-1 routes below (`json/check.sh`, `json-classify/check.sh`,
`json-s1-masks/check.sh`, `json-entry/check.sh`, `json-utf8/check.sh`) read
none of the relation, and their observations are untouched by the restatement.
The stage-2 observations are the C entries and the compiled route, whose bytes
did not change.

The table's revision column names the freeze each row belongs to.  The runs
were first made at `4a8f20e`; the frozen code is `ea641ebc…`.  The freeze
digest is `git diff e88ee2d 65a26b4 --binary -- LeanLLVM LeanLLVMTest
LeanLLVM.lean`, over committed bytes only, so this document's own text does not
move it.  The diff from the observed tree to the frozen one is Lean proof
modules, the umbrella's import lines and the test pins: it touches no test
script, kernel source, corpus or fixture, and the route's emitted-C cone — the
69 modules `probes/json/route/build.sh` lists — is identical at both.  The rows
whose instruments read C units or corpora therefore stand on inputs the freeze
does not change, and the Lean-side rows and the two Lean test files were re-run
at the frozen bytes; the commands below are the frozen runs where they were
repeated.

On the frozen bytes (`65a26b4`, Lean 4.35.0 and clang/LLVM 21.1.8 from the
flake), from a checkout whose source hashes match the commit:
`nix develop -c lake build` exits 0 at 2,518 jobs with zero `^error` lines
(`LeanLLVMTest`'s guarded pins included); `nix develop -c bash
probes/json/route/build.sh` exits 0 and writes the byte-identical binary
(sha256 `56291191…`); `nix develop -c bash tests/json-noevent/check.sh` exits 0
with the same 23 `ok` lines; and `tests/stage2-noevent-rows.lean` and
`tests/json-noevent.lean` each exit 0.

One provenance note, because a freeze digest is worth what the build behind it
covers: the first freeze digest named a commit whose `LeanLLVM.lean` — at the
repository root, outside the two directories staged — lacked the three
registration imports, so the new modules were unimported and
`nix develop -c lake build LeanLLVMTest` exited 1 with `Unknown constant
'LeanLLVM.Refinement.stage2NoEvent_step_terms_delta_not_relation_determined'`.
The corrected commits `557f5c8` and `65a26b4` add the imports and the trace
module; the digest above is over those bytes, and the build and checks above
were run on them.

| Claim | Instrument | Revision | Corpus / arms | What it does not cover |
|---|---|---|---|---|
| The reference runner's renderings agree with a hand-written manifest, and a tampered row is a mismatch | `nix develop -c bash tests/json/check.sh` | `e88ee2d` + tree above | 130 manifest rows over `tests/json/corpus`; tampered-manifest arm | The stage-2 relation or the walk; the manifest is hand-written, not the runner's own output |
| The pinned classifier fixture, the Lean body and the installed object agree; the defect detector bites | `nix develop -c bash tests/json-classify/check.sh` | `ea641ebc…` | 71 windows (9 manifest rows, 70 corpus windows over 130 files, mixed block); object sha256 `95a38141…` | The relation; the object's behaviour on an unaligned pointer |
| The mask unit's object and the Lean body agree on the rows the run reaches | `nix develop -c bash tests/json-s1-masks/check.sh` | `ea641ebc…` | exits 3 with `SETUP: s1f_lo_tab not found in the kernel source`; the run reaches the row comparison (a mismatch would print `FAIL` and exit 1) and then stops at its defect-mutation step, which searches `kernel/json/s1_block.c` while the table lives in `s1_block_impl.h` — the same at `e88ee2d` (`grep -c s1f_lo_tab` is 0 in the `.c` at both) | Whether the rows are right: the check ends with a setup fault and prints no `ok` line, so its negative control is unexercised at this tree |
| The no-event stage-2 and pipeline entries agree with the certified entry and the unchanged fold | `nix develop -c bash tests/json-noevent/check.sh` | `ea641ebc…` | 69 documents, 68 stage-2-route and 69 pipeline-route, `both`/`list`/`pipeline` arms; 183 frozen event rows; 13 value documents | That the compiled stage-2 call equals the reference decoder on all admitted documents; see the boundary below |
| The entry unit's three kernels agree with the Lean bodies, row for row | `nix develop -c bash tests/json-entry/check.sh` | `ea641ebc…` | 197 595 rows from 6 corpus streams and 65 859 arm streams; object sha256 `f712e98a…` | The stage-2 walk; the relation; each detector is one class's rows |
| The UTF-8 stage's object, Lean body and measured statements agree, and the stage's behaviour matrix is re-derived | `nix develop -c bash tests/json-utf8/check.sh` | `ea641ebc…` | 73 610 rows per gate value (27 corpus + 73 583 arm); 13 `ok` lines; defect object moves 144 rows | The stage-2 walk; the relation; the timing arm was not re-run |
| The driver refuses an unmodelled return and function attribute, and the loop fixture is emitted with the relation's block roles | `nix develop -c bash tests/m4-loop-emission.sh --capture`, `--return-attr`, `--function-attr` | `ea641ebc…` | three modes, each exit 0 (`all assertions held`); `--declare-attr` is added after this revision and has no evidence row here | The stage-2 walk; the C-to-object step |
| The stage-2 unit's text is the measured text, modulo its declared deletions and new text | `nix develop -c bash kernel/json/identity/source-identity.sh --unit stage2` | `ea641ebc…` | 45 entities, walk deleted arms | exits 1 at one entity: `s2_walk` differs by one token (`p` for `n` at the quote arm's `od_fail`), the deliberate "report the opening quote for unterminated strings" change; the identity list does not yet accommodate it, and the difference is present at `e88ee2d` (the file is unmodified) |
| The pipeline unit's source and emitted-code identities hold | `kernel/json/identity/source-identity.sh --unit pipeline`; `ir-identity.sh --unit pipeline` | `ea641ebc…` | call census and emission | The stage-2 walk's rows; each arm is a text/emission identity, not a semantic refinement |
| The relation's axiom footprint is exactly `propext` and `Quot.sound` after the restatement | `#guard_msgs` breaks in `LeanLLVM/Refinement/JsonStage2Spec.lean`, checked by `nix develop -c lake build` | `ea641ebc…` | 9 pins (`Stage2EventRel` and its constructors) | Not a check of the rows' content, only of the proof's footprint |
| The no-event relation's witness pins and the row tier's interface | `nix develop -c lake env lean tests/json-noevent.lean`; `nix develop -c lake env lean tests/stage2-noevent-rows.lean` | `ea641ebc…` | relation instances at the null and true-tag witnesses; 9 `#check`s and 9 axiom pins | The str and number rows: neither file exercises them |

The stage-2 unit has no emitted-code identity arm: `ir-identity.sh --unit stage2`
exits 3 with `SETUP: unit stage2 has no IR identity arm; implemented units: s1
entry utf8 escape pipeline noevent pipeline-noevent`.  The emitted-code identity
that does exist for the stage-2 path is the no-event check's protected-artefact
comparison and its one-symbol censuses (NE4/NE6), not an arm of that script.

### What the green no-event run supports, and what it does not

`tests/json-noevent/check.sh` exits 0 with every `ok` line.  What it supports:

- **The two no-event actors agree on the corpus.**  The shipped route's
  `--consume-noevent` and the C caller's `--noevent` print one identical
  `reading` line on all **68 admitted documents** of the 69-document corpus; the
  empty document is outside the arm and refused at the driver's own entry
  (`ok: the route and the C caller print one identical reading on all 68 admitted
  documents`).
- **That reading is the certified event stream's.**  On those documents the
  line's `verdict`, `nk`, `nxp` and `err` equal the certified event arm's
  observation and its `tokens`/`values`/`sum` equal that arm's unchanged
  consumer fold (`ok: every one of those readings equals the event arm (six
  words, tokens, values, fold sum)`); the event arm reproduces all **183** rows
  of `tests/json-noevent/base-event-rows.tsv` — exit word, six observation
  words, arena and event payload digests, document digest and stdout digest
  (`ok: the event arm reproduces all 183 base rows`).
- **The manifest's pins hold per document and arm.**  Every row's verdict,
  refusal offset and readings equal the manifest's, over the corpus's three arm
  assignments: 54 documents in `both` arms, 14 escape- or control-bearing
  documents in the `list` arm, one `pipeline`-only document — for 68 stage-2
  documents and 69 pipeline documents (`ok: every document agrees with the
  certified stage-2 entry in both arms`; `ok: the two pipelines agree end to
  end, nk and nxp included, in both arms`).
- **The refusals carry the declared zeros and the certified offsets**, and every
  class `kernel/json/stage2.h` names has a document
  (`ok: every refusal class carries its pinned offset and zeroed readings`).
- **The negative controls fire in-run**: the record payload removed, the tail
  list zeroed, the entry pre-zero deleted and the refusal stores no-opped each
  move the assertion family it belongs to, so the comparisons are live
  (`ok: omitting the record payload fires the reading assertion on strings
  only`; `… zeroing the tail beside agreeing nk/nxp … on escapes only`;
  `… deleting the entry pre-zero leaves the sentinel on the UTF-8 gate only`).
- **The value arm carries the reference's canonical value or refusal** on the
  13 `tests/json-value/corpus` documents, including the non-canonical number
  spellings, and a tampered expectation is rejected.

What it does **not** support, stated as narrowly as it is true:

- **It is not "the compiled stage-2 call equals the reference decoder on all
  admitted documents".**  It is an equality between two C entries, the
  certified event arm and the unchanged consumer fold, on 69 committed
  documents.  The corpus is a sample, not the admitted domain: a document
  outside it has no row.
- **The stage-2 refusal offsets are the certified entry's**, so on a refusal the
  agreement is between the two entries and the manifest, not a comparison with
  `parseBytes`' own error and offset.  The one arm that reads the reference
  parser directly is `--value`, on its 13-document corpus.
- **It says nothing about the relation.**  The rows the entry writes are
  compared with the manifest and with the event arm's stream; whether those
  records inhabit `Stage2EventRel` is not observed by any route.
- **It says nothing about the installed unit's text.**  NE4 checks the
  protected artefacts' bytes against `66159e24…` and the two identity arms'
  symbol census; the unit's token identity is the separate arm above, which
  does not pass at `s2_walk`.

### What remains unproved

The north star's equality — the compiled stage-2 call's run equals the
reference decoder's on the admitted domain — is not a theorem at any document.
The gap between the theorems and the executable observations is these three
things, and no fourth:

1. **No row producer and no seed head from an executable start state.**  Every
   decision and boundary theorem is stated at `hrows : Stage2NoEventWalkRows
   calls mem F` and `hhead : Stage2NoEventWalkHead K mem k s`; the trace is
   earned at those heads (`of_zeros` at the seed, `trace'` along a segment, the
   exit's report at a terminal), so it is not a third caller-supplied premise.
   The per-class producers build the rows and the accept terminal at the
   parser's tape.  Nothing connects the compiled entry's argument registers and
   memory words to the seed head or the producers, so no theorem's conclusion is
   about the binary the route runs.
2. **The acceptance's read-back identity is carried, not derived.**  The term
   equation is stated at `consumeRecords bs arena rs`, and the relation does not
   determine that list (nor its term sum) — `stage2NoEvent_str_len_free` realised
   at the `"\/"` witness with two `ArenaBound` derivations.  The two traces at
   the same tokens are not one by any relation-side theorem, so the deployment
   must supply that identity; the tie is exactly the two register comparisons
   (`stage2NoEventWalkAccept_counts_iff`), and nothing in the tree computes the
   counted-token register from a document.
3. **The number payload's reading stops at a hypothesis.**  `StrtodReader`
   proves the reader's field extraction from a lexeme and that the compiled
   scanner's loops *as a body* compute it; that the C accumulators hold those
   fields is that module's own stated remaining assumption.  The restated
   number row therefore carries a hypothesis about the installed unit beside
   the `strtodSpec` conversion, and no route compares the two at the ABI.

Everything else in the deployment half is either proved (the verdict tie, the
boundary, the record supply, the counts classification) or assumed as stated
above (compiler correctness for the C-to-IR and IR-to-object steps, and the
native admission's agreement).


## The number spelling, the read-back split and the rows from the start, observed at `34dcec1`

The five commits between `f24a048` and `34dcec1` do not touch the emitted C.  They
change the Lean side the deployment argument stands on: the number arm now names
the document's own lexeme and derives its acceptance from the reader; the two
counters the acceptance carries are split into a length that is a theorem and a
term sum that is not; the rows bundle, its head and its trace are produced from
the record's own start state; and the depth-zero case those producers cannot
reach is proved empty rather than described.  This section records what the
tree's instruments say at those bytes, and where the boundary between theorem and
observation still lies.

The frozen code is `34dcec1` (`34dcec1e6cc778492d0b764e2339d8151afd6423`), and
the freeze digest is
`sha256 (git diff f24a048 34dcec1 --binary -- LeanLLVM LeanLLVMTest LeanLLVM.lean)`
= `78f7bcd59f8ffea385f10a06d9ac65a2f2f554017cde3b629d185ad066a2f261`, over
committed bytes only.  The range is nine files, 2,295 insertions and 53
deletions: the three new modules (`JsonStage2NumberPayload`, `JsonStage2NoEventWalkReadbackIdentity`,
`JsonStage2NoEventWalkRowsAssembly`), the restatements in `JsonStage2Body`, two
row modules, `LeanLLVM.lean`, `LeanLLVMTest/Refinement.lean` and
`docs/contract.md`.  The digest's cone is the eight files inside its three
paths.

**What the freeze does not touch.**  `git diff f24a048 34dcec1 -- kernel probes
tests` prints nothing: every kernel source, every harness script, every corpus,
manifest, fixture and frozen row file is byte-identical at both revisions.
Consequently the emitted-C cone `probes/json/route/build.sh` links — the six
certified kernel units, the two additive no-event units, the depth-counter
fixture, the policy scan and the 69 Lean modules whose C the link consumes — is
the same text at `f24a048` and at `34dcec1`, and the instruments below are the
same scripts.  Their *inputs under the Lean library* moved, which is why the rows
of the earlier section, which belong to `ea641ebc…`, are not reused here: every
number below was produced on the frozen bytes.

**The bytes observed.**  The tree was shipped as `git archive 34dcec1`
(archive sha256 `f6a6f26b95ca0cc0b80d313ba312ac5e655440956fcc720df5e724752d1f8a74`),
extracted into an empty directory, and registered with `git init -q && git add
-A`.  The commit that produced has no relation to the project's history, but its
tree does: `git rev-parse HEAD^{tree}` is
`6438609d070ff6cfb324960f40a66281b3a7ade8`, the value of `34dcec1^{tree}`.  All
commands ran on a Compute Engine instance (`lp-c4-01a21253`, `europe-west1-b`, 8
vCPU, 62 GB, Lean and clang from the flake) from that tree; no command ran on the
development machine, and nothing was copied back except the outputs quoted here.
Disk was the binding resource on that instance.  It completed the default
target before being reclaimed: exit 0 at 2,524 jobs on the archive above, and its
tree hash equalled `34dcec1^{tree}`.  Its route and check runs were lost with
its disk.  The instance the remaining rows were measured on
(`evidence-c5-01a21253`, same zone and shape, 100 GB) received the same archive
byte for byte — `sha256sum` of the shipped tar is the same
`f6a6f26b95ca0cc0b80d313ba312ac5e655440956fcc720df5e724752d1f8a74` — and
produced the same tree hash.  So the default-target row below has two independent
observations on one set of bytes; every other row is from the second instance.

**A prerequisite the archive does not carry.**  `tests/json-noevent/check.sh`
guards its protected-artefact comparison with
`git cat-file -e 66159e24b93d7f78139d08a8d1794f32ae12e777^{commit}`, so a tree
made only by extracting the archive and running `git init -q && git add -A` exits
3 with `SETUP: the pinned base 66159e24b93d7f78139d08a8d1794f32ae12e777 is not in
this repository` — measured on a second copy of the same tree, with the route
binary and driver pointed at by `ROUTE`/`NOEVENT_DRIVER`.  The base commit's
objects were fetched into the shipped tree's repository from a bare repository
holding that commit; no working file changed (`git status --short` empty), and
the comparison then ran against the base revision's blobs rather than being
skipped.  The no-event row is therefore over the shipped bytes plus the history
the check requires, not over the archive alone.

The route binary's digest is an identifier, not a reproducibility claim:
`strings` on it shows the absolute build root on its library path, so the same
sources at a different checkout path yield a different hash.  It is recorded for
this artefact and is not compared with the earlier section's `56291191…`.

### The four proved items, and what each changes

**The number path reads the document's spelling, and its acceptance is derived.**
The walk's number arm had asked the document's slice to be `d.lexeme`.  `Decimal`
renders the exponent marker as `0x65` and the sign as `0x2D` or nothing, so no
well-formed decimal spells `1E5`, and the arm's premise had no witness at a
document the scanner accepts: `lexeme_no_upperE`, `lexeme_no_plus`,
`lexeme_ne_eDoc`, and the former premise's emptiness at `1E5` as
`numberSlice_ne_eDoc`.  The arm now quantifies over the document's own `lex` with
the reader's witness, and the payload follows from the reader at that spelling:
`numFastEmitted_of_reader`, `numberPayload_of_reader`,
`numberPayload_spelling_invariant`, `stage2NumFast_writes_strtodSpec_of_reader`,
with `eDoc_payload` and `eDoc_numberArm_witness` inhabiting the restated premise
at `1E5`.  Separately, the emitted index scan's acceptance had been a hypothesis
at six sites; `numLexScan_accepts_iff_numLexB` identifies it with the tree's
structural `numLexB`, `LeanLLVM.JSON.numLexB_iff` carries that to `RfcNumber`, and
`numLexScan_accepts_of_reader` composes it with the reader's own tie, so the six
`hscan` binders are gone and the acceptance is derived where it is used.
`docs/contract.md` is restated to match: the lexical agreement is now proved, and
what remains the scanner's obligation is the token's *extent*.

What this changes for the deployment half is narrow and worth stating exactly:
the number arm no longer carries either a false premise or an undischarged
acceptance.  It does not connect the C function to `numLexScan`.  `numLexScan` is
a model of the emitted control flow written in the same module as the proofs; it
has no `@[implemented_by]` annotation and no C reads it.  The theorem is about the
model.

**The read-back splits at what the walk carries.**  `Stage2NoEventWalkCountsTie`
states the acceptance's two equations.  `consumeRecords_length_eq_nonSeparators`
makes the first a theorem of the relation and the document's non-separator count;
`stage2NoEventWalkCountsTie_step` and `…_steps` compose the pair along the trace's
own step deltas, so the walk's accounting produces the pair at the event list it
accumulates.  The second equation does not survive: at the records of `"\/"` with
a two-byte arena there are two `Stage2Records` derivations of equal length and
term sums 6 and 7 (`stage2NoEventRecords_terms_two_derivations`,
`stage2NoEventWalkRecordsSupply_terms_two_derivations`), and no function of the
document, the arena and the tokens returns the read-back's term sum
(`stage2NoEventReadback_terms_not_functionable`,
`stage2NoEventWalkCountsTie_readback_not_determined`).  At an acceptance the pair
is the boundary's `consume` field at the reference's read-back
(`stage2NoEventWalkReferenceAccept_countsTie`).

What this changes: the deployment no longer supplies the length equation — it is
derived — and the term-sum equation is no longer an unexplained carrier but a
proved non-functionability.  The consumer still supplies the chosen records and
the read-back identity.

**The rows are assembled from the state the program reaches.**
`Stage2NoEventWalkRows` was a caller-supplied function-per-head.  Now
`stage2NoEventWalkRows_of_start` takes the record's precondition and the four
staged objects and returns the carry (`K.tok = 0`, `K.terms = 0`, `K.arena = []`),
the entry-state invariant, the two base reads (`readLanes32` on the entry stream,
`readBytes` on the document), and a bundle `R` that *is*
`stage2NoEventWalkRowsAtStart`; on the nonempty-stream branch it also returns the
seed head `NodeBlock5`, its run, its zero depth and frame, and the fact that
`R.row` there is `stage2NoEventWalkSeedRow` at `Stage2NoEventWalkTrace.of_zeros`.
`stage2NoEventWalkReferenceRun_of_start` hands that bundle to
`stage2NoEventWalkReferenceRun_spec`.  So the bundle, the head and the trace are
produced; the consumer supplies the four class producers
(`…StringReady`, `…BracketReady`, `…BraceReady`, `…ValueReady`) — each with its
route staging and terminal exit — and the terminal exits' carried facts.

**The depth-zero case is proved empty.**  The seed head's `phi` layer is
`%sp.0.ph1403 = 0` and `%frame.0.ph1402 = 0`
(`stage2NoEventWalkSeedHead_sp`, `…_fr`).  Every container producer needs a
positive depth: the pair rows take `1 ≤ sp`, `sp < 2 ^ 32`, `1 ≤ fr`, `fr < 2 ^ 8`,
and the descend branches carry `sp ≠ 0`.  `stage2NoEventWalkSeedHead_noPosDepth`,
`…_noPosFrame`, `…_noDescend`, `…_noPair`, `…_noPairWords` and
`…_noContainer` refute each at zero.  The consequence is not a proof gap papered
over: at the start state the rows function's container coverage excludes a
document whose first entry opens `[` or `{` and whose next entry is not the
closer.  The depth-zero pair cases (`[]`, `{}`) are the `…ZeroRow` reductions and
do have terminal producers.

### The claim table

Every row was re-run on the frozen bytes from the shipped tree.  The digest column
names the artefact the row is about where the instrument produces one, otherwise
the instrument's own bytes.  The default target does not build the five JSON
executables the stage-1 checks drive, so the table's stage-1 rows were measured
after `nix develop -c bash probes/install/lake-locked.sh build leanllvm-json
leanllvm-json-classify leanllvm-json-s1-masks leanllvm-json-entry
leanllvm-json-utf8` (exit 0, 2,528 jobs); that build is a prerequisite of those
rows, not part of the default target's claim.

| Claim | Instrument | Digest | Corpus / arms | What it does not cover |
|---|---|---|---|---|
| The default target elaborates, the new pins among it | `nix develop -c bash probes/install/lake-locked.sh build` | 2,524 jobs, exit 0 in 1,246 s (the first observation, on the reclaimed instance, also 2,524 jobs in 1,365 s); freeze `78f7bcd5…` | the whole library and `LeanLLVMTest`; 1,876 `#guard_msgs` blocks, 81 of them new | Nothing about the C; a widened footprint fails here, not a proof of the rows |
| The route links the six kernel units and the two no-event entries | `nix develop -c bash probes/json/route/build.sh` | binary sha256 `c1541bbb24a6efbe6e40c9fc414758de952bc7f78e86070317831004d25d301d`; adapter `f060411c2737cd8505aedaacf27590a41ad9393d0857c60d0cb673e58922bb4e` | 69 Lean modules' C, 8 C units, `RouteMain.lean` | Not a semantic check: the link's own symbol assertions only |
| The two no-event entries agree with the certified entry and the fold | `nix develop -c bash tests/json-noevent/check.sh` | 23 `ok` lines, exit 0 in 261 s; manifest sha256 `f5565f83…` | 69 documents (68 stage-2, 69 pipeline), `both`/`list`/`pipeline` arms, 183 frozen event rows, 13 value documents | The relation, the walk proofs; the corpus is a sample |
| The relation's witness pins and the gap/literal tables | `nix develop -c lake env lean tests/json-noevent.lean` | sha256 `eb82cbf5…`; exit 0, 41 lines in 3 s | null/true witnesses at the empty arena; six gap rows plus a guarded mutant; eleven literal rows plus two mutation controls | The number path, the arm and the new modules: no declaration from them is named |
| The rows tier's interface and the F1 refusal | `nix develop -c lake env lean tests/stage2-noevent-rows.lean` | sha256 `88c0aae3…`; exit 0, 211 lines in 1 s | 9 `#check`s and 9 axiom pins over `RowsAssemble`/`ContainerB`/`Brace` | `JsonStage2NoEventWalkRowsAssembly`'s start-state theorem and its depth-zero lemmas are not named |
| The reference runner's renderings agree with the manifest | `nix develop -c bash tests/json/check.sh` | sha256 `9eef09f8…`; exit 0 in 1 s; 1 `ok` line | 130 corpus files and manifest rows; tampered arm | The stage-2 relation and the walk |
| The classifier fixture, the Lean body and the object agree | `nix develop -c bash tests/json-classify/check.sh` | sha256 `34c69ff0…`; object sha256 `95a38141fe3e9558d744c5762f6f81a6b79437424302dd121fc3662361d94a7f`; exit 0 in 5 s; 6 `ok` lines | 9 manifest rows; 70 corpus windows over 130 files; 71 windows compared with the object; the mixed block | The relation; the object on an unaligned pointer |
| The mask unit's object and the Lean body agree | `nix develop -c bash tests/json-s1-masks/check.sh` | sha256 `563103ba…`; runner sha256 `7b3d24f42597495882298d6b9aba2cfc97c0f7bd345f58dd9f5fda4aa73b4af4`; exit 3 in 240 s; no `ok` line | the row comparison runs; the check then stops in its defect-mutation step with `SETUP: s1f_lo_tab not found in the kernel source` and `SETUP: the table mutation did not apply` | the rows' correctness: the negative control is unexercised, so a row agreement is unchecked and the run is not evidence for the mask table |
| The entry unit's three kernels agree row for row | `nix develop -c bash tests/json-entry/check.sh` | sha256 `0b7835ff…`; object sha256 `f712e98adb996c4501560cdb90dd811376994b880144daedde1b56dbf4da4e91`; exit 0 in 1,414 s; 8 `ok` lines | 197,595 rows from 6 corpus streams and 65,859 arm streams; 2,091/65,544/65,545 rows moved by the three detectors | The stage-2 walk; the relation |
| The UTF-8 stage's object, body and behaviour matrix agree | `nix develop -c bash tests/json-utf8/check.sh` | sha256 `99e6ed87…`; exit 0 in 29 s; 13 `ok` lines | 73,610 rows per gate value (27 corpus + 73,583 arm); 144 rows moved by the defect object | The stage-2 walk; the relation; the timing arm |
| The relation's and the new modules' footprints are the pinned ones | the 81 new `#guard_msgs` blocks in `LeanLLVMTest/Refinement.lean`, checked by the build | 1,876 blocks, 81 new; exit 0 at the build above | 70 declarations in three modules plus the earlier 11; `JsonStage2Spec`'s nine relation pins unchanged | A footprint pin is not a statement about the rows' content |


### Commands, exits and output tails

All commands ran from the tree root; the last line of each output is quoted, with
`…` for elision.

```
nix develop -c bash probes/install/lake-locked.sh build            exit 0  Build completed successfully (2524 jobs).
nix develop -c bash probes/install/lake-locked.sh build leanllvm-json …  exit 0  Build completed successfully (2528 jobs).
nix develop -c bash probes/json/route/build.sh                     exit 0  ok: …/probes/json/route/build/leanllvm-json-route
nix develop -c bash tests/json-noevent/check.sh                    exit 0  ok: the no-event entries agree with the certified routes; the sentinel separates refusals; the census and the byte identity are pinned
nix develop -c lake env lean tests/json-noevent.lean               exit 0  runFuel calls k JsonStage2NoEventIR.stage2NoEventBody e
nix develop -c lake env lean tests/stage2-noevent-rows.lean       exit 0  'LeanLLVM.Refinement.stage2NoEventWalkF1_notRows' depends on axioms: [propext, Quot.sound]
nix develop -c bash tests/json/check.sh                            exit 0  ok: the corpus agrees with the manifest; a tampered expectation is a mismatch
nix develop -c bash tests/json-classify/check.sh                   exit 0  ok: a tampered expectation is a mismatch
nix develop -c bash tests/json-s1-masks/check.sh                   exit 3  SETUP: the table mutation did not apply
nix develop -c bash tests/json-entry/check.sh                      exit 0  ok: a tampered expectation is a mismatch naming its row
nix develop -c bash tests/json-utf8/check.sh                       exit 0  ok: a tampered expectation is a mismatch naming its row
```

`probes/install/lake-locked.sh build` without arguments is the default target
(`leanllvm`, `ITree`, `LeanLLVMTest`); the second line's five names are the
executables the stage-1 checks drive and are listed in full in the paragraph
above the table.  Wall times were 1,246 s and 14 s for the two builds, 101 s for the
route build and 261 s for the no-event check; the Lean files took 3 s and 1 s; the stage-1
checks took 1 s, 5 s, 240 s, 1,414 s and 29 s in the table's order.

### Which checks' claims rest on the new theorems

Measured by importing them, the answer is less than the change's title suggests,
and it is worth recording that precisely:

- **The executable routes rest on none of them.**  `tests/json-noevent/check.sh`
  observes the two C entries and the binary built from them; no C reads a Lean
  theorem.  Its `--value` arm reaches `StrtodReader.reader` through
  `canonValue`, and the reader is unchanged by this freeze.
- **`tests/json-noevent.lean` does not name any new declaration.**  Its subjects
  are the relation obstruction at `null`/`true`, the gap-recovery rule's six
  rows and the literal chain's eleven rows; all predate the freeze.  It is re-run
  here because the umbrella `LeanLLVM` it imports moved underneath it — a
  regression check, not a dependency.
- **`tests/stage2-noevent-rows.lean` checks the older interface.**  It imports
  `JsonStage2NoEventWalkRowsAssemble`, `…RowsContainerB` and `…RowsBrace`, and
  pins `stage2NoEventWalkRows_of_ready`, `…_of_classes` and the F1 refusal.  It
  does **not** import `JsonStage2NoEventWalkRowsAssembly`, so
  `stage2NoEventWalkRows_of_start` and the six depth-zero lemmas are covered only
  by that module's own `#print axioms` (which the build elaborates) and by the
  new `#guard_msgs` pins, not by this test file.
- **None of `json-classify/check.sh`, `json-s1-masks/check.sh`,
  `json-entry/check.sh` or `json-utf8/check.sh` touches the number path or the
  arm.**  Grepping each for `noevent`, `stage2`, `num_fast`, `numLex` and
  `json/route` returns nothing: they are stage-1 routes over the classifier, the
  mask unit, the entry unit and the UTF-8 gate, and they read none of the
  restated relation.  They were re-run anyway, because the same `lake build`
  produces the oleans their Lean bodies are compared against, so a green run is a
  statement about the touched library as well as about the C.
- **What does carry the new theorems is the build's pins.**  `LeanLLVMTest/
  Refinement.lean` gained 81 `#guard_msgs` blocks in the freeze (11 in
  `168df2e`, 70 in `34dcec1`), pinning 70 declarations across the three new
  modules and the restatements.  They are the instrument that fails when a
  footprint widens.  The measurement corrected three docstrings: the
  accepted-answer lemma carries `Classical.choice`, six declarations carry
  nothing, and `JsonStage2Body`'s comment claiming `numFastEmitted_refines`
  inherits `Classical.choice` is wrong — its footprint is `[propext,
  Quot.sound]`.  The comment is not corrected in the freeze.

### The restatement's executable footprint

The question is whether any executable check now depends on
`numLexScan_accepts_iff_numLexB`, and whether the `1E5`/`eDoc` witnesses have an
executable counterpart.  Measured on these bytes:

- **No executable check depends on the theorem.**  `numLexScan` is a plain
  definition in `JsonStage2Body` with no `@[implemented_by]`; the C function it
  models is not built from it.  The `#guard`s beside it — the three malformed
  tokens, the accepted controls, the empty lexeme — evaluate the *model*, and
  they are the same guards that existed before the theorem; what changed is that
  the guards' subject now has a proof tying it to `numLexB`.  The theorem's
  consumers are the six Lean declarations that dropped `hscan`, not a route.
- **`1E5` has no corpus document.**  `eDoc = [0x31,0x45,0x35]`, and
  `eDoc_numberArm_witness` inhabits the arm's premises with it at the model.
  The nearest executable spellings are `tests/json/corpus/num-exp-plus.json`
  (`1E+3`, accepted by the reference runner) and `tests/json/corpus/
  num-negexp.json` (`-1.5E-7`), plus `2.5E-3` inside the value arm's
  `numbers-noncanonical`; none is `1E5`, and none reads the Lean model.  The
  no-event corpus's exponent document is the refusing `1e`.
- **The proof that the C scan is the model scan is not in this freeze.**  What is
  proved is that two Lean definitions agree.  That the emitted `num_fast_el1`
  loop computes `numLexScan` is the C-to-model step, and it remains assumed the
  same way the other installed units' refinements are assumed.

### What the green no-event run supports, and what it does not

`tests/json-noevent/check.sh` exits 0 with all 23 `ok` lines.  Its support is
unchanged from the earlier section and is not restated as new evidence: the two
no-event actors agree on 68 admitted documents, those readings equal the
certified event arm's, the manifest's pins hold per document and arm, the
refusals carry the declared zeros and offsets, the in-run defect objects fire,
the event arm reproduces all 183 base rows, and the value arm carries the
reference's values on its 13 documents.  What this freeze adds is that the same
script, run over the restated library, still does so; what it does not add is a
row about the relation, the walk, or any document outside the corpus.

The earlier section's owed C-observable run is discharged.  `xxd` is absent from
the instance's dev shell (`command -v xxd` prints nothing), and the check passes
because `hex_to_bin` reads the event payloads with `sed`/`printf` instead
(`3cef886`, "take the event digests without xxd").  The run above therefore does
not depend on a tool the Lean evidence lane lacked.

### What remains unproved

The north star's equality — the compiled stage-2 call's run equals the reference
decoder's on the admitted domain — is still not a theorem at any document.  After
this freeze the gap is these five things:

1. **The compiled entry's words are not connected to the start state.**  The
   rows, the head and the trace are now produced from `Γ_stage2_noevent.pre` and
   the four staged objects, but nothing connects the compiled entry's argument
   registers and memory to that precondition.  The theorem's conclusion is about
   a `Mem` and an argument list, not about the binary the route runs.
2. **The container classes have no producer at depth zero.**  The seed head has
   `sp = fr = 0`; the pair and descend rows need positive depth, and the six
   lemmas above refute every one of them there.  A document whose first entry
   opens `[` or `{` and whose next entry is not the closer is therefore outside
   the tree's row coverage at the start state.  This is a proved *limit*, not a
   missing case that could be supplied by a stronger premise: no producer of this
   tree covers it.
3. **The accept terminal's facts are still carried.**  `Stage2NoEventWalk
   ReferenceFacts` carries the parse equality, the record trace, the read-back
   identity and the value equation, and the four class producers' terminal rows
   supply them.  The length equation is now derived
   (`consumeRecords_length_eq_nonSeparators`), but the term-sum identity is not,
   and its non-derivability is proved
   (`stage2NoEventReadback_terms_not_functionable`), not assumed.
4. **The number arm's reading stops at the reader's model.**  The conversion is
   `strtodSpec`'s and the acceptance is `numLexB`'s at the model, but that the C
   accumulators hold the fields `StrtodReader` returns is still the reader
   module's stated assumption, and the C scan's equality to `numLexScan` is
   unproved.
5. **The scanner's token extent is stated, not proved.**  `docs/contract.md` now
   says so: a token the stage-1 scanner classifies as a number is RFC 8259 §6's
   token only if the extent the scanner hands the number path is the grammar's
   extent; that obligation is not discharged here.

The two standing assumptions are unchanged: the C-to-IR and IR-to-object steps
for the installed units are compiler correctness, and the native admission's
agreement with `admission` is a check, not a theorem.

## The revision's instruments at `c8f1f94`

Everything below was observed from one tree, produced by `git archive c8f1f94`
and initialized there (`git init -q; git add -A`); the repository's object
database was attached so the one check that reads a pinned revision's blob
(`tests/json-noevent/check.sh`, NE4) could do so, and `git status` reported no
tracked change against `c8f1f94`.  The machine was the worker
`nx-ag-01a21253` (`europe-west1-b`, `n4-highmem-8`: 8 vCPU, Intel Xeon Platinum
8581C, 62 GiB, hostname `nixos`), Lean 4.35.0 and clang/LLVM 21.1.8 from the
flake.  Nothing was built or run on the development machine.

### The freeze digest

The digest covers every path these instruments read from:

```bash
git diff f39a621 c8f1f94 --binary -- LeanLLVM LeanLLVMTest LeanLLVM.lean probes tests docs | sha256sum
da245ce760b3887be2ab536c5c8b398e08182695102ea0bb9f5e07ee5aac903c  -
```

It is a digest of the twelve-commit interval's diff, so it moves if any tracked
byte under those paths moves, and it says nothing about files outside them —
`flake.nix`, `flake.lock`, `lakefile.toml` and the CI configuration are not
covered.  In the table below each instrument is additionally pinned by the git blob it
was at `c8f1f94` — a SHA-1 object id, where the freeze digest above is SHA-256 —
which is the check that the script that ran is the script this page describes.

### What was run, and what each instrument can claim

| Instrument | Digest (`git rev-parse c8f1f94:<path>`) | Corpus / arms | Non-coverage |
|---|---|---|---|
| `probes/install/lake-locked.sh build` | `a5afc527925ccee2b6a3e973201fd5f430eb0f1a` | the default targets `leanllvm`, `ITree`, `LeanLLVMTest`: 2548 jobs, exit 0, no `error:` line | compilation only; it does not run whatever proof a module carries |
| `probes/json/route/build.sh` (`OPT=-O2`, `TIMING=0`) | `ce01e5e6c0040cbfec46c08254894364ff502111` | six kernel TUs, the two no-event units, the depth counter, `policy.c`, `shim.c`, `RouteMain`, the driver and `guard_check`; symbol assertions on the adapter and the executable | the link's symbol list is asserted, not the object's behaviour; the Lean cone must have been built first |
| `tests/json-indexed-reader.sh` | `b68691c8cc043786b37f7b45d281a86d07eee5ee` | 29 hand-built streams: empty, truncated record, spans past either source, unknown tags, undecodable bodies, a 2,000-event array | buffers a route never returns; it is not a proof of the two readers' equality |
| `probes/json/route/indexed-check.sh` | `eea29fa8331430b8ff2ad9f51cba6d2cb1b21efd` | 147 documents (130 `tests/json/corpus` + 14 `tests/json-value/corpus` + three 64 KiB synthetic shapes): 76 fast-path streams compared, 71 outside the fast path | only documents the route admits; agreement of two readers, not either against the model |
| `tests/json-event-slice/check.sh` | `b9465a2e740841f882b0782aed6febcd383abbcd` | two fixtures, `[1]` (native success) and the zero-byte document (reference fallback) | two documents; `EvbEmission` remains the declared assumption |
| `tests/json-value/check.sh` | `91124cfbdaada6b90bc2855bde54576c28418cd7` | 14 documents, digests pinned, one tampered expectation rejected | finite corpus; the value is the reference path's, not the object's |
| `tests/json-noevent/check.sh` | `74e349156ca0cd8971498a5f8059ae82a7ea484d` | 69-document corpus, both arms of both routes, the in-script cuts, NE4 byte identity against `66159e24`, NE8's 183 base rows | the corpus is finite; the model relation stays in Lean |
| `tests/json-s1-masks/check.sh` | `cecd3b04aad6625de3fdf6d31c9ba0cfdcb9c28a` | 688,824 rows (8 mixed + 8 × 86 corpus windows + 131,072 byte + 524,288 alphabet + 32,768 random), both arms | aligned staging only; the fixture's alignment gap is stated in the script |
| `tests/m4-loop-emission.sh` | `8381903d6fb7fac374e85cbcdbf2f5827ad8cd04` | `--capture` under `lake`/`clang`/`opt` shims and the four header-refusal modes over the copied driver | the shims are not the real compiler pipeline; five fixtures, not a grammar |
| `tests/json/check.sh` | `167312a14216411795b07acecb13b781fbf5d7da` | 130-document corpus plus the tampered manifest | the runner against a hand-written manifest |
| `tests/json-classify/check.sh` | `00c1953bd31a8eb206ad8c9f3c3e70919979ca32` | the block classifier's two actors over corpus windows and the generated arms | aligned 32-byte windows only |
| `tests/json-entry/check.sh` | `01f772b592eb696f1abeb7afce655773faa67958` | the entry streams' two actors over the mask corpus and arms | the emitted literal chain stays in Lean |
| `tests/json-utf8/check.sh` | `295e38072e1775371ab3d440b97e955b29cb02b2` | 73,610 rows per gate value, three actors and a scalar reference | gate soundness is stated over the published staging obligation |

`probes/json/route/build.sh`'s binary was
`7b2ad9106cf525492efd9917d4d43d07bca624850370d72a293a9841f1bf8b10`
(SHA-256, uninstrumented build).  The stage columns in the sweep section come
from the same script rebuilt with `TIMING=1`; that build's binary is a different
artefact and is not the one the route checks ran.

### The routes that changed, and the controls

Uncut, every command below exited 0.  The default build is
`nix develop -c bash probes/install/lake-locked.sh build`: it printed
`Build completed successfully (2548 jobs).` and no `error:` line.  The route's
link step needed one cone build first — `tests/json-indexed-reader.sh`'s own
target `LeanLLVM.Refinement.JsonEventCursorInterface` is not imported by the
default targets, so the first `probes/json/route/build.sh` exited 1 with
`build: absent: .lake/build/ir/LeanLLVM/Refinement/JsonEventCursor.c`; the
hinted cone build (73 jobs) then the same link step exited 0.  The extra
executables the stage-1 routes drive were built by the same lock:
`lake-locked.sh build leanllvm-json leanllvm-json-classify leanllvm-json-entry
leanllvm-json-utf8 leanllvm-json-s1-masks` (2552 jobs, exit 0).

| Command | Exit | Tail |
|---|---|---|
| `tests/json-indexed-reader.sh` | 0 | `indexed-reader: ok — 29 cases, both readers agree` |
| `probes/json/route/indexed-check.sh` | 0 | `indexed-check: ok — 147 documents, 76 fast-path streams compared, 71 outside the fast path` |
| `tests/json-event-slice/check.sh` | 0 | `ok: [1] is a native success: verdict=1 nk=3 nxp=0 ndst=0 nev=11 err=0` and `ok: the [1] event slice's two caller fixtures` |
| `tests/json-value/check.sh` | 0 | `json-value: ok — 14 documents, digests match, tampered expectation rejected` |
| `tests/json-noevent/check.sh` | 0 | `ok: the event arm reproduces all 183 base rows (exit, six words, both payloads, document and stdout)` and `ok: the no-event entries agree with the certified routes; the sentinel separates refusals; the census and the byte identity are pinned` |
| `tests/json-s1-masks/check.sh` | 0 | `ok: the detector bites: 128248 of 688824 row(s) moved, all comma-carrying; first is mixed…` |
| `tests/m4-loop-emission.sh --capture` | 0 | `ok: E1: the body shifts the xor result by the lane offset that is the SSA result of 'mul i64 <counter-load>, 8' …` then `all assertions held` |
| `tests/m4-loop-emission.sh --declare-attr` | 0 | `E4: … unsupported attribute group '#0' after the parameter list of @f` |
| `tests/m4-loop-emission.sh --declare-param-attr` | 0 | `E5: … parameter 1 of @f carries the attribute 'range', which is not modelled` |
| `tests/m4-loop-emission.sh --return-attr` | 0 | `E2: … unsupported return attribute 'range ( i64 0 , 1 )' before the return type of @f` |
| `tests/m4-loop-emission.sh --function-attr` | 0 | `E3: … unsupported token(s) 'noreturn' after the parameter list of @f` |

The mask control's clean arm is the row equality: 688,824 rows classified by the
Lean body and the object, with the object built from `kernel/json/s1_block.c`
(digest `288fb42237c9d5e42940155037ddc1026302e50888e60154b12c006bc7f82991`)
rather than from the fixture.  Its mutated arm is the same run's detector: the
flipped table entry moves 128,248 rows, every one comma-carrying, and the first
moved row is the `mixed` row printed above.  So the control fails where the
classification says it should and nowhere else.

The event slice's two fixtures are the whole of that scenario:

- **`corpus/one` is `[1]`.**  `--doc` exits 0 with
  `verdict=1 nk=3 nxp=0 ndst=0 nev=11 err=0` — an empty arena and a real verdict,
  so the native call ran and did not fall back — and `--value` prints
  `value: verdict=1 value=5b23303030303030303030303030663033665d`, the UTF-8 hex
  of `[#000000000000f03f]`, the same canonical value `[1.0]` has.
- **`corpus/empty` is the zero-byte document.**  Admission declines it, no native
  call is made, and both arms report the reference parser's own refusal:
  `refused: invalid: unexpected end at 0` on stderr at exit 2, and
  `value: refused class=invalid:unexpectedEnd offset=0` on stdout at exit 2.
- The scenario's control reads the value line's form from `tests/json-value`'s
  `refused-empty` first, so a detector that reads nothing fails as an absence.

### The unaffected stage-1 routes

All four still pass, and none stopped at setup in this run:

| Route | Exit | Tail |
|---|---|---|
| `tests/json/check.sh` | 0 | `ok: the corpus agrees with the manifest; a tampered expectation is a mismatch` |
| `tests/json-classify/check.sh` | 0 | `ok: the installed object (sha256 95a38141…) agrees with the Lean body on 71 window(s)`; the detector moves `0x7bd6f7b7` to `0x7bd4f7a7` at offset 0 of `mixed.block` |
| `tests/json-entry/check.sh` | 0 | `ok: the object (kernel sha256 f712e98a…) agrees with the Lean body on 197595 row(s)`; the POS8, B8 and B3 detectors move 2,091, 65,544 and 65,545 rows |
| `tests/json-utf8/check.sh` | 0 | `ok: both gate values return the same word on 73053 documents`; the defect object moves exactly the 144 rows whose last byte is `C0`, `C1` or at least `F5` at both gates |

One setup fact is worth recording because it is easy to read as a route failure:
none of these four executables is a default target (`lakefile.toml`'s
`defaultTargets` are `leanllvm`, `ITree` and `LeanLLVMTest`), so on a tree built
by the default command alone `leanllvm-json`, `leanllvm-json-classify`,
`leanllvm-json-entry` and `leanllvm-json-utf8` are absent and each script exits
3 at its own absent-binary line.  The pass above is after building those five
targets by name (`leanllvm-json-s1-masks` included, for the mask route).  That
is a build prerequisite, not a regression: nothing in this revision changed
those scripts' fixtures or their setup checks.

### The reader's before-and-after sweep

Both trees were built on this host and swept back to back in one session, on
the generator's dense shape at its fixed size sweep: `f39a621` (the last
evidence freeze, whose `--value` consumes the returned buffers with the list
reader `eventsOfBytes`) and `c8f1f94` (this revision, `eventsOfBytesIndexed`),
each `OPT=-O2`, kernel `-O2`, `TIMING=1`.  Each cell is the median of three
whole `--value` calls for 64 KiB to 512 KiB and one call at 1 MiB under a 600 s
bound, timed from before the spawn to after the exit with the value line
discarded; both binaries were run through the identical loop.

| Size (bytes) | `f39a621`, list reader (s) | `c8f1f94`, indexed reader (s) | Ratio |
|---|---|---|---|
| 65,536 | 5.327 | 0.449 | 11.9 |
| 131,072 | 20.995 | 0.541 | 38.8 |
| 262,144 | 82.052 | 0.751 | 109.3 |
| 524,288 | 336.125 | 1.200 | 280.1 |
| 1,048,576 | did not finish inside 600 s (`exit 124`) | 2.584 | — |

The pre-change binary's growth is superlinear in the size; the indexed reader's
is not.  The instrumented revision also prices the two calls it makes after the
native call, on the same five documents (`TIMING=1` build, medians of three
21-repeat stage probes, zero fallbacks):

| Size (bytes) | Wall (ms) | `value_bytes_ns` (ms) | `value_decode_ns` (ms) | path |
|---|---|---|---|---|
| 65,536 | 450.3 | 4.71 | 0.97 | fast |
| 131,072 | 549.7 | 9.38 | 1.97 | fast |
| 262,144 | 757.0 | 18.71 | 3.92 | fast |
| 524,288 | 1,254.9 | 37.95 | 8.62 | fast |
| 1,048,576 | 2,943.6 | 77.91 | 18.36 | fast |

**Caveats that belong to these numbers.**  One session on one spot worker
(`nx-ag-01a21253`), not a quiet host: no PMU, `CLOCK_MONOTONIC` reads only, and
the machine is shared.  The wall and the component intervals do not compose by
subtraction — the wall is a single spawn-and-exit call while the components come
from a 21-repeat probe inside one process — and the two instruments disagree on
the same builds by up to 14 % at 1 MiB (`value-sweep.sh`'s own wall was 2,944 ms
against the loop's 2,584 ms; at 128 KiB, 550 against 541 ms).  The comparison is
same-host, same-session and same shape, which is what makes the ratio
meaningful, but it is not a quiet-host measurement, and the 1 MiB point on the
pre-change side is an absence (a timed-out call), not a measured wall.

### What remains unproved at this revision

- **The two readers are equal only where they were compared.**  `indexed-check`
  compared them on 76 admitted streams and `tests/json-indexed-reader.lean` on
  29 hand-built buffers.  No theorem states
  `eventsOfBytesIndexed = eventsOfBytes` for arbitrary buffers, and a buffer the
  routed object never returns is outside both instruments.
- **The emitted-stream step is an assumption, not a proof.**  `EvbEmission`
  (`LeanLLVM/Refinement/JsonEventEmission.lean`) is the declared premise that the
  selected object leaves the arena and the trace's event bytes at their
  destinations.  The event slice is that premise's caller side on two documents;
  nothing in this revision eliminates the premise.
- **The objects are compared with the bodies, not proved equal to them.**
  `tests/json-classify`, `tests/json-entry`, `tests/json-s1-masks` and
  `tests/json-noevent` compare a compiled object with a Lean body over generated
  arms.  The arms are bounded (688,824 mask rows, 73,610 UTF-8 rows per gate,
  183 base rows), and the refinement statements that would quantify over all
  inputs are the Lean development's, not these routes'.
- **Admission's depth and policy are finite.**  `tests/json/check.sh` and the
  route's depth and policy rows sample the corpus; the 520-frame stack bound and
  the character-policy scan are not exhaustively enumerated here.
- **One session, one spot machine, no PMU.**  The sweep's walls are
  `CLOCK_MONOTONIC` around a process spawn, on a shared machine that is not
  quiet, and the reader and decode columns come from a 21-repeat probe while the
  wall is a single call.  The two do not compose by subtraction, and the numbers
  are not a quiet-host measurement.
- **The pre-change sweep stops at 512 KiB.**  The 1 MiB document did not finish
  inside the 600 s call bound on the pre-change binary, so the before/after
  ratio is measured on four sizes and the fifth is an absence, not a number.
- **The identity row needs history the archive does not carry.**
  `tests/json-noevent/check.sh`'s NE4 compares six paths with
  `66159e24`'s blobs through `git show`.  A bare `git archive c8f1f94` tree
  without the object database stops that check at setup, so the byte-identity
  claim is conditional on attaching the history.
- **The capture mode is shimmed.**  `tests/m4-loop-emission.sh --capture` runs
  the capture script against local shims for `lake`, `clang` and `opt`, so it
  checks the relations the script asserts over an emission, not a real compiler
  pipeline.  The four header-refusal modes are five fixed fixtures; they show the
  refusal fires, not that the header grammar is complete.
- **The mask detector's moved-row count is a property of its own cut.**  The
  script builds the defect object and counts the rows the flipped table entry
  moves; that shows the detector bites, and the row equality against the body is
  the separate claim.
- **No axiom audit is part of any route.**  `lake build` elaborates every proof
  in the default targets, but no instrument on this page prints the axioms a
  theorem rests on, and `sorry`-freedom is not asserted here.
- **The digest is scoped.**  It covers `LeanLLVM`, `LeanLLVMTest`, `LeanLLVM.lean`,
  `probes`, `tests` and `docs` between `f39a621` and `c8f1f94`.  The flake, its
  lock and `lakefile.toml` are outside it, so the toolchain that built these
  artefacts is named by version, not pinned by the digest.
