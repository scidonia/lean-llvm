# Evidence for the JSON route scenarios

The three JSON routes exist to make externally visible behaviour observable:
the API's accept/refuse outcomes, the tape's meaning, and the corpus runner's
agreement with its oracle. A green run alone does not show that a route would
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
| `X1` fixture pin | `probes/install/ir/json-classify.candidate.ll`: `splat (i8 44)` → `splat (i8 45)` | exit 0 (the fixture is not a `lake build` input, `AGENTS.md`) | `nix develop -c lake env lean LeanLLVM/Vellum/JsonClassifyIR.lean` | 1 | `JsonClassifyIR.lean:93:0`, did not evaluate to `true` |
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
  `scanCaller` (`LeanLLVM/Vellum/JsonSeam.lean`), which stages its own
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
