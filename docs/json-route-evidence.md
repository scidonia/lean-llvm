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
the cut is therefore a runtime override — `@[implemented_by]` — in a copy. The
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
