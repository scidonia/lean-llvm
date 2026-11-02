# JSON corpus check

`leanllvm-json` reads `tests/json/manifest.tsv` and prints one tab-separated
`<path>\t<verdict>\t<rendering>` line per row, comparing every line with the
manifest.  It exits 0 when all lines agree and 1 otherwise, with a
`mismatch: ...` line on stderr naming the disagreement.  The verdict column is
one of `accept`, `invalid`, `inputTooLong`, `depthExceeded` and `outOfCapacity`,
and the rendering column is `-` for every verdict other than `accept`, so the
corpus exercises both the semantic refusals and the three resource outcomes.

The manifest and the corpus are hand-written fixtures, not output of the thing
they judge.  No mode of `leanllvm-json` emits a manifest; each `accept` row's
rendering is written by hand against the decoded value the case means.  A
manifest produced by the runner would make the comparison vacuous, so the
scenario's oracle is independent of the executable it runs.

The corpus holds one file per case: the grammar and policy cases that are byte sequences independent of Lean syntax — the number grammar, the
standard escapes, the strict-UTF-8 boundary sequences, the `unescaped` ranges,
the surrogate and noncharacter cases, the parser literals, documents, trailing
data, byte-order mark, policy refusals and empty input — plus the padded family
`padN` = `[` + (`N`−2) spaces + `]` with expected value `[]`.  The scenario
runs the built binary as an external process over the corpus and the manifest,
and then over a copy of the manifest with one expectation changed.  The binary
is the artifact `probes/install/lake-locked.sh build leanllvm-json` builds; the
scenario does not invoke `lake`, so a corpus check does not build or contest the
certificate lock.  The copy is written in a private temporary directory; the
corpus and the repository manifest are only read.

    nix develop -c bash tests/json/check.sh

### JC2 — the runner agrees with the manifest and reports a changed expectation

- **Actor:** an operator running the corpus check.
- **Given:** `tests/json/corpus` with one hand-written file per manifest row —
  the grammar and policy cases plus the `padN` family described above;
  `tests/json/manifest.tsv` with the four columns and the statically held
  limits profiles, written by hand, including every `accept` row's rendering;
  and the `leanllvm-json` binary the locked executable route builds.  No mode
  of `leanllvm-json` emits a manifest, so the oracle is not the runner's own
  output.
- **When:** the operator runs the scenario with the command above.  The
  scenario first checks that the manifest names every verdict, runs the binary
  with the repository manifest, counts its printed lines, then changes the
  first accepted row's expected rendering by appending `0` to it, writes the
  changed bytes to a temporary manifest, and runs the binary again with that
  manifest.
- **Then:** the script exits 0, and every assertion holds:
  - each of `accept`, `invalid`, `inputTooLong`, `depthExceeded` and
    `outOfCapacity` has at least one row; a verdict with no row is a failure,
    because the corpus is what exercises the four outcomes and a missing
    verdict would otherwise pass silently;
  - the run over the unchanged manifest exits 0;
  - that run prints exactly one line per manifest row, the row count taken from
    the manifest and compared with the line count of the output; a runner that
    skips a row still exits 0, so the count is the observable that says every
    row was judged;
  - the run over the changed manifest exits nonzero, and its stderr carries a
    line beginning `mismatch:`, so the disagreement is reported as a mismatch
    of a row and not as a usage or fixture fault.
- **Why:** an executable that exits 0 whatever the fixture bytes say cannot
  report a decoded value, an accept or a rejection, and an executable that
  judges only the rows it prints cannot have judged the manifest.  The
  hand-written oracle is what makes agreement mean agreement: a manifest
  emitted by the runner would agree with itself.  The verdict check keeps the
  corpus from passing while it exercises only the accepted path or only
  `invalid`, which is what separates the three resource outcomes from a syntax
  refusal in the observable output.  The unchanged-manifest run is the control
  that the corpus and the manifest are usable before the changed-expectation
  run is read as a refusal, and changing one rendering leaves the manifest's
  shape and the corpus untouched, so the second run's status is attributable
  to the changed expectation.
