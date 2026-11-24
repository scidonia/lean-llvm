# The fair comparison's corpus, gates and report

`tests/json-fair` holds the equal-output harness and the pinned corpus the
shipped route's no-event arm is measured against.  `README.md` states the
terms, the event encoding and the measurement discipline; this file pins the
three properties every row depends on and records the attribution the
body-bound tail work still owes:

- **NF1** the corpus regenerates from committed sources and every document is
  pinned by size and sha256, with the detector's own affirmative control.
- **NF2** the harness times no document whose writer bytes or consumer reading
  differ from the pipeline's.
- **NF3** the report's summary recounts from its per-document rows.
- **NF4** the body-bound attribution (stub; the instrument does not exist at
  this revision).

    nix develop -c bash tests/json-fair/check.sh

The check writes nothing to the repository: the corpus is regenerated into a
private directory, the harness's build and per-document table live there, and
the staged cuts are compiled in throwaway copies.  Exit status is 0 when every
assertion holds, 1 when one fails, and 3 when the route is not usable (an
absent source, compiler, corpus generator input or simdjson store, so a setup
fault is never read as an assertion result).

## The corpus

151 documents in two groups: the 148 heterogeneous documents of `gen.py` (four
styles at 512 B, 2 KiB, 8 KiB, 32 KiB, 128 KiB, 512 KiB and 1 MiB with five
seeds each, plus `deep` and `escapes` at 64 KiB and 256 KiB with two seeds
each) and the three canonical 64 KiB documents of `tests/json-units-bench/gen.c`
(`syn-dense-64k`, `syn-strings-64k`, `syn-utf8-64k`).  Every document is at most
1 MiB, the route's input bound; `gen.py`'s base seed is fixed and its first line
records the absolute source path and sha256 of the generator text it was copied
from.

`manifest.tsv` has one row per document: `file`, `style`, `target_bytes`,
`records`, `bytes`, `sha256`, `root`, `seed`, `max_depth`, `seed_index`.  The
three canonical rows leave `records`, `max_depth` and `seed_index` as `-`,
because those columns describe `gen.py`'s record structure.

The documents are generated at run time and are not committed.  The one-time
`--exit-tmp` comparison against the corpus's measured copies is not part of
this check: its input lies outside the repository and may be absent, and after
it has run the generator and the manifest are the source of truth.

## NF1 — the corpus regenerates and the manifest is its pin

- **Actor:** `tests/json-fair/generate.sh`, run as an external process.
- **Given:** `gen.py`, `manifest.tsv` with its 151 rows, the canonical
  generator `tests/json-units-bench/gen.c`, `python3`, `clang`, and a private
  output directory.
- **When:** the check runs
  `generate.sh --out=<private directory>` and then, for the control, runs
  `generate.sh --verify --out=<a copy with one document byte changed>`.
- **Then:** the generator exits 0 and materialises exactly 151 documents; every
  manifest row's `bytes` and `sha256` equal the generated file's; the document
  set equals the manifest's, with exactly 148 `hetero-*` and 3 `syn-*` rows and
  no row named twice; the unchanged directory passes `--verify`; and the copy
  with one byte changed fails the same `--verify` detector, naming the document
  and reporting the digest it computed beside the manifest's.  The mutation
  changes the digest and not the size, so the size check alone cannot be what
  rejects it.
- **Why:** the corpus left the temporary directory it was measured in, so "the
  corpus is reproducible" is a check and not a sentence.  A detector that
  matches nothing cannot pass as green: the unmutated corpus and the mutated
  copy go through the same per-row function in the same run.

## NF2 — the harness gates every document before it times it

- **Actor:** `tests/json-fair/run.sh`, run as an external process over the
  pinned corpus.
- **Given:** the six certified kernel objects compiled from `kernel/json/
  {pipeline,s1_block,entry,escape,utf8,stage2}.c`, the additive no-event
  objects, simdjson 5.0.5 at the pinned store paths, the corpus materialised
  from NF1, and `fair.cc`'s writer.
- **When:** the check runs
  `FAIR_NOEVENT=1 BENCH_TRIALS=<t> BENCH_REPS=<r> run.sh --short`, and then the
  same command in a throwaway copy of the tree whose `fair.cc` declares one
  fewer payload byte in every key and string record.
- **Then:** the uncut run exits 0, reports zero gate failures over 151
  documents, and leaves one gate-pass line and one timed row for every manifest
  document; the cut tree compiles, its run exits 1, and its gate line names at
  least one document with `writer=1 ev=0 arena=1` — the writer produced a
  stream, the event bytes differ from `leanllvm_json_pipeline`'s, the arena
  bytes still agree, and the consumer reading differs as a consequence.  A
  document the cut fails is not timed.  The failing document passed in the
  uncut run, so the two runs differ only by the cut.
- **Why:** every timing the directory records is a time for *equal output*.
  The gate is what makes the word "equal" checkable per document, and the cut
  is what makes the gate's failure observable rather than assumed.  The cut is
  reachable from the boundary the harness drives — the writer's record emitter
  runs for every key and string body — and it changes no production byte and
  no other gate's outcome.

## NF3 — the report's summary recounts from its rows

- **Actor:** the report generator, `run.sh`'s aggregation over the harness's
  raw rows.
- **Given:** the uncut run's `rows.tsv` (one `ROW` line per document, arm and
  trial, each value a trial's median over `BENCH_REPS` repetitions) and its
  `per-document.tsv`.
- **When:** the check recomputes every derived number from the rows and
  compares it with the table and the printed summary.
- **Then:**
  - every per-document arm cell is the median of that arm's trial medians, and
    the `rpn/ps` cell is the median of the document's per-trial quotients
    `rpn[ t ] / ps[ t ]`;
  - the table has one row per manifest document, and its `bytes` column is the
    manifest's;
  - the summary's counts partition the corpus: `faster` (quotient below 1.0),
    `in band` (1.0 to 1.10 inclusive) and `over 10%` (above 1.10) sum to the
    corpus size, every stated denominator is that size, and the same holds for
    the 148 heterogeneous documents;
  - the summary's median quotient is the median of the per-document `rpn/ps`
    quotients, and the majority sentence's state agrees with the counts and
    carries the same denominator;
  - a copy of the summary with one count incremented fails the same recount,
    naming the count and what the rows give.
- **Why:** the row is the only form the performance claim may take.  A count
  that does not recount from the rows is a number lifted out of its table, and
  the affirmative control shows the recount is not a formatting check.

## NF4 — the body-bound attribution (M6 stub; no instrument at this revision)

- **Actor:** the ablation variant, a measurement-only build of
  `kernel/json/pipeline_noevent.c` that timestamps its stages, driven by
  `tests/json-fair/ablate.sh` over the variant sources in
  `tests/json-fair/ablate/`.  The instrument does not exist at this revision,
  and this check does not run it.
- **Boundary:** the instrument's per-stage timestamps around one pipeline call
  over the corpus, and the residual documents the NF3 report lists as over 10%.
- **Outcome when the instrument lands:** the stage shares sum to the call's
  time within the instrument's stated resolution, and each over-10% document's
  dominant term is named.  A control that adds a known sleep to one stage must
  move that stage's share by the sleep within the same resolution; the
  unmodified variant's shares sum to the call.  The instrument names escapes,
  the 8/32 KiB fixed costs and per-entry dispatch as the candidate terms, and
  the tail's stop condition is stated with that arithmetic.
- **Why it is a stub:** the attribution is a measurement of a body that has not
  been frozen or instrumented yet.  Writing the scenario now records what M6
  must establish; implementing the instrument here would measure a body that is
  about to change under the tail work and would answer a question the report
  has not yet posed.

## Coverage of the planned definitions

| site | the definition it pins | what it does not claim |
|---|---|---|
| NF1 | every row's size and sha256, the 148+3 count, and a one-byte mutation rejected by the same per-row detector | that the corpus samples any real workload, or that the generator is unchanged since the measurement (the one-time external comparison is separate) |
| NF2 | per document, the writer's event and arena bytes equal `leanllvm_json_pipeline`'s and the C consumer agrees on both streams; the no-event reading and stage-1 cursors equal the certified fold's | that the writer's decoder is independent of the pipeline's (it calls the same expand entry), or that a passing gate proves the body refines the model |
| NF3 | the counts partition the corpus with the denominator stated, the medians are of within-trial quotients, and a tampered summary fails the recount | a cross-machine or cross-governor claim, or that `parse` is the fair denominator |
| NF4 | the planned attribution: stage shares sum to the call within the instrument's resolution, the over-10% documents' dominant term is named, a known sleep moves a share | that the tail is reachable or unreachable; the stop condition is stated at NF4's own run, not here |

## What the directory does not claim

- **One host, one CPU.**  The wall times are the host and CPU the run records,
  pinned by `taskset`; they are not a cross-machine claim.
- **`ps` is not `parse`.**  `parse` validates and walks without producing the
  consumer's reading; `ps` produces it.  A `parse` quotient is not the fair
  comparison and is not reported as one.
- **The corpus is synthetic.**  It bounds every document at the route's input
  bound and mixes four styles, deep nesting and escapes; it is not a sample of
  any workload.
- **Equal output is not refinement.**  The gates compare two implementations'
  bytes and readings; the body-to-binary and body-to-model distances are
  separate artefacts.
- **The no-event arm's row is the measurement, not the route's default.**  The
  harness links the arm when asked; which arm the shipped route runs is a
  separate decision with its own contracts.
