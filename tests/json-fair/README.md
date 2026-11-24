# The fair comparison

This directory holds an equal-output harness for the JSON pipeline and a
reproducible corpus.  The comparison is with simdjson 5.0.5's full traversal,
and the row it produces is the one the no-event entry is measured against: the
consumer's reading on both sides, with no event buffer on either side.

```bash
nix develop -c bash tests/json-fair/generate.sh --check
nix develop -c bash tests/json-fair/generate.sh --check --exit-tmp   # one time only
nix develop -c bash tests/json-fair/run.sh
```

## The corpus

151 documents, generated from committed sources and pinned by size and sha256
in `manifest.tsv`:

- **148 heterogeneous documents** from `gen.py`: four styles (`pretty`, `tab`,
  `compact`, `spaced`) at 512 B, 2 KiB, 8 KiB, 32 KiB, 128 KiB, 512 KiB and
  1 MiB with five seeds each, plus `deep` (60 levels of nesting) and `escapes`
  (control bytes, `\"`, `\\`, `\n`, `\t`, `\u00e9`, a surrogate pair) at 64 KiB
  and 256 KiB with two seeds each.  The generator's base seed is
  `0x5EED2026F1ED`; every document is at most 1 MiB, the route's input bound.
  The generator text is the one the corpus was measured with: the first line of
  `gen.py` records the absolute source path and that file's sha256
  (`e0602885…`), and the text after that line is the source unchanged.
- **three canonical 64 KiB documents** from `tests/json-units-bench/gen.c` at
  its fixed splitmix64 seed: `syn-dense-64k`, `syn-strings-64k` and
  `syn-utf8-64k`, the same bytes the stage-1 unit measurement uses.  Their
  manifest rows leave `records`, `max_depth` and `seed_index` as `-`; those
  columns are properties of `gen.py`'s record structure and the units'
  transcript does not record them.

`generate.sh` regenerates all 151, asserts every row's size and sha256, and
compares `gen.py`'s own manifest with the committed 148 rows, so a generator or
toolchain that changes a byte fails rather than producing a new corpus.  It
also flips one byte in a copy and requires the same per-row check to reject it:
a detector that matches nothing cannot pass as green.

`--exit-tmp` compares the 148 heterogeneous documents byte-for-byte with the
copies the corpus was originally measured from in `/tmp`.  It is the one-time
check that the committed generator is a copy of the measured one; after it has
run, `gen.py` plus `manifest.tsv` are the source of truth.  An absent `/tmp`
directory is a setup failure, never a pass.

The documents themselves are not committed; `corpus/` is generated and
ignored.  `run.sh` generates the corpus when it is absent and otherwise
verifies it against the manifest before timing anything.

## The terms

`fair.cc` measures seven arms over the same document in the same process:

| arm | work |
|---|---|
| `parse` | simdjson's `iterate` plus the complete value traversal, no output |
| `pw` | the traversal plus this tree's event-stream writer |
| `pwc` | `pw` plus the C consumer's fold |
| `ps` | the traversal plus the consumer's sum computed directly, no event buffer |
| `rp` | `leanllvm_json_pipeline`, which materialises its event stream |
| `rpc` | `rp` plus the C consumer's fold |
| `rpn` | `leanllvm_json_pipeline_noevent`'s returned reading, no event buffer and no consumer walk |

`rpn` exists only when the no-event objects are linked (`FAIR_NOEVENT=1`);
without it the harness links the certified set alone.  `rp`/`rpc` are the
certified arm; a run without the no-event objects measures no consumer-boundary
row.

## Equal output

The writer (`pw`, and the sum behind `ps`) reproduces the event stream and arena
`kernel/json/stage2.c` emits:

- containers: one byte (`T_OBJ`=1, `T_OBJ_END`=2, `T_ARR`=3, `T_ARR_END`=4);
- key/string: 13 bytes — tag (`T_KEY`=5, `T_STR`=6), a 4-byte LE length, an
  8-byte LE payload.  A plain body's payload is its document offset with the top
  bit set (`(uint64_t)(p + 1) | 1 << 63`, `p` the opening quote); an escaped
  body's payload is its offset in the arena;
- number: 9 bytes — `T_NUM`=7 and the value's eight IEEE-754 bytes;
- literal: 1 byte — `T_TRUE`=8, `T_FALSE`=9, `T_NULL`=10.

Whether a body is plain or escaped is the pipeline's own stage-1 escape list: a
list position inside the body selects the decoded form, exactly as
`s2_string_body` decides it.  The arm word is the route admission's
(`leanllvm_route_escape_can_skip`: bit 1 is cleared when the document has
neither a backslash nor a control byte), evaluated once per document outside
every timed region.  The decoded bytes come from
`leanllvm_json_escape_expand`, the entry `stage2.c` itself calls, so the arena
is a reproduction of the reader's arithmetic rather than a second unescaper.

The same C consumer (`consume`) reads both streams.  Its fold is the pipeline's
reading, and the no-event entry's three returned words are compared with it:

- **equal output** means, per document, the writer's event bytes equal
  `leanllvm_json_pipeline`'s `nev` bytes, the writer's arena bytes equal the
  pipeline's `ndst` bytes, and the consumer's `tokens`, `values`, `walked` and
  `sum` agree on both streams.

## The gates

Before anything is timed, `fair.cc` requires, per document:

1. the writer's event and arena bytes equal the pipeline's;
2. the consumer agrees on both streams;
3. the direct sum (`ps`) equals that consumer's fold over the pipeline's
   stream;
4. when linked, the no-event arm's `tokens`, `values` and `sum` equal that fold
   and its stage-1 cursors equal the certified call's.

A failure prints the document, the failing gate, the stream lengths and the
first differing offset, and the process exits non-zero.  A failed gate means the
document is not timed and is not a measurement.

## The discipline

`run.sh` follows the stage-1 units' measurement discipline
(`tests/json-units-bench/bench-route-simdjson.sh`): `taskset` pins each process
to one CPU from `BENCH_CPUS`; each document gets one warm pass of every arm
outside the clock; each arm is `BENCH_REPS` repetitions and the trial's value is
their median; the whole set runs `BENCH_TRIALS` times with the arm order rotated
at every trial, so no arm always goes first.  Every quotient is taken inside one
trial on one CPU and reduced across trials, so a drift between trials does not
become a quotient.  The per-document table is `build/per-document.tsv`.

The counts over the `rpn/ps` quotient are a partition of the documents:

- **faster**: quotient below 1.0;
- **in band**: 1.0 to 1.10 inclusive (at parity or at most 10% over);
- **over 10%**: above 1.10.

The majority condition is "strictly faster on more than half of the corpus", and
the summary prints it with its denominator.  The report also states the same
counts over the 148 heterogeneous documents alone, because that is the group the
earlier note's rows used.

## The build

The six certified kernel translation units are compiled at the route's own
level (`-O2 -march=x86-64-v3 -mpclmul -std=gnu11`); the harness and the
simdjson traversal are compiled at `-O3` with the same architecture flags.  The
kernel objects are the shipped route's object set; the traversal is compiled
here because it is the `parse`/`pw`/`ps` side.  `run.sh` records the compiler
versions, both flag sets, the simdjson store paths and library digest, the host,
the CPU, the governor and the load average beside every measurement.

The simdjson dev output and library are the realised nix builds of nixpkgs'
5.0.5:

```bash
nix build --no-link --print-out-paths 'nixpkgs#simdjson.dev'
nix build --no-link --print-out-paths 'nixpkgs#simdjson'
```

## Limits

- **`ps` is not `parse`.**  `parse` validates and walks the document without
  producing the consumer's reading; `ps` produces that reading.  A quotient
  with `parse` in the denominator is not the fair comparison and is not
  reported as one.
- **`ps` is not `pw`.**  `ps` writes no event record, but it still decodes
  escaped bodies into a scratch arena so it can sum their bytes; that decode is
  part of the consumer's reading on both sides.
- **One machine, one CPU per row.**  The numbers are wall time on the host and
  CPU the run records, not a cross-machine or cross-governor claim.  The
  default `BENCH_CPUS` is one CPU; a list measures each and keeps the CPU in
  every row.
- **The corpus is synthetic.**  It bounds every document at the route's input
  bound and mixes four styles, deep nesting and escapes; it is not a sample of
  any workload.
- **The writer shares the decoder.**  Arena bytes are decoded through the same
  entry point the pipeline calls, so the arena gate checks the record layout,
  lengths and offsets, not the decoder's arithmetic independently.
