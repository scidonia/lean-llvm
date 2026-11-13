# The native parse core in the route's call shape

`kernel/json/bench/profile-pipeline.cc` prices the six stages with a
64-byte-aligned document window and buffers reused across rounds.  The route
does neither: it stages `[0,0,0] ++ doc ++ pad` and hands the object
`window + 3`, and every repetition's thirteen buffers are fresh allocations.
This directory measures whether that difference is the gap between the route's
`native_ns` row and the profile's `pipeline` row, and splits the core's cost in
the shape the route actually calls it.

| File | What it is |
|---|---|
| `shape.cc` | one binary holding the six staged kernel objects and simdjson 4.6.11: the whole pipeline with a 64-byte window and reused buffers (`site`), the same with arm 0 (`arm0`, checked only where the escape list is empty), the route's three-byte offset (`off3`), an aligned offset (`off0`), fresh per-call buffers in the route's staging capacities (`fresh3`), the same with 64-byte-aligned buffers (`fresh+64`) and with an aligned window (`fresh0`), the reference's `iterate` plus full traversal (`reference`), that traversal with the number conversion removed (the pair is the reference's own conversion cost, `ref-num`), and its padded-copy staging (`pad`); then the six stages separately in the `site` shape |
| `shape.sh` | builds the six units at the measured clang line, links the harness against the pinned simdjson, and runs it under a CPU pin; with no `--corpus` it generates the nine documents `probes/json/route/bench.sh` times, from the same commands, and writes the manifest `kernel/json/bench/profile-pipeline.sh --corpus` reads |

## What it checks before the clock

Every variant must return the same verdict, `nk`, `nxp`, `ndst`, `nev`, `err`,
and the same event and arena bytes as `site`; a variant that parses differently
is a setup fault (exit 3), not a timing row.  `arm0` is checked only where the
route's own call produced `nxp = 0`: an empty escape list is the same input to
stage 2 under either arm, so the two calls must agree, and on a document with a
backslash they legitimately do not.  The manifest digests are checked first, so
a row names the bytes the record names.

## Commands

```bash
nix develop -c bash probes/json/core-shape/shape.sh --corpus-out .lake/core-profile --rounds 31 --core 3
nix develop -c bash kernel/json/bench/profile-pipeline.sh --corpus .lake/core-profile/corpus.tsv --rounds 31 --core 3
```

The first command writes the nine documents and their manifest under
`.lake/core-profile/` and runs the shape probe; the second times the same bytes
with the stage instrument.  `BENCH`-style knobs are `--corpus`, `--rounds` and
`--core`; `SIMDJSON_LIB`/`SIMDJSON_DEV` name a locally built simdjson 4.6.11.

## What it measured

Recorded in [the stage timings page](../../../docs/json-route-stage-timings.md),
"The native parse core's stages".  The short form: the route's window offset,
its fresh buffers and their alignment are all inside this machine's noise —
every variant within 4.5 ns/block of the baseline, with the sign flipping
between documents, against a 3.0 ns/block move of the baseline itself between
two runs — so the route's `native_ns` figure is the core's own cost; the gap to simdjson is the stage-1 pass (masks plus entry emission,
13.3–15.4 ns/block net of the overlap the fused call recovers) and the number
conversion (10.8–13.4 ns/block, 1.27–1.31 times the reference's per number),
while the walk's per-entry dispatch is 6.1–9.0 ns/block **cheaper** than the
reference's non-number work.  The escape list is built on every document because
the route passes arm 2, and it costs 1.1–4.9 ns/block where it produces nothing;
`arm0` on a document from which the admission's candidate flag is clear is the
same call, and that is the one measured, not-landed improvement this probe
found.
