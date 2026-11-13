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
| `shape.cc` | one binary holding the six staged kernel objects and simdjson 4.6.11: the whole pipeline with a 64-byte window and reused buffers (`site`), the same with arm 0 (`arm0`), the escape-list guard's scan and the call it selects (`guard`, with `guardscan` for the scan alone and two `site` slots for the paired before and its drift control), the route's three-byte offset (`off3`), an aligned offset (`off0`), fresh per-call buffers in the route's staging capacities (`fresh3`), the same with 64-byte-aligned buffers (`fresh+64`) and with an aligned window (`fresh0`), the reference's `iterate` plus full traversal (`reference`), that traversal with the number conversion removed (the pair is the reference's own conversion cost, `ref-num`), and its padded-copy staging (`pad`); then the six stages separately in the `site` shape |
| `shape.sh` | builds the six units at the measured clang line, links the harness against the pinned simdjson, and runs it under a CPU pin; with no `--corpus` it generates the nine documents `probes/json/route/bench.sh` times, from the same commands, and writes the manifest `kernel/json/bench/profile-pipeline.sh --corpus` reads |

## What it checks before the clock

Every variant must return the same verdict, `nk`, `nxp`, `ndst`, `nev`, `err`,
and the same event and arena bytes as `site`; a variant that parses differently
is a setup fault (exit 3), not a timing row.  The escape-list guard's two sides
are checked from the route's own copy of the condition
(`../route/escape_guard.h`): where the guard fires, arm 2's list must be empty
and arm 0 must produce the identical result, and where it does not fire and
arm 2's list is not empty, forcing arm 0 must change the result — a guard that
never mattered cannot pass for one that does.  The manifest digests are checked
first, so a row names the bytes the record names.

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
reference's non-number work.

The escape-list guard has its own paired table on this page's output: `site`
(the route's call before the change, arm 2) against `guard` (the presence scan
and the arm it selects), one call each per timed window, order rotated, with
two `site` slots as the drift control.  Over three sessions of 301 rounds the
guard's median saving is 0.6–2.4 ns/block on the five documents it fires on
(−0.9 to −2.1 on the scalar arrays, −1.5 to −2.4 on `scale-4096`, and −0.8 to
−1.2 on `fast-utf8` in two sessions with a +0.4 cell in the third), and −0.13 to
+0.19 ns/block on the four it cannot help; the
control's median ratio stays within 0.9948–0.9996.  The scan itself is
1.6–2.1 ns/block over a full document and 0.38–0.59 where the early exit finds a
backslash.  The route passes the arm this fact selects, so the list is no longer
built where its output is empty; [the stage timings
page](../../../docs/json-route-stage-timings.md) records the same measurement in
the record's own table.
