# entry-opt

What the entry emitter costs on `syn-strings-64k`, and what three other shapes
of the same work cost.  C only; the harness never reads Lean, never calls a
Lean binary, and writes only to stdout.  `run.sh` builds into a private
directory and writes the transcript beside this file.

```
nix develop -c bash probes/json/route/entry-opt/run.sh
nix develop -c bash probes/json/route/entry-opt/run.sh --rounds 21 --reps 31 --passes 8
nix develop -c bash probes/json/route/entry-opt/run.sh --gates-only
nix develop -c bash probes/json/route/entry-opt/run.sh \
  --doc tests/json-units-bench/build/corpus/syn-dense-64k.json \
  --log probes/json/route/entry-opt/transcript-dense.txt
```

The build also produces `entry-opt-shape`, the untimed entry-word shape report.
`build.sh` prints both binaries' `ok:` paths; with the path it prints, the
report on the recorded document is

```
<build>/entry-opt-shape tests/json-units-bench/build/corpus/syn-strings-64k.json
```

The build is the route's own compiler line —
`-O2 -march=x86-64-v3 -mpclmul -falign-loops=64 -falign-functions=64` for the
six `kernel/json` units and for the two other emitter shapes, `-O3` with the
same target flags for the instrument.  The recorded document,
`tests/json-units-bench/build/corpus/syn-strings-64k.json`, is pinned by size
and sha256 (the document `cost-profile` measures); any other document's size and
sha256 are printed and its reference counts are the run's own pipeline call.
The transcript is written beside this file as `transcript.txt`.

## The shapes

`pipeline.c` calls the installed emitter once per block with `nblk = 1`.  On
this document that is 1024 calls, and the document's entry words are sparse:

```
blocks=1024  positions=2056  nonzero_blocks=679  zero_blocks=345
nonzero bytes per nonzero word: 1:507  2:163  3:9
positions per word:            0:345  1:24  2:21  3:600  4:4  5:6  6:24
empty mask-byte groups in those words: 4572 of 5432 (84.2%)
```

The installed POS8 emitter writes one 32-byte table row per mask byte whatever
the byte holds, so those 679 words pay 5432 group stores for the 860 groups that
carry a position.  The two other shapes are

| shape | what it changes |
|---|---|
| `skip` | the installed eight-iteration group loop with `if (!x) continue`: the same table, the same 32-byte group store, empty bytes skipped |
| `sparse` | no table and no group store: one 4-byte store per set lane, walked with `tzcnt`/`blsr` |

and the call shape under test is one call per block (as today) versus one call
over all block words (`batch`).  Batching needs the entry words of every block
in the caller's `entw`, so the harness keeps one word per block; `pipeline.c`
today writes only `entw[0]`.  The stage-1 rows all write one word per block and
all build the escape list, so their paired differences isolate the emission.

## The gates

Before the clock and again after it.  A failure exits 3 and no row is a
measurement.

- the pipeline call accepts with the document's recorded counts —
  `nk=2056`, `nxp=1772`, `ndst=55931`, `nev=8907`, `err=0`, the arena FNV
  `802d2b86cf9965d7` and events `9f6cc1cf74087659`, which are the values in
  `cost-profile/transcript.txt`;
- a separately run stage-1 loop writes the entry stream and escape list the
  pipeline wrote, and stage 2 over them writes the same header words, arena and
  event bytes;
- every emitter and stage-1 shape writes the same entry stream, leaves every
  word at or past `k' + 8` as the sentinel, and gives stage 2 the same verdict,
  cursors, arena and events;
- every stage-1 shape records the same mask words as the baseline;
- the two other shapes agree with the installed one on every arm:
  64 single lanes, 256 group-0 byte values, 65536 splitmix64 single words, the
  empty and full words, a 4096-word splitmix64 stream, the 1025-word line of the
  document's own words, 1024 random slices of that line, and the document's
  words batched — each at `blk0 = 0` and, where the stream has more than one
  word, at a nonzero `blk0`.  66,952 streams per gate pass, and the gate pass
  runs again after the clock.
- the installed POS8 table is the rule it is specified by (offsets of set bits,
  padded with zeros), checked row by row.

The arm coverage is what makes the emitter claim more than "it matches on this
one document": the document's words exercise the sparse case, and the arms
exercise single-group words, dense words (up to 64 lanes) and a full mask, which
the sparse shape handles with the same walk.

## The measurement

`cost-profile`'s statistics: each round times every act `reps` times in a
rotated order, an act's sample is the round's median, a row is the median of the
round medians with the minimum and maximum beside it, and a delta is the median
of the round's paired difference.  Each act is timed over `passes` full passes
and the sample is the total divided by `passes`.  All acts are in one binary
and are interleaved round by round, so the comparison is same-binary and paired;
the calibrated chain (a dependent-add chain of 2,000,000 iterations) prices the
round's frequency.

`run.sh` refuses to time while Lean is building: an explicit
`lake build` / `lake -c` / `lean -c` / `lean --run` / `leanc` command line, the
repository's `.lake/install-certificate.lock` directory, or more than 5 Lean CPU
ticks across the host in one wall-clock second.  Idle `lean --server` processes
are listed but are not a build; the CPU delta is what distinguishes them.  The
tick delta across the sweep itself is recorded, and the run is refused if it
shows a build that started and finished inside the window.

## Results

Two sweeps of the same binary on `syn-strings-64k` (`transcript.txt`,
`transcript-repeat.txt`) and one on `syn-dense-64k` (`transcript-dense.txt`),
each 21 rounds x 31 reps x 8 passes.  The calibrated chain read 4.43 and 4.59 GHz
in the two `syn-strings` runs and 4.49 GHz in the dense run, so their ns rows
differ by a few percent; the cycle columns are the comparison across that, and
they agree within about 2.5% per row between the two `syn-strings` runs.  The
deltas below are quoted per run.  Absolute rows belong to this harness; the
deltas are the comparison, and the `pipeline` row is a placement reference, not
the route's interval.

### syn-strings-64k — 679 of 1024 words nonzero, 84.2% of their groups empty

| act | median ns (run 1) | min-max | cycles | median ns (run 2) | cycles |
|---|---:|---:|---:|---:|---:|
| `emitter/perblock` | 4314 | 4175-4549 | 18980 | 4214 | 19357 |
| `emitter/batch` | 3327 | 3067-3476 | 14668 | 3120 | 14484 |
| `emitter/perblock-skip` | 3985 | 3569-4349 | 17597 | 3900 | 17760 |
| `emitter/batch-skip` | 1788 | 1748-1890 | 8023 | 1735 | 8059 |
| `emitter/perblock-sparse` | 2552 | 2249-2709 | 11253 | 2537 | 11789 |
| `emitter/batch-sparse` | 797 | 748-813 | 3557 | 762 | 3476 |
| `s1/prologue` | 11210 | 10631-11649 | 49856 | 10710 | 49779 |
| `s1/perblock` | 15450 | 14856-15959 | 68586 | 14545 | 67098 |
| `s1/batch` | 14522 | 13794-15170 | 64424 | 13705 | 63204 |
| `s1/batch-skip` | 12863 | 12112-13563 | 57204 | 12303 | 56442 |
| `s1/batch-sparse` | 11812 | 11372-12259 | 52429 | 11393 | 52516 |
| `pipeline` | 27548 | 26218-28991 | 124053 | 27269 | 124579 |

Paired deltas, ns, median of the per-round differences (run 1 / run 2):

| pair | delta | as us |
|---|---:|---:|
| `s1/perblock - s1/prologue` (the emission term) | +4105 / +3905 | +4.11 / +3.91 |
| `s1/batch - s1/perblock` (batching alone) | -816 / -883 | -0.82 / -0.88 |
| `s1/batch-skip - s1/batch` (skip's own part) | -1610 / -1453 | -1.61 / -1.45 |
| `s1/batch-sparse - s1/batch` (sparse's own part) | -2731 / -2394 | -2.73 / -2.39 |
| `s1/batch-sparse - s1/perblock` (both together) | -3605 / -3258 | -3.61 / -3.26 |

Stage 1, UTF-8 and stage 2 are unchanged and consume the same stream, so a
stage-1 delta is the whole pipeline's delta; the harness cannot time the changed
pipeline because it does not own `pipeline.c`.  The emission term's 4.11 us
becomes 0.54 us (0.61 in run 2) in the `s1/prologue - s1/batch-sparse`
difference: what remains is the cost of writing the 2056 positions.

### syn-dense-64k — 1020 of 1024 words nonzero, 0.0% of their groups empty

| act | median ns | min-max | cycles |
|---|---:|---:|---:|
| `emitter/perblock` | 6441 | 6002-6897 | 29675 |
| `emitter/batch` | 5378 | 5022-5747 | 24466 |
| `emitter/perblock-skip` | 6106 | 5736-6543 | 28124 |
| `emitter/batch-skip` | 5118 | 4801-5486 | 23369 |
| `emitter/perblock-sparse` | 18464 | 17331-19673 | 84463 |
| `emitter/batch-sparse` | 15712 | 14783-16842 | 72655 |
| `s1/prologue` | 8948 | 8366-9619 | 40514 |
| `s1/perblock` | 14705 | 14285-15823 | 68342 |
| `s1/batch` | 13802 | 12992-14773 | 63314 |
| `s1/batch-skip` | 13614 | 12823-14601 | 62278 |
| `s1/batch-sparse` | 23959 | 22861-25848 | 109336 |
| `pipeline` | 93189 | 87653-99974 | 429707 |

Paired deltas, ns, median (min-max of the round differences):

| pair | delta | as us |
|---|---:|---:|
| `s1/perblock - s1/prologue` | +5986 | +5.99 |
| `s1/batch - s1/perblock` | -985 (-1560..-397) | -0.99 |
| `s1/batch-skip - s1/batch` | -202 (-702..+480) | -0.20 |
| `s1/batch-sparse - s1/batch` | +10335 (+9070..+11127) | +10.34 |

### What the two documents say

- **Batching the call is the only shape that wins on both**: -0.82/-0.88 us on
  `syn-strings` and -0.99 us on `syn-dense`, against a per-block call that costs
  one `noinline` call and one loop setup per block.  Over precomputed words the
  same pair is -1.01/-1.09 us.  It changes the caller and the `entw` capacity,
  not the emitter's body.
- **Skipping empty groups pays only when batched, and only on sparse words**:
  -1.61/-1.45 us on `syn-strings` on top of batching, and -0.20 us on
  `syn-dense` (a range that crosses zero: -0.70..+0.48).  Without batching its
  own part is -0.30/-0.35 us on `syn-strings`, against -2.50 us when batched:
  the eight data-dependent branch tests cost most of what the empty groups'
  stores saved, and the batched loop is where that changes.
- **The per-lane walk is the largest sparse-document win and a dense-document
  loss**: -2.73/-2.39 us on top of batching on `syn-strings`, +10.34 us on
  `syn-dense`, where the 8 groups become 36-38 dependent `tzcnt`/`blsr` steps
  per block.  It is not a drop-in shape; it needs a per-document selection the
  emitter does not make, or a per-word hybrid this experiment does not test.
- The emitter rows show the floor the stage-1 rows approach: on `syn-strings`
  4.31 us per block-by-block pass falls to 0.80 us batched per-lane (4.21 to
  0.76 in the second run), for the same 2056 positions.

## Limits

- Two documents, one arm (2: POS8 emitter, escape list built, gated UTF-8), one
  compiler line: `syn-strings-64k` (84.2% empty groups) and `syn-dense-64k`
  (0.0%).  The 4 MiB sibling has the same entry-word shape as `syn-strings-64k`
  — 84.1% empty groups over 65,536 blocks, from `entry-opt-shape`, untimed — but
  it is not timed, and no other corpus document is.  A shape can still lose on a
  document between those two densities.
- The dense document's pipeline row is 93.2 us, of which the stage-1 loop is
  14.7 us: the rest is UTF-8 and stage 2 over its 132,638 events.  A stage-1
  change of 1 us is a smaller share there than on `syn-strings` (27.5 us, stage
  1 15.5 us).  The rows do not compare shares across documents.
- The regime is not the route's.  `cost-profile/transcript.txt` records the same
  emission term as 10.95 us in the route context and 6.34 us back to back
  (its paired `entry` rows); this harness's emission term is 3.9-4.1 us.  The
  difference is context, placement and the escape list that both members of
  this harness's pair carry, which is why a candidate's route number belongs to
  `workspace.sh` and is not scaled from these rows.
- Absolute rows are this harness's.  `cost-profile/README.md` records the same
  kernel objects and call differing by more than 1.5x across rebuilt harnesses
  at a constant calibrated clock, so no row here is compared with
  `cost-profile`'s or the route's numbers except where both sides are named.
- The emitter rows read precomputed words, so they exclude the mask unit's work
  and the escape list; the stage-1 rows include both.  Only the stage-1 paired
  differences are a claim about the route's stage 1.
- The stage-1 rows keep one entry word per block, which the batched shapes need
  and the per-block shape does not; the 8 KiB write is in every stage-1 row, so
  it cancels in the paired differences rather than favouring one shape.
- The two other shapes are new C text compiled at the same line, not edits to
  `kernel/json/entry.c`.  Adoption would change a pinned fixture and a Lean
  body: `probes/install/ir/json-entry.candidate.ll` and its AST pin in
  `LeanLLVM/Refinement/JsonEntryIR.lean` for a kernel change, and
  `probes/install/ir/json-pipeline.candidate.ll` and
  `LeanLLVM/Refinement/JsonPipelineIR.lean` for the caller-side batch.  This
  probe measures, and does not amend, either.
- Batching needs `entw` to hold `blocks` words instead of one; the route's
  staging allocates 8 bytes for it today, so adoption also touches the
  workspace's staging and the `pipeline.h` ABI text.
- The `sparse` shape keeps `entry.h`'s contract as stated — no byte of `out`
  outside `[k, k' + 8)` is written, and only `[0, k')` is the stream — but its
  last written lane is `k' - 1` rather than POS8's `k' + 7`, so the header's
  sentence about which lane each emitter leaves last would need the new shape's
  answer.  The `skip` shape keeps POS8's answer.
