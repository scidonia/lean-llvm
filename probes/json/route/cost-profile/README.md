# cost-profile

A C-only instrument that measures the `syn-strings-64k` native interval the
reused workspace times, at the route's compiler line and arm, and prices the
pieces it is made of.

```
nix develop -c bash probes/json/route/cost-profile/run.sh
nix develop -c bash probes/json/route/cost-profile/run.sh --rounds 31 --reps 21 --core 0 --placement
```

`--placement` adds a fourth phase: the instrument is rebuilt with a filler
object that moves the kernel objects to the route harness's own code addresses,
and both placements are timed, so a difference between two binaries is
attributed to placement instead of being read as a kernel property.

The script builds into a private temporary directory, refuses to time while
Lean is building or elaborating (an explicit `lake build` / `lean -c` /
`lean --run` / `leanc` command line, or more than 50 ms of Lean CPU across the
host in one wall-clock second), and writes `transcript.txt` beside itself.  It
runs two sweeps of the same binary: `--context route`, which precedes every
timed act with the route's fresh call and its reused admission and staging, and
`--context none`, which runs the acts back to back.  The difference between the
sweeps is the context term, measured rather than assumed.  After them, the
route's own `workspace.sh` runs in the same session, so the 41-42 µs figure
being decomposed and this instrument's rows belong to one host state.

## What is timed

The kernel objects are the route's own sources compiled at
`-O2 -march=x86-64-v3 -mpclmul -falign-loops=64 -falign-functions=64`, arm 2,
with the caller's buffers shaped as `probes/json/route/workspace.cc` shapes
them: the window `[0,0,0] ++ document ++ 32` at `malloc` alignment, and the
thirteen buffer capacities the record declares (`epcap = 64 * blocks + 9`,
`xpcap = 64 * blocks + 8`, `dstcap = n + 64`, `evcap = 13 * n + 128`).

| act | what it calls |
|---|---|
| `masks` | the mask unit, the entry word's composition and the tail clamp |
| `entry` | the entry emitter over precomputed words |
| `escape` | the escape-list builder over precomputed masks |
| `s1_no_escape` | the block prologue plus the emitter |
| `s1_fused` | the whole of `pipeline.c`'s block loop |
| `pipe_nostage2` | the block loop plus the UTF-8 call |
| `utf8` | the UTF-8 stage at the route's gate |
| `stage2` | the walk over the pipeline's entry and escape streams |
| `stage2_plain` | the same walk with an empty escape list (cost probe) |
| `expand` | `leanllvm_json_escape_expand` once per escaped body |
| `pipeline` | `leanllvm_json_pipeline` |
| `native` | the pipeline, the 80-byte tagged header and the two result `memcpy`s |
| `copy_total` / `copy_dst` / `copy_ev` | the header and copies, and each copy alone |
| `chain` | the calibrated clock: a dependent-add chain, one iteration per cycle |

The first five of those are nested: `masks`, `s1_no_escape`, `s1_fused`,
`pipe_nostage2` and `pipeline` differ by exactly one call each.  The per-round
paired differences therefore isolate one term each, and per round they
telescope to the pipeline.  The report prints those differences, the same
residual against the *isolated* acts (`entry`, `escape`, `stage2` over
precomputed streams) as the de-fusion term, and `stage2 - stage2_plain` and
`expand` for the list-driven decode.  No sum of medians is presented as the
pipeline's time.

Every row carries a calibrated-clock figure as well: the `chain` act runs in
each round, and cycles are that round's act median times the chain's iteration
count over that round's chain time.  This makes a frequency difference visible
instead of silently inflating a nanosecond row.

## Gates

Before the clock and again after it:

- one untimed `leanllvm_json_pipeline` call is the reference observation, and it
  must accept with `nxp=1772`, `ndst=55931`, `nev=8907`;
- a separately run stage-1 loop must write the same entry stream and escape
  list, and stage 2 over them the same header words, arena and events;
- the independent byte scan in this file (the rule
  `probes/json/escape_driver.c` states) must derive the same positions, every
  position must fall inside exactly one string body, and 620 bodies must carry
  one;
- `leanllvm_json_escape_expand` over those 620 bodies, in order and with one
  threaded cursor, must write exactly the pipeline's arena and leave the cursor
  at `nxp`;
- the admission must select arm 2 (`escape_skip == 0`).

A failed gate exits 3 and prints nothing as a measurement.

Every act updates the harness's volatile sink before it returns, so that update
is inside the timed interval.  It is one L1-resident read-modify-write; it
appears once in each member of a paired difference, so the differences are
unaffected, and it is about 1-2% of the smallest standalone row (`copy_ev`).

## The reference parser

The instrument does not link simdjson.  `syn-strings-64k`'s paired full-parse
figure (11.5 µs, and 11.7 µs in this session's `workspace` run) is the existing
`workspace`/`paired-reference` measurement; reproducing it here would require
the C++ baseline and the 5.0.5 dev output, which is outside this instrument's
"C only" build.  The route binary's `--consume` row is compared field by field
as a second binary's reading of the same kernel; it is not an independent
parser.

## A measured limit: code placement

The same kernel objects and the same call can differ by more than a factor of
1.5 across rebuilt harnesses at a constant calibrated clock: in the probe that
led to this knob, one build measured 41.2 µs / 197 k cycles and another
23.8 µs / 111 k cycles on the same document, same arm, same buffers, with the
chain at 4.7-4.8 GHz in both.  `build.sh` takes `FILLER_N` and `run.sh` takes
`--placement`: a filler object of that many bytes is linked before the kernel
objects, moving their code addresses without changing their code, and
`--placement` rebuilds the instrument until `leanllvm_json_pipeline` sits at the
route harness's own address.

On this instrument the natural address `0x82c0` and the route harness's exact
address `0xef80` measured 31.28 and 31.49 µs `native` in the route context, so
the kernel's code address alone does not account for the route harness's own
40.8 µs.  The larger spread came from whole-binary rebuilds, where data
addresses and linkage move too; it is a limit on cross-binary comparison, not an
effect of the kernel objects.

The 42.2 µs figure therefore belongs to `workspace`'s harness.  A rebuilt
harness is not a substitute for its absolute figure, though it decomposes the
work it does reproduce; the report states which regime each row belongs to and
does not attribute the context/placement remainder to any kernel stage.
