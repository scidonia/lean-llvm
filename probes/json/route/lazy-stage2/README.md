# lazy-stage2

A bench-only instrument that prices stage 2's escape decode two ways — with the
stage-1 escape-position list, and with the list-free rescan the shipping arm
takes instead — so the deferral's tradeoff is measured rather than estimated.
Nothing here is a kernel unit, a candidate for the tree, or read by any gate of
the shipped route.

```
nix develop -c bash probes/json/route/lazy-stage2/run.sh
nix develop -c bash probes/json/route/lazy-stage2/run.sh --rounds 21 --reps 21 --core 2
```

The script builds the route's six kernel objects at the route's own compiler
line (`-O2 -march=x86-64-v3 -mpclmul -falign-loops=64 -falign-functions=64`) and
this instrument at the harness line (`-O3`, same target flags), into a private
temporary directory, and writes `transcript.txt` beside itself.  The document is
`tests/json-units-bench/build/corpus/syn-strings-64k.json`, regenerated from
`gen.c` when absent and checked against the recorded size and sha256 either way.

## What is timed

Eight acts run in one binary and one session, rotated within each round (`acts`
advance by one each round), so every reading is a same-host pair.  The buffers
are shaped as `workspace.cc` shapes them: the window `[0,0,0] ++ document ++
64`, `epcap = 64 * blocks + 9`, `xpcap = 64 * blocks + 8`, `dstcap = n + 64`,
`evcap = 13 * n + 128`.

| act | what it calls |
|---|---|
| `stage2` | `leanllvm_json_stage2` over the pipeline's entry and escape streams — the committed walk at arm 2 (`S2_VAL \| S2_STR \| S2_EV`) |
| `stage2_rescan` | the same call with `nxp = 0`: stage 2 classifies each body's own span and decodes it with `leanllvm_json_escape_decode`, the list-free arm |
| `expand_arena` | `leanllvm_json_escape_expand` over the 620 escaped bodies, in order and with one threaded cursor, into the arena — the list-driven decode on its own |
| `expand_l1` | the same 620 calls, each body decoded into one reused 4 KiB scratch instead of the 55,931-byte arena.  Its per-body output is gated against the arena slice, so the work is identical and only the destination differs |
| `copy_arena` | `memcpy` of `ndst` bytes from the document into the arena: the floor of writing the decoded extent at all |
| `pipeline` | `leanllvm_json_pipeline` at arm 2 — the stage-1 list is built and stage 2 consumes it |
| `pipeline_rescan` | the same pipeline at arm 0 — the shipping arm: stage 1 emits no list and stage 2 rescans |
| `chain` | the calibrated clock |

`stage2_rescan` is not a fork: it is the committed ABI with an empty list, and
its verdict, extents, refusal offset, arena and events must equal `stage2`'s
byte for byte before the clock.  `pipeline_rescan` likewise must equal
`pipeline`'s consumer-observable output (the list count is the one field that
differs by construction).  Those gates are what make the paired differences a
price for the same work rather than a comparison of two stages.

## Gates

Before the clock and again after it:

- the reference pipeline accepts with the recorded words (`nk=2056`,
  `nxp=1772`, `ndst=55931`, `nev=8907`, `err=0`);
- an independent byte scan (`probes/json/escape_driver.c`'s rule) reproduces the
  escape list, every position falls inside exactly one of the 685 bodies, and
  exactly 620 bodies carry one;
- stage 2 over the pipeline's streams reproduces the arena and event bytes;
- the rescanned walk reproduces the committed walk's verdict, extents, refusal
  offset, arena and events exactly;
- the list-free pipeline reproduces the list arm's consumer-observable output
  exactly;
- the direct expander over the 620 bodies, one cursor, reproduces the arena and
  leaves `xj == nxp`;
- every `expand_l1` body's scratch content equals its arena slice;
- the largest decoded body (151 bytes) fits the L1 scratch.

A failed gate exits 3 and prints nothing as a measurement.

## Results, `rounds=21 reps=21 core=0`, chain 4.587 GHz

```
stage2             10772 ns     stage2_rescan     15861 ns
expand_arena        6952 ns     expand_l1          6241 ns
copy_arena           803 ns     pipeline          28994 ns
pipeline_rescan    31387 ns
```

Per-round pairs (median of the round differences, with min..max):
`stage2_rescan - stage2 = 4284` (784..8528) ns, `pipeline_rescan - pipeline =
2155` (0..11554) ns, `expand_arena - expand_l1 = 427` (0..4145) ns.

| reading | value | share of the arm-2 pipeline |
|---|---:|---:|
| rescan price in stage 2 (`stage2_rescan − stage2`, act medians) | 5.09 µs | 17.6 % |
| net pipeline tradeoff (`pipeline_rescan − pipeline`, act medians) | +2.39 µs | +8.3 % |

The `expand_l1 − stage2_rescan` and `copy_arena − stage2_rescan` rows are zero
in the median: on this document the rescan costs at least as much as decoding
every escaped body into an L1-resident scratch, and far more than the arena
copy.

## What withholding the list does to the verdict

Nothing, now.  `s2_string_body` takes the list branch when a list is supplied
and otherwise scans the body's span; both validate every body, so a withheld
list is a decoding-route change and not a validation change.  `verdict-probe.c`
shows it on three small documents:

```
control-byte   n=11 nk=7 nxp=1  pipeline: verdict=0 err=7
control-byte   same walk, list withheld (nxp=0): verdict=0 err=7
bad-escape     n=12 nk=7 nxp=1  pipeline: verdict=0 err=7
bad-escape     same walk, list withheld (nxp=0): verdict=0 err=7
structural     n=6 nk=5 nxp=0  pipeline: verdict=0 err=5
structural     same walk, list withheld (nxp=0): verdict=0 err=5
```

`{"a":"x<0x01>y"}` and `{"a":"x\qy"}` are refused by the reference parser and by
both stage-2 routes at the same byte; the structural refusal is untouched.  On
the pre-deferral unit the two withheld-list calls accepted both string-body
documents — that observation is what the rescan path removes, and the probe is
the control that would fail if it regressed.

## What the rows say

On this escape-heavy document — 620 of 685 string bodies carry an escape, and
55,931 bytes are decoded — the list-free arm is **slower end to end** on this
host: stage 2 pays about 5 µs more to rescan the bodies, which is more than the
stage-1 list costs here, and the net is +2.4 µs (8.3 %) against arm 2.  The
paired spread includes zero, so the size of the net is not established by this
run; the direction on this class is.

That is the tradeoff the north-star criterion makes explicit: the criterion is
a *stage-1* comparison (the fused block unit's arm 0 against simdjson's stage 1
over the eight documents), and arm 0 meets it on every class — stage 1 simply
does less work.  Moving the escape work into stage 2 is not free, and on a
document whose strings are mostly escaped the rescan can cost more than the
structure it replaces.  On a document with few or no escapes the rescan's body
scan finds nothing and the stage-1 saving is kept; the stage-1 north-star table
is the measurement for that side, and this probe is the measurement for this
one.  Neither harness claims the other's row.

## Limits

- One document, one arm pair, one host.  `syn-strings-64k` is the corpus's
  escape-heavy shape; a document whose strings are mostly unescaped takes the
  plain form for them and this instrument's tradeoff is far smaller.
- Absolute rows belong to this binary and this host.  The version that measured
  the pre-deferral probe recorded the same kernel and call at 23.8 µs and
  41.2 µs in two rebuilt harnesses at one calibrated clock; the paired
  differences are what survive a rebuild, and the `pipeline` row is an anchor
  for the shares, not a route figure.
- The rescan's price is not a decoder price.  It includes classifying every
  body's span (`z_scan`) and the list-free decode's own window scan; the
  `stage2_rescan − stage2` row is the whole difference, not one pass of it.
- `expand_l1` prices decode-with-validation into a small destination.  The
  rescan writes into the arena because stage 2's escaped records name arena
  offsets; a variant that validated without materialising would differ by at
  most the store side, which `copy_arena` bounds at 0.8 µs.
