# lazy-stage2

A bench-only instrument that prices stage 2's escape-list-driven decode and the
lazy alternative to it, so the question "can stage 2 skip materialising the
decoded strings?" is answered with a paired measurement rather than an
estimate.  Nothing here is a kernel unit, a candidate for the tree, or read by
any gate of the shipped route.

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

Six acts run in one binary and one session, rotated within each round (`acts`
advance by one each round), so every reading is a same-host pair.  The buffers
are shaped as `workspace.cc` shapes them: the window `[0,0,0] ++ document ++
64`, `epcap = 64 * blocks + 9`, `xpcap = 64 * blocks + 8`, `dstcap = n + 64`,
`evcap = 13 * n + 128`, and arm 2.

| act | what it calls |
|---|---|
| `stage2` | `leanllvm_json_stage2` over the pipeline's entry and escape streams — the committed walk (`S2_VAL \| S2_STR \| S2_EV`) |
| `stage2_plain` | the same call with `nxp = 0`: every body takes the input-span form, so no body is decoded and none is validated against the list |
| `expand_arena` | `leanllvm_json_escape_expand` over the 620 escaped bodies, in order and with one threaded cursor, into the arena — the decode a consumer would pay if it materialised the strings itself |
| `expand_l1` | the same 620 calls, each body decoded into one reused 4 KiB scratch instead of the 55,931-byte arena |
| `copy_arena` | `memcpy` of `ndst` bytes from the document into the arena: the floor of writing the decoded extent at all |
| `pipeline` | `leanllvm_json_pipeline` |

`stage2_plain` is the committed ABI, not a fork, and it is the *lower* bound of a
lazy stage 2: a lazy walk that still emits one 13-byte record per string does
the same work minus the decode and the list-driven validation.  `expand_l1`
prices that validation when the destination is not the arena: its per-body
output is gated against the arena slice, so the work is identical and only the
destination differs.

## Gates

Before the clock and again after it:

- the reference pipeline accepts with the recorded words (`nk=2056`,
  `nxp=1772`, `ndst=55931`, `nev=8907`, `err=0`);
- an independent byte scan (`probes/json/escape_driver.c`'s rule) reproduces the
  escape list, every position falls inside exactly one of the 685 bodies, and
  exactly 620 bodies carry one;
- stage 2 over the pipeline's streams reproduces the arena and event bytes;
- the plain walk's event stream is the committed one's **record shape**: the
  same tags in the same order, the same record count, and the same bytes for
  every non-string record; only the 685 string records' length and field differ
  (`str_records=685` of `records=687`).
  That is what makes `stage2_plain` a cost proxy for a lazy stage 2 rather than
  a different stream;
- the direct expander over the 620 bodies, one cursor, reproduces the arena and
  leaves `xj == nxp`;
- every `expand_l1` body's scratch content equals its arena slice;
- the largest decoded body (151 bytes) fits the L1 scratch.

A failed gate exits 3 and prints nothing as a measurement.

## Results, `rounds=21 reps=21 core=2`, chain 3.256 GHz

```
stage2         13704 ns        stage2_plain     2745 ns
expand_arena    9461 ns        expand_l1        8609 ns
copy_arena      1186 ns        pipeline        36049 ns
```

Per-round pairs: `stage2 - stage2_plain = 10794`, `expand_l1 - stage2_plain =
5886`, `expand_arena - stage2_plain = 6604`, `expand_arena - expand_l1 = 809`,
`copy_arena - stage2_plain = 0`.

| reading | value | share of the pipeline |
|---|---:|---:|
| list-driven decode in stage 2 (`stage2 - stage2_plain`) | 11.0 µs | 30 % |
| decoding the same bodies into an L1 scratch | 8.6 µs | 24 % |
| writing the 55,931-byte arena (`copy_arena`) | 1.19 µs | 3.3 % |
| lazy pipeline, no validation (`pipeline - stage2 + stage2_plain`, paired) | 26.0 µs | saves 28 % |
| lazy pipeline, validation kept (`+ expand_l1`, paired) | 34.8 µs | saves 3.6 % |

The share column is `(stage2 − stage2_plain) / pipeline` on the act medians
(30.4 %), and the same for the validation-kept variant with `expand_l1`
subtracted as well (6.5 %).  The paired rows are per-round sums and carry both
terms' noise: they are wider (26.0 µs spans 23.4–28.7) and they say 28 % and
3.6 %.  The two constructions bracket the same thing; the act-median one is the
tighter.

The **shares, not the absolute rows**, are what this probe claims.  Another
session of the same instrument at chain 4.428 GHz (rows 1.36× smaller in
proportion: `stage2` 10.048, `stage2_plain` 2.112, `expand_l1` 6.643,
`copy_arena` 0.926, `pipeline` 28.183) gave the same two shares, 28.2 % and
4.6 %, and a first session at 4.267 GHz gave 27.6 % and 2.3 %.  The
validation-kept share is the noisy one because it is a small difference of
large terms.

## What withholding the list does to the verdict

`s2_string_body` takes form (a) — the body is its own materialisation and
nothing is checked — exactly when the body has no listed position, so the list
*is* the validation driver for string bodies.  `verdict-probe.c` shows both
consequences on two eleven/twelve-byte documents:

```
control-byte   n=11 nk=7 nxp=1  pipeline: verdict=0 err=7
control-byte   same walk, list withheld (nxp=0): verdict=1 err=0 nev=28
bad-escape     n=12 nk=7 nxp=1  pipeline: verdict=0 err=7
bad-escape     same walk, list withheld (nxp=0): verdict=1 err=0 nev=28
```

`{"a":"x<0x01>y"}` and `{"a":"x\qy"}` are refused by the reference parser and by
the committed pipeline at the byte the list names; with the list withheld the
walk accepts both.  So the 28 % row above is not a lazy stage 2 — it is a stage 2
whose verdict no longer agrees with the parser's, which is what the record's
refusal clause and the route's parser equivalence are stated at.

## What the rows say

The decode and validation of the escaped bodies is the cost; the materialisation
is not.  Decoding into a reused 4 KiB scratch costs within 0.8 µs of decoding
into the 55,931-byte arena, and a plain `memcpy` of the arena's extent is
1.19 µs.  So a lazy stage 2 that *keeps* the list-driven validation buys
1.2-2.4 µs (3.6-6.5 %): the validator still reads the same bytes and parses the
same 1,772 escapes.

Removing the list-driven work altogether is the only variant that saves
meaningfully (28 %), and it is not a lazy stage 2 but a stage 2 that stops
validating string bodies: form (a) in `s2_string_body` is what a body with no
listed position takes, and the list is stage 1's record of every byte a string
body must be checked for.  A pipeline that skipped it would accept documents the
reference parser refuses, which is exactly what the stage-2 record's refusal
clause and the route's parser equivalence are stated at.

Even the upper bound does not close the full-parse gap: a pipeline with stage 2
at zero would still be `pipeline - stage2 = 22.3 µs`, and this session's lazy
bound is 26.0 µs (at 3.256 GHz; the recorded pair's clock ratio makes the first
number about 16.4 µs in the 4.4 GHz regime).  The recorded simdjson 5.0.5
`parse` row for this document on this host is 4.929 GB/s (13.3 µs, 0.944
cycles/byte at 4.49 GHz).  Clock-normalised to that row, stage 2 free is about
16-18 µs and the lazy bound about 19-20 µs, so the pair would be about 1.2-1.4×
against the ~2× this session shows clock-normalised (2.1× at 4.428 GHz, the
probe's own earlier run) — a narrowing, not a closing.  That is a
cross-binary comparison and this shop's rows move by up to a third across
rebuilt harnesses (the cost profile's README records 23.8 µs against 41.2 µs at
one clock); the paired columns above are the same-binary evidence.

## Limits

- One document, one arm, one host.  `syn-strings-64k` is the corpus's
  escape-heavy shape: 620 of 685 string bodies carry a listed position and
  55,931 bytes are decoded.  A document whose strings are mostly unescaped takes
  form (a) for them and stage 2's list-driven share is far smaller; on `syn-`
  documents without escapes the whole term disappears, so this instrument's
  ratio is a bound for *this* document class, not for the corpus.
- Absolute rows belong to this binary.  The cost profile's README records the
  same kernel and call measuring 23.8 µs and 41.2 µs in two rebuilt harnesses at
  one calibrated clock; the paired differences above are what survive a
  rebuild, and the `pipeline` row is an anchor for the shares, not a route
  figure.
- The simdjson row quoted above is from `docs/json-pipeline-performance.md`, a
  different binary and session; it is a cross-binary comparison and is labelled
  as one there.  The same-binary, same-session evidence is the paired difference
  column.
- `expand_l1` prices decode-with-validation.  A validator that decodes logically
  but stores nothing would be cheaper by at most the store side, which
  `copy_arena` bounds at 0.93 µs for the whole arena extent; no row here claims
  such a validator's exact cost, because none is implemented.
