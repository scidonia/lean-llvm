# Refusal census

Two corpora, measured separately and labelled with their units.

## The corpus this repository ships

`repo-census.sh` runs the built driver over every **tracked** `*.ll` file and
compares each result with `repo-corpus.manifest`.  The manifest is an
expectation, so it checks both directions: an entry that says `parsed` must
parse, and an entry that says `refused` must be refused with the named token.
A driver that parses everything fails on the refused entries; one that refuses
everything fails on the parsed entries.

```sh
nix develop -c bash probes/install/lake-locked.sh build leanllvm
bash probes/census/repo-census.sh          # checked
bash probes/census/repo-census.sh --all    # also counts generated IR
```

Measured 2026-11-08 with the driver built from this tree:

- **Tracked corpus: 27 files, 29 `define`s — 24 of the 27 files parse, 3 are
  refused.**  The refusals are `probes/install/ir/baseline.o1.ll` (return
  attribute `range`), and `probes/install/ir/baseline.raw.ll` and
  `probes/install/ir/candidate.raw.ll` (parameter attribute `noundef`).
- **Coverage: 0 of the 27 files contain an `icmp … ptr` line, 0 contain a
  written callee function type, 3 contain a literal vector operand, 2 an
  `extractelement` line, 3 an `insertelement` line and 3 a `zeroinitializer`
  operand.**  The three files carrying those vector constructs are
  `tests/v16/ci2.ll` (below), `probes/install/ir/json-s1-masks.candidate.ll` and
  `probes/install/ir/json-entry.candidate.ll`, and all three parse, so the corpus
  does exercise them.
- **Working tree including generated IR: 46 files — 42 of the 46 files parse,
  4 are refused.**  The fourth refusal is `probes/app/build/app.ll`,
  refused at line 1 (`source_filename`), not at an instruction.  That file holds
  the tree's only `icmp … ptr` line, so the line itself is never reached.  The
  extra 19 files are untracked build output under `probes/*/build`, which is why
  `--all` reports without asserting: the checked manifest is the tracked set.

## The stage-1 kernel

`tests/v16/ci2.ll` is `v16.generated.ll`'s `@ci2` — the stage-1 index kernel the
fast prototype uses — with the capture strip applied: the per-function text the
extended census's `strip.py` produces, so it is the same text the peel below was
measured on.  It is committed, and `repo-corpus.manifest` lists it as `parsed`, so
the kernel's parse is a checked entry rather than a scratch-corpus observation.

`tests/v16/depth_count.ll` is the same strip applied to that module's
`@depth_count`, the depth counter of the same index stream: the `nocapture`,
`readonly` and `writeonly` parameter attributes, the `align` on the two loads and
the four stores, and the `nuw` flag on the counter's add are removed, and every
other line is verbatim.  It is committed and listed as `parsed`, and
`LeanLLVM/Vellum/DepthCountRefine.lean` proves the kernel against its depth fold
(`depth_count_refines`) over that text, with the parsed AST pinned by a `#guard`.
The strip instrument is the extended census's scratch `strip.py`, so — as for
`ci2.ll` — the re-runnable check of the fixture is the manifest entry and this
script, not the capture.

`probes/install/ir/json-s1-masks.candidate.ll` is the extracted stage-1 mask
unit — `kernel/json/s1_block.c`'s `leanllvm_json_s1_masks` at the measured
compiler line, normalised by `probes/install/ir/capture-s1-masks.sh`.  That
capture derives, in the same run, the normalisation inventory
(`json-s1-masks.strip.tsv`), the rewrite inventory (`json-s1-masks.rewrites.tsv`)
and the fixture's own construct inventory (`json-s1-masks.inventory`), and
refuses when any of the four no longer regenerates.  The fixture is committed and
`repo-corpus.manifest` lists it as `parsed`, so its parse is a checked entry;
`LeanLLVM/Vellum/JsonS1MasksIR.lean` pins the parsed AST by `#guard` and
`LeanLLVM/Vellum/JsonS1MasksSteps.lean` proves the body (`s1_masks_refines`).

`probes/install/ir/json-entry.candidate.ll` is the extracted entry unit — the two
position emitters `@s1f_k_pos8` and `@s1f_k_b8` of `kernel/json/entry.c` at the
measured compiler line, reduced to those two `define` blocks by
`probes/install/ir/capture-entry.sh`.  That capture derives, in the same run, the
normalisation inventory (`json-entry.strip.tsv`), the rewrite inventory
(`json-entry.rewrites.tsv`), the table read it rewrites (`json-entry.table.tsv`,
per site) and the fixture's construct inventory (`json-entry.inventory`), and
`kernel/json/identity/inventory.sh --unit entry` is the gate: it regenerates all
five, compares them, parses the fixture and fires its controls.  The fixture is
committed and `repo-corpus.manifest` lists it as `parsed`, so its parse — both
functions, one file — is a checked entry;
`LeanLLVM/Vellum/JsonEntryIR.lean` pins the parsed ASTs by `#guard`,
`LeanLLVM/Vellum/JsonEntrySteps.lean` proves POS8's body (`entry_pos8_refines`)
and `LeanLLVM/Vellum/JsonB8Steps.lean` proves B8's (`entry_b8_refines`), the two
kernels' agreement (`entry_pos8_b8_agree`) and B8's undefinedness beyond its
reads (`entry_b8_undefined_of_no_read`).

The manifest entry counts once the fixture is **tracked**: `repo-census.sh`
enumerates `git ls-files`, so a green run over an untracked file describes a tree
state that will not exist once it is committed.  Both fixtures are tracked, so
the counts above include their rows, and the run that counts is one over a tree
in which they are.

The chain below is the peel **sequence** on that text, not the set of constructs
the text contains: each relaxation rewrites the line it is applied to, so a
construct on a line another relaxation stubs is never reached and cannot appear.
`peel2.py` is the scratch instrument, not part of this repository; the re-runnable
check of the same fact is the manifest entry and `repo-census.sh` above, which
drive the built driver over the committed file.  The sequence it reports:

| driver | chain |
|---|---|
| `c5adb94` (before this change) | `semantic:vector-literal-operand`, `semantic:op-extractelement` |
| this change | *(empty)* |

The text itself carries four of the constructs this change adds, and the sequence
names two of them:

- literal vector operands, on the `icmp` lines and inside the `pclmulqdq` call;
- `insertelement` with a `zeroinitializer` operand, at `tests/v16/ci2.ll:97`;
- `extractelement`, at `tests/v16/ci2.ll:99`.

`op-insertelement` cannot appear in the sequence because the first relaxation,
`semantic:vector-literal-operand`, replaces every line carrying a literal vector
or `zeroinitializer` — including that line — with a stub before the parser reaches
it.  `zeroinitializer` is hidden the same way.  Both therefore had to be modelled
even though the sequence does not name them.  The extended-census table below
does count `op-insertelement` for other functions, because those `insertelement`
lines carry no literal vector or `zeroinitializer` and so are never stubbed.

The chain before typed `getelementptr` carried `semantic:gep-element-i64` as
well; the previous change admitted that construct, which is why it is absent from
the first row.  The driver run on the committed fixture (`--passes none`) exits 0
and re-emits 120 lines.

The kernel's `call <2 x i64> @llvm.x86.pclmulqdq(... <2 x i64> <i64 -1, i64 0>
...)` line carries the literal vector in an argument position and takes a
vector-typed result; the argument position is covered by the literal operand and
the argument scanner, and the vector-typed result was already accepted, so
neither needed a construct of its own.

## The delta this change measured on the extended corpus

Before = the `after2` run recorded for the previous package (`integrated.O2.after2.jsonl`
and its three siblings, driver at `c5adb94`); after = a fresh run of the same
instrument over the same texts with this change's driver.  Both runs open with the
three controls, and all fifteen control lines (three per input, counting
`control.jsonl`) report `parses=True caps=[]` in both.

Units: a construct column counts **functions whose peel chain contains that
construct** (one hit per function per construct, not files and not instructions);
the parsed column counts **functions** out of the universe's total.

| universe, flags | functions | parsed before → after | literal vector operand | `extractelement` | `insertelement` | non-splat vector constant |
|---|---|---|---|---|---|---|
| integrated O2 | 41 | 4 → 8 | 11 → 0 | 14 → 0 | 7 → 0 | 3 → 0 |
| integrated O3 | 41 | 3 → 7 | 12 → 0 | 14 → 0 | 9 → 0 | 3 → 0 |
| p5 O2 | 58 | 1 → 1 | 46 → 0 | 46 → 0 | 47 → 0 | 2 → 0 |
| p5 O3 | 58 | 1 → 1 | 46 → 0 | 46 → 0 | 47 → 0 | 2 → 0 |

No function that parsed before stopped parsing in any of the four runs.  The four
that newly parse are `ci`, `ci1`, `ci2` and `v2a_nc` of `v16.generated.ll`, at
both flag sets — so this package enabled three kernels it was not asked for,
besides `ci2`.  The p5 universe's parsed count does not move: every function
there still needs several other constructs, which is why a construct's chain
membership falling to zero is the measurable part rather than the parsed count.

## The extended census (scratch corpus, not in this repository)

The numbers below come from a corpus that is **not** committed.  It has no Git
history, so its identity is the digest of its inputs, not a commit.  They are
an observation, not a route a reader can re-run from this checkout.  The
re-runnable route is the tracked-corpus manifest above.

Corpus: `/tmp/scidonia-spike18`, 19 `*.ll` modules under `ir/`: `p16` (`-O2
-mavx2 -fno-slp-vectorize -mbmi -mbmi2 -mpclmul` and `-O3 -march=x86-64-v3
-mpclmul`), `utf8f` (same two flag sets), the generated `v16` kernel set, the
address-taken walker TU `keep_ws` (both flag sets), and the earlier `p5`
modules promoted with `instnamer`.  They were emitted or captured by
`/tmp/scidonia-spike18/census/COMMANDS.md` with clang/opt 21.1.8 from
`/tmp/scidonia-spike17/src`.

Digests (`sha256sum`):

| input | digest |
|---|---|
| `census/census.py` | `84634a83cef2bc1dc2872d4bc727d48adb0b695be8d850120c99d840a03cdd08` |
| `census/peel2.py` | `de637250b88c2617e2c86be53f321e4f9e348374f19f95b910c1dbcc87ab5a66` |
| `census/strip.py` | `ceffcf4ec339c00459832cb899869701bf3f469cd1e6baccede3d9b8712b585f` |
| `census/aggregate.py` | `c1ec26f2bfde4ad9530c7d848aae8295c89e84a3a717e1cd470b1b1fee1f116e` |
| `census/COMMANDS.md` | `8d15f151c3670a8531da7d86fc487bb12d2108c5936f8004c7b6e4f3c6287c60` |
| the 19 `ir/**/*.ll` modules, sorted, `sha256sum` of their `sha256sum` lines | `067bb475bddda084562ce9e8714a996849af2b8cf1dacf05925129e32858047e` |

Instrument: `census.py` runs the driver on one function at a time; `peel2.py`
reads the refusal and relaxes exactly that construct in a scratch copy;
`strip.py` applies the capture strip list; `aggregate.py` prints the report.
Every run begins with the three controls (`json-scan.candidate.ll`,
`json-classify.candidate.ll`, `baseline.ll`), which must parse with an empty
capability list.

Commands, with the driver rebuilt *before* the run:

```sh
nix develop -c bash probes/install/lake-locked.sh build leanllvm
cd /tmp/scidonia-spike18
D=/home/gavin/dev/Scidonia/lean-llvm/.lake/build/bin/leanllvm
python3 census/census.py "$D" integrated O2 > /tmp/f2d-census/integrated.O2.after2.jsonl
python3 census/census.py "$D" integrated O3 > /tmp/f2d-census/integrated.O3.after2.jsonl
python3 census/census.py "$D" p5 O2 > /tmp/f2d-census/p5.O2.after2.jsonl
python3 census/census.py "$D" p5 O3 > /tmp/f2d-census/p5.O3.after2.jsonl
python3 census/aggregate.py census/control.jsonl \
  /tmp/f2d-census/integrated.O2.after2.jsonl \
  /tmp/f2d-census/integrated.O3.after2.jsonl \
  /tmp/f2d-census/p5.O2.after2.jsonl \
  /tmp/f2d-census/p5.O3.after2.jsonl > /tmp/f2d-census/report.after2.txt
```

Before/after comparison: `report.txt` is the same aggregation made before the
change; `report.after2.txt` is the fresh run.  A re-run with the rebuilt driver
was byte-identical to the first after-run (`diff -q` clean).

Units: the integrated universe has 41 **functions** and the p5 universe 58.
`aggregate.py` prints, per construct, functions whose peel chain needs that
construct ("one hit per function per construct"), plus a "first refusal" count
of functions whose first refusal is that construct.  Neither number counts
files or instructions.

| universe, flags | functions | pointer `icmp` construct hits, before → after | written callee type construct hits, before → after |
|---|---|---|---|
| integrated O2 | 41 | 21 → 0 | 17 → 0 |
| integrated O3 | 41 | 21 → 0 | 17 → 0 |
| p5 O2 | 58 | 18 → 0 | 0 → 0 |
| p5 O3 | 58 | 18 → 0 | 0 → 0 |

First-refusal counts over the same runs: integrated O2 and O3 go from 6 to 0
for pointer `icmp` and from 17 to 0 for the written callee type; p5 O2 and O3
go from 11 to 0 for pointer `icmp` and stay at 0 for the written callee type.
The parsed counts were unchanged **in that comparison**: integrated O2 4 of 41
parsed (37 blocked), integrated O3 3 of 41 parsed (38 blocked), p5 O2 1 of 58
parsed (57 blocked), p5 O3 1 of 58 parsed (57 blocked).  The functions those two
constructs blocked remained blocked by other constructs, so no parsed count moved
there.  This package's comparison, above, is a later one: it moves the integrated
parsed counts 4 → 8 and 3 → 7 and leaves p5 at 1 → 1.

Both reports contain zero `unclassified:` entries, and all 15 control lines
(three controls in each of the five aggregation inputs, counting
`control.jsonl`) report `parses=True caps=[]`.

Limit: this corpus reaches pointer `icmp` with `eq` and `ne` and reaches
written callee function types, which is what the two rows above measure.  It
does not reach a signed pointer predicate or a mixed pointer/integer
comparison; those are parser refusals with their evidence in
`LeanLLVMTest/Core.lean`.
