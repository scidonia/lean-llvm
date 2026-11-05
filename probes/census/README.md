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

Measured 2026-11-05 with the driver built from `7d679eb` plus this change
(binary `2026-11-05 12:33:28`, after `LeanLLVM/Semantics.lean` at `12:31:55`):

- **Tracked corpus: 22 files, 23 `define`s — 19 of the 22 files parse, 3 are
  refused.**  The refusals are `probes/install/ir/baseline.o1.ll` (return
  attribute `range`), and `probes/install/ir/baseline.raw.ll` and
  `probes/install/ir/candidate.raw.ll` (parameter attribute `noundef`).
- **Coverage of the two constructs this change adds: 0 of the 22 files contain
  an `icmp … ptr` line, and 0 contain a written callee function type.**  This
  corpus therefore does not exercise them; their evidence is
  `LeanLLVMTest/Core.lean`.
- **Working tree including generated IR: 41 files, 72 `define`s — 37 of the 41
  files parse, 4 are refused.**  The fourth refusal is
  `probes/app/build/app.ll`, refused at line 1 (`source_filename`), not at an
  instruction.  That file holds the tree's only `icmp … ptr` line, so the line
  itself is never reached.  The extra 19 files are untracked build output under
  `probes/*/build`, which is why `--all` reports without asserting: the
  checked manifest is the tracked set.

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
The parsed counts are unchanged: integrated O2 4 of 41 parsed (37 blocked),
integrated O3 3 of 41 parsed (38 blocked), p5 O2 1 of 58 parsed (57 blocked),
p5 O3 1 of 58 parsed (57 blocked).  The functions the two constructs blocked
remain blocked by other constructs, so no parsed count moves.

Both reports contain zero `unclassified:` entries, and all 15 control lines
(three controls in each of the five aggregation inputs, counting
`control.jsonl`) report `parses=True caps=[]`.

Limit: this corpus reaches pointer `icmp` with `eq` and `ne` and reaches
written callee function types, which is what the two rows above measure.  It
does not reach a signed pointer predicate or a mixed pointer/integer
comparison; those are parser refusals with their evidence in
`LeanLLVMTest/Core.lean`.
