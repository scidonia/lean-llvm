# The escape list and the escape expander, measured

The stage-1 escape list has two arms: the measured builder leaves a
`uint32_t` stream of escape positions when its per-document gate lets it build
one, and leaves nothing when the gate suppresses it.  The escape expander is the
list-driven decoder the stage-2 consumer calls.  This file records what those
two pieces of measured code do, per arm and per row, at a named revision, so
that a statement about them can be written from the measurement rather than
from a reading of the code.

Recorded at `7ac7b29`, Lean 4.35.0 and clang/LLVM 21.1.8 from the flake, with
the vendored set that `kernel/json/measured/SHA256SUMS` pins at that revision.
The scratch tree the headers were copied from is `/tmp/scidonia-spike45/src`; a
directory whose vendored files hash to those digests is the revision the
measurements below describe, and nothing here was measured against any other.

## The instruments

Two probes, both committed, each split into a translation unit that includes the
vendored measured text and a driver that holds an independently written
reference and the matrix:

|Pair|Actor|Reference|
|---|---|---|
|escape list|`probes/json/escape_measured.c`: `s1f_build_dispatch` from `kernel/json/measured/s1fuse.h` at the measured configuration, reading the list back through `s1f_esc_list`|`probes/json/escape_driver.c`: a byte scan written from the escape rule, plus a re-derivation of the gate's arithmetic from `dens.h`'s own thresholds|
|escape expander|`probes/json/unescape_measured.c`: `us_dec_x` from `kernel/json/measured/uj.c` + `usdec.h` at `-DUS_EMIT4=1`|`probes/json/unescape_driver.c`: a decoder written from the escape rule, keeping its own list cursor|

Neither driver includes a vendored header, so the two derivations do not share
text.  Both are built at the measured compiler line and configuration
(`build49.sh:17-21` in the scratch tree), from the repository root, because the
include and source paths are relative to it:

```sh
nix develop -c clang -O3 -march=x86-64-v3 -mpclmul -std=gnu11 \
  -falign-loops=64 -falign-functions=64 \
  -DSTAGE_PROBE -DS1F_ENT_PROBE=1 -DS1F_DENS=1 -DS1F_TWOPHASE=1 -DS1F_EXP2=11 \
  -DS1F_DISPATCH=1 -DS1F_UTF8=7 -DS1F_KL_DOC=1 -DPSTAGE=32 -DPMODE=2 \
  -DS1F_XS=5 -DS2_XP=1 -DS2_DEC_GATE=2 -DS1F_XS_DYN=1 \
  -I kernel/json/measured -c probes/json/escape_measured.c -o /tmp/probe.o
nix develop -c clang -O2 -DDENS_PLAIN_NUM=1 \
  -o /tmp/escape_matrix probes/json/escape_driver.c /tmp/probe.o
```

The driver's four modes print one transcript each:
`--measured` (the actor's rows), `--reference` (the reference's rows),
`--class` (`<source> <label> <re-derived class> <exhibited class>`), and
`--gate` (`<source> <label> <nb> <stride> <samples> <hits> <class>`, the gate's
own reading of each document).  `DENS_PLAIN_NUM` is taken from `dens.h` rather
than retyped, which is the value the measured translation unit sees.

The escape expander's matrix is one binary with no arguments; it prints its rows
and a per-group count, and exits nonzero if any row disagrees or if the row
total does not equal the sum of the group bounds.

```sh
nix develop -c clang -O3 -march=x86-64-v3 -mpclmul -std=gnu11 \
  -Wno-initializer-overrides -Wno-macro-redefined \
  -I kernel/json/measured -DUS_EMIT4=1 \
  probes/json/unescape_measured.c probes/json/unescape_driver.c \
  -o /tmp/unescape_matrix
```

Both measurements were taken against the pinned set and reproduce byte for byte:
`sha256sum -c kernel/json/measured/SHA256SUMS` reported 17 of 17 files OK
immediately before and immediately after the run, and a second run of all five
transcripts in the same session produced files identical to the first.

## The escape list, per arm

The corpus is `tests/json-escape/corpus.tsv`: **21 rows**, its own line count.
Each transcript has one line per row.  The columns below are the four
transcripts joined on the row's label: `n` is the document's length, `nb` its
number of whole 64-byte blocks, `samples`/`hits` the gate's counts over the
sampled blocks, `derived` the class the driver re-derives from the bytes,
`exhibited` the class the measured actor shows, and the last two columns the
emitted count and the reference's.

|Row|n|nb|samples|hits|derived|exhibited|emitted|reference|verdict|
|---|---|---|---|---|---|---|---|---|---|
|`empty`|0|0|0|0|`plain`|`plain`|0|0|agree|
|`short:backslash-n`|10|0|0|0|`plain`|`plain`|0|1|**differ**|
|`short:raw-control`|9|0|0|0|`plain`|`plain`|0|1|**differ**|
|`short:none`|2|0|0|0|`plain`|`plain`|0|0|agree|
|`plain:long-none`|208|3|3|0|`plain`|`plain`|0|0|agree|
|`plain:long-raw-control`|209|3|3|0|`plain`|`plain`|0|1|**differ**|
|`plain:upper-half-escape`|209|3|3|0|`plain`|`plain`|0|1|**differ**|
|`sparse:one-escape`|210|3|3|1|`listed`|`listed`|1|1|agree|
|`heavy:forty-escapes`|88|1|1|13|`listed`|`listed`|40|40|agree|
|`carry:run2@63`|67|1|1|1|`listed`|`listed`|2|2|agree|
|`carry:run3@63`|67|1|1|1|`listed`|`listed`|3|3|agree|
|`carry:run4@62`|68|1|1|1|`listed`|`listed`|3|3|agree|
|`carry:run1@63`|66|1|1|1|`listed`|`listed`|2|2|agree|
|`carry:run5@61`|68|1|1|1|`listed`|`listed`|4|4|agree|
|`carry:run6@60`|67|1|1|1|`listed`|`listed`|4|4|agree|
|`many:one-block`|65|1|1|16|`listed`|`listed`|20|20|agree|
|`outside:backslash`|4|0|0|0|`plain`|`plain`|0|0|agree|
|`escaped:quote`|12|0|0|0|`plain`|`plain`|0|1|**differ**|
|`escaped:control`|12|0|0|0|`plain`|`plain`|0|2|**differ**|
|`heavy:across-blocks`|128|2|2|18|`listed`|`listed`|40|40|agree|
|`tail:escape-at-63`|65|1|1|0|`plain`|`plain`|0|1|**differ**|

**The counts, each from the table.** 21 rows = **11 suppressed** (`exhibited
plain`) + **10 built** (`listed`).  **7 rows differ**, and they are exactly the
suppressed rows whose reference count is not zero: `short:backslash-n`,
`short:raw-control`, `plain:long-raw-control`, `plain:upper-half-escape`,
`escaped:quote`, `escaped:control`, `tail:escape-at-63`; the first in corpus
order is `short:backslash-n`.  The other **4** suppressed rows carry no
position: `empty`, `short:none`, `plain:long-none`, `outside:backslash`.  On the
**10** built rows the two derivations agree, count and position list alike: the
listed rows' position columns diff empty.

The per-document gate, read from the actor's own measurements rather than from
the class alone:

- **7 rows have fewer than one whole 64-byte block** (`nb = 0`), and the gate
  answers `PLAIN` before sampling anything (`dens.h:222`): `empty`,
  `short:backslash-n`, `short:raw-control`, `short:none`, `outside:backslash`,
  `escaped:quote`, `escaped:control`.
- **4 rows have blocks and are suppressed by the sample.**  `plain:long-none`
  has no escape at all (`hits = 0`).  The other three each carry an escape the
  rule names and the sample does not see, because each sampled block
  contributes only its **first 32 bytes** — the vector loaded at
  `dens.h:231` is the block's first 256 bits and the popcount at `:232-233`
  counts that vector's matches — and the threshold is
  `hits*64 < samples*DENS_PLAIN_NUM` (`:261-262`): `plain:long-raw-control`
  (control byte at 106, in the high half of block 1),
  `plain:upper-half-escape` (backslash at 106, same half), and
  `tail:escape-at-63` (backslash at 63, the high half of the only block).

So the gate is an **arm selector, not a presence classifier**: confronted with
7 documents that do carry escapes it leaves no list.  Across those 7 rows the
reference names 8 positions, of which 5 are escape-start backslashes
(`short:backslash-n` at 6, `plain:upper-half-escape` at 106, `escaped:quote` at
7, `escaped:control` at 7, `tail:escape-at-63` at 63) and 3 are raw control
bytes (`short:raw-control` at 6, `plain:long-raw-control` at 106,
`escaped:control` at 8).  No statement about the suppressed arm may therefore
say that the document has no escapes; the arm's own claim is only that the count
is zero and no position is claimed.

## What the built arm leaves

The list's contents for the 10 built rows, as the measured actor emitted them
and as the reference derived them (identical in each row):

|Row|count|positions|
|---|---|---|
|`sparse:one-escape`|1|70|
|`heavy:forty-escapes`|40|6 8 10 12 14 16 18 20 22 24 26 28 30 32 34 36 38 40 42 44 46 48 50 52 54 56 58 60 62 64 66 68 70 72 74 76 78 80 82 84|
|`carry:run1@63`|2|8 63|
|`carry:run2@63`|2|8 63|
|`carry:run3@63`|3|8 63 65|
|`carry:run4@62`|3|8 62 64|
|`carry:run5@61`|4|8 61 63 65|
|`carry:run6@60`|4|8 60 62 64|
|`many:one-block`|20|1 3 5 7 9 11 13 15 17 19 21 23 25 27 29 31 33 35 37 39|
|`heavy:across-blocks`|40|6 8 10 12 14 16 18 20 22 24 26 28 30 32 34 36 38 40 42 44 86 88 90 92 94 96 98 100 102 104 106 108 110 112 114 116 118 120 122 124|

The run rows are the ones that pin the rule's shape: a run of backslashes
contributes its **even-offset members**, since an odd-offset backslash in the
run is the one the previous escape consumed.  `carry:run3@63` is the three-byte
run at 63–65 and names 63 and 65 — offsets 0 and 2 — and never 64;
`carry:run4@62`, `carry:run5@61` and `carry:run6@60` do the same over runs of
four, five and six bytes.  `heavy:across-blocks` shows the list is one
document-order stream that spans blocks: its escapes at 40, 42 and 44 all lie in
block 0 and the stream continues at 86 in block 1, with no per-block re-start
and no entry for a boundary.

## The escape expander, counted matrix

53 rows in 10 groups, every row a body and the position list its own escapes
name, both sides run over the same pair:

|Group|Rows|What the rows are|
|---|---|---|
|`simple`|8|each of `\" \\ \/ \b \f \n \r \t`, as a two-byte body|
|`u-bmp`|11|`\uXXXX` at 0, 0x1F, 0x41, 0x7F, 0x80, 0x7FF, 0x800, 0xD7FF, 0xE000, 0xFFFD, 0xFFFF|
|`pair`|3|three surrogate pairs, twelve-byte bodies, two list entries each|
|`pair-edge`|4|lone high, lone low, high followed by `\u0041`, high followed by another high|
|`refused`|4|unknown letter, short `\u`, trailing backslash, bad hex|
|`control`|1|a raw `0x0A` at a position|
|`offset`|14|an escape at offsets 0–8 of a 16-byte body, and at 60–64 of an 80-byte body|
|`multi`|4|two escapes, simple + pair, pair + simple, two escapes 60 bytes apart|
|`carry`|3|`pos0 = 64` with entries below, inside and at the body's end|
|`empty`|1|an empty body with an empty list|

**0 rows differ**, and the total, 53, is asserted against
`8 + 11 + 3 + 4 + 4 + 1 + (9 + 5) + 4 + 3 + 1`.  The rows that carry the
statement's obligations:

- **A pair is one code point from twelve input bytes and two list entries.**
  `D83D+DE00` decodes to `f09f9880`, `D800+DC00` to `f0908080`, `DBFF+DFFF` to
  `f48fbfbf`; the decoder's list cursor advances past the pair's second entry
  in the same step, which both sides print and compare.
- **A lone surrogate is the three-byte form of its own code point**:
  `D800` decodes to `eda080`, `DC00` to `edb080`.  The model's string value is
  a list of code points, so this is the form the bridge to it has to state; a
  document carrying a lone surrogate does not fall outside the relation.
- **A high surrogate followed by a non-low is not a pair**: `\uD800\u0041`
  decodes to `eda08041`, the second escape decoded on its own, which shows the
  pair test is the low surrogate's range and not merely a following `\u`.
- **A refusal is at the escape's own offset, body-relative**: unknown letter 0,
  short `\u` 0, bad hex 0, trailing backslash 1, raw `0x0A` at 1.  The offset
  is the position the rule names, not the byte that failed the hex test.
- **The carry is part of the boundary, not an assumption**: with `pos0 = 64`,
  the entries below 64 are skipped, the entry at the body's end (72) stops the
  walk, and both sides' cursor indices agree on every row.

Two preconditions the matrix surfaced, both measured rather than read off:

- **The body needs 32 readable bytes past its end.**  The run copier on every
  path is `us_run` (`usdec.h:396-411`), whose first load at `:398` is a bare
  `_mm256_loadu_si256`, so its last short segment loads 32 bytes at `p + i` for
  `i` up to `n`; a body staged at exactly its `n` bytes is read past, and a row
  that broke this crashed in the copy rather than disagreeing.
- **The list must be the document's own escape positions.**  `us_dec_x` never
  range-tests a list entry against its input cursor: its loop computes the run
  length `b - i` with no `b < i` test (`usdec.h:879-880`), so a position that
  falls inside an escape the previous entry consumed underflows it.  A body
  `aaa\n` at `pos0 = 64` with the list `{67, 68}` leaves `i = 5` after the
  escape and then asks for `4 - 5 = 2^64 - 1` bytes, and the probe dies with
  `SIGSEGV` (exit 139).  This is specific to the list-driven entry, not a
  property of the file: the mask-driven kernels all carry the test —
  `usdec.h:709`, `:723`, `:757`, `:771` (`if ((uint64_t)b < cur) continue;`)
  and `:1094` (`if (b < i) continue; /* consumed by the previous */`) — so the
  two arms of the pipeline are **not** equally robust to a list that is not the
  document's positions.  The caller's side of the boundary therefore has to
  carry that promise; a statement that admits an arbitrary `uint32_t` array
  would be describing a call the measured code does not survive.

## What this does and does not cover

The escape list's route assertion — the clause-by-clause comparison, the two
controls and the staged cut — lives in `tests/json-escape/check.sh`; this file
records the measurement that assertion rests on and is not itself a gate.

Not claimed: any timing (no clock is read by either probe); any class for a
document outside the corpus; the pairing of a suppressed list with the
consumer's scan-driven decoder, which is the assembled pipeline's obligation and
not either unit's; and any behaviour of the alternate decoder arms
(`usdec_variants43.h`, `usdec_variants44.h`), whose headers are vendored and
compile but which the escape unit's statement does not use.
