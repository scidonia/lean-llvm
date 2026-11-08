# The stage-1 units

Two units of the measured SIMD JSON pipeline live here, each a unit of the same
vendored header pair (`measured/s1fuse.h`, `measured/xlist.h`) with its own
public ABI, its own specification in `LeanLLVM/Vellum/`, and its own identity
arms and route:

- **`s1_block.c`**, the classification mask unit, and
- **`entry.c`**, the entry unit: a block's `ent` word to positions.

Neither is the pipeline.  Nothing here decodes UTF-8, builds or expands an
escape list, or reads a value; `measured/` is read-only reference, compiled by
the identity and bench scripts alone and by no `lake` target.  The two units
share the vendored files, the compiler line and the arms' machinery, and nothing
else: each has its own entity list, its own deletion list and its own boundary.

## The mask unit

`s1_block.c` is the stage-1 classification kernel: given 64 bytes and the carry
the previous block left, it produces the block's unescaped-quote, structural
(delimiter), in-string, whitespace, backslash and control masks, and the carry
the next block enters with.

### The ABI

```c
typedef struct { uint64_t esc_open, esc_ppar, im_carry; } s1_carry;
typedef struct { uint64_t quote, delim, in_string, ws, backslash, ctl; } s1_masks;

void leanllvm_json_s1_masks(const uint8_t *p, s1_carry *carry, s1_masks *out);
```

Byte offsets are fixed by the definitions: the carry at `+0/+8/+16`, the output
at `+0/+8/+16/+24/+32/+40`.  Six words cross the boundary, not seven: the
escape mask is the kernel's internal word and the escaped-quote mask is derived
as `quote_raw & ~quote` by the specification, not stored.

`s1f_masks` keeps its measured name, its measured parameter type `S1F *` and its
measured signature inside the translation unit; `S1F` is this unit's three-word
carry (`typedef s1_carry S1F;`), so the hoist moves values and not arithmetic.
The public wrapper is the only new function, and its two `_mm256_loadu_si256`
loads are new code: the measured loads live in `s1f_build2`, which is the
pipeline loop and not this unit.

### Build

```bash
nix develop -c clang -O3 -march=x86-64-v3 -mpclmul -std=gnu11 \
  -falign-loops=64 -falign-functions=64 -I kernel/json -c kernel/json/s1_block.c
```

That is `build49.sh:17`'s compiler line, the one the measured build used.
`lake` does not build the kernel: it is a C unit of the identity, route and
bench scripts, not of the Lean library.

### What is measured text, and what is not

Every function and table in `s1_block.c` except the wrapper is copied from
`measured/s1fuse.h` unchanged, including names, signatures, formatting and
comments.  `identity/source-identity.sh` extracts the entities below from the
vendored header, applies the deletion list, and diffs the tokens against the
same entities in `s1_block.c`; `identity/ir-identity.sh` compiles both sides and
compares the emitted code.

The list below is **data**: the script reads it, so an entity or a deletion that
is not recorded here shows up as a diff rather than being excused.

<!-- identity-list:begin -->
entities: s1f_prefix_xor s1f_escaped s1f_lo_tab s1f_hi_tab s1f_sw32 s1f_sm_ws s1f_masks
delete: 434
delete: 443-445
delete: 446
delete: 450-454
carry-fields-deleted: prevS bs_prevb bs_prevs
entry-entities: s1fuse:s1f_ke_pos8 s1fuse:s1f_ke_b8 s1fuse:S1F_DEFINE_KERNEL s1fuse:s1f_k_pos8 s1fuse:s1f_k_b8 xlist:xl_pos8 xlist:xl_pos8_init
entry-delete: xlist:34-38
entry-delete: xlist:49-52
entry-extra: leanllvm_json_entry_pos8 leanllvm_json_entry_b8 leanllvm_json_entry_table
entry-xl-exempt: xl_pos8 xl_pos8_init xl_pos8_ready
<!-- identity-list:end -->

The four deletions are the two conditional arms inside `s1f_masks`, resolved to
the measured build's values: `S1F_XS=5` (`build49.sh:21`) takes the arm that
keeps both the control and backslash words, and `S1F_CTAB` keeps its default
`1` (`measured/s1fuse.h:384-386`), which takes the table path.  The `#else`
arms are deleted; nothing else inside the seven entities is touched.

The block also carries the **entry unit's** lists, and the entry section below
reads them: `entry-entities:` names the seven entities `entry.c` copies, each
prefixed with the vendored file it comes from (`s1fuse` for the kernels and the
block-loop macro, `xlist` for the table and its initialiser); `entry-delete:`
names the lines dropped from them; `entry-extra:` names the definitions the unit
carries that are not measured text; and `entry-xl-exempt:` is the exact set of
`xl_` identifiers the unit's own text may name.

### The deletion list

Besides the four in-entity deletions above, the extraction leaves behind every
part of the measured header this unit is not.  That is what makes the unit a
unit; each row is a deletion, and a row marked *whole* is a site that is never
extracted at all.

|Site|Measured value|Deleted|
|---|---|---|
|`s1fuse.h:433-445` `#if S1F_XS`|`S1F_XS=5` (`build49.sh:21`) → on|the `#else` `(void)bm_o; (void)ctl_o;` arm (whole lines)|
|`s1fuse.h:446-455` `#if S1F_CTAB`|default `1` (`:384-386`) → table path|`s1f_structural` (`:370-377`) and the `#else` `cmpeq` chain (whole)|
|`s1fuse.h:112-155, 156-165` UTF-8 arms|`S1F_UTF8=7`, `S1F_KL_DOC=1`|the UTF-8 machinery and its includes (whole; the UTF-8 probe's subject, which is not a mask)|
|`s1fuse.h:249-343` `s1f_init`, `s1f_x_reserve`, `s1f_em_reserve`, `s1f_uk_*`|—|the buffers and per-process switches (whole)|
|`s1fuse.h:505-543` `s1f_ent_probe`|`S1F_ENT_PROBE=1` (`build49.sh:19`)|the probe, a decision instrument rather than a mask (whole)|
|`s1fuse.h:544-716` `s1f_emit` and its variants|—|the inline per-block emitter of `s1f_build` (whole; the entry unit extracts the two block kernels the selector dispatches to — `s1f_ke_pos8`/`s1f_ke_b8` below — and not this inline path)|
|`s1fuse.h:1102-1333` expanders, kernel ids|—|the escape expanders and the kernel selector (whole; the entry unit exports both emitters instead)|
|`s1fuse.h:1614-1932` `s1f_build2`|—|the pipeline loop, the caller of this unit (whole)|
|`S1F_STATS`/`S1F_XS_STATS` blocks|off|the histograms (whole)|
|`SP_MODES`, `SP45_MODES`, `S1F_U8_MODES`, `DENS_PRINT`, `modes*.h`|off in `m49`|the per-process arm switches (whole)|
|`S1F`'s `prevS`, `bs_prevb`, `bs_prevs`|—|carry fields these masks do not touch (whole; the entry and escape units)|

The unit's own `S1F` is therefore three words, not six.  The measured code
computes exactly these six words into six local pointers and three `S1F` fields,
so this is a hoist of values, not a re-shaping of arithmetic.

### Limits

1. **It reads 64 bytes per block, unconditionally.**  The measured builder's
   `nb = (n + 63) / 64` (`s1fuse.h:1670`) means its last block reads past `n`,
   and the measured corpora are padded.  The contract is "64 bytes readable at
   `p`"; the tail policy is the entry unit's (`lim` masking at
   `s1fuse.h:1721-1722`), where `LeanLLVM/Vellum/JsonEntryIR.lean`'s
   `entry_tail_eq` states it: a block's word masked with `limMask (n - b)` has
   exactly that block's positions below the document's end `n`.
2. **The escape rule does not consult the string state.**  This is the kernel's
   rule, kept; it is stated where the specification states it.
3. **No alignment requirement, and the loads are this unit's.**  The wrapper
   loads unaligned, so the unit's callers may stage a block at any address with
   64 readable bytes; the route checks agreement at a misaligned address for
   that reason.
4. **No aliasing claim.**  The carry and output slots are separate objects the
   caller owns; nothing here states what happens if they overlap.

## The entry unit

`entry.c` is the entry unit of the same measured pipeline: a block's `ent` word
becomes positions in a 32-bit stream.  The word itself is not computed here and
has no body here -- the measured header computes it inline in three places
(`s1f_ent_probe`, `s1f_build`, `s1f_build2`), and hoisting them would be new C
with no measured counterpart -- so this unit starts where the word ends and the
two emitters begin.

### The ABI

```c
uint64_t leanllvm_json_entry_pos8(const uint64_t *ent, uint64_t blk0,
                                  uint64_t nblk, uint32_t *out, uint64_t k);
uint64_t leanllvm_json_entry_b8  (const uint64_t *ent, uint64_t blk0,
                                  uint64_t nblk, uint32_t *out, uint64_t k);
void     leanllvm_json_entry_table(uint32_t *dst);   /* 256 x 8 i32, 8 KiB */
```

`ent` holds `nblk` mask words, lane 0 of `ent[0]` being byte 0 of block `blk0`;
the return value is the cursor after the last word the call appended, and the
`k' - k` words at `out[k .. k')` are the set lanes' positions in block and lane
order, each `64 * (blk0 + i) + lane` truncated to 32 bits.  `pos8` and `b8` are
two emitters of the same stream and either one's output is the other's.

These are the measured block loop's parameters, hoisted: `S1F_DEFINE_KERNEL`
already declares exactly `(uint64_t *ent, uint64_t blk0, uint64_t nblk,
uint32_t *out, uint64_t k) -> uint64_t`, so the wrappers' parameters are the
measured function's and the only new code is the `const` -- a qualifier, not an
instruction -- plus `leanllvm_json_entry_table`, which initialises the unit's own
table and copies 8 KiB of it into the caller's buffer.  There is deliberately no
count helper: a count is derivable from the masks, and a C popcount would be a
third route to the same number with no caller.

### Build

```bash
nix develop -c clang -O3 -march=x86-64-v3 -mpclmul -std=gnu11 \
  -falign-loops=64 -falign-functions=64 -I kernel/json -c kernel/json/entry.c
```

That is `build49.sh:17`'s compiler line, the one the measured build used.  The
unit reads no `-D` switch: the emitters sit inside `#if S1F_EXP2 == 11` in the
measured header, and the entity list takes the entities from inside that region.
The guard lines are outside every entity and so are not part of this unit's
text; a build that had to define `S1F_EXP2` to see them would be configuring the
unit rather than extracting it.

### What is measured text, and what is not

The table, its initialiser, the two kernels and the block-loop macro are copied
from `measured/xlist.h` and `measured/s1fuse.h` unchanged, including names,
signatures, formatting and comments; `identity/source-identity.sh --unit entry`
extracts the seven `entry-entities:` from those two files, applies the two
`entry-delete:` rows, and diffs the tokens against the same entities in
`entry.c`.  The reverse check is the same script's: every definition the unit
carries must be on the entity list or on `entry-extra:`, so a copy of a measured
function the list does not name is a diff and not an omission.

The two deletion rows are the `xl_pos8b` pair, an offset table and a fill loop
that only `xl_emit`'s offset form reads: `xlist:34-38` is the 64 KiB array with
its comment, and `xlist:49-52` is the two nested loops that populate it.  The
fill loop is inside `xl_pos8_init`, so the token diff sees it directly.  The
array is not inside any entity, so two other checks of the same run are what
make its absence a fault: the reverse check reports any definition the unit
carries that the list does not name (and `xl_pos8b` would be one), and the `xl_`
check requires the unit's own text to name exactly the `entry-xl-exempt:` set
(`xl_pos8`, `xl_pos8_init`, `xl_pos8_ready` -- the array, its initialiser and the
idempotence flag the initialiser reads), so a fourth `xl_` name is a setup
failure (exit 3) rather than an invisible pass.  `xl_pos8_ready` and the
initialiser's gate on it are kept, so a second `leanllvm_json_entry_table` call
is a load and a branch instead of an 8 KiB refill.

The `ent` word itself is not this unit's text and is not its body, but it is
not left unchecked either.  `identity/ent_oracle.c` holds the word's measured
statements — the three inline copies in the measured header are one text, and
that file is it — and `identity/ent-identity.sh --text-only` diffs those tokens
against each of the three vendored sites, with the `S1F_CTAB` arms resolved to
the measured table path and a control that rewrites one numeral.  The same
script's row half compares the oracle's `S`, `ent` and tail-masked `ent` against
the specification's word, row by row; it reads the specification route's
`--ent` mode, checks for it, and stops at its edge rather than loading a second
model of the word, so `ent-identity.sh` with no flags exits `3` until that mode
exists and `--text-only` is the half that runs here.

The new text is the three ABI functions.  Everything else in the measured
header is outside this unit and is not copied: the `ent` word's three inline
computations, the kernel selection (`s1f_ent_probe`, `dens_pick_kernel`,
`s1f_expand_k`) and its ids, the escape list and its expanders, `s1f_emit` and
the buffer management.  The unit exports *both* emitters instead of choosing
one, because the choice is a document-level decision and not this unit's.

### The deletion list

Besides the two in-entity rows above, the extraction leaves behind every part of
the measured header this unit is not.  Each row is a deletion, and a row marked
*whole* is a site that is never extracted at all.

|Site|Measured value|Deleted|
|---|---|---|
|`s1fuse.h:1235, 1352` `#if S1F_EXP2 == 11`|`S1F_EXP2=11` (`build49.sh:19`)|the `#if`/`#endif` lines (whole lines; the region stays)|
|`s1fuse.h:1265-1275` `s1f_ke_b2`|the `S1F_EXP2 == 11` region|the two-entry kernel (whole; not a measured selection)|
|`s1fuse.h:1278-1285` `s1f_ke_b4`|`SP45_MODES` only|the four-entry kernel (whole; no recorded cost)|
|`s1fuse.h:1318-1326` `SP45_MODES` instantiations|off in `m49`|the duplicate kernel instances (whole)|
|`s1fuse.h:1329-1333` `S1F_K_*` kernel ids|`SP45_MODES` only|the id macros (whole; the selection is the caller's)|
|`s1fuse.h:1335-1351, 1354-1562` `s1f_expand_k`, `s1f_expand`|`S1F_EXP2` arms|the selector and dispatcher (whole)|
|`s1fuse.h:1133-1166, 1168-1192, 1195-1232` `S1F_POS8`, `S1F_P8_ONE`, the escape expanders|`s1f_build`'s inline emit and `S1F_EXP2` arms|the two macros and the three functions (whole; the escape list is the unescaper's subject)|
|`s1fuse.h:544-716` `s1f_emit` and its variants|—|the inline emitter of `s1f_build` (whole; not the two-phase path)|
|`s1fuse.h:1115-1123` `s1f_ent_reserve`|—|the buffer management (whole; this unit writes into a caller's buffer)|
|`s1fuse.h:505-543, 873-894, 1706-1722` the three `ent` sites|—|not extracted: no measured function computes `ent` alone, so the word is specified and its statements are copied by `identity/ent_oracle.c`|
|`xlist.h:34-38` `xl_pos8b`|read only by `xl_emit`'s offset form|the 64 KiB array and its comment (whole)|
|`xlist.h:49-52` `xl_pos8b`'s fill loop|inside `xl_pos8_init`|the two nested loops (whole; `xl_pos8_ready` and its gate are kept)|

### Limits

1. **The position stream is 32-bit.**  The block base is
   `(uint32_t)((blk0 + i) << 6)` inside `S1F_DEFINE_KERNEL`, so a document at or
   above 2^32 bytes truncates; the specification states its clauses at the
   truncated value and its untruncated corollary under the bound that rules the
   truncation out.
2. **The two emitters write different spans past the emitted count.**  `pos8`'s
   eight stores are unconditional and the cursor advances by each group's
   popcount, so a trailing group whose byte is empty still stores eight lanes at
   the final cursor: its last written lane is `k' + 7`.  `b8` writes eight slots
   for a block of one to seven entries and exactly its count above that, so its
   last written lane is `k' + 6`.  The first lane neither writes is `k' + 8`.
   Those lanes are the caller's: a buffer must carry eight words of slack past
   the largest count its input can reach, and a reader reads only `k'` words.
3. **`__builtin_ctzll` on a cleared word is undefined in C**, and the emission
   carries `llvm.cttz.i64` with its poison flag set (`i1 true`) for that reason.
   The model has no poison: the flag is admitted with a bound, and the bound is
   the overshoot region of limit 2, which no clause of the specification and no
   arm of the route reads.
4. **The table read is an aligned 32-byte load of a 32-byte-aligned array.**
   The model has no alignment and addresses bytes, so the specification's
   hypothesis is byte-readability of the row's 32 bytes; the object reads its
   own array at the address the C gives it.
5. **No aliasing claim.**  `ent`, `out` and the table are disjoint objects the
   caller owns; nothing here states what happens if they overlap.
6. **The selector is not here.**  Both emitters are exported and neither is
   chosen; which one a document gets is the caller's decision.
7. **It does not truncate at the document's end.**  A block's word is emitted
   whole; the last block's is masked by the caller — `lim = n - (bi << 6)` and
   `ent &= (1ULL << lim) - 1ULL` at `s1fuse.h:1721-1722` — and
   `LeanLLVM/Vellum/JsonEntryIR.lean`'s `entry_tail_eq` states what that leaves:
   the block's positions below the document's end, and nothing above it.  The
   buffer the caller provides is the caller's to size (limit 2).

## The checks

```bash
nix develop -c bash kernel/json/identity/source-identity.sh             # mask unit: tokens + mutation control
nix develop -c bash kernel/json/identity/source-identity.sh --arms-only # C1: the TU and the arm detector
nix develop -c bash kernel/json/identity/source-identity.sh --vendor    # pinned digests + live diff
nix develop -c bash kernel/json/identity/source-identity.sh --preprocess # mask unit: macro-set invariance
nix develop -c bash kernel/json/identity/ir-identity.sh                # mask unit: emitted-code identity + controls
nix develop -c bash kernel/json/identity/ir-identity.sh --unit entry   # entry unit: emitted-code identity + controls
nix develop -c bash kernel/json/identity/source-identity.sh --unit entry # entry unit: tokens + two controls
nix develop -c bash kernel/json/identity/source-identity.sh --unit entry --arms-only # entry unit: the TU, the
                                                                       # detectors and the public symbols
nix develop -c bash kernel/json/identity/ent-identity.sh --text-only   # the ent word's statements
nix develop -c bash kernel/json/identity/inventory.sh                  # the fixture's inventory gate
nix develop -c bash kernel/json/bench/paired.sh                        # mask unit: paired timing
nix develop -c bash kernel/json/bench/paired.sh --unit entry           # entry unit: paired timing, both kernels
nix develop -c bash kernel/json/identity/final-identity.sh entry       # the entry unit's three arms, one command
```

`final-identity.sh <unit>` is the dispatcher: it runs the unit's token identity,
its IR identity and its paired timing arm in that order, and exits `3` naming
the missing piece for a unit it does not implement.  Add `--tree-only` to either
identity script to refuse any input path outside this repository, so the claim
reproduces from a checkout with the scratch tree gone.  Under it, `--vendor`
refuses while the scratch tree exists, because the live diff is the one thing
that asks to read outside.

Two properties of the instruments are worth knowing when reading their output:

- `ir-identity.sh` compares emitted code.  "Identical IR" means the instruction
  text — every opcode, operand, type, constant and branch edge.  Analysis
  metadata is excluded only where that text is identical *and* the metadata
  difference has a cause named in the output: in the mask unit the TBAA
  struct-path node's field count, 6 → 3, which follows the enumerated deletion
  of `prevS`, `bs_prevb` and `bs_prevs` (the `carry-fields-deleted` line above).
  The entry unit claims **no** exclusion: its two lifted modules are the same
  node graph whose node numbers differ because each side was serialised from a
  different source module, so the sections are compared as a canonical graph --
  every node's text with its references replaced by the referenced node's
  canonical text, the `distinct` loop node's self-reference included -- and the
  node count is printed beside it.  A metadata difference with no nameable cause
  is a finding and fails the arm.
- `paired.sh` places both probes on 4 KiB boundaries.  The two bodies are the
  same machine code, but identical code at different addresses can run at
  different speeds on a core whose caches map by address; without the alignment
  the harness reports the address as well as the code, and it did so by 1.2
  ns/block on one core and one input.  The entry unit's bench aligns every
  function to 4 KiB as well -- its kernels are measured text and cannot carry
  the attribute -- and asserts the probes' page alignment and the kernels'
  shared page offset with `nm`.  It prints each arm's size and the random arm's
  seed with the result, so the sample it timed is reproducible from the output
  alone; the arms are the shapes that discriminate a wrong body: the 64
  single-lane masks, the 256 group-value masks (every table row), the empty and
  full masks, a 1,025-block stream, and the first 4,096 masks of the fixed-seed
  stream.

```bash
nix develop -c bash kernel/json/identity/source-identity.sh            # tokens + mutation control
nix develop -c bash kernel/json/identity/source-identity.sh --arms-only # C1: the TU and the arm detector
nix develop -c bash kernel/json/identity/source-identity.sh --vendor    # pinned digests + live diff
nix develop -c bash kernel/json/identity/source-identity.sh --preprocess # macro-set invariance
nix develop -c bash kernel/json/identity/ir-identity.sh                # emitted-code identity + controls
nix develop -c bash kernel/json/identity/inventory.sh                  # the fixture's inventory gate
nix develop -c bash kernel/json/bench/paired.sh                        # paired timing, both arms
```

Add `--tree-only` to either identity script to refuse any input path outside
this repository, so the claim reproduces from a checkout with the scratch tree
gone.  Under it, `--vendor` refuses while the scratch tree exists, because the
live diff is the one thing that asks to read outside.

Two properties of the instruments are worth knowing when reading their output:

- `ir-identity.sh` compares emitted code.  "Identical IR" means the instruction
  text — every opcode, operand, type, constant and branch edge.  Analysis
  metadata is excluded only where that text is identical *and* the metadata
  difference has a cause named in the output: here the TBAA struct-path node's
  field count, 6 → 3, which follows the enumerated deletion of `prevS`,
  `bs_prevb` and `bs_prevs` (the `carry-fields-deleted` line above).  A metadata
  difference with no nameable cause is a finding and fails the arm.
- `paired.sh` places both probes on 4 KiB boundaries.  The two bodies are the
  same machine code, but identical code at different addresses can run at
  different speeds on a core whose caches map by address; without the alignment
  the harness reports the address as well as the code, and it did so by 1.2
  ns/block on one core and one input.

`inventory.sh` reads `probes/install/ir/capture-s1-masks.sh` and the four
artefacts that capture derives from this unit: the fixture
`json-s1-masks.candidate.ll` and its three inventories — `.strip.tsv` (what the
normalisation removed, by class), `.rewrites.tsv` (what it rewrote, with its
reason) and `.inventory` (the fixture's opcodes and call targets).  On this tree
it exits `0`: the fixture regenerates byte-identically from `s1_block.c` at the
pinned flags, all three inventories byte-equal their committed copies, the
fixture parses, and both controls fire.  It exits `3`, naming the missing or
differing item, for anything else — a missing input or a non-regenerating
artefact is an unusable input, not a verdict about this unit.

The entry unit's inventory gate is its own capture's: `--unit entry` names
`probes/install/ir/capture-entry.sh` and exits `3` while that capture does not
exist, because the classes that gate checks -- the strip classes, the rewrite
classes, and the table-rewrite class the entry fixture's GEPs become -- are the
capture's formats, and a list kept in the gate would be the hand-kept list this
gate exists to avoid.  An invocation with no `--unit` is the mask unit's,
unchanged.

