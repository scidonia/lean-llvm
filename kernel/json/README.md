# The stage-1 classification mask unit

`s1_block.c` is the stage-1 classification kernel of the measured SIMD JSON
pipeline: given 64 bytes and the carry the previous block left, it produces the
block's unescaped-quote, structural (delimiter), in-string, whitespace,
backslash and control masks, and the carry the next block enters with.

It is **the mask unit, not the pipeline**.  Nothing here emits entry positions,
decodes UTF-8, builds or expands an escape list, or reads a value.  The measured
header it comes from (`measured/s1fuse.h`) carries all of those; `measured/` is
read-only reference, compiled by `identity/oracle.c` alone and by no build
target.

## The ABI

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

## Build

```bash
nix develop -c clang -O3 -march=x86-64-v3 -mpclmul -std=gnu11 \
  -falign-loops=64 -falign-functions=64 -I kernel/json -c kernel/json/s1_block.c
```

That is `build49.sh:17`'s compiler line, the one the measured build used.
`lake` does not build the kernel: it is a C unit of the identity, route and
bench scripts, not of the Lean library.

## What is measured text, and what is not

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
<!-- identity-list:end -->

The four deletions are the two conditional arms inside `s1f_masks`, resolved to
the measured build's values: `S1F_XS=5` (`build49.sh:21`) takes the arm that
keeps both the control and backslash words, and `S1F_CTAB` keeps its default
`1` (`measured/s1fuse.h:384-386`), which takes the table path.  The `#else`
arms are deleted; nothing else inside the seven entities is touched.

## The deletion list

Besides the four in-entity deletions above, the extraction leaves behind every
part of the measured header this unit is not.  That is what makes the unit a
unit; each row is a deletion, and a row marked *whole* is a site that is never
extracted at all.

|Site|Measured value|Deleted|
|---|---|---|
|`s1fuse.h:433-445` `#if S1F_XS`|`S1F_XS=5` (`build49.sh:21`) → on|the `#else` `(void)bm_o; (void)ctl_o;` arm (whole lines)|
|`s1fuse.h:446-455` `#if S1F_CTAB`|default `1` (`:384-386`) → table path|`s1f_structural` (`:370-377`) and the `#else` `cmpeq` chain (whole)|
|`s1fuse.h:112-155, 156-165` UTF-8 arms|`S1F_UTF8=7`, `S1F_KL_DOC=1`|the UTF-8 machinery and its includes (whole; M3's subject)|
|`s1fuse.h:249-343` `s1f_init`, `s1f_x_reserve`, `s1f_em_reserve`, `s1f_uk_*`|—|the buffers and per-process switches (whole)|
|`s1fuse.h:505-543` `s1f_ent_probe`|`S1F_ENT_PROBE=1` (`build49.sh:19`)|the probe, a decision instrument rather than a mask (whole)|
|`s1fuse.h:544-716` `s1f_emit` and its variants|—|the entry emitter (whole; M2's subject)|
|`s1fuse.h:1102-1333` expanders, kernel ids|—|M2's subject (whole)|
|`s1fuse.h:1614-1932` `s1f_build2`|—|the pipeline loop, the caller of this unit (whole)|
|`S1F_STATS`/`S1F_XS_STATS` blocks|off|the histograms (whole)|
|`SP_MODES`, `SP45_MODES`, `S1F_U8_MODES`, `DENS_PRINT`, `modes*.h`|off in `m49`|the per-process arm switches (whole)|
|`S1F`'s `prevS`, `bs_prevb`, `bs_prevs`|—|carry fields these masks do not touch (whole; M2/M4)|

The unit's own `S1F` is therefore three words, not six.  The measured code
computes exactly these six words into six local pointers and three `S1F` fields,
so this is a hoist of values, not a re-shaping of arithmetic.

## Limits

1. **It reads 64 bytes per block, unconditionally.**  The measured builder's
   `nb = (n + 63) / 64` (`s1fuse.h:1670`) means its last block reads past `n`,
   and the measured corpora are padded.  The contract is "64 bytes readable at
   `p`"; the tail policy is M2's (`lim` masking at `s1fuse.h:1721-1722`).
2. **The escape rule does not consult the string state.**  This is the kernel's
   rule, kept; it is stated where the specification states it.
3. **No alignment requirement, and the loads are this unit's.**  The wrapper
   loads unaligned, so the unit's callers may stage a block at any address with
   64 readable bytes; the route checks agreement at a misaligned address for
   that reason.
4. **No aliasing claim.**  The carry and output slots are separate objects the
   caller owns; nothing here states what happens if they overlap.

## The checks

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

