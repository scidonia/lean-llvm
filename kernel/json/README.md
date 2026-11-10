# The stage-1 units

Two units of the measured SIMD JSON pipeline are extracted here, each a unit of
the same vendored measured set (`measured/`) with its own public ABI, its own
specification and identity arms, and its own boundary, and the extraction of a
third is what this directory's lists and arms are ready for:

- **`s1_block.c`**, the classification mask unit,
- **`entry.c`**, the entry unit: a block's `ent` word to positions, and
- **the UTF-8 validity unit**, the stage that decides whether the bytes scanned
  so far form valid UTF-8, whose unit is `kernel/json/utf8.c`.

None is the pipeline.  Nothing here decodes UTF-8 into text, builds or expands
an escape list, or reads a value: the UTF-8 unit returns a validity word and no
positions.  `measured/` is read-only reference, compiled by the identity, bench and route
scripts and by no `lake` target.  The units share the vendored
files, the compiler line and the arms' machinery, and nothing else: each has its
own entity list, its own deletion list and its own boundary.

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
utf8-entities: u8kl:kl_t1 u8kl:kl_t2 u8kl:kl_t3 u8kl:kl_err32_ld u8kl:kl_err_vec_ld u8kl:kl_tail_byte
utf8-stage: s1fuse:1833-1841
utf8-stage-tail: s1fuse:1911-1912
utf8-stage-copy: s1fuse:997-1005 s1fuse:1070-1071
utf8-stage-unit: utf8.c
utf8-stage-begin: /* begin: copied stage statements */
utf8-stage-end: /* end: copied stage statements */
utf8-rename: s1f_u8_ungated ungated
utf8-extra: leanllvm_json_utf8
utf8-permutation: KLCARRY kl_carry_init kl_err32 kl_err_vec kl_block_vec kl_block kl_block_ld kl_carry_prefix
escape-entities: xlist:xl_lanes xlist:xl_batch xlist:xl_emit_batch xlist:xl_emit usdec:US_FAIL usdec:us_hex4_pshufb usdec:us_hex4 usdec:us_emit usdec:us_esc_u usdec:us_esc usdec:us_run usdec:us_run_long usdec:us_dec_x uj:UJ_UNESC uj:uj_enc_word
escape-delete: xlist:301 xlist:303-313 xlist:315 usdec:288 usdec:293-304 usdec:334-375 usdec:387 usdec:399-403 usdec:407-410 usdec:275 usdec:277-279 usdec:862-868 usdec:876-878 usdec:879 usdec:881 usdec:883-885 usdec:891-893 usdec:898 usdec:906 usdec:909 usdec:911 usdec:913
escape-extra: leanllvm_json_escape_list leanllvm_json_escape_expand
stage2-entities: s2port:S2_VAL s2port:S2_STR s2port:S2_EV s2port:s2_init s2port:s2_value_pos s2port:s2_after_value s2port:s2_string_touch s2port:s2_walk p16:IXP@106 p16:NUMF_SLOW p16:num_fast p16:od_fail p16:touch_bytes p16:touch_u64 p16:od_gap_recover p16:od_scalar_value p6:PRIME p6:err_set p6:out_init p6:hup p6:out_raw p6:out_tag p6:out_u64 p6:dbits p6:is_ws p6:lit_check p6:num_scan p6:MAXD strz:z_init numf1:NUMF_SIMD numf1:NUMF_EL1_POW10 numf1:NUMF_EL1_P10 numf1:num_d8_el1 numf1:num_fast_el1@60 numel_el:EL_ENTRY@61 numel_el:EL_MASK numel_el:EL_HALF numel_el:el_pack numel_el:el_exact numel_el:num_el_el1 epow:EPOW epow:EPOW_MIN epow:EPOW_MAX usdec:US_SLACK
stage2-delete: s2port:438 s2port:442 s2port:444-488 s2port:494-521 s2port:580 s2port:582 s2port:608 s2port:611-614 s2port:650-652 s2port:654 s2port:701
stage2-extra: leanllvm_json_stage2 s2_string_body z_arena_reserve out_reserve p6:to_double
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

The `utf8-` rows are the **UTF-8 unit's**, and the UTF-8 section below reads
them:

- `utf8-entities:` names the six definitions `utf8.c` copies from `u8kl.h`;
- `utf8-stage:` and `utf8-stage-tail:` are **line ranges** of the vendored
  header — the statements `S1F_KL_DOC` selects inside `s1f_build2`'s block loop,
  and the reduce and tail statements it runs after the loop. Each is a
  `<source>:<first>-<last>` span. `utf8-stage-copy:` is the same two spans in
  `s1f_build`, the builder the measured configuration does not select; the token
  arm compares it with `utf8-stage:` + `utf8-stage-tail:`, which is what makes
  choosing one copy harmless. The script concatenates `utf8-stage:` and then
  `utf8-stage-tail:`, in that fixed key order, so that pair is the measured
  side of the comparison; the order of the *list* is not load-bearing, while the
  order of the spans **within one row** is: swapping the two spans of
  `utf8-stage-copy:` changes the concatenation;
- `utf8-stage-unit:` names the unit file, `utf8-stage-begin:` and
  `utf8-stage-end:` the two marker comments that delimit the unit's copy of the
  stage inside it;
- `utf8-rename:` is the one renamed token, `<measured> <unit>` — the
  document-level static becomes the function's parameter — and a row whose
  measured name is absent from the measured text is a setup fault, so a dead
  rename cannot pass;
- `utf8-extra:` names the definition the unit carries that is not measured text;
- `utf8-permutation:` names the `u8kl.h` definitions the measured build does
  not select. Together with `utf8-entities:` it is the complete `kl_` name set
  of the vendored header, so a seventh name is a setup fault rather than an
  unlisted copy.

The stage form is a range on both sides because these statements have no name
to locate them by: the measured side is pinned by line, which is safe only
because the file is pinned by digest, and the unit side is pinned by markers,
because a line locator inside a file this repository owns would break on every
unrelated insertion.  Both sides are required to be non-empty and to have a
non-empty normalisation: a comparison that reports `identical (0 token bytes)`
for two empty extractions is not evidence of anything, and a range clipped to a
preprocessor directive alone normalises to nothing for exactly that reason.

### The deletion list

Besides the four in-entity deletions above, the extraction leaves behind every
part of the measured header this unit is not.  That is what makes the unit a
unit; each row is a deletion, and a row marked *whole* is a site that is never
extracted at all.

|Site|Measured value|Deleted|
|---|---|---|
|`s1fuse.h:433-445` `#if S1F_XS`|`S1F_XS=5` (`build49.sh:21`) → on|the `#else` `(void)bm_o; (void)ctl_o;` arm (whole lines)|
|`s1fuse.h:446-455` `#if S1F_CTAB`|default `1` (`:384-386`) → table path|`s1f_structural` (`:370-377`) and the `#else` `cmpeq` chain (whole)|
|`s1fuse.h:112-165, 715-803` UTF-8 arms|`S1F_UTF8=7`, `S1F_KL_DOC=1`|the UTF-8 machinery and its includes (whole).  It has **two** sites, not one: the includes and the gates at `:112-165` and the mask-derived probe `s1f_uge`/`s1f_uchunk`/`s1f_uchunk_x`/`s1f_pend` at `:715-803` — the `S1F_UTF8=1..6` path, refuted in `docs/json-pipeline-performance.md:152` at +8.1/+7.3 ns/block|
|`s1fuse.h:1832-1842, 1908-1918` the `S1F_KL_DOC` stage of `s1f_build2`|`S1F_KL_DOC=1`|the UTF-8 unit's stage statements (whole here — not a mask; that unit extracts them by line range)|
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
   exactly that block's positions below the document's end `n`.  The UTF-8 unit
   has a document-end rule of its own and it is a different one — its last block
   is scanned whole, and the end is the DFA's zero padding plus `kl_tail_byte`
   (below) — so the two tails are not one rule stated twice.
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

## The UTF-8 unit

The UTF-8 unit is the stage-1 UTF-8 validity stage: the Keiser–Lemire
`pshufb` table DFA the measured builder runs in its block loop, and the
document-end rule it applies after the loop.  The stage is not a measured
function — it is statements inside the block loop of `s1f_build2`
(`measured/s1fuse.h:1614`), which `S1F_TWOPHASE=1` selects — so the table DFA's
definitions and the stage's statements are copied from two places, and the
identity arms compare both.  The stage's unit is `kernel/json/utf8.c`, extracted
with the stage's corpus: the entity list, the stage rows and the arms below are
what that extraction must satisfy, and they are checked once it exists.

### The ABI

```c
uint64_t leanllvm_json_utf8(const uint8_t *b, uint64_t n, int ungated);
```

The measured statements' own types, hoisted: the document-level static the stage
reads per document becomes the `int` parameter `ungated`, and the word the stage
writes to `*uerr` becomes the return.  A document is valid exactly when the
returned word is zero, and the verdict does not depend on `ungated` — which of
the two gate paths a document takes is decided by the caller.

Three obligations on the caller, each of them measured rather than conventional:

1. **`3 <= b`, and `b-3 .. b-1` read as zero.**  The DFA's state crosses the
   buffer start: with `F0 90 80` staged there, a document beginning `80` flips
   from reject to accept.
2. **`n` is the document's length and `b .. b+n-1` is the document.**
3. **`b+n .. b+64*ceil(n/64)-1` is readable and zero.**  Those bytes are inside
   the scanned window and the verdict depends on them; a non-zero padding byte
   can suppress a rejection.

And one length bound, also the caller's: **`n < 2^63`**.  The body's
`(n + 63)` wraps above it, and `n` is itself an index in the tail's read of
`b[n-1]`.

### Build

The unit's build is `build49.sh:17`'s compiler line, the one the measured build
used, with `-I kernel/json`; `lake` does not build it, because it is a C unit of
the identity, route and bench scripts and not of the Lean library.  The unit
includes `<immintrin.h>`, `<stdint.h>` and `utf8.h` and nothing else: the
vendored headers are the source of record, not this unit's includes.

### What is measured text, and what is not

The six definitions `utf8-entities:` names in `u8kl.h` and the stage statements of
`measured/s1fuse.h:1833-1841, 1911-1912` are copied unchanged, including names,
formatting and comments.  The statements have no name, so the identity list
names them by **line range** on the measured side — safe only because that file
is pinned by digest — and by a **marker pair** inside `utf8.c`,
`/* begin: copied stage statements */` and `/* end: copied stage statements */`,
one pair per measured range.
`identity/source-identity.sh --unit utf8` diffs the tokens of each entity and of
the stage, concatenating `utf8-stage:`'s ranges and then `utf8-stage-tail:`'s —
the order the comparison reads them in — and concatenating every pair inside the
unit in file order.  The pair count must equal the range count, so a unit that
lost a pair is a setup fault rather than a comparison against a prefix.  The
comparison also requires **both** sides of the stage to be non-empty with a
non-empty normalisation; an empty extraction is a setup fault, never an
equality.

One token is **renamed**, and it is a recorded row rather than a silent edit:
`s1f_u8_ungated` becomes `ungated`, because the document-level static becomes
the parameter.  The new text is the function header with its five declarations
(`nb`, `prev_ascii`, `high`, `u8k`, `err`), the loop header with `p`, `v0` and
`v1`, and the `return err`; `utf8-extra:` names its one definition, so the
reverse check accepts it.  A second check compares the two measured copies of
the stage — `s1f_build2`'s, which is the source of record, and `s1f_build`'s,
which the measured configuration does not select — token for token, which is
what makes choosing one of them harmless.

### The deletion list

Besides the six entities, the extraction leaves behind every part of the
measured header and of `u8kl.h` this unit is not.  Each row is a deletion, and a
row marked *whole* is a site that is never extracted at all.

|Site|Measured value|Deleted|
|---|---|---|
|`u8kl.h:57-160` the permutation form|not selected at `S1F_UTF8=7`|`KLCARRY`, `kl_carry_init`, `kl_err32`, `kl_err_vec`, `kl_block_vec`, `kl_block`, `kl_block_ld`, `kl_carry_prefix` (whole; the measured call sites are `kl_err_vec_ld` twice and `kl_tail_byte` once)|
|`s1fuse.h:715-803` `s1f_uge`, `s1f_uchunk`, `s1f_uchunk_x`, `s1f_pend`|`#if S1F_UTF8`, the mask-derived probe|whole|
|`s1fuse.h:117` the `u8fold.h` include|`S1F_UTF8=3..6`|whole, and `u8fold.h` is not vendored|
|`s1fuse.h:134-165` `s1f_u8_decide` and the `S1F_KL_DOC` guards|`S1F_KL_DOC=1`|whole; the selection is the caller's|
|`s1fuse.h:239-263` `s1f_u8_fold`, `s1f_u8_kl` and their environment reads|`S1F_UTF8 == 4`, `S1F_UTF8 == 8`|whole|
|`s1fuse.h:153-163` `s1f_u8_mode`, `S1F_U8_MODES`|off in `m49`|whole|
|`s1fuse.h:806-1091` `s1f_build`, and `:944-1077` its UTF-8 stage copy|not selected (`S1F_TWOPHASE=1`)|whole; its stage text is asserted token-identical to `s1f_build2`'s|
|`s1fuse.h:1782-1831` the `S1F_UTF8` 3, 4, 5 and 6 branches|`S1F_UTF8=7`|whole|
|`s1fuse.h:1842-1851` the `#elif S1F_KL_GATE` arm|`S1F_KL_DOC=1`|whole, and it is why the stage range ends at `:1841`|
|`s1fuse.h:1853-1894` the `S1F_UTF8` 8 and 2 branches|`S1F_UTF8=7`|whole|

The `kl_` identifiers the vendored header carries are therefore exactly the six
entities plus the eight permutation-form names, and the token arm asserts that
set: a seventh `kl_` name is a setup fault, because it would be a definition
both lists miss.  For the same reason this unit's arm detector is its own — the
unit is the UTF-8 machinery, so `kl_` is its subject and not a measurement arm
to be refused, while `dens_`, `S1F_`, `SP_` and `sp_` stay refused.

### Limits

1. **The tail is asymmetric, and it is measured.**  With `n % 64 != 0` the zero
   padding supplies the position after the last document byte, so a truncated
   final character is rejected; with `n % 64 = 0` that position does not exist,
   so a truncated `C2-F4` tail is accepted, while `C0`/`C1`/`F5-FF` is still
   rejected by `kl_tail_byte`.  The document-level rule for the truncation is
   finalisation's, and the narrowing matters: `ScanBlocks.tailRun_ended` proves
   the **model's** finalisation rule and not the measured stage 2's, so what
   this unit's arms establish is that the rule is not this stage's; the proof
   that the pipeline's finalisation refuses it is a later stage's.
2. **The verdict is about the staged window, not about `b .. b+n-1`.**  Three
   bytes before the document and up to 63 after it are read and are part of the
   condition; a document staged at the end of a buffer that is not zero-filled
   gets a different verdict if it starts with a continuation byte.
3. **It reads `64*ceil(n/64) + 3` bytes and nothing else.**  For `n = 0` it
   reads nothing at all: the loop does not run and the tail is guarded by
   `n != 0`.
4. **The word is 0 or 1**, and the emission's own `range(i64 0, 2)` says so.  It
   is not a position: the stage reports that the document is invalid, not where,
   and the offsets belong to the pipeline's stage 2.
5. **No alignment requirement and no aliasing claim.**  The loads are unaligned,
   the model addresses bytes, and the caller owns the buffer; nothing here
   states what happens if it overlaps anything.
6. **The selection is not here.**  The unit is defined for both values of
   `ungated` and the verdict does not depend on which was chosen.
7. **The tables are read, not derived.**  `u8kl.h`'s comment records that they
   were verified exhaustively against a scalar reference; this unit reads them
   as they are, and the identity arms pin them by digest and by name rather than
   re-deriving the constants.

## The escape unit

The escape unit is two measured stages under one ABI: the stage-1 escape-position
list — the block's control and escape-start positions, appended to the caller's
`uint32_t` stream — and the stage-2 list-driven expander, the decoder a string
body is run through with the document's position list.  The list is
`xlist.h`'s `xl_lanes` and `xl_emit` at `XL_EMIT=1` (`s1fuse.h:70-71`, selected
by `S1F_XS=5`); the expander is `usdec.h`'s `us_dec_x` at `US_EMIT4=1`, with
`UJ_UNESC` and `uj_enc_word` from `uj.c`.  The unit is `kernel/json/escape.c`,
and the identity arms compare every copied definition.

### The ABI

```c
void leanllvm_json_escape_list(uint64_t bs, uint64_t ctl, uint64_t im,
                               uint64_t blk0, uint32_t *xp,
                               uint64_t *xn, uint64_t *carry);
uint64_t leanllvm_json_escape_expand(const uint8_t *b, uint64_t n, uint8_t *dst,
                                     uint64_t *err, const uint32_t *xp,
                                     uint64_t *xj, uint64_t nxp, uint64_t pos0);
```

The list takes the classifier's **three words**, not bytes: lane `t` of `bs`,
`ctl` and `im` is document byte `64 * blk0 + t`.  That is why the unit does not
copy `s1f_masks`: the mask unit produces those words and this unit consumes them.
`carry[0]`/`carry[1]` are the previous block's last-byte backslash and its
escape-start flag, zero at the document's first block, updated from this block,
so a caller walking blocks threads the pair through.  `*xn` is the stream's
count in and out, and the buffer needs **`*xn + 64 + 8` writable entries**: one
block cannot hold more than 64 positions, and the measured eight-entry batch
writes its slots past the true count.  Only `*xn` entries are the stream.

The expander keeps `us_dec_x`'s measured eight-parameter signature and return.
`b .. b+n-1` is the body, `pos0` its document offset, `*xj` the list cursor, and
the return is the decoded length or `~0ULL` with `*err` the body-relative
refusal offset.

### The caller's obligations

Each is the measurement's, not the ABI's convenience:

1. **The expander's `xp` is exactly this body's escape positions**, not a
   `uint32_t` array of that capacity.  `us_dec_x` never tests a position against
   its input cursor (`usdec.h:880` computes `b - i` with no `b < i` guard, while
   the scan-driven kernels have one at `:709`, `:723`, `:757`, `:771`, `:1094`),
   so a position inside an escape the previous one consumed underflows the run
   length and the copy faults.  A caller that took the list from
   `leanllvm_json_escape_list` has this by construction.
2. **`b + n .. b + n + 31` is readable.**  `us_run`'s first load
   (`usdec.h:398`) is unconditional on every path.
3. **`dst` needs 64 writable bytes past the decoded extent; the measured form
   writes at most 32.**  `us_run` stores one 32-byte vector unconditionally and
   a second at `dst + 32 .. dst + 63` when `US_W == 64` and its arm takes it
   (`usdec.h:398-410`).  The measured `US_RUN2=0` form takes the second only
   for a run longer than 32 bytes, so its farthest write past the decoded
   extent is 32 — the unconditional first store on a zero-length copy — and 31
   for a non-empty run of at most 32.  The ABI asks for 64 because that is the
   whole extent the pinned function can write; the `US_RUN2=1` form stores the
   second vector unconditionally.  The vendored comment at `:390-392` ("up to
   31 bytes past the run") is therefore accurate for a non-empty run in the
   measured form and understates the empty copy and the unselected form.  The
   pinned bytes are not edited.
4. `*xj <= nxp`, `pos0 + n` does not wrap, and `dst` does not overlap `b` or
   `xp`.  The list's position base is `(uint32_t)(blk0 << 6)`, so a document at
   or above 2^32 bytes truncates; the entry stream has the same width limit.

### What is measured text, and what is not

The fifteen definitions `escape-entities:` names are copied unchanged from
`xlist.h`, `usdec.h` and `uj.c`, with the arms the measured configuration does
not take deleted by line, as `escape-delete:` records: the `xl_emit` batch's
other shapes, the `us_emit` encoder arms, the branch-free `us_esc` arm, the
`US_RUN2` and non-64 window forms of `us_run`, the scalar hex reader, and
`us_dec_x`'s diagnostic and trace arms.  Every copied entity has a name, so there
is **no stage row** for this unit: the stage form exists for measured statements
that have no name to locate them by, and nothing here is one.

The only new text is the two ABI functions, the `US_XP_DIAG` default the
decoder's kept guard reads, the two attribute selectors the deleted conditional
blocks left outside the extracted spans (`us_esc_u`'s inline form and
`us_dec_x`'s `noinline`), and the includes — no measured token is renamed, and
the expander keeps `us_dec_x`'s measured name and signature.  The bilateral
check in `source-identity.sh` names the two ABI definitions through
`escape-extra:`.  That row is an **exemption, not a comparison**: the bilateral
check asks the same question of an entity name and an extra name (is this
definition listed?), but it token-compares only the entity rows, so moving a
measured name into `escape-extra:` would stop comparing it.  Here the extras
are exactly the two ABI functions, and `--arms-only` asserts both symbols with
`nm`, so nothing measured is exempt.

### The arms

`source-identity.sh --unit escape` diffs all fifteen entities' tokens with one
numeral control; `--arms-only` compiles the unit standalone, runs a detector
calibrated to refuse `dens_`/`S1F_`/`SP_`/`sp_` while accepting this unit's
`xl_`/`us_`/`uj_` vocabulary (with a positive control that inserts a `dens_`
name), and asserts exactly the two ABI symbols.  `ir-identity.sh --unit escape`
lifts the two ABI functions and `us_dec_x` from the unit and from
`identity/escape_oracle.c` — the measured text with the same wrapper bodies —
and requires an empty `llvm-diff`, with two controls: a numeral in `xl_batch`
and the `pos0 + n` bound in `us_dec_x`.  `bench/paired.sh --unit escape` times
the extracted unit against that oracle in one binary and bounds every input
except `arm:escapes-64`, which one block divides a fixed call and placement
term by and which is therefore reported only as an observation; the summary
names the bounded set, not "every input".

Three things the bound does not say.  **The timing comparison includes placement**:
the two objects' instruction text is identical — the identity arms check it and
the objects' sizes match — so a difference this arm reports is where the code
lands, not what it does, and a placement-driven difference is not a defect of
the extraction.  **The claim is one-sided**: the extracted body is not slower
than the measured one by more than 0.5 ns per block, `extracted − measured ≤
+0.5`, so a row on the favourable side is not a regression (the check line in
`paired-escape.c` is still two-sided and reports such a row as `FAIL` until it
is updated).  Because the per-round spread can exceed the bound, a 15-round row
is triaged with its high-round interval and its one-sided rolling-window rate
before it is read as a regression.  **On identical-text rows the arm measures
layout**: when the two objects' instruction text is identical, a difference
this arm reports is the placement difference — a deterministic bias, not noise,
and one the bound cannot absorb — so the arm's real role is the comparison
across different code (the staged build against the inlined one); on an
identical-text row it measures where the code lands.  Padding the extracted
object so the call distances match is the placement-equalising option: it is
recorded and not taken, because it changes what the arm measures in the other
direction, and the choice is the user's.

### Limits

1. **The per-document gate is not here.**  Whether a document gets a list at all
   is the density probe's decision, and it is an arm selector, not a
   presence test: seven of the route's twenty-one rows carry escapes the gate
   suppresses.  The caller passes the arm; this unit never classifies a
   document.
2. **Outside `pre` the model and the measured code differ.**  Lean's subtraction
   truncates, so on a list that is not the document's positions the model copies
   nothing where the C underflows and faults; `pre` excludes exactly that input.
   The same is true of every unit's under-reservation case.
3. **The list is a 32-bit position stream**, and the batch's reserve slots past
   the count hold the emitter's stores, not positions.
4. **No aliasing claim.**  The caller owns `xp`, `dst` and the document; nothing
   here states what happens if they overlap.

## The assembled pipeline

`kernel/json/pipeline.c` is the caller the units above were hoisted for: the
block loop that runs the mask unit over every 64-byte block, composes the entry
word, hands it to the selected entry emitter, appends the block's escape
positions where the gate selects that arm, and then hands the entry stream to
stage 2.  It reaches each unit through the external entry point that unit's
header declares, so the pipeline's own text is the three lines of stage 1 the
units do not carry: the scalar word `S` and its run starts, the entry word's
composition, and the tail clamp.  `pipeline.h` states the ABI, the caller's
staging and the arm selector.

### The staging is the model's, and the one-TU form is the measured one

The pipeline is assembled as **separate translation units with the units'
external ABIs**.  That is the form the per-unit records are stated at: the
block loop is the caller, and each unit boundary is a call site a per-unit
record is consumed at.  An inlined body of thousands of instructions admits no
compositional proof, so the staged form is not a performance choice; it is the
form the refinement relation is about.

The recorded ratios in `docs/json-pipeline-performance.md`, in contrast, were
measured on the **one-TU form**: the same six files compiled as a single
translation unit, with `-O3` free to inline across what the staged form keeps
apart.  The two forms are therefore not interchangeable for a ratio, and the
timing arm measures the difference rather than transferring the record.
`docs/json-pipeline-performance.md` states no simdjson release, so this arm
claims no ratio against that reference at all: it compares two builds of this
repository's own source, and continuity with the recorded table is not assumed.

### The entry table is the caller's

`pipeline.c` never initialises `xl_pos8`, the entry unit's table: the pos8
emitter reads it, and a run whose table is not built produces an empty entry
stream and refuses every document at offset 0.  Each side's table is
file-static inside its own translation unit, so each side has one, and the
caller fills both before the first pipeline call -- the constructor idiom
`bench/paired-entry.c:79` uses.  `bench/paired-pipeline.c` does this for both
forms, compares the two 8 KiB copies (they are the same table), and refuses the
measurement if either is missing.  `pipeline.h` states the precondition where a
caller reads it.

### The timing arm

```bash
nix develop -c bash kernel/json/bench/paired.sh --unit pipeline
nix develop -c bash kernel/json/bench/paired.sh --unit pipeline --core 2 --core 5
```

The arm builds five binaries: the four pairs the decision is read from, and an
exchange of the baseline's two sides.  Each pair is linked into one binary,
because a cross-binary comparison is not a comparison
(`docs/json-pipeline-performance.md` §7.2), so each row's two sides share one
process and one window:

|row|first side|second side|what it answers|
|---|---|---|---|
|`baseline`|staged-plain|one-TU-plain|the staging as first measured|
|`arrangement`|one-TU-plain|staged-plain|the baseline's two forms with their roles exchanged: the arrangement term|
|`decision`|staged-LTO|staged-plain|did the link-time build change what the code costs|
|`reach`|staged-LTO|one-TU-LTO|does the staged build reach the inlined form, both configured alike|
|`control`|one-TU-LTO|one-TU-plain|does LTO move a form whose boundaries are already inlined|

The four forms are one source.  The staged form is `pipeline.c` and the five
units as translation units; the one-TU form is the same six files compiled as
one translation unit; the two LTO forms are those same builds compiled to
bitcode with `-flto` and linked with the whole measured line plus `-flto`,
because `-march` and `-falign-loops` are codegen decisions taken at the link
and an LTO link without them would codegen a different target.  No source file
differs between the rows; the ABI renames on the side that needs them — so one
binary can hold both sides — are the whole adaptation.

Every binary runs every document under `probes/bench/json/` through both sides
once, and requires exact agreement on the verdict, the first error offset, the
entry count, the escape count, the arena and event extents and the bytes of all
four buffers before the clock starts.  Each round runs both sides twice, once in
each order, and averages each side, so a drift inside the round cancels in the
In every binary the first side is `probe_pipeline_staged` and the second
`probe_pipeline_inlined`; the shell passes the pair's labels, and the harness's
median is `d = first - second` ns/block, so **`d > 0` means the first side is
slower**.  One block is 64 document bytes.

- **The verdict is derived from the difference, and the arithmetic is
  checked.**  The harness computes `d = first - second`, fails a claimed row only
  when `d > +0.5`, prints both sides' columns with their labels, and refuses the
  run (exit 3) when a verdict or a direction disagrees with the columns it
  printed.  This replaces an earlier form in which, at `907bc61`,
  `bench/paired-pipeline.c:551` computed `d = y - x` while `:584-585` failed on
  the claim `:500` stated as `staged - one-TU <= +0.5`: a row could print
  `FAIL: staged is slower` with the staged column the smaller one.  The
  pre-fix rows are therefore read from their columns rather than from that word;
  the defect is recorded because it is why the instrument now checks its own
  verdict, and it was found by the timing arm's own output.
- **The arm.**  The caller's selector is `arm 0`: the POS8 emitter, no escape
  list, the gated UTF-8 path.  That is the decision the measured table takes
  for a plain document with POS8 selected, and it is a caller's selector rather
  than a classifier, so both forms run the same arms.
- **301 rounds.**  The round count is this unit's default, because the row's
  per-round spread can exceed the bound (the escape arm's high-round finding).
  A row with fewer rounds, or a document under one full 4 KiB block, is an
  observation and carries no delta claim: one block divides the fixed
  per-document term by its block count, which is the rule the escape arm's
  one-block input already follows.
- **What the linker kept.**  The census is read from the final object, because a
  pre-link LTO object is bitcode and the calls it keeps are not the calls the
  linker leaves.  At clang 21.1.8 the plain staged form keeps all six boundaries
  (its census is the pinned emission's); the one-TU plain form inlines four —
  the mask unit, both entry emitters and the UTF-8 stage — and keeps the escape
  list and stage 2; the staged form linked with LTO inlines five into
  `probe_pipeline_staged`, leaving the escape list as two calls; and the one-TU
  form linked with LTO inlines all six.  The shell prints the table boundary by
  boundary, with the caller's symbol beside it, and refuses the measurement when
  the LTO link inlined nothing — a build flag whose effect is not shown is not a
  measurement.
- **Build and target beside every row.**  The report prints the compiler, the
  compile line, the LTO link line, the target triple and the seven objects'
  digests; each row repeats the build identifier, which names its pair, and the
  CPU it ran on with the core class read from `CPUID.1Ah.EAX[31:24]`.  The core
  is named on the row, not only in the shell's banner.  The one-TU sources are
  compiled by their file name from the work directory, because clang writes the
  source path into bitcode: a relative name keeps an LTO object's digest the
  same from one run to the next, where an absolute path under a fresh temporary
  directory would change it and the digest would identify nothing.
- **The window's edges.**  The shell snapshots the load average, the running
  processes and the build tools immediately before and after each timing run,
  excluding its own ancestors.  A snapshot cannot prove that the window between
  them was quiet, so a run whose edge snapshots name a build process is labelled
  as such, and the label is printed with the rows; a clean label is only the
  absence of a named build at the two edges.

Every form is compiled with `-falign-functions=4096` so every function starts a
page, and the shell asserts that both pipeline symbols of every binary do.  The
comparison still includes placement: the forms place their code differently, and
a difference that survives the census is a difference of the two forms, not
noise.  Identical text at different addresses is known to move a row by more
than the bound, so the arrangement term is a row rather than an assumption: the
`arrangement` pair is the baseline's two sides with their symbol roles exchanged
and linked from the same objects, so its difference is what the placement of
these two forms contributes.  A baseline-sized difference the exchange does not
survive is arrangement, not code.

### The pipeline's identity arms

`source-identity.sh --unit pipeline` reads the call census of
`leanllvm_json_pipeline`'s body from its preprocessed definition: exactly the
six ABIs `probes/install/ir/json-pipeline.inventory` names, each once.  Its
control changes one call's target and requires the census to report it.
`--arms-only` compiles the caller, runs the units' measurement-vocabulary
detector with its positive control, and asserts the one public symbol.
`--link-census` is accepted here too: the pipeline's place in the assembled
link is its own claim, and the arm asserts that `ld -r` over the six objects
leaves no undefined project symbol and defines `leanllvm_json_pipeline`.

`ir-identity.sh --unit pipeline` relates the three texts that must agree: the
emission of `pipeline.c`, the object built from that same source, and the pinned
fixture `probes/install/ir/json-pipeline.candidate.ll`.  Their call censuses
(the multiset of the six ABIs, after loop unswitching) must be equal.  That is
what makes "the object the theorem is about is the object the timing arm
measures" a checked relation.  Its two controls change one call target in a copy
of the source and remove one call from a copy of the fixture; both are reported.

### Limits

1. **The one-TU form is the compiler's choice.**  It is the same source compiled
   as one translation unit, not a forced-inline form; which boundaries it
   inlines is a property of the compiler and is printed rather than assumed.
2. **The arm measures different code.**  The staged form's boundaries are
   composable call sites; whether they cost or save on a given build is what the
   row and its census report, and the row is a statement about the two forms,
   not a refutation of either.  The record's ratios remain the one-TU form's.
3. **The pipeline's arms are the caller's.**  The density gate that selects an
   emitter and the escape list per document is not in this unit, and the arm
   passes one selector for every document.  A document whose recorded class
   would select another emitter is outside this arm's row.

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
nix develop -c bash kernel/json/identity/source-identity.sh --unit utf8 # UTF-8 unit: tokens, the stage range
                                                                       # and its eight controls
nix develop -c bash kernel/json/identity/source-identity.sh --unit utf8 --arms-only # UTF-8 unit: the TU, its
                                                                       # calibrated detector and its ABI symbol
nix develop -c bash kernel/json/identity/ir-identity.sh --unit utf8    # UTF-8 unit: the stage's emitted-code
                                                                       # identity + two controls
nix develop -c bash kernel/json/identity/source-identity.sh --unit escape # escape unit: tokens, deletions,
                                                                       # mutation control
nix develop -c bash kernel/json/identity/source-identity.sh --unit escape --arms-only # escape unit: the TU,
                                                                       # calibrated detector, two ABI symbols
nix develop -c bash kernel/json/identity/ir-identity.sh --unit escape   # escape unit: emitted-code identity +
                                                                       # two controls
nix develop -c bash kernel/json/bench/paired.sh --unit escape           # escape unit: paired timing
nix develop -c bash kernel/json/identity/inventory.sh                  # the fixture's inventory gate
nix develop -c bash kernel/json/identity/inventory.sh --unit utf8      # the UTF-8 fixture's inventory gate
nix develop -c bash kernel/json/bench/paired.sh                        # mask unit: paired timing
nix develop -c bash kernel/json/bench/paired.sh --unit entry           # entry unit: paired timing, both kernels
nix develop -c bash kernel/json/bench/paired.sh --unit utf8            # UTF-8 unit: paired timing
nix develop -c bash kernel/json/identity/final-identity.sh entry       # the entry unit's three arms, one command
nix develop -c bash kernel/json/identity/final-identity.sh utf8        # the UTF-8 unit's three arms, one command
nix develop -c bash kernel/json/identity/final-identity.sh escape      # the escape unit's three arms, one command
nix develop -c bash kernel/json/identity/source-identity.sh --unit pipeline # the caller's call census + control
nix develop -c bash kernel/json/identity/source-identity.sh --unit pipeline --arms-only # the caller's TU, detector and symbol
nix develop -c bash kernel/json/identity/source-identity.sh --unit pipeline --link-census # the assembled link
nix develop -c bash kernel/json/identity/ir-identity.sh --unit pipeline     # emission, object and fixture census + two controls
nix develop -c bash kernel/json/bench/paired.sh --unit pipeline             # staged vs one-TU timing, 301 rounds
nix develop -c bash kernel/json/identity/final-identity.sh pipeline         # the pipeline's three arms, one command
```

`final-identity.sh <unit>` is the dispatcher: it runs the unit's token identity,
its IR identity and its paired timing arm in that order, and exits `3` naming
the missing piece for a unit it does not implement.  Add `--tree-only` to either
identity script to refuse any input path outside this repository, so the claim
reproduces from a checkout with the scratch tree gone.  Under it, `--vendor`
refuses while the scratch tree exists, because the live diff is the one thing
that asks to read outside.

`source-identity.sh --unit utf8 --stage-tu` prints the measured side of the
UTF-8 unit's emitted-code comparison — the measured declarations with the
extracted stage pasted in — and it is the **one** definition of that text:
`ir-identity.sh --unit utf8` and `bench/paired.sh --unit utf8` both build their
measured side from it rather than from copies.  `UTF8_STAGE_NAME` in the
environment renames the function, which is how the timing arm can link it beside
the unit in one binary.

Three properties of the instruments are worth knowing when reading their output:

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
- `llvm-diff` does **not** compare instruction flags, so the UTF-8 unit's arm
  also compares the two lifted modules' code text byte for byte before their
  metadata sections.  A `nuw` removed from an instruction is a difference in
  that text and no difference to `llvm-diff` — measured, and the reason the unit
  prints both verdicts for that control.
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
`probes/install/ir/capture-entry.sh` and the four artefacts it derives, because
the classes that gate checks -- the strip classes, the rewrite classes, and the
table-rewrite class the entry fixture's GEPs become -- are the capture's formats,
and a list kept in the gate would be the hand-kept list this gate exists to
avoid.  The UTF-8 unit's gate names its own capture and its three inventories in
the same way (`--unit utf8`: `capture-utf8.sh`, with no table class, because that
unit's tables fold to literal vector operands), and it exits `3` naming the
missing file while an input is absent.  An invocation with no `--unit` is the
mask unit's, unchanged.

