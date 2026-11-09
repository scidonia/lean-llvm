# The vendored measured sources

## What the set is

Thirty-seven files, copied byte for byte from the measured scratch tree
`/tmp/scidonia-spike45/src` and pinned by `SHA256SUMS`.  The `pulled by` column
names the file that includes each one in the measured tree, not the unit that
ends up using it: where a header is reached only through another header, the
pulling header is what a reader has to look at to see the configuration under
which the file is read.

|File|sha256|what it supplies|pulled by|
|---|---|---|---|
|`s1fuse.h`|`d1ee36b9831b553df7fccfe697e7cc2b29fc1f20da59eeefd1f338bc50954a9e`|the stage-1 mask unit: `s1f_masks`, its four helpers `s1f_prefix_xor`, `s1f_escaped`, `s1f_sw32`, `s1f_sm_ws`, the tables `s1f_lo_tab`/`s1f_hi_tab`, and the `S1F` carry type; also the entry kernels, the escape-list arm at `S1F_XS`, and the UTF-8 stage's statements|`sb34.c:30` in the measured chain; `identity/oracle.c` and `identity/entry_oracle.c` include it alone|
|`xlist.h`|`242286de0e1047e516f95b6eef313f9817adec4c981945cd03746e5c37397f51`|the escape-position list `xl_lanes`/`xl_emit` at `S1F_XS=5`, its eight-entry batch and the reserve it writes past the true count|`s1fuse.h:98`|
|`dens.h`|`77e5dcb05c08bceaf34f9c0833a929f2cba0f7a62bf84db8ed041697eb0ef6f2`|the document-level readings: `dens_probe`, the three classes, the sampled escape density and the thresholds `DENS_PLAIN_NUM`/`DENS_HEAVY_NUM`; `S1F_XS_DYN` consults its class|`s1fuse.h:37`, and `s2port.h:30`|
|`u8kl.h`|`403fbe19709600a924e4704a3bbd0eca474a12f1be885fd17fd1dcab36074c21`|the Keiser–Lemire UTF-8 validator `s1fuse.h` includes at `S1F_UTF8=7`: the three 32-byte tables `kl_t1`/`kl_t2`/`kl_t3`, the load-form error vector `kl_err32_ld`/`kl_err_vec_ld`, the tail test `kl_tail_byte`, and — not selected by the measured build — the permutation form `KLCARRY`, `kl_carry_init`, `kl_err32`, `kl_err_vec`, `kl_block_vec`, `kl_block`, `kl_block_ld` and `kl_carry_prefix`|`s1fuse.h:124`, under `S1F_UTF8 == 7 || S1F_UTF8 == 8`|
|`usdec.h`|`6d3498003b2fd7c17c6de560ccb020c6aa2aa2422881e944c525836c819a26b8`|the per-body list decoder `us_dec_x` and the kernels `us_dec_kernel`/`us_body_kernel`; its escape step `us_esc` and `\u` step `us_esc_u`, the hex reader `us_hex4` and the four-class byte mask `us_cls`, and the run copy `us_run`/`us_run_long`|`s2port.h:29`|
|`usdec_gate.h`|`569ced2c6efd11584de9a77318ea7d3160066575bc671a777368f6a023efbc64`|two shapes of the list decoder in one build — `us_dec_x_out` (out of line, `\u` inline), `us_dec_x_inl` (`\u` out of line) and `us_dec_x_inl2` (both inline) — with the two `\u` steps `us_esc_u_ni` and `us_esc_si` they substitute|`s2port.h:43`, when `S2_DEC_GATE || SP_MODES`; the measured `S2_DEC_GATE=2` selects it|
|`modes.h`|`f3499831eb0222d0da55916cf3e30509aedf6b3a64b584482b6a99e93e7d4ec0`|the runtime selectors `sp_list` (the escape list's gate on or off), `sp_gate`, `sp_fold`, `sp_dec`, `sp_noim`, `sp_disp`, `sp_print` and `sp_modes_init`|`s1fuse.h:39` and `s2port.h:46`, under `SP_MODES`|
|`modes43.h`|`46f3013dcad93b8fccf86674814aae6174bc28b48ef182f772d7f60253e11523`|the runtime selector `sp43_esc` over the fourteen 43-series escape-step shapes, and the census they print|`s2port.h:49`, under `SP43_MODES`|
|`modes44.h`|`9f264c7dd23e9bab713c6a640385c9603ee542d540a5edf4bbd58ff74fc7aef3`|the runtime selector `sp44_dec` over the carried-kind arms and the `sp44_kind` record switch|`s2port.h:54`, under `SP44_MODES`|
|`modes45.h`|`8e89c475b3bcd587064aebc392894095c0152d3952c143f6ed10b7beb2a94f5e`|the runtime selector `sp45_kern` over the entry-emitter kernels, forced or probed|`s1fuse.h:46`, under `SP45_MODES`|
|`usdec_esc43.h`|`471c816c4b2b4a884341901d27b47cb46a8e5c11f9fb613fc6255cf912726cd6`|the table-driven escape expansion: `us_emit4`, `us_esc_u2`, the 256-entry `US_ESC43` class table with `US_E_U`/`US_E_BAD`, and the steps `us_esc_t`, `us_esc_bf`, `us_esc_sni`, `us_esc_tni`, `us_esc_u2only`|`usdec_kind44.h:23`; also `s2port.h:50`, under `SP43_MODES`|
|`usdec_variants43.h`|`427f462a805298d9feba57f90032b6cd1d0ba78ebf238f5635886f8431bf0093`|thirteen 43-series decoder shapes, each the same body with a different escape step, including the identical-copy placement controls `us_dec_x_dup43`, `us_dec_x_dup2_43` and `us_dec_x_dup3_43`|`s2port.h:51`, under `SP43_MODES`|
|`usdec_kind44.h`|`6a4aac48affd024714ab80520150c04eeb4490ce42a4177b190fad054e02c902`|the escape steps that consume a carried kind bit: `us_esc_k_simple`, `us_esc_k_if`, `us_esc_k_jmp`, `us_esc_k_sw`, under `K44_STRICT`|`usdec_variants44.h:15`; also `s2port.h:55`, under `SP44_MODES`|
|`usdec_variants44.h`|`c75cbb91fb14f1d5affac7563c94130daa34066769c127962cd9949215b8bf06`|seven carried-kind decoder shapes and the identical-copy placement controls `us_dec_x_dup44`, `us_dec_x_dup2_44`, `us_dec_x_kifdup44`, `us_dec_x_kifdup2_44`|`s2port.h:56`, under `SP44_MODES`|
|`usdec_x_body.inc`|`667da9db8b72a08a767f2376daed32185c6aeed58f64f415cb7939963301987f`|one copy of the list decoder's body, parameterised by `USDEC_NAME`, `USDEC_ATTR` and `USDEC_ESCFN`, so a build can hold several shapes with one text|`usdec_gate.h:61,72,81`, `usdec_variants43.h` at thirteen sites, `usdec_variants44.h:25,31`|
|`usdec_x_kind.inc`|`045e1357105c100beee2dacde9172a36890cdcd63b88a990aa38ff7d60d2b227`|the same body with the escape kind carried in, whose escape step reads the kind record rather than the bytes|`usdec_variants44.h:38,44,50,57,63`|
|`uj.c`|`11155f19663c22ee43a00ae5b844262860b25ee2046c32aea856cf89633bd263`|`UJ_UNESC` (the simple-escape map, `:30`), `UJ_HEX` (`:37`), `uj_enc` (`:49`) and `uj_enc_word` (`:127`); also the fused unescaper `uj_decode` and the SIMD run helpers, which no unit of this repository calls — the file is pinned whole because a digest pins a file, not a selection from it.  It includes only `<stdint.h>`, `<string.h>` and `<immintrin.h>`, so the set's closure closes at it|`p16.c:57` in the measured chain; nothing inside this set pulls it, and `usdec.h`'s escape step and encoder reference three of its four names at the measured `US_ENC=0` — `UJ_HEX` (`:240`, `:350-351`, `:359-360`), `UJ_UNESC` (`:338`, `:349`, `:378`, `:428`, `:659`) and `uj_enc_word` (`:290`, `:300`, `:447`); `uj_enc` (`:295`) is not compiled at the measured flags: `US_EMIT4=1` selects the `#if US_EMIT4` arm of `us_emit` (`:288`) before the `#elif US_ENC` arm (`:293`); reaching `:295` takes `-DUS_EMIT4=0 -DUS_ENC=1`|
|`s2port.h`|`4e785ea0c70e770852e323e182c428e9e5ea213bfb39b73f955035f4d3029d9e`|the stage-2 unit: the `S2` cursor record (input, raw index, derived entry stream `ep`, and the `xp`/`em`/`uk` escape planes), `s2_init`, the entry-stream builder `s2_build`, the value-position tests `s2_value_pos`/`s2_after_value`, the string-body handler `s2_string_body` and its consuming form `s2_string_touch`, and the loop `s2_walk`; the flags `S2_VAL`/`S2_STR`/`S2_EV`, the `S2_XP`/`S2_XM` planes and the `S2_DEC_GATE` selector|`sb34.c:29`, after `sb34.c:28` includes `p16.c`; the stage-2 unit's own text in `kernel/json/stage2.c` is taken from the file|
|`p16.c`|`b8c669d74b6e1780af7a469e792d6e39b98092d114f5ee0492d9d1b7a6075a2c`|the cursor over the stage-1 index stream: the packing forms `IXP`/`IXK`, the kind enum `K_*`, the token and cursor records `OdTok`/`OdCur` with their `od_reset*` forms, failure reporting `od_fail`, the span accumulate helpers `touch_bytes`/`touch_u64`, the value-position tests, the scalar path `od_scalar_value`, the gap recovery `od_gap_recover` and the walk `od_walk`; it includes `p6.c` (`:33`), the `num*` chain (`:42`, `:44`, `:52`, `:54`, under `NUMF_EL`/`NUMF_NOINLINE`), `uj.c` (`:57`), `str3.c` (`:58`), `zesc.c` (`:59`), `zf.c` (`:60`), `str3body.inc` (`:447`), `strz.c` (`:448`), the emitter `emit24.c` (`:664`) and the five walk arms (`:658`, `:662`, `:663`, `:665`, `:666`)|`sb34.c:28`; nothing inside this set pulls it|
|`p6.c`|`b542d9656aa03ccb8f85d2d43fe25a2ffbe707aa9cb3f6847f4ac2eeb21a5b72`|the reference parser and harness: `Err`/`err_set`; the output buffer `Out` with `out_init`/`out_reserve`/`out_raw`/`out_tag`/`out_u32`/`out_u64` and the `hup` checksum; the event tags `T_*`; `dbits`, `is_ws`, `is_delim`, `lit_check`, `to_double`, `num_scan`; the nesting limit `MAXD`, the container constants `C_OBJ`/`C_ARR`, the decoded-string scratch `g_sbuf`, the tape/DOM consumers, and `main`, which the puller renames `p6_original_main`|`p16.c:33`|
|`strz.c`|`d6db00a6b1e7b0664275085f0cea9b25bfac36fd2276911bd37a915498616672`|zero-copy string bodies: the `ZOut` event sink with its reused arena and `z_init`/`z_free`/`z_reset`, `z_arena_reserve`, the plain-body sentinel `Z_NONE`, the special finder `z_scan`, the control-byte finder `z_scan_ctl`, the body handlers `od_string_body_z`/`od_string_body_z_cls` and the event expander `z_expand`|`p16.c:448`; `walkz_body.inc:271` and `walkzk_body.inc:166` call its body handlers|
|`numf_el1.h`|`0cccfa3ecf7e058eabc684c2df7898ef8d3509ded91033b87b568e4cfbb79c94`|the tiered number scan's inline tier: `num_fast_el1`, its eight-digit reader `num_d8_el1`, the power tables `NUMF_EL1_POW10`/`NUMF_EL1_P10` and the diagnostic counters `g_nume1_el`/`g_nume1_slow`; it includes `numel.h` (`:18`) and `numel_el.h` (`:19`)|`p16.c:44`, under `NUMF_EL` and not `NUMF_NOINLINE`; it is `numf.h`'s counterpart|
|`numel.h`|`a4da03f77dc937359d795d234087664d269200bb7e186fca37cbfa591cae6f03`|`num_el`, the 128-bit exact decimal-to-double for a mantissa below 10^19 and `q` in the table range, with the remainder-versus-half-ulp comparison and the cannot-decide return|`numf_el1.h:18`; it includes `epow_table.h` (`:18`)|
|`numel_el.h`|`2f12ddc91adf6d1320ee5d8822c3092ea0276b278b2049ae382f06a7ed25d5d7`|the deferred Eisel–Lemire entry `num_el_el1`, inlined or out of line through `EL_ENTRY` under `EL_ENTRY_NOINLINE`, and `num_el_el1c`, which computes the low product half only inside the guard window|`numf_el1.h:19`|
|`epow_table.h`|`954e93961f751417aaf495cbd0661094a8000e67919553664a7e7da752a25370`|the `EPow` record, the 91-entry `EPOW` table of 128-bit normalised significands of 10^q for `q` in [-45,45], and the range bounds `EPOW_MIN`/`EPOW_MAX`|`numel.h:18`|
|`str3.c`|`1627129aa2c65c78e6ea5049c89856e21ee651396789b9ea878f1c27417cce6b`|the string-body decode kernels `uj3_plain` and `uj3_simple` with their mask helpers `uj3_ctl_mask`/`uj3_keep`, selected by the stage-1 escape class; a body carrying `\u` still falls back to `uj_decode`/`uj_decode_acc`|`p16.c:58`|
|`str3body.inc`|`3e9ce13cae4f7f6e198c38b78cb8c4af3bdff34524cd17bd6bc51ca3a9637f91`|`od_str_path`/`od_str_dispatch`, which read a body's escape class from the stage-1 masks without re-reading input bytes, and the handler `od_string_body_e` that sends the body to the plain, simple-escape or `\u` kernel|`p16.c:447`|
|`zesc.c`|`cb9ef94a46a099f70ca44907156c6a3bed374299fdb35a988b2040590019b1ce`|chunked escape materialisation: the simple-escape map `ZE_UNESC`, the 64-byte special mask `ze_block_mask`, the vector run copy `ze_run`, the escape step `ze_esc` and the kernel `ze_decode`|`p16.c:59`|
|`zf.c`|`444735b9911facb38a55295a86c65b0680466f296f011a48b2da5250c589e25d`|the fused validate-and-copy string-body pass: the escape validators `zf_esc_val`/`zf_esc_cp` and the thirteen kernels generated from `zf_impl.inc` — `zf_val32`/`zf_val64`/`zf_val64f`, `zf_span32`/`zf_span64`/`zf_span64f`, `zf_cp64`, `zf_val32b`/`zf_val64b`, `zf_span32b`/`zf_span64b`, `zf_span_t` and `zf_val64c` — and the window/escape counters|`p16.c:60`; it includes `zf_impl.inc` at `:474`, `:484`, `:496`, `:507`, `:517`, `:529`, `:541`, `:552`, `:562`, `:572`, `:582`, `:595`, `:607`|
|`zf_impl.inc`|`0fe151e576fe82f932f2c4946a68ca04e2b5d791267bf0f043f69b84f9713a15`|one copy of the fused body loop, parameterised by `ZF_NAME`, `ZF_COPY` (0 validate, 1 materialise, 2 lazily materialise) and `ZF_W` (32 or 64), with the `ZF_FAST`/`ZF_ESC`/`ZF_NOVAL` arms and the whole-window mask consumption|`zf.c` at the thirteen sites named in the row above|
|`emit24.c`|`5380fca48714abb3491239c3cb793e275195c3e9e0a8e12753f8248bce10510b`|the gated emitter with the token kind folded into an entry's spare bits: `E24_SHIFT`, the `E24_KIND` table, `e24_entry` and `scan_cand_kind`|`p16.c:664`; the `PACK_SHIFT == 5` cursor form (`IXP`/`IXK`) reads its entries|
|`walk_body.inc`|`1e436365cff81dec2b69c5e3cc60d12d60ddc9811d72504280db4e376b1cb91e`|`od_walk`'s body, parameterised by `WNAME`/`WSTEP`/`WGAPRE`/`WSTR`, so the grammar, value and error code exists once per tokenizer|`walk_e.inc:11` and `walk_s.inc:90`|
|`walk_e.inc`|`f1eb6b458af7c76638113bc85dbb169bb0371518f46c93a2f3559158819ab1ef`|`od_walk_e`: the `od_step_s` tokenizer with the three-path string body `od_string_body_e` inlined through `walk_body.inc`|`p16.c:666`|
|`walk_m.inc`|`06442c2286e5c341f9cd98c6b4c6b53cdb30506216cec31cb84b6001d28de77d`|the masks-direct tokenizer and walk: the whitespace skip `od_ws_skip` with its byte, SSE2 and AVX2 `MASK_SWAR` forms, and `od_step_m`/`od_walk_m`, which take token positions from the candidate mask and drop the index stream|`p16.c:658`|
|`walk_s.inc`|`d2ea25ed293d95c6acf2d9f6608a3ba2c71357f3c49ad083c0caf40062cd9751`|`od_walk_s`: the `od_step_s` tokenizer with the SIMD whitespace skip, the byte-chain scalar classifier `od_scalar_kind_chain`, and the `NO_VISITED` counter arm|`p16.c:662`|
|`walkz_body.inc`|`e1aaf5dbb6754dedb35a08ce74c82efad8522f764407e736b490670f076353ac`|`od_walk_z`/`od_walk_z_cls`, the `od_step_s` grammar with zero-copy string bodies into a `ZOut` sink, and the `PF_NEXT` prefetch arm|`p16.c:663`; also `wm.c:36`|
|`walkzk_body.inc`|`9f87ef3817a6fcf1b0733d0d16120b5f19cac85bed6ce6804202f2487c43bdc8`|`od_step_sk` and `od_walk_zk`, which read a token's kind from the packed entry (`ent >> E24_SHIFT`, kind in the low five bits) instead of loading the input byte and the kind table|`p16.c:665`|

The stage-2 unit's text is read from `s2port.h`, `p16.c`, `strz.c`, `p6.c` and
the `numf`/`numel` chain: `s2port.h` holds the loop and its cursor, and every
block the loop calls — the reference parser's records and output buffer, the
index cursor, the number conversion, the zero-copy body and the escape
materialisers — is reached from `p16.c`, which is why those files are pinned
whole beside it.  The closure was established by compiling rather than by
enumeration: a translation unit holding `#define P9_NO_MAIN 1`,
`#include "p16.c"` and `#include "s2port.h"` was built with the measured
compiler line `clang -O3 -march=x86-64-v3 -mpclmul -std=gnu11
-Wno-initializer-overrides -Wno-macro-redefined` (clang 21.1.8) at the
configuration `-DNUMF_EL -DSTAGE_PROBE -DS1F_DENS=1 -DS1F_EXP2=11
-DS1F_UTF8=7 -DS1F_KL_DOC=1 -DPSTAGE=32 -DPMODE=2 -DS1F_XS=5 -DS2_XP=1
-DS2_DEC_GATE=2 -DS1F_XS_DYN=1 -DUS_EMIT4=1`, and `clang -E -H`'s local file
list was read.  That list names exactly the twenty files this vendoring adds
plus the five already pinned (`dens.h`, `usdec.h`, `usdec_gate.h`,
`usdec_x_body.inc`, `uj.c`) and no other local file.  The three `numf*` headers
the list does not name are excluded for that reason: the measured configuration
defines `NUMF_EL` and not `NUMF_NOINLINE`, so `p16.c:44` reads `numf_el1.h`
while `:42`, `:52` and `:54` are not taken, and `numf.h`, `numf_ni.h` and
`numf_el1_ni.h` are the arms of a configuration no unit of this repository
builds.  The evidence run at `abdfb8d` was `sha256sum -c SHA256SUMS` and the
compile above, both clean: every digest row reports `OK`, and the compile writes
`tu.o` and exits 0.

`usdec.h` is the file whose closure forced `uj.c` into the set: a translation
unit holding the header at the measured flags (with the libc and intrinsic
headers it needs) fails with **three** undeclared names under
`-ferror-limit=0`: `UJ_HEX` and `UJ_UNESC` (variables) and `uj_enc_word` (a
call in `us_emit`, which the header itself defines, so the diagnostic does not
wait for `us_dec_x` to be instantiated).  `-DUS_ENC=1` does not change that
count at the measured flags, because `US_EMIT4=1` takes the `#if US_EMIT4` arm
of `us_emit` before the `#elif US_ENC` arm; the fourth name, `uj_enc`, appears
only under `-DUS_EMIT4=0 -DUS_ENC=1`, which reports four.  The measured chain
supplies the three only because `sb34.c:28` includes `p16.c` (whose `:57` is
`#include "uj.c"`) before `:29` includes `s2port.h`.  `usdec_x_body.inc`'s
own header comment says it is "included from usdec_gate.h"; it is also included
from `usdec_variants43.h` and `usdec_variants44.h`, and the row above gives the
sites, because that comment describes the first caller rather than every one.

`usdec.h`'s own comment on the run copy **understates the write obligation of
this file, and the pinned bytes are not edited to say so.**  `:390-392` says the
store over-writes "up to 31 bytes past the run", which is the arithmetic of the
`US_RUN2 == 0` form the measured build selects (`:78-80`, `:404-406`: the second
32-byte store is taken only when `len > 32`).  The same function also holds the
`US_RUN2 == 1` form (`:400-402`), which stores the second vector unconditionally,
so a one-byte run reaches `dst + 63`.  Both reads of this file must therefore
stage **64 writable bytes past the decoded extent**; a unit or probe built on the
comment alone would reserve half of what the file can write.

Four stage-1 units are read out of these files, not one: the mask unit (`s1f_masks` and
its four helpers, the two tables and the `S1F` type, all in `s1fuse.h`), the
entry unit (`xl_pos8` and its initialiser from `xlist.h`, the two entry kernels
and their block-loop macro from `s1fuse.h`), the UTF-8 unit (`u8kl.h`'s six
selected definitions and `s1fuse.h`'s `S1F_KL_DOC` stage statements), and the
escape unit (`xlist.h`'s list for the built arm and `usdec.h`'s `us_dec_x` for
the expansion, whose other forms are in the `usdec_*` headers and the two
`.inc` files).  The set grew by thirteen files with the escape unit and
`SHA256SUMS` moved with it.

The measured build they come from is `build49.sh` in the same tree: the
compiler line `clang -O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64
-falign-functions=64` (clang 21.1.8) and the configuration `m49`
(`build49.sh:19-21`): `-DSTAGE_PROBE -DS1F_ENT_PROBE=1 -DS1F_DENS=1
-DS1F_TWOPHASE=1 -DS1F_EXP2=11 -DS1F_DISPATCH=1`, `-DS1F_UTF8=7 -DS1F_KL_DOC=1`,
`-DPSTAGE=32 -DPMODE=2 -DS1F_XS=5 -DS2_XP=1 -DS2_DEC_GATE=2 -DS1F_XS_DYN=1`,
plus `-DUS_EMIT4=1` for the escape step.  The scratch tree is not
version-controlled, so the digests above are its revision: a copy of the tree
whose thirty-seven files hash to these values is the tree these units were
extracted from.

The emission that configuration produces has `target datalayout =
"e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"`
and `target triple = "x86_64-unknown-linux-gnu"`; the data layout and pointer
width are what the compiled object's behaviour rests on, and the target
features are `-march=x86-64-v3 -mpclmul` (`AVX2`, `BMI1`, `BMI2`, `PCLMUL`).
The fixture's own header normalisation — which of `target datalayout`,
`target triple`, `source_filename` and the `attributes #N = { … }` groups it
removes — is recorded by the capture's generated strip inventory beside the
fixture, not transcribed here.

## At what the set is complete

The set is complete **at the measured `-D` set above**, and that qualification
is part of the pin: `s1fuse.h` and `usdec.h` each include further text under
macros the measured configuration does not define, and that text is deliberately
outside the pin.  The closure was proved by compiling rather than by
enumeration, at `7ac7b29` with clang 21.1.8, in three positions because the set
has three entry points and a single translation unit would miss the arm that
fails:

|Position|Translation unit|Flags|Result|
|---|---|---|---|
|the decoder|`uj.c`, `usdec.h`, `usdec_gate.h`|the measured set with `-DUS_EMIT4=1`|exit 0, no error|
|the variant arms|`uj.c`, `usdec.h`, `usdec_esc43.h`, `usdec_kind44.h`, `usdec_variants43.h`, `usdec_variants44.h`|the measured set plus `-DSP43_MODES -DSP44_MODES`|exit 0, no error|
|the mode selectors|`dens.h`, `s1fuse.h`, `modes43.h`, `modes44.h`|`-DSP_MODES -DSP45_MODES -DSP43_MODES -DS1F_XS=5 …`|exit 0, no error|

`modes45.h` is not standalone — it reads `DENS_K_*` from `dens.h` and `s1f_kern`
from `s1fuse.h:44` — so it is compiled at its puller's position, `s1fuse.h:46`,
which is why the third row includes `s1fuse.h` rather than the four `modes*.h`
files alone.

Four pulls are outside the set, each with the reason it is out:

- **`kind44.h`** — included by `s1fuse.h:289` under `SP44_MODES`, which the
  measured build does not set (`build49.sh:24`'s `M` is `-DSP_MODES
  -DSP45_MODES -DS1F_U8_MODES -DDENS_PRINT`; `:29` is a `b p49` build
  invocation, not the `M` definition).  The decoder's 44-series arms are
  in the set because they are `usdec_*` files; their stage-1 counterpart is not,
  and a `clang -E -H` run over `dens.h` + `s1fuse.h` at the `m49` set reads
  exactly `dens.h`, `s1fuse.h` and `xlist.h` — plus `u8kl.h` at `-DS1F_UTF8=7` —
  and no other local file.
- **`u8fold.h`** — included by `s1fuse.h:117` at `S1F_UTF8 ∈ {3,4,5,6}`; the
  measured value is 7, which selects `u8kl.h` instead.
- **`usdec_x_hi.inc`** — included by `bench44.c:173,179,185` only; no header in
  the set pulls it.
- **`us_pos8.inc`** — included by `usdec.h:453` under `US_EXP`, which the
  measured configuration leaves at 0; `clang -E -H` over the decoder translation
  unit at `-DUS_EMIT4=1 -DS2_DEC_GATE=2` reads `usdec.h`, `usdec_gate.h` and
  `usdec_x_body.inc` and nothing else from this directory.

A reader who greps a pull site and does not find the file here has found the
boundary, not a broken pin: the missing text belongs to a configuration no unit
of this repository builds.

## How the pin is read back

Two rules, both learned by getting them wrong:

- **The path spec is repository-relative.** `sha256sum -c SHA256SUMS` from this
  directory checks the worktree; from the repository root,
  `git cat-file blob :kernel/json/measured/<file>` for each row compared with its
  digest checks a staged tree. A spec built from `$PWD` resolves to no blob,
  `git cat-file` then succeeds on the empty object, and **every row reports the
  digest of the empty string** — a read-out that is indistinguishable from a pin
  whose files have all been emptied. Report the per-file digest comparison and
  the tree object (`git write-tree`) together, because either alone leaves the
  other uncheckable.
- **Completeness is established by compiling at each puller's position**, not by
  enumerating the includes a reader can see. The table above gives the three
  positions; an enumeration finds only what was recalled, while a compile finds
  what the preprocessor actually reads — and the difference is a file that every
  listed header used and no list named.

## Why each file is committed

So that the identity claim reproduces from a checkout.  `identity/oracle.c`
compiles `s1f_masks` out of `s1fuse.h` and `identity/entry_oracle.c` compiles the
two entry kernels out of the same file; `identity/ir-identity.sh` compares each
emission with the one the matching unit in `kernel/json/` produces; and both
scripts run under `--tree-only`, which refuses any input path outside this
repository.  `u8kl.h` is committed for the same reason: the UTF-8 unit's token
arm diffs its copied entities and its stage statements against `u8kl.h` and
`s1fuse.h`, and its IR arm builds the measured side of the comparison from those
same two files.  The escape unit's two halves are committed for the same reason
and are measured from here rather than retyped: `probes/json/escape_measured.c`
builds the list from `s1fuse.h` at the measured configuration, and
`probes/json/unescape_measured.c` builds the expander from `uj.c` and `usdec.h`,
each against a reference written independently in its driver.  The scratch tree
is a convenience for the first vendoring and for the digests' corroboration,
never a dependency of the result.  The timing arms' probe translation units
(`bench/paired.c`, `bench/paired-entry.c`) include the same files for the same
reason, one unit each.

## Read-only

No `lake` target builds these files.  No lint runs over them.  The translation
units that include them are the identity arms' oracles, the timing arms' probes,
the route's table dumper (`probes/json/u8kl_tables.c`, compiled by
`tests/json-utf8/check.sh` to print the three tables the specification states),
and the escape probes above, and each exists to be compiled, compared or timed,
never linked into anything shipped.  An edit to any of them is an edit to the
pinned set: it moves `SHA256SUMS` deliberately and it re-opens the identity
claim, which is why no change to `kernel/json/s1_block.c`,
`kernel/json/entry.c`, `kernel/json/utf8.c` or `kernel/json/escape.c` may be
accompanied by a silent refresh of it.
