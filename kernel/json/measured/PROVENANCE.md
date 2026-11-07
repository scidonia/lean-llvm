# The vendored measured sources

## What the set is

Three files, copied byte for byte from the measured scratch tree
`/tmp/scidonia-spike45/src` and pinned by `SHA256SUMS`:

|File|sha256|what it supplies|
|---|---|---|
|`s1fuse.h`|`d1ee36b9831b553df7fccfe697e7cc2b29fc1f20da59eeefd1f338bc50954a9e`|the stage-1 mask unit: `s1f_masks`, its four helpers `s1f_prefix_xor`, `s1f_escaped`, `s1f_sw32`, `s1f_sm_ws`, the tables `s1f_lo_tab`/`s1f_hi_tab`, and the `S1F` carry type|
|`xlist.h`|`242286de0e1047e516f95b6eef313f9817adec4c981945cd03746e5c37397f51`|the escape-position list the measured builder includes at `S1F_XS=5`; not used by the mask unit, but part of the header's own include closure at the measured configuration|
|`dens.h`|`77e5dcb05c08bceaf34f9c0833a929f2cba0f7a62bf84db8ed041697eb0ef6f2`|the document-level readings; likewise included by `s1fuse.h` before the mask region|

The measured build they come from is `build49.sh` in the same tree: the
compiler line `clang -O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64
-falign-functions=64` (clang 21.1.8) and the configuration `m49`
(`build49.sh:19-21`): `-DSTAGE_PROBE -DS1F_ENT_PROBE=1 -DS1F_DENS=1
-DS1F_TWOPHASE=1 -DS1F_EXP2=11 -DS1F_DISPATCH=1`, `-DS1F_UTF8=7 -DS1F_KL_DOC=1`,
`-DPSTAGE=32 -DPMODE=2 -DS1F_XS=5 -DS2_XP=1 -DS2_DEC_GATE=2 -DS1F_XS_DYN=1`.
The scratch tree is not version-controlled, so the digests above are its
revision: a copy of the tree whose three files hash to these values is the tree
this unit was extracted from.

The emission that configuration produces has `target datalayout =
"e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"`
and `target triple = "x86_64-unknown-linux-gnu"`; the data layout and pointer
width are what the compiled object's behaviour rests on, and the target
features are `-march=x86-64-v3 -mpclmul` (`AVX2`, `BMI1`, `BMI2`, `PCLMUL`).
The fixture's own header normalisation — which of `target datalayout`,
`target triple`, `source_filename` and the `attributes #N = { … }` groups it
removes — is recorded by the capture's generated strip inventory beside the
fixture, not transcribed here.

## Why each file is committed

So that the identity claim reproduces from a checkout.  `identity/oracle.c`
compiles `s1f_masks` out of `s1fuse.h`; `identity/ir-identity.sh` compares that
emission with the one `kernel/json/s1_block.c` produces; and both scripts run
under `--tree-only`, which refuses any input path outside this repository.  The
scratch tree is a convenience for the first vendoring and for the digests'
corroboration, never a dependency of the result.

## Read-only

No target builds these files.  No lint runs over them.  `identity/oracle.c` is
the only translation unit that includes them, and it exists to be compiled and
compared, never linked into anything shipped.  An edit to any of them is an edit
to the pinned set: it moves `SHA256SUMS` deliberately and it re-opens the
identity claim, which is why no change to `kernel/json/s1_block.c` may be
accompanied by a silent refresh of it.
