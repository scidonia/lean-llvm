/* pipeline_fast_plain.h -- the benchmark-only split-stage-1 pipeline entries.

   `kernel/json/pipeline_fast_plain.c` is the full pipeline over the
   `split_plain` stage-1 shape `tests/json-units-bench/bench-contract.cc`
   times: the staged classifier (`leanllvm_json_s1_masks`) computes the block's
   six words into a function-local slot, the entry word is composed exactly as
   `pipeline.c` composes it, the words are collected into the caller's `ent`,
   one entry-emitter call turns the array into the entry stream, and the
   document is then handed to the tree's `leanllvm_json_utf8` sweep and to the
   unchanged `leanllvm_json_stage2`.  The bench times this shape as
   `split_plain`, whose rows are in
   `tests/json-units-bench/string-classifier-transcript.txt`.  The default
   `leanllvm_json_pipeline` (`pipeline.h`) is untouched and remains the route's
   certified path.

   The bench times `split_plain` with the harness's per-document emitter:
   `pos8` on the dense documents and `b8` on the strings and UTF-8 documents.
   The emitter is a stage-1 selection and not part of the shape, so this file
   exports both, and a caller pairs each document with the emitter the bench
   used for its class.  Both entries have `pipeline_fast.h`'s ABI and fields.

   ## The proved body, and the exported entries

   `pf_plain_pipeline` is the split-stage-1 body at the *certified* pipeline's
   twenty-slot ABI: it takes the two caller-staged stage-1 slots (`sc` 24 B,
   `mk` 48 B), the `ent` array in the `entw` slot, the cursors and the `arm`
   selector, and has no `alloca`.  It is the pin target for the body's
   `Satisfies` (`probes/install/ir/pipeline_fast_plain.candidate.ll`); the one
   staging difference from `pipeline.c` is that the `entw` slot is the
   `(n+63)>>6`-word array, so the route stages `8 * pipelineBlocks n` bytes
   there.

   The exported `_pos8`/`_b8` entries keep the sixteen-argument ABI below and
   are the *caller* of that body: each stages `sc`/`mk`/`xcarry` as zeroed
   locals and passes `arm = 0`/`1`.  The harness's gate over the corpus is what
   relates the entries to the default; the body theorem is about
   `pf_plain_pipeline`, not the wrappers.

   ## The ABI

   The document is `b .. b+n-1`.  The caller stages:

     - `ent`: `(n + 63) >> 6` `uint64_t`s, one entry word per 64-byte block.
       It is the only caller-staged scratch: the classifier's carry and six-word
       slot are function locals, as the bench's `split_plain` keeps them;
     - `ep` with capacity `*nk + 64 * ((n + 63) >> 6) + 8` `uint32_t`s and
       cursor `*nk`.  POS8 writes whole eight-lane groups and its last group in
       a block can reach `k' + 7`, which the eight-word slack covers
       (`entry.h`);
     - `dst` with capacity `dstcap` and cursor `*ndst`, and `ev` with capacity
       `evcap` and cursor `*nev`, whose promises are `stage2.h`'s;
     - `xp` and `*nxp`.  This shape is list-free: the entry writes neither and
       passes both to stage 2 unchanged, exactly as `leanllvm_json_pipeline`
       with arm bit 1 clear.  `xpcap` is accepted for signature parity and
       ignored.

   `*err` is the first error offset on a refusal and is not written on
   acceptance.  The UTF-8 refusal keeps the default's rule: a non-zero
   `leanllvm_json_utf8` word sets `*err = n` and returns `0`, after the entry
   stream has been written.

   ## Staging the document and the emitter's obligation

   The classifier reads 64 bytes per block unconditionally, and the UTF-8 unit
   requires `3 <= b`, the three bytes `b-3 .. b-1` readable and zero, and
   `b+n .. 64*((n+63)>>6)-1` readable and zero (`utf8.h`).  Entry positions are
   32-bit, so a document at or above 2^32 bytes truncates (`entry.h`).

   `leanllvm_json_pipeline_fast_plain_pos8` emits with
   `leanllvm_json_entry_pos8`, which reads the entry unit's static table and
   traps if it is unfilled: a caller must call `leanllvm_json_entry_table`
   once before its first pos8 call (`entry.h`).  The `_b8` entry reads no table
   and carries no such obligation.

   ## How a caller selects it

   Call `leanllvm_json_pipeline_fast_plain_pos8` or
   `leanllvm_json_pipeline_fast_plain_b8` where it would call
   `leanllvm_json_pipeline` with `arm == 0`, using the emitter the bench paired
   with the document's class.  There is no arm argument and no runtime switch.

   ## What a harness compares

   Same document, freshly staged cursors and buffers, default with `arm == 0`
   (and the table initialised for pos8): the return value; `*err` when the
   verdict is `0`; `*nk` and `ep[0 .. *nk)` in order; `*nxp` and `xp`, which
   both entries must leave as they were; `*ndst` and `dst[0 .. *ndst)`; `*nev`
   and `ev[0 .. *nev)`.

   Bytes past those extents are the emitter's and stage 2's slack and are not
   part of the comparison.  The `ent` words are internal scratch and are a
   diagnostic only.

   ## The gate

   Neither entry is reported without its gate.  The adapter's
   `leanllvm_route_gate_candidate` (`probes/json/route/shim.c`) runs once
   before each mode's timing loop, from the same fresh staging as the default
   at `arm == 0`, and a difference exits nonzero before a row is printed:

     - `--consume-reuse-fast-plain-pos8` gates
       `leanllvm_json_pipeline_fast_plain_pos8`;
     - `--consume-reuse-fast-plain-b8` gates
       `leanllvm_json_pipeline_fast_plain_b8`.

   The pos8 entry's `leanllvm_json_entry_table` obligation is the caller's; the
   adapter's `route_init` fills the table before the gate's first default or
   candidate call.  The gate is the only equivalence claim these entries
   have. */
#ifndef LEANLLVM_KERNEL_JSON_PIPELINE_FAST_PLAIN_H
#define LEANLLVM_KERNEL_JSON_PIPELINE_FAST_PLAIN_H

#include <stdint.h>

uint64_t leanllvm_json_pipeline_fast_plain_pos8(const uint8_t *b, uint64_t n,
                                                uint64_t *ent,
                                                uint32_t *ep, uint64_t epcap,
                                                uint64_t *nk,
                                                uint32_t *xp, uint64_t xpcap,
                                                uint64_t *nxp,
                                                uint8_t *dst, uint64_t dstcap,
                                                uint64_t *ndst,
                                                uint8_t *ev, uint64_t evcap,
                                                uint64_t *nev,
                                                uint64_t *err);

uint64_t leanllvm_json_pipeline_fast_plain_b8(const uint8_t *b, uint64_t n,
                                              uint64_t *ent,
                                              uint32_t *ep, uint64_t epcap,
                                              uint64_t *nk,
                                              uint32_t *xp, uint64_t xpcap,
                                              uint64_t *nxp,
                                              uint8_t *dst, uint64_t dstcap,
                                              uint64_t *ndst,
                                              uint8_t *ev, uint64_t evcap,
                                              uint64_t *nev,
                                              uint64_t *err);

#endif
