/* pipeline_fast.h -- the benchmark-only full-pipeline candidate's entries.

   `kernel/json/pipeline_fast.c` is the stage-1 candidate
   `tests/json-units-bench/bench-contract.c` measures as `splitfast3_u8`: the
   list-free fast classifier that keeps the mask words and both carries in
   registers, the UTF-8 gate fused over the vectors the classifier already
   loaded, the three-slot entry emitter, and the entry stream handed to the
   unchanged stage 2.  The default `leanllvm_json_pipeline` (`pipeline.h`) is
   not touched by this file's existence and remains the route's certified
   path; these entries exist so a harness can time and diff the candidate
   against it on the same document.

   One entry is that list-free shape (`leanllvm_json_pipeline_fast`); the
   second (`leanllvm_json_pipeline_fast_list`) adds the stage-1 escape list and
   leaves its count for stage 2, so the list-driven decoder can be measured
   against the list-free rescan.  A third (`leanllvm_json_pipeline_fast_best`)
   dispatches to one of those or to `pipeline_fast_plain.h`'s pos8 entry from a
   bounded prefix scan, so the per-document best the C ranking found can be
   measured as one entry.  All three share the ABI below.

   ## No refinement theorem

   Unlike `leanllvm_json_pipeline`, none of the three entries has a refinement
   theorem or a contract object in `LeanLLVM/Refinement`: the composition of
   the fused classifier, its inline UTF-8 gate and the three-slot emitter has
   not been proved against `JsonPipelineSpec`.  Their observable equivalence to
   the default is the gate over the corpus, not a proof.  A caller that needs
   the certified route calls `leanllvm_json_pipeline`.

   ## What is reused, and what is the candidate's own

   - The classifier's arithmetic is the tree's: `s1_block_impl.h`'s
     `s1f_escaped`, `s1f_prefix_xor` and its two classification tables, driven
     by a local block function (`pf_masks`) that keeps the words in registers
     instead of storing the six-word slot.  The list-free entry forms the
     unescaped-quote, structural, in-string and *neither* words; the raw
     backslash word is consumed by `s1f_escaped` and not returned, and
     whitespace and control are never computed, because neither its
     composition nor stage 2 reads them.  The list entry forms the same four
     words, returns the raw backslash word `s1f_escaped` already computes, and
     adds the control-byte word, because those three are what
     `leanllvm_json_escape_list` takes; nothing else about the composition
     changes.  The four words give the same entry word as the staged loop's
     six: the scalar word is `~(quote | delim | in_string | ws)` there and
     `neither & ~quote & ~in_string` here, and `neither` is exactly
     `~(delim | ws)`.
   - The UTF-8 gate is `measured/u8kl.h`'s load form (`kl_err_vec_ld` and
     `kl_tail_byte`), called over the same two vectors the classifier already
     loaded.  The header is included rather than copied, so the tables have one
     source -- the one `utf8.c`'s identity arm pins -- and this file carries no
     third copy to drift.  The gate is exactly `leanllvm_json_utf8(b, n, 0)`'s:
     a block skips the DFA when it and its predecessor are all ASCII, and the
     document-end tail byte is checked after the loop.  The word it produces is
     the unit's word, not a second rule.
   - The entry emitter is the tree's `leanllvm_json_entry_b3` (`entry.h`).
   - The entry word's composition (the scalar word and its run starts, the
     entry word, and the tail clamp) is the pipeline's own three lines,
     `JsonScanSpec.entryMask64` and `limMask`, exactly as in `pipeline.c`.
   - The second half of the verdict is the tree's `leanllvm_json_stage2`
     (`stage2.h`), called with the same entry stream, the entry's `xp`/`*nxp`
     (empty for the list-free entry, the built list for the list entry), and
     the caller's arena and event buffers and cursors.

   ## The ABI

   The document is `b .. b+n-1`.  The caller stages:

     - `ent`: `(n + 63) >> 6` `uint64_t`s, one entry word per 64-byte block.
       It is the candidate's only caller-staged scratch beyond the default's
       output buffers: the default's `sc`, `mk` and `entw` slots do not exist
       here (the mask words and the classifier's carry stay in registers, and
       the entry word is written straight into `ent` for the one emitter call),
       and the escape-list carry, which the default receives in `xcarry`, is
       the list entry's own local zeroed at the first block;
     - `ep` with capacity `*nk + 64 * ((n + 63) >> 6) + 8` `uint32_t`s and
       cursor `*nk`.  The emitter's group stores reach up to three words past
       the final cursor, and the eight-word slack is the entry unit's rule
       (`entry.h`);
     - `dst` with capacity `dstcap` and cursor `*ndst`, and `ev` with capacity
       `evcap` and cursor `*nev`, whose promises are `stage2.h`'s;
     - `xp` with capacity `xpcap` and count `*nxp`.  The list-free entry has no
       escape-list arm: it writes neither `xp` nor `*nxp` and passes both to
       stage 2 unchanged, exactly as `leanllvm_json_pipeline` does with arm bit
       1 clear.  The list entry appends this document's positions at `*nxp` and
       passes the updated count; its capacity rule is in "The list arm" below.
       A caller of the best entry stages `xp` at that list capacity, because
       the choice is the document's.  `xpcap` is accepted for signature parity
       with the default and is ignored by all three, as it is there.

   `*err` is the first error offset on a refusal and is not written on
   acceptance.  The UTF-8 refusal keeps the default's document-end rule: a
   non-zero fused word sets `*err = n` and returns `0`, after the entry stream
   has been written, because the default writes it before its UTF-8 call.

   ## Staging the document

   The block loop reads 64 bytes per block unconditionally and the fused gate's
   three shift loads read `p-3 .. p-1`, so, as `utf8.h` and `s1_blocks.h`
   require, `3 <= b`, the three bytes `b-3 .. b-1` read as zero, and
   `b+n .. 64*((n+63)>>6)-1` is readable and zero.  Entry positions are 32-bit,
   so a document at or above 2^32 bytes truncates, as `entry.h` states.

   ## How a caller selects it

   Call `leanllvm_json_pipeline_fast` where it would call
   `leanllvm_json_pipeline` with `arm == 0`, and
   `leanllvm_json_pipeline_fast_list` where it would call the default with arm
   bit 1 set.  Neither candidate takes an arm word: each entry is one fixed
   shape, and both emit with `b3`.

   The default comparison's arm bit 0 is the default's own emitter selection,
   not the candidate's: with the bit clear the default emits with pos8, and
   that call requires `leanllvm_json_entry_table` first (`pipeline.h`); with
   the bit set it emits with b8 and has no table obligation.  Because both
   candidates emit with `b3`, they read no entry-unit table and carry no
   `leanllvm_json_entry_table` obligation of their own.

   ## The list arm

   `leanllvm_json_pipeline_fast_list` is the same stage-1 pass with the
   list-free classifier's control-byte word added and, per block,
   `leanllvm_json_escape_list` called on the block's raw-backslash,
   control-byte and in-string words.  The list's carry is the pass's own, both
   words zero at the document's first block, so the caller stages no carry and
   the ABI is the list-free entry's.  The entry writes `xp` and `*nxp` and
   passes them to stage 2, which then takes its list-driven decoder instead of
   scanning each string body.

   `xp` must hold `*nxp + 64 * ((n + 63) >> 6) + 8` entries: one block cannot
   hold more than 64 positions, and the list unit's eight-entry batch writes
   its whole slot run past the true count (`escape.h`).  Only `[0, *nxp)` after
   the call is the stream.  A document with no escapes gets an empty list; the
   arm is a policy selector and not an escape-position test.

   The list-free entry is unchanged by this arm: it computes no control word,
   calls no list unit, and passes `xp`/`*nxp` through untouched.

   ## The best entry

   `leanllvm_json_pipeline_fast_best` chooses one of the pipeline entries per
   document and calls it unchanged, so its output is the chosen entry's
   standalone output by construction:

     - a high byte in the prefix: UTF-8, `leanllvm_json_pipeline_fast`;
     - otherwise a backslash in the prefix: strings, at or below 64 KiB
       (`n <= 65536`) `leanllvm_json_pipeline_fast`, above it
       `leanllvm_json_pipeline_fast_list`;
     - otherwise dense: `leanllvm_json_pipeline_fast_plain_pos8`
       (`pipeline_fast_plain.h`).

   The detector reads at most the first 128 document bytes and only bytes the
   chosen entry's own pass reads: the first 64-byte block whenever `n > 0`, and
   the second block only when `n > 64`.  Each block is two 32-byte loads, two
   `cmpeq`/`movemask` pairs for the backslash, and one OR; the blocks' ORs feed
   a second, and one `testz` answers the high-bit question over all 128 bytes.
   The cost is independent of the document's length -- a handful of vector
   ops, well under 0.01% of a 64 KiB pass and a few nanoseconds beside the
   smallest selected document -- and `n == 0` is dense without a load.  The
   second block is inside the staging window the first block already requires:
   `64 * blocks + 32` readable bytes after `b`, and `n > 64` implies at least
   two blocks.

   The separation is the measured corpus's: on the 99 documents the C ranking
   used, the first backslash of a strings document is at offset 74-115 and the
   first high byte of a UTF-8 document at offset 7-28, so 128 bytes separates
   every one of them; a dense document carries neither.  A document that mixes
   the classes falls to the class of its prefix; the choice moves the timing
   and never the output.

   The gate follows the choice.  A dense or non-list choice is compared against
   the default at `arm == 0` on the fields "What a harness compares" lists,
   with `*nxp == 0` and `xp` unchanged; the list choice is compared at
   `arm == 2`, with `*nxp` and `xp[0 .. *nxp)` added.  The chosen arm is
   observable without asking the detector: a non-zero `*nxp` means the list
   entry ran, and a zero count is compared at arm 0, where an empty list's arm
   agrees on every consumer-visible field (`probes/json/route/guard.sh`).  The
   claim is a speed claim only; the output's identity is the chosen entry's,
   which that entry's own gate establishes.

   ## What a harness compares

   Same document, freshly staged cursors and buffers:

     - the list-free entry against the default with `arm == 0`: the fields
       below, with `xp` and `*nxp` left exactly as the caller staged them;
     - the list entry against the default with the list bit set (`arm == 2`,
       with `arm == 0`'s `leanllvm_json_entry_table` obligation met): the same
       fields, plus `*nxp` and `xp[0 .. *nxp)`, the escape positions the
       default's `arm & 2` call appends.

   The fields, for either entry:

     - the return value (the verdict);
     - `*err`, when the verdict is `0`;
     - `*nk` and `ep[0 .. *nk)`, the entry positions in order;
     - `*ndst` and `dst[0 .. *ndst)`;
     - `*nev` and `ev[0 .. *nev)`.

   Bytes past those extents are the emitters', the list unit's and stage 2's
   slack and are not part of the comparison.  The `ent` words are the
   candidate's internal scratch; comparing them against the default's
   per-block entry word is a diagnostic, not an observable field.  The fused
   UTF-8 word is not exported: it reaches the harness through the verdict and
   `*err`, which the default derives from `leanllvm_json_utf8(b, n, 0)` on the
   same document, so the comparison above covers it.

   ## The gate

   Neither entry is reported without its gate.  The adapter's
   `leanllvm_route_gate_candidate` (`probes/json/route/shim.c`) runs once
   before each candidate mode's timing loop, from the same fresh staging as the
   default, and a difference exits nonzero before a row is printed:

     - `--consume-reuse-fast` gates `leanllvm_json_pipeline_fast` against
       `arm == 0`, with `*nxp` and the whole `xp` buffer required back
       unchanged;
     - `--consume-reuse-fast-list` gates `leanllvm_json_pipeline_fast_list`
       against `arm == 2`, with `*nxp` and `xp[0 .. *nxp)` compared against the
       default's list stream.

   The gate is the only equivalence claim these entries have; a row from either
   mode is a gated row. */
#ifndef LEANLLVM_KERNEL_JSON_PIPELINE_FAST_H
#define LEANLLVM_KERNEL_JSON_PIPELINE_FAST_H

#include <stdint.h>

uint64_t leanllvm_json_pipeline_fast(const uint8_t *b, uint64_t n,
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

uint64_t leanllvm_json_pipeline_fast_list(const uint8_t *b, uint64_t n,
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

uint64_t leanllvm_json_pipeline_fast_best(const uint8_t *b, uint64_t n,
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
