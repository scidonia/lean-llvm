/* entry_probe.c -- the extracted side of the entry unit's IR identity arm.

   The translation unit is `entry.c` itself, included so `llvm-extract` lifts
   the unit's own `s1f_k_pos8` and `s1f_k_b8` rather than a copy of them; the
   probe below is `entry_oracle.c`'s signature, character for character, and is
   the only thing this file adds.

   Both kernels are already called by the unit's two wrappers, so they are in
   the module without the probe; the probe is here so the two sides' modules are
   built the same way and so a wrapper that stopped calling a kernel fails the
   lift instead of silently comparing one function twice. */
#include "../entry.c"

uint64_t entry_stream_probe(uint64_t *ent, uint64_t blk0, uint64_t nblk,
                            uint32_t *out, uint64_t k, int kern) {
    return kern ? s1f_k_b8(ent, blk0, nblk, out, k)
                : s1f_k_pos8(ent, blk0, nblk, out, k);
}
