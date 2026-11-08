/* entry_oracle.c -- the measured side of the entry unit's IR identity arm.

   It includes the vendored measured headers and calls `s1f_k_pos8` and
   `s1f_k_b8` through their measured signatures, which is what makes the two
   block loops part of the emitted module: both are `static __attribute__
   ((noinline))`, so a call reaches them, and an unreferenced one is removed by
   the backend before `llvm-extract` could see it.

   The table's initialiser is made reachable rather than assumed.  Under `-O3`
   the initialiser is inlined into the constructor below, and with no reachable
   call the array is never written, everything reads zero and the global folds
   out of the module -- so the emission a probe without this constructor
   produced would not be the emission the measurement ran.  The constructor is
   outside the timed region and outside the two lifted functions, and both
   sides carry an identical one.

   `S1F_UTF8` is left at the header's default 0: the UTF-8 stage is a different
   unit, and no identity claim here reaches it.  The rest of the measured `-D`
   set (`build49.sh:19-21`) is passed by `ir-identity.sh --unit entry`;
   `S1F_EXP2=11` among them is what builds the kernel region at all, and the
   two switches above the emitters leave `s1f_ke_b4` and the `SP45_MODES`
   instantiations out of the module exactly as the measured build does. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

#include "../measured/s1fuse.h"

#if S1F_EXP2 != 11
#error "compile entry_oracle.c with -DS1F_EXP2=11, the measured configuration (build49.sh:19)"
#endif

uint64_t entry_stream_probe(uint64_t *ent, uint64_t blk0, uint64_t nblk,
                            uint32_t *out, uint64_t k, int kern) {
    return kern ? s1f_k_b8(ent, blk0, nblk, out, k)
                : s1f_k_pos8(ent, blk0, nblk, out, k);
}

__attribute__((constructor)) static void entry_oracle_init(void) {
    xl_pos8_init();
}
