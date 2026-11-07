/* stub.c -- the staged cut for the route's red.

   It defines the ABI and nothing else: every mask word is zero and the carry
   slot is left untouched.  Linked in place of the kernel object, with nothing
   else moved, it is the cut that makes the route's driver disagree with the
   Lean body; the first failing row it produces is the red, and it is not a
   claim about the kernel, which is why it lives here and is never linked into
   anything the route ships.

   Build it with the measured compiler line and the same include path as the
   kernel, and link it in place of the kernel object:

     clang -O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-loops=64 \
       -falign-functions=64 -I kernel/json -c kernel/json/identity/stub.c
*/
#include "s1_block.h"

void leanllvm_json_s1_masks(const uint8_t *p, s1_carry *carry, s1_masks *out) {
    (void)p;
    (void)carry;
    out->quote = 0;
    out->delim = 0;
    out->in_string = 0;
    out->ws = 0;
    out->backslash = 0;
    out->ctl = 0;
}
