/* policy.h -- the character-policy scan's one public entry point.

   The rule is `policyRefusal`'s (`LeanLLVM/JsonKernelDomain.lean`): run the
   reference's own string-body scanner (`scanCharsEnd`) at every byte of the
   document that is `"`, and report the first body scan that refuses under
   RFC 7493 §2.1 -- an unpaired surrogate escape, or a noncharacter -- at the
   byte the reference names.  This unit answers the same question, over the same
   bytes, as a native scan; `policy.c` states what it reproduces and
   `probes/json/route/check.sh` compares the two per corpus row.

   `cls` is one of `POLICY_NONE`, `POLICY_UNPAIRED` and `POLICY_NONCHARACTER`,
   and `pos` is the document byte the refusal is reported at (the `pos` field of
   `KernelRefusal.unpairedSurrogate` and `.noncharacter`), meaningful only when
   `cls` is not `POLICY_NONE`.  The return value is 0 for a measured answer and
   -1 when the scan could not allocate its class array, which the caller must
   report rather than read as `POLICY_NONE`.

   The unit reads `b[0 .. n-1]` and no byte past it, allocates nothing for a
   document whose blocks fit its stack class array, and reads the document
   once when no character-policy refusal is possible in it (see `policy.c`). */
#ifndef LEANLLVM_ROUTE_POLICY_H
#define LEANLLVM_ROUTE_POLICY_H

#include <stdint.h>

/* The class of a character-policy refusal. */
#define POLICY_NONE 0
#define POLICY_UNPAIRED 1
#define POLICY_NONCHARACTER 2

int leanllvm_route_policy_scan(const uint8_t *b, uint64_t n, uint64_t *cls,
                               uint64_t *pos);

#endif
