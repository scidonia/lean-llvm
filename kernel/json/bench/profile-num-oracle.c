/* profile-num-oracle.c -- the measured side of the number-path comparison.

   `profile-pipeline.cc` times the same document's number tokens through two
   conversions: the extracted walk's `num_fast_el1` (in the generated copy of
   `stage2.c`) and the measured text this file holds.  This file includes only
   the vendored `measured/numf_el1.h` at the measured configuration, so the
   two sides do not share a header and a difference cannot come from one
   include path.

   `NUMF_SLOW` is the measured chain's third tier (`num_scan`/`strtod` in the
   measured build).  This oracle does not carry `p6.c`, so its third tier is a
   counter and a refusal instead: the differential is a measurement of the
   first two tiers, and the driver refuses to report a row whose document
   reaches the third (the corpus census shows none of the seven does).  A
   document that did would be a setup fault, not a slower conversion.

   The loop returns `ok ^ h`, where `h` folds every converted double's bits,
   so the driver's equality check compares the values and not only the count.
   The same fold and the same addition order are in the extracted loop, in
   `profile-pipeline.sh`'s appended block. */
#include <immintrin.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

/* The third tier is a call into a separate translation unit, so the compiler
   cannot see that it always fails and fold the branch: the loop this file
   emits has the same slow-path call the measured text has, and the extracted
   loop's `num_scan` call is the counterpart the IR comparison expects. */
int profile_slow(const uint8_t *p, uint64_t n, double *out, size_t *err);

#define NUMF_SLOW profile_slow
#include "numf_el1.h"

typedef struct { uint32_t pos, len; } profile_tok;

uint64_t profile_num_loop_measured(const uint8_t *doc, const profile_tok *t,
                                   uint64_t nt, volatile double *sink) {
    double acc = 0.0;
    uint64_t ok = 0, h = 0;
    size_t err = 0;
    for (uint64_t j = 0; j < nt; j++) {
        double d = 0.0;
        if (num_fast_el1(doc + t[j].pos, t[j].len, &d, &err)) {
            uint64_t u;
            memcpy(&u, &d, 8);
            h = (h ^ u) * 0x9E3779B97F4A7C15ULL;
            acc += d;
            ok++;
        }
    }
    *sink = acc;
    return ok ^ h;
}

/* `profile_num_loop_measured_slow` lives in profile-num-slow.c with the stub,
   so this file sees only a declaration of both. */
