/* profile-num-slow.c -- the measured number path's third tier, as an opaque
   call.

   `profile-num-oracle.c` includes the vendored `numf_el1.h` at the measured
   configuration, whose third tier is `NUMF_SLOW` (`num_scan`/`strtod` in the
   measured build).  This file supplies that symbol from a different
   translation unit, so the compiler cannot fold the branch away and the
   oracle's emitted loop keeps the slow-path call the measured text has.  It
   counts the calls and refuses: the oracle models the first two tiers only,
   and the profile treats a reached third tier as a setup fault. */
#include <stddef.h>
#include <stdint.h>

static uint64_t g_profile_measured_slow;

int profile_slow(const uint8_t *p, uint64_t n, double *out, size_t *err) {
    (void)p;
    (void)n;
    (void)out;
    (void)err;
    g_profile_measured_slow++;
    return 0;
}

uint64_t profile_num_loop_measured_slow(void) { return g_profile_measured_slow; }
