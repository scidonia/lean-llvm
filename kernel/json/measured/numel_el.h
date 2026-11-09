/* numel_el.h -- Eisel-Lemire decimal -> double for w < 10^19, q in
   [EPOW_MIN, EPOW_MAX], with the rounding-bound test stated as a guard slice
   and the low half of the product computed only when it can change the answer.

   Requires epow_table.h (EPow, EPOW, EPOW_MIN, EPOW_MAX) to have been
   included already: numel.h or numel_bl.h both do that.

   The table entry is 10^q = (M + f) * 2^e with M = hi:lo in [2^127, 2^128)
   and 0 <= f < 1 (f == 0 for q >= 0; verified by vt.py).  With
       W  = w << lz                     (2^63 <= W < 2^64)
       A  = W * hi                      (128-bit, exact)
       B  = W * lo                      (128-bit, exact)
       c  = B >> 64, L = B & (2^64 - 1)
   the product is

       w * 10^q = U * 2^(e - lz),   U = H * 2^64 + L + g,
       H = A + c  (128-bit, exact),  g = W * f  in [0, 2^64).

   U is 191 or 192 bits wide; the double's 53-bit significand is
       m  = U >> (138 + ub),   ub = (U >= 2^191) = H >> 127
          = H >> (74 + ub) = hi64(H) >> (10 + ub),
   and the remainder below m, in units of 2^64, is
       r = hp * 2^64 + Rlo + (L + g) / 2^64,     hp = hi64(H) & mask(ub)
   against a half ulp of hh = 2^(9 + ub) at the same scale.  So:
       hp >  hh            -> above half, round up
       hp <  hh - 1        -> below half, round down
       hp == hh            -> above unless Rlo == L == 0 and g == 0 (a tie)
       hp == hh - 1        -> below unless Rlo * 2^64 + L + g >= 2^128
   The last two are the only places the low word is needed at all.

   For the deferred variant (num_el_el1) only A is computed, and the answer
   must be the one H would give for either value of the carry out of the low
   word (carry = 1 iff Alo + c >= 2^64).  Enumerating hp(A) with
   mask = 2*hh - 1:

     hp <= hh-3      down both ways                      -> decide
     hp == hh-2      carry moves it to hh-1, which the low word decides
     hp == hh-1      carry moves it to hh, same
     hp == hh        no carry gives the tie test, a carry gives "above"
     hp >= hh+1      above both ways                     -> decide
     hp == mask      no carry rounds up; with a carry the significand takes
                     the carry and hp wraps to 0, and both give m+1
     Ahi == 2^63-1   the only way H can cross 2^127; here hp == mask, and both
                     readings give (m, hp) = (2^53, *), which the rounding fold
                     turns into the same binade either way

   so the window is hp in [hh-2, hh], three of 1024 (ub = 0) or 2048 (ub = 1)
   guard values, and the low multiply runs only inside it.

   Anything outside the table range, subnormal, overflow, or a remainder
   indistinguishable from an exact tie returns 0 and leaves the decision to
   the caller's exact path. */
#ifndef NUMEL_EL_H
#define NUMEL_EL_H

#ifdef EL_ENTRY_NOINLINE
/* The tier-2 entry as an out-of-line call: it keeps the walker's code layout
   independent of the kernel it calls, at the price of a call per tier-2 value. */
#define EL_ENTRY static __attribute__((noinline))
#else
#define EL_ENTRY __attribute__((always_inline)) static inline
#endif

#define EL_MASK(ub) (0x3FFu | ((uint32_t)(ub) << 10))
#define EL_HALF(ub) (0x200u << (ub))

/* diagnostics: how often each exit is taken (the pipeline's counters) */
static uint64_t g_el_window, g_el_undec, g_el_range;

/* Significand, rounding direction, exponent and bit pattern from the guard
   slice: m is 53 bits, up is 0 or 1. */
__attribute__((always_inline)) static inline int el_pack(uint64_t m, unsigned up, unsigned ub,
                                                         const EPow *t, unsigned lz, double *out) {
    uint64_t mm = m + up;
    unsigned ov = (unsigned)(mm >> 53);      /* rounding carried into the next binade */
    unsigned sh = 10u + ub + ov;
    int eu = 180 + (int)sh + t->e - (int)lz;
    if (eu > 1023 || eu < -1022) { g_el_range++; return 0; }   /* overflow / subnormal */
    uint64_t bits = ((uint64_t)(eu + 1023) << 52) | (mm & ((1ULL << 52) - 1));
    double d;
    memcpy(&d, &bits, 8);
    *out = d;
    return 1;
}

/* Both halves of the product: the exact decision, branchless rounding. */
__attribute__((always_inline)) static inline int el_exact(uint64_t W, unsigned lz, const EPow *t,
                                                          int64_t q, double *out) {
    unsigned __int128 A = (unsigned __int128)W * t->hi;
    unsigned __int128 B = (unsigned __int128)W * t->lo;
    uint64_t Alo = (uint64_t)A, Ahi = (uint64_t)(A >> 64);
    uint64_t L = (uint64_t)B, c = (uint64_t)(B >> 64);
    uint64_t Rlo = Alo + c;
    uint64_t Rhi = Ahi + (Rlo < Alo);        /* hi64(H) */
    unsigned ub = (unsigned)(Rhi >> 63);
    unsigned sh = 10u + ub;
    uint64_t m = Rhi >> sh;
    uint64_t hp = Rhi & EL_MASK(ub);
    uint64_t hh = EL_HALF(ub);
    unsigned tie = (hp == hh);
    unsigned close = (hp == hh - 1);
    /* a tie is possible only when the dropped significand is zero, and only
       q < 0 can hide one (g > 0 is not guaranteed); at hp == hh - 1 only
       Rlo == 2^64 - 1 can be pushed over by L + g */
    unsigned undec = ((tie & ((Rlo | L) == 0u)) |
                      (close & (Rlo == ~(uint64_t)0))) & (unsigned)(q < 0);
    if (__builtin_expect(undec != 0, 0)) { g_el_undec++; return 0; }
    unsigned up = (unsigned)(hp > hh) | (tie & (unsigned)(((Rlo | L) != 0u) | (m & 1)));
    return el_pack(m, up, ub, t, lz, out);
}

/* Full precision: both multiplies on every value. */
__attribute__((always_inline)) static inline int num_el_el2(uint64_t w, int64_t q, double *out) {
    if (q < EPOW_MIN || q > EPOW_MAX) return 0;
    if (w == 0) { *out = 0.0; return 1; }
    unsigned lz = (unsigned)__builtin_clzll(w);
    return el_exact(w << lz, lz, &EPOW[q - EPOW_MIN], q, out);
}

/* The rare path, out of line and cold: keeping it out of the fast path's
   register allocation is worth more than its own icache footprint. */
__attribute__((noinline, cold)) static int el_exact_cold(uint64_t W, unsigned lz, const EPow *t,
                                                         int64_t q, double *out) {
    return el_exact(W, lz, t, q, out);
}

/* Deferred: one 64x64 multiply on the fast path, the second only inside the
   bound window, where the exact decision is re-made from both halves. */
EL_ENTRY int num_el_el1(uint64_t w, int64_t q, double *out) {
    if (q < EPOW_MIN || q > EPOW_MAX) return 0;
    if (w == 0) { *out = 0.0; return 1; }
    const EPow *t = &EPOW[q - EPOW_MIN];
    unsigned lz = (unsigned)__builtin_clzll(w);
    uint64_t W = w << lz;
    unsigned __int128 A = (unsigned __int128)W * t->hi;
    uint64_t Ahi = (uint64_t)(A >> 64);
    unsigned ub = (unsigned)(Ahi >> 63);
    unsigned sh = 10u + ub;
    uint64_t hp = Ahi & EL_MASK(ub);
    uint64_t hh = EL_HALF(ub);
    if (__builtin_expect(hp - (hh - 2) <= 2, 0)) {
        g_el_window++;
        return el_exact(W, lz, t, q, out);
    }
    return el_pack(Ahi >> sh, (unsigned)(hp > hh), ub, t, lz, out);
}

/* Same, with the rare path out of line: the fast path stays a leaf. */
__attribute__((always_inline)) static inline int num_el_el1c(uint64_t w, int64_t q, double *out) {
    if (q < EPOW_MIN || q > EPOW_MAX) return 0;
    if (w == 0) { *out = 0.0; return 1; }
    const EPow *t = &EPOW[q - EPOW_MIN];
    unsigned lz = (unsigned)__builtin_clzll(w);
    uint64_t W = w << lz;
    unsigned __int128 A = (unsigned __int128)W * t->hi;
    uint64_t Ahi = (uint64_t)(A >> 64);
    unsigned ub = (unsigned)(Ahi >> 63);
    unsigned sh = 10u + ub;
    uint64_t hp = Ahi & EL_MASK(ub);
    uint64_t hh = EL_HALF(ub);
    if (__builtin_expect(hp - (hh - 2) <= 2, 0))
        return el_exact_cold(W, lz, t, q, out);
    return el_pack(Ahi >> sh, (unsigned)(hp > hh), ub, t, lz, out);
}

/* Both halves, the rounding test as a branch chain (the shape numel.h has, for
   attributing the cost of the test itself). */
__attribute__((always_inline)) static inline int num_el_el2b(uint64_t w, int64_t q, double *out) {
    if (q < EPOW_MIN || q > EPOW_MAX) return 0;
    if (w == 0) { *out = 0.0; return 1; }
    const EPow *t = &EPOW[q - EPOW_MIN];
    unsigned lz = (unsigned)__builtin_clzll(w);
    uint64_t W = w << lz;
    unsigned __int128 A = (unsigned __int128)W * t->hi;
    unsigned __int128 B = (unsigned __int128)W * t->lo;
    uint64_t Alo = (uint64_t)A, Ahi = (uint64_t)(A >> 64);
    uint64_t L = (uint64_t)B, c = (uint64_t)(B >> 64);
    uint64_t Rlo = Alo + c;
    uint64_t Rhi = Ahi + (Rlo < Alo);
    unsigned ub = (unsigned)(Rhi >> 63);
    unsigned sh = 10u + ub;
    uint64_t m = Rhi >> sh;
    uint64_t hp = Rhi & EL_MASK(ub);
    uint64_t hh = EL_HALF(ub);
    unsigned up;
    if (hp > hh) up = 1;
    else if (hp + 1 < hh) up = 0;
    else if (hp == hh) {
        if (Rlo | L) up = 1;
        else if (q >= 0) up = (unsigned)(m & 1);
        else return 0;
    } else {
        if (q < 0 && Rlo == ~(uint64_t)0) return 0;
        up = 0;
    }
    return el_pack(m, up, ub, t, lz, out);
}

#endif
