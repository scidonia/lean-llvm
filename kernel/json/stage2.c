/* stage2.c -- the stage-2 unit: `s2_walk`'s per-entry dispatch over the entry
   stream, writing the caller's event stream and arena and the first error
   offset.

   The walk, the string body, the value-position and after-value rules, the
   cursor's value helpers, the zero-copy string scan, the event encoding and the
   number conversion are the measured text of kernel/json/measured/s2port.h,
   p16.c, strz.c, p6.c and the `num*`/`num_el` chain, at the measured `-D` set
   (build49.sh:19-21, `m49`), with the arms that set does not take deleted
   (README.md's `stage2-delete:` rows; `identity/source-identity.sh --unit
   stage2` applies them and diffs).  The entities keep their measured names and
   signatures, so the token diff and the IR diff compare the measured functions
   rather than a re-spelling of them.

   Three representation adaptations, each forced by the ABI `stage2.h`
   declares, and one change of the conversion itself; all four are recorded in
   README.md rather than made silently:

     - the arena and the event stream are the caller's.  `ZOut.ar/alen/acap`
       bind to `dst`, `*ndst` and `dstcap`, and `Out.b/len/cap` of `z->ev` bind
       to `ev`, `*nev` and `evcap`, so an arena record's offset is an offset
       into `dst` and each cursor appends to the caller's.  The measured
       `z_arena_reserve` and `out_reserve` reallocated; here the capacity is the
       caller's, stated in `pre`, and a reserve that would exceed it traps --
       a loud failure on a violated promise, never a behaviour the unit models.

     - the escaped body's decoder is the escape unit's ABI entry point,
       `leanllvm_json_escape_expand`, not a copy of `us_dec_x`.  The measured
       per-body call is the same signature and the same semantics the escape
       unit publishes (`escape.h`), which is what makes the composition
       `stage2 -> escape_expand` a call and not a duplicate.

     - the flags are fixed at the pipeline's call site: `S2_VAL | S2_STR |
       S2_EV`, so the walk validates, validates string bodies and materialises
       events, which is the post `pipeline.h` describes.

     - the number conversion's third tier is this unit's own rather than the C
       library's.  The measured `to_double` copied the lexeme into a 64-byte
       buffer and called `strtod`, allocating the copy when the lexeme did not
       fit; `to_double` here reads at most 768 significant digits plus one
       sticky bit and rounds once, so it allocates nothing and admits no length
       bound.  Its body is therefore new text, not the measured function's.

   Nothing else is new text.  `leanllvm_json_stage2` at the end of this file is
   the ABI wrapper: it stages the caller's buffers into the measured `ZOut` and
   reports the walk's own verdict and refusal offset. */
#include "stage2.h"

#include "escape.h"

#include <immintrin.h>
#include <stdint.h>
#include <string.h>

/* The shipped decoder's slack (`usdec.h:497-500`, `US_EMIT4=1`), which the
   caller's arena must carry past the decoded extent. */
#define US_SLACK 64

/* --------------------------------------------- encoding and reference text -- */
/* kernel/json/measured/p6.c: the event encoding, the reference checks and the
   number grammar's slow path. */

typedef struct {
    int ok;
    uint64_t off;
    const char *msg;
} Err;

static void err_set(Err *e, uint64_t off, const char *msg) {
    e->ok = 0;
    e->off = off;
    e->msg = msg;
}

/* --------------------------------------------------------------------- out -- */
#define PRIME 0x9E3779B97F4A7C15ULL

typedef struct {
    uint8_t *b;
    size_t len, cap;
    uint64_t h;
    int hash;                       /* 1: accumulate a checksum, do not store */
} Out;

static void out_init(Out *o, int hash) {
    memset(o, 0, sizeof *o);
    o->hash = hash;
}
static void out_reserve(Out *o, size_t need) {
    /* The event stream is the caller's: its capacity is a `pre` clause,
       not a growth.  The measured body reallocated here; a caller that
       under-reserves is outside the unit's domain, and overrunning its
       buffer would be the silent form of that failure, so the
       violation is loud instead. */
    if (o->len + need <= o->cap) return;
    __builtin_trap();
}

static inline void hup(Out *o, const void *p, size_t n) {
    const uint8_t *q = (const uint8_t *)p;
    uint64_t h = o->h;
    size_t i = 0;
    while (i + 8 <= n) {
        uint64_t w;
        memcpy(&w, q + i, 8);
        h = (h ^ w) * PRIME;
        i += 8;
    }
    if (i < n) {
        uint64_t w = 0;
        for (size_t j = 0; j < n - i; j++) w |= (uint64_t)q[i + j] << (8 * j);
        h = (h ^ w) * PRIME;
    }
    o->h = (h + (uint64_t)n) * PRIME;
}

static inline void out_raw(Out *o, const void *p, size_t n) {
    if (o->hash) { hup(o, p, n); return; }
    out_reserve(o, n);
    memcpy(o->b + o->len, p, n);
    o->len += n;
}

static inline void out_tag(Out *o, uint8_t t) { out_raw(o, &t, 1); }
static inline void out_u64(Out *o, uint64_t v) {
    uint8_t b[8];
    for (int i = 0; i < 8; i++) b[i] = (uint8_t)(v >> (8 * i));
    out_raw(o, b, 8);
}

enum {
    T_OBJ = 1, T_OBJ_END = 2, T_ARR = 3, T_ARR_END = 4,
    T_KEY = 5, T_STR = 6, T_NUM = 7, T_TRUE = 8, T_FALSE = 9, T_NULL = 10
};

static uint64_t dbits(double d) {
    uint64_t u;
    memcpy(&u, &d, 8);
    return u;
}

/* ------------------------------------------------------------------ lexing -- */
static inline int is_ws(uint8_t c) {
    return c == ' ' || c == '\n' || c == '\r' || c == '\t';
}
/* The slow path's conversion.  Its definition is with the conversion tiers,
   after the power tables it shares with them; it is forward-declared here
   because `num_scan` is the measured text and its call site does not move. */
static double to_double(const uint8_t *p, uint64_t n);

/* RFC 8259 number grammar; *err = first offending index inside p. */
static int num_scan(const uint8_t *p, uint64_t n, double *out, size_t *err) {
    uint64_t i = 0;
    if (i < n && p[i] == '-') i++;
    if (i >= n) { *err = (size_t)i; return 0; }
    if (p[i] == '0') {
        i++;
    } else if (p[i] >= '1' && p[i] <= '9') {
        while (i < n && p[i] >= '0' && p[i] <= '9') i++;
    } else {
        *err = (size_t)i; return 0;
    }
    if (i < n && p[i] == '.') {
        i++;
        if (i >= n || p[i] < '0' || p[i] > '9') { *err = (size_t)i; return 0; }
        while (i < n && p[i] >= '0' && p[i] <= '9') i++;
    }
    if (i < n && (p[i] == 'e' || p[i] == 'E')) {
        i++;
        if (i < n && (p[i] == '+' || p[i] == '-')) i++;
        if (i >= n || p[i] < '0' || p[i] > '9') { *err = (size_t)i; return 0; }
        while (i < n && p[i] >= '0' && p[i] <= '9') i++;
    }
    if (i != n) { *err = (size_t)i; return 0; }
    if (out) *out = to_double(p, n);
    return 1;
}

static int lit_check(const uint8_t *p, uint64_t n, const char *lit, uint32_t ln,
                     size_t *err) {
    uint64_t m = n < ln ? n : ln;
    for (uint64_t i = 0; i < m; i++)
        if (p[i] != (uint8_t)lit[i]) { *err = (size_t)i; return 0; }
    if (n != ln) { *err = (size_t)m; return 0; }
    return 1;
}

#define MAXD 520
enum { C_OBJ = 1, C_ARR = 2 };

static Out g_sbuf;                      /* reusable decoded-string scratch */

/* kernel/json/measured/epow_table.h, numel_el.h and numf_el1.h: the tiered
   conversion `num_fast` names, at `NUMF_EL` without `NUMF_NOINLINE`. */
typedef struct { uint64_t hi, lo; int32_t e; } EPow;
#define EPOW_MIN (-45)
#define EPOW_MAX (45)
static const EPow EPOW[91] = {
    { 0xb6b00d69bb55c8d1ULL, 0x3d607b97c5fd0d22ULL, -277 },  /* 10^-45 */
    { 0xe45c10c42a2b3b05ULL, 0x8cb89a7db77c506aULL, -274 },  /* 10^-44 */
    { 0x8eb98a7a9a5b04e3ULL, 0x77f3608e92adb242ULL, -270 },  /* 10^-43 */
    { 0xb267ed1940f1c61cULL, 0x55f038b237591ed3ULL, -267 },  /* 10^-42 */
    { 0xdf01e85f912e37a3ULL, 0x6b6c46dec52f6688ULL, -264 },  /* 10^-41 */
    { 0x8b61313bbabce2c6ULL, 0x2323ac4b3b3da015ULL, -260 },  /* 10^-40 */
    { 0xae397d8aa96c1b77ULL, 0xabec975e0a0d081aULL, -257 },  /* 10^-39 */
    { 0xd9c7dced53c72255ULL, 0x96e7bd358c904a21ULL, -254 },  /* 10^-38 */
    { 0x881cea14545c7575ULL, 0x7e50d64177da2e54ULL, -250 },  /* 10^-37 */
    { 0xaa242499697392d2ULL, 0xdde50bd1d5d0b9e9ULL, -247 },  /* 10^-36 */
    { 0xd4ad2dbfc3d07787ULL, 0x955e4ec64b44e864ULL, -244 },  /* 10^-35 */
    { 0x84ec3c97da624ab4ULL, 0xbd5af13bef0b113eULL, -240 },  /* 10^-34 */
    { 0xa6274bbdd0fadd61ULL, 0xecb1ad8aeacdd58eULL, -237 },  /* 10^-33 */
    { 0xcfb11ead453994baULL, 0x67de18eda5814af2ULL, -234 },  /* 10^-32 */
    { 0x81ceb32c4b43fcf4ULL, 0x80eacf948770ced7ULL, -230 },  /* 10^-31 */
    { 0xa2425ff75e14fc31ULL, 0xa1258379a94d028dULL, -227 },  /* 10^-30 */
    { 0xcad2f7f5359a3b3eULL, 0x096ee45813a04330ULL, -224 },  /* 10^-29 */
    { 0xfd87b5f28300ca0dULL, 0x8bca9d6e188853fcULL, -221 },  /* 10^-28 */
    { 0x9e74d1b791e07e48ULL, 0x775ea264cf55347dULL, -217 },  /* 10^-27 */
    { 0xc612062576589ddaULL, 0x95364afe032a819dULL, -214 },  /* 10^-26 */
    { 0xf79687aed3eec551ULL, 0x3a83ddbd83f52204ULL, -211 },  /* 10^-25 */
    { 0x9abe14cd44753b52ULL, 0xc4926a9672793542ULL, -207 },  /* 10^-24 */
    { 0xc16d9a0095928a27ULL, 0x75b7053c0f178293ULL, -204 },  /* 10^-23 */
    { 0xf1c90080baf72cb1ULL, 0x5324c68b12dd6338ULL, -201 },  /* 10^-22 */
    { 0x971da05074da7beeULL, 0xd3f6fc16ebca5e03ULL, -197 },  /* 10^-21 */
    { 0xbce5086492111aeaULL, 0x88f4bb1ca6bcf584ULL, -194 },  /* 10^-20 */
    { 0xec1e4a7db69561a5ULL, 0x2b31e9e3d06c32e5ULL, -191 },  /* 10^-19 */
    { 0x9392ee8e921d5d07ULL, 0x3aff322e62439fcfULL, -187 },  /* 10^-18 */
    { 0xb877aa3236a4b449ULL, 0x09befeb9fad487c2ULL, -184 },  /* 10^-17 */
    { 0xe69594bec44de15bULL, 0x4c2ebe687989a9b3ULL, -181 },  /* 10^-16 */
    { 0x901d7cf73ab0acd9ULL, 0x0f9d37014bf60a10ULL, -177 },  /* 10^-15 */
    { 0xb424dc35095cd80fULL, 0x538484c19ef38c94ULL, -174 },  /* 10^-14 */
    { 0xe12e13424bb40e13ULL, 0x2865a5f206b06fb9ULL, -171 },  /* 10^-13 */
    { 0x8cbccc096f5088cbULL, 0xf93f87b7442e45d3ULL, -167 },  /* 10^-12 */
    { 0xafebff0bcb24aafeULL, 0xf78f69a51539d748ULL, -164 },  /* 10^-11 */
    { 0xdbe6fecebdedd5beULL, 0xb573440e5a884d1bULL, -161 },  /* 10^-10 */
    { 0x89705f4136b4a597ULL, 0x31680a88f8953030ULL, -157 },  /* 10^-9 */
    { 0xabcc77118461cefcULL, 0xfdc20d2b36ba7c3dULL, -154 },  /* 10^-8 */
    { 0xd6bf94d5e57a42bcULL, 0x3d32907604691b4cULL, -151 },  /* 10^-7 */
    { 0x8637bd05af6c69b5ULL, 0xa63f9a49c2c1b10fULL, -147 },  /* 10^-6 */
    { 0xa7c5ac471b478423ULL, 0x0fcf80dc33721d53ULL, -144 },  /* 10^-5 */
    { 0xd1b71758e219652bULL, 0xd3c36113404ea4a8ULL, -141 },  /* 10^-4 */
    { 0x83126e978d4fdf3bULL, 0x645a1cac083126e9ULL, -137 },  /* 10^-3 */
    { 0xa3d70a3d70a3d70aULL, 0x3d70a3d70a3d70a3ULL, -134 },  /* 10^-2 */
    { 0xccccccccccccccccULL, 0xccccccccccccccccULL, -131 },  /* 10^-1 */
    { 0x8000000000000000ULL, 0x0000000000000000ULL, -127 },  /* 10^0 */
    { 0xa000000000000000ULL, 0x0000000000000000ULL, -124 },  /* 10^1 */
    { 0xc800000000000000ULL, 0x0000000000000000ULL, -121 },  /* 10^2 */
    { 0xfa00000000000000ULL, 0x0000000000000000ULL, -118 },  /* 10^3 */
    { 0x9c40000000000000ULL, 0x0000000000000000ULL, -114 },  /* 10^4 */
    { 0xc350000000000000ULL, 0x0000000000000000ULL, -111 },  /* 10^5 */
    { 0xf424000000000000ULL, 0x0000000000000000ULL, -108 },  /* 10^6 */
    { 0x9896800000000000ULL, 0x0000000000000000ULL, -104 },  /* 10^7 */
    { 0xbebc200000000000ULL, 0x0000000000000000ULL, -101 },  /* 10^8 */
    { 0xee6b280000000000ULL, 0x0000000000000000ULL, -98 },  /* 10^9 */
    { 0x9502f90000000000ULL, 0x0000000000000000ULL, -94 },  /* 10^10 */
    { 0xba43b74000000000ULL, 0x0000000000000000ULL, -91 },  /* 10^11 */
    { 0xe8d4a51000000000ULL, 0x0000000000000000ULL, -88 },  /* 10^12 */
    { 0x9184e72a00000000ULL, 0x0000000000000000ULL, -84 },  /* 10^13 */
    { 0xb5e620f480000000ULL, 0x0000000000000000ULL, -81 },  /* 10^14 */
    { 0xe35fa931a0000000ULL, 0x0000000000000000ULL, -78 },  /* 10^15 */
    { 0x8e1bc9bf04000000ULL, 0x0000000000000000ULL, -74 },  /* 10^16 */
    { 0xb1a2bc2ec5000000ULL, 0x0000000000000000ULL, -71 },  /* 10^17 */
    { 0xde0b6b3a76400000ULL, 0x0000000000000000ULL, -68 },  /* 10^18 */
    { 0x8ac7230489e80000ULL, 0x0000000000000000ULL, -64 },  /* 10^19 */
    { 0xad78ebc5ac620000ULL, 0x0000000000000000ULL, -61 },  /* 10^20 */
    { 0xd8d726b7177a8000ULL, 0x0000000000000000ULL, -58 },  /* 10^21 */
    { 0x878678326eac9000ULL, 0x0000000000000000ULL, -54 },  /* 10^22 */
    { 0xa968163f0a57b400ULL, 0x0000000000000000ULL, -51 },  /* 10^23 */
    { 0xd3c21bcecceda100ULL, 0x0000000000000000ULL, -48 },  /* 10^24 */
    { 0x84595161401484a0ULL, 0x0000000000000000ULL, -44 },  /* 10^25 */
    { 0xa56fa5b99019a5c8ULL, 0x0000000000000000ULL, -41 },  /* 10^26 */
    { 0xcecb8f27f4200f3aULL, 0x0000000000000000ULL, -38 },  /* 10^27 */
    { 0x813f3978f8940984ULL, 0x4000000000000000ULL, -34 },  /* 10^28 */
    { 0xa18f07d736b90be5ULL, 0x5000000000000000ULL, -31 },  /* 10^29 */
    { 0xc9f2c9cd04674edeULL, 0xa400000000000000ULL, -28 },  /* 10^30 */
    { 0xfc6f7c4045812296ULL, 0x4d00000000000000ULL, -25 },  /* 10^31 */
    { 0x9dc5ada82b70b59dULL, 0xf020000000000000ULL, -21 },  /* 10^32 */
    { 0xc5371912364ce305ULL, 0x6c28000000000000ULL, -18 },  /* 10^33 */
    { 0xf684df56c3e01bc6ULL, 0xc732000000000000ULL, -15 },  /* 10^34 */
    { 0x9a130b963a6c115cULL, 0x3c7f400000000000ULL, -11 },  /* 10^35 */
    { 0xc097ce7bc90715b3ULL, 0x4b9f100000000000ULL, -8 },  /* 10^36 */
    { 0xf0bdc21abb48db20ULL, 0x1e86d40000000000ULL, -5 },  /* 10^37 */
    { 0x96769950b50d88f4ULL, 0x1314448000000000ULL, -1 },  /* 10^38 */
    { 0xbc143fa4e250eb31ULL, 0x17d955a000000000ULL, 2 },  /* 10^39 */
    { 0xeb194f8e1ae525fdULL, 0x5dcfab0800000000ULL, 5 },  /* 10^40 */
    { 0x92efd1b8d0cf37beULL, 0x5aa1cae500000000ULL, 9 },  /* 10^41 */
    { 0xb7abc627050305adULL, 0xf14a3d9e40000000ULL, 12 },  /* 10^42 */
    { 0xe596b7b0c643c719ULL, 0x6d9ccd05d0000000ULL, 15 },  /* 10^43 */
    { 0x8f7e32ce7bea5c6fULL, 0xe4820023a2000000ULL, 19 },  /* 10^44 */
    { 0xb35dbf821ae4f38bULL, 0xdda2802c8a800000ULL, 22 },  /* 10^45 */
};
#define EL_ENTRY __attribute__((always_inline)) static inline
#define EL_MASK(ub) (0x3FFu | ((uint32_t)(ub) << 10))
#define EL_HALF(ub) (0x200u << (ub))
static uint64_t g_el_window, g_el_undec, g_el_range;
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
static uint64_t g_nume1_el, g_nume1_slow;      /* tier counters (diagnostics) */

static const double NUMF_EL1_POW10[23] = {
    1e0, 1e1, 1e2, 1e3, 1e4, 1e5, 1e6, 1e7, 1e8, 1e9, 1e10, 1e11,
    1e12, 1e13, 1e14, 1e15, 1e16, 1e17, 1e18, 1e19, 1e20, 1e21, 1e22
};

static const uint64_t NUMF_EL1_P10[20] = {
    1ULL, 10ULL, 100ULL, 1000ULL, 10000ULL, 100000ULL, 1000000ULL,
    10000000ULL, 100000000ULL, 1000000000ULL, 10000000000ULL,
    100000000000ULL, 1000000000000ULL, 10000000000000ULL,
    100000000000000ULL, 1000000000000000ULL, 10000000000000000ULL,
    100000000000000000ULL, 1000000000000000000ULL, 10000000000000000000ULL
};
#define NUMF_SIMD 1
#define NUMF_SLOW num_scan
__attribute__((always_inline)) static inline int num_d8_el1(const uint8_t *p, uint32_t *val) {
    uint64_t w;
    memcpy(&w, p, 8);
    __m128i v = _mm_cvtsi64_si128((long long)w);
    __m128i d = _mm_sub_epi8(v, _mm_set1_epi8('0'));
    int ok = _mm_movemask_epi8(_mm_cmpeq_epi8(_mm_min_epu8(d, _mm_set1_epi8(9)), d));
    if ((ok & 0xFF) != 0xFF) return 0;
    __m128i t = _mm_maddubs_epi16(d, _mm_set1_epi16(0x010A));   /* bytes 10,1 */
    __m128i q = _mm_madd_epi16(t, _mm_set1_epi32(100 | (1 << 16)));
    *val = (uint32_t)_mm_cvtsi128_si32(q) * 10000u +
           (uint32_t)_mm_extract_epi32(q, 1);
    return 1;
}
__attribute__((always_inline)) static inline int num_fast_el1(const uint8_t *p, uint64_t n, double *out, size_t *err) {
    uint64_t i = 0;
    int neg = 0;
    if (i < n && p[i] == '-') { neg = 1; i++; }
    if (i >= n) { *err = (size_t)i; return 0; }
    uint64_t ip = 0, fr = 0, idig = 0, fdig = 0;
    if (p[i] == '0') {
        idig = 1; i++;
    } else if (p[i] >= '1' && p[i] <= '9') {
        ip = (uint64_t)(p[i] - '0'); idig = 1; i++;
#if NUMF_SIMD
        while (i + 8 <= n && idig + 8 <= 19) {
            uint32_t v8;
            if (!num_d8_el1(p + i, &v8)) break;
            ip = ip * 100000000ULL + v8; idig += 8; i += 8;
        }
#endif
        while (i < n && p[i] >= '0' && p[i] <= '9') {
            if (idig < 19) ip = ip * 10 + (uint64_t)(p[i] - '0');
            idig++; i++;
        }
    } else { *err = (size_t)i; return 0; }
    if (i < n && p[i] == '.') {
        i++;
        if (i >= n || p[i] < '0' || p[i] > '9') { *err = (size_t)i; return 0; }
#if NUMF_SIMD
        while (i + 8 <= n && fdig + 8 <= 19) {
            uint32_t v8;
            if (!num_d8_el1(p + i, &v8)) break;
            fr = fr * 100000000ULL + v8; fdig += 8; i += 8;
        }
#endif
        while (i < n && p[i] >= '0' && p[i] <= '9') {
            if (fdig < 19) fr = fr * 10 + (uint64_t)(p[i] - '0');
            fdig++; i++;
        }
    }
    int64_t exp10 = 0;
    if (i < n && (p[i] == 'e' || p[i] == 'E')) {
        i++;
        int esign = 0;
        if (i < n && (p[i] == '+' || p[i] == '-')) { esign = (p[i] == '-'); i++; }
        if (i >= n || p[i] < '0' || p[i] > '9') { *err = (size_t)i; return 0; }
        /* saturate instead of counting digits: leading zeros must not stop the
           accumulation ("1e00005" is 1e5), and any value past 100000 leaves the
           fast range, so the slow path will re-read the token exactly */
        while (i < n && p[i] >= '0' && p[i] <= '9') {
            if (exp10 < 100000) exp10 = exp10 * 10 + (int64_t)(p[i] - '0');
            i++;
        }
        if (esign) exp10 = -exp10;
    }
    if (i != n) { *err = (size_t)i; return 0; }
    int64_t eff = exp10 - (int64_t)fdig;
    uint64_t nd = idig + fdig;
    if (nd <= 19 && eff >= EPOW_MIN && eff <= EPOW_MAX) {
        uint64_t mant = ip * NUMF_EL1_P10[fdig] + fr;
        if (nd <= 15 && eff >= -22 && eff <= 22) {
            /* both operands exact doubles: one IEEE operation is the result */
            double d = (eff >= 0) ? (double)mant * NUMF_EL1_POW10[eff]
                                  : (double)mant / NUMF_EL1_POW10[-eff];
            *out = neg ? -d : d;
            return 1;
        }
        double d;
        if (num_el_el1(mant, eff, &d)) {
            g_nume1_el++;
            *out = neg ? -d : d;
            return 1;
        }
    }
    double d;
    g_nume1_slow++;
    if (!NUMF_SLOW(p, n, &d, err)) return 0;
    *out = d;
    return 1;
}

/* ------------------------------------------- the fallback's conversion -- */

/* `num_fast`'s third tier: the correctly rounded (nearest, ties-to-even)
   binary64 value of a number lexeme the tiered kernels declined, computed from
   the lexeme alone, with no allocation and no length bound.

   ## What the measured third tier did, and why it is replaced

   `measured/p6.c`'s `to_double` copied the lexeme into a 64-byte stack buffer
   and called the C library's `strtod`, allocating the copy when the lexeme did
   not fit.  The length is the document's, so that allocation was input-sized,
   and its exhaustion terminated the process; and the result was the platform's
   `strtod`, which the unit's statement cannot see.  This conversion keeps the
   first of those properties out of the unit and the second out of the result.

   ## The retained window is 768 significant digits

   Rounding `x` is decided by comparing `x` with binary64 values and with
   midpoints of adjacent binary64 values.  Each of those has a finite decimal
   expansion, and the longest needs at most 768 significant digits: a midpoint
   is `(2m+1)*2^(e-1)` with `2m+1 < 2^54` and `e-1 >= -1075`, i.e.
   `(2m+1)*5^1075 / 10^1075`, and `log10((2^54-1)*5^1075) = 767.65`.  So a
   window of 768 retained digits holds every boundary exactly; the digits past
   it can only say whether the value is strictly above the retained decimal,
   and that is one sticky bit.

   Past the window nothing is refused and nothing is truncated in the sense
   that changes a rounding decision: the tail's weight is carried in the
   exponent, and the sticky bit is the whole of the tail's contribution.  A
   tie is then recognisable, because every midpoint is a decimal of at most 768
   significant digits while a value with a nonzero digit past the window is
   not -- so a tie requires the sticky bit clear.

   ## The invariant used

   Write the retained digits as an integer `M` and the weight of `M`'s last
   digit as `10^S`, and let `d` be the discarded tail, so the magnitude is

       V = M*10^S + d,        0 <= d < 10^S,     d > 0 iff sticky.

   A boundary `B = J*2^eB` is compared with `V` by scaling both by `10^-S`:

       V*10^-S = M + d*10^-S                       (the tail is < 1)
       B*10^-S = J*5^-S * 2^(eB-S)

   When the sticky bit is set, the window is full (`R = STK_DIGITS`), so
   `S = f - 767` for a value whose leading decimal digit is at exponent `f`,
   and `eB + 767 - f >= 0`: the boundaries compared against are within two ulps
   of the value, so `f - eB <= 767`, and the worst case -- a value in the low
   binades near `2^-1021`, whose down-midpoint is `(2^54-1)*2^-1075` -- has
   `f = -308`, `eB = -1075` and shift `-1075 + 767 + 308 = 0`.  So the right
   side is an integer `T`, and the comparison is `M` against `T`: below is
   `V < B`, above is `V > B`, and equal is `V > B` exactly because the tail is
   nonzero.

   That is `J_j(x)`, shift-right-with-jamming (FloatLib's "rounding after
   jamming"): the discarded tail is replaced by the single jam bit `j`, and the
   nearest-even decision of the jammed value is the original's when the jam
   lands below the guard position.  Here every boundary the decision is made at
   is represented exactly inside the window, so the jam's only job is to
   distinguish "equal to the retained decimal" from "strictly above it" -- and
   one rounding from the retained digits plus that bit is the whole computation.
   When the sticky bit is clear the value is the exact decimal `M*10^S`, and
   the comparison clears both denominators exactly.

   ## What the walk does

   The value is rounded by bracketing it: start from a double-precision
   approximation, then compare `V` exactly with the candidate, and with the
   midpoint above or below it, moving one binary64 step at a time until `V`
   lies in the candidate's rounding interval.  A comparison at a midpoint that
   returns equal is a tie, and the candidate with the even trailing significand
   wins.  The approximation is only a starting point: every decision is made by
   the exact comparison, so its error costs steps, never correctness. */

#define STK_DIGITS 768

/* Limbs enough for every operand: the largest is a 768-digit significand
   (2552 bits) shifted by the 1075-bit denominator clearance, or the scaled
   boundary `J*5^k*2^shift`, both under 3840 bits; 96 limbs is 6144. */
#define STK_LIMBS 96

typedef struct { uint64_t w[STK_LIMBS]; int n; } StkBn;

static void stk_zero(StkBn *a) { a->n = 0; }

static void stk_from_u64(StkBn *a, uint64_t v) {
    a->w[0] = v;
    a->n = v != 0;
}

static void stk_copy(StkBn *d, const StkBn *s) {
    d->n = s->n;
    if (s->n) memcpy(d->w, s->w, (size_t)s->n * sizeof s->w[0]);
}

/* a <- a*m + add, in place. */
static void stk_mul_add(StkBn *a, uint64_t m, uint64_t add) {
    unsigned __int128 carry = add;
    for (int i = 0; i < a->n; i++) {
        carry += (unsigned __int128)a->w[i] * m;
        a->w[i] = (uint64_t)carry;
        carry >>= 64;
    }
    while (carry) { a->w[a->n++] = (uint64_t)carry; carry >>= 64; }
}

static void stk_mul_u64(StkBn *a, uint64_t m) { stk_mul_add(a, m, 0); }

/* a <- a << bits, for the shifts the comparisons make (at most the 1075-bit
   denominator clearance plus a boundary's own exponent). */
static void stk_shl(StkBn *a, unsigned bits) {
    if (bits == 0 || a->n == 0) return;
    unsigned limbs = bits / 64, rem = bits % 64;
    if (rem) {
        uint64_t carry = 0;
        for (int i = 0; i < a->n; i++) {
            uint64_t v = a->w[i];
            a->w[i] = (v << rem) | carry;
            carry = v >> (64 - rem);
        }
        if (carry) a->w[a->n++] = carry;
    }
    if (limbs) {
        for (int i = a->n - 1; i >= 0; i--) a->w[i + (int)limbs] = a->w[i];
        for (unsigned i = 0; i < limbs; i++) a->w[i] = 0;
        a->n += (int)limbs;
    }
}

/* The order of two nonnegative bignums. */
static int stk_cmp_bn(const StkBn *a, const StkBn *b) {
    if (a->n != b->n) return a->n < b->n ? -1 : 1;
    for (int i = a->n - 1; i >= 0; i--)
        if (a->w[i] != b->w[i]) return a->w[i] < b->w[i] ? -1 : 1;
    return 0;
}

typedef struct {
    StkBn m;        /* the retained digits, as an integer */
    StkBn pow;      /* 5^-S when sticky, else 10^-S (or 1 when S = 0) */
    int64_t S;      /* the retained digits' decimal exponent */
    int sticky;     /* some digit past the window is nonzero */
} Stk;

/* `stk_cmp` -- the sign of `V - B`, where `V = M*10^S + d` is the lexeme's
   magnitude (`d < 10^S`, `d > 0` iff sticky) and `B = J*2^eB` is a binary64
   value or a midpoint of two.  The invariant it relies on: with the sticky bit
   set, `S < 0` and `k = -S` satisfy `eB + k >= 0`, so `B*10^k` is an integer
   and `V*10^k = M + d*10^k` has an integral part `M` and a tail below 1.  With
   the sticky bit clear the value is the exact decimal `M*10^S` and both
   denominators are cleared by the shifts. */
static int stk_cmp(const Stk *v, uint64_t J, int64_t eB) {
    StkBn a, b;
    if (v->sticky) {
        stk_copy(&b, &v->pow);
        stk_mul_u64(&b, J);
        stk_shl(&b, (unsigned)(eB - v->S));
        /* M against T; equal means the tail lifts V above B. */
        return stk_cmp_bn(&v->m, &b) < 0 ? -1 : 1;
    }
    stk_copy(&a, &v->m);
    if (eB < 0) stk_shl(&a, (unsigned)-eB);
    stk_copy(&b, &v->pow);
    stk_mul_u64(&b, J);
    if (eB > 0) stk_shl(&b, (unsigned)eB);
    return stk_cmp_bn(&a, &b);
}

/* 5^0..5^26; 5^27 is the largest power of five below 2^64. */
static const uint64_t STK_P5[27] = {
    1ULL, 5ULL, 25ULL, 125ULL, 625ULL, 3125ULL, 15625ULL, 78125ULL,
    390625ULL, 1953125ULL, 9765625ULL, 48828125ULL, 244140625ULL,
    1220703125ULL, 6103515625ULL, 30517578125ULL, 152587890625ULL,
    762939453125ULL, 3814697265625ULL, 19073486328125ULL,
    95367431640625ULL, 476837158203125ULL, 2384185791015625ULL,
    11920928955078125ULL, 59604644775390625ULL, 298023223876953125ULL,
    1490116119384765625ULL
};

static double stk_from_bits(uint64_t u) {
    double d;
    memcpy(&d, &u, 8);
    return d;
}

/* The lexeme `p[0..n)` is one `num_scan` accepted: an optional '-', an `int`
   part, an optional fraction, and an optional exponent.  `num_scan` has
   already refused everything else, so this reads the digits again rather than
   re-testing the grammar. */
static double to_double(const uint8_t *p, uint64_t n) {
    const uint64_t inf_bits = 0x7ff0000000000000ULL;
    const uint64_t max_bits = 0x7fefffffffffffffULL;
    const uint64_t frac_mask = (1ULL << 52) - 1;

    uint64_t i = 0;
    int neg = 0;
    if (i < n && p[i] == '-') { neg = 1; i++; }

    uint8_t dig[STK_DIGITS];
    uint64_t R = 0;             /* retained significant digits */
    uint64_t T = 0;             /* all digits, leading zeros included */
    uint64_t F = 0;             /* digits after the '.' */
    uint64_t lead = 0;          /* digits before the first nonzero one */
    uint64_t top = 0, topn = 0; /* the leading at most 19 digits, as an integer */
    int in_frac = 0, seen = 0, sticky = 0;

    for (; i < n; i++) {
        uint8_t c = p[i];
        if (c >= '0' && c <= '9') {
            uint8_t d = (uint8_t)(c - '0');
            T++;
            if (in_frac) F++;
            if (!seen) {
                if (d == 0) { lead++; continue; }
                seen = 1;
            }
            if (R < STK_DIGITS) {
                dig[R++] = d;
                if (topn < 19) { top = top * 10 + d; topn++; }
            } else if (d != 0) {
                sticky = 1;
            }
        } else if (c == '.') {
            in_frac = 1;
        } else {
            break;                       /* the exponent marker */
        }
    }
    if (!seen) return neg ? -0.0 : 0.0;  /* every digit is zero */

    int64_t exp10 = 0;
    if (i < n) {                         /* 'e' or 'E' */
        int esign = 0;
        i++;
        if (i < n && (p[i] == '+' || p[i] == '-')) { esign = (p[i] == '-'); i++; }
        int64_t e = 0;
        for (; i < n; i++)
            if (e < 1000000) e = e * 10 + (int64_t)(p[i] - '0');
        exp10 = esign ? -e : e;
    }

    /* V = M*10^S with M the R retained digits; f is the leading digit's
       decimal exponent, so V is in [10^f, 10^(f+1)). */
    int64_t S = exp10 - (int64_t)F + (int64_t)(T - lead - R);
    int64_t f = (int64_t)(R - 1) + S;

    /* Two decisive magnitude clamps, so no wrong finite value can come out of
       an exponent that leaves the format: 10^309 is above the overflow
       threshold, and anything below 10^-324 is below half the smallest
       subnormal, so it rounds to zero.  The nearest-even rule decides both. */
    if (f >= 309) return neg ? -stk_from_bits(inf_bits) : stk_from_bits(inf_bits);
    if (f <= -325) return neg ? -0.0 : 0.0;

    Stk v;
    v.sticky = sticky;
    v.S = S;

    stk_zero(&v.m);
    {
        uint64_t chunk = 0;
        int cn = 0;
        for (uint64_t j = 0; j < R; j++) {
            chunk = chunk * 10 + dig[j];
            if (++cn == 19) {
                stk_mul_add(&v.m, NUMF_EL1_P10[19], chunk);
                chunk = 0; cn = 0;
            }
        }
        if (cn) stk_mul_add(&v.m, NUMF_EL1_P10[cn], chunk);
    }

    stk_from_u64(&v.pow, 1);
    if (sticky) {
        /* 5^-S.  A sticky bit is set only when the lexeme had more than
           STK_DIGITS significant digits, and `f = 767 + S <= 308` for a value
           in range, so S < 0 here. */
        int64_t k = -S;
        while (k >= 27) { stk_mul_u64(&v.pow, 7450580596923828125ULL); k -= 27; }
        if (k) stk_mul_u64(&v.pow, STK_P5[k]);
    } else if (S < 0) {
        int64_t k = -S;
        while (k >= 19) { stk_mul_u64(&v.pow, NUMF_EL1_P10[19]); k -= 19; }
        if (k) stk_mul_u64(&v.pow, NUMF_EL1_P10[k]);
    } else {
        /* An exact decimal with a nonnegative exponent: fold 10^S into the
           significand, so the comparison has one form. */
        int64_t k = S;
        while (k >= 19) { stk_mul_u64(&v.m, NUMF_EL1_P10[19]); k -= 19; }
        if (k) stk_mul_u64(&v.m, NUMF_EL1_P10[k]);
        v.S = 0;
    }

    /* The starting point: the leading at most 19 digits, scaled by exact
       powers of ten.  Its error is a few ulps, which costs steps in the walk
       and nothing else. */
    int64_t e10 = f - (int64_t)(topn - 1);
    double d = (double)top;
    while (e10 > 0) {
        int c = e10 > 22 ? 22 : (int)e10;
        d *= NUMF_EL1_POW10[c];
        e10 -= c;
        if (dbits(d) >= inf_bits) break;
    }
    while (e10 < 0) {
        int c = e10 < -22 ? 22 : (int)-e10;
        d /= NUMF_EL1_POW10[c];
        e10 += c;
        if (d == 0.0) break;
    }

    uint64_t b = dbits(d);
    for (;;) {
        if (b == 0) {
            /* Zero's upper boundary is half the smallest subnormal; a tie
               there is between 0 and 2^-1074 and zero is the even one. */
            if (stk_cmp(&v, 1, -1075) > 0) { b = 1; continue; }
            break;
        }
        if (b >= inf_bits) {
            /* Infinity's lower boundary is the overflow threshold, and a tie
               there is infinity (the largest finite value's significand is
               odd). */
            if (stk_cmp(&v, (1ULL << 54) - 1, 970) < 0) { b = max_bits; continue; }
            b = inf_bits;
            break;
        }
        uint64_t be = (b >> 52) & 0x7ff;
        uint64_t m = (be == 0) ? (b & frac_mask) : ((1ULL << 52) | (b & frac_mask));
        int64_t e = (be == 0) ? -1074 : (int64_t)be - 1075;
        int s = stk_cmp(&v, m, e);
        if (s == 0) break;               /* V is this double exactly */
        if (s > 0) {
            /* The boundary above: (2m+1)*2^(e-1), also at a binade top. */
            int su = stk_cmp(&v, 2 * m + 1, e - 1);
            if (su < 0) break;           /* below it: this candidate */
            if (su == 0) {               /* a tie: the even significand wins */
                if (m & 1) b++;
                break;
            }
            b++;
            continue;
        }
        /* The boundary below, in the shape its binade gives it. */
        uint64_t J;
        int64_t eB;
        if (be == 0 || m > (1ULL << 52)) { J = 2 * m - 1; eB = e - 1; }
        else if (be == 1) { J = (1ULL << 53) - 1; eB = -1075; }
        else { J = (1ULL << 54) - 1; eB = e - 2; }
        int sd = stk_cmp(&v, J, eB);
        if (sd > 0) break;               /* above it: this candidate */
        if (sd == 0) {                   /* a tie: the even significand wins */
            if (m & 1) b--;
            break;
        }
        b--;
    }

    double r = stk_from_bits(b);
    return neg ? -r : r;
}

/* The alias the call sites use, after the function it names, so
   that no definition of `num_fast_el1` is shadowed by it. */
#define num_fast num_fast_el1

/* ---------------------------------------------- zero-copy string bodies -- */
/* kernel/json/measured/strz.c: the event arena and the body scan. */
typedef struct {
    Out ev;                 /* event stream (hash = 0) */
    uint8_t *ar;            /* arena for escaped bodies */
    size_t alen, acap;
} ZOut;
static void z_init(ZOut *z) {
    memset(z, 0, sizeof *z);
    out_init(&z->ev, 0);
}
static void z_arena_reserve(ZOut *z, size_t need) {
    /* The arena is the caller's: `alen` is its cursor and `acap` the
       capacity the caller staged, so the measured grow is a `pre`
       clause here.  A caller that under-reserves is outside the unit's
       domain; the trap is the loud form of that violation, never a
       behaviour the record models. */
    if (z->alen + need <= z->acap) return;
    __builtin_trap();
}

/* ------------------------------------------- the cursor's value helpers -- */
/* kernel/json/measured/p16.c: the scalar's first-whitespace extent, its number
   or literal check, and the recorded refusal. */
#define IXP(v) ((uint64_t)(v))
enum {
    K_OBJ = T_OBJ, K_OBJ_END = T_OBJ_END, K_ARR = T_ARR, K_ARR_END = T_ARR_END,
    K_KEY = T_KEY, K_STR = T_STR, K_NUM = T_NUM, K_TRUE = T_TRUE,
    K_FALSE = T_FALSE, K_NULL = T_NULL,
    K_COMMA = 20, K_COLON = 21
};
typedef struct {
    uint64_t pos, end;
    uint32_t kind;
    int gap;                            /* scalar bounded by the next index */
} OdTok;
typedef struct {
    const uint8_t *b;
    uint64_t n;
    const uint32_t *ix;
    uint64_t nix;
    uint64_t k, cur;                    /* next index, next byte to consider */
    uint8_t ctype[MAXD], cst[MAXD];
    uint32_t sp;
    int root_done;
    uint64_t visited;                   /* tokens stepped (gate bookkeeping) */
    int trusting;                       /* validate == 0 */
    Err *e;
    /* masks-direct mode: the next unconsumed candidate bit */
    const uint64_t *cand, *im;
    const uint64_t *esc;                /* stage-1 escape-class mask */
    const uint8_t *cls;                 /* stage-1 per-block escape class */
    int exact;                          /* refine a class-3 block with the mask */
    int twoway;                         /* escape blocks go to the ladder only */
    uint64_t nb, bb, bit, bits;
} OdCur;
static int od_fail(OdCur *c, uint64_t off, const char *msg) {
    err_set(c->e, off, msg);
    return 0;
}
__attribute__((always_inline)) static inline uint64_t touch_bytes(const uint8_t *p, uint64_t n, uint64_t acc) {
    uint64_t a = 0, b2 = 0, c2 = 0, d = 0, i = 0;
    for (; i + 32 <= n; i += 32) {
        uint64_t w0, w1, w2, w3;
        memcpy(&w0, p + i, 8); memcpy(&w1, p + i + 8, 8);
        memcpy(&w2, p + i + 16, 8); memcpy(&w3, p + i + 24, 8);
        a += w0; b2 += w1; c2 += w2; d += w3;
    }
    for (; i + 8 <= n; i += 8) { uint64_t w; memcpy(&w, p + i, 8); a += w; }
    for (; i < n; i++) a += p[i];
    return acc + a + b2 + c2 + d;
}
static inline uint64_t touch_u64(uint64_t acc, uint64_t v) {
    return acc + v * 0x9E3779B97F4A7C15ULL;
}
static void od_gap_recover(OdCur *c, const OdTok *t) {
    const uint8_t *b = c->b;
    uint64_t ip = (c->k < c->nix) ? IXP(c->ix[c->k]) : c->n;
    uint64_t ee = t->pos;
    while (ee < ip && !is_ws(b[ee])) ee++;
    if (ee == ip) return;                       /* no internal whitespace */
    OdTok t2 = *t;
    t2.end = ee;
    uint8_t ch = b[t2.pos];
    if (ch == '-' || (ch >= '0' && ch <= '9')) {
        double d; size_t ei;
        if (!num_fast(b + t2.pos, t2.end - t2.pos, &d, &ei)) {
            err_set(c->e, t2.pos + ei, "number");
            return;
        }
    } else {
        const char *lit; uint32_t ln;
        if (ch == 't') { lit = "true"; ln = 4; }
        else if (ch == 'f') { lit = "false"; ln = 5; }
        else if (ch == 'n') { lit = "null"; ln = 4; }
        else { err_set(c->e, t2.pos, "scalar"); return; }
        size_t ei;
        if (!lit_check(b + t2.pos, t2.end - t2.pos, lit, ln, &ei)) {
            err_set(c->e, t2.pos + ei, "literal");
            return;
        }
    }
    uint64_t s2 = ee;
    while (s2 < ip && is_ws(b[s2])) s2++;
    err_set(c->e, s2, "extra token");
}
__attribute__((always_inline)) static inline int od_scalar_value(OdCur *c, const OdTok *t, Out *o, uint64_t *acc) {
    uint8_t ch = c->b[t->pos];
    if (t->kind == 0) return od_fail(c, t->pos, "scalar");
    if (t->kind == K_NUM) {
        double d;
        size_t ei;
#ifdef SKIP_NUM
        if (!o) { *acc = touch_u64(*acc, t->end - t->pos); return 1; }
#endif
        if (!num_fast(c->b + t->pos, t->end - t->pos, &d, &ei))
            return od_fail(c, t->pos + ei, "number");
        if (o) { out_tag(o, T_NUM); out_u64(o, dbits(d)); }
        else *acc = touch_u64(*acc, dbits(d));
        return 1;
    }
    const char *lit;
    uint32_t ln;
    uint8_t tag;
    if (ch == 't')      { lit = "true";  ln = 4; tag = T_TRUE;  }
    else if (ch == 'f') { lit = "false"; ln = 5; tag = T_FALSE; }
    else if (ch == 'n') { lit = "null";  ln = 4; tag = T_NULL;  }
    else return od_fail(c, t->pos, "scalar");
    size_t ei;
    if (!lit_check(c->b + t->pos, t->end - t->pos, lit, ln, &ei))
        return od_fail(c, t->pos + ei, "literal");
    if (o) out_tag(o, tag);
    else *acc = touch_u64(*acc, tag);
    return 1;
}

/* ---------------------------------------------------------------- the walk -- */
/* kernel/json/measured/s2port.h: the entry stream's dispatch. */
#define S2_VAL 1u
#define S2_STR 2u
#define S2_EV  4u
typedef struct {
    const uint8_t *b;
    uint64_t n, nb;
    const uint32_t *ix;      /* raw stage-1 index */
    uint64_t nix;
    const uint64_t *im;      /* in-string / quote-open bit per position */
    uint32_t *ep;            /* derived entry stream (positions) */
    uint64_t nsp;
    uint64_t visited;
    const uint32_t *xp;      /* stage-1 escape positions (document order) */
    uint64_t nxp;
    const uint64_t *em;      /* stage-1 escape mask per 64-byte block */
    uint64_t nem;
    const uint64_t *uk;      /* stage-1 escape-kind bit per block */
    uint64_t nuk;
} S2;
__attribute__((always_inline)) static inline void
s2_init(S2 *s, const uint8_t *b, uint64_t n, uint64_t nb,
        const uint32_t *ix, uint64_t nix, const uint64_t *im, uint32_t *ep) {
    s->b = b; s->n = n; s->nb = nb; s->ix = ix; s->nix = nix;
    s->im = im; s->ep = ep; s->nsp = 0; s->visited = 0;
    s->xp = NULL; s->nxp = 0;
    s->em = NULL; s->nem = 0;
    s->uk = NULL; s->nuk = 0;
}
/* Value-position test, same states as the reference walk. */
__attribute__((always_inline)) static inline int s2_value_pos(uint32_t sp, int root_done,
                                                              const uint8_t *ct,
                                                              const uint8_t *cs) {
    if (sp == 0) return !root_done;
    uint32_t t = sp - 1;
    if (ct[t] == C_OBJ) return cs[t] == 2;
    return cs[t] == 0 || cs[t] == 2;
}
__attribute__((always_inline)) static inline void s2_after_value(uint32_t *sp, int *root_done,
                                                                 uint8_t *ct, uint8_t *cs) {
    if (*sp == 0) { *root_done = 1; return; }
    uint32_t t = *sp - 1;
    cs[t] = (ct[t] == C_OBJ) ? 3 : 1;
}
/* String body: the validation half of od_string_body_z, without the event
   record.

   Two forms, and between them one pass over the body:
     no escape   z_scan found nothing to decode, so the body is its own
                 materialisation -- no copy is made at all (form (a));
     escape      z_scan stopped at the first backslash.  Everything before it
                 is already known clean and its decoded bytes are the input
                 bytes, so they are copied and the SIMD unescaper starts at
                 the backslash itself (form (b)).  Nothing before that offset
                 is traversed twice.
   The error offset is the reference's: a control byte at its own offset, a
   malformed escape at its backslash. */
__attribute__((always_inline)) static inline int s2_string_body(OdCur *c, const uint8_t *p,
                                                               uint64_t len, uint8_t *dst,
                                                               size_t *outn,
                                                               const uint32_t *xp,
                                                               uint64_t *xj, uint64_t nxp,
                                                               const uint64_t *em,
                                                               const uint64_t *uk) {
    /* The stage-1 list already names every special byte of this body: no scan
       is needed to classify it, and the unescaper starts at once. */
    {
        uint64_t pos0 = (uint64_t)(p - c->b);
        while (*xj < nxp && (uint64_t)xp[*xj] < pos0) (*xj)++;
        if (!(*xj < nxp && (uint64_t)xp[*xj] < pos0 + len)) {
            *outn = (size_t)len;                            /* form (a) */
            return 1;
        }
        size_t ei = 0;
        /* The escaped body's decoder is the escape unit's ABI entry
           point: the measured call's signature and semantics are what
           `escape.h` publishes, so the body is decoded by that call
           rather than by a second copy of `us_dec_x` in this unit. */
        size_t on = (size_t)leanllvm_json_escape_expand(p, len, dst, &ei,
                                                       xp, xj, nxp, pos0);
        if (on == (size_t)-1) {
            od_fail(c, pos0 + ei, "string");
            return 0;
        }
        *outn = on;                                         /* form (b) */
        return 2;
    }
}
/* Consuming string: sum the body bytes, no validation. */
__attribute__((always_inline)) static inline void s2_string_touch(const uint8_t *p, uint64_t len,
                                                                 uint64_t *acc) {
    *acc = touch_bytes(p, len, *acc);
}
/* flags is a compile-time constant at every call site; always_inline lets the
   compiler drop the branches the mode does not need, which is how the four
   measurements below are built from one source. */
__attribute__((always_inline)) static inline uint64_t
s2_walk(S2 *s, unsigned flags, ZOut *z, Err *e) {
    const uint8_t *b = s->b;
    uint64_t n = s->n;
    const uint32_t *ep = s->ep;
    uint64_t nsp = s->nsp;
    OdCur c;
    memset(&c, 0, sizeof c);
    c.b = b; c.n = n; c.ix = ep; c.nix = nsp; c.e = e;

    uint8_t ctype[MAXD], cst[MAXD];
    uint32_t sp = 0;
    int root_done = 0;
    uint64_t acc = 0, visited = 0;
    uint64_t k = 0;
    uint64_t xj = 0;
    const uint32_t *xp = s->xp;
    uint64_t nxp = s->nxp;

    while (k < nsp) {
        uint32_t p = ep[k++];
        uint8_t ch = b[p];
        c.k = k;
        visited++;
        switch (ch) {
        case '{':
        case '[': {
            if (flags & S2_VAL) {
                if (!s2_value_pos(sp, root_done, ctype, cst))
                    return od_fail(&c, p, "container where no value is allowed"), 0;
                if (sp >= MAXD) return od_fail(&c, p, "nesting limit"), 0;
                ctype[sp] = (ch == '{') ? C_OBJ : C_ARR;
                cst[sp] = 0;
                sp++;
            }
            if (flags & S2_EV) out_tag(&z->ev, (ch == '{') ? T_OBJ : T_ARR);
            else acc = touch_u64(acc, (ch == '{') ? K_OBJ : K_ARR);
            break;
        }
        case '}':
        case ']': {
            if (flags & S2_VAL) {
                if (sp == 0) return od_fail(&c, p, "close"), 0;
                uint32_t t = sp - 1;
                uint8_t want = (ch == '}') ? C_OBJ : C_ARR;
                if (ctype[t] != want) return od_fail(&c, p, "bracket type"), 0;
                uint8_t st = cst[t];
                int ok = (want == C_OBJ) ? (st == 3 || st == 0) : (st == 1 || st == 0);
                if (!ok) return od_fail(&c, p, "trailing comma"), 0;
                sp--;
                s2_after_value(&sp, &root_done, ctype, cst);
            }
            if (flags & S2_EV) out_tag(&z->ev, (ch == '}') ? T_OBJ_END : T_ARR_END);
            else acc = touch_u64(acc, (ch == '}') ? K_OBJ_END : K_ARR_END);
            break;
        }
        case ',': {
            if (flags & S2_VAL) {
                if (sp == 0) return od_fail(&c, p, "comma"), 0;
                uint32_t t = sp - 1;
                if (ctype[t] == C_OBJ) {
                    if (cst[t] != 3) return od_fail(&c, p, "comma"), 0;
                    cst[t] = 4;
                } else {
                    if (cst[t] != 1) return od_fail(&c, p, "comma"), 0;
                    cst[t] = 2;
                }
            }
            (void)ch;
            break;
        }
        case ':': {
            if (flags & S2_VAL) {
                if (sp == 0) return od_fail(&c, p, "colon"), 0;
                uint32_t t = sp - 1;
                if (ctype[t] != C_OBJ || cst[t] != 1) return od_fail(&c, p, "colon"), 0;
                cst[t] = 2;
            }
            (void)ch;
            break;
        }
        case '"': {
            if (k >= nsp) return od_fail(&c, n, "unterminated"), 0;
            uint32_t close = ep[k++];
            c.k = k;
            if (close >= n) return od_fail(&c, n, "unterminated"), 0;
            int key = 0;
            if (flags & S2_VAL) {
                int val = s2_value_pos(sp, root_done, ctype, cst);
                if (sp > 0 && ctype[sp - 1] == C_OBJ) {
                    uint8_t st = cst[sp - 1];
                    if (st == 0 || st == 4) key = 1;
                }
                if (!key && !val) return od_fail(&c, p, "string where no value is allowed"), 0;
            }
            uint64_t len = (uint64_t)close - p - 1;
            if (flags & (S2_STR | S2_EV)) {
                /* one body pass for both forms: with S2_EV the decoded bytes
                   go straight to the event arena, otherwise to the scratch */
                size_t outn = 0;
                uint8_t *dst;
                if (flags & S2_EV) {
                    z_arena_reserve(z, (size_t)len + US_SLACK);
                    dst = z->ar + z->alen;
                } else {
                    out_reserve(&g_sbuf, (size_t)len + US_SLACK);
                    dst = g_sbuf.b;
                }
                int form = s2_string_body(&c, b + p + 1, len, dst, &outn,
                                          xp, &xj, nxp, s->em, s->uk);
                if (!form) return 0;
                if (flags & S2_EV) {
                    uint32_t ol;
                    uint64_t rec;
                    if (form == 1) {          /* plain: a span into the input */
                        ol = (uint32_t)len;
                        rec = (uint64_t)(p + 1) | (1ULL << 63);
                    } else {                  /* escaped: bytes in the arena */
                        ol = (uint32_t)outn;
                        rec = z->alen;
                        z->alen += outn;
                    }
                    out_reserve(&z->ev, 13);
                    uint8_t *e = z->ev.b + z->ev.len;
                    e[0] = (uint8_t)(key ? T_KEY : T_STR);
                    memcpy(e + 1, &ol, 4);
                    memcpy(e + 5, &rec, 8);
                    z->ev.len += 13;
                } else {
                    if (form == 2) g_sbuf.len = outn;
                    acc = touch_u64(acc, len);
                }
            } else {
                s2_string_touch(b + p + 1, len, &acc);
            }
            if (flags & S2_VAL) {
                if (key) cst[sp - 1] = 1;
                else s2_after_value(&sp, &root_done, ctype, cst);
            }
            break;
        }
        default: {
            /* A scalar gap.  Its text ends at the first whitespace, exactly as
               the reference cursor's gap scan does; the next entry position is
               the delimiter that follows. */
            uint64_t ip = (k < nsp) ? (uint64_t)ep[k] : n;
            uint64_t ee = p;
            OdTok t;
            t.pos = p;
            t.gap = 1;
            if (ip > p && !is_ws(b[ip - 1])) {
                ee = ip;
            } else {
                while (ee < ip && !is_ws(b[ee])) ee++;
            }
            t.end = ee;
            {
                uint8_t c0 = b[p];
                if (c0 == '-' || (c0 >= '0' && c0 <= '9')) t.kind = K_NUM;
                else if (c0 == 't') t.kind = K_TRUE;
                else if (c0 == 'f') t.kind = K_FALSE;
                else if (c0 == 'n') t.kind = K_NULL;
                else t.kind = 0;
            }
            if (flags & S2_VAL) {
                if (!s2_value_pos(sp, root_done, ctype, cst))
                    return od_fail(&c, p, "scalar where no value is allowed"), 0;
            }
            if (flags & S2_EV) {
                if (!od_scalar_value(&c, &t, &z->ev, &acc)) {
                    if (t.gap) od_gap_recover(&c, &t);
                    return 0;
                }
            } else {
                if (!od_scalar_value(&c, &t, NULL, &acc)) {
                    if (t.gap) od_gap_recover(&c, &t);
                    return 0;
                }
            }
            if (flags & S2_VAL) s2_after_value(&sp, &root_done, ctype, cst);
            /* Anything between the scalar's first-whitespace end and the next
               entry is a second token in the same gap; the reference reaches
               it as another scalar and rejects it at that byte. */
            if (ee < ip) {
                uint64_t q = ee;
                while (q < ip && is_ws(b[q])) q++;
                if (q < ip) return od_fail(&c, q, "extra token"), 0;
            }
            break;
        }
        }
    }
    if (flags & S2_VAL) {
        if (sp != 0) return od_fail(&c, n, "unclosed container"), 0;
        if (!root_done) return od_fail(&c, n, "no value"), 0;
    }
    e->ok = 1;
    e->off = 0;
    e->msg = "ok";
    s->visited = visited;
    return acc + 1;
}

/* ------------------------------------------------------------------- ABI -- */
uint64_t leanllvm_json_stage2(const uint8_t *b, uint64_t n,
                              const uint32_t *ep, uint64_t nep,
                              const uint32_t *xp, uint64_t nxp,
                              uint8_t *dst, uint64_t dstcap, uint64_t *ndst,
                              uint8_t *ev, uint64_t evcap, uint64_t *nev,
                              uint64_t *err) {
    S2 s;
    ZOut z;
    Err e;

    s2_init(&s, b, n, (n + 63) >> 6, NULL, 0, NULL, (uint32_t *)ep);
    s.nsp = nep;
    s.xp = xp;
    s.nxp = nxp;

    z_init(&z);
    z.ar = dst;
    z.alen = (size_t)*ndst;
    z.acap = (size_t)dstcap;
    z.ev.b = ev;
    z.ev.len = (size_t)*nev;
    z.ev.cap = (size_t)evcap;

    /* The mode `pipeline.c`'s call site passes — the set §8.3's post needs.  The
       measured text constant-propagates the same set at its own call site, so
       the body stays the measured walk; a caller-chosen mode is a wrapper
       change, not a body edit. */
    uint64_t r = s2_walk(&s, S2_VAL | S2_STR | S2_EV, &z, &e);
    *ndst = (uint64_t)z.alen;
    *nev = (uint64_t)z.ev.len;
    if (!r) *err = e.off;
    return r ? 1 : 0;
}
