/* The comma-mask corpus: the seam's result for each input, and a lane-wise
 * specification check that does not go through any seam body.
 *
 * `spec` is the definition written out in C: bit `8 * i + 7` of the mask is set
 * exactly when byte `i` of `x ^ 0x2C2C2C2C2C2C2C2C` is zero.  It is not
 * derived from the baseline, the candidate or the loop, so agreement with it
 * is not those bodies agreeing with each other.  A disagreement prints its own
 * `mismatch` line and makes the program exit nonzero.
 *
 * This is a runtime check over the corpus, not a proof and not an installation
 * certificate: the theorem for an installed unit is `IR_refines` over the
 * candidate and the baseline, and the loop's own theorem is in
 * `LeanLLVM/Vellum/CommaMaskLoop.lean`.
 */
#include <stdint.h>
#include <stdio.h>

extern uint64_t leanllvm_comma_mask8(uint64_t);

static const uint64_t words[] = {
    0,
    0x2C,
    0x2D2C,
    0x2C2C2C2C2C2C2C2C,
    0x2C00000000000000,
    0x0102030405060708,
    0xFFFFFFFFFFFFFFFF,
};

static uint64_t spec(uint64_t x) {
    uint64_t m = x ^ 0x2C2C2C2C2C2C2C2CULL;
    uint64_t mask = 0;
    for (unsigned i = 0; i < 8; i++) {
        if (((m >> (8 * i)) & 0xFF) == 0) {
            mask |= 0x80ULL << (8 * i);
        }
    }
    return mask;
}

int main(void) {
    int bad = 0;
    for (unsigned i = 0; i < sizeof words / sizeof words[0]; i++) {
        uint64_t x = words[i];
        uint64_t got = leanllvm_comma_mask8(x);
        uint64_t want = spec(x);
        printf("%llu %llu\n", (unsigned long long)x, (unsigned long long)got);
        if (got != want) {
            printf("mismatch %llu got %llu want %llu\n",
                   (unsigned long long)x, (unsigned long long)got,
                   (unsigned long long)want);
            bad = 1;
        }
    }
    return bad;
}
