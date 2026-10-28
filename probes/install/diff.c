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

int main(void) {
    for (unsigned i = 0; i < sizeof words / sizeof words[0]; i++) {
        printf("%llu %llu\n", (unsigned long long)words[i],
               (unsigned long long)leanllvm_comma_mask8(words[i]));
    }
    return 0;
}
