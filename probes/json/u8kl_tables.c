/* u8kl_tables.c -- the vendored header's three tables, printed.
 *
 * One line per table, in the form `leanllvm-json-utf8 --tables` prints:
 *
 *     <name> <b00> <b01> ... <b31>
 *
 * with each byte two lowercase hexadecimal digits.  This translation unit is the
 * route's side of C58's table derivation: it includes the vendored header, so the
 * bytes it prints are the ones the header declares rather than a copy of them,
 * and `tests/json-utf8/check.sh` compares its output with the specification's
 * row for row.
 *
 * It links nothing and computes nothing.  `kernel/json/measured/u8kl.h` is
 * read-only reference, and this is one of the translation units that includes it
 * only to be compiled and compared.
 */
#include <stdio.h>

#include "u8kl.h"

static void print_row(const char *name, const uint8_t *t) {
    printf("%s", name);
    for (int k = 0; k < 32; k++)
        printf(" %02x", (unsigned)t[k]);
    printf("\n");
}

int main(void) {
    print_row("kl_t1", kl_t1);
    print_row("kl_t2", kl_t2);
    print_row("kl_t3", kl_t3);
    return 0;
}
