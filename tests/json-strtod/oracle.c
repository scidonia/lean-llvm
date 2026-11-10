/* oracle.c -- glibc's `strtod` over the corpus, as the double's bit pattern.

   The row is `<lexeme>\t<bits>`; a lexeme the library does not consume whole
   is reported as a `setup` row rather than a comparison, because a partial
   conversion is a fault in the corpus line, not a disagreement about
   rounding.  This is the reference the specification's agreement is measured
   against, and it is not a model: it is the C library the emitted body's third
   tier calls. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

int main(int argc, char **argv) {
    const char *path = argc > 1 ? argv[1] : "tests/json-strtod/corpus.txt";
    char line[8192];
    FILE *f = fopen(path, "r");
    if (!f) { perror(path); return 2; }
    while (fgets(line, sizeof line, f)) {
        size_t n = strlen(line);
        while (n && (line[n - 1] == '\n' || line[n - 1] == '\r')) line[--n] = 0;
        if (!n) continue;
        char *end = NULL;
        double d = strtod(line, &end);
        if (end != line + n) {
            printf("%s\tsetup: strtod consumed %zu of %zu\n", line,
                   (size_t)(end - line), n);
            continue;
        }
        uint64_t u;
        memcpy(&u, &d, 8);
        printf("%s\t%llu\n", line, (unsigned long long)u);
    }
    fclose(f);
    return 0;
}
