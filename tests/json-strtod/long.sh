#!/usr/bin/env bash
# The fallback conversion on the lexemes whose length or whose tail decides the
# rounding.
#
#   nix develop -c bash tests/json-strtod/long.sh
#
# The subject is `kernel/json/stage2.c`'s `to_double`, the conversion `num_fast`
# reaches after its tiered kernels decline.  The driver includes the unit's own
# text, so it calls the same static functions the build compiles, and converts
# each lexeme twice: once through the emitted conversion and once through the C
# library's `strtod`, which is the reference `tests/json-strtod/corpus.txt` is
# checked against.  A row agrees when the two encodings are equal.
#
# What the rows establish:
#
#   * the long lexemes -- 10^3, 10^5 and 10^6 digits -- convert correctly;
#   * a nonzero digit beyond the retained window changes the rounding exactly
#     as the exact value demands.  Rows 3/4, 5/6 and 7/8 are one prefix with the
#     tail zeroed and the same prefix with a single nonzero digit far past the
#     window: the first is the exact tie `4503599627370496.5`, the second is
#     strictly above it, and the two encodings must differ.  That difference is
#     the sticky bit's whole purpose;
#   * the earlier tie cases still agree, and the magnitude clamps (10^1000000,
#     10^-1000000) return infinity and zero;
#   * no allocation happens on the conversion path, measured twice.  The driver
#     links with `--wrap=malloc`, so every allocation the unit's text makes goes
#     through a wrapper that refuses it and counts the attempt; the run must
#     report zero attempts while every row still agrees.  For the 10^5 and 10^6
#     digit rows the driver also lowers its address-space limit to just above
#     what it already holds, returns the glibc arena's free pages
#     (`malloc_trim`), requests the lexeme's own copy size (`n + 1`) through
#     the *real* allocator -- refused, which is the limit biting -- and
#     then converts the lexeme with the real allocator still available, which
#     must succeed.  The same request succeeds once the limit is restored, so
#     the refusal is the limit and not the size.
#
# Exit status: 0 when every claim holds, 1 when a row disagrees or an allocation
# was attempted, 3 when the fixture cannot be built or a control fails, so a
# setup fault is never read as a conversion result.
set -uo pipefail

here=$(cd "$(dirname "$0")/../.." && pwd)
cd "$here"

cc=${CC:-cc}
work=$(mktemp -d) || { echo "SETUP: cannot create a temporary directory" >&2; exit 3; }
trap 'rm -rf "$work"' EXIT

cat > "$work/long.c" <<'DRIVER'
/* Adversarial rows for the stage-2 fallback conversion.  The unit's text is
   included, so `num_fast` and `to_double` here are the build's own. */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <sys/resource.h>
#include <malloc.h>
#include <unistd.h>

extern void *__real_malloc(size_t);
extern double __real_strtod(const char *, char **);

/* `volatile`: the wrapper is reached through the linker's `--wrap` rewrite, not
   by a call the compiler can see, so a plain static would be dead-store
   eliminated as if nothing read it. */
static volatile int armed;
static volatile unsigned long alloc_attempts, strtod_attempts;
static unsigned long cap_rows, cap_refused, cap_granted, cap_uncapped;

/* Armed: refuse and count.  Unarmed: the real allocator. */
void *__wrap_malloc(size_t n) {
    if (armed) { alloc_attempts++; return NULL; }
    return __real_malloc(n);
}

double __wrap_strtod(const char *s, char **e) {
    if (armed) strtod_attempts++;
    return __real_strtod(s, e);
}

#include "stage2.c"

/* The driver's total mapped size, so the cap can be set just above it. */
static unsigned long long mapped_bytes(void) {
    FILE *f = fopen("/proc/self/statm", "r");
    long pages = 0, rss = 0;
    if (!f) return 0;
    if (fscanf(f, "%ld %ld", &pages, &rss) != 2) pages = 0;
    fclose(f);
    long ps = sysconf(_SC_PAGESIZE);
    return pages > 0 && ps > 0 ? (unsigned long long)pages * (unsigned long long)ps : 0;
}

static uint64_t bits_of(double d) {
    uint64_t u;
    memcpy(&u, &d, 8);
    return u;
}

int main(int argc, char **argv) {
    int cap_mode = argc > 1 && strcmp(argv[1], "--cap") == 0;

    /* The wrappers' own positive control, before anything else is measured:
       an allocation and a `strtod` call inside the armed window must be seen. */
    armed = 1;
    void *probe = malloc(32);
    double one = strtod("1", NULL);
    armed = 0;
    if (probe != NULL || strtod_attempts != 1 || one != 1.0) {
        fprintf(stderr, "SETUP: the armed wrapper control did not fire "
                "(malloc %s, strtod calls %lu)\n",
                probe ? "granted" : "refused", strtod_attempts);
        return 3;
    }
    alloc_attempts = 0;
    strtod_attempts = 0;

    char *line = NULL;
    size_t line_cap = 0;
    long rows = 0, bad = 0;
    ssize_t got;
    while ((got = getline(&line, &line_cap, stdin)) > 0) {
        size_t n = (size_t)got;
        while (n && (line[n - 1] == '\n' || line[n - 1] == '\r')) line[--n] = 0;
        if (!n) continue;
        rows++;

        /* The reference first: outside every armed or capped window. */
        char *end = NULL;
        double want = __real_strtod(line, &end);
        if (end != line + n) {
            printf("SETUP: strtod consumed %zu of %zu\n",
                   (size_t)(end - line), n);
            return 3;
        }

        /* The emitted conversion with the allocator armed. */
        double d = 0.0;
        size_t err = 0;
        armed = 1;
        int ok = num_fast((const uint8_t *)line, n, &d, &err);
        armed = 0;

        int ok_cap = 1;
        if (cap_mode && n >= 100000) {
            /* A limit that would refuse the copy the old tier made: the
               driver's mapped size plus half the lexeme, so `n + 1` bytes
               cannot be granted, while the conversion's few kilobytes of
               stack can. */
            struct rlimit saved;
            /* Return the heap's free pages first, so the request below cannot
               be served from spare arena and has to ask the address space. */
            malloc_trim(0);
            unsigned long long va = mapped_bytes();
            if (va && getrlimit(RLIMIT_AS, &saved) == 0) {
                struct rlimit low;
                low.rlim_cur = (rlim_t)(va + (unsigned long long)n / 2);
                low.rlim_max = saved.rlim_max;
                if (setrlimit(RLIMIT_AS, &low) == 0) {
                    void *copy = __real_malloc(n + 1);
                    cap_rows++;
                    if (copy) {
                        free(copy);
                        cap_granted++;
                    } else {
                        cap_refused++;
                    }
                    double c = 0.0;
                    size_t ce = 0;
                    ok_cap = num_fast((const uint8_t *)line, n, &c, &ce);
                    if (!ok_cap || bits_of(c) != bits_of(d)) ok_cap = 0;
                    if (setrlimit(RLIMIT_AS, &saved) != 0) {
                        fprintf(stderr, "SETUP: the limit was not restored\n");
                        return 3;
                    }
                }
                /* The same request without the cap: the control that the
                   refusal above was the limit's. */
                void *copy = __real_malloc(n + 1);
                if (copy) { free(copy); cap_uncapped++; }
            }
        }

        uint64_t a = bits_of(d), b = bits_of(want);
        int agree = ok && ok_cap && a == b;
        if (!agree) bad++;
        printf("%ld\t%llu\t%llu\t%s\n", rows,
               (unsigned long long)a, (unsigned long long)b,
               agree ? "ok" : "DIFF");
    }
    free(line);
    printf("rows=%ld mismatches=%ld alloc_attempts=%lu "
           "cap_rows=%lu cap_refused=%lu cap_granted=%lu cap_uncapped=%lu\n",
           rows, bad, alloc_attempts, cap_rows, cap_refused, cap_granted,
           cap_uncapped);
    if (bad) return 1;
    if (alloc_attempts || strtod_attempts) {
        fprintf(stderr, "FAIL: the conversion allocated or called strtod\n");
        return 1;
    }
    if (cap_rows && cap_granted) {
        fprintf(stderr, "FAIL: the cap did not refuse the copy\n");
        return 1;
    }
    if (cap_mode && (cap_rows == 0 || cap_uncapped != cap_rows)) {
        fprintf(stderr, "FAIL: the cap control did not run in both windows\n");
        return 1;
    }
    return 0;
}
DRIVER

$cc -O2 -std=gnu11 -march=x86-64-v3 -fno-builtin -I "$here/kernel/json" \
    -Wl,--wrap=malloc -Wl,--wrap=strtod \
    -o "$work/long" "$work/long.c" "$here/kernel/json/escape.c" || exit 3

# The static detector for the same claim, with its own control: the unit's
# object must not reference the allocator, the terminator or the library's
# conversion, while a translation unit that does reference them is reported.
$cc -O2 -std=gnu11 -march=x86-64-v3 -I "$here/kernel/json" \
    -c "$here/kernel/json/stage2.c" -o "$work/stage2.o" || exit 3
cat > "$work/uses.c" <<'USES'
#include <stdlib.h>
double uses(const char *s) { char *e; double d = strtod(s, &e); if (!e) exit(2); return d; }
USES
$cc -O2 -std=gnu11 -march=x86-64-v3 -c "$work/uses.c" -o "$work/uses.o" || exit 3
needles='malloc|calloc|realloc|free|exit|abort|strtod'
unit=$(nm -u "$work/stage2.o" | awk '{ print $NF }' | grep -xE "$needles")
control=$(nm -u "$work/uses.o" | awk '{ print $NF }' | grep -xE "$needles")
if [ -n "$unit" ]; then
  printf 'FAIL: the unit references: %s\n' "$(echo "$unit")" >&2
  exit 1
fi
if [ -z "$control" ]; then
  echo 'SETUP: the symbol detector did not see the control' >&2
  exit 3
fi

# --- the rows --------------------------------------------------------------
z() { head -c "$1" /dev/zero | tr '\0' '0'; }

{
  printf '1.%s\n'                 "$(z 1000)"                  # 1: 1.000...0
  printf '1.%s1\n'                "$(z 999)"                   # 2: 1 + 1e-1000
  printf '4503599627370496.5%s\n' "$(z 999)"                   # 3: exact tie
  printf '4503599627370496.5%s1\n' "$(z 998)"                  # 4: above the tie
  printf '4503599627370496.5%s\n' "$(z 99999)"                 # 5: exact tie
  printf '4503599627370496.5%s1\n' "$(z 99998)"                # 6: above it
  printf '4503599627370496.5%s\n' "$(z 999999)"                # 7: exact tie
  printf '4503599627370496.5%s1\n' "$(z 999998)"               # 8: above it
  printf '1%s\n'                  "$(z 1000000)"               # 9: overflow
  printf '0.%s1\n'                "$(z 999999)"                # 10: underflow
  printf '2.2250738585072014%se-308\n' "$(z 900)"              # 11: near normal
  printf '2.2250738585072011%se-308\n' "$(z 900)"              # 12
  printf '4.9406564584124654%se-324\n' "$(z 900)"              # 13: subnormal
  printf '2.4703282292062327%se-324\n' "$(z 900)"              # 14: half-min
  printf '2.4703282292062328%se-324\n' "$(z 900)"              # 15
  printf '1.7976931348623157%se308\n' "$(z 900)"               # 16: max finite
  printf '1.7976931348623159%se308\n' "$(z 900)"               # 17: overflow
  printf '9007199254740993\n'                                  # 18: earlier ties
  printf '4503599627370496.5\n'                                # 19
  printf '4503599627370495.5\n'                                # 20
  printf '2.4703282292062327e-324\n'                           # 21
  printf '0.1000000000000000055511151231257827021181583404541015625\n'   # 22
  printf '0.1000000000000000055511151231257827021181583404541015626\n'   # 23
  printf '1.00000000000000011102230246251565404236316680908203125\n'     # 24
  printf '1.000000000000000111022302462515654042363166809082031250000001\n' # 25
  # At the smallest normal, where the rounding boundary below the candidate is
  # `(2^53+1)*2^-1075`: the tail digit is what forces the comparison there, and
  # the retained window ends exactly at the boundary's last digit.
  printf '2.2250738585072014%s1e-308\n' "$(z 899)"             # 26
  printf '2.2250738585072014%s0e-308\n' "$(z 900)"             # 27
} > "$work/rows.txt"

"$work/long" --cap < "$work/rows.txt" > "$work/out.txt" 2> "$work/err.txt"
status=$?
if [ "$status" -ne 0 ]; then
  echo "the conversion harness failed (status $status):" >&2
  cat "$work/err.txt" >&2
  tail -n 5 "$work/out.txt" >&2
  exit 1
fi

# Every row must agree, and the summary must show no allocation attempt.
summary=$(tail -n 1 "$work/out.txt")
case "$summary" in
  *mismatches=0*) ;;
  *) echo "FAIL: $summary" >&2; exit 1 ;;
esac
case "$summary" in
  *alloc_attempts=0*) ;;
  *) echo "FAIL: $summary" >&2; exit 1 ;;
esac
case "$summary" in
  *cap_refused=*) ;;
  *) echo "FAIL: the address-space control did not run: $summary" >&2; exit 1 ;;
esac
refused=$(printf '%s\n' "$summary" | sed -n 's/.*cap_refused=\([0-9]*\).*/\1/p')
if [ "${refused:-0}" -lt 2 ]; then
  echo "FAIL: the cap did not refuse the copy on the 10^5 and 10^6 rows: $summary" >&2
  exit 1
fi

# The sticky rows: same prefix, tail zeroed against one far nonzero digit.  The
# two encodings must differ, or the case is not exercising the sticky bit.
for pair in '3 4' '5 6' '7 8'; do
  set -- $pair
  a=$(awk -F '\t' -v r="$1" '$1 == r { print $2 }' "$work/out.txt")
  b=$(awk -F '\t' -v r="$2" '$1 == r { print $2 }' "$work/out.txt")
  if [ -z "$a" ] || [ -z "$b" ]; then
    echo "SETUP: rows $1 and $2 are missing" >&2
    exit 3
  fi
  if [ "$a" = "$b" ]; then
    echo "FAIL: rows $1 and $2 agree ($a); the tail did not change the rounding" >&2
    exit 1
  fi
done

rows=$(printf '%s\n' "$summary" | sed -n 's/^rows=\([0-9]*\).*/\1/p')
echo "long-lexeme agreement: $rows/$rows rows, no allocation on the conversion path"
echo "  address-space control: $refused refusals of the lexeme's copy size"
exit 0
