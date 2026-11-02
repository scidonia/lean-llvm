/* Benchmark driver for one seam object.
 *
 * Calls the seam `iterations` times over a deterministic xorshift stream,
 * prints the final generator state, a checksum of the results, and the
 * elapsed nanoseconds.  Keeping the checksum in a volatile accumulator and
 * printing it prevents the loop from being optimised away, and comparing the
 * two units' checksums proves both computed the same results.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

extern uint64_t leanllvm_comma_mask8(uint64_t);

int main(int argc, char **argv) {
  if (argc != 2) { fprintf(stderr, "usage: %s <iterations>\n", argv[0]); return 2; }
  unsigned long n = strtoul(argv[1], NULL, 10);
  uint64_t s = 0x9E3779B97F4A7C15ull;
  uint64_t acc = 0;
  struct timespec a, b;
  clock_gettime(CLOCK_MONOTONIC_RAW, &a);
  for (unsigned long i = 0; i < n; ++i) {
    s ^= s << 13; s ^= s >> 7; s ^= s << 17;
    acc ^= leanllvm_comma_mask8(s);
  }
  clock_gettime(CLOCK_MONOTONIC_RAW, &b);
  double ns = (double)(b.tv_sec - a.tv_sec) * 1e9 + (double)(b.tv_nsec - a.tv_nsec);
  printf("state=%016llx checksum=%016llx ns=%.3f\n",
         (unsigned long long)s, (unsigned long long)acc, ns);
  return 0;
}
