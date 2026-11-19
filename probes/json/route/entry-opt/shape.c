/* shape.c -- the entry-word shape of one document under the route's stage-1
   prologue: how many blocks carry a word, how many bytes of each nonzero word
   are empty, and how many positions the stream holds.

   This is the untimed description the entry-opt harness reports before its
   clock, and the reason its candidates are shaped the way they are: the
   measured pos8 emitter writes one 32-byte group per mask byte of a nonzero
   word, so a word with two occupied bytes pays for eight.

   Usage: shape <document>   (the document is read whole, and the caller's
   window is the route's: three zero bytes, the document, and 32 staged bytes
   past its end.)
*/
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "s1_block.h"

int main(int argc, char **argv) {
  if (argc != 2) { fprintf(stderr, "usage: shape <document>\n"); return 2; }
  FILE *f = fopen(argv[1], "rb");
  if (f == NULL) { perror(argv[1]); return 2; }
  if (fseek(f, 0, SEEK_END) != 0) { perror("fseek"); return 2; }
  long sz = ftell(f);
  if (sz < 0) { perror("ftell"); return 2; }
  if (fseek(f, 0, SEEK_SET) != 0) { perror("fseek"); return 2; }
  uint64_t n = (uint64_t)sz;
  uint64_t blocks = (n + 63) >> 6;
  uint8_t *win = calloc(3 + n + 32, 1);
  if (win == NULL) { fprintf(stderr, "shape: out of memory\n"); return 2; }
  if (fread(win + 3, 1, n, f) != n) { perror("fread"); return 2; }
  fclose(f);
  const uint8_t *doc = win + 3;

  s1_carry sc = {0, 0, 0};
  s1_masks m;
  uint64_t prevS = 0;
  uint64_t nonzero = 0, empty_bytes_in_nonzero = 0, bytes_in_nonzero = 0;
  uint64_t hist_bytes[9] = {0}, hist_pc[9] = {0};
  uint64_t hist_pc_more = 0, hist_bytes_more = 0;
  uint64_t positions = 0;

  for (uint64_t i = 0; i < blocks; i++) {
    leanllvm_json_s1_masks(doc + (i << 6), &sc, &m);
    uint64_t S = ~(m.quote | m.delim | m.in_string | m.ws);
    uint64_t ent = m.quote | (m.delim & ~m.in_string);
    ent |= S & ~((S << 1) | prevS);
    prevS = S >> 63;
    uint64_t lim = n - (i << 6);
    if (lim < 64) ent &= (1ULL << lim) - 1ULL;
    unsigned pc = (unsigned)__builtin_popcountll(ent);
    positions += pc;
    if (ent != 0) {
      nonzero++;
      unsigned nb = 0;
      for (unsigned b = 0; b < 8; b++)
        if ((unsigned)((ent >> (8 * b)) & 0xFFu) != 0) nb++;
      bytes_in_nonzero += 8;
      empty_bytes_in_nonzero += 8 - nb;
      if (nb <= 8) hist_bytes[nb]++; else hist_bytes_more++;
    }
    if (pc <= 8) hist_pc[pc]++; else hist_pc_more++;
  }

  printf("doc=%s size=%" PRIu64 " blocks=%" PRIu64 "\n", argv[1], n, blocks);
  printf("positions=%" PRIu64 " nonzero_blocks=%" PRIu64
         " zero_blocks=%" PRIu64 "\n",
         positions, nonzero, blocks - nonzero);
  printf("group_bytes_in_nonzero=%" PRIu64 " empty_group_bytes=%" PRIu64
         " (%.1f%%)\n",
         bytes_in_nonzero, empty_bytes_in_nonzero,
         bytes_in_nonzero ? 100.0 * (double)empty_bytes_in_nonzero /
                                (double)bytes_in_nonzero
                          : 0.0);
  printf("hist_popcount:");
  for (unsigned i = 0; i <= 8; i++) printf(" %u:%" PRIu64, i, hist_pc[i]);
  printf(" >8:%" PRIu64 "\n", hist_pc_more);
  printf("hist_nonzero_bytes_per_word:");
  for (unsigned i = 0; i <= 8; i++) printf(" %u:%" PRIu64, i, hist_bytes[i]);
  printf(" >8:%" PRIu64 "\n", hist_bytes_more);
  free(win);
  return 0;
}
