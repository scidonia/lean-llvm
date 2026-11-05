/* The depth counter's corpus driver.
 *
 * `depth_count` is the installed unit's symbol.  The driver reads a corpus of
 * index arrays -- one row per case, `<name>\t<tokens>\t<indices>`, both lists
 * decimal and comma-separated and empty for the empty list -- stages the token
 * buffer and the index array in memory, calls the unit in the position the ABI
 * names, and prints
 *
 *   <name>\t<return>\t<stats[0]>\t<stats[1]>
 *
 * It holds no expectation.  The expected values are `depthSpec`'s, printed by
 * `leanllvm-depth-check` over the same corpus, and the scenario compares the
 * two: the return, the recorded depth and the recorded sum must each be the
 * specification's value for the row.  An index outside the token buffer is
 * refused rather than passed to the unit, because the model's read there is
 * undefined and a C read there is undefined too.
 *
 * A malformed row is reported on stderr and makes the exit status nonzero, so
 * an input fault is not read as a numeric disagreement.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern int64_t depth_count(const unsigned char *buf, const uint32_t *idx,
                           int64_t nidx, int64_t *stats);

#define MAX_TOKENS 4096
#define MAX_INDICES 4096

static int parse_list(const char *text, long *out, int max) {
  int n = 0;
  if (*text == '\0') return 0;
  while (*text != '\0') {
    char *end = NULL;
    long value = strtol(text, &end, 10);
    if (end == text || value < 0) return -1;
    if (n == max) return -1;
    out[n++] = value;
    text = end;
    if (*text == ',') {
      text++;
      if (*text == '\0') return -1;
    } else if (*text != '\0') {
      return -1;
    }
  }
  return n;
}

/* Stage one row and report what the unit did.  Returns 0, or -1 when the row
 * cannot be represented as the ABI's inputs. */
static int run_row(char *line) {
  char *name = line;
  char *sep1 = strchr(name, '\t');
  if (sep1 == NULL) return -1;
  *sep1 = '\0';
  char *tokens_text = sep1 + 1;
  char *sep2 = strchr(tokens_text, '\t');
  if (sep2 == NULL) return -1;
  *sep2 = '\0';
  char *indices_text = sep2 + 1;

  long tokens[MAX_TOKENS];
  long indices[MAX_INDICES];
  int ntok = parse_list(tokens_text, tokens, MAX_TOKENS);
  int nidx = parse_list(indices_text, indices, MAX_INDICES);
  if (ntok < 0 || nidx < 0) return -1;

  unsigned char buf[MAX_TOKENS] = {0};
  uint32_t idx[MAX_INDICES];
  for (int i = 0; i < ntok; i++) {
    if (tokens[i] > 255) return -1;
    buf[i] = (unsigned char)tokens[i];
  }
  for (int i = 0; i < nidx; i++) {
    if (indices[i] > 0xFFFFFFFFL || indices[i] >= ntok) return -1;
    idx[i] = (uint32_t)indices[i];
  }

  int64_t stats[2] = {-1, -1};
  int64_t ret = depth_count(buf, idx, (int64_t)nidx, stats);
  printf("%s\t%lld\t%lld\t%lld\n", name, (long long)ret,
         (long long)stats[0], (long long)stats[1]);
  return 0;
}

int main(int argc, char **argv) {
  if (argc != 2) {
    fprintf(stderr, "usage: %s <corpus.tsv>\n", argv[0]);
    return 2;
  }
  FILE *corpus = fopen(argv[1], "r");
  if (corpus == NULL) {
    perror(argv[1]);
    return 2;
  }
  char line[65536];
  int bad = 0;
  while (fgets(line, sizeof line, corpus) != NULL) {
    line[strcspn(line, "\n")] = '\0';
    if (line[0] == '\0' || line[0] == '#') continue;
    if (run_row(line) != 0) {
      fprintf(stderr, "malformed corpus row: %s\n", line);
      bad = 1;
    }
  }
  if (ferror(corpus)) {
    perror(argv[1]);
    fclose(corpus);
    return 2;
  }
  fclose(corpus);
  return bad;
}
