/*
 * Corpus driver for the JSON block classifier's installed object.
 *
 *   classify_driver <file>...
 *
 * The object is the committed fixture compiled as it stands:
 *
 *   clang -c probes/install/ir/json-classify.candidate.ll \
 *     -o json-classify.candidate.o
 *   clang -O2 -o classify_driver probes/json/classify_driver.c \
 *     json-classify.candidate.o
 *
 * For every 32-byte window of every named file the driver calls
 * `leanllvm_json_classify32` — the symbol the object defines — and prints
 *
 *   <path>\t<offset>\t0x<eight lowercase hex digits>
 *
 * with the path exactly as given on the command line, so the output is
 * comparable line for line with `leanllvm-json-classify --windows`.  A file
 * shorter than 32 bytes contributes no window.
 *
 * Alignment: each window is copied into a 32-byte-aligned scratch buffer and
 * the classifier is called on that pointer, never on `buffer + offset`.  The
 * committed fixture's load carries no alignment operand: the capture drops
 * clang's `align 1` because the parser's `load` has no alignment field, and
 * under LLVM's reading an unadorned load assumes the type's ABI alignment.
 * For this build — `clang -c` on the fixture, without `-mavx2` — the load
 * lowers to two 16-byte `movdqa`s, so the object requires **16-byte**
 * alignment, not the type's 32.  Measured on this host: a 16-byte-aligned,
 * non-32-byte-aligned pointer returns `0x7bd6f7b7` and exits 0, while
 * `pad33`'s offset-1 window exits 139 before the staging was added, and 66 of
 * the corpus's 70 windows are at a non-zero offset.  The scratch buffer is
 * 32-byte aligned because that is the load's type alignment and is
 * conservative for a 16-byte requirement.  The driver therefore establishes
 * agreement on aligned windows only; the object's behaviour on an unaligned
 * pointer is not covered by this route.  That gap is real and is not removed
 * by staging: the fixture text says nothing about alignment, and the object
 * built from it assumes some.  Closing it needs one of the layers to change —
 * a capture that keeps `align 1` together with a parser that models or
 * deliberately ignores it, a candidate whose lowering does not assume
 * alignment, or a semantics that models alignment, which LeanLLVM's `load`
 * does not today.
 *
 * This is test infrastructure: it declares the symbol and calls it.  It does
 * not implement the classifier and asserts nothing about the object's
 * lowering; the comparison it feeds is what says the compiled object and the
 * certified Lean body agree on the windows offered to them.
 *
 * Exit status: 0 on success, 2 when an argument is missing or a file cannot be
 * read, so a setup fault is never read as a classification result.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern uint32_t leanllvm_json_classify32(const uint8_t *p);

static int window_file(const char *path) {
  FILE *f = fopen(path, "rb");
  if (!f) {
    fprintf(stderr, "classify_driver: cannot read '%s'\n", path);
    return 2;
  }
  if (fseek(f, 0, SEEK_END) != 0) {
    fprintf(stderr, "classify_driver: cannot seek '%s'\n", path);
    fclose(f);
    return 2;
  }
  long size = ftell(f);
  if (size < 0 || fseek(f, 0, SEEK_SET) != 0) {
    fprintf(stderr, "classify_driver: cannot measure '%s'\n", path);
    fclose(f);
    return 2;
  }
  uint8_t *buf = malloc(size > 0 ? (size_t)size : 1);
  if (buf == NULL) {
    fprintf(stderr, "classify_driver: out of memory reading '%s'\n", path);
    fclose(f);
    return 2;
  }
  if (size > 0 && fread(buf, 1, (size_t)size, f) != (size_t)size) {
    fprintf(stderr, "classify_driver: short read on '%s'\n", path);
    free(buf);
    fclose(f);
    return 2;
  }
  fclose(f);

  _Alignas(32) uint8_t window[32];
  for (long off = 0; off + 32 <= size; off++) {
    memcpy(window, buf + off, sizeof window);
    uint32_t mask = leanllvm_json_classify32(window);
    printf("%s\t%ld\t0x%08x\n", path, off, (unsigned)mask);
  }

  free(buf);
  return 0;
}

int main(int argc, char **argv) {
  if (argc < 2) {
    fprintf(stderr, "usage: classify_driver <file>...\n");
    return 2;
  }
  for (int i = 1; i < argc; i++) {
    int status = window_file(argv[i]);
    if (status != 0) return status;
  }
  return 0;
}
