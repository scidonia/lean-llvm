/* verdict-probe.c -- withholding the escape list must not change the verdict.

   A bench-only control for `README.md`'s "what withholding the list does"
   section: two tiny documents whose strings carry a byte the reference parser
   refuses, run through the pipeline as committed and through the same stage-2
   call with `nxp = 0` -- the list-free arm, where stage 2 classifies each body
   by scanning its own span.

   The committed pipeline refuses both at offset 7.  With the list withheld the
   walk must refuse them at the same offset: the rescan validates the body, so
   the list is a decoding input and not the validation driver.  A structural
   refusal is in neither list's ownership and stays the same as well.

   Exit status: 0 when every withheld-list call reproduces the committed
   verdict and refusal offset, 3 when one does not. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "entry.h"
#include "pipeline.h"
#include "stage2.h"

static void *xalloc(size_t n) {
  void *p = malloc(n ? n : 1);
  if (p == NULL) { fprintf(stderr, "verdict-probe: out of memory\n"); exit(2); }
  return p;
}

/* Byte-explicit so the control byte and the malformed escape are unambiguous:
   {"a":"x<0x01>y"}  and  {"a":"x\qy"}. */
static const uint8_t doc_control[] = {0x7B, 0x22, 0x61, 0x22, 0x3A, 0x22,
                                      0x78, 0x01, 0x79, 0x22, 0x7D};
static const uint8_t doc_bad_escape[] = {0x7B, 0x22, 0x61, 0x22, 0x3A, 0x22,
                                         0x78, 0x5C, 0x71, 0x79, 0x22, 0x7D};
/* The affirmative control: a structural refusal, which the list does not own.
   {"a":} */
static const uint8_t doc_no_value[] = {0x7B, 0x22, 0x61, 0x22, 0x3A, 0x7D};

static int failures;

static void probe(const char *name, const uint8_t *doc, uint64_t n,
                  int expect_refuse_at) {
  const uint64_t nb = (n + 63) >> 6, off = 3;
  uint8_t *win = (uint8_t *)xalloc((size_t)n + off + 64);
  memset(win, 0, (size_t)n + off + 64);
  memcpy(win + off, doc, (size_t)n);
  const uint64_t epcap = 64 * nb + 9, xpcap = 64 * nb + 8;
  const uint64_t dstcap = n + 64, evcap = 13 * n + 128;
  uint32_t *ep = (uint32_t *)xalloc((size_t)epcap * 4);
  uint32_t *xp = (uint32_t *)xalloc((size_t)xpcap * 4);
  uint8_t *dst = (uint8_t *)xalloc((size_t)dstcap);
  uint8_t *ev = (uint8_t *)xalloc((size_t)evcap);
  uint64_t *sc = (uint64_t *)xalloc(24), *mk = (uint64_t *)xalloc(48);
  uint64_t *entw = (uint64_t *)xalloc(8), *xc = (uint64_t *)xalloc(16);
  memset(sc, 0, 24); memset(mk, 0, 48); memset(entw, 0, 8); memset(xc, 0, 16);

  uint64_t nk = 0, nxp = 0, ndst = 0, nev = 0, err = 0;
  uint64_t v = leanllvm_json_pipeline(win + off, n, sc, mk, entw, ep, epcap, &nk,
                                      xp, xpcap, &nxp, xc, dst, dstcap, &ndst,
                                      ev, evcap, &nev, &err, 2);
  printf("%-14s n=%llu nk=%llu nxp=%llu  pipeline: verdict=%llu err=%llu\n",
         name, (unsigned long long)n, (unsigned long long)nk,
         (unsigned long long)nxp, (unsigned long long)v,
         (unsigned long long)err);
  if (v != 0 || (expect_refuse_at >= 0 && err != (uint64_t)expect_refuse_at)) {
    fprintf(stderr, "GATE: %s: the committed pipeline did not refuse as expected\n",
            name);
    failures++;
  }

  uint64_t nd2 = 0, ne2 = 0, er2 = 0;
  uint64_t v2 = leanllvm_json_stage2(win + off, n, ep, nk, xp, 0, dst, dstcap,
                                     &nd2, ev, evcap, &ne2, &er2);
  printf("%-14s same walk, list withheld (nxp=0): verdict=%llu err=%llu nev=%llu\n",
         name, (unsigned long long)v2, (unsigned long long)er2,
         (unsigned long long)ne2);
  if (v2 != v || er2 != err) {
    fprintf(stderr,
            "GATE: %s: the withheld-list call is (%llu, err %llu), the committed "
            "call (%llu, err %llu)\n",
            name, (unsigned long long)v2, (unsigned long long)er2,
            (unsigned long long)v, (unsigned long long)err);
    failures++;
  }

  free(win); free(ep); free(xp); free(dst); free(ev);
  free(sc); free(mk); free(entw); free(xc);
}

int main(void) {
  static uint32_t table[256 * 8];
  leanllvm_json_entry_table(table);   /* the pos8 emitter's table, once per process */
  probe("control-byte", doc_control, sizeof doc_control, 7);
  probe("bad-escape", doc_bad_escape, sizeof doc_bad_escape, 7);
  /* The list owns the decoding route, not the structural rules: a document
     with no value after the colon is refused by both. */
  probe("structural", doc_no_value, sizeof doc_no_value, 5);
  if (failures != 0) {
    fprintf(stderr, "verdict-probe: %d gate(s) failed\n", failures);
    return 3;
  }
  printf("observation: withholding the list changes neither verdict nor refusal\n"
         "             offset; the rescan validates the same bytes\n");
  return 0;
}
