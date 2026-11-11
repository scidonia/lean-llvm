/* shim.c -- the adapter between the Lean route and the native pipeline.
 *
 * It is the piece no Lean term can be: a Lean `ByteArray`'s data pointer is the
 * runtime's C API (`lean_sarray_cptr`), so the addresses the pipeline's ABI
 * takes can only be produced here.  The adapter copies every caller buffer into
 * its own allocation, so no native store reaches a Lean-owned object, and
 * returns the observable bytes as a fresh `ByteArray`.
 *
 * Result layout (little-endian words, then the payloads):
 *   verdict:8  nk:8  nxp:8  ndst:8  nev:8  err:8
 *   arena[0..ndst]  events[0..nev]
 */
#include <lean/lean.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "pipeline.h"
#include "entry.h"

static uint8_t *copy_array(lean_object *a) {
  size_t n = lean_sarray_size(a);
  uint8_t *p = (uint8_t *)malloc(n ? n : 1);
  if (!p) return NULL;
  memcpy(p, lean_sarray_cptr(a), n);
  return p;
}

static void store64(uint8_t *p, uint64_t v) {
  for (int i = 0; i < 8; i++) p[i] = (uint8_t)(v >> (8 * i));
}

LEAN_EXPORT uint64_t leanllvm_json_route_table(lean_object *dst) {
  (void)dst;
  uint32_t *tmp = (uint32_t *)calloc(2048, sizeof(uint32_t));
  if (!tmp) return 0;
  leanllvm_json_entry_table(tmp);
  free(tmp);
  return 1;
}

LEAN_EXPORT lean_object *leanllvm_json_route(
    lean_object *win, uint64_t n,
    lean_object *sc, lean_object *mk, lean_object *entw,
    lean_object *ep, uint64_t epcap, lean_object *nk,
    lean_object *xp, uint64_t xpcap, lean_object *nxp, lean_object *xcarry,
    lean_object *dst, uint64_t dstcap, lean_object *ndst,
    lean_object *ev, uint64_t evcap, lean_object *nev,
    lean_object *err, uint64_t arm) {
  (void)epcap; (void)xpcap;
  size_t winLen = lean_sarray_size(win);
  /* the document's base is the window's byte 3 */
  uint8_t *wb = copy_array(win);
  uint8_t *scb = copy_array(sc);
  uint8_t *mkb = copy_array(mk);
  uint8_t *ewb = copy_array(entw);
  uint8_t *epb = copy_array(ep);
  uint8_t *nkb = copy_array(nk);
  uint8_t *xpb = copy_array(xp);
  uint8_t *nxb = copy_array(nxp);
  uint8_t *xcb = copy_array(xcarry);
  uint8_t *dsb = copy_array(dst);
  uint8_t *ndb = copy_array(ndst);
  uint8_t *evb = copy_array(ev);
  uint8_t *nvb = copy_array(nev);
  uint8_t *erb = copy_array(err);
  if (!wb || !scb || !mkb || !ewb || !epb || !nkb || !xpb || !nxb || !xcb ||
      !dsb || !ndb || !evb || !nvb || !erb || winLen < 3) {
    goto fail;
  }

  uint64_t verdict = leanllvm_json_pipeline(
      wb + 3, n, (uint64_t *)scb, (uint64_t *)mkb, (uint64_t *)ewb,
      (uint32_t *)epb, epcap, (uint64_t *)nkb,
      (uint32_t *)xpb, xpcap, (uint64_t *)nxb, (uint64_t *)xcb,
      dsb, dstcap, (uint64_t *)ndb,
      evb, evcap, (uint64_t *)nvb, (uint64_t *)erb, arm);

  uint64_t nkv = *(uint64_t *)nkb;
  uint64_t nxv = *(uint64_t *)nxb;
  uint64_t ndv = *(uint64_t *)ndb;
  uint64_t nevV = *(uint64_t *)nvb;
  uint64_t erv = *(uint64_t *)erb;
  if (ndv > dstcap) ndv = dstcap;
  if (nevV > evcap) nevV = evcap;

  size_t total = 48 + (size_t)ndv + (size_t)nevV;
  lean_object *res = lean_alloc_sarray(1, total, total);
  uint8_t *out = lean_sarray_cptr(res);
  store64(out + 0, verdict);
  store64(out + 8, nkv);
  store64(out + 16, nxv);
  store64(out + 24, ndv);
  store64(out + 32, nevV);
  store64(out + 40, erv);
  memcpy(out + 48, dsb, (size_t)ndv);
  memcpy(out + 48 + ndv, evb, (size_t)nevV);

  free(wb); free(scb); free(mkb); free(ewb); free(epb); free(nkb); free(xpb);
  free(nxb); free(xcb); free(dsb); free(ndb); free(evb); free(nvb); free(erb);
  return res;

fail:
  free(wb); free(scb); free(mkb); free(ewb); free(epb); free(nkb); free(xpb);
  free(nxb); free(xcb); free(dsb); free(ndb); free(evb); free(nvb); free(erb);
  return lean_alloc_sarray(1, 48, 48);
}
