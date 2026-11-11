/* shim.c -- the adapter between the Lean route and the native pipeline.
 *
 * It is the piece no Lean term can be: a Lean `ByteArray`'s data pointer is the
 * runtime's C API (`lean_sarray_cptr`), so the addresses the pipeline's ABI
 * takes can only be produced here.  The adapter copies every caller buffer into
 * its own allocation, so no native store reaches a Lean-owned object, and
 * returns the observable bytes as a fresh `ByteArray`.
 *
 * ## Result layout (little-endian words, then the payloads)
 *
 *   tag:8  detail:8  want:8  got:8
 *   verdict:8  nk:8  nxp:8  ndst:8  nev:8  err:8
 *   arena[0..ndst]  events[0..nev]
 *
 * `tag` names the outcome class: the object ran and accepted, the object ran
 * and refused, a staging precondition failed before the call, a staging copy
 * could not be allocated, or a returned cursor exceeded the capacity it was
 * given.  The observation words are the object's for the first two tags and
 * zero for the last three.  `detail` is a `ROUTE_PC_*` index naming the
 * precondition or cursor that failed; `want` and `got` carry its expected and
 * observed numbers, so the caller reports what failed rather than that
 * something did.  The payload follows the header only on the first two tags.
 *
 * ## No clamping, and why the checks are before the call
 *
 * A returned cursor larger than its capacity means the object stored past a
 * buffer.  A clamped cursor would present that as a shorter, well-formed
 * result: the store has already happened, and the truncation only removes the
 * evidence.  The cursors are therefore checked before a byte is copied out,
 * and a cursor past its capacity is reported as an internal contract
 * violation.  For the same reason every buffer's extent and the capacity
 * arithmetic are checked before the call: a check after the call cannot repair
 * a store that has already left the buffer.
 *
 * ## The POS8 table
 *
 * The entry emitter reads the unit's own static table, so the table has to be
 * filled before the first call.  Initialisation is part of this adapter's
 * setup (`route_init`), not an obligation on the caller: the caller cannot
 * observe the table, and an initialiser it invokes as a pure call can be
 * eliminated when the result is unused -- measured once, with every container
 * refused because the table stayed zero.  `route_init` calls the unit's
 * initialiser, which is an ordinary external call: it has side effects this
 * translation unit cannot prove away, so the call survives.
 */
#include <lean/lean.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "pipeline.h"
#include "entry.h"

/* The result's header: ten words, then the payload. */
#define ROUTE_HEADER_BYTES 80

/* The outcome classes. */
enum route_tag {
  ROUTE_OBSERVED = 0, /* the object ran and accepted (verdict 1) */
  ROUTE_REFUSED = 1,  /* the object ran and refused (verdict 0, err is its offset) */
  ROUTE_DOMAIN = 2,   /* a staging precondition failed before the call */
  ROUTE_ALLOC = 3,    /* a staging copy could not be allocated */
  ROUTE_CONTRACT = 4  /* a returned cursor exceeded its capacity */
};

/* The failed precondition, mirrored by `preconditionName` in RouteMain.lean. */
enum route_precondition {
  PC_NONE = 0,
  PC_WINDOW = 1,
  PC_SC = 2,
  PC_MK = 3,
  PC_ENTW = 4,
  PC_EP = 5,
  PC_NK = 6,
  PC_XP = 7,
  PC_NXP = 8,
  PC_XCARRY = 9,
  PC_DST = 10,
  PC_NDST = 11,
  PC_EV = 12,
  PC_NEV = 13,
  PC_ERR = 14,
  PC_ARM = 15,
  PC_CURSOR_NK = 16,
  PC_CURSOR_NXP = 17,
  PC_CURSOR_NDST = 18,
  PC_CURSOR_NEV = 19,
  PC_TOTAL = 20
};

/* The caller's arrays, in the order the copy loop walks them. */
enum route_input {
  IN_WIN, IN_SC, IN_MK, IN_ENTW, IN_EP, IN_NK, IN_XP, IN_NXP, IN_XCARRY,
  IN_DST, IN_NDST, IN_EV, IN_NEV, IN_ERR, IN_COUNT
};

static uint32_t route_table_slot[256 * 8];
static int route_table_ready;

/* Fill the entry unit's own table once per process.  The slot is the unit's
   8 KiB export: the unit's initialiser writes its static table and then the
   caller's slot, and only the static table is read by the emitter. */
static void route_init(void) {
  if (route_table_ready) return;
  leanllvm_json_entry_table(route_table_slot);
  route_table_ready = 1;
}

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

/* The array's byte length, compared as the ABI's `uint64_t` sizes. */
static uint64_t array_bytes(lean_object *a) {
  return (uint64_t)lean_sarray_size(a);
}

/* The tagged result.  `obs` is the six observation words, zero for a failure,
   and the payloads are copied only when their lengths are non-zero. */
static lean_object *build_result(uint64_t tag, uint64_t detail, uint64_t want,
                                 uint64_t got, const uint64_t *obs,
                                 const uint8_t *arena, size_t ndst,
                                 const uint8_t *events, size_t nev) {
  size_t total = ROUTE_HEADER_BYTES + ndst + nev;
  lean_object *res = lean_alloc_sarray(1, total, total);
  uint8_t *out = lean_sarray_cptr(res);
  store64(out + 0, tag);
  store64(out + 8, detail);
  store64(out + 16, want);
  store64(out + 24, got);
  for (int i = 0; i < 6; i++) store64(out + 32 + 8 * (size_t)i, obs[i]);
  if (ndst) memcpy(out + ROUTE_HEADER_BYTES, arena, ndst);
  if (nev) memcpy(out + ROUTE_HEADER_BYTES + ndst, events, nev);
  return res;
}

static lean_object *failure(uint64_t tag, uint64_t detail, uint64_t want,
                            uint64_t got) {
  static const uint64_t none[6] = {0, 0, 0, 0, 0, 0};
  return build_result(tag, detail, want, got, none, NULL, 0, NULL, 0);
}

LEAN_EXPORT lean_object *leanllvm_json_route(
    lean_object *win, uint64_t n,
    lean_object *sc, lean_object *mk, lean_object *entw,
    lean_object *ep, uint64_t epcap, lean_object *nk,
    lean_object *xp, uint64_t xpcap, lean_object *nxp, lean_object *xcarry,
    lean_object *dst, uint64_t dstcap, lean_object *ndst,
    lean_object *ev, uint64_t evcap, lean_object *nev,
    lean_object *err, uint64_t arm) {
  route_init();

  /* Preconditions, before any buffer is copied and before the call.  The
     window carries the document at offset 3, so its readable bytes past the
     base are `len - 3` and the document needs `n`. */
  uint64_t winLen = array_bytes(win);
  if (winLen < 3 || n > winLen - 3)
    return failure(ROUTE_DOMAIN, PC_WINDOW, n, winLen < 3 ? 0 : winLen - 3);
  if (array_bytes(sc) < 24) return failure(ROUTE_DOMAIN, PC_SC, 24, array_bytes(sc));
  if (array_bytes(mk) < 48) return failure(ROUTE_DOMAIN, PC_MK, 48, array_bytes(mk));
  if (array_bytes(entw) < 8)
    return failure(ROUTE_DOMAIN, PC_ENTW, 8, array_bytes(entw));
  if (epcap > UINT64_MAX / 4)
    return failure(ROUTE_DOMAIN, PC_EP, UINT64_MAX / 4, epcap);
  if (array_bytes(ep) < 4 * epcap)
    return failure(ROUTE_DOMAIN, PC_EP, 4 * epcap, array_bytes(ep));
  if (array_bytes(nk) < 8) return failure(ROUTE_DOMAIN, PC_NK, 8, array_bytes(nk));
  if (xpcap > UINT64_MAX / 4)
    return failure(ROUTE_DOMAIN, PC_XP, UINT64_MAX / 4, xpcap);
  if (array_bytes(xp) < 4 * xpcap)
    return failure(ROUTE_DOMAIN, PC_XP, 4 * xpcap, array_bytes(xp));
  if (array_bytes(nxp) < 8)
    return failure(ROUTE_DOMAIN, PC_NXP, 8, array_bytes(nxp));
  if (array_bytes(xcarry) < 16)
    return failure(ROUTE_DOMAIN, PC_XCARRY, 16, array_bytes(xcarry));
  if (array_bytes(dst) < dstcap)
    return failure(ROUTE_DOMAIN, PC_DST, dstcap, array_bytes(dst));
  if (array_bytes(ndst) < 8)
    return failure(ROUTE_DOMAIN, PC_NDST, 8, array_bytes(ndst));
  if (array_bytes(ev) < evcap)
    return failure(ROUTE_DOMAIN, PC_EV, evcap, array_bytes(ev));
  if (array_bytes(nev) < 8)
    return failure(ROUTE_DOMAIN, PC_NEV, 8, array_bytes(nev));
  if (array_bytes(err) < 8)
    return failure(ROUTE_DOMAIN, PC_ERR, 8, array_bytes(err));
  if ((arm & ~(uint64_t)7) != 0)
    return failure(ROUTE_DOMAIN, PC_ARM, 0, arm);

  lean_object *ins[IN_COUNT] = {win, sc, mk, entw, ep, nk, xp, nxp, xcarry,
                                dst, ndst, ev, nev, err};
  uint8_t *copies[IN_COUNT] = {0};
  for (int i = 0; i < IN_COUNT; i++) {
    copies[i] = copy_array(ins[i]);
    if (!copies[i]) {
      uint64_t bytes = array_bytes(ins[i]);
      for (int j = 0; j < i; j++) free(copies[j]);
      return failure(ROUTE_ALLOC, PC_NONE, bytes, 0);
    }
  }

  uint64_t verdict = leanllvm_json_pipeline(
      copies[IN_WIN] + 3, n, (uint64_t *)copies[IN_SC], (uint64_t *)copies[IN_MK],
      (uint64_t *)copies[IN_ENTW], (uint32_t *)copies[IN_EP], epcap,
      (uint64_t *)copies[IN_NK], (uint32_t *)copies[IN_XP], xpcap,
      (uint64_t *)copies[IN_NXP], (uint64_t *)copies[IN_XCARRY],
      copies[IN_DST], dstcap, (uint64_t *)copies[IN_NDST],
      copies[IN_EV], evcap, (uint64_t *)copies[IN_NEV],
      (uint64_t *)copies[IN_ERR], arm);

  uint64_t nkv = *(uint64_t *)copies[IN_NK];
  uint64_t nxv = *(uint64_t *)copies[IN_NXP];
  uint64_t ndv = *(uint64_t *)copies[IN_NDST];
  uint64_t nevV = *(uint64_t *)copies[IN_NEV];
  uint64_t erv = *(uint64_t *)copies[IN_ERR];

  /* A cursor past its capacity is an internal contract violation: the object
     wrote past a buffer, and returning a clamped count would report the
     corruption as a shorter result. */
  lean_object *out = NULL;
  if (nkv > epcap) {
    out = failure(ROUTE_CONTRACT, PC_CURSOR_NK, epcap, nkv);
  } else if (nxv > xpcap) {
    out = failure(ROUTE_CONTRACT, PC_CURSOR_NXP, xpcap, nxv);
  } else if (ndv > dstcap) {
    out = failure(ROUTE_CONTRACT, PC_CURSOR_NDST, dstcap, ndv);
  } else if (nevV > evcap) {
    out = failure(ROUTE_CONTRACT, PC_CURSOR_NEV, evcap, nevV);
  } else if (ndv > SIZE_MAX - ROUTE_HEADER_BYTES ||
             nevV > SIZE_MAX - ROUTE_HEADER_BYTES - (size_t)ndv) {
    out = failure(ROUTE_CONTRACT, PC_TOTAL, ndv, nevV);
  } else {
    uint64_t obs[6] = {verdict, nkv, nxv, ndv, nevV, erv};
    out = build_result(verdict == 1 ? ROUTE_OBSERVED : ROUTE_REFUSED, PC_NONE,
                       0, 0, obs, copies[IN_DST], (size_t)ndv,
                       copies[IN_EV], (size_t)nevV);
  }

  for (int i = 0; i < IN_COUNT; i++) free(copies[i]);
  return out;
}
