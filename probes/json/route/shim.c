/* shim.c -- the adapter between the Lean route and the native pipeline.
 *
 * It is the piece no Lean term can be: a Lean `ByteArray`'s data pointer is the
 * runtime's C API (`lean_sarray_cptr`), so the addresses the pipeline's ABI
 * takes can only be produced here.  The adapter copies every caller buffer the
 * object writes into its own allocation, so no native store reaches a
 * Lean-owned object, and returns the observable bytes as a fresh `ByteArray`.
 * The document window is the one buffer the object only reads, so it is handed
 * over in place (the caller's padding is required, not assumed; see the
 * precondition at `PC_WINDOW_BLOCKS`).
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
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "escape_guard.h"
#include "pipeline.h"
#include "pipeline_fast.h"
#include "pipeline_fast_plain.h"
#include "entry.h"
#include "policy.h"
#include "admission.h"

/* The proved stage-1 depth counter's one entry point, at the ABI
   `tests/v16/depth_count.ll` defines and `DepthCountRefine` proves: the
   document, an index array of positions in it, that array's length, and the
   two-word statistics slot the unit writes (the final depth and the sum of the
   prefix depths).  It is compiled from the fixture at the same `clang -c` line
   as the install's unit and linked beside the kernel units. */
extern int64_t depth_count(const uint8_t *buf, const int32_t *idx,
                           int64_t nidx, int64_t *stats);

/* The result's header: ten words, then the payload. */
#define ROUTE_HEADER_BYTES 80

/* ## Stage timing, and why it is gated
 *
 * `RouteMain.lean --stages` reports the route's stages separately, and three of
 * them happen inside this adapter: the copy of the caller's arrays, the native
 * call, and the copy of the result back.  A `ROUTE_TIMING` build records those
 * three intervals in `leanllvm_route_stage_ns` (nanoseconds, CLOCK_MONOTONIC)
 * and `leanllvm_route_stage_ns_at` reads a slot.  The slots are declared in
 * both builds so the program links either way, but they start at `UINT64_MAX`,
 * which no measured duration reaches: a build that never filled them reports
 * that rather than a zero that would read as a fast stage, and `--stages`
 * refuses to print a row.
 *
 * The gate is off unless `build.sh` is invoked with `TIMING=1`, and with it off
 * this translation unit contains no clock read at all -- `build.sh` asserts
 * with `nm` that `clock_gettime` is absent from the ordinary object's undefined
 * symbols and present in the instrumented one -- so the ordinary adapter's
 * work is the work it was before this instrument. */
#include <time.h>

/* A duration in nanoseconds no run reaches: 584 years. */
#define ROUTE_STAGE_UNFILLED UINT64_MAX

/* The stage slots.  Slots 0-2 are the three intervals the adapter has always
   recorded, with their meanings per entry:
 *
 *   0  the caller's arrays copied into the object's ABI (`route_impl`), or the
 *      document copy plus the cursor resets (the reuse entries);
 *   1  the native call;
 *   2  the copy-out: `build_result` and its two payload copies (the reuse
 *      entries: the result object and whatever it copies, which is the header
 *      alone in the no-copy variant).
 *
 * The candidate entry splits its own wrapper work further, so a route-native
 * row can be attributed without another clock around the call:
 *
 *   3  the document copy alone;
 *   4  the five cursor stores alone;
 *   5  the staging preconditions (the checks before the document copy);
 *   6  the returned cursors and the contract checks after the call.
 *
 * Slot 0 is the parent of 3 and 4: it spans both, so the residual below uses
 * slots 1 and 3-6 and never adds 0.  The remaining time between the Lean-side
 * call's brackets and the sum of those slots is the `route_ns` residual the
 * candidate rows report as `ffi_ns`.  It is not only the FFI and the runtime's
 * boxing: it is everything else between the brackets -- the FFI call path, the
 * pointer derivations at the call's entry and return, `route_init`'s branch,
 * and the result handling's boxing.  A build without `ROUTE_TIMING` leaves
 * every slot unfilled. */
uint64_t leanllvm_route_stage_ns[7] = {
    ROUTE_STAGE_UNFILLED, ROUTE_STAGE_UNFILLED, ROUTE_STAGE_UNFILLED,
    ROUTE_STAGE_UNFILLED, ROUTE_STAGE_UNFILLED, ROUTE_STAGE_UNFILLED,
    ROUTE_STAGE_UNFILLED};

/* Reading a slot is an effect: the value is mutable state the adapter wrote,
   so the getter returns the runtime's IO result rather than a pure `uint64_t`.
   A pure extern with a literal index is a constant the compiler folds once --
   measured, with all three slots reported from the first call and every later
   repetition reading that cached value. */
lean_object *leanllvm_route_stage_ns_at(uint64_t i) {
  uint64_t v = i < 7 ? leanllvm_route_stage_ns[i] : 0;
  return lean_io_result_mk_ok(lean_uint64_to_nat(v));
}

#ifdef ROUTE_TIMING
static uint64_t route_now_ns(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (uint64_t)ts.tv_sec * 1000000000ull + (uint64_t)ts.tv_nsec;
}
#endif

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
  PC_TOTAL = 20,
  PC_WINDOW_BLOCKS = 21,
  PC_DOC = 22,
  PC_REUSE_DOC = 23,
  PC_REUSE_ENT = 24,
  PC_REUSE_FAST_EP = 25,
  PC_CANDIDATE = 26
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

/* ## The staging buffers
 *
 * `RouteMain.lean`'s `stage` needs fresh zero-filled buffers at the record's
 * capacities.  Built in Lean as `ByteArray.mk (Array.replicate n 0)`, the fill
 * goes through `lean_mk_array`'s boxed replication and then the byte-array
 * conversion's element-by-element unboxing: 1.5-2.2 GB/s per byte written on
 * this machine, which is where the staging stage's time went.  Here the buffer
 * is one allocation and one `memset`, and the bytes handed over are the same
 * zeros the record's staging is stated with. */
LEAN_EXPORT lean_object *leanllvm_route_zeroed(uint64_t n) {
  size_t size = (size_t)n;
  lean_object *r = lean_alloc_sarray(1, size, size);
  if (size) memset(lean_sarray_cptr(r), 0, size);
  return lean_io_result_mk_ok(r);
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

/* ## The two-phase admission
 *
 * `admission` is the certified decision (`LeanLLVM/JsonKernelDomain.lean`) and
 * has four clauses: the document is non-empty, it is inside the input bound, it
 * nests no deeper than the bound admits, and the reference's character policy
 * refuses nothing in it.  The first three are facts about the bytes -- the third
 * is `docDepth`, the maximum of the stage-1 depth counter's fold over the
 * document's structural delimiter sequence; the fourth is the reference's own
 * `scanCharsEnd`, through `policyRefusal`.
 *
 * The decision is therefore taken in two phases.  Phase one is
 * `leanllvm_route_admit`: the depth walk below, which also reports the
 * policy-candidate flag, and the empty and length bounds compared against
 * numbers the caller supplies.  Phase two is
 * `leanllvm_route_policy`: the native character-policy scan `policy.c` defines,
 * run by the caller only when phase one saw a candidate.  The reference's own
 * `policyRefusal` is not called on this path; it is the oracle the route's
 * `--admit` mode measures and `check.sh` compares the native answer against,
 * row by row and at the refusal's class and byte.
 *
 * ## Why the policy phase may be skipped
 *
 * `policyRefusal` runs `policyRefusalAt` at every byte that is `"`, so a
 * document with no `"` byte has no reason to report.  The depth walk visits
 * every byte outside a body and opens every body at a quote it visits, so it
 * sees a quote byte whenever one exists, and it sees a backslash outside a body
 * directly; skipping the phase when its flag is false therefore cannot miss a
 * refusal, and consulting it when true runs the exact scan.  The flag stays true
 * past a refused body, because that body was opened by a quote the walk saw, so
 * a quote after it still sets it even though the walk stopped.
 *
 * ## The depth clause: the maximum structural nesting
 *
 * The clause is `docDepth`: the maximum of the stage-1 fold over the document's
 * *structural* delimiter sequence -- the `{`/`[`/`}`/`]` bytes outside string
 * bodies, in document order, stepped `+1`/`-1` -- and not the count of opener
 * bytes, not the final balance.  A string carrying 129 `[` bytes measures 0 and
 * is admitted; a document nested 129 levels measures 129 and is refused,
 * whatever else its bytes carry.
 *
 * The token sequence is `structTokensFrom`'s, walked by position: a `"` starts a
 * string body that is skipped to the reference body scan's stop, a body that scan
 * refuses ends the sequence, and every other byte is a structural delimiter if
 * it is one of `{`/`[`/`}`/`]`.  The walk steps the running depth over those
 * bytes and keeps the maximum -- a max-tracking accumulator, because neither of
 * the proved counter's two statistics determines a maximum.  The walk does not
 * read the classifier's `in_string` mask: that is the unescaped-quote reading,
 * and a quote a backslash run precedes is not escaped to this walk, so `\"` at
 * the top level opens a body the classifier would not open.  The gate's
 * fixed-seed sweep contains that document; it is why the string state is carried
 * here.
 *
 * Beside the maximum, the walk's lane list is handed to the proved depth counter
 * (`tests/v16/depth_count.ll`): it reports the sequence's final depth and the
 * sum of its prefix depths, and the adapter recombines them per block.  Its
 * recombined final depth and the accumulator's are two arithmetics over one
 * lane list, and `--admit` reports both so `check.sh` can compare them; the
 * maximum is the accumulator's alone and is compared against `docDepth`.
 *
 * ## Zero copy, and what the caller owes
 *
 * Phase one reads the caller's own `ByteArray` in place: no buffer is allocated,
 * and the last, partial block is copied into a padded 64-byte stack array only
 * where the proved counter is called on that block's lanes.  `route_impl`'s window
 * handoff is the same rule for the pipeline: the object's document parameter is
 * `const` in every unit, so the adapter hands over the caller's bytes instead of
 * copying them, and the window is required to cover the document's whole last
 * block rather than only its `n` bytes.
 */

/* The admission result's header: ten words, no payload.  `tag` names the
   measured class or a failed precondition; the other words are meaningful for
   one of the two. */
#define ADMIT_HEADER_BYTES 80

/* The depth pass's header: nine words, no payload. */
#define DEPTH_HEADER_BYTES 72

/* The character-policy scan's header: six words, no payload. */
#define POLICY_HEADER_BYTES 48

/* The class of a policy result. */
enum policy_tag {
  POLICY_SCANNED = 0, /* the scan ran; the class and the byte follow */
  POLICY_DOMAIN = 2,  /* a precondition failed before the scan */
  POLICY_ALLOC = 3    /* the scan's class array could not be allocated */
};

/* The class of an admission result and its clauses are `admission.h`'s. */

/* A word-addressed header, `words` words wide, no payload. */
static lean_object *word_result(size_t bytes, const uint64_t *w, size_t words) {
  lean_object *res = lean_alloc_sarray(1, bytes, bytes);
  uint8_t *out = lean_sarray_cptr(res);
  for (size_t i = 0; i < words; i++) store64(out + 8 * i, w[i]);
  return res;
}

/* Phase one's result.  `want`/`got` describe the clause's comparison, or the
   failed precondition when `tag` is `ADMIT_DOMAIN`; `depth` is the measured
   maximum structural nesting the depth clause compares (and zero on the empty
   and over-long paths, which refuse before a byte of the walk runs).  The last
   word is the escape-list guard's fact (`escape_guard.h`), taken in the same
   call as the other document facts because a separate native call costs more
   than the list the guard skips. */
static lean_object *admit_result(uint64_t tag, uint64_t detail, uint64_t want,
                                 uint64_t got, uint64_t depth,
                                 uint64_t candidate, uint64_t blocks,
                                 uint64_t verdict, uint64_t clause,
                                 uint64_t escape_skip) {
  uint64_t w[10] = {tag, detail, want, got, depth, candidate, blocks, verdict,
                    clause, escape_skip};
  return word_result(ADMIT_HEADER_BYTES, w, 10);
}

/* The document's bytes, which the caller provides the length of: `n > doc.size`
   is the one precondition, and it is checked before a byte is read.  The pass
   itself is `admission.h`'s, which the workspace probe calls directly; this
   wrapper only packs its answer into the header `RouteMain.lean` decodes. */
static lean_object *admit_impl(lean_object *doc, uint64_t n, uint64_t maxInput,
                               uint64_t maxDepth) {
  const uint8_t *b = lean_sarray_cptr(doc);
  admit_facts f;
  admit_phase1(b, n, array_bytes(doc), maxInput, maxDepth, &f);
  return admit_result(f.tag, f.tag == ADMIT_DOMAIN ? PC_DOC : 0, f.want, f.got,
                      f.depth, f.candidate, f.blocks, f.verdict, f.clause,
                      f.escape_skip);
}

/* The depth facts, as their own pass over the document. */
static lean_object *depth_impl(lean_object *doc, uint64_t n) {
  uint64_t bytes = array_bytes(doc);
  if (n > bytes) {
    uint64_t w[9] = {ADMIT_DOMAIN, PC_DOC, n, bytes, 0, 0, 0, 0, 0};
    return word_result(DEPTH_HEADER_BYTES, w, 9);
  }
  depth_facts f = {0, 0, 0, 0, 0, 0, 0};
  if (n) admit_depth_measure(lean_sarray_cptr(doc), n, &f);
  uint64_t w[9] = {ADMIT_MEASURED, 0, 0, 0, (uint64_t)f.final, (uint64_t)f.sum,
                   f.tokens, (uint64_t)f.max, (uint64_t)f.walk_final};
  return word_result(DEPTH_HEADER_BYTES, w, 9);
}

/* Phase two's result.  `tag` is the measured class or the failure that
   preceded it; the measured header's `want` is the document's length (the
   bytes the scan covered) and `got` is zero, and `class` and `pos` are the
   refusal the scan reported -- `POLICY_NONE` and 0 for a document the policy
   admits. */
static lean_object *policy_result(uint64_t tag, uint64_t detail, uint64_t want,
                                  uint64_t got, uint64_t class_,
                                  uint64_t pos) {
  uint64_t w[6] = {tag, detail, want, got, class_, pos};
  return word_result(POLICY_HEADER_BYTES, w, 6);
}

/* The character-policy scan over the document's bytes, which the caller
   provides the length of: `n > doc.size` is the one precondition, and it is
   checked before a byte is read.  The scan itself is `policy.c`'s; this wraps
   its answer and its one failure (a class array that could not be allocated,
   reported rather than read as an admitted document). */
static lean_object *policy_impl(lean_object *doc, uint64_t n) {
  uint64_t bytes = array_bytes(doc);
  if (n > bytes) {
    return policy_result(POLICY_DOMAIN, PC_DOC, n, bytes, POLICY_NONE, 0);
  }
  uint64_t cls = POLICY_NONE, pos = 0;
  if (n && leanllvm_route_policy_scan(lean_sarray_cptr(doc), n, &cls, &pos) != 0) {
    return policy_result(POLICY_ALLOC, PC_NONE, n, 0, POLICY_NONE, 0);
  }
  return policy_result(POLICY_SCANNED, 0, n, 0, cls, pos);
}

/* The adapter's body.  `leanllvm_json_route` below wraps it in the runtime's IO
   result, so the route's call is sequenced against the clock reads that divide
   its stages; a pure `let` is free to move, and a call moved past a slot read
   would report the previous call's interval. */
static lean_object *route_impl(
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
     base are `len - 3` and the document needs `n`.  The mask unit reads every
     block's 64 bytes unconditionally, and the window is handed to the object in
     place (see the copy below), so the bytes past the base must cover the
     document's whole last block: `64 * blocks(n)`, not `n`. */
  uint64_t winLen = array_bytes(win);
  uint64_t past = winLen < 3 ? 0 : winLen - 3;
  if (winLen < 3 || n > past)
    return failure(ROUTE_DOMAIN, PC_WINDOW, n, past);
  if (admit_block_count(n) > past / 64)
    return failure(ROUTE_DOMAIN, PC_WINDOW_BLOCKS, admit_block_count(n), past / 64);
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
  /* The window is the one buffer the object only reads: every unit's document
     parameter is `const`, and the block requirement above keeps the read inside
     the caller's own bytes.  It is therefore borrowed, not copied, and it is
     neither freed nor written below.  The other thirteen buffers are written by
     the object, so they keep their own allocations. */
  uint8_t *copies[IN_COUNT] = {0};
  copies[IN_WIN] = lean_sarray_cptr(win);
#ifdef ROUTE_TIMING
  uint64_t route_t_copy0 = route_now_ns();
#endif
  for (int i = IN_WIN + 1; i < IN_COUNT; i++) {
    copies[i] = copy_array(ins[i]);
    if (!copies[i]) {
      uint64_t bytes = array_bytes(ins[i]);
      for (int j = IN_WIN + 1; j < i; j++) free(copies[j]);
      return failure(ROUTE_ALLOC, PC_NONE, bytes, 0);
    }
  }
#ifdef ROUTE_TIMING
  uint64_t route_t_native0 = route_now_ns();
  leanllvm_route_stage_ns[0] = route_t_native0 - route_t_copy0;
#endif

  uint64_t verdict = leanllvm_json_pipeline(
      copies[IN_WIN] + 3, n, (uint64_t *)copies[IN_SC], (uint64_t *)copies[IN_MK],
      (uint64_t *)copies[IN_ENTW], (uint32_t *)copies[IN_EP], epcap,
      (uint64_t *)copies[IN_NK], (uint32_t *)copies[IN_XP], xpcap,
      (uint64_t *)copies[IN_NXP], (uint64_t *)copies[IN_XCARRY],
      copies[IN_DST], dstcap, (uint64_t *)copies[IN_NDST],
      copies[IN_EV], evcap, (uint64_t *)copies[IN_NEV],
      (uint64_t *)copies[IN_ERR], arm);

#ifdef ROUTE_TIMING
  uint64_t route_t_out0 = route_now_ns();
  leanllvm_route_stage_ns[1] = route_t_out0 - route_t_native0;
#endif

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

  /* The copy-out interval closes after the staging copies are released, so the
     adapter's own work is entirely inside one of the three stages.  The
     window's bytes are the caller's and are not released here. */
  for (int i = IN_WIN + 1; i < IN_COUNT; i++) free(copies[i]);
#ifdef ROUTE_TIMING
  leanllvm_route_stage_ns[2] = route_now_ns() - route_t_out0;
#endif
  return out;
}

LEAN_EXPORT lean_object *leanllvm_json_route(
    lean_object *win, uint64_t n,
    lean_object *sc, lean_object *mk, lean_object *entw,
    lean_object *ep, uint64_t epcap, lean_object *nk,
    lean_object *xp, uint64_t xpcap, lean_object *nxp, lean_object *xcarry,
    lean_object *dst, uint64_t dstcap, lean_object *ndst,
    lean_object *ev, uint64_t evcap, lean_object *nev,
    lean_object *err, uint64_t arm) {
  return lean_io_result_mk_ok(
      route_impl(win, n, sc, mk, entw, ep, epcap, nk, xp, xpcap, nxp, xcarry,
                 dst, dstcap, ndst, ev, evcap, nev, err, arm));
}

/* The reuse entries hand a Lean `ByteArray`'s storage to the object as
   `uint64_t *` and `uint32_t *`.  Two facts make those casts sound, and neither
   is left unstated:
 *
 *   - the sarray payload's offset is a multiple of 8 (the assertion below), and
 *     Lean's object allocator returns at least pointer-aligned memory, so the
 *     word stores the pipeline ABI makes are naturally aligned;
 *   - the payload is reached only through those word types, plus character-type
 *     accesses (the `memset`s of the reset words and carries, the `memcpy`s of
 *     the document and the payloads, and the `uint8_t` `dst`/`ev` buffers): no
 *     address is read through one non-character type after being written
 *     through another.  C lets a character-type access alias any object, so the
 *     route needs no `-fno-strict-aliasing` -- type-based alias analysis sees
 *     no conflicting-typed pair on these addresses;
 *   - Lean's collector does not move an object, so the pointers stay valid for
 *     the whole call, and the call runs no Lean code that could relocate or
 *     mutate the array.
 *
 * The 32-bit casts are aligned a fortiori.  A build for an architecture without
 * unaligned word access would need these casts replaced by a staging copy; on
 * this route's `x86-64-v3` target they are checked here rather than assumed. */
_Static_assert(offsetof(lean_sarray_object, m_data) % 8 == 0,
               "the reuse entries cast a ByteArray's payload to word pointers");

/* ## The benchmark-only reused workspace
 *
 * `--consume-reuse` is the route with the workspace's per-call allocation and
 * protective copy removed, so a caller can price the native call on its own.
 * The default entry copies all thirteen caller buffers into its own
 * allocations on every call and frees them (`route_impl`); this entry hands the
 * caller's own arrays to `leanllvm_json_pipeline` in place, so the object's
 * stores land in the buffers the caller staged once.  It is a measurement
 * entry, not a second route: `RouteMain.lean`'s `routeReuse` is its only
 * caller, and no other mode reaches it.
 *
 * Writing into caller-owned memory is exactly what the default entry exists to
 * prevent, and it is safe here only because these buffers belong to the mode:
 * `--consume-reuse` allocates them once, hands the same arrays back on every
 * repetition, and nothing reads them between calls, so the mutation is not
 * observable through another Lean value.
 *
 * The per-call state is the state the object does not initialise for itself:
 * the five cursor words (`nk`, `nxp`, `ndst`, `nev`, `err`) and the two carries
 * the mask unit and the escape list read before they write (`sc`'s 24 bytes and
 * `xcarry`'s 16).  They are reset here, as the workspace bench's
 * `act_stage_reused` does, and nothing else in the buffers is rewritten: the
 * buffers deliberately carry the previous call's bytes instead of a zero fill.
 * Correctness rests on the read trace, not on an in-process comparison: every
 * byte the pipeline reads from the workspace is one this call wrote or the
 * adapter reset -- `sc` reset and `mk`/`entw` written before the emitter reads
 * them, `ep` from the reset cursor, no `xp` read (`nxp` reset to zero for arm
 * 0), `dst`/`ev` from their reset cursors, and the window's document copied in
 * this call with the base bytes and tail padding zero from staging.  A
 * divergence from `--consume` on the same document is found by diffing the two
 * rows offline, not inside the run.  The caller zeroed every buffer once at
 * allocation, so the first call starts from zeros and later calls inherit the
 * previous document's bytes.
 *
 * The document is copied into the window at offset 3 on every call: the window
 * is the one input the object only reads, and the caller re-reads the document
 * for every repetition.  The result is built by `build_result`, the same tagged
 * header and payload copy the default entry's outcome path uses, so a reuse row
 * is read by the same consumer code as a `--consume` row.
 *
 * A `ROUTE_TIMING` build fills the same three slots: slot 0 is the document
 * copy and the resets (there is no caller-array copy to price), slot 1 the
 * native call, slot 2 the result build and its two payload copies.
 */
static lean_object *route_reuse_impl(
    lean_object *win, lean_object *doc, uint64_t n,
    lean_object *sc, lean_object *mk, lean_object *entw,
    lean_object *ep, uint64_t epcap, lean_object *nk,
    lean_object *xp, uint64_t xpcap, lean_object *nxp, lean_object *xcarry,
    lean_object *dst, uint64_t dstcap, lean_object *ndst,
    lean_object *ev, uint64_t evcap, lean_object *nev,
    lean_object *err, uint64_t arm) {
  route_init();

  /* The default entry's preconditions, stated over the arrays this call will
     write in place, plus the document's own length: the window's padding and
     every capacity were fixed at the staged length, so a document longer than
     the staged `n` cannot be copied into the window and is refused rather than
     read past. */
  uint64_t winLen = array_bytes(win);
  uint64_t past = winLen < 3 ? 0 : winLen - 3;
  if (winLen < 3 || n > past)
    return failure(ROUTE_DOMAIN, PC_WINDOW, n, past);
  if (admit_block_count(n) > past / 64)
    return failure(ROUTE_DOMAIN, PC_WINDOW_BLOCKS, admit_block_count(n), past / 64);
  if (n > array_bytes(doc))
    return failure(ROUTE_DOMAIN, PC_REUSE_DOC, n, array_bytes(doc));
  if (array_bytes(sc) < 24) return failure(ROUTE_DOMAIN, PC_SC, 24, array_bytes(sc));
  if (array_bytes(mk) < 48) return failure(ROUTE_DOMAIN, PC_MK, 48, array_bytes(mk));
  if (array_bytes(entw) < 8)
    return failure(ROUTE_DOMAIN, PC_ENTW, 8, array_bytes(entw));
  if (epcap > UINT64_MAX / 4)
    return failure(ROUTE_DOMAIN, PC_EP, UINT64_MAX / 4, epcap);
  if (array_bytes(ep) < 4 * epcap)
    return failure(ROUTE_DOMAIN, PC_EP, 4 * epcap, array_bytes(ep));
  /* `epcap` is the caller's word count; the emitter's rule is what actually
     bounds its stores: `*nk + 64 * blocks + 8` slots at the cursor this call
     resets to zero (`entry.h`).  The reuse path writes the caller's own `ep`,
     so it checks the rule the object relies on rather than the count alone. */
  if (array_bytes(ep) / 4 < 64 * admit_block_count(n) + 8)
    return failure(ROUTE_DOMAIN, PC_EP, 64 * admit_block_count(n) + 8,
                   array_bytes(ep) / 4);
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

  uint8_t *winp = lean_sarray_cptr(win);
  uint8_t *scp = lean_sarray_cptr(sc);
  uint8_t *mkp = lean_sarray_cptr(mk);
  uint8_t *entwp = lean_sarray_cptr(entw);
  uint8_t *epp = lean_sarray_cptr(ep);
  uint8_t *nkp = lean_sarray_cptr(nk);
  uint8_t *xpp = lean_sarray_cptr(xp);
  uint8_t *nxpp = lean_sarray_cptr(nxp);
  uint8_t *xcarryp = lean_sarray_cptr(xcarry);
  uint8_t *dstp = lean_sarray_cptr(dst);
  uint8_t *ndstp = lean_sarray_cptr(ndst);
  uint8_t *evp = lean_sarray_cptr(ev);
  uint8_t *nevp = lean_sarray_cptr(nev);
  uint8_t *errp = lean_sarray_cptr(err);

#ifdef ROUTE_TIMING
  uint64_t route_t_reuse0 = route_now_ns();
#endif
  memcpy(winp + 3, lean_sarray_cptr(doc), (size_t)n);
  *(uint64_t *)nkp = 0;
  *(uint64_t *)nxpp = 0;
  *(uint64_t *)ndstp = 0;
  *(uint64_t *)nevp = 0;
  *(uint64_t *)errp = 0;
  memset(scp, 0, 24);
  memset(xcarryp, 0, 16);
#ifdef ROUTE_TIMING
  uint64_t route_t_native0 = route_now_ns();
  leanllvm_route_stage_ns[0] = route_t_native0 - route_t_reuse0;
#endif

  uint64_t verdict = leanllvm_json_pipeline(
      winp + 3, n, (uint64_t *)scp, (uint64_t *)mkp, (uint64_t *)entwp,
      (uint32_t *)epp, epcap, (uint64_t *)nkp, (uint32_t *)xpp, xpcap,
      (uint64_t *)nxpp, (uint64_t *)xcarryp, dstp, dstcap, (uint64_t *)ndstp,
      evp, evcap, (uint64_t *)nevp, (uint64_t *)errp, arm);

#ifdef ROUTE_TIMING
  uint64_t route_t_out0 = route_now_ns();
  leanllvm_route_stage_ns[1] = route_t_out0 - route_t_native0;
#endif

  uint64_t nkv = *(uint64_t *)nkp;
  uint64_t nxv = *(uint64_t *)nxpp;
  uint64_t ndv = *(uint64_t *)ndstp;
  uint64_t nevV = *(uint64_t *)nevp;
  uint64_t erv = *(uint64_t *)errp;

  /* The same cursor contract as the default entry: a returned cursor past its
     capacity is reported, never clamped, because the store has already left
     the buffer. */
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
                       0, 0, obs, dstp, (size_t)ndv, evp, (size_t)nevV);
  }

  /* The buffers are the caller's and are not released here. */
#ifdef ROUTE_TIMING
  leanllvm_route_stage_ns[2] = route_now_ns() - route_t_out0;
#endif
  return out;
}

/* The reuse entry: the default entry's arguments plus the document, with the
   thirteen arrays handed to the object in place.  `--consume-reuse` is its only
   caller; `route_reuse_impl` above states what it reuses and what it resets. */
LEAN_EXPORT lean_object *leanllvm_json_route_reuse(
    lean_object *win, lean_object *doc, uint64_t n,
    lean_object *sc, lean_object *mk, lean_object *entw,
    lean_object *ep, uint64_t epcap, lean_object *nk,
    lean_object *xp, uint64_t xpcap, lean_object *nxp, lean_object *xcarry,
    lean_object *dst, uint64_t dstcap, lean_object *ndst,
    lean_object *ev, uint64_t evcap, lean_object *nev,
    lean_object *err, uint64_t arm) {
  return lean_io_result_mk_ok(
      route_reuse_impl(win, doc, n, sc, mk, entw, ep, epcap, nk, xp, xpcap,
                       nxp, xcarry, dst, dstcap, ndst, ev, evcap, nev, err,
                       arm));
}

/* ## The candidate workspaces
 *
 * `--consume-reuse-fast*` are `--consume-reuse` with one of the benchmark-only
 * pipeline entries from `kernel/json/pipeline_fast.c` or
 * `kernel/json/pipeline_fast_plain.c` as the native call:
 *
 *   - `leanllvm_json_pipeline_fast` (`CAND_FUSED`): the list-free fused
 *     classifier, its inline UTF-8 gate, the three-slot emitter and the
 *     unchanged stage 2;
 *   - `leanllvm_json_pipeline_fast_list` (`CAND_LIST`): the same pass with the
 *     stage-1 escape list, so it writes `xp`/`*nxp` and stage 2 takes its
 *     list-driven decoder;
 *   - `leanllvm_json_pipeline_fast_plain_pos8` / `_b8` (`CAND_PLAIN_POS8` /
 *     `CAND_PLAIN_B8`): the `split_plain` shape -- the staged classifier, the
 *     entry word composed as `pipeline.c` composes it, the collected `ent`
 *     array through one entry emitter, then the UTF-8 unit -- with the pos8
 *     emitter (which needs `leanllvm_json_entry_table`, filled by
 *     `route_init`) or the table-free b8 emitter;
 *   - `leanllvm_json_pipeline_fast_best` (`CAND_BEST`): the per-document
 *     choice -- a bounded prefix scan selects the fused, the list, or the
 *     plain pos8 entry and calls it unchanged, so its `xp`/`*nxp` is the
 *     chosen entry's (empty and untouched for the list-free choices, the list
 *     stream for the larger-strings choice).
 *
 * None of them has a refinement theorem: their equivalence to the default is
 * this adapter's gate (`leanllvm_route_gate_candidate` below), not a proof.
 * The default entry and every other mode keep calling
 * `leanllvm_json_pipeline`, and `pipeline.h` is untouched by the candidates.
 *
 * The buffers are handed over in place and the document is copied into the
 * window on every call, exactly as the reuse entry does; the per-call state is
 * the five cursors (`nk`, `nxp`, `ndst`, `nev`, `err`).  There are no
 * `sc`/`mk`/`entw`/`xcarry` resets because the candidates keep their masks and
 * carries in registers or in locals; `ent` is the only caller-staged scratch
 * (one word per 64-byte block), and every word it reads it wrote on the same
 * call.
 *
 * `ep` is staged at the default's capacity, which covers the candidate rule
 * (`entry.h`: `*nk + 64 * blocks + 8`, with the count reset to zero) plus the
 * default's own `64 * blocks + 9`.  `xp` is staged at the default's
 * `64 * blocks + 8` slots: the list-free candidates must hand it back
 * untouched, and `CAND_LIST` appends the escape positions from the zeroed
 * count, exactly where the default's `arm = 2` call appends them.
 *
 * The gate runs from the fresh staging once per mode invocation, not on the
 * timing loop's stale buffers.  That is enough because a candidate reads no
 * byte it did not write or the adapter did not reset on the same call: `ent`
 * is written for every block before the emitter reads it, `ep` from the reset
 * cursor before stage 2 reads it, `xp` from the reset count for `CAND_LIST`
 * and not at all for the list-free entries (`*nxp` stays zero), `dst`/`ev`
 * from their reset cursors, and the window holds the document copied on this
 * call (its base bytes and tail padding are the zeros staging left).  A
 * document whose length is unchanged but whose bytes change between
 * repetitions is measured without being re-gated.
 *
 * ## The no-copy result
 *
 * `--consume-reuse-fast-nocopy` runs this same call path and returns the
 * observation as the 80-byte header alone -- tag, detail, the expected and
 * observed words, then the six observation words -- with no payload.  The
 * consumer reads the staged arrays directly (`dst[0..ndst)`, `ev[0..nev)`), so
 * the result allocation and its two payload copies are gone and slot 2 prices
 * the header alone.  The emitted bytes are the candidate's own and are
 * unchanged: same call, same buffers, same resets.  The slot split (3 document
 * copy, 4 cursor resets, 5 preconditions, 6 post-call checks) makes the
 * wrapper's cost visible per row; the `route_ns` residual is the FFI path, the
 * pointer derivations and `route_init`, not only the FFI and the boxing.
 */
enum route_candidate {
  CAND_FUSED = 0,      /* pipeline_fast: list-free, b3 emitter */
  CAND_LIST = 1,       /* pipeline_fast_list: the arm-2 escape list, b3 */
  CAND_PLAIN_POS8 = 2, /* pipeline_fast_plain_pos8: split stage 1 */
  CAND_PLAIN_B8 = 3,   /* pipeline_fast_plain_b8: split stage 1 */
  CAND_BEST = 4        /* pipeline_fast_best: the per-document choice */
};

static lean_object *route_reuse_candidate_impl(
    lean_object *win, lean_object *doc, uint64_t n,
    lean_object *ent, lean_object *ep, uint64_t epcap,
    lean_object *nk, lean_object *xp, uint64_t xpcap, lean_object *nxp,
    lean_object *dst, uint64_t dstcap, lean_object *ndst,
    lean_object *ev, uint64_t evcap, lean_object *nev,
    lean_object *err, uint64_t variant, uint64_t nocopy) {
  route_init();

#ifdef ROUTE_TIMING
  uint64_t route_t_checks0 = route_now_ns();
#endif
  if (variant > CAND_BEST)
    return failure(ROUTE_DOMAIN, PC_CANDIDATE, CAND_BEST, variant);

  uint64_t nb = admit_block_count(n);
  uint64_t winLen = array_bytes(win);
  uint64_t past = winLen < 3 ? 0 : winLen - 3;
  if (winLen < 3 || n > past)
    return failure(ROUTE_DOMAIN, PC_WINDOW, n, past);
  if (nb > past / 64)
    return failure(ROUTE_DOMAIN, PC_WINDOW_BLOCKS, nb, past / 64);
  if (n > array_bytes(doc))
    return failure(ROUTE_DOMAIN, PC_REUSE_DOC, n, array_bytes(doc));
  if (array_bytes(ent) / 8 < nb)
    return failure(ROUTE_DOMAIN, PC_REUSE_ENT, nb, array_bytes(ent) / 8);
  if (epcap > UINT64_MAX / 4)
    return failure(ROUTE_DOMAIN, PC_EP, UINT64_MAX / 4, epcap);
  if (array_bytes(ep) < 4 * epcap)
    return failure(ROUTE_DOMAIN, PC_EP, 4 * epcap, array_bytes(ep));
  if (array_bytes(ep) / 4 < 64 * nb + 8)
    return failure(ROUTE_DOMAIN, PC_REUSE_FAST_EP, 64 * nb + 8,
                   array_bytes(ep) / 4);
  if (array_bytes(nk) < 8) return failure(ROUTE_DOMAIN, PC_NK, 8, array_bytes(nk));
  if (xpcap > UINT64_MAX / 4)
    return failure(ROUTE_DOMAIN, PC_XP, UINT64_MAX / 4, xpcap);
  if (array_bytes(xp) < 4 * xpcap)
    return failure(ROUTE_DOMAIN, PC_XP, 4 * xpcap, array_bytes(xp));
  /* The list candidate and the per-document choice (whose strings arm can be
     the list) append from the reset count, so the list unit's rule
     (`escape.h`: `*nxp + 64 * blocks + 8` entries) is `64 * blocks + 8` here. */
  if ((variant == CAND_LIST || variant == CAND_BEST) &&
      array_bytes(xp) / 4 < 64 * nb + 8)
    return failure(ROUTE_DOMAIN, PC_XP, 64 * nb + 8, array_bytes(xp) / 4);
  if (array_bytes(nxp) < 8)
    return failure(ROUTE_DOMAIN, PC_NXP, 8, array_bytes(nxp));
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

#ifdef ROUTE_TIMING
  leanllvm_route_stage_ns[5] = route_now_ns() - route_t_checks0;
#endif

  uint8_t *winp = lean_sarray_cptr(win);
  uint8_t *entp = lean_sarray_cptr(ent);
  uint8_t *epp = lean_sarray_cptr(ep);
  uint8_t *nkp = lean_sarray_cptr(nk);
  uint8_t *xpp = lean_sarray_cptr(xp);
  uint8_t *nxpp = lean_sarray_cptr(nxp);
  uint8_t *dstp = lean_sarray_cptr(dst);
  uint8_t *ndstp = lean_sarray_cptr(ndst);
  uint8_t *evp = lean_sarray_cptr(ev);
  uint8_t *nevp = lean_sarray_cptr(nev);
  uint8_t *errp = lean_sarray_cptr(err);

#ifdef ROUTE_TIMING
  uint64_t route_t_reuse0 = route_now_ns();
#endif
  memcpy(winp + 3, lean_sarray_cptr(doc), (size_t)n);
#ifdef ROUTE_TIMING
  uint64_t route_t_reset0 = route_now_ns();
  leanllvm_route_stage_ns[3] = route_t_reset0 - route_t_reuse0;
#endif
  *(uint64_t *)nkp = 0;
  *(uint64_t *)nxpp = 0;
  *(uint64_t *)ndstp = 0;
  *(uint64_t *)nevp = 0;
  *(uint64_t *)errp = 0;
#ifdef ROUTE_TIMING
  uint64_t route_t_native0 = route_now_ns();
  leanllvm_route_stage_ns[4] = route_t_native0 - route_t_reset0;
  leanllvm_route_stage_ns[0] = route_t_native0 - route_t_reuse0;
#endif

  uint64_t verdict;
  switch (variant) {
  case CAND_LIST:
    verdict = leanllvm_json_pipeline_fast_list(
        winp + 3, n, (uint64_t *)entp, (uint32_t *)epp, epcap, (uint64_t *)nkp,
        (uint32_t *)xpp, xpcap, (uint64_t *)nxpp, dstp, dstcap,
        (uint64_t *)ndstp, evp, evcap, (uint64_t *)nevp, (uint64_t *)errp);
    break;
  case CAND_PLAIN_POS8:
    verdict = leanllvm_json_pipeline_fast_plain_pos8(
        winp + 3, n, (uint64_t *)entp, (uint32_t *)epp, epcap, (uint64_t *)nkp,
        (uint32_t *)xpp, xpcap, (uint64_t *)nxpp, dstp, dstcap,
        (uint64_t *)ndstp, evp, evcap, (uint64_t *)nevp, (uint64_t *)errp);
    break;
  case CAND_PLAIN_B8:
    verdict = leanllvm_json_pipeline_fast_plain_b8(
        winp + 3, n, (uint64_t *)entp, (uint32_t *)epp, epcap, (uint64_t *)nkp,
        (uint32_t *)xpp, xpcap, (uint64_t *)nxpp, dstp, dstcap,
        (uint64_t *)ndstp, evp, evcap, (uint64_t *)nevp, (uint64_t *)errp);
    break;
  case CAND_BEST:
    verdict = leanllvm_json_pipeline_fast_best(
        winp + 3, n, (uint64_t *)entp, (uint32_t *)epp, epcap, (uint64_t *)nkp,
        (uint32_t *)xpp, xpcap, (uint64_t *)nxpp, dstp, dstcap,
        (uint64_t *)ndstp, evp, evcap, (uint64_t *)nevp, (uint64_t *)errp);
    break;
  default: /* CAND_FUSED, the only remaining value */
    verdict = leanllvm_json_pipeline_fast(
        winp + 3, n, (uint64_t *)entp, (uint32_t *)epp, epcap, (uint64_t *)nkp,
        (uint32_t *)xpp, xpcap, (uint64_t *)nxpp, dstp, dstcap,
        (uint64_t *)ndstp, evp, evcap, (uint64_t *)nevp, (uint64_t *)errp);
    break;
  }

#ifdef ROUTE_TIMING
  uint64_t route_t_out0 = route_now_ns();
  leanllvm_route_stage_ns[1] = route_t_out0 - route_t_native0;
#endif

  uint64_t nkv = *(uint64_t *)nkp;
  uint64_t nxv = *(uint64_t *)nxpp;
  uint64_t ndv = *(uint64_t *)ndstp;
  uint64_t nevV = *(uint64_t *)nevp;
  uint64_t erv = *(uint64_t *)errp;
  uint64_t epslots = array_bytes(ep) / 4;
  /* The list entry and the per-document choice (whose strings arm can be the
     list) write `xp`, so their count is bounded by the buffer's capacity; the
     list-free candidates must hand the count back as received, and this call
     reset it to zero. */
  int lists = variant == CAND_LIST || variant == CAND_BEST;
  int nxp_bad = lists ? nxv > xpcap : nxv != 0;
  uint64_t nxp_want = lists ? xpcap : 0;

  /* The contract checks are slot 6's; the timestamp is taken after the whole
     chain so the result construction (success or failure header) is slot 2. */
  uint64_t fail_tag = 0, fail_detail = 0, fail_want = 0, fail_got = 0;
  if (nkv > epslots) {
    fail_tag = ROUTE_CONTRACT;
    fail_detail = PC_CURSOR_NK;
    fail_want = epslots;
    fail_got = nkv;
  } else if (nxp_bad) {
    fail_tag = ROUTE_CONTRACT;
    fail_detail = PC_CURSOR_NXP;
    fail_want = nxp_want;
    fail_got = nxv;
  } else if (ndv > dstcap) {
    fail_tag = ROUTE_CONTRACT;
    fail_detail = PC_CURSOR_NDST;
    fail_want = dstcap;
    fail_got = ndv;
  } else if (nevV > evcap) {
    fail_tag = ROUTE_CONTRACT;
    fail_detail = PC_CURSOR_NEV;
    fail_want = evcap;
    fail_got = nevV;
  } else if (ndv > SIZE_MAX - ROUTE_HEADER_BYTES ||
             nevV > SIZE_MAX - ROUTE_HEADER_BYTES - (size_t)ndv) {
    fail_tag = ROUTE_CONTRACT;
    fail_detail = PC_TOTAL;
    fail_want = ndv;
    fail_got = nevV;
  }

#ifdef ROUTE_TIMING
  uint64_t route_t_result0 = route_now_ns();
  leanllvm_route_stage_ns[6] = route_t_result0 - route_t_out0;
#endif

  lean_object *out = NULL;
  if (fail_tag) {
    out = failure(fail_tag, fail_detail, fail_want, fail_got);
  } else if (nocopy) {
    /* The observation alone: the consumer reads the staged `dst` and `ev`
       between the cursors this header reports. */
    uint64_t hdr[10] = {verdict == 1 ? ROUTE_OBSERVED : ROUTE_REFUSED, PC_NONE,
                        0, 0, verdict, nkv, nxv, ndv, nevV, erv};
    out = word_result(ROUTE_HEADER_BYTES, hdr, 10);
  } else {
    uint64_t obs[6] = {verdict, nkv, nxv, ndv, nevV, erv};
    out = build_result(verdict == 1 ? ROUTE_OBSERVED : ROUTE_REFUSED, PC_NONE,
                       0, 0, obs, dstp, (size_t)ndv, evp, (size_t)nevV);
  }

#ifdef ROUTE_TIMING
  leanllvm_route_stage_ns[2] = route_now_ns() - route_t_result0;
#endif
  return out;
}

/* The candidate timing entry: the reuse call's buffers, less the four the
   candidates do not have, plus the `ent` scratch, the variant selector, and
   `nocopy` (`1` returns the 80-byte observation header and leaves the payload
   in the staged `dst`/`ev`).  `--consume-reuse-fast*` are its only callers. */
LEAN_EXPORT lean_object *leanllvm_json_route_reuse_candidate(
    lean_object *win, lean_object *doc, uint64_t n,
    lean_object *ent, lean_object *ep, uint64_t epcap,
    lean_object *nk, lean_object *xp, uint64_t xpcap, lean_object *nxp,
    lean_object *dst, uint64_t dstcap, lean_object *ndst,
    lean_object *ev, uint64_t evcap, lean_object *nev,
    lean_object *err, uint64_t variant, uint64_t nocopy) {
  return lean_io_result_mk_ok(
      route_reuse_candidate_impl(win, doc, n, ent, ep, epcap, nk, xp, xpcap,
                                 nxp, dst, dstcap, ndst, ev, evcap, nev, err,
                                 variant, nocopy));
}

/* ## The candidates' equivalence gate
 *
 * `leanllvm_route_gate_candidate` runs the default and the selected candidate
 * from the same fresh staging -- every buffer zeroed and the document copied
 * in, the state `--consume`'s staged call receives -- and compares the fields
 * `pipeline_fast.h` and `pipeline_fast_plain.h` list.  The reference arm is the
 * one the candidate's shape pairs with: `arm = 2` for `CAND_LIST` (the stage-1
 * escape list, with bit 0 clear so the pos8 table is needed), `arm = 0` for the
 * list-free and plain entries, and for `CAND_BEST` the arm its own `*nxp`
 * names -- zero means arm 0 with the buffer unchanged, non-zero means arm 2
 * with `xp[0..nxp)` compared (`gate_best_core` runs the candidate first and
 * the default at the selected arm).  The compared fields are the return value,
 * `err`, `nk` and `ep[0..nk)`, then `nxp` and `xp`: the list entry appends the
 * same positions as the default's `arm & 2` call, so `xp[0..nxp)` is compared;
 * every other entry must hand `nxp` and the whole `xp` buffer back as it
 * received them.  Then `ndst` and `dst[0..ndst)`, and `nev` and `ev[0..nev)`.
 * The first difference is reported as its field, the byte offset within the
 * field, and the default's and the candidate's values.  `ent` is internal
 * scratch and is not compared.
 *
 * The pos8 entry's table obligation is `route_init`'s: it fills the entry
 * unit's table before the gate's first default or candidate call, so neither
 * the `CAND_PLAIN_POS8` entry nor the default's arm-0 emitter can see an
 * unfilled table.
 *
 * The result is a five-word header: tag, field, offset, expected, observed.
 *
 * The comparison is of the fresh staging.  The timing loop's stale-buffer
 * calls are not re-gated; the read trace stated above (each candidate reads
 * only bytes it wrote or the adapter reset on the call) is what carries the
 * fresh result across, and a consumer-level divergence would be an offline row
 * difference against `--consume`.
 */
#define GATE_HEADER_BYTES 40

enum route_gate_tag {
  GATE_MATCH = 0,  /* every listed field agreed */
  GATE_DIFF = 1,   /* `field` is the first field that differed */
  GATE_DOMAIN = 2, /* a staging precondition or a cursor bound failed */
  GATE_ALLOC = 3   /* a gate snapshot could not be allocated */
};

/* The compared fields, in the order the gate visits them. */
enum route_gate_field {
  GATE_NONE = 0,
  GATE_VERDICT = 1,
  GATE_ERR = 2,
  GATE_NK = 3,
  GATE_EP = 4,
  GATE_NXP = 5,
  GATE_XP = 6,
  GATE_NDST = 7,
  GATE_DST = 8,
  GATE_NEV = 9,
  GATE_EV = 10
};

static lean_object *gate_result(uint64_t tag, uint64_t field, uint64_t off,
                                uint64_t want, uint64_t got) {
  uint64_t w[5] = {tag, field, off, want, got};
  return word_result(GATE_HEADER_BYTES, w, 5);
}

/* The buffers of one gate run, so both pipelines are handed one description of
   the same staging. */
typedef struct {
  uint8_t *win;
  size_t winLen;
  uint8_t *sc, *mk, *entw, *ep, *nk, *xp, *nxp, *xcarry, *ent;
  uint8_t *dst, *ndst, *ev, *nev, *err;
  size_t epBytes, xpBytes, entBytes, dstBytes, evBytes;
  const uint8_t *doc;
  size_t n;
} gate_buffers;

/* The fresh staging `--consume` gives every call: every buffer zeroed and the
   document copied into the window.  Both pipelines start here, so a difference
   is theirs and not the buffers'. */
static void gate_fresh(const gate_buffers *w) {
  memset(w->sc, 0, 24);
  memset(w->mk, 0, 48);
  memset(w->entw, 0, 8);
  memset(w->ep, 0, w->epBytes);
  memset(w->nk, 0, 8);
  memset(w->xp, 0, w->xpBytes);
  memset(w->nxp, 0, 8);
  memset(w->xcarry, 0, 16);
  memset(w->ent, 0, w->entBytes);
  memset(w->dst, 0, w->dstBytes);
  memset(w->ndst, 0, 8);
  memset(w->ev, 0, w->evBytes);
  memset(w->nev, 0, 8);
  memset(w->err, 0, 8);
  memset(w->win, 0, w->winLen);
  memcpy(w->win + 3, w->doc, w->n);
}

/* The first differing byte of two extents, if any. */
static int gate_diff(const uint8_t *a, const uint8_t *b, size_t len,
                     size_t *at) {
  for (size_t i = 0; i < len; i++) {
    if (a[i] != b[i]) {
      *at = i;
      return 1;
    }
  }
  return 0;
}

/* The per-document choice entry picks its shape from the document, so its
   reference arm is observable from its own `*nxp`: zero means the list-free
   shape (the default at arm 0, and the whole `xp` buffer must be as received);
   non-zero means the list (the default at arm 2, and `xp[0..nxp)` must match).
   The candidate runs first -- its count picks the arm -- and its outputs are
   snapshotted before the reference overwrites the buffers.  The comparison is
   `expected` = default, `observed` = candidate, as in `gate_candidate_impl`,
   and covers the same fields without weakening any of them. */
static lean_object *gate_best_core(const gate_buffers *w, uint64_t epcap,
                                   uint64_t xpcap, uint64_t dstcap,
                                   uint64_t evcap, uint64_t n) {
  uint8_t *ep_snap = NULL, *dst_snap = NULL, *ev_snap = NULL, *xp_snap = NULL;
  lean_object *res = NULL;
  uint64_t d_verdict = 0, d_err = 0, d_nk = 0, d_nxp = 0, d_ndst = 0,
           d_nev = 0;
  uint64_t c_verdict = 0, c_err = 0, c_nk = 0, c_nxp = 0, c_ndst = 0,
           c_nev = 0;
  size_t epUse = 0, dstUse = 0, evUse = 0, xpUse = 0, at = 0;
  uint64_t arm = 0;

  /* The candidate, from the fresh staging. */
  gate_fresh(w);
  c_verdict = leanllvm_json_pipeline_fast_best(
      w->win + 3, n, (uint64_t *)w->ent, (uint32_t *)w->ep, epcap,
      (uint64_t *)w->nk, (uint32_t *)w->xp, xpcap, (uint64_t *)w->nxp, w->dst,
      dstcap, (uint64_t *)w->ndst, w->ev, evcap, (uint64_t *)w->nev,
      (uint64_t *)w->err);
  c_err = *(uint64_t *)w->err;
  c_nk = *(uint64_t *)w->nk;
  c_nxp = *(uint64_t *)w->nxp;
  c_ndst = *(uint64_t *)w->ndst;
  c_nev = *(uint64_t *)w->nev;
  if (c_nk > w->epBytes / 4) {
    res = gate_result(GATE_DOMAIN, PC_CURSOR_NK, 0, w->epBytes / 4, c_nk);
    goto done;
  }
  if (c_nxp > xpcap) {
    res = gate_result(GATE_DOMAIN, PC_CURSOR_NXP, 0, xpcap, c_nxp);
    goto done;
  }
  if (c_ndst > dstcap) {
    res = gate_result(GATE_DOMAIN, PC_CURSOR_NDST, 0, dstcap, c_ndst);
    goto done;
  }
  if (c_nev > evcap) {
    res = gate_result(GATE_DOMAIN, PC_CURSOR_NEV, 0, evcap, c_nev);
    goto done;
  }

  arm = c_nxp > 0 ? 2 : 0;
  epUse = 4 * (size_t)c_nk;
  dstUse = (size_t)c_ndst;
  evUse = (size_t)c_nev;
  xpUse = arm == 2 ? 4 * (size_t)c_nxp : w->xpBytes;
  ep_snap = (uint8_t *)malloc(epUse ? epUse : 1);
  dst_snap = (uint8_t *)malloc(dstUse ? dstUse : 1);
  ev_snap = (uint8_t *)malloc(evUse ? evUse : 1);
  xp_snap = (uint8_t *)malloc(xpUse ? xpUse : 1);
  if (!ep_snap || !dst_snap || !ev_snap || !xp_snap) {
    res = gate_result(GATE_ALLOC, PC_NONE, 0,
                      (uint64_t)(epUse + dstUse + evUse + xpUse), 0);
    goto done;
  }
  memcpy(ep_snap, w->ep, epUse);
  memcpy(dst_snap, w->dst, dstUse);
  memcpy(ev_snap, w->ev, evUse);
  memcpy(xp_snap, w->xp, xpUse);

  /* The reference, from the same fresh staging, at the selected arm. */
  gate_fresh(w);
  d_verdict = leanllvm_json_pipeline(
      w->win + 3, n, (uint64_t *)w->sc, (uint64_t *)w->mk, (uint64_t *)w->entw,
      (uint32_t *)w->ep, epcap, (uint64_t *)w->nk, (uint32_t *)w->xp, xpcap,
      (uint64_t *)w->nxp, (uint64_t *)w->xcarry, w->dst, dstcap,
      (uint64_t *)w->ndst, w->ev, evcap, (uint64_t *)w->nev,
      (uint64_t *)w->err, arm);
  d_err = *(uint64_t *)w->err;
  d_nk = *(uint64_t *)w->nk;
  d_nxp = *(uint64_t *)w->nxp;
  d_ndst = *(uint64_t *)w->ndst;
  d_nev = *(uint64_t *)w->nev;
  if (d_nk > epcap || d_nk > w->epBytes / 4) {
    res = gate_result(GATE_DOMAIN, PC_CURSOR_NK, 0, epcap, d_nk);
    goto done;
  }
  if (d_nxp > xpcap) {
    res = gate_result(GATE_DOMAIN, PC_CURSOR_NXP, 0, xpcap, d_nxp);
    goto done;
  }
  if (d_ndst > dstcap) {
    res = gate_result(GATE_DOMAIN, PC_CURSOR_NDST, 0, dstcap, d_ndst);
    goto done;
  }
  if (d_nev > evcap) {
    res = gate_result(GATE_DOMAIN, PC_CURSOR_NEV, 0, evcap, d_nev);
    goto done;
  }

  /* The comparison, expected = default, observed = candidate. */
  if (d_verdict != c_verdict) {
    res = gate_result(GATE_DIFF, GATE_VERDICT, 0, d_verdict, c_verdict);
    goto done;
  }
  if (d_err != c_err) {
    res = gate_result(GATE_DIFF, GATE_ERR, 0, d_err, c_err);
    goto done;
  }
  if (d_nk != c_nk) {
    res = gate_result(GATE_DIFF, GATE_NK, 0, d_nk, c_nk);
    goto done;
  }
  if (gate_diff(w->ep, ep_snap, epUse, &at)) {
    res = gate_result(GATE_DIFF, GATE_EP, (uint64_t)at, w->ep[at], ep_snap[at]);
    goto done;
  }
  if (arm == 2) {
    /* The list the default's arm-2 call appended, against the candidate's. */
    if (d_nxp != c_nxp) {
      res = gate_result(GATE_DIFF, GATE_NXP, 0, d_nxp, c_nxp);
      goto done;
    }
    if (gate_diff(w->xp, xp_snap, xpUse, &at)) {
      res = gate_result(GATE_DIFF, GATE_XP, (uint64_t)at, w->xp[at],
                        xp_snap[at]);
      goto done;
    }
  } else {
    /* A list-free choice must hand the count and the whole buffer back as it
       received them (the default's arm-0 call left them zeroed). */
    if (c_nxp != 0) {
      res = gate_result(GATE_DIFF, GATE_NXP, 0, 0, c_nxp);
      goto done;
    }
    if (gate_diff(w->xp, xp_snap, xpUse, &at)) {
      res = gate_result(GATE_DIFF, GATE_XP, (uint64_t)at, w->xp[at],
                        xp_snap[at]);
      goto done;
    }
  }
  if (d_ndst != c_ndst) {
    res = gate_result(GATE_DIFF, GATE_NDST, 0, d_ndst, c_ndst);
    goto done;
  }
  if (gate_diff(w->dst, dst_snap, dstUse, &at)) {
    res = gate_result(GATE_DIFF, GATE_DST, (uint64_t)at, w->dst[at],
                      dst_snap[at]);
    goto done;
  }
  if (d_nev != c_nev) {
    res = gate_result(GATE_DIFF, GATE_NEV, 0, d_nev, c_nev);
    goto done;
  }
  if (gate_diff(w->ev, ev_snap, evUse, &at)) {
    res = gate_result(GATE_DIFF, GATE_EV, (uint64_t)at, w->ev[at], ev_snap[at]);
    goto done;
  }
  res = gate_result(GATE_MATCH, GATE_NONE, 0, 0, 0);

done:
  free(ep_snap);
  free(dst_snap);
  free(ev_snap);
  free(xp_snap);
  return res;
}

static lean_object *gate_candidate_impl(
    lean_object *win, lean_object *doc, uint64_t n,
    lean_object *sc, lean_object *mk, lean_object *entw,
    lean_object *ep, uint64_t epcap,
    lean_object *nk, lean_object *xp, uint64_t xpcap, lean_object *nxp,
    lean_object *xcarry, lean_object *ent,
    lean_object *dst, uint64_t dstcap, lean_object *ndst,
    lean_object *ev, uint64_t evcap, lean_object *nev,
    lean_object *err, uint64_t variant) {
  route_init();

  if (variant > CAND_BEST)
    return gate_result(GATE_DOMAIN, PC_CANDIDATE, 0, CAND_BEST, variant);

  uint64_t nb = admit_block_count(n);
  uint64_t winLen = array_bytes(win);
  uint64_t past = winLen < 3 ? 0 : winLen - 3;
  if (winLen < 3 || n > past)
    return gate_result(GATE_DOMAIN, PC_WINDOW, 0, n, past);
  if (nb > past / 64)
    return gate_result(GATE_DOMAIN, PC_WINDOW_BLOCKS, 0, nb, past / 64);
  if (n > array_bytes(doc))
    return gate_result(GATE_DOMAIN, PC_REUSE_DOC, 0, n, array_bytes(doc));
  if (array_bytes(sc) < 24)
    return gate_result(GATE_DOMAIN, PC_SC, 0, 24, array_bytes(sc));
  if (array_bytes(mk) < 48)
    return gate_result(GATE_DOMAIN, PC_MK, 0, 48, array_bytes(mk));
  if (array_bytes(entw) < 8)
    return gate_result(GATE_DOMAIN, PC_ENTW, 0, 8, array_bytes(entw));
  if (epcap > UINT64_MAX / 4)
    return gate_result(GATE_DOMAIN, PC_EP, 0, UINT64_MAX / 4, epcap);
  if (array_bytes(ep) < 4 * epcap)
    return gate_result(GATE_DOMAIN, PC_EP, 0, 4 * epcap, array_bytes(ep));
  if (array_bytes(ep) / 4 < 64 * nb + 8)
    return gate_result(GATE_DOMAIN, PC_REUSE_FAST_EP, 0, 64 * nb + 8,
                       array_bytes(ep) / 4);
  if (array_bytes(nk) < 8)
    return gate_result(GATE_DOMAIN, PC_NK, 0, 8, array_bytes(nk));
  if (xpcap > UINT64_MAX / 4)
    return gate_result(GATE_DOMAIN, PC_XP, 0, UINT64_MAX / 4, xpcap);
  if (array_bytes(xp) < 4 * xpcap)
    return gate_result(GATE_DOMAIN, PC_XP, 0, 4 * xpcap, array_bytes(xp));
  if ((variant == CAND_LIST || variant == CAND_BEST) &&
      array_bytes(xp) / 4 < 64 * nb + 8)
    return gate_result(GATE_DOMAIN, PC_XP, 0, 64 * nb + 8,
                       array_bytes(xp) / 4);
  if (array_bytes(nxp) < 8)
    return gate_result(GATE_DOMAIN, PC_NXP, 0, 8, array_bytes(nxp));
  if (array_bytes(xcarry) < 16)
    return gate_result(GATE_DOMAIN, PC_XCARRY, 0, 16, array_bytes(xcarry));
  if (array_bytes(ent) / 8 < nb)
    return gate_result(GATE_DOMAIN, PC_REUSE_ENT, 0, nb, array_bytes(ent) / 8);
  if (array_bytes(dst) < dstcap)
    return gate_result(GATE_DOMAIN, PC_DST, 0, dstcap, array_bytes(dst));
  if (array_bytes(ndst) < 8)
    return gate_result(GATE_DOMAIN, PC_NDST, 0, 8, array_bytes(ndst));
  if (array_bytes(ev) < evcap)
    return gate_result(GATE_DOMAIN, PC_EV, 0, evcap, array_bytes(ev));
  if (array_bytes(nev) < 8)
    return gate_result(GATE_DOMAIN, PC_NEV, 0, 8, array_bytes(nev));
  if (array_bytes(err) < 8)
    return gate_result(GATE_DOMAIN, PC_ERR, 0, 8, array_bytes(err));

  gate_buffers w;
  w.win = lean_sarray_cptr(win);
  w.winLen = (size_t)winLen;
  w.sc = lean_sarray_cptr(sc);
  w.mk = lean_sarray_cptr(mk);
  w.entw = lean_sarray_cptr(entw);
  w.ep = lean_sarray_cptr(ep);
  w.nk = lean_sarray_cptr(nk);
  w.xp = lean_sarray_cptr(xp);
  w.nxp = lean_sarray_cptr(nxp);
  w.xcarry = lean_sarray_cptr(xcarry);
  w.ent = lean_sarray_cptr(ent);
  w.dst = lean_sarray_cptr(dst);
  w.ndst = lean_sarray_cptr(ndst);
  w.ev = lean_sarray_cptr(ev);
  w.nev = lean_sarray_cptr(nev);
  w.err = lean_sarray_cptr(err);
  w.epBytes = (size_t)array_bytes(ep);
  w.xpBytes = (size_t)array_bytes(xp);
  w.entBytes = (size_t)array_bytes(ent);
  w.dstBytes = (size_t)dstcap;
  w.evBytes = (size_t)evcap;
  w.doc = lean_sarray_cptr(doc);
  w.n = (size_t)n;

  /* The per-document choice's reference arm depends on what the candidate
     chose, so its gate runs the candidate first and the default at the arm the
     candidate's `*nxp` names. */
  if (variant == CAND_BEST)
    return gate_best_core(&w, epcap, xpcap, dstcap, evcap, n);

  uint8_t *ep_snap = NULL, *dst_snap = NULL, *ev_snap = NULL, *xp_snap = NULL;
  lean_object *res = NULL;
  uint64_t d_verdict = 0, d_err = 0, d_nk = 0, d_nxp = 0, d_ndst = 0,
           d_nev = 0;
  uint64_t c_verdict = 0, c_err = 0, c_nk = 0, c_nxp = 0, c_ndst = 0,
           c_nev = 0;
  size_t epUse = 0, dstUse = 0, evUse = 0, xpUse = 0, at = 0;

  /* The default, from the fresh staging: the reference `--consume`'s adapter
     call receives, at the arm the candidate's shape pairs with. */
  uint64_t arm = variant == CAND_LIST ? 2 : 0;
  gate_fresh(&w);
  d_verdict = leanllvm_json_pipeline(
      w.win + 3, n, (uint64_t *)w.sc, (uint64_t *)w.mk, (uint64_t *)w.entw,
      (uint32_t *)w.ep, epcap, (uint64_t *)w.nk, (uint32_t *)w.xp, xpcap,
      (uint64_t *)w.nxp, (uint64_t *)w.xcarry, w.dst, dstcap,
      (uint64_t *)w.ndst, w.ev, evcap, (uint64_t *)w.nev, (uint64_t *)w.err,
      arm);
  d_err = *(uint64_t *)w.err;
  d_nk = *(uint64_t *)w.nk;
  d_nxp = *(uint64_t *)w.nxp;
  d_ndst = *(uint64_t *)w.ndst;
  d_nev = *(uint64_t *)w.nev;
  if (d_nk > epcap || d_nk > w.epBytes / 4) {
    res = gate_result(GATE_DOMAIN, PC_CURSOR_NK, 0, epcap, d_nk);
    goto done;
  }
  if (d_nxp > xpcap) {
    res = gate_result(GATE_DOMAIN, PC_CURSOR_NXP, 0, xpcap, d_nxp);
    goto done;
  }
  if (d_ndst > dstcap) {
    res = gate_result(GATE_DOMAIN, PC_CURSOR_NDST, 0, dstcap, d_ndst);
    goto done;
  }
  if (d_nev > evcap) {
    res = gate_result(GATE_DOMAIN, PC_CURSOR_NEV, 0, evcap, d_nev);
    goto done;
  }

  epUse = 4 * (size_t)d_nk;
  dstUse = (size_t)d_ndst;
  evUse = (size_t)d_nev;
  /* The list entry's `xp` is compared against the default's stream; every other
     entry must leave `xp` alone, so its whole staged buffer is snapshotted. */
  xpUse = variant == CAND_LIST ? 4 * (size_t)d_nxp : w.xpBytes;
  ep_snap = (uint8_t *)malloc(epUse ? epUse : 1);
  dst_snap = (uint8_t *)malloc(dstUse ? dstUse : 1);
  ev_snap = (uint8_t *)malloc(evUse ? evUse : 1);
  xp_snap = (uint8_t *)malloc(xpUse ? xpUse : 1);
  if (!ep_snap || !dst_snap || !ev_snap || !xp_snap) {
    res = gate_result(GATE_ALLOC, PC_NONE, 0,
                      (uint64_t)(epUse + dstUse + evUse + xpUse), 0);
    goto done;
  }
  memcpy(ep_snap, w.ep, epUse);
  memcpy(dst_snap, w.dst, dstUse);
  memcpy(ev_snap, w.ev, evUse);
  if (variant == CAND_LIST) memcpy(xp_snap, w.xp, xpUse);

  /* The candidate, from the same fresh staging.  A list-free entry's `xp` is
     snapshotted just before its call, so the gate can check it was left
     alone. */
  gate_fresh(&w);
  if (variant != CAND_LIST) memcpy(xp_snap, w.xp, xpUse);
  switch (variant) {
  case CAND_LIST:
    c_verdict = leanllvm_json_pipeline_fast_list(
        w.win + 3, n, (uint64_t *)w.ent, (uint32_t *)w.ep, epcap,
        (uint64_t *)w.nk, (uint32_t *)w.xp, xpcap, (uint64_t *)w.nxp, w.dst,
        dstcap, (uint64_t *)w.ndst, w.ev, evcap, (uint64_t *)w.nev,
        (uint64_t *)w.err);
    break;
  case CAND_PLAIN_POS8:
    c_verdict = leanllvm_json_pipeline_fast_plain_pos8(
        w.win + 3, n, (uint64_t *)w.ent, (uint32_t *)w.ep, epcap,
        (uint64_t *)w.nk, (uint32_t *)w.xp, xpcap, (uint64_t *)w.nxp, w.dst,
        dstcap, (uint64_t *)w.ndst, w.ev, evcap, (uint64_t *)w.nev,
        (uint64_t *)w.err);
    break;
  case CAND_PLAIN_B8:
    c_verdict = leanllvm_json_pipeline_fast_plain_b8(
        w.win + 3, n, (uint64_t *)w.ent, (uint32_t *)w.ep, epcap,
        (uint64_t *)w.nk, (uint32_t *)w.xp, xpcap, (uint64_t *)w.nxp, w.dst,
        dstcap, (uint64_t *)w.ndst, w.ev, evcap, (uint64_t *)w.nev,
        (uint64_t *)w.err);
    break;
  default: /* CAND_FUSED */
    c_verdict = leanllvm_json_pipeline_fast(
        w.win + 3, n, (uint64_t *)w.ent, (uint32_t *)w.ep, epcap,
        (uint64_t *)w.nk, (uint32_t *)w.xp, xpcap, (uint64_t *)w.nxp, w.dst,
        dstcap, (uint64_t *)w.ndst, w.ev, evcap, (uint64_t *)w.nev,
        (uint64_t *)w.err);
    break;
  }
  c_err = *(uint64_t *)w.err;
  c_nk = *(uint64_t *)w.nk;
  c_nxp = *(uint64_t *)w.nxp;
  c_ndst = *(uint64_t *)w.ndst;
  c_nev = *(uint64_t *)w.nev;
  if (c_nk > w.epBytes / 4) {
    res = gate_result(GATE_DOMAIN, PC_CURSOR_NK, 0, w.epBytes / 4, c_nk);
    goto done;
  }
  if (variant == CAND_LIST && c_nxp > xpcap) {
    res = gate_result(GATE_DOMAIN, PC_CURSOR_NXP, 0, xpcap, c_nxp);
    goto done;
  }
  if (c_ndst > dstcap) {
    res = gate_result(GATE_DOMAIN, PC_CURSOR_NDST, 0, dstcap, c_ndst);
    goto done;
  }
  if (c_nev > evcap) {
    res = gate_result(GATE_DOMAIN, PC_CURSOR_NEV, 0, evcap, c_nev);
    goto done;
  }

  /* The comparison, in `pipeline_fast.h`'s order. */
  if (c_verdict != d_verdict) {
    res = gate_result(GATE_DIFF, GATE_VERDICT, 0, d_verdict, c_verdict);
    goto done;
  }
  if (c_err != d_err) {
    res = gate_result(GATE_DIFF, GATE_ERR, 0, d_err, c_err);
    goto done;
  }
  if (c_nk != d_nk) {
    res = gate_result(GATE_DIFF, GATE_NK, 0, d_nk, c_nk);
    goto done;
  }
  if (gate_diff(ep_snap, w.ep, epUse, &at)) {
    res = gate_result(GATE_DIFF, GATE_EP, (uint64_t)at, ep_snap[at], w.ep[at]);
    goto done;
  }
  if (variant == CAND_LIST) {
    /* The escape positions the default's arm-2 call appended, against the
       candidate's list stream. */
    if (c_nxp != d_nxp) {
      res = gate_result(GATE_DIFF, GATE_NXP, 0, d_nxp, c_nxp);
      goto done;
    }
    if (gate_diff(xp_snap, w.xp, xpUse, &at)) {
      res = gate_result(GATE_DIFF, GATE_XP, (uint64_t)at, xp_snap[at],
                        w.xp[at]);
      goto done;
    }
  } else {
    /* A list-free entry must hand the count and the whole buffer back as it
       received them. */
    if (c_nxp != 0) {
      res = gate_result(GATE_DIFF, GATE_NXP, 0, 0, c_nxp);
      goto done;
    }
    if (gate_diff(xp_snap, w.xp, w.xpBytes, &at)) {
      res = gate_result(GATE_DIFF, GATE_XP, (uint64_t)at, xp_snap[at],
                        w.xp[at]);
      goto done;
    }
  }
  if (c_ndst != d_ndst) {
    res = gate_result(GATE_DIFF, GATE_NDST, 0, d_ndst, c_ndst);
    goto done;
  }
  if (gate_diff(dst_snap, w.dst, dstUse, &at)) {
    res = gate_result(GATE_DIFF, GATE_DST, (uint64_t)at, dst_snap[at], w.dst[at]);
    goto done;
  }
  if (c_nev != d_nev) {
    res = gate_result(GATE_DIFF, GATE_NEV, 0, d_nev, c_nev);
    goto done;
  }
  if (gate_diff(ev_snap, w.ev, evUse, &at)) {
    res = gate_result(GATE_DIFF, GATE_EV, (uint64_t)at, ev_snap[at], w.ev[at]);
    goto done;
  }
  res = gate_result(GATE_MATCH, GATE_NONE, 0, 0, 0);

done:
  free(ep_snap);
  free(dst_snap);
  free(ev_snap);
  free(xp_snap);
  return res;
}

/* The gate entry.  The `--consume-reuse-fast*` modes call it once before their
   timing loop; the stage report's slots are the timing entry's, so the gate's
   default run is never in a reported interval. */
LEAN_EXPORT lean_object *leanllvm_route_gate_candidate(
    lean_object *win, lean_object *doc, uint64_t n,
    lean_object *sc, lean_object *mk, lean_object *entw,
    lean_object *ep, uint64_t epcap,
    lean_object *nk, lean_object *xp, uint64_t xpcap, lean_object *nxp,
    lean_object *xcarry, lean_object *ent,
    lean_object *dst, uint64_t dstcap, lean_object *ndst,
    lean_object *ev, uint64_t evcap, lean_object *nev,
    lean_object *err, uint64_t variant) {
  return lean_io_result_mk_ok(
      gate_candidate_impl(win, doc, n, sc, mk, entw, ep, epcap, nk, xp, xpcap,
                          nxp, xcarry, ent, dst, dstcap, ndst, ev, evcap, nev,
                          err, variant));
}

/* ## The benchmark-only C consumer
 *
 * `leanllvm_route_consume_fast` walks the staged arena and event stream in C,
 * at the widths and stop rule `kernel/json/stage2.h` documents and the Lean
 * consumers implement: a key or string is 13 bytes (tag, a four-byte
 * little-endian length, an eight-byte span), a number 9 bytes, every other tag
 * 1, and a record that would run past the stream stops the walk instead of
 * reading past it.  It computes the same fields the Lean readings report -- the
 * token count, the event cursor at the stop, the arena extent, the checksum
 * (arena bytes plus every record's tag, length and payload, wrapping in 64
 * bits), whether the walk landed on the stream's end, and the value count (one
 * per token) -- so a mode can price the consumer without materialising one
 * Lean `Event` per token.
 *
 * The result is seven words: status (0 walked, 2 an extent past its array),
 * tokens, the event cursor at the stop, the arena extent, the checksum,
 * `walked`, and the value count.  The emitted bytes and the observation are the
 * pipeline's; this function only reads them, and a mode gates its fields
 * against the Lean readings before timing it.
 */
#define ROUTE_CONSUMER_WORDS 7
#define ROUTE_CONSUMER_BYTES (8 * ROUTE_CONSUMER_WORDS)

static uint32_t load32(const uint8_t *p) {
  return (uint32_t)p[0] | ((uint32_t)p[1] << 8) | ((uint32_t)p[2] << 16) |
         ((uint32_t)p[3] << 24);
}

static uint64_t load64(const uint8_t *p) {
  uint64_t v = 0;
  for (int i = 7; i >= 0; i--) v = (v << 8) | (uint64_t)p[i];
  return v;
}

static lean_object *consume_fast_impl(lean_object *dst, uint64_t ndst,
                                      lean_object *ev, uint64_t nev) {
  uint64_t w[ROUTE_CONSUMER_WORDS] = {0};
  if (ndst > array_bytes(dst) || nev > array_bytes(ev)) {
    w[0] = 2;
    return word_result(ROUTE_CONSUMER_BYTES, w, ROUTE_CONSUMER_WORDS);
  }
  const uint8_t *d = lean_sarray_cptr(dst);
  const uint8_t *e = lean_sarray_cptr(ev);
  uint64_t arena = 0;
  for (uint64_t i = 0; i < ndst; i++) arena += d[i];
  uint64_t k = 0, tokens = 0, sum = arena, walked = 1;
  while (k < nev) {
    uint8_t tag = e[k];
    uint64_t width = (tag == 5 || tag == 6) ? 13 : (tag == 7 ? 9 : 1);
    if (k + width > nev) {
      walked = 0;
      break;
    }
    uint64_t len = 0, payload = 0;
    if (width == 13) {
      len = (uint64_t)load32(e + k + 1);
      payload = load64(e + k + 5);
    } else if (width == 9) {
      payload = load64(e + k + 1);
    }
    sum += (uint64_t)tag + len + payload;
    k += width;
    tokens++;
  }
  w[0] = 0;
  w[1] = tokens;
  w[2] = k;
  w[3] = ndst;
  w[4] = sum;
  w[5] = walked;
  w[6] = tokens;
  return word_result(ROUTE_CONSUMER_BYTES, w, ROUTE_CONSUMER_WORDS);
}

/* The export's order is the Lean declaration's -- `consumeFast (dst ev :
   ByteArray) (ndst nev : UInt64)` -- so the two arrays come before the two
   extents; the walk's internal parameter order is unchanged. */
LEAN_EXPORT lean_object *leanllvm_route_consume_fast(
    lean_object *dst, lean_object *ev, uint64_t ndst, uint64_t nev) {
  return lean_io_result_mk_ok(consume_fast_impl(dst, ndst, ev, nev));
}

/* Phase one of the two-phase admission: the document, its length, and the two
   bounds the certified predicate states -- from `kernelMaxInput` and
   `kernelMaxDepth` in `RouteMain.lean`, so the numbers are the library's and not
   a second copy of them here. */
LEAN_EXPORT lean_object *leanllvm_route_admit(lean_object *doc, uint64_t n,
                                              uint64_t maxInput,
                                              uint64_t maxDepth) {
  return lean_io_result_mk_ok(admit_impl(doc, n, maxInput, maxDepth));
}

/* Phase two of the two-phase admission: the native character-policy scan over
   the document.  The caller runs it only when phase one's candidate flag is
   set, and compares its answer with the reference's `policyRefusal` in the
   route's `--admit` mode. */
LEAN_EXPORT lean_object *leanllvm_route_policy(lean_object *doc, uint64_t n) {
  return lean_io_result_mk_ok(policy_impl(doc, n));
}

/* The proved depth counter over the document's delimiter lanes: the facts, for
   the admission record, and never part of the decision. */
LEAN_EXPORT lean_object *leanllvm_route_depth(lean_object *doc, uint64_t n) {
  return lean_io_result_mk_ok(depth_impl(doc, n));
}
