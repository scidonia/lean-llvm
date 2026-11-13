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
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "escape_guard.h"
#include "pipeline.h"
#include "entry.h"
#include "policy.h"

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

uint64_t leanllvm_route_stage_ns[3] = {
    ROUTE_STAGE_UNFILLED, ROUTE_STAGE_UNFILLED, ROUTE_STAGE_UNFILLED};

/* Reading a slot is an effect: the value is mutable state the adapter wrote,
   so the getter returns the runtime's IO result rather than a pure `uint64_t`.
   A pure extern with a literal index is a constant the compiler folds once --
   measured, with all three slots reported from the first call and every later
   repetition reading that cached value. */
lean_object *leanllvm_route_stage_ns_at(uint64_t i) {
  uint64_t v = i < 3 ? leanllvm_route_stage_ns[i] : 0;
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
  PC_DOC = 22
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

/* The class of an admission result. */
enum admit_tag {
  ADMIT_MEASURED = 0, /* the scan ran; the clause words follow */
  ADMIT_DOMAIN = 2    /* a precondition failed before the scan */
};

/* The clause that refused the document, in `admission`'s own order. */
enum admit_clause {
  ADMIT_NONE = 0,
  ADMIT_EMPTY = 1,
  ADMIT_LENGTH = 2,
  ADMIT_DEPTH = 3
};

/* The document's 64-byte blocks, without the overflow `(n + 63) / 64` has at
   `n` near `UINT64_MAX`. */
static uint64_t block_count(uint64_t n) { return n / 64 + (n % 64 != 0); }

/* What the document's structural delimiter sequence measures. */
typedef struct {
  int64_t max;        /* the maximum running depth: the clause's number */
  int64_t final;      /* the proved counter's recombined final depth */
  int64_t walk_final; /* the accumulator's own final depth */
  int64_t sum;        /* the proved counter's recombined prefix-depth sum */
  uint64_t tokens;    /* structural delimiters the fold stepped over */
  uint64_t blocks;    /* the document's 64-byte blocks */
  int candidate;      /* a quote or a backslash byte anywhere in the document */
} depth_facts;

/* The block's structural lanes, through the proved depth counter and
   recombined.  The unit starts every call at depth 0, so the block's prefix
   depths are its own plus the depth carried into it, which enters its sum once
   per lane; the carry after the block is the sum of the spans. */
static void depth_flush(const uint8_t *b, uint64_t n, uint8_t *tail,
                        uint64_t block, const uint32_t *lanes, uint64_t cnt,
                        int64_t *into, int64_t *sum) {
  const uint8_t *p = b + 64 * block;
  uint64_t rest = n - 64 * block;
  if (rest < 64) {
    memset(tail, 0, 64);
    memcpy(tail, p, (size_t)rest);
    p = tail;
  }
  int64_t stats[2];
  int64_t span = depth_count(p, (const int32_t *)lanes, (int64_t)cnt, stats);
  *sum += stats[1] + (int64_t)cnt * *into;
  *into += span;
}

/* The document's structural token walk, and the maximum it reaches.

   `structTokensFrom` is the rule: at a `"` the reference body scan runs and the
   walk continues past its stop, and a body that scan refuses ends the sequence
   there; any other byte is a structural delimiter if it is one of `{`/`[`/`}`/
   `]`, stepped `+1`/`-1`.  The walk is by position, not by the classifier's
   masks: `in_string` is the unescaped-quote reading, and a quote a backslash run
   precedes is *not* escaped to this walk -- at the top level there is no escape
   state, so `\"` opens a body the classifier would not open.  That document
   (`sweep-114` in the gate's fixed-seed set) is why the string state is carried
   here and the delimiter bytes are read by the walk.

   The maximum is tracked as the running depth grows, because neither statistic
   the proved counter returns determines one; the lanes the walk steps are handed
   to that counter per block, so the two arithmetics are over one list.  The
   candidate flag is the walk's own reading of the bytes it visits: a quote byte
   exists exactly when the walk visited one -- every body is opened by a quote the
   walk sees -- and a backslash outside a body is visited too, so the flag is true
   whenever the document carries either byte. */
static void depth_measure(const uint8_t *b, uint64_t n, depth_facts *f) {
  uint32_t lanes[64];
  uint8_t tail[64] __attribute__((aligned(32)));
  uint64_t nb = block_count(n);
  int64_t at = 0, into = 0, sum = 0, max = 0;
  uint64_t tokens = 0, nl = 0, block = 0;
  int cand = 0;

  for (uint64_t i = 0; i < n;) {
    uint8_t c = b[i];
    if (c == 0x22) { /* a string body, or the sequence's end */
      uint64_t stop;
      cand = 1;
      if (leanllvm_route_body_stop(b, n, i + 1, &stop)) break;
      i = stop;
      continue;
    }
    if (c == 0x5C) cand = 1;
    if (c == 0x5B || c == 0x7B || c == 0x5D || c == 0x7D) {
      int open = c == 0x5B || c == 0x7B;
      uint64_t blk = i / 64;
      if (blk != block) {
        if (nl) depth_flush(b, n, tail, block, lanes, nl, &into, &sum);
        nl = 0;
        block = blk;
      }
      lanes[nl++] = (uint32_t)(i & 63);
      at += open ? 1 : -1;
      if (at > max) max = at;
      tokens++;
    }
    i++;
  }
  if (nl) depth_flush(b, n, tail, block, lanes, nl, &into, &sum);

  f->max = max;
  f->final = into;
  f->walk_final = at;
  f->sum = sum;
  f->tokens = tokens;
  f->blocks = nb;
  f->candidate = cand;
}

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
   is the one precondition, and it is checked before a byte is read. */
static lean_object *admit_impl(lean_object *doc, uint64_t n, uint64_t maxInput,
                               uint64_t maxDepth) {
  uint64_t bytes = array_bytes(doc);
  if (n > bytes)
    return admit_result(ADMIT_DOMAIN, PC_DOC, n, bytes, 0, 0, 0, 0, ADMIT_NONE,
                        0);
  if (n == 0)
    return admit_result(ADMIT_MEASURED, 0, 1, 0, 0, 0, 0, 0, ADMIT_EMPTY, 0);
  if (n > maxInput)
    return admit_result(ADMIT_MEASURED, 0, maxInput, n, 0, 0, 0, 0,
                        ADMIT_LENGTH, 0);

  const uint8_t *b = lean_sarray_cptr(doc);
  depth_facts f;
  depth_measure(b, n, &f);
  uint64_t depth = (uint64_t)f.max;
  uint64_t clause = depth > maxDepth ? ADMIT_DEPTH : ADMIT_NONE;
  uint64_t verdict = clause == ADMIT_NONE ? 1 : 0;
  /* The escape-list guard, one presence pass over the same bytes.  Only a
     document the native clauses admit can reach the pipeline, so a refused one
     is not scanned: the fact costs nothing on a row the route refuses. */
  uint64_t skip = verdict ? (uint64_t)leanllvm_route_escape_can_skip(b, n) : 0;
  return admit_result(ADMIT_MEASURED, 0, maxDepth, depth, depth,
                      (uint64_t)f.candidate, f.blocks, verdict, clause, skip);
}

/* The depth facts, as their own pass over the document. */
static lean_object *depth_impl(lean_object *doc, uint64_t n) {
  uint64_t bytes = array_bytes(doc);
  if (n > bytes) {
    uint64_t w[9] = {ADMIT_DOMAIN, PC_DOC, n, bytes, 0, 0, 0, 0, 0};
    return word_result(DEPTH_HEADER_BYTES, w, 9);
  }
  depth_facts f = {0, 0, 0, 0, 0, 0, 0};
  if (n) depth_measure(lean_sarray_cptr(doc), n, &f);
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
  if (block_count(n) > past / 64)
    return failure(ROUTE_DOMAIN, PC_WINDOW_BLOCKS, block_count(n), past / 64);
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
