/* admission.h -- the route's two-phase admission as a plain C computation.
 *
 * `shim.c` wraps this for the Lean route and `workspace.cc` calls it directly,
 * so the depth walk, the policy phase and the escape-list guard's fact are one
 * source in both.  Nothing here allocates except the policy scan's class array,
 * which is either the scan's own stack or a caller-supplied workspace.
 *
 * The clauses are `LeanLLVM.JsonKernelDomain.admission`'s: the document is
 * non-empty, it is inside the input bound, its `docDepth` is inside the depth
 * bound, and the reference's character policy refuses nothing in it.  Phase one
 * measures the depth facts and the policy-candidate flag; phase two runs the
 * native character-policy scan only where that flag is set, because a document
 * with no quote and no backslash byte has no body for the policy to refuse.
 *
 * `admit_decide` folds both phases into the answer `RouteMain.lean`'s `decide2`
 * takes, and is what the workspace instrument times as the admission stage.
 * `admit_phase1` is the adapter's entry, because the Lean route drives phase two
 * itself (it also measures and compares the scan).
 *
 * `block_count` is the overflow-free `(n + 63) / 64`.
 */
#ifndef LEANLLVM_ROUTE_ADMISSION_H
#define LEANLLVM_ROUTE_ADMISSION_H

#include <stdint.h>
#include <string.h>

#include "policy.h"
#include "escape_guard.h"

/* The proved stage-1 depth counter, at the ABI `tests/v16/depth_count.ll`
   defines: the document, an index array of positions in it, that array's
   length, and the two-word statistics slot the unit writes (the final depth and
   the sum of the prefix depths). */
extern int64_t depth_count(const uint8_t *buf, const int32_t *idx, int64_t nidx,
                           int64_t *stats);

/* The class of an admission result: the measured facts, or a precondition that
   failed before a byte was read. */
enum admit_tag {
  ADMIT_MEASURED = 0, /* the pass ran; the clause words follow */
  ADMIT_DOMAIN = 2    /* a precondition failed before the pass */
};

/* The clause that refused the document, in `admission`'s own order. */
enum admit_clause {
  ADMIT_NONE = 0,
  ADMIT_EMPTY = 1,
  ADMIT_LENGTH = 2,
  ADMIT_DEPTH = 3
};

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

/* The admission's answer, in the words `shim.c`'s header carries plus the
   policy phase's own answer (meaningful when `candidate` and the native clauses
   admitted, and `policy_class` is 0 for a document the policy admits). */
typedef struct {
  uint64_t tag;         /* ADMIT_MEASURED or ADMIT_DOMAIN */
  uint64_t detail;      /* the failed precondition, for ADMIT_DOMAIN */
  uint64_t want;        /* the clause's expected number, or the precondition's */
  uint64_t got;         /* the clause's observed number */
  uint64_t depth;       /* the measured maximum structural nesting */
  uint64_t candidate;   /* the walk saw a quote or a backslash */
  uint64_t blocks;      /* the document's 64-byte blocks */
  uint64_t verdict;     /* 1 admitted, 0 refused */
  uint64_t clause;      /* ADMIT_* */
  uint64_t escape_skip; /* the escape-list guard's decision */
  uint64_t policy_class; /* POLICY_NONE, or the refusal's class */
  uint64_t policy_pos;   /* the refusal's byte, when policy_class != 0 */
} admit_facts;

static uint64_t admit_block_count(uint64_t n) { return n / 64 + (n % 64 != 0); }

/* The block's structural lanes, through the proved depth counter and
   recombined.  The unit starts every call at depth 0, so the block's prefix
   depths are its own plus the depth carried into it, which enters its sum once
   per lane; the carry after the block is the sum of the spans. */
static void admit_depth_flush(const uint8_t *b, uint64_t n, uint8_t *tail,
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
   there; any other byte is a structural delimiter if it is one of
   `{`/`[`/`}`/`]`, stepped `+1`/`-1`.  The walk is by position, not by the
   classifier's masks: `in_string` is the unescaped-quote reading, and a quote a
   backslash run precedes is *not* escaped to this walk -- at the top level there
   is no escape state, so `\"` opens a body the classifier would not open.  The
   document the route's agreement gate carries for that case is why the string
   state is carried here and the delimiter bytes are read by the walk.

   The maximum is tracked as the running depth grows, because neither statistic
   the proved counter returns determines one; the lanes the walk steps are handed
   to that counter per block, so the two arithmetics are over one list. */
static void admit_depth_measure(const uint8_t *b, uint64_t n, depth_facts *f) {
  uint32_t lanes[64];
  uint8_t tail[64] __attribute__((aligned(32)));
  uint64_t nb = admit_block_count(n);
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
        if (nl) admit_depth_flush(b, n, tail, block, lanes, nl, &into, &sum);
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
  if (nl) admit_depth_flush(b, n, tail, block, lanes, nl, &into, &sum);

  f->max = max;
  f->final = into;
  f->walk_final = at;
  f->sum = sum;
  f->tokens = tokens;
  f->blocks = nb;
  f->candidate = cand;
}

/* Phase one over the document's bytes: `n` is the byte count the caller states,
   `doc_bytes` the buffer's own length (the adapter's one precondition), and
   `max_input`/`max_depth` the certified bounds. */
static void admit_phase1(const uint8_t *b, uint64_t n, uint64_t doc_bytes,
                         uint64_t max_input, uint64_t max_depth,
                         admit_facts *o) {
  memset(o, 0, sizeof *o);
  o->tag = ADMIT_MEASURED;
  if (n > doc_bytes) {
    o->tag = ADMIT_DOMAIN;
    o->want = n;
    o->got = doc_bytes;
    return;
  }
  if (n == 0) {
    o->want = 1;
    o->clause = ADMIT_EMPTY;
    return;
  }
  if (n > max_input) {
    o->want = max_input;
    o->got = n;
    o->clause = ADMIT_LENGTH;
    return;
  }

  depth_facts f;
  memset(&f, 0, sizeof f);
  admit_depth_measure(b, n, &f);
  o->depth = (uint64_t)f.max;
  o->candidate = (uint64_t)f.candidate;
  o->blocks = f.blocks;
  o->clause = o->depth > max_depth ? ADMIT_DEPTH : ADMIT_NONE;
  o->verdict = o->clause == ADMIT_NONE ? 1 : 0;
  o->want = max_depth;
  o->got = o->depth;
  /* The escape-list guard, one presence pass over the same bytes.  Only a
     document the native clauses admit can reach the pipeline, so a refused one
     is not scanned: the fact costs nothing on a row the route refuses. */
  o->escape_skip =
      o->verdict ? (uint64_t)leanllvm_route_escape_can_skip(b, n) : 0;
}

/* Both phases, as `decide2` takes them.  `ws`/`ws_cap` are the policy scan's
   class-array workspace, or NULL for the scan's own allocation.  A scan that
   cannot find an array is reported through `policy_class = UINT64_MAX`, which
   no measured class reaches. */
static void admit_decide(const uint8_t *b, uint64_t n, uint64_t max_input,
                         uint64_t max_depth, uint8_t *ws, uint64_t ws_cap,
                         admit_facts *o) {
  admit_phase1(b, n, n, max_input, max_depth, o);
  if (o->tag != ADMIT_MEASURED || !o->verdict || !o->candidate) return;
  uint64_t cls = POLICY_NONE, pos = 0;
  if (leanllvm_route_policy_scan_ws(b, n, ws, ws_cap, &cls, &pos) != 0) {
    o->policy_class = UINT64_MAX;
    o->policy_pos = 0;
    return;
  }
  o->policy_class = cls;
  o->policy_pos = pos;
  if (cls != POLICY_NONE) {
    o->verdict = 0;
    o->clause = ADMIT_NONE; /* a policy refusal is not a native clause */
  }
}

#endif
