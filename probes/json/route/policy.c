/* policy.c -- the character-policy scan, native, over the stage-1 masks.

   `policyRefusal` (`LeanLLVM/JsonKernelDomain.lean`) is the certified rule.
   `policyRefusalAt doc i` runs the reference's own body scanner
   (`scanCharsEnd doc (i + 1) 0`) at every byte `i` that is `"`, and reports a
   refusal only for the two Policy reasons -- `.unpairedSurrogate off` and
   `.noncharacter off` -- at `i + 1 + off`.  `policyRefusal` is the first such
   `i` in ascending order, so the answer is the first quote byte, in document
   order, whose body scan reaches one of those two refusals before it reaches
   the closing quote or any other refusal.

   This unit computes that answer without the parser.  `policy_step` is
   `scanCharsAt`'s branch structure: the same accept set, the same lookahead,
   the same order in which a refusal is raised, and the same reason each branch
   names.  The scan's answer depends only on the position it starts at -- the
   body scanner's `off` is a position within the body, but every refusal it
   reports is a document position, and its fuel (`bs.size - i`) bounds a scan
   that advances at least one byte per step, so fuel never ends a scan the
   lookups would not have ended.  So `cls[i]`, the class a scan starting at `i`
   reaches, is a function of `i` alone, and it is computed once per position
   from the document's end: `cls[i]` is either raised at `i` or is `cls[next]`
   for the one position the step at `i` continues at.  That makes the exact scan
   one backward pass plus one forward pass, and no position is visited twice.

   ## What a refusal needs, and the screen

   A character-policy refusal is possible in a document only if one of two byte
   patterns occurs in it:

     - `5C 75`, the `\u` escape.  `unpairedSurrogate` is raised in that branch
       and nowhere else, and a `\u` escape is the only escape that can carry a
       noncharacter through `okConsIx` -- `EscVal`'s eight characters are all
       below `0x80`;
     - a byte at or above `0xEF`, the only lead byte a UTF-8 noncharacter can
       have.  Noncharacters are `U+FDD0..U+FDEF`, `U+FFFE`, `U+FFFF` and, above
       the BMP, `U+nFFFE`/`U+nFFFF`: three-byte forms lead with `0xEF`, and
       four-byte forms with `0xF0..0xF4`.  `0xF5..0xFF` lead no character at all
       (they are `badUTF8`, which is not a policy refusal), so the test is wider
       than the rule and never narrower.

   `policy_possible` tests those two patterns over the document and, when
   neither occurs, the scan answers `POLICY_NONE` without visiting a position:
   the escape document of the route's corpus (`["\n" x 1000]`) is dismissed
   here, and so is every ASCII document and every document whose non-ASCII bytes
   are below `0xEF`.  The screen is a necessary condition, not a heuristic: it
   cannot hide a refusal, so it is exact where it fires and it is what makes the
   phase's cost a pass over the bytes rather than a parse of them.

   ## The quote bytes, from the mask unit's lanes

   The scan starts at every `"` byte, escaped or not, so it needs the document's
   quote bytes and not the string spans a well-formed document would have.  The
   stage-1 mask unit reports the block's unescaped quotes (`quote`) and every
   backslash byte (`backslash`); an escaped quote is a backslash's next byte, so
   the block's quote bytes are `quote | {p + 1 : backslash at p, b[p + 1] == '"'}`,
   and a backslash in the block's last lane is the next block's first byte's
   predecessor.  The carry threads forward, as the mask unit requires, so the
   pass visits blocks in order and lanes in order, which is the order
   `policyRefusal`'s `findSome?` reads.

   ## The cost

   A document the screen dismisses costs one pass, no allocation and no branch
   per byte: 32 bytes per iteration with one shifted compare pair and one
   unsigned compare.  A document it does not dismiss costs that pass, a
   one-byte-per-position class array (stack while the document is at most
   `POLICY_STACK_DOC` bytes, `n + 1` bytes of heap past it), one backward pass
   and the block pass.  The reference's `policyRefusal` is a body scan at every
   quote byte; on the route's escape document it was 99.2% of the admission
   stage, which is the cost this unit exists to remove.

   ## What this unit is not

   It is not a certificate.  Its agreement with `policyRefusal` is observed,
   per corpus row and at the refusal's class and byte, by
   `probes/json/route/check.sh`; there is no refinement theorem for it, and
   `kernel/json/` -- whose units are the certified ones -- does not contain it.
   A divergence is therefore a red in that scenario rather than a violated
   proof, which is why the reading is compared and not assumed. */
#include "policy.h"

#include <immintrin.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "s1_block.h"

/* The stack class array's extent in bytes; a document at most this long minus
   one position needs no heap.  4 KiB covers the route's corpus and the
   scenario's boundary documents, and the heap path covers the input bound. */
#define POLICY_STACK_DOC 4095

/* A document position no scan continues at: the closing quote, the end of the
   document, or a refusal that is not the character policy's. */
#define P_STOP UINT64_MAX

/* ## The step, at one position

   `self` is the class the position itself raises, or `POLICY_NONE` when the
   position accepts a character and the scan continues at `next` (`P_STOP`
   when the scan ends here without a refusal).  Every branch that advances
   returns a position greater than `i`, so a walk terminates, and every
   `next` is at most `n`, so it indexes a class array of `n + 1` entries. */
typedef struct {
  uint64_t next;
  uint8_t self;
} pstep;

/* `IsNoncharacter` (`LeanLLVM/JSON/Bytes.lean`): `U+FDD0..U+FDEF`, and every
   `U+nFFFE` / `U+nFFFF`.  The scan never forms a code point above `0x10FFFF`,
   so the low sixteen bits decide the second and third clauses. */
static int policy_noncharacter(uint32_t c) {
  if (c >= 0xFDD0u && c <= 0xFDEFu) return 1;
  uint32_t low = c & 0xFFFFu;
  return low == 0xFFFEu || low == 0xFFFFu;
}

/* `HexVal`: a decimal digit, or an upper- or lower-case hex letter. */
static int policy_hex(uint8_t b, uint32_t *v) {
  if (b >= 0x30 && b <= 0x39) {
    *v = (uint32_t)(b - 0x30);
    return 1;
  }
  if (b >= 0x41 && b <= 0x46) {
    *v = (uint32_t)(b - 0x37);
    return 1;
  }
  if (b >= 0x61 && b <= 0x66) {
    *v = (uint32_t)(b - 0x57);
    return 1;
  }
  return 0;
}

/* `Hex4` over four readable bytes. */
static int policy_hex4(const uint8_t *p, uint32_t *out) {
  uint32_t a, b, c, d;
  if (!policy_hex(p[0], &a) || !policy_hex(p[1], &b) || !policy_hex(p[2], &c) ||
      !policy_hex(p[3], &d))
    return 0;
  *out = (a << 12) | (b << 8) | (c << 4) | d;
  return 1;
}

static pstep policy_step(const uint8_t *b, uint64_t n, uint64_t i) {
  pstep s = {P_STOP, POLICY_NONE};
  uint8_t c = b[i];

  /* A quote ends the body: `scanCharsAt`'s `.ok` arm, no refusal. */
  if (c == 0x22) return s;

  if (c == 0x5C) {
    if (i + 1 >= n) return s; /* ended */
    uint8_t e = b[i + 1];
    /* `EscVal`'s eight characters.  All are below 0x80, so `okConsIx` cannot
       refuse them as noncharacters. */
    switch (e) {
      case 0x22: /* \" */
      case 0x5C: /* \\ */
      case 0x2F: /* \/ */
      case 0x62: /* \b */
      case 0x66: /* \f */
      case 0x6E: /* \n */
      case 0x72: /* \r */
      case 0x74: /* \t */
        s.next = i + 2;
        return s;
      default:
        break;
    }
    if (e != 0x75) return s; /* badEscape: not the character policy's */
    if (i + 5 >= n) return s; /* ended inside the hex digits */
    uint32_t cv;
    if (!policy_hex4(b + i + 2, &cv)) return s; /* badEscape */
    if (cv >= 0xD800u && cv <= 0xDBFFu) {
      /* A high surrogate must be followed by `\u` and a low surrogate; each
         missing or unexpected byte is `.unpairedSurrogate off`, reported at
         the escape's `\` -- this position. */
      if (i + 11 >= n) {
        s.self = POLICY_UNPAIRED;
        return s;
      }
      if (b[i + 6] != 0x5C || b[i + 7] != 0x75) {
        s.self = POLICY_UNPAIRED;
        return s;
      }
      uint32_t lv;
      if (!policy_hex4(b + i + 8, &lv)) return s; /* badEscape at off + 8 */
      if (lv < 0xDC00u || lv > 0xDFFFu) {
        s.self = POLICY_UNPAIRED;
        return s;
      }
      uint32_t cp = 0x10000u + (cv - 0xD800u) * 0x400u + (lv - 0xDC00u);
      if (policy_noncharacter(cp)) {
        s.self = POLICY_NONCHARACTER;
        return s;
      }
      s.next = i + 12;
      return s;
    }
    if (cv >= 0xDC00u && cv <= 0xDFFFu) {
      s.self = POLICY_UNPAIRED;
      return s;
    }
    if (policy_noncharacter(cv)) {
      s.self = POLICY_NONCHARACTER;
      return s;
    }
    s.next = i + 6;
    return s;
  }

  if (c < 0x80) {
    if (c < 0x20) return s; /* controlCharacter: not the character policy's */
    s.next = i + 1;
    return s;
  }

  /* The UTF-8 forms `scanCharsAt` accepts, byte for byte.  `0x80..0xC1` and
     `0xF5..0xFF` have no accepting branch. */
  if (c < 0xC2 || c > 0xF4) return s;
  if (c <= 0xDF) {
    if (i + 1 >= n) return s;
    uint8_t b1 = b[i + 1];
    if (b1 < 0x80 || b1 > 0xBF) return s;
    s.next = i + 2;
    return s;
  }
  if (c <= 0xEF) {
    if (i + 2 >= n) return s;
    uint8_t b1 = b[i + 1], b2 = b[i + 2];
    uint32_t cp;
    if (c == 0xE0) {
      if (b1 < 0xA0 || b1 > 0xBF || b2 < 0x80 || b2 > 0xBF) return s;
      cp = (uint32_t)(b1 - 0x80) * 0x40u + (uint32_t)(b2 - 0x80);
    } else if (c == 0xED) {
      if (b1 < 0x80 || b1 > 0x9F || b2 < 0x80 || b2 > 0xBF) return s;
      cp = 0xD000u + (uint32_t)(b1 - 0x80) * 0x40u + (uint32_t)(b2 - 0x80);
    } else {
      if (b1 < 0x80 || b1 > 0xBF || b2 < 0x80 || b2 > 0xBF) return s;
      cp = (uint32_t)(c - 0xE0) * 0x1000u + (uint32_t)(b1 - 0x80) * 0x40u +
           (uint32_t)(b2 - 0x80);
    }
    if (policy_noncharacter(cp)) {
      s.self = POLICY_NONCHARACTER;
      return s;
    }
    s.next = i + 3;
    return s;
  }

  if (i + 3 >= n) return s;
  uint8_t b1 = b[i + 1], b2 = b[i + 2], b3 = b[i + 3];
  if (b2 < 0x80 || b2 > 0xBF || b3 < 0x80 || b3 > 0xBF) return s;
  uint32_t cp;
  if (c == 0xF0) {
    if (b1 < 0x90 || b1 > 0xBF) return s;
    cp = (uint32_t)(b1 - 0x80) * 0x1000u + (uint32_t)(b2 - 0x80) * 0x40u +
         (uint32_t)(b3 - 0x80);
  } else if (c <= 0xF3) {
    if (b1 < 0x80 || b1 > 0xBF) return s;
    cp = (uint32_t)(c - 0xF0) * 0x40000u + (uint32_t)(b1 - 0x80) * 0x1000u +
         (uint32_t)(b2 - 0x80) * 0x40u + (uint32_t)(b3 - 0x80);
  } else { /* 0xF4 */
    if (b1 < 0x80 || b1 > 0x8F) return s;
    cp = 0x100000u + (uint32_t)(b1 - 0x80) * 0x1000u +
         (uint32_t)(b2 - 0x80) * 0x40u + (uint32_t)(b3 - 0x80);
  }
  if (policy_noncharacter(cp)) {
    s.self = POLICY_NONCHARACTER;
    return s;
  }
  s.next = i + 4;
  return s;
}

/* The class a scan starting at `i` reaches, given `cls` for every position it
   can continue at.  `cls[n]` is `POLICY_NONE`: a scan starting past the last
   byte is `ended`. */
static uint8_t policy_class_of(const uint8_t *b, uint64_t n, uint64_t i,
                               const uint8_t *cls) {
  pstep s = policy_step(b, n, i);
  if (s.self != POLICY_NONE) return s.self;
  return s.next == P_STOP ? POLICY_NONE : cls[s.next];
}

/* The byte a refusal found by a scan starting at `s` is reported at: the walk
   from `s` to the position that raises it.  `cls[s]` must not be
   `POLICY_NONE`. */
static uint64_t policy_refusal_pos(const uint8_t *b, uint64_t n, uint64_t s) {
  uint64_t i = s;
  for (;;) {
    pstep st = policy_step(b, n, i);
    if (st.self != POLICY_NONE) return i;
    i = st.next;
  }
}

/* ## The screen

   Whether a character-policy refusal is possible in these bytes at all: a
   `\u` escape, or a byte at or above `0xEF`.  Both are necessary conditions
   (the unit's comment states why), so a document this refuses to rule out is
   the only one the exact scan visits. */
static int policy_possible(const uint8_t *b, uint64_t n) {
  const __m256i bs = _mm256_set1_epi8((char)0x5C);
  const __m256i u = _mm256_set1_epi8((char)0x75);
  const __m256i ef = _mm256_set1_epi8((char)0xEF);
  __m256i hit = _mm256_setzero_si256();
  uint64_t i = 0;
  /* The shifted load reads `b[i + 32]`, so a chunk needs 33 readable bytes;
     the last 32 are the byte loop's. */
  for (; i + 33 <= n; i += 32) {
    __m256i v = _mm256_loadu_si256((const __m256i *)(const void *)(b + i));
    __m256i w = _mm256_loadu_si256((const __m256i *)(const void *)(b + i + 1));
    __m256i esc =
        _mm256_and_si256(_mm256_cmpeq_epi8(v, bs), _mm256_cmpeq_epi8(w, u));
    __m256i high = _mm256_cmpeq_epi8(_mm256_max_epu8(v, ef), v);
    hit = _mm256_or_si256(hit, _mm256_or_si256(esc, high));
  }
  if (!_mm256_testz_si256(hit, hit)) return 1;
  for (; i < n; i++) {
    if (b[i] >= 0xEF) return 1;
    if (b[i] == 0x5C && i + 1 < n && b[i + 1] == 0x75) return 1;
  }
  return 0;
}

/* The block pass: the document's quote bytes from the mask unit's lanes, and
   the first of them, in document order, whose scan reaches a refusal.  Returns
   the class and writes the refusal's byte. */
static uint64_t policy_first_quote(const uint8_t *b, uint64_t n,
                                   const uint8_t *cls, uint64_t *pos) {
  uint8_t tail[64] __attribute__((aligned(32)));
  s1_carry carry = {0, 0, 0};
  uint64_t blocks = n / 64 + (n % 64 != 0);
  int carry_quote = 0; /* the block's first byte is an escaped quote */

  for (uint64_t k = 0; k < blocks; k++) {
    const uint8_t *p = b + 64 * k;
    uint64_t rest = n - 64 * k;
    if (rest < 64) {
      memset(tail, 0, 64);
      memcpy(tail, p, (size_t)rest);
      p = tail;
    }
    s1_masks m;
    leanllvm_json_s1_masks(p, &carry, &m);

    /* The block's quote bytes: the unescaped ones the mask unit marks, and the
       escaped ones, which are a backslash lane's next byte. */
    uint64_t q = m.quote;
    uint64_t backslash = m.backslash;
    if (carry_quote) q |= 1;
    carry_quote = 0;
    while (backslash) {
      unsigned lane = (unsigned)__builtin_ctzll(backslash);
      backslash &= backslash - 1;
      if (lane == 63) {
        uint64_t at = 64 * k + 64;
        if (at < n && b[at] == 0x22) carry_quote = 1;
      } else if (p[lane + 1] == 0x22) {
        q |= (uint64_t)1 << (lane + 1);
      }
    }

    while (q) {
      unsigned lane = (unsigned)__builtin_ctzll(q);
      q &= q - 1;
      uint64_t start = 64 * k + lane + 1;
      if (cls[start] != POLICY_NONE) {
        *pos = policy_refusal_pos(b, n, start);
        return cls[start];
      }
    }
  }
  return POLICY_NONE;
}

int leanllvm_route_policy_scan(const uint8_t *b, uint64_t n, uint64_t *cls_o,
                               uint64_t *pos_o) {
  *cls_o = POLICY_NONE;
  *pos_o = 0;
  if (n == 0) return 0;
  if (!policy_possible(b, n)) return 0;

  uint8_t stack[POLICY_STACK_DOC + 1];
  uint8_t *cls = n <= POLICY_STACK_DOC ? stack : (uint8_t *)malloc(n + 1);
  if (!cls) return -1;
  cls[n] = POLICY_NONE;
  for (uint64_t i = n; i-- > 0;) cls[i] = policy_class_of(b, n, i, cls);

  *cls_o = policy_first_quote(b, n, cls, pos_o);
  if (cls != stack) free(cls);
  return 0;
}
