/* p6.c -- span-based DOM, cursor, and typed streaming over the parse tape.
   Scratch experiment; nothing here belongs to the repository.

   Pipeline under test (all end-to-end measurements include it):
     bytes --(AVX2 stage1 + UTF-8 + two-pass tape)--> tape --> consumer
   Consumers:
     cursor : one pass over tape + input; validates grammar; emits values
     dom    : flat span node array + arena + interned keys; then tree walk
     typed  : bytes -> typed values directly; no tape, no DOM
   Grammar validation (bracket type/depth matching, structure alternation,
   number and string well-formedness) is inside every consumer path.

   Build:
     clang -O3 -march=x86-64-v3 -mpclmul -std=gnu11 -c p5k.c -o p5k.o
     clang -O3 -march=x86-64-v3 -mpclmul -std=gnu11 p6.c p5k.o -lm -o p6
*/
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>
#include <malloc.h>

/* ------------------------------------------------------------------ kernels */
extern uint64_t k_tape_twopass(const uint8_t *buf, uint64_t nblocks,
                               uint64_t *tape, uint64_t *candbuf,
                               uint64_t *imbuf, uint64_t *uerr);
extern uint64_t k_stage1_utf8(const uint8_t *buf, uint64_t nblocks,
                              uint64_t *im_out, uint64_t *uerr);
extern uint64_t k_utf8(const uint8_t *buf, uint64_t n, uint64_t *uerr);

/* ------------------------------------------------------------------- error -- */
typedef struct {
    int ok;
    uint64_t off;
    const char *msg;
} Err;

static void err_set(Err *e, uint64_t off, const char *msg) {
    e->ok = 0;
    e->off = off;
    e->msg = msg;
}

/* --------------------------------------------------------------------- out -- */
#define PRIME 0x9E3779B97F4A7C15ULL

typedef struct {
    uint8_t *b;
    size_t len, cap;
    uint64_t h;
    int hash;                       /* 1: accumulate a checksum, do not store */
} Out;

static void out_init(Out *o, int hash) {
    memset(o, 0, sizeof *o);
    o->hash = hash;
}

static void out_free(Out *o) {
    free(o->b);
    o->b = NULL; o->cap = o->len = 0;
}

static void out_reserve(Out *o, size_t need) {
    if (o->len + need <= o->cap) return;
    size_t nc = o->cap ? o->cap : 256;
    while (nc < o->len + need) nc <<= 1;
    uint8_t *nb = (uint8_t *)realloc(o->b, nc);
    if (!nb) { fprintf(stderr, "oom\n"); exit(2); }
    o->b = nb; o->cap = nc;
}

static inline void hup(Out *o, const void *p, size_t n) {
    const uint8_t *q = (const uint8_t *)p;
    uint64_t h = o->h;
    size_t i = 0;
    while (i + 8 <= n) {
        uint64_t w;
        memcpy(&w, q + i, 8);
        h = (h ^ w) * PRIME;
        i += 8;
    }
    if (i < n) {
        uint64_t w = 0;
        for (size_t j = 0; j < n - i; j++) w |= (uint64_t)q[i + j] << (8 * j);
        h = (h ^ w) * PRIME;
    }
    o->h = (h + (uint64_t)n) * PRIME;
}

static inline void out_raw(Out *o, const void *p, size_t n) {
    if (o->hash) { hup(o, p, n); return; }
    out_reserve(o, n);
    memcpy(o->b + o->len, p, n);
    o->len += n;
}

static inline void out_tag(Out *o, uint8_t t) { out_raw(o, &t, 1); }

static inline void out_u32(Out *o, uint32_t v) {
    uint8_t b[4] = { (uint8_t)v, (uint8_t)(v >> 8), (uint8_t)(v >> 16), (uint8_t)(v >> 24) };
    out_raw(o, b, 4);
}

static inline void out_u64(Out *o, uint64_t v) {
    uint8_t b[8];
    for (int i = 0; i < 8; i++) b[i] = (uint8_t)(v >> (8 * i));
    out_raw(o, b, 8);
}

/* event tags */
enum {
    T_OBJ = 1, T_OBJ_END = 2, T_ARR = 3, T_ARR_END = 4,
    T_KEY = 5, T_STR = 6, T_NUM = 7, T_TRUE = 8, T_FALSE = 9, T_NULL = 10
};

static uint64_t dbits(double d) {
    uint64_t u;
    memcpy(&u, &d, 8);
    return u;
}

/* ------------------------------------------------------------------ lexing -- */
static inline int is_ws(uint8_t c) {
    return c == ' ' || c == '\n' || c == '\r' || c == '\t';
}

/* JSON scalar token delimiters: whitespace, structural characters, quote */
static inline int is_delim(uint8_t c) {
    return is_ws(c) || c == ',' || c == ':' || c == '{' || c == '}' ||
           c == '[' || c == ']' || c == '"';
}

static const int8_t UNESC[256] = {
    [0 ... 255] = -1,
    ['"'] = '"', ['\\'] = '\\', ['/'] = '/', ['b'] = 8,
    ['f'] = 12, ['n'] = 10, ['r'] = 13, ['t'] = 9
};

static inline int hv(uint8_t c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
}

static void put_utf8(Out *o, uint32_t cp) {
    uint8_t b[4];
    if (cp < 0x80) {
        b[0] = (uint8_t)cp;
        out_raw(o, b, 1);
    } else if (cp < 0x800) {
        b[0] = (uint8_t)(0xC0 | (cp >> 6));
        b[1] = (uint8_t)(0x80 | (cp & 0x3F));
        out_raw(o, b, 2);
    } else if (cp < 0x10000) {
        b[0] = (uint8_t)(0xE0 | (cp >> 12));
        b[1] = (uint8_t)(0x80 | ((cp >> 6) & 0x3F));
        b[2] = (uint8_t)(0x80 | (cp & 0x3F));
        out_raw(o, b, 3);
    } else {
        b[0] = (uint8_t)(0xF0 | (cp >> 18));
        b[1] = (uint8_t)(0x80 | ((cp >> 12) & 0x3F));
        b[2] = (uint8_t)(0x80 | ((cp >> 6) & 0x3F));
        b[3] = (uint8_t)(0x80 | (cp & 0x3F));
        out_raw(o, b, 4);
    }
}

/* Validate JSON string content p[0..n) (no surrounding quotes) and, when dst
   is non-NULL, append the decoded bytes.  Returns 1 on success; on failure
   returns 0 with *err = index inside p of the offending byte. */
static int str_process(const uint8_t *p, uint64_t n, Out *dst, int *has_esc,
                       size_t *err) {
    uint64_t i = 0;
    int esc_found = 0;
    while (i < n) {
        uint8_t c = p[i];
        if (c != '\\') {
            if (c < 0x20) { *err = (size_t)i; return 0; }
            uint64_t s = i;
            do { i++; } while (i < n && p[i] != '\\' && p[i] >= 0x20);
            if (dst) out_raw(dst, p + s, i - s);
            continue;
        }
        esc_found = 1;
        if (i + 1 >= n) { *err = (size_t)i; return 0; }
        uint8_t e = p[i + 1];
        int8_t uv = UNESC[e];
        if (uv >= 0) {
            if (dst) { uint8_t b = (uint8_t)uv; out_raw(dst, &b, 1); }
            i += 2;
            continue;
        }
        if (e != 'u') { *err = (size_t)i; return 0; }
        if (i + 6 > n) { *err = (size_t)i; return 0; }
        int h0 = hv(p[i + 2]), h1 = hv(p[i + 3]);
        int h2 = hv(p[i + 4]), h3 = hv(p[i + 5]);
        if (h0 < 0 || h1 < 0 || h2 < 0 || h3 < 0) { *err = (size_t)i; return 0; }
        uint32_t cp = ((uint32_t)h0 << 12) | ((uint32_t)h1 << 8) |
                      ((uint32_t)h2 << 4) | (uint32_t)h3;
        i += 6;
        if (cp >= 0xD800 && cp <= 0xDBFF && i + 6 <= n &&
            p[i] == '\\' && p[i + 1] == 'u') {
            int g0 = hv(p[i + 2]), g1 = hv(p[i + 3]);
            int g2 = hv(p[i + 4]), g3 = hv(p[i + 5]);
            if (g0 >= 0 && g1 >= 0 && g2 >= 0 && g3 >= 0) {
                uint32_t lo = ((uint32_t)g0 << 12) | ((uint32_t)g1 << 8) |
                              ((uint32_t)g2 << 4) | (uint32_t)g3;
                if (lo >= 0xDC00 && lo <= 0xDFFF) {
                    cp = 0x10000 + ((cp - 0xD800) << 10) + (lo - 0xDC00);
                    i += 6;
                }
            }
        }
        if (dst) put_utf8(dst, cp);
    }
    if (has_esc) *has_esc = esc_found;
    return 1;
}

static double to_double(const uint8_t *p, uint64_t n) {
    /* exact fast path for JSON integers of at most 15 digits */
    {
        uint64_t i = 0;
        int neg = 0, nd = 0;
        if (i < n && p[i] == '-') { neg = 1; i++; }
        uint64_t v = 0;
        while (i < n && p[i] >= '0' && p[i] <= '9') {
            if (++nd > 15) break;
            v = v * 10 + (uint64_t)(p[i] - '0');
            i++;
        }
        if (i == n && nd > 0 && nd <= 15)
            return neg ? -(double)v : (double)v;
    }
    char tmp[64];
    if (n < sizeof tmp) {
        memcpy(tmp, p, n);
        tmp[n] = 0;
        return strtod(tmp, NULL);
    }
    char *h = (char *)malloc(n + 1);
    if (!h) { fprintf(stderr, "oom\n"); exit(2); }
    memcpy(h, p, n);
    h[n] = 0;
    double d = strtod(h, NULL);
    free(h);
    return d;
}

/* RFC 8259 number grammar; *err = first offending index inside p. */
static int num_scan(const uint8_t *p, uint64_t n, double *out, size_t *err) {
    uint64_t i = 0;
    if (i < n && p[i] == '-') i++;
    if (i >= n) { *err = (size_t)i; return 0; }
    if (p[i] == '0') {
        i++;
    } else if (p[i] >= '1' && p[i] <= '9') {
        while (i < n && p[i] >= '0' && p[i] <= '9') i++;
    } else {
        *err = (size_t)i; return 0;
    }
    if (i < n && p[i] == '.') {
        i++;
        if (i >= n || p[i] < '0' || p[i] > '9') { *err = (size_t)i; return 0; }
        while (i < n && p[i] >= '0' && p[i] <= '9') i++;
    }
    if (i < n && (p[i] == 'e' || p[i] == 'E')) {
        i++;
        if (i < n && (p[i] == '+' || p[i] == '-')) i++;
        if (i >= n || p[i] < '0' || p[i] > '9') { *err = (size_t)i; return 0; }
        while (i < n && p[i] >= '0' && p[i] <= '9') i++;
    }
    if (i != n) { *err = (size_t)i; return 0; }
    if (out) *out = to_double(p, n);
    return 1;
}

static int lit_check(const uint8_t *p, uint64_t n, const char *lit, uint32_t ln,
                     size_t *err) {
    uint64_t m = n < ln ? n : ln;
    for (uint64_t i = 0; i < m; i++)
        if (p[i] != (uint8_t)lit[i]) { *err = (size_t)i; return 0; }
    if (n != ln) { *err = (size_t)m; return 0; }
    return 1;
}

/* ------------------------------------------------------------------ interning */
typedef struct {
    uint32_t off, len, hash, meta;      /* meta = (gen << 1) | in_arena */
} KEnt;

typedef struct {
    uint32_t *slot;                     /* entry id + 1 */
    uint32_t *sgen;                     /* generation of the slot */
    uint32_t cap, count, gen;
    KEnt *ent;
    uint32_t nent, ecap;
} Intern;

typedef struct Dom Dom;

struct Dom {
    const uint8_t *input;
    /* node array: flat, document order */
    struct Node *nodes;
    uint32_t node_cap, nnodes, root;
    uint32_t cnode[520], last_child[520];
    /* arena for materialised text (keys at build, escaped values on demand) */
    Out arena;
    size_t key_end;
    Intern in;
};

typedef struct Node {
    uint32_t off, len;
    uint32_t first_child, next_sibling;
    uint32_t key;                       /* intern entry id + 1, 0 = none */
    uint16_t kind;
    uint8_t flags;                      /* 1 = content has an escape */
    uint8_t pad;
} Node;

#define NONE 0xFFFFFFFFu

enum { N_OBJ = 1, N_ARR = 2, N_STR = 3, N_NUM = 4, N_TRUE = 5, N_FALSE = 6, N_NULL = 7 };

static inline uint32_t kent_hash(const uint8_t *p, uint32_t n) {
    uint32_t h = 2166136261u;
    for (uint32_t i = 0; i < n; i++) { h ^= p[i]; h *= 16777619u; }
    return h;
}

static void intern_reset(Intern *t) {
    t->count = 0;
    t->nent = 0;
    t->gen++;
    if (t->gen == 0) {                   /* wrap: clear slots, keep generation */
        if (t->cap) memset(t->sgen, 0, (size_t)t->cap * sizeof(uint32_t));
        t->gen = 1;
    }
}

static const uint8_t *kent_bytes(Dom *d, const KEnt *e) {
    return (e->meta & 1) ? d->arena.b + e->off : d->input + e->off;
}

static void intern_grow(Dom *d) {
    Intern *t = &d->in;
    uint32_t ncap = t->cap ? t->cap * 2 : 128;
    uint32_t *ns = (uint32_t *)calloc(ncap, sizeof(uint32_t));
    uint32_t *ng = (uint32_t *)calloc(ncap, sizeof(uint32_t));
    if (!ns || !ng) { fprintf(stderr, "oom\n"); exit(2); }
    for (uint32_t i = 0; i < t->nent; i++) {
        KEnt *e = &t->ent[i];
        if ((e->meta >> 1) != t->gen) continue;
        uint32_t s = e->hash & (ncap - 1);
        while (ng[s] == t->gen) s = (s + 1) & (ncap - 1);
        ns[s] = i + 1;
        ng[s] = t->gen;
    }
    free(t->slot); free(t->sgen);
    t->slot = ns; t->sgen = ng; t->cap = ncap;
}

/* returns entry id (0-based); p must be stable for the lifetime of the build */
static uint32_t intern_put(Dom *d, const uint8_t *p, uint32_t len, int in_arena) {
    Intern *t = &d->in;
    if (t->cap == 0 || (t->count + 1) * 4 >= t->cap * 3) intern_grow(d);
    uint32_t h = kent_hash(p, len);
    uint32_t s = h & (t->cap - 1);
    while (t->sgen[s] == t->gen) {
        uint32_t id = t->slot[s] - 1;
        KEnt *e = &t->ent[id];
        if (e->hash == h && e->len == len &&
            memcmp(kent_bytes(d, e), p, len) == 0) return id;
        s = (s + 1) & (t->cap - 1);
    }
    if (t->nent == t->ecap) {
        uint32_t nc = t->ecap ? t->ecap * 2 : 256;
        KEnt *ne = (KEnt *)realloc(t->ent, (size_t)nc * sizeof(KEnt));
        if (!ne) { fprintf(stderr, "oom\n"); exit(2); }
        t->ent = ne; t->ecap = nc;
    }
    uint32_t id = t->nent++;
    uint32_t off = in_arena ? (uint32_t)(p - d->arena.b) : (uint32_t)(p - d->input);
    t->ent[id].off = off;
    t->ent[id].len = len;
    t->ent[id].hash = h;
    t->ent[id].meta = ((uint32_t)t->gen << 1) | (uint32_t)(in_arena & 1);
    t->slot[s] = id + 1;
    t->sgen[s] = t->gen;
    t->count++;
    return id;
}

static void dom_reset(Dom *d) {
    d->nnodes = 0;
    d->root = NONE;
    d->arena.len = 0;
    d->key_end = 0;
    intern_reset(&d->in);
}

static void dom_init(Dom *d, const uint8_t *input) {
    memset(d, 0, sizeof *d);
    d->input = input;
    d->root = NONE;
    out_init(&d->arena, 0);
}

static void dom_free(Dom *d) {
    free(d->nodes);
    free(d->in.slot);
    free(d->in.sgen);
    free(d->in.ent);
    out_free(&d->arena);
    memset(d, 0, sizeof *d);
}

static uint32_t dom_add(Dom *d, uint32_t sp, uint8_t kind, uint32_t off, uint32_t len,
                        uint32_t key, uint8_t flags) {
    if (d->nnodes == d->node_cap) {
        uint32_t nc = d->node_cap ? d->node_cap + d->node_cap / 2 + 64 : 1024;
        Node *nn = (Node *)realloc(d->nodes, (size_t)nc * sizeof(Node));
        if (!nn) { fprintf(stderr, "oom\n"); exit(2); }
        d->nodes = nn; d->node_cap = nc;
    }
    uint32_t idx = d->nnodes++;
    Node *nd = &d->nodes[idx];
    nd->off = off; nd->len = len;
    nd->first_child = NONE; nd->next_sibling = NONE;
    nd->key = key; nd->kind = kind; nd->flags = flags; nd->pad = 0;
    if (sp == 0) {
        d->root = idx;
    } else {
        uint32_t pi = d->cnode[sp - 1];
        Node *pa = &d->nodes[pi];
        if (pa->first_child == NONE) pa->first_child = idx;
        else d->nodes[d->last_child[sp - 1]].next_sibling = idx;
        d->last_child[sp - 1] = idx;
    }
    return idx;
}

/* -------------------------------------------------------------- tape walker -- */
#define MAXD 520
enum { C_OBJ = 1, C_ARR = 2 };

static Out g_sbuf;                      /* reusable decoded-string scratch */

typedef struct {
    const uint8_t *b;
    uint64_t n;
    Out *o;                             /* NULL while building a DOM */
    Dom *d;                             /* NULL for the cursor */
    Err *e;
    uint8_t ctype[MAXD], cst[MAXD];
    uint32_t sp;
    int root_done;
    int64_t depth;
    uint32_t pending_key;
    int have_key;
} W;

static int w_fail(W *w, uint64_t off, const char *msg) {
    err_set(w->e, off, msg);
    return 0;
}

static int w_value_pos(W *w) {
    if (w->sp == 0) return !w->root_done;
    uint32_t t = w->sp - 1;
    if (w->ctype[t] == C_OBJ) return w->cst[t] == 2;
    return w->cst[t] == 0 || w->cst[t] == 2;
}

static void w_after_value(W *w) {
    if (w->sp == 0) { w->root_done = 1; return; }
    uint32_t t = w->sp - 1;
    w->cst[t] = (w->ctype[t] == C_OBJ) ? 3 : 1;
}

static int w_scalar(W *w, uint64_t s, uint64_t e) {
    if (!w_value_pos(w)) return w_fail(w, s, "scalar where no value is allowed");
    uint8_t c = w->b[s];
    uint32_t off = (uint32_t)s, len = (uint32_t)(e - s);
    uint32_t key = w->have_key ? w->pending_key : 0;
    if (c == '-' || (c >= '0' && c <= '9')) {
        double d = 0;
        size_t ei;
        /* the DOM only validates here; its walk decodes on access */
        int ok = w->d ? num_scan(w->b + s, len, NULL, &ei)
                      : num_scan(w->b + s, len, &d, &ei);
        if (!ok) return w_fail(w, s + ei, "number");
        if (w->d) dom_add(w->d, w->sp, N_NUM, off, len, key, 0);
        else { out_tag(w->o, T_NUM); out_u64(w->o, dbits(d)); }
    } else {
        const char *lit;
        uint32_t ln;
        uint8_t tag, nk;
        if (c == 't')      { lit = "true";  ln = 4; tag = T_TRUE;  nk = N_TRUE;  }
        else if (c == 'f') { lit = "false"; ln = 5; tag = T_FALSE; nk = N_FALSE; }
        else if (c == 'n') { lit = "null";  ln = 4; tag = T_NULL;  nk = N_NULL;  }
        else return w_fail(w, s, "scalar");
        size_t ei;
        if (!lit_check(w->b + s, len, lit, ln, &ei)) return w_fail(w, s + ei, "literal");
        if (w->d) dom_add(w->d, w->sp, nk, off, len, key, 0);
        else out_tag(w->o, tag);
    }
    w->have_key = 0;
    w_after_value(w);
    return 1;
}

static int w_string(W *w, uint64_t qpos, uint64_t cpos) {
    uint64_t start = qpos + 1;
    uint64_t len = cpos - start;
    int key = 0, val = w_value_pos(w);
    if (w->sp > 0 && w->ctype[w->sp - 1] == C_OBJ) {
        uint8_t st = w->cst[w->sp - 1];
        if (st == 0 || st == 4) key = 1;
    }
    if (!key && !val) return w_fail(w, qpos, "string where no value is allowed");
    int he = 0;
    size_t ei = 0;
    if (w->d) {
        if (key) {
            g_sbuf.len = 0;
            if (!str_process(w->b + start, len, &g_sbuf, &he, &ei))
                return w_fail(w, start + ei, "string");
            uint32_t id;
            if (he) {
                size_t aoff = w->d->arena.len;
                out_raw(&w->d->arena, g_sbuf.b, g_sbuf.len);
                id = intern_put(w->d, w->d->arena.b + aoff, (uint32_t)g_sbuf.len, 1);
            } else {
                id = intern_put(w->d, w->b + start, (uint32_t)len, 0);
            }
            w->pending_key = id + 1;
            w->have_key = 1;
            w->cst[w->sp - 1] = 1;
        } else {
            if (!str_process(w->b + start, len, NULL, &he, &ei))
                return w_fail(w, start + ei, "string");
            dom_add(w->d, w->sp, N_STR, (uint32_t)start, (uint32_t)len,
                    w->have_key ? w->pending_key : 0, (uint8_t)(he ? 1 : 0));
            w->have_key = 0;
            w_after_value(w);
        }
    } else {
        g_sbuf.len = 0;
        if (!str_process(w->b + start, len, &g_sbuf, &he, &ei))
            return w_fail(w, start + ei, "string");
        if (key) {
            out_tag(w->o, T_KEY);
            out_u32(w->o, (uint32_t)g_sbuf.len);
            out_raw(w->o, g_sbuf.b, g_sbuf.len);
            w->cst[w->sp - 1] = 1;
        } else {
            out_tag(w->o, T_STR);
            out_u32(w->o, (uint32_t)g_sbuf.len);
            out_raw(w->o, g_sbuf.b, g_sbuf.len);
            w_after_value(w);
        }
    }
    return 1;
}

static inline int32_t dep12(uint64_t w) {
    int32_t d = (int32_t)((w >> 36) & 0xFFFu);
    return d >= 2048 ? d - 4096 : d;
}

static int tape_walk(const uint8_t *b, uint64_t n, const uint64_t *tp, uint64_t nt,
                     Out *o, Dom *d, Err *e) {
    W w;
    memset(&w, 0, sizeof w);
    w.b = b; w.n = n; w.o = o; w.d = d; w.e = e;
    if (d) { dom_reset(d); d->input = b; }
    uint64_t ti = 0, cur = 0;
    while (ti < nt) {
        uint64_t word = tp[ti];
        uint32_t pos = (uint32_t)(word & 0xFFFFFFFFu);
        uint32_t kind = (uint32_t)((word >> 32) & 15u);
        if ((uint64_t)pos >= n) return w_fail(&w, n, "token out of range");

        /* scalar in the gap before this token */
        uint64_t s = cur;
        while (s < pos && is_ws(b[s])) s++;
        if (s < pos) {
            uint64_t ee = s;
            while (ee < pos && !is_ws(b[ee])) ee++;
            if (!w_scalar(&w, s, ee)) return 0;
            uint64_t s2 = ee;
            while (s2 < pos && is_ws(b[s2])) s2++;
            if (s2 < pos) return w_fail(&w, s2, "extra token");
        }

        /* depth/bracket-depth invariant carried in the tape word */
        int32_t td = dep12(word);
        if (kind >= 3 && kind <= 6) {
            int32_t want = (int32_t)w.depth + ((kind == 3 || kind == 5) ? 1 : -1);
            if (td != want) return w_fail(&w, pos, "depth");
            w.depth = td;
        } else if (td != (int32_t)w.depth) {
            return w_fail(&w, pos, "depth");
        }

        switch (kind) {
        case 1: {                        /* , */
            if (w.sp == 0) return w_fail(&w, pos, "comma");
            uint32_t t = w.sp - 1;
            if (w.ctype[t] == C_OBJ) {
                if (w.cst[t] != 3) return w_fail(&w, pos, "comma");
                w.cst[t] = 4;
            } else {
                if (w.cst[t] != 1) return w_fail(&w, pos, "comma");
                w.cst[t] = 2;
            }
            cur = pos + 1;
            ti++;
            break;
        }
        case 2: {                        /* : */
            if (w.sp == 0) return w_fail(&w, pos, "colon");
            uint32_t t = w.sp - 1;
            if (w.ctype[t] != C_OBJ || w.cst[t] != 1)
                return w_fail(&w, pos, "colon");
            w.cst[t] = 2;
            cur = pos + 1;
            ti++;
            break;
        }
        case 3: case 5: {                /* { [ */
            if (!w_value_pos(&w)) return w_fail(&w, pos, "container where no value is allowed");
            if (w.sp >= MAXD) return w_fail(&w, pos, "nesting limit");
            uint8_t ct = (kind == 3) ? C_OBJ : C_ARR;
            if (w.d) {
                uint32_t idx = dom_add(w.d, w.sp, (ct == C_OBJ) ? N_OBJ : N_ARR,
                                       pos, 0, w.have_key ? w.pending_key : 0, 0);
                w.d->cnode[w.sp] = idx;
                w.d->last_child[w.sp] = NONE;
            } else {
                out_tag(w.o, (ct == C_OBJ) ? T_OBJ : T_ARR);
            }
            w.have_key = 0;
            w.ctype[w.sp] = ct;
            w.cst[w.sp] = 0;
            w.sp++;
            cur = pos + 1;
            ti++;
            break;
        }
        case 4: case 6: {                /* } ] */
            if (w.sp == 0) return w_fail(&w, pos, "close");
            uint32_t t = w.sp - 1;
            uint8_t want = (kind == 4) ? C_OBJ : C_ARR;
            if (w.ctype[t] != want) return w_fail(&w, pos, "bracket type");
            uint8_t st = w.cst[t];
            int ok = (want == C_OBJ) ? (st == 3 || st == 0) : (st == 1 || st == 0);
            if (!ok) return w_fail(&w, pos, "trailing comma");
            w.sp--;
            if (!w.d) out_tag(w.o, (kind == 4) ? T_OBJ_END : T_ARR_END);
            w_after_value(&w);
            cur = pos + 1;
            ti++;
            break;
        }
        case 7: {                        /* opening quote */
            if (ti + 1 >= nt) return w_fail(&w, n, "unterminated");
            uint64_t w2 = tp[ti + 1];
            if ((uint32_t)((w2 >> 32) & 15u) != 8) return w_fail(&w, n, "unterminated");
            uint64_t cp = (uint32_t)(w2 & 0xFFFFFFFFu);
            if (cp <= pos) return w_fail(&w, pos, "quote order");
            if (dep12(w2) != (int32_t)w.depth) return w_fail(&w, cp, "depth");
            if (!w_string(&w, pos, cp)) return 0;
            cur = cp + 1;
            ti += 2;
            break;
        }
        default:
            return w_fail(&w, pos, "kind");
        }
    }
    {
        uint64_t s = cur;
        while (s < n && is_ws(b[s])) s++;
        if (s < n) return w_fail(&w, s, "trailing bytes");
    }
    if (w.sp != 0) return w_fail(&w, n, "unclosed container");
    if (!w.root_done) return w_fail(&w, n, "no value");
    if (w.depth != 0) return w_fail(&w, n, "depth");
    e->ok = 1;
    e->off = 0;
    e->msg = "ok";
    return 1;
}

/* --------------------------------------------------------------- DOM walk --- */
static int dom_emit(Dom *d, uint32_t idx, int depth, Out *o, Err *e) {
    if (idx >= d->nnodes) { err_set(e, 0, "node index"); return 0; }
    if (depth > 2048) { err_set(e, 0, "dom depth"); return 0; }
    Node *nd = &d->nodes[idx];

    if (nd->key) {
        KEnt *ke = &d->in.ent[nd->key - 1];
        const uint8_t *kp = (ke->meta & 1) ? d->arena.b + ke->off : d->input + ke->off;
        out_tag(o, T_KEY);
        out_u32(o, ke->len);
        out_raw(o, kp, ke->len);
    }
    switch (nd->kind) {
    case N_OBJ:
    case N_ARR: {
        out_tag(o, (nd->kind == N_OBJ) ? T_OBJ : T_ARR);
        for (uint32_t c = nd->first_child; c != NONE; c = d->nodes[c].next_sibling)
            if (!dom_emit(d, c, depth + 1, o, e)) return 0;
        out_tag(o, (nd->kind == N_OBJ) ? T_OBJ_END : T_ARR_END);
        return 1;
    }
    case N_STR: {
        if (nd->flags & 1) {
            size_t aoff = d->arena.len;
            int he = 0;
            size_t ei = 0;
            if (!str_process(d->input + nd->off, nd->len, &d->arena, &he, &ei)) {
                err_set(e, nd->off + ei, "string");
                return 0;
            }
            out_tag(o, T_STR);
            out_u32(o, (uint32_t)(d->arena.len - aoff));
            out_raw(o, d->arena.b + aoff, d->arena.len - aoff);
        } else {
            out_tag(o, T_STR);
            out_u32(o, nd->len);
            out_raw(o, d->input + nd->off, nd->len);
        }
        return 1;
    }
    case N_NUM: {
        double v = to_double(d->input + nd->off, nd->len);
        out_tag(o, T_NUM);
        out_u64(o, dbits(v));
        return 1;
    }
    case N_TRUE:  out_tag(o, T_TRUE);  return 1;
    case N_FALSE: out_tag(o, T_FALSE); return 1;
    case N_NULL:  out_tag(o, T_NULL);  return 1;
    default:
        err_set(e, 0, "node kind");
        return 0;
    }
}

static int dom_walk(Dom *d, Out *o, Err *e) {
    d->arena.len = d->key_end;
    if (d->root == NONE) { err_set(e, 0, "empty dom"); return 0; }
    if (!dom_emit(d, d->root, 0, o, e)) return 0;
    e->ok = 1;
    e->off = 0;
    e->msg = "ok";
    return 1;
}

/* ------------------------------------------------------------ direct parser -- */
typedef struct {
    const uint8_t *b;
    uint64_t n, i;
    Out *o;
    Err *e;
} P;

static int p_fail(P *p, uint64_t off, const char *msg) {
    err_set(p->e, off, msg);
    return 0;
}

static void p_ws(P *p) {
    while (p->i < p->n && is_ws(p->b[p->i])) p->i++;
}

static uint64_t tok_end(const uint8_t *b, uint64_t n, uint64_t i) {
    while (i < n && !is_delim(b[i])) i++;
    return i;
}

/* at '"' */
static int p_string(P *p, int is_key) {
    uint64_t start = p->i + 1;
    uint64_t q = start;
    while (q < p->n) {
        uint8_t c = p->b[q];
        if (c == '"') break;
        if (c == '\\') {
            if (q + 1 < p->n) q += 2;
            else { q = p->n; break; }
        } else {
            q++;
        }
    }
    if (q >= p->n) return p_fail(p, p->n, "unterminated");
    size_t ei = 0;
    g_sbuf.len = 0;
    if (!str_process(p->b + start, q - start, &g_sbuf, NULL, &ei))
        return p_fail(p, start + ei, "string");
    if (is_key) {
        out_tag(p->o, T_KEY);
        out_u32(p->o, (uint32_t)g_sbuf.len);
        out_raw(p->o, g_sbuf.b, g_sbuf.len);
    } else {
        out_tag(p->o, T_STR);
        out_u32(p->o, (uint32_t)g_sbuf.len);
        out_raw(p->o, g_sbuf.b, g_sbuf.len);
    }
    p->i = q + 1;
    return 1;
}

static int p_value(P *p, int depth) {
    if (depth > 2048) return p_fail(p, p->i, "nesting limit");
    p_ws(p);
    if (p->i >= p->n) return p_fail(p, p->n, "unexpected end");
    uint8_t c = p->b[p->i];
    if (c == '{') {
        out_tag(p->o, T_OBJ);
        p->i++;
        p_ws(p);
        if (p->i < p->n && p->b[p->i] == '}') {
            p->i++;
            out_tag(p->o, T_OBJ_END);
            return 1;
        }
        for (;;) {
            p_ws(p);
            if (p->i >= p->n || p->b[p->i] != '"') return p_fail(p, p->i, "key");
            if (!p_string(p, 1)) return 0;
            p_ws(p);
            if (p->i >= p->n || p->b[p->i] != ':') return p_fail(p, p->i, "colon");
            p->i++;
            if (!p_value(p, depth + 1)) return 0;
            p_ws(p);
            if (p->i < p->n && p->b[p->i] == ',') { p->i++; continue; }
            if (p->i < p->n && p->b[p->i] == '}') {
                p->i++;
                out_tag(p->o, T_OBJ_END);
                return 1;
            }
            return p_fail(p, p->i, "object end");
        }
    }
    if (c == '[') {
        out_tag(p->o, T_ARR);
        p->i++;
        p_ws(p);
        if (p->i < p->n && p->b[p->i] == ']') {
            p->i++;
            out_tag(p->o, T_ARR_END);
            return 1;
        }
        for (;;) {
            if (!p_value(p, depth + 1)) return 0;
            p_ws(p);
            if (p->i < p->n && p->b[p->i] == ',') { p->i++; continue; }
            if (p->i < p->n && p->b[p->i] == ']') {
                p->i++;
                out_tag(p->o, T_ARR_END);
                return 1;
            }
            return p_fail(p, p->i, "array end");
        }
    }
    if (c == '"') return p_string(p, 0);

    uint64_t e = tok_end(p->b, p->n, p->i);
    uint64_t len = e - p->i;
    if (c == '-' || (c >= '0' && c <= '9')) {
        double d;
        size_t ei;
        if (!num_scan(p->b + p->i, len, &d, &ei)) return p_fail(p, p->i + ei, "number");
        out_tag(p->o, T_NUM);
        out_u64(p->o, dbits(d));
    } else {
        const char *lit;
        uint32_t ln;
        uint8_t tag;
        if (c == 't')      { lit = "true";  ln = 4; tag = T_TRUE;  }
        else if (c == 'f') { lit = "false"; ln = 5; tag = T_FALSE; }
        else if (c == 'n') { lit = "null";  ln = 4; tag = T_NULL;  }
        else return p_fail(p, p->i, "value");
        size_t ei;
        if (!lit_check(p->b + p->i, len, lit, ln, &ei))
            return p_fail(p, p->i + ei, "literal");
        out_tag(p->o, tag);
    }
    p->i = e;
    return 1;
}

static int utf8_scalar_first(const uint8_t *p, uint64_t n, uint64_t *errpos) {
    uint64_t i = 0;
    while (i < n) {
        uint8_t c = p[i];
        if (c < 0x80) { i++; continue; }
        if (c < 0xC2) goto bad;
        if (c < 0xE0) {
            if (i + 1 >= n || (p[i + 1] & 0xC0) != 0x80) goto bad;
            i += 2; continue;
        }
        if (c < 0xF0) {
            if (i + 2 >= n) goto bad;
            uint8_t c1 = p[i + 1], c2 = p[i + 2];
            if ((c1 & 0xC0) != 0x80 || (c2 & 0xC0) != 0x80) goto bad;
            if (c == 0xE0 && c1 < 0xA0) goto bad;
            if (c == 0xED && c1 > 0x9F) goto bad;
            i += 3; continue;
        }
        if (c < 0xF5) {
            if (i + 3 >= n) goto bad;
            uint8_t c1 = p[i + 1], c2 = p[i + 2], c3 = p[i + 3];
            if ((c1 & 0xC0) != 0x80 || (c2 & 0xC0) != 0x80 ||
                (c3 & 0xC0) != 0x80) goto bad;
            if (c == 0xF0 && c1 < 0x90) goto bad;
            if (c == 0xF4 && c1 > 0x8F) goto bad;
            i += 4; continue;
        }
    bad:
        if (errpos) *errpos = i;
        return -1;
    }
    return 0;
}

static int direct_parse(const uint8_t *b, uint64_t n, Out *o, Err *e) {
    uint64_t uerr = 0;
    k_utf8(b, n, &uerr);
    if (uerr) {
        uint64_t ep = 0;
        utf8_scalar_first(b, n, &ep);
        err_set(e, ep, "utf8");
        return 0;
    }
    P p;
    memset(&p, 0, sizeof p);
    p.b = b; p.n = n; p.o = o; p.e = e;
    if (!p_value(&p, 0)) return 0;
    p_ws(&p);
    if (p.i != n) return p_fail(&p, p.i, "trailing bytes");
    e->ok = 1;
    e->off = 0;
    e->msg = "ok";
    return 1;
}

/* -------------------------------------------------------- typed fixed schema -- */
/* wl_dense: [[int,...],...] */
static int typed_dense(const uint8_t *b, uint64_t n, Out *o, Err *e) {
    uint64_t uerr = 0;
    k_utf8(b, n, &uerr);
    if (uerr) {
        uint64_t ep = 0;
        utf8_scalar_first(b, n, &ep);
        err_set(e, ep, "utf8");
        return 0;
    }
    uint64_t i = 0;
    while (i < n && is_ws(b[i])) i++;
    if (i >= n || b[i] != '[') { err_set(e, i, "outer array"); return 0; }
    i++;
    out_tag(o, T_ARR);
    while (i < n && is_ws(b[i])) i++;
    if (i < n && b[i] == ']') {
        i++;
        out_tag(o, T_ARR_END);
        goto tail;
    }
    for (;;) {
        while (i < n && is_ws(b[i])) i++;
        if (i >= n || b[i] != '[') { err_set(e, i, "row"); return 0; }
        i++;
        out_tag(o, T_ARR);
        while (i < n && is_ws(b[i])) i++;
        if (i < n && b[i] == ']') {
            i++;
            out_tag(o, T_ARR_END);
        } else {
            for (;;) {
                while (i < n && is_ws(b[i])) i++;
                uint64_t s = i;
                int neg = 0;
                if (i < n && b[i] == '-') { neg = 1; i++; }
                if (i >= n || b[i] < '0' || b[i] > '9') { err_set(e, i, "int"); return 0; }
                uint64_t v = 0;
                if (b[i] == '0') {
                    i++;
                    if (i < n && b[i] >= '0' && b[i] <= '9') { err_set(e, i, "leading zero"); return 0; }
                } else {
                    while (i < n && b[i] >= '0' && b[i] <= '9') {
                        v = v * 10 + (uint64_t)(b[i] - '0');
                        i++;
                    }
                }
                if (i == s || (neg && i == s + 1)) { err_set(e, i, "int"); return 0; }
                double d = neg ? -(double)v : (double)v;
                out_tag(o, T_NUM);
                out_u64(o, dbits(d));
                while (i < n && is_ws(b[i])) i++;
                if (i < n && b[i] == ',') { i++; continue; }
                if (i < n && b[i] == ']') { i++; out_tag(o, T_ARR_END); break; }
                err_set(e, i, "row end");
                return 0;
            }
        }
        while (i < n && is_ws(b[i])) i++;
        if (i < n && b[i] == ',') { i++; continue; }
        if (i < n && b[i] == ']') { i++; break; }
        err_set(e, i, "outer end");
        return 0;
    }
    out_tag(o, T_ARR_END);
tail:
    while (i < n && is_ws(b[i])) i++;
    if (i != n) { err_set(e, i, "trailing"); return 0; }
    e->ok = 1; e->off = 0; e->msg = "ok";
    return 1;
}

/* wl_longstr: [{"k":"...","n":int},...] */
static int typed_longstr(const uint8_t *b, uint64_t n, Out *o, Err *e) {
    uint64_t uerr = 0;
    k_utf8(b, n, &uerr);
    if (uerr) {
        uint64_t ep = 0;
        utf8_scalar_first(b, n, &ep);
        err_set(e, ep, "utf8");
        return 0;
    }
    uint64_t i = 0;
    while (i < n && is_ws(b[i])) i++;
    if (i >= n || b[i] != '[') { err_set(e, i, "outer array"); return 0; }
    i++;
    out_tag(o, T_ARR);
    while (i < n && is_ws(b[i])) i++;
    if (i < n && b[i] == ']') { i++; out_tag(o, T_ARR_END); goto tail; }
    for (;;) {
        while (i < n && is_ws(b[i])) i++;
        if (i >= n || b[i] != '{') { err_set(e, i, "object"); return 0; }
        i++;
        out_tag(o, T_OBJ);
        while (i < n && is_ws(b[i])) i++;
        if (i + 2 >= n || b[i] != '"' || b[i + 1] != 'k' || b[i + 2] != '"') {
            err_set(e, i, "key k"); return 0;
        }
        i += 3;
        out_tag(o, T_KEY);
        out_u32(o, 1);
        out_raw(o, "k", 1);
        while (i < n && is_ws(b[i])) i++;
        if (i >= n || b[i] != ':') { err_set(e, i, "colon"); return 0; }
        i++;
        while (i < n && is_ws(b[i])) i++;
        if (i >= n || b[i] != '"') { err_set(e, i, "string"); return 0; }
        uint64_t start = i + 1, q = start;
        while (q < n) {
            uint8_t c = b[q];
            if (c == '"') break;
            if (c == '\\') { if (q + 1 < n) q += 2; else { q = n; break; } }
            else q++;
        }
        if (q >= n) { err_set(e, n, "unterminated"); return 0; }
        size_t ei = 0;
        g_sbuf.len = 0;
        if (!str_process(b + start, q - start, &g_sbuf, NULL, &ei)) {
            err_set(e, start + ei, "string");
            return 0;
        }
        out_tag(o, T_STR);
        out_u32(o, (uint32_t)g_sbuf.len);
        out_raw(o, g_sbuf.b, g_sbuf.len);
        i = q + 1;
        while (i < n && is_ws(b[i])) i++;
        if (i >= n || b[i] != ',') { err_set(e, i, "comma"); return 0; }
        i++;
        while (i < n && is_ws(b[i])) i++;
        if (i + 2 >= n || b[i] != '"' || b[i + 1] != 'n' || b[i + 2] != '"') {
            err_set(e, i, "key n"); return 0;
        }
        i += 3;
        out_tag(o, T_KEY);
        out_u32(o, 1);
        out_raw(o, "n", 1);
        while (i < n && is_ws(b[i])) i++;
        if (i >= n || b[i] != ':') { err_set(e, i, "colon"); return 0; }
        i++;
        while (i < n && is_ws(b[i])) i++;
        int neg = 0;
        if (i < n && b[i] == '-') { neg = 1; i++; }
        if (i >= n || b[i] < '0' || b[i] > '9') { err_set(e, i, "int"); return 0; }
        uint64_t v = 0;
        if (b[i] == '0') { i++; }
        else while (i < n && b[i] >= '0' && b[i] <= '9') {
            v = v * 10 + (uint64_t)(b[i] - '0');
            i++;
        }
        out_tag(o, T_NUM);
        out_u64(o, dbits(neg ? -(double)v : (double)v));
        while (i < n && is_ws(b[i])) i++;
        if (i >= n || b[i] != '}') { err_set(e, i, "object end"); return 0; }
        i++;
        out_tag(o, T_OBJ_END);
        while (i < n && is_ws(b[i])) i++;
        if (i < n && b[i] == ',') { i++; continue; }
        if (i < n && b[i] == ']') { i++; break; }
        err_set(e, i, "outer end");
        return 0;
    }
    out_tag(o, T_ARR_END);
tail:
    while (i < n && is_ws(b[i])) i++;
    if (i != n) { err_set(e, i, "trailing"); return 0; }
    e->ok = 1; e->off = 0; e->msg = "ok";
    return 1;
}

/* ------------------------------------------------------------------ utilities */
static void *xalloc(size_t n) {
    void *p = aligned_alloc(64, (n + 63) & ~(size_t)63);
    if (!p) { fprintf(stderr, "oom %zu\n", n); exit(2); }
    memset(p, 0, (n + 63) & ~(size_t)63);
    return p;
}

static uint8_t *load_padded(const char *path, uint64_t *nbytes) {
    FILE *f = fopen(path, "rb");
    if (!f) { perror(path); exit(2); }
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    fseek(f, 0, SEEK_SET);
    uint8_t *base = (uint8_t *)xalloc((size_t)sz + 192);
    if (fread(base + 64, 1, (size_t)sz, f) != (size_t)sz) {
        fprintf(stderr, "read %s\n", path);
        exit(2);
    }
    fclose(f);
    *nbytes = (uint64_t)sz;
    return base + 64;
}

static double now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec * 1e9 + (double)ts.tv_nsec;
}

static int dcmp(const void *a, const void *b) {
    double x = *(const double *)a, y = *(const double *)b;
    return (x > y) - (x < y);
}

static int fails = 0;
#define CHECK(cond, ...)                                                       \
    do {                                                                       \
        if (!(cond)) { printf("FAIL  "); printf(__VA_ARGS__); printf("\n"); fails++; } \
    } while (0)

static int ev_equal(const Out *a, const Out *b) {
    if (a->len != b->len) return 0;
    if (a->len == 0) return 1;
    return memcmp(a->b, b->b, a->len) == 0;
}

/* --------------------------------------------------------- scalar tape check */
static int scalar_tape_check(const uint8_t *b, uint64_t n, const uint64_t *tp,
                             uint64_t nt, uint64_t *mismatch) {
    uint64_t k = 0;
    int instr = 0;
    int bs_run = 0;                     /* backslash-run parity, global */
    int64_t depth = 0;
    for (uint64_t i = 0; i < n; i++) {
        uint8_t c = b[i];
        if (c == '\\') { bs_run ^= 1; continue; }
        int escaped = bs_run;
        bs_run = 0;
        if (c == '"') {
            if (escaped) continue;      /* the tape masks escaped quotes */
            uint64_t w;
            if (instr) {
                instr = 0;
                w = i | (8ULL << 32) | ((uint64_t)(depth & 0xFFF) << 36);
            } else {
                instr = 1;
                w = i | (7ULL << 32) | ((uint64_t)(depth & 0xFFF) << 36);
            }
            if (k >= nt || tp[k] != w) { *mismatch = k; return 0; }
            k++;
            continue;
        }
        if (instr) continue;
        uint32_t kind = (c == ',') ? 1u : (c == ':') ? 2u : (c == '{') ? 3u :
                        (c == '}') ? 4u : (c == '[') ? 5u : (c == ']') ? 6u : 0u;
        if (!kind) continue;
        depth += (c == '{' || c == '[') ? 1 : (c == '}' || c == ']') ? -1 : 0;
        uint64_t w = i | ((uint64_t)kind << 32) | ((uint64_t)(depth & 0xFFF) << 36);
        if (k >= nt || tp[k] != w) { *mismatch = k; return 0; }
        k++;
    }
    if (k != nt) { *mismatch = k; return 0; }
    return 1;
}

/* ------------------------------------------------------------------- context */
typedef struct {
    uint8_t *base;                      /* padded allocation base */
    uint8_t *b;
    uint64_t nbytes, nb;
    uint64_t *tape, *cand, *imb;
    uint64_t nt, uerr;
    Dom dom;
    Out ev;
} Ctx;

static void ctx_init(Ctx *x) {
    memset(x, 0, sizeof *x);
    out_init(&x->ev, 1);
}

static void ctx_load(Ctx *x, const char *path) {
    x->b = load_padded(path, &x->nbytes);
    x->base = x->b - 64;
    x->nb = x->nbytes / 64;
    uint64_t words = x->nbytes + 64;
    x->tape = (uint64_t *)xalloc(words * 8);
    x->cand = (uint64_t *)xalloc(x->nb * 8 + 64);
    x->imb = (uint64_t *)xalloc(x->nb * 8 + 64);
    dom_init(&x->dom, x->b);
}

static void ctx_free(Ctx *x) {
    dom_free(&x->dom);
    free(x->tape); free(x->cand); free(x->imb);
    free(x->base);
    out_free(&x->ev);
}

static uint64_t build_tape(Ctx *x) {
    x->uerr = 0;
    x->nt = k_tape_twopass(x->b, x->nb, x->tape, x->cand, x->imb, &x->uerr);
    return x->nt;
}

/* --------------------------------------------------------------- correctness */
typedef struct {
    const char *name;
    int valid;                          /* expected verdict */
} Wl;

static void gate_file(const char *dir, const char *name) {
    char path[512];
    snprintf(path, sizeof path, "%s/%s", dir, name);
    uint64_t nbytes;
    uint8_t *b = load_padded(path, &nbytes);
    uint64_t nb = nbytes / 64;

    Out ref; out_init(&ref, 0);
    Err eref;
    int okref = direct_parse(b, nbytes, &ref, &eref);

    uint64_t *tape = (uint64_t *)xalloc((nbytes + 64) * 8);
    uint64_t *cand = (uint64_t *)xalloc(nb * 8 + 64);
    uint64_t *imb = (uint64_t *)xalloc(nb * 8 + 64);
    uint64_t uerr = 0;
    uint64_t nt = k_tape_twopass(b, nb, tape, cand, imb, &uerr);

    uint64_t mism = 0;
    int tape_ok = scalar_tape_check(b, nbytes, tape, nt, &mism);

    uint64_t utf8_off = 0;
    int utf8_bad = utf8_scalar_first(b, nbytes, &utf8_off) != 0;

    /* cursor */
    Out ec; out_init(&ec, 0);
    Err ec_err;
    int cok;
    if (uerr) {
        cok = 0;
        err_set(&ec_err, utf8_off, "utf8");
    } else {
        cok = tape_walk(b, nbytes, tape, nt, &ec, NULL, &ec_err);
    }

    /* DOM */
    Dom dom;
    dom_init(&dom, b);
    Out ed; out_init(&ed, 0);
    Err ed_err;
    int dok;
    if (uerr) {
        dok = 0;
        err_set(&ed_err, utf8_off, "utf8");
    } else {
        dok = tape_walk(b, nbytes, tape, nt, NULL, &dom, &ed_err);
        if (dok) {
            dom.key_end = dom.arena.len;
            dok = dom_walk(&dom, &ed, &ed_err);
        }
    }
    uint32_t nnodes = dom.nnodes;

    /* typed (generic direct decode, no tape, no DOM) */
    Out et; out_init(&et, 0);
    Err et_err;
    int tok = direct_parse(b, nbytes, &et, &et_err);

    int all_ok = 1;
    CHECK(tape_ok, "%s: tape differs from scalar reference at word %llu",
          name, (unsigned long long)mism);
    if (!tape_ok) all_ok = 0;

    if (okref) {
        CHECK(cok, "%s: cursor rejected valid input (%s at %llu)", name,
              ec_err.msg, (unsigned long long)ec_err.off);
        CHECK(dok, "%s: dom rejected valid input (%s at %llu)", name,
              ed_err.msg, (unsigned long long)ed_err.off);
        CHECK(tok, "%s: typed rejected valid input (%s at %llu)", name,
              et_err.msg, (unsigned long long)et_err.off);
        CHECK(ev_equal(&ref, &ec), "%s: cursor values differ (%zu vs %zu bytes)",
              name, ref.len, ec.len);
        CHECK(ev_equal(&ref, &ed), "%s: dom values differ (%zu vs %zu bytes)",
              name, ref.len, ed.len);
        CHECK(ev_equal(&ref, &et), "%s: typed values differ (%zu vs %zu bytes)",
              name, ref.len, et.len);
        if (!(cok && dok && tok && ev_equal(&ref, &ec) && ev_equal(&ref, &ed) &&
              ev_equal(&ref, &et))) all_ok = 0;
        printf("OK   %-26s valid    tokens=%llu nodes=%u events=%zu bytes\n",
               name, (unsigned long long)nt, nnodes, ref.len);
    } else {
        CHECK(!cok, "%s: cursor accepted invalid input", name);
        CHECK(!dok, "%s: dom accepted invalid input", name);
        CHECK(!tok, "%s: typed accepted invalid input", name);
        CHECK(!ec_err.ok && !ed_err.ok && !et_err.ok, "%s: error flag", name);
        CHECK(ec_err.off == eref.off, "%s: cursor error off %llu != ref %llu (%s)",
              name, (unsigned long long)ec_err.off,
              (unsigned long long)eref.off, eref.msg);
        CHECK(ed_err.off == eref.off, "%s: dom error off %llu != ref %llu (%s)",
              name, (unsigned long long)ed_err.off,
              (unsigned long long)eref.off, ed_err.msg);
        CHECK(et_err.off == eref.off, "%s: typed error off %llu != ref %llu (%s)",
              name, (unsigned long long)et_err.off,
              (unsigned long long)eref.off, et_err.msg);
        if (!(!cok && !dok && !tok && ec_err.off == eref.off &&
              ed_err.off == eref.off && et_err.off == eref.off)) all_ok = 0;
        printf("OK   %-26s reject   at byte %llu (%s)%s tokens=%llu\n",
               name, (unsigned long long)eref.off, eref.msg,
               utf8_bad ? " [invalid UTF-8]" : "",
               (unsigned long long)nt);
    }
    (void)all_ok;

    out_free(&ref); out_free(&ec); out_free(&ed); out_free(&et);
    dom_free(&dom);
    free(tape); free(cand); free(imb);
    free(b - 64);
}

/* typed fixed-schema verification on the two homogeneous workloads */
static void gate_fixed(const char *dir, const char *name, int which) {
    char path[512];
    snprintf(path, sizeof path, "%s/%s", dir, name);
    uint64_t nbytes;
    uint8_t *b = load_padded(path, &nbytes);
    Out ref; out_init(&ref, 0);
    Err e1;
    CHECK(direct_parse(b, nbytes, &ref, &e1), "%s: reference failed", name);
    Out fx; out_init(&fx, 0);
    Err e2;
    int ok = which == 0 ? typed_dense(b, nbytes, &fx, &e2)
                        : typed_longstr(b, nbytes, &fx, &e2);
    CHECK(ok, "%s: typed fixed schema failed (%s at %llu)", name, e2.msg,
          (unsigned long long)e2.off);
    if (!ev_equal(&ref, &fx)) {
        size_t m = ref.len < fx.len ? ref.len : fx.len;
        size_t d = 0;
        while (d < m && ref.b[d] == fx.b[d]) d++;
        printf("DIFF %s at %zu/%zu vs %zu bytes; ref:", name, d, ref.len, fx.len);
        for (size_t z = d; z < d + 12 && z < ref.len; z++) printf(" %02x", ref.b[z]);
        printf(" | fixed:");
        for (size_t z = d; z < d + 12 && z < fx.len; z++) printf(" %02x", fx.b[z]);
        printf("\n");
    }
    CHECK(ev_equal(&ref, &fx), "%s: typed fixed schema values differ", name);
    printf("OK   %-26s typed-fixed %s\n", name,
           which == 0 ? "[[int]]" : "[{k:string,n:int}]");
    out_free(&ref); out_free(&fx);
    free(b - 64);
}

static int gate(const char *dir) {
    printf("== correctness gate: values first, rates only after ==\n");
    /* the tape builder is the baseline every tape consumer sees */
    static const char *valid[] = {
        "workload.json", "wl1m.json", "wl_dense.json",
        "wl_longstr.json", "wl10m.json"
    };
    for (unsigned i = 0; i < sizeof valid / sizeof *valid; i++) gate_file(dir, valid[i]);
    gate_file(dir, "wl_escstress.json");
    gate_file(dir, "wl_malformed_utf8.json");
    gate_file(dir, "wl_bad_bracket.json");
    gate_file(dir, "wl_bad_number.json");
    gate_file(dir, "wl_bad_comma.json");
    gate_fixed(dir, "wl_dense.json", 0);
    gate_fixed(dir, "wl_longstr.json", 1);
    printf("gate: %d failure(s)\n", fails);
    return fails ? 3 : 0;
}

/* ------------------------------------------------------------------ benchmark */
static volatile uint64_t sink;

typedef struct {
    const char *name;
    uint64_t (*fn)(Ctx *);
    double bytes;
    uint64_t nb;
    int invalid;
} Bench;

static double run_once(Bench *b, Ctx *x, int iters) {
    double t0 = now_ns();
    uint64_t acc = 0;
    for (int i = 0; i < iters; i++) acc ^= b->fn(x);
    double t1 = now_ns();
    sink ^= acc;
    return (t1 - t0) / (double)iters;
}

static void bench_row(Bench *b, Ctx *x, int iters, int runs) {
    double v[64];
    if (runs > 64) runs = 64;
    run_once(b, x, 1);
    for (int r = 0; r < runs; r++) v[r] = run_once(b, x, iters);
    qsort(v, (size_t)runs, sizeof(double), dcmp);
    double med = v[runs / 2], mn = v[0], mx = v[runs - 1];
    double mean = 0;
    for (int r = 0; r < runs; r++) mean += v[r];
    mean /= runs;
    double var = 0;
    for (int r = 0; r < runs; r++) var += (v[r] - mean) * (v[r] - mean);
    var /= runs;
    double cv = mean > 0 ? 100.0 * sqrt(var) / mean : 0;
    double nsblk = med / (double)b->nb;
    if (b->invalid)
        printf("%-34s med=%9.1f ns  that is the reject path, not a parse rate  cv=%5.2f%%\n",
               b->name, med, cv);
    else
        printf("%-34s med=%7.3f GB/s  %7.2f ns/blk  min=%7.3f max=%7.3f cv=%5.2f%%\n",
               b->name, b->bytes / med, nsblk, b->bytes / mx, b->bytes / mn, cv);
}

static uint64_t f_tape(Ctx *x) { return build_tape(x); }

static uint64_t f_cursor_walk(Ctx *x) {
    Out *o = &x->ev;
    o->len = 0; o->h = 0;
    if (x->uerr) return 0;
    Err e;
    if (!tape_walk(x->b, x->nbytes, x->tape, x->nt, o, NULL, &e)) return e.off;
    return o->h;
}

static uint64_t f_cursor_e2e(Ctx *x) {
    build_tape(x);
    return f_cursor_walk(x);
}

static uint64_t f_dom_build(Ctx *x) {
    Err e;
    if (x->uerr) return 0;
    if (!tape_walk(x->b, x->nbytes, x->tape, x->nt, NULL, &x->dom, &e))
        return e.off;
    x->dom.key_end = x->dom.arena.len;
    return x->dom.nnodes;
}

static uint64_t f_dom_walk(Ctx *x) {
    Out *o = &x->ev;
    o->len = 0; o->h = 0;
    Err e;
    if (!dom_walk(&x->dom, o, &e)) return e.off;
    return o->h;
}

static uint64_t f_dom_e2e(Ctx *x) {
    build_tape(x);
    if (!f_dom_build(x)) return 0;
    return f_dom_walk(x);
}

static uint32_t *g_perm;
static uint32_t g_perm_n;

static uint64_t f_dom_probe(Ctx *x) {
    uint64_t acc = 0;
    Node *nd = x->dom.nodes;
    for (uint32_t k = 0; k < g_perm_n; k++) {
        uint32_t i = g_perm[k];
        acc += nd[i].kind + nd[i].off + nd[i].len + nd[i].key + nd[i].flags;
    }
    return acc;
}

static uint64_t f_typed(Ctx *x) {
    Out *o = &x->ev;
    o->len = 0; o->h = 0;
    Err e;
    if (!direct_parse(x->b, x->nbytes, o, &e)) return e.off;
    return o->h;
}

static uint64_t f_typed_dense(Ctx *x) {
    Out *o = &x->ev;
    o->len = 0; o->h = 0;
    Err e;
    if (!typed_dense(x->b, x->nbytes, o, &e)) return e.off;
    return o->h;
}

static uint64_t f_typed_longstr(Ctx *x) {
    Out *o = &x->ev;
    o->len = 0; o->h = 0;
    Err e;
    if (!typed_longstr(x->b, x->nbytes, o, &e)) return e.off;
    return o->h;
}

static void bench_workload(const char *dir, const char *name, int fixed_dense,
                           int fixed_longstr, int invalid) {
    char path[512];
    snprintf(path, sizeof path, "%s/%s", dir, name);
    Ctx x;
    ctx_init(&x);
    ctx_load(&x, path);
    printf("\n-- %s: %llu bytes, %llu blocks --\n", name,
           (unsigned long long)x.nbytes, (unsigned long long)x.nb);

    int iters = x.nbytes > 6000000 ? 5 : 10;
    int runs = 7;

    /* setup: build the tape and DOM once for the standalone rows */
    build_tape(&x);
    dom_reset(&x.dom);
    Err e;
    int built = 0;
    if (!x.uerr && !invalid)
        built = tape_walk(x.b, x.nbytes, x.tape, x.nt, NULL, &x.dom, &e);
    if (built) x.dom.key_end = x.dom.arena.len;

    if (built) {
        g_perm_n = x.dom.nnodes;
        g_perm = (uint32_t *)malloc((size_t)g_perm_n * 4);
        for (uint32_t i = 0; i < g_perm_n; i++) g_perm[i] = i;
        uint64_t s = 0x123456789ABCDEFULL;
        for (uint32_t i = g_perm_n; i-- > 1;) {
            s ^= s << 13; s ^= s >> 7; s ^= s << 17;
            uint32_t j = (uint32_t)(s % (i + 1));
            uint32_t tmp = g_perm[i]; g_perm[i] = g_perm[j]; g_perm[j] = tmp;
        }
    }

    Bench rows[10];
    int n = 0;
    rows[n++] = (Bench){"tape only", f_tape, (double)x.nbytes, x.nb, 0};
    rows[n++] = (Bench){"cursor walk (tape prebuilt)", f_cursor_walk, (double)x.nbytes, x.nb, invalid};
    rows[n++] = (Bench){"cursor end-to-end", f_cursor_e2e, (double)x.nbytes, x.nb, invalid};
    if (built) {
        rows[n++] = (Bench){"dom build (tape prebuilt)", f_dom_build, (double)x.nbytes, x.nb, 0};
        rows[n++] = (Bench){"dom walk (dom prebuilt)", f_dom_walk, (double)x.nbytes, x.nb, 0};
        rows[n++] = (Bench){"dom end-to-end", f_dom_e2e, (double)x.nbytes, x.nb, 0};
        rows[n++] = (Bench){"dom random probe", f_dom_probe, (double)x.nbytes, x.nb, 0};
    }
    rows[n++] = (Bench){"typed direct (no tape/dom)", f_typed, (double)x.nbytes, x.nb, invalid};
    if (fixed_dense)
        rows[n++] = (Bench){"typed fixed schema [[int]]", f_typed_dense, (double)x.nbytes, x.nb, 0};
    if (fixed_longstr)
        rows[n++] = (Bench){"typed fixed [{k,n}]", f_typed_longstr, (double)x.nbytes, x.nb, 0};

    for (int i = 0; i < n; i++) bench_row(&rows[i], &x, iters, runs);

    free(g_perm); g_perm = NULL; g_perm_n = 0;
    ctx_free(&x);
}

static int bench(const char *dir) {
    if (fails) { printf("refusing to measure: correctness gate failed\n"); return 3; }
    bench_workload(dir, "workload.json", 0, 0, 0);
    bench_workload(dir, "wl1m.json", 0, 0, 0);
    bench_workload(dir, "wl_dense.json", 1, 0, 0);
    bench_workload(dir, "wl_longstr.json", 0, 1, 0);
    bench_workload(dir, "wl10m.json", 0, 0, 0);
    bench_workload(dir, "wl_escstress.json", 0, 0, 1);
    return 0;
}

/* -------------------------------------------------------------------- memory */
static void vm_stats(uint64_t *hwm_kb, uint64_t *rss_kb) {
    FILE *f = fopen("/proc/self/status", "r");
    uint64_t h = 0, r = 0;
    char line[256];
    if (f) {
        while (fgets(line, sizeof line, f)) {
            if (sscanf(line, "VmHWM: %llu kB", (unsigned long long *)&h) == 1) continue;
            if (sscanf(line, "VmRSS: %llu kB", (unsigned long long *)&r) == 1) continue;
        }
        fclose(f);
    }
    *hwm_kb = h; *rss_kb = r;
}

static int mem_one(const char *dir, const char *name) {
    char path[512];
    snprintf(path, sizeof path, "%s/%s", dir, name);
    uint64_t nbytes;
    uint8_t *b = load_padded(path, &nbytes);
    uint64_t nb = nbytes / 64;

    uint64_t uerr = 0;
    uint64_t nt = k_stage1_utf8(b, nb, NULL, &uerr);

    uint64_t *tape = (uint64_t *)xalloc(nt * 8 + 64);
    uint64_t *cand = (uint64_t *)xalloc(nb * 8 + 64);
    uint64_t *imb = (uint64_t *)xalloc(nb * 8 + 64);
    uint64_t nt2 = k_tape_twopass(b, nb, tape, cand, imb, &uerr);
    if (nt2 != nt) { printf("FAIL token count %llu != %llu\n",
                            (unsigned long long)nt, (unsigned long long)nt2); fails++; }

    Dom dom;
    dom_init(&dom, b);
    Out ev; out_init(&ev, 1);
    Err e;
    int built = 0;
    if (!uerr) built = tape_walk(b, nbytes, tape, nt, NULL, &dom, &e);
    size_t key_bytes = 0, val_bytes = 0;
    if (built) {
        dom.key_end = dom.arena.len;
        key_bytes = dom.key_end;
        dom.arena.len = dom.key_end;
        size_t before = dom.arena.len;
        Out *o = &ev; o->len = 0; o->h = 0;
        if (!dom_walk(&dom, o, &e)) built = 0;
        val_bytes = dom.arena.len - before;
    }
    uint64_t hwm, rss;
    vm_stats(&hwm, &rss);
    printf("MEM %-24s in=%llu tape=%llu tok (%llu) %.2fx  nodes=%u used=%u cap=%u "
           "%.2fB/node arena: key=%zu val=%zu cap=%zu  intern: ent=%u ecap=%u "
           "slots=%u  rss=%llu kB hwm=%llu kB%s\n",
           name,
           (unsigned long long)nbytes,
           (unsigned long long)(nt * 8), (unsigned long long)nt,
           (double)(nt * 8) / (double)nbytes,
           dom.nnodes, dom.nnodes, dom.node_cap,
           dom.nnodes ? (double)(dom.node_cap * sizeof(Node)) / (double)dom.nnodes : 0.0,
           key_bytes, val_bytes, dom.arena.cap,
           dom.in.nent, dom.in.ecap, dom.in.cap,
           (unsigned long long)rss, (unsigned long long)hwm,
           uerr ? " [rejected: invalid UTF-8]" : (built ? "" : " [rejected]"));

    free(tape); free(cand); free(imb);
    out_free(&ev);
    dom_free(&dom);
    free(b - 64);
    return 0;
}

static int mem_consumer(const char *dir, const char *name, int typed) {
    char path[512];
    snprintf(path, sizeof path, "%s/%s", dir, name);
    uint64_t nbytes;
    uint8_t *b = load_padded(path, &nbytes);
    uint64_t nb = nbytes / 64;
    Out ev; out_init(&ev, 1);
    Err e;
    int ok = 0;
    if (typed) {
        ok = direct_parse(b, nbytes, &ev, &e);
    } else {
        uint64_t uerr = 0;
        uint64_t nt = k_stage1_utf8(b, nb, NULL, &uerr);
        uint64_t *tape = (uint64_t *)xalloc(nt * 8 + 64);
        uint64_t *cand = (uint64_t *)xalloc(nb * 8 + 64);
        uint64_t *imb = (uint64_t *)xalloc(nb * 8 + 64);
        uint64_t nt2 = k_tape_twopass(b, nb, tape, cand, imb, &uerr);
        if (!uerr && nt2 == nt) ok = tape_walk(b, nbytes, tape, nt, &ev, NULL, &e);
        uint64_t hwm, rss;
        vm_stats(&hwm, &rss);
        printf("MEMC %-22s %-8s in=%llu tape=%llu scratch_max=%zu rss=%llu kB hwm=%llu kB\n",
               name, "cursor", (unsigned long long)nbytes,
               (unsigned long long)(nt * 8), g_sbuf.cap,
               (unsigned long long)rss, (unsigned long long)hwm);
        free(tape); free(cand); free(imb);
        out_free(&ev);
        free(b - 64);
        return ok ? 0 : 1;
    }
    uint64_t hwm, rss;
    vm_stats(&hwm, &rss);
    printf("MEMC %-22s %-8s in=%llu scratch_max=%zu rss=%llu kB hwm=%llu kB\n",
           name, "typed", (unsigned long long)nbytes, g_sbuf.cap,
           (unsigned long long)rss, (unsigned long long)hwm);
    out_free(&ev);
    free(b - 64);
    return ok ? 0 : 1;
}

static int mem_mode(const char *dir, const char *name) {
    return mem_one(dir, name);
}

/* dump the reference event stream for an independent cross-check */
static int dump_mode(const char *dir, const char *name, const char *out) {
    char path[512];
    snprintf(path, sizeof path, "%s/%s", dir, name);
    uint64_t nbytes;
    uint8_t *b = load_padded(path, &nbytes);
    Out ev; out_init(&ev, 0);
    Err e;
    int ok = direct_parse(b, nbytes, &ev, &e);
    FILE *f = fopen(out, "wb");
    if (!f) { perror(out); return 2; }
    if (ev.len) fwrite(ev.b, 1, ev.len, f);
    fclose(f);
    printf("DUMP %-22s ok=%d events=%zu %s@%llu -> %s\n",
           name, ok, ev.len, e.msg, (unsigned long long)e.off, out);
    out_free(&ev);
    free(b - 64);
    return ok ? 0 : 1;
}

/* ---------------------------------------------------------------------- main */
int main(int argc, char **argv) {
    const char *dir = argc > 1 ? argv[1] : ".";
    const char *mode = argc > 2 ? argv[2] : "all";
    out_init(&g_sbuf, 0);

    if (!strcmp(mode, "gate")) {
        int rc = gate(dir);
        out_free(&g_sbuf);
        return rc;
    }
    if (!strcmp(mode, "bench")) {
        if (gate(dir)) { out_free(&g_sbuf); return 3; }
        int rc = bench(dir);
        out_free(&g_sbuf);
        return rc;
    }
    if (!strcmp(mode, "mem")) {
        int rc = mem_mode(dir, argc > 3 ? argv[3] : "workload.json");
        out_free(&g_sbuf);
        return rc;
    }
    if (!strcmp(mode, "dump")) {
        int rc = dump_mode(dir, argc > 3 ? argv[3] : "workload.json",
                           argc > 4 ? argv[4] : "/tmp/scidonia-spike2/p5/events.bin");
        out_free(&g_sbuf);
        return rc;
    }
    if (!strcmp(mode, "memcursor") || !strcmp(mode, "memtyped")) {
        int rc = mem_consumer(dir, argc > 3 ? argv[3] : "workload.json",
                              !strcmp(mode, "memtyped"));
        out_free(&g_sbuf);
        return rc;
    }
    if (gate(dir)) { out_free(&g_sbuf); return 3; }
    bench(dir);
    out_free(&g_sbuf);
    return 0;
}
