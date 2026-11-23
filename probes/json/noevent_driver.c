/*
 * Differential driver for the no-event entries.
 *
 *   noevent_driver [--arm list|nolist] [--route stage2|pipeline] <document>...
 *
 * `--route stage2` (the default) compares at the stage-2 boundary: the two
 * actors are the stage-2 entry `kernel/json/stage2.h` publishes and the
 * additive entry `kernel/json/stage2_noevent.h` publishes, both called here on
 * the same stage-1 output.  The reference is the certified entry followed by
 * the unchanged consumer fold
 * (`probes/json/route/cost-profile/cost-profile.c`'s `fold_result`), the fold
 * the model's `consumer` states and the route's rows carry; the subject is the
 * no-event entry's own `(tokens, values, sum)`.
 *
 * Stage 1 there is `leanllvm_json_pipeline`, called only for its entry stream
 * and escape list; its arena and event stream are discarded.  The reference
 * side then calls the certified stage-2 entry directly, so the comparison is
 * at the stage-2 boundary and not at the pipeline's.  `--arm list` builds the
 * stage-1 escape list and passes it to both sides; `--arm nolist` passes
 * `nxp = 0` to both sides and refuses a document containing a backslash,
 * because a body with no list entry is the plain span form and the pair would
 * otherwise be compared outside the certified route's domain.
 *
 * `--route pipeline` compares the two assembled pipelines end to end:
 * `leanllvm_json_pipeline` (plus the fold) against
 * `leanllvm_json_pipeline_noevent`.  Each side runs its own stage 1, so the
 * comparison covers the entry stream's cursor `nk` and the escape list's count
 * `nxp` as well as the verdict, the refusal offset and the reading.  On a
 * refusal the three reading slots must hold zero under both refusal classes --
 * the UTF-8 stage's document-level refusal and the walk's -- because the
 * pipeline entry zeroes them at entry and only an acceptance overwrites them.
 * `--arm nolist` clears the pipeline's escape-list bit on both sides.
 *
 * Every buffer is the caller's and every one is sized by the ABI's `pre`; the
 * document is staged at offset 3 of its buffer, so no pointer's alignment is
 * assumed.  `scratch` is `n + 64` bytes, the bound a body's `len + US_SLACK`
 * reaches at most.  The three reading slots are pre-filled with `0xDEADBEEF`
 * so a refusal that left them untouched is distinguishable from one that wrote
 * the declared zeros.
 *
 * One row per document.  At the stage-2 boundary:
 *
 *   <path>\t<accept|refuse>\t<verdict>\t<err>\t<tokens>\t<values>\t<sum>
 *
 * and at the pipeline boundary the two stage-1 outputs are appended:
 *
 *   ...\t<sum>\t<nk>\t<nxp>
 *
 * `verdict` is `1` or `0`; `err` is the refusal offset and `-` on acceptance;
 * the three reading words are printed on acceptance and `-` on refusal.  The
 * row is what the two sides agree on; a disagreement is printed as `FAIL` with
 * both readings and exits 3, so a row is never emitted for a failing document.
 *
 * Exit status: 0 every document agrees, 3 a differential failure, 2 a setup
 * fault (an unreadable document, a backslash in the no-list arm, or a consumer
 * fold that did not walk the event stream).
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* The three ABIs, declared rather than included, so a changed header cannot
   make the driver agree with itself. */
extern uint64_t leanllvm_json_pipeline(const uint8_t *b, uint64_t n,
                                       uint64_t *sc, uint64_t *mk,
                                       uint64_t *entw, uint32_t *ep,
                                       uint64_t epcap, uint64_t *nk,
                                       uint32_t *xp, uint64_t xpcap,
                                       uint64_t *nxp, uint64_t *xcarry,
                                       uint8_t *dst, uint64_t dstcap,
                                       uint64_t *ndst, uint8_t *ev,
                                       uint64_t evcap, uint64_t *nev,
                                       uint64_t *err, uint64_t arm);
extern uint64_t leanllvm_json_stage2(const uint8_t *b, uint64_t n,
                                     const uint32_t *ep, uint64_t nep,
                                     const uint32_t *xp, uint64_t nxp,
                                     uint8_t *dst, uint64_t dstcap,
                                     uint64_t *ndst, uint8_t *ev,
                                     uint64_t evcap, uint64_t *nev,
                                     uint64_t *err);
extern uint64_t leanllvm_json_stage2_noevent(const uint8_t *b, uint64_t n,
                                             const uint32_t *ep, uint64_t nep,
                                             const uint32_t *xp, uint64_t nxp,
                                             uint8_t *scratch,
                                             uint64_t scratchcap,
                                             uint64_t *tokens,
                                             uint64_t *values, uint64_t *sum,
                                             uint64_t *err);
extern uint64_t leanllvm_json_pipeline_noevent(
    const uint8_t *b, uint64_t n, uint64_t *sc, uint64_t *mk, uint64_t *entw,
    uint32_t *ep, uint64_t epcap, uint64_t *nk, uint32_t *xp, uint64_t xpcap,
    uint64_t *nxp, uint64_t *xcarry, uint8_t *scratch, uint64_t scratchcap,
    uint64_t *tokens, uint64_t *values, uint64_t *sum, uint64_t *err,
    uint64_t arm);

#define SENT 0xDEADBEEFDEADBEEFULL
#define US_SLACK 64

static void die(int code, const char *msg) {
  fprintf(stderr, "noevent_driver: %s\n", msg);
  exit(code);
}

static void *xcalloc(size_t n, size_t sz) {
  void *p = calloc(n ? n : 1, sz ? sz : 1);
  if (!p) die(2, "out of memory");
  return p;
}

/* ------------------------------------------------------- the consumer fold -- */
struct folded {
  uint64_t tokens, events, sum, values;
  int walked;
};

static uint64_t load64(const uint8_t *p) {
  uint64_t v;
  memcpy(&v, p, 8);
  return v;
}

static uint64_t event_width(uint8_t tag) {
  if (tag == 5 || tag == 6) return 13;
  if (tag == 7) return 9;
  return 1;
}

/* `cost-profile.c`'s `fold_result`, build mode: the arena's byte sum plus each
   event's tag, length and payload words. */
static struct folded fold(const uint8_t *arena, uint64_t ndst,
                          const uint8_t *ev, uint64_t nev) {
  struct folded c;
  uint64_t sum = 0, k = 0, tokens = 0;
  memset(&c, 0, sizeof c);
  for (uint64_t i = 0; i < ndst; i++) sum += arena[i];
  while (k < nev) {
    uint8_t tag = ev[k];
    uint64_t width = event_width(tag);
    if (k + width > nev) break;
    uint64_t len = 0, payload = 0;
    if (width == 13) {
      len = (uint64_t)ev[k + 1] | ((uint64_t)ev[k + 2] << 8) |
            ((uint64_t)ev[k + 3] << 16) | ((uint64_t)ev[k + 4] << 24);
      payload = load64(ev + k + 5);
    } else if (width == 9) {
      payload = load64(ev + k + 1);
    }
    sum += (uint64_t)tag + len + payload;
    k += width;
    tokens++;
  }
  c.tokens = tokens;
  c.events = k;
  c.sum = sum;
  c.walked = (k == nev);
  c.values = c.walked ? tokens : 0;
  return c;
}

/* ------------------------------------------------------------- documents -- */
struct document {
  uint8_t *win;
  const uint8_t *doc;
  uint64_t n;
};

/* Read the document at offset 3 of its buffer, so no pointer's alignment is
   assumed, and refuse a backslash in the no-list arm. */
static int load_document(const char *path, int list_arm, struct document *d) {
  FILE *f = fopen(path, "rb");
  if (!f) {
    fprintf(stderr, "noevent_driver: cannot read %s\n", path);
    return 2;
  }
  if (fseek(f, 0, SEEK_END) != 0) die(2, "seek failed");
  long sz = ftell(f);
  if (sz < 0) die(2, "size failed");
  if (fseek(f, 0, SEEK_SET) != 0) die(2, "seek failed");
  d->n = (uint64_t)sz;
  d->win = (uint8_t *)xcalloc((size_t)d->n + 3 + US_SLACK, 1);
  if (d->n && fread(d->win + 3, 1, (size_t)d->n, f) != (size_t)d->n) {
    fprintf(stderr, "noevent_driver: short read on %s\n", path);
    fclose(f);
    free(d->win);
    return 2;
  }
  fclose(f);
  d->doc = d->win + 3;
  if (!list_arm && memchr(d->doc, '\\', (size_t)d->n)) {
    fprintf(stderr,
                 "noevent_driver: %s carries a backslash; the no-list arm is "
                 "for escape-free documents\n",
                 path);
    free(d->win);
    return 2;
  }
  return 0;
}

/* --------------------------------------------------------------- one row -- */
static int run_document_stage2(const char *path, int list_arm) {
  struct document d;
  if (load_document(path, list_arm, &d)) return 2;
  uint8_t *win = d.win;
  const uint8_t *doc = d.doc;
  uint64_t n = d.n;

  uint64_t epcap = 64 * ((n + 63) >> 6) + 9;
  uint64_t xpcap = 64 * ((n + 63) >> 6) + 8;
  uint64_t dstcap = n + US_SLACK;
  uint64_t evcap = 13 * n + 128;
  uint32_t *ep = (uint32_t *)xcalloc((size_t)epcap, 4);
  uint32_t *xp = (uint32_t *)xcalloc((size_t)xpcap, 4);
  uint8_t *dst = (uint8_t *)xcalloc((size_t)dstcap, 1);
  uint8_t *ev = (uint8_t *)xcalloc((size_t)evcap, 1);
  uint8_t *scratch = (uint8_t *)xcalloc((size_t)n + US_SLACK, 1);
  uint64_t *sc = (uint64_t *)xcalloc(3, 8);
  uint64_t *mk = (uint64_t *)xcalloc(6, 8);
  uint64_t *entw = (uint64_t *)xcalloc(1, 8);
  uint64_t *xcarry = (uint64_t *)xcalloc(2, 8);

  /* Stage 1: the entry stream, and the escape list when the arm selects it.
     Bit 0 set selects B8, which has no table obligation. */
  uint64_t nk = 0, nxp = 0, err = 0;
  uint64_t sink_dst = 0, sink_nev = 0;
  uint64_t arm = 1 | (list_arm ? 2 : 0);
  (void)leanllvm_json_pipeline(doc, n, sc, mk, entw, ep, epcap, &nk, xp, xpcap,
                               &nxp, xcarry, dst, dstcap, &sink_dst, ev, evcap,
                               &sink_nev, &err, arm);

  const uint32_t *xpp = list_arm ? xp : NULL;
  uint64_t nxpp = list_arm ? nxp : 0;

  /* The reference: the certified stage-2 entry, then the unchanged fold. */
  uint64_t ndst = 0, nev = 0, ref_err = 0;
  uint64_t ref_verdict = leanllvm_json_stage2(
      doc, n, ep, nk, xpp, nxpp, dst, dstcap, &ndst, ev, evcap, &nev, &ref_err);

  struct folded ref;
  memset(&ref, 0, sizeof ref);
  if (ref_verdict) {
    ref = fold(dst, ndst, ev, nev);
    if (!ref.walked) {
      fprintf(stderr,
                   "noevent_driver: %s: the consumer did not walk the event "
                   "stream\n",
                   path);
      return 2;
    }
  }

  /* The subject: the no-event entry, with a sentinel in each reading slot. */
  uint64_t t = SENT, v = SENT, s = SENT, nev_err = 0;
  uint64_t nev_verdict = leanllvm_json_stage2_noevent(
      doc, n, ep, nk, xpp, nxpp, scratch, n + US_SLACK, &t, &v, &s, &nev_err);

  int bad = 0;
  if (nev_verdict != ref_verdict) {
    fprintf(stderr,
                 "FAIL %s verdict: reference %llu, no-event %llu\n", path,
                 (unsigned long long)ref_verdict,
                 (unsigned long long)nev_verdict);
    bad = 1;
  } else if (!ref_verdict) {
    if (nev_err != ref_err) {
      fprintf(stderr,
                   "FAIL %s refusal offset: reference %llu, no-event %llu\n",
                   path, (unsigned long long)ref_err,
                   (unsigned long long)nev_err);
      bad = 1;
    }
    if (t != 0 || v != 0 || s != 0) {
      fprintf(stderr,
                   "FAIL %s refusal slots: expected zero, got %llu/%llu/%llu\n",
                   path, (unsigned long long)t, (unsigned long long)v,
                   (unsigned long long)s);
      bad = 1;
    }
  } else {
    if (t != ref.tokens || v != ref.values || s != ref.sum) {
      fprintf(stderr,
                   "FAIL %s reading: reference %llu/%llu/%llu, no-event "
                   "%llu/%llu/%llu\n",
                   path, (unsigned long long)ref.tokens,
                   (unsigned long long)ref.values, (unsigned long long)ref.sum,
                   (unsigned long long)t, (unsigned long long)v,
                   (unsigned long long)s);
      bad = 1;
    }
  }

  if (!bad) {
    if (ref_verdict)
      printf("%s\taccept\t1\t-\t%llu\t%llu\t%llu\n", path,
                  (unsigned long long)ref.tokens,
                  (unsigned long long)ref.values,
                  (unsigned long long)ref.sum);
    else
      printf("%s\trefuse\t0\t%llu\t-\t-\t-\n", path,
                  (unsigned long long)ref_err);
  }

  free(win);
  free(ep);
  free(xp);
  free(dst);
  free(ev);
  free(scratch);
  free(sc);
  free(mk);
  free(entw);
  free(xcarry);
  return bad ? 3 : 0;
}

/* ---------------------------------------------------------- the pipeline -- */
static int run_document_pipeline(const char *path, int list_arm) {
  struct document d;
  if (load_document(path, list_arm, &d)) return 2;
  const uint8_t *doc = d.doc;
  uint64_t n = d.n;

  uint64_t epcap = 64 * ((n + 63) >> 6) + 9;
  uint64_t xpcap = 64 * ((n + 63) >> 6) + 8;
  uint64_t dstcap = n + US_SLACK;
  uint64_t evcap = 13 * n + 128;

  /* The reference pipeline's buffers. */
  uint32_t *ep = (uint32_t *)xcalloc((size_t)epcap, 4);
  uint32_t *xp = (uint32_t *)xcalloc((size_t)xpcap, 4);
  uint8_t *dst = (uint8_t *)xcalloc((size_t)dstcap, 1);
  uint8_t *ev = (uint8_t *)xcalloc((size_t)evcap, 1);
  uint64_t *sc = (uint64_t *)xcalloc(3, 8);
  uint64_t *mk = (uint64_t *)xcalloc(6, 8);
  uint64_t *entw = (uint64_t *)xcalloc(1, 8);
  uint64_t *xcarry = (uint64_t *)xcalloc(2, 8);

  /* The subject runs its own stage 1, so it has its own staging. */
  uint32_t *ep2 = (uint32_t *)xcalloc((size_t)epcap, 4);
  uint32_t *xp2 = (uint32_t *)xcalloc((size_t)xpcap, 4);
  uint8_t *scratch = (uint8_t *)xcalloc((size_t)n + US_SLACK, 1);
  uint64_t *sc2 = (uint64_t *)xcalloc(3, 8);
  uint64_t *mk2 = (uint64_t *)xcalloc(6, 8);
  uint64_t *entw2 = (uint64_t *)xcalloc(1, 8);
  uint64_t *xcarry2 = (uint64_t *)xcalloc(2, 8);

  /* Bit 0 set selects B8, which has no table obligation; bit 1 is the
     escape-list gate. */
  uint64_t arm = 1 | (list_arm ? 2 : 0);

  /* The reference: the certified pipeline, then the unchanged fold. */
  uint64_t ref_nk = 0, ref_nxp = 0, ref_err = 0, ndst = 0, nev = 0;
  uint64_t ref_verdict = leanllvm_json_pipeline(
      doc, n, sc, mk, entw, ep, epcap, &ref_nk, xp, xpcap, &ref_nxp, xcarry,
      dst, dstcap, &ndst, ev, evcap, &nev, &ref_err, arm);

  struct folded ref;
  memset(&ref, 0, sizeof ref);
  if (ref_verdict) {
    ref = fold(dst, ndst, ev, nev);
    if (!ref.walked) {
      fprintf(stderr,
                   "noevent_driver: %s: the consumer did not walk the event "
                   "stream\n",
                   path);
      return 2;
    }
  }

  /* The subject: the same stage 1 and the no-event tail, sentinel slots. */
  uint64_t t = SENT, v = SENT, s = SENT, sub_err = 0;
  uint64_t sub_nk = 0, sub_nxp = 0;
  uint64_t sub_verdict = leanllvm_json_pipeline_noevent(
      doc, n, sc2, mk2, entw2, ep2, epcap, &sub_nk, xp2, xpcap, &sub_nxp,
      xcarry2, scratch, n + US_SLACK, &t, &v, &s, &sub_err, arm);

  int bad = 0;
  if (sub_verdict != ref_verdict) {
    fprintf(stderr, "FAIL %s verdict: pipeline %llu, no-event %llu\n", path,
                 (unsigned long long)ref_verdict,
                 (unsigned long long)sub_verdict);
    bad = 1;
  }
  if (sub_nk != ref_nk) {
    fprintf(stderr, "FAIL %s nk: pipeline %llu, no-event %llu\n", path,
                 (unsigned long long)ref_nk, (unsigned long long)sub_nk);
    bad = 1;
  }
  if (sub_nxp != ref_nxp) {
    fprintf(stderr, "FAIL %s nxp: pipeline %llu, no-event %llu\n", path,
                 (unsigned long long)ref_nxp, (unsigned long long)sub_nxp);
    bad = 1;
  }
  if (!bad) {
    if (!ref_verdict) {
      if (sub_err != ref_err) {
        fprintf(stderr,
                     "FAIL %s refusal offset: pipeline %llu, no-event %llu\n",
                     path, (unsigned long long)ref_err,
                     (unsigned long long)sub_err);
        bad = 1;
      }
      if (t != 0 || v != 0 || s != 0) {
        fprintf(stderr,
                     "FAIL %s refusal slots: expected zero, got %llu/%llu/%llu\n",
                     path, (unsigned long long)t, (unsigned long long)v,
                     (unsigned long long)s);
        bad = 1;
      }
    } else if (t != ref.tokens || v != ref.values || s != ref.sum) {
      fprintf(stderr,
                   "FAIL %s reading: pipeline %llu/%llu/%llu, no-event "
                   "%llu/%llu/%llu\n",
                   path, (unsigned long long)ref.tokens,
                   (unsigned long long)ref.values, (unsigned long long)ref.sum,
                   (unsigned long long)t, (unsigned long long)v,
                   (unsigned long long)s);
      bad = 1;
    }
  }

  if (!bad) {
    if (ref_verdict)
      printf("%s\taccept\t1\t-\t%llu\t%llu\t%llu\t%llu\t%llu\n", path,
                  (unsigned long long)ref.tokens,
                  (unsigned long long)ref.values,
                  (unsigned long long)ref.sum,
                  (unsigned long long)ref_nk,
                  (unsigned long long)ref_nxp);
    else
      printf("%s\trefuse\t0\t%llu\t-\t-\t-\t%llu\t%llu\n", path,
                  (unsigned long long)ref_err,
                  (unsigned long long)ref_nk,
                  (unsigned long long)ref_nxp);
  }

  free(d.win);
  free(ep);
  free(xp);
  free(dst);
  free(ev);
  free(ep2);
  free(xp2);
  free(scratch);
  free(sc);
  free(mk);
  free(entw);
  free(xcarry);
  free(sc2);
  free(mk2);
  free(entw2);
  free(xcarry2);
  return bad ? 3 : 0;
}

int main(int argc, char **argv) {
  int list_arm = 1;
  int pipeline_route = 0;
  int i = 1;
  for (; i < argc; i++) {
    if (!strcmp(argv[i], "--arm")) {
      if (i + 1 >= argc) die(2, "--arm needs list or nolist");
      if (!strcmp(argv[i + 1], "list")) list_arm = 1;
      else if (!strcmp(argv[i + 1], "nolist")) list_arm = 0;
      else die(2, "--arm takes list or nolist");
      i++;
    } else if (!strcmp(argv[i], "--route")) {
      if (i + 1 >= argc) die(2, "--route needs stage2 or pipeline");
      if (!strcmp(argv[i + 1], "stage2")) pipeline_route = 0;
      else if (!strcmp(argv[i + 1], "pipeline")) pipeline_route = 1;
      else die(2, "--route takes stage2 or pipeline");
      i++;
    } else if (argv[i][0] == '-' && argv[i][1] == '-') {
      die(2, "unknown option");
    } else {
      break;
    }
  }
  if (i >= argc)
    die(2, "usage: noevent_driver [--arm list|nolist] "
           "[--route stage2|pipeline] <document>...");

  int status = 0;
  for (; i < argc; i++) {
    int r = pipeline_route ? run_document_pipeline(argv[i], list_arm)
                           : run_document_stage2(argv[i], list_arm);
    if (r == 2) return 2;       /* a setup fault stops the run */
    if (r == 3) status = 3;     /* a differential failure is reported per doc */
  }
  return status;
}
