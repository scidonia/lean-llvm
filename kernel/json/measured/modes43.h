/* modes43.h -- runtime selection of the escape-step shapes, for the one
   binary that compares them (SP43 env).  Scratch.

   Tokens (comma or + separated):
     esc=o   the shipped escape step (us_esc; simple inline, \u inline)
     esc=t   table-driven class test, simple escapes one 4-byte store,
             \u through the rewritten step
     esc=b   branch-free table: both classes computed, one 8-byte store
     print   report the document class and the decoder census on stderr */
#ifndef MODES43_H
#define MODES43_H

#include <stdlib.h>
#include <string.h>

static int sp43_esc = 0;
static int sp43_print = 0;

/* census of the timed string-body path, printed at exit */
static uint64_t sp43_calls, sp43_escapes, sp43_outbytes;

static void sp43_modes_init(void) {
    const char *e = getenv("SP43");
    if (!e) return;
    char buf[256];
    size_t l = strlen(e);
    if (l >= sizeof buf) l = sizeof buf - 1;
    memcpy(buf, e, l);
    buf[l] = 0;
    for (char *t = strtok(buf, ",+"); t; t = strtok(NULL, ",+")) {
        if (!strcmp(t, "esc=o")) sp43_esc = 0;
        else if (!strcmp(t, "esc=t")) sp43_esc = 1;
        else if (!strcmp(t, "esc=b")) sp43_esc = 2;
        else if (!strcmp(t, "esc=u2")) sp43_esc = 3;
        else if (!strcmp(t, "esc=dup")) sp43_esc = 4;
        else if (!strcmp(t, "esc=p6")) sp43_esc = 5;
        else if (!strcmp(t, "esc=dup2")) sp43_esc = 6;
        else if (!strcmp(t, "esc=dup3")) sp43_esc = 7;
        else if (!strcmp(t, "esc=p1")) sp43_esc = 8;
        else if (!strcmp(t, "esc=p2")) sp43_esc = 9;
        else if (!strcmp(t, "esc=p3")) sp43_esc = 10;
        else if (!strcmp(t, "esc=sni")) sp43_esc = 11;
        else if (!strcmp(t, "esc=tni")) sp43_esc = 12;
        else if (!strcmp(t, "esc=bfs")) sp43_esc = 13;
        else if (!strcmp(t, "print")) sp43_print = 1;
    }
}

static void __attribute__((destructor)) sp43_dump(void) {
    if (!sp43_print) return;
    fprintf(stderr, "SP43CALLS bodies=%llu escapes=%llu outbytes=%llu\n",
            (unsigned long long)sp43_calls,
            (unsigned long long)sp43_escapes,
            (unsigned long long)sp43_outbytes);
}

#endif /* MODES43_H */
