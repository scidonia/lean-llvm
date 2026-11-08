/* modes44.h -- runtime selection of the carried-kind arms, for the one binary
   that compares them (SP44 env).  Scratch.

   Tokens (comma or + separated):
     off    shipped: no kind record, shipped escape step
     pro    stage 1 computes and stores the kind record; shipped consumer
            (prices the producer)
     rec    carried kind, if dispatch
     recj   carried kind, computed goto
     recs   carried kind, switch
     dupa   copy A of the shipped consumer      (placement floor)
     dupb   copy B of the shipped consumer      (placement floor)
     rdup   copy A of the `if` consumer         (placement floor)
     rdup2  copy B of the `if` consumer         (placement floor)
     print  report the decoder census on stderr */
#ifndef MODES44_H
#define MODES44_H

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int sp44_kind = 0;   /* stage 1 computes and stores the kind record */
static int sp44_dec = 0;    /* 0 shipped; 1 if; 2 jmp; 3 switch;
                               4 dupA; 5 dupB; 6 rec-dupA; 7 rec-dupB */
static int sp44_print = 0;

static uint64_t sp44_calls, sp44_escapes, sp44_outbytes, sp44_kindbits;

static void sp44_modes_init(void) {
    const char *e = getenv("SP44");
    if (!e) return;
    char buf[256];
    size_t l = strlen(e);
    if (l >= sizeof buf) l = sizeof buf - 1;
    memcpy(buf, e, l);
    buf[l] = 0;
    for (char *t = strtok(buf, ",+"); t; t = strtok(NULL, ",+")) {
        if (!strcmp(t, "off")) { sp44_kind = 0; sp44_dec = 0; }
        else if (!strcmp(t, "pro")) { sp44_kind = 1; sp44_dec = 0; }
        else if (!strcmp(t, "rec")) { sp44_kind = 1; sp44_dec = 1; }
        else if (!strcmp(t, "recj")) { sp44_kind = 1; sp44_dec = 2; }
        else if (!strcmp(t, "recs")) { sp44_kind = 1; sp44_dec = 3; }
        else if (!strcmp(t, "dupa")) { sp44_kind = 1; sp44_dec = 4; }
        else if (!strcmp(t, "dupb")) { sp44_kind = 1; sp44_dec = 5; }
        else if (!strcmp(t, "rdup")) { sp44_kind = 1; sp44_dec = 6; }
        else if (!strcmp(t, "rdup2")) { sp44_kind = 1; sp44_dec = 7; }
        else if (!strcmp(t, "print")) sp44_print = 1;
    }
}

static void __attribute__((destructor)) sp44_dump(void) {
    if (!sp44_print) return;
    fprintf(stderr, "SP44CALLS bodies=%llu escapes=%llu outbytes=%llu kindbits=%llu\n",
            (unsigned long long)sp44_calls, (unsigned long long)sp44_escapes,
            (unsigned long long)sp44_outbytes,
            (unsigned long long)sp44_kindbits);
}

#endif /* MODES44_H */
