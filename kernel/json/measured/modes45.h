/* modes45.h -- runtime selection of the entry-emitter kernel, for the one
   binary that compares the kernels (SP45 env).  Scratch.

   Tokens (comma separated):
     auto   the document probe decides (the default)
     kpos8  force the POS8 byte-table kernel
     k2     force the two-entry batch
     k4     force the four-entry batch
     k8     force the eight-entry batch
     c1     the eight-entry kernel, duplicate placement A
     c2     the eight-entry kernel, duplicate placement B
     p1     the POS8 kernel, duplicate placement A
     p2     the POS8 kernel, duplicate placement B
     print  report the probe reading and the chosen kernel on stderr

   `auto` and every forced arm run the same stage-1 object code up to the
   s1f_expand_k call, so a difference between arms is the kernel's own cost
   plus the address it landed at; c1/c2 are identical code at two other
   addresses and bound the second term. */
#ifndef MODES45_H
#define MODES45_H

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int sp45_kern = -1;     /* -1: probe decides */
static int sp45_print = 0;

static void sp45_modes_init(void) {
    const char *e = getenv("SP45");
    if (!e) return;
    char buf[256];
    size_t l = strlen(e);
    if (l >= sizeof buf) l = sizeof buf - 1;
    memcpy(buf, e, l);
    buf[l] = 0;
    for (char *t = strtok(buf, ",+"); t; t = strtok(NULL, ",+")) {
        if (!strcmp(t, "auto")) sp45_kern = -1;
        else if (!strcmp(t, "kpos8")) sp45_kern = DENS_K_POS8;
        else if (!strcmp(t, "k2")) sp45_kern = DENS_K_B2;
        else if (!strcmp(t, "k4")) sp45_kern = DENS_K_B4;
        else if (!strcmp(t, "k8")) sp45_kern = DENS_K_B8;
        else if (!strcmp(t, "c1")) sp45_kern = 4;
        else if (!strcmp(t, "c2")) sp45_kern = 5;
        else if (!strcmp(t, "p1")) sp45_kern = 6;
        else if (!strcmp(t, "p2")) sp45_kern = 7;
        else if (!strcmp(t, "print")) sp45_print = 1;
    }
}

static void __attribute__((destructor)) sp45_dump(void) {
    if (!sp45_print) return;
    fprintf(stderr, "PROBE esc_class=%d ent_q8=%d ent_per_blk=%.2f "
                    "kernel=%d forced=%d\n",
            dens_doc_class, dens_ent_q8, (double)dens_ent_q8 / 256.0,
            s1f_kern, sp45_kern);
}

#endif /* MODES45_H */
