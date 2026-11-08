/* modes.h -- runtime selection of the variants, for the one binary that
   compares them.  Scratch.

   Every P2 build on this machine moves the canonical ratio by up to 6% when
   only *uncalled* code changes (measured: `pad_e0..e10`, identical timed path,
   99.2-105.1 ns/block).  A comparison between two builds is therefore not
   attributable to the change that separates them.  Building every variant in
   one binary and selecting it per process removes that: the timed code is the
   same object code in every arm.

   Tokens (comma separated, env SP42):
     disp    stage 1 through s1f_build_dispatch (two-phase) instead of s1f_build
     fold    escape list as per-block masks expanded in the shared pass
     noim    skip lane extraction on a block with no in-string byte
     dec=o   out-of-line decoder (the shipped shape)
     dec=i   inlined decoder (`\u` out of line), always
     dec=g   density: SPARSE inlined, PLAIN/HEAVY out of line
     dec=2   density, two classes: only PLAIN out of line
     dec=j   PLAIN out of line, everything else inlined (`\u` inlined too)
     dec=h   PLAIN out of line, SPARSE inlined (`\u` out), HEAVY inlined
     list=0  build no escape list at all
     gate    density decides whether the list is built (PLAIN -> none)
     print   report the document class on stderr */
#ifndef MODES_H
#define MODES_H

#include <stdlib.h>
#include <string.h>

static int sp_disp = 0;
static int sp_fold = 0;
static int sp_noim = 0;
static int sp_dec = 0;
static int sp_list = 1;
static int sp_gate = 0;
static int sp_print = 0;

static void sp_modes_init(void) {
    const char *e = getenv("SP42");
    if (!e) return;
    char buf[256];
    size_t l = strlen(e);
    if (l >= sizeof buf) l = sizeof buf - 1;
    memcpy(buf, e, l);
    buf[l] = 0;
    for (char *t = strtok(buf, ",+"); t; t = strtok(NULL, ",+")) {
        if (!strcmp(t, "disp")) sp_disp = 1;
        else if (!strcmp(t, "fold")) sp_fold = 1;
        else if (!strcmp(t, "noim")) sp_noim = 1;
        else if (!strcmp(t, "gate")) sp_gate = 1;
        else if (!strcmp(t, "print")) sp_print = 1;
        else if (!strcmp(t, "list=0")) sp_list = 0;
        else if (!strcmp(t, "dec=o")) sp_dec = 0;
        else if (!strcmp(t, "dec=i")) sp_dec = 1;
        else if (!strcmp(t, "dec=g")) sp_dec = 2;
        else if (!strcmp(t, "dec=2")) sp_dec = 3;
        else if (!strcmp(t, "dec=j")) sp_dec = 4;
        else if (!strcmp(t, "dec=h")) sp_dec = 5;
    }
}

#endif /* MODES_H */
