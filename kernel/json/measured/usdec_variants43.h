/* usdec_variants43.h -- the list decoder with each escape-step shape, all in
   one binary.  Scratch.  Included from s2port.h under SP43_MODES only, after
   usdec.h and usdec_esc43.h.

   Arms:
     us_dec_x_dup43   a second copy of the shipped body (us_esc).  Its delta
                      from us_dec_x is the placement floor of this method:
                      identical source, different address.
     us_dec_x_u2_43   shipped class branch, rewritten \u step
     us_dec_x_tab43   table-driven class test + rewritten \u
     us_dec_x_bf43    branch-free table + rewritten \u
     us_dec_x_p6_43   the floor probe: the body is only copied */
#ifndef USDEC_VARIANTS43_H
#define USDEC_VARIANTS43_H

#define USDEC_ATTR __attribute__((noinline)) static

#undef US_XP_DIAG
#define US_XP_DIAG 0

#define USDEC_NAME us_dec_x_dup43
#define USDEC_ESCFN us_esc
#include "usdec_x_body.inc"
#undef USDEC_NAME
#undef USDEC_ESCFN

#define USDEC_NAME us_dec_x_dup2_43
#define USDEC_ESCFN us_esc
#include "usdec_x_body.inc"
#undef USDEC_NAME
#undef USDEC_ESCFN

#define USDEC_NAME us_dec_x_dup3_43
#define USDEC_ESCFN us_esc
#include "usdec_x_body.inc"
#undef USDEC_NAME
#undef USDEC_ESCFN

#define USDEC_NAME us_dec_x_u2_43
#define USDEC_ESCFN us_esc_u2only
#include "usdec_x_body.inc"
#undef USDEC_NAME
#undef USDEC_ESCFN

#define USDEC_NAME us_dec_x_tab43
#define USDEC_ESCFN us_esc_t
#include "usdec_x_body.inc"
#undef USDEC_NAME
#undef USDEC_ESCFN

#define USDEC_NAME us_dec_x_sni43
#define USDEC_ESCFN us_esc_sni
#include "usdec_x_body.inc"
#undef USDEC_NAME
#undef USDEC_ESCFN

#define USDEC_NAME us_dec_x_tni43
#define USDEC_ESCFN us_esc_tni
#include "usdec_x_body.inc"
#undef USDEC_NAME
#undef USDEC_ESCFN

#define USDEC_NAME us_dec_x_bfs43
#define USDEC_ESCFN us_esc_bfs
#include "usdec_x_body.inc"
#undef USDEC_NAME
#undef USDEC_ESCFN

#define USDEC_NAME us_dec_x_bf43
#define USDEC_ESCFN us_esc_bf
#include "usdec_x_body.inc"
#undef USDEC_NAME
#undef USDEC_ESCFN

#undef US_XP_DIAG
#define US_XP_DIAG 1
#define USDEC_NAME us_dec_x_p1_43
#define USDEC_ESCFN us_esc
#include "usdec_x_body.inc"
#undef USDEC_NAME
#undef USDEC_ESCFN

#undef US_XP_DIAG
#define US_XP_DIAG 2
#define USDEC_NAME us_dec_x_p2_43
#define USDEC_ESCFN us_esc
#include "usdec_x_body.inc"
#undef USDEC_NAME
#undef USDEC_ESCFN

#undef US_XP_DIAG
#define US_XP_DIAG 3
#define USDEC_NAME us_dec_x_p3_43
#define USDEC_ESCFN us_esc
#include "usdec_x_body.inc"
#undef USDEC_NAME
#undef USDEC_ESCFN

#undef US_XP_DIAG
#define US_XP_DIAG 6
#define USDEC_NAME us_dec_x_p6_43
#define USDEC_ESCFN us_esc
#include "usdec_x_body.inc"
#undef USDEC_NAME
#undef USDEC_ESCFN
#undef US_XP_DIAG
#define US_XP_DIAG 0

#undef USDEC_ATTR

#endif /* USDEC_VARIANTS43_H */
