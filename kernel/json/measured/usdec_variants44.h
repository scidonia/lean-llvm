/* usdec_variants44.h -- the list decoder with the carried-kind escape step,
   and the identical-copy controls that establish the placement floor, all in
   one binary.  Scratch.

     us_dec_x_dup44      shipped consumer, copy A       (placement control)
     us_dec_x_dup2_44    shipped consumer, copy B       (placement control)
     us_dec_x_kif44      carried kind, if dispatch
     us_dec_x_kjmp44     carried kind, computed goto
     us_dec_x_ksw44      carried kind, switch
     us_dec_x_kifdup44   identical copy of kif          (placement control)
     us_dec_x_kifdup2_44 identical copy of kif, third   (placement control) */
#ifndef USDEC_VARIANTS44_H
#define USDEC_VARIANTS44_H

#include "usdec_kind44.h"

#define USDEC_ATTR __attribute__((noinline)) static

#undef US_XP_DIAG
#define US_XP_DIAG 0

/* ---- placement controls: the shipped consumer, three addresses ---------- */
#define USDEC_NAME us_dec_x_dup44
#define USDEC_ESCFN us_esc
#include "usdec_x_body.inc"
#undef USDEC_NAME
#undef USDEC_ESCFN

#define USDEC_NAME us_dec_x_dup2_44
#define USDEC_ESCFN us_esc
#include "usdec_x_body.inc"
#undef USDEC_NAME
#undef USDEC_ESCFN

/* ---- carried kind ------------------------------------------------------ */
#define USDEC_NAME us_dec_x_kif44
#define USDEC_ESCFN us_esc_k_if
#include "usdec_x_kind.inc"
#undef USDEC_NAME
#undef USDEC_ESCFN

#define USDEC_NAME us_dec_x_kjmp44
#define USDEC_ESCFN us_esc_k_jmp
#include "usdec_x_kind.inc"
#undef USDEC_NAME
#undef USDEC_ESCFN

#define USDEC_NAME us_dec_x_ksw44
#define USDEC_ESCFN us_esc_k_sw
#include "usdec_x_kind.inc"
#undef USDEC_NAME
#undef USDEC_ESCFN

/* ---- identical copies of the `if` shape -------------------------------- */
#define USDEC_NAME us_dec_x_kifdup44
#define USDEC_ESCFN us_esc_k_if
#include "usdec_x_kind.inc"
#undef USDEC_NAME
#undef USDEC_ESCFN

#define USDEC_NAME us_dec_x_kifdup2_44
#define USDEC_ESCFN us_esc_k_if
#include "usdec_x_kind.inc"
#undef USDEC_NAME
#undef USDEC_ESCFN

#undef USDEC_ATTR

#endif /* USDEC_VARIANTS44_H */
