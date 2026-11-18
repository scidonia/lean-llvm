/* filler.c -- a link-order padding function used only to move the kernel
   objects' code addresses.

   `FILLER_N` controls the size: the body is that many one-byte `nop`s.  Built
   with `FILLER_N=0` the object still emits a function and its padding, which is
   what a build with no `-DFILLER_N` uses; `FILLER_N=4096` shifts every object
   linked after it by four kilobytes.

   This exists to measure, not to be linked into a product: it is how
   `cost-profile` shows that the same kernel objects and the same call can
   differ by more than a factor of 1.5 across placements at a fixed calibrated
   clock.  See README.md. */
#ifndef FILLER_N
#define FILLER_N 0
#endif
#define FILLER_S2(x) #x
#define FILLER_S(x) FILLER_S2(x)

__attribute__((noinline, used)) void cost_profile_filler(void) {
  __asm__ volatile(".rept " FILLER_S(FILLER_N) "\n nop\n .endr" ::: "memory");
}
