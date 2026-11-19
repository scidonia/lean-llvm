/* bench-unity.c -- the harness with the stage-1 units compiled into it.

   The measured pipeline build is one translation unit, so its block loop calls
   the mask and entry text as local functions rather than across objects.  This
   file reproduces that shape for the fused and split-on-the-same-stream rows:
   it includes the two unit sources and then `bench.c`, and is compiled at the
   measured flags (`-O3 -march=x86-64-v3 -mpclmul -std=gnu11 -falign-*`).  The
   UTF-8 unit stays a linked object; it is not part of the stage-1 comparison.

   Nothing in this file changes what a row measures; `bench.sh` builds it as a
   separate binary and labels its rows a separate variant.  The unit kernels
   keep their own `noinline` attributes. */
#define _GNU_SOURCE

#include "../../kernel/json/s1_block.c"
#include "../../kernel/json/entry.c"

/* The unit headers above already define `s1_carry` and `s1_masks`. */
#define BENCH_UNITY_STAGE1
#include "bench.c"
