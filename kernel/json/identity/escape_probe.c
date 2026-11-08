/* escape_probe.c -- the extracted side of the escape unit's IR identity arm.

   The translation unit is `escape.c` itself, included so `llvm-extract` lifts
   the unit's own ABI functions and its `us_dec_x` rather than a copy of them.
   Nothing else is added: the two entries are already definitions in the unit,
   and adding a wrapper would compare the wrapper instead of them. */
#include "../escape.c"
