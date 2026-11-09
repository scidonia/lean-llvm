/* walk_e.inc -- the index-stream tokenizer with the three-path string body.
   Scratch; not part of the repository.

   Same tokenizer and grammar as od_walk_s; only the string body handler is
   replaced by the escape-mask dispatch (str3body.inc), which inlines paths 1
   and 2 into the walk and leaves path 3 a call. */
#define WNAME od_walk_e
#define WSTEP od_step_s
#define WGAPRE od_gap_recover
#define WSTR od_string_body_e
#include "walk_body.inc"
