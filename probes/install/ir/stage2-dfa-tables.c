/* stage2-dfa-tables.c -- the DFA stage-2 dispatch tables, captured.

   These are the three `static const` arrays of the byte-gated spike
   (`sd_cls`, `sd_tr` and `sd_restore`), with only the enumerations their
   initialisers name.  The spike itself is a scratch translation unit; this
   file is the part of it a proof reads, kept here so the Lean encoding of the
   same three arrays and the C bytes are compared by a build-time check rather
   than by a reader.

   `main` prints the arrays as decimal byte rows, one array per line:

     cc -O2 -std=gnu11 stage2-dfa-tables.c -o /tmp/stage2-dfa-tables
     /tmp/stage2-dfa-tables > stage2-dfa.tables.txt

   `stage2-dfa.tables.txt` is that output and is the text
   `LeanLLVM.Refinement.JsonStage2DfaTable` includes; the module's `#guard`
   compares it with the Lean table.  Editing an array here without
   regenerating the text (or editing the Lean table to match) fails that
   guard. */

#include <stdint.h>
#include <stdio.h>

enum {
    SD_ROOT = 0,      /* expecting the document's single root value */
    SD_ROOT_END,      /* root done; nothing more is legal */
    SD_OBJ_FIRST,     /* after '{': a key or '}' */
    SD_OBJ_KEY,       /* after ',': a key, and not '}' (trailing comma) */
    SD_OBJ_COLON,     /* after a key: ':' */
    SD_OBJ_VAL,       /* after ':': a value */
    SD_OBJ_COMMA,     /* after a value: ',' or '}' */
    SD_ARR_FIRST,     /* after '[': a value or ']' */
    SD_ARR_VAL,       /* after ',': a value, and not ']' (trailing comma) */
    SD_ARR_COMMA      /* after a value: ',' or ']' */
};

enum {
    A_NONE = 0,       /* comma or colon: state change only */
    A_OPEN_OBJ,
    A_OPEN_ARR,
    A_CLOSE_OBJ,
    A_CLOSE_ARR,
    A_QUOTE,          /* a key or a string, decided by the previous state */
    A_SCALAR,
    A_ERR             /* the entry is not legal in this state */
};

/* Symbols: 0 '{', 1 '[', 2 '}', 3 ']', 4 ',', 5 ':', 6 '"', 7 scalar start. */
static const uint8_t sd_cls[256] = {
    [0 ... 255] = 7,
    ['{'] = 0, ['['] = 1, ['}'] = 2, [']'] = 3,
    [','] = 4, [':'] = 5, ['"'] = 6
};

#define SD_T(a, n) ((uint8_t)(((a) << 4) | (n)))
/* sd_tr[state][symbol] = (action << 4) | next state; a close's next state is
   the stack's restore value and the field is unused. */
static const uint8_t sd_tr[10][8] = {
    /* SD_ROOT */
    { SD_T(A_OPEN_OBJ, SD_OBJ_FIRST), SD_T(A_OPEN_ARR, SD_ARR_FIRST),
      SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0),
      SD_T(A_QUOTE, SD_ROOT_END), SD_T(A_SCALAR, SD_ROOT_END) },
    /* SD_ROOT_END */
    { SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0),
      SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0) },
    /* SD_OBJ_FIRST: key or '}' */
    { SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_CLOSE_OBJ, 0), SD_T(A_ERR, 0),
      SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_QUOTE, SD_OBJ_COLON),
      SD_T(A_ERR, 0) },
    /* SD_OBJ_KEY: key only */
    { SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0),
      SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_QUOTE, SD_OBJ_COLON),
      SD_T(A_ERR, 0) },
    /* SD_OBJ_COLON: ':' only */
    { SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0),
      SD_T(A_ERR, 0), SD_T(A_NONE, SD_OBJ_VAL), SD_T(A_ERR, 0),
      SD_T(A_ERR, 0) },
    /* SD_OBJ_VAL: a value */
    { SD_T(A_OPEN_OBJ, SD_OBJ_FIRST), SD_T(A_OPEN_ARR, SD_ARR_FIRST),
      SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0),
      SD_T(A_QUOTE, SD_OBJ_COMMA), SD_T(A_SCALAR, SD_OBJ_COMMA) },
    /* SD_OBJ_COMMA: ',' or '}' */
    { SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_CLOSE_OBJ, 0), SD_T(A_ERR, 0),
      SD_T(A_NONE, SD_OBJ_KEY), SD_T(A_ERR, 0), SD_T(A_ERR, 0),
      SD_T(A_ERR, 0) },
    /* SD_ARR_FIRST: a value or ']' */
    { SD_T(A_OPEN_OBJ, SD_OBJ_FIRST), SD_T(A_OPEN_ARR, SD_ARR_FIRST),
      SD_T(A_ERR, 0), SD_T(A_CLOSE_ARR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0),
      SD_T(A_QUOTE, SD_ARR_COMMA), SD_T(A_SCALAR, SD_ARR_COMMA) },
    /* SD_ARR_VAL: a value only */
    { SD_T(A_OPEN_OBJ, SD_OBJ_FIRST), SD_T(A_OPEN_ARR, SD_ARR_FIRST),
      SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0),
      SD_T(A_QUOTE, SD_ARR_COMMA), SD_T(A_SCALAR, SD_ARR_COMMA) },
    /* SD_ARR_COMMA: ',' or ']' */
    { SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_CLOSE_ARR, 0),
      SD_T(A_NONE, SD_ARR_VAL), SD_T(A_ERR, 0), SD_T(A_ERR, 0),
      SD_T(A_ERR, 0) },
};

/* The state a parent frame resumes in once its child closes: the frame is
   either an object expecting a value (after ':') or an array expecting one
   (after '[' or ','). */
static const uint8_t sd_restore[10] = {
    [SD_OBJ_VAL] = SD_OBJ_COMMA,
    [SD_ARR_FIRST] = SD_ARR_COMMA,
    [SD_ARR_VAL] = SD_ARR_COMMA
};

int main(void) {
    printf("sd_cls");
    for (int i = 0; i < 256; i++) printf(" %u", (unsigned)sd_cls[i]);
    printf("\nsd_tr");
    for (int s = 0; s < 10; s++)
        for (int y = 0; y < 8; y++) printf(" %u", (unsigned)sd_tr[s][y]);
    printf("\nsd_restore");
    for (int s = 0; s < 10; s++) printf(" %u", (unsigned)sd_restore[s]);
    printf("\n");
    return 0;
}
