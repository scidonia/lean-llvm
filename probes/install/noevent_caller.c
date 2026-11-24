/* The no-event stage-2 unit's installation caller.
 *
 * The selector links a caller object with the selected unit, and the caller
 * must import the unit's symbol: that import is what the selector's `nm -u`
 * check reads.  The comma-mask caller cannot serve here — its symbol is the
 * one-word seam — so this caller names the entry the installed object defines.
 *
 * The installed object is compiled from the pinned emission, whose parameters
 * are the twelve-slot ABI followed by the four local objects the fragment
 * cannot allocate (`probes/install/ir/stage2-noevent.staging.tsv`: the
 * container stack, the refusal record, the cursor record and the number path's
 * output slot).  The caller stages those four objects, because the emitted
 * function takes them as parameters.
 *
 * It runs one empty document through the entry and exits 0 when the entry
 * returns a verdict word, which is the whole of the observable this installation
 * route checks.  The values the unit reports on a document are the differential
 * gate's subject (`tests/json-noevent/check.sh`), not this caller's.
 */
#include <stdint.h>
#include <stdio.h>

extern uint64_t leanllvm_json_stage2_noevent(
    const uint8_t *b, uint64_t n, const uint32_t *ep, uint64_t nep,
    const uint32_t *xp, uint64_t nxp, uint8_t *scratch, uint64_t scratchcap,
    uint64_t *tokens, uint64_t *values, uint64_t *sum, uint64_t *err,
    uint8_t *stk, uint8_t *e, uint8_t *c, uint8_t *d);

int main(void) {
  static const uint8_t document[1] = {0};
  static uint8_t scratch[8];
  static uint8_t stk[520];
  static uint8_t e[24];
  static uint8_t c[1192];
  static uint8_t d[8];
  uint64_t tokens = 0, values = 0, sum = 0, err = 0;
  /* An empty document is admitted or refused by the walk's own rules; the
     verdict is the return value, so a call that returns a word the ABI defines
     is the link's observable. */
  uint64_t verdict = leanllvm_json_stage2_noevent(
      document, 0, 0, 0, 0, 0, scratch, sizeof scratch, &tokens, &values, &sum,
      &err, stk, e, c, d);
  if (verdict > 1) {
    fprintf(stderr, "noevent caller: verdict %llu is not a word the ABI defines\n",
            (unsigned long long)verdict);
    return 1;
  }
  printf("verdict=%llu\n", (unsigned long long)verdict);
  return 0;
}
