/* stage2_dfa.h -- the table-driven dispatch candidate's entry.  Bench-only:
   the certified `stage2.h` remains the default, and this header is not
   included by the route. */
#ifndef LEANLLVM_KERNEL_JSON_STAGE2_DFA_H
#define LEANLLVM_KERNEL_JSON_STAGE2_DFA_H

#include <stdint.h>

uint64_t leanllvm_json_stage2_dfa(const uint8_t *b, uint64_t n,
                                  const uint32_t *ep, uint64_t nep,
                                  const uint32_t *xp, uint64_t nxp,
                                  uint8_t *dst, uint64_t dstcap,
                                  uint64_t *ndst,
                                  uint8_t *ev, uint64_t evcap,
                                  uint64_t *nev,
                                  uint64_t *err);

uint64_t leanllvm_json_pipeline_dfa(const uint8_t *b, uint64_t n,
                                    uint64_t *sc, uint64_t *mk, uint64_t *entw,
                                    uint32_t *ep, uint64_t epcap, uint64_t *nk,
                                    uint32_t *xp, uint64_t xpcap, uint64_t *nxp,
                                    uint64_t *xcarry,
                                    uint8_t *dst, uint64_t dstcap,
                                    uint64_t *ndst,
                                    uint8_t *ev, uint64_t evcap,
                                    uint64_t *nev,
                                    uint64_t *err, uint64_t arm);

#endif
