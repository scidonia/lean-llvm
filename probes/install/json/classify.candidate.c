#include <stdint.h>
#include <immintrin.h>

/* The twelve bytes the classifier marks: the six structural characters
   `{ } [ ] : ,` and the string delimiters `"` and `\`, plus the four
   whitespace bytes space, tab, newline and carriage return (RFC 8259 §2's ws
   production).  32 lanes, one bit per lane in the returned i32, lane 0 in
   bit 0. */
uint32_t leanllvm_json_classify32(const uint8_t *p) {
  __m256i v = _mm256_loadu_si256((const __m256i *)p);
  __m256i m = _mm256_cmpeq_epi8(v, _mm256_set1_epi8('"'));
  m = _mm256_or_si256(m, _mm256_cmpeq_epi8(v, _mm256_set1_epi8('\\')));
  m = _mm256_or_si256(m, _mm256_cmpeq_epi8(v, _mm256_set1_epi8(':')));
  m = _mm256_or_si256(m, _mm256_cmpeq_epi8(v, _mm256_set1_epi8(',')));
  m = _mm256_or_si256(m, _mm256_cmpeq_epi8(v, _mm256_set1_epi8('{')));
  m = _mm256_or_si256(m, _mm256_cmpeq_epi8(v, _mm256_set1_epi8('}')));
  m = _mm256_or_si256(m, _mm256_cmpeq_epi8(v, _mm256_set1_epi8('[')));
  m = _mm256_or_si256(m, _mm256_cmpeq_epi8(v, _mm256_set1_epi8(']')));
  m = _mm256_or_si256(m, _mm256_cmpeq_epi8(v, _mm256_set1_epi8(' ')));
  m = _mm256_or_si256(m, _mm256_cmpeq_epi8(v, _mm256_set1_epi8('\t')));
  m = _mm256_or_si256(m, _mm256_cmpeq_epi8(v, _mm256_set1_epi8('\n')));
  m = _mm256_or_si256(m, _mm256_cmpeq_epi8(v, _mm256_set1_epi8('\r')));
  return (uint32_t)_mm256_movemask_epi8(m);
}
