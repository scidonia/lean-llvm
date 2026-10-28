; probes/install/build/Baseline.c emitted at -O1, for the record:
;
;   clang -S -emit-llvm -O1 -I"$(lake env lean --print-prefix)/include" \
;     probes/install/build/Baseline.c
;
; verbatim `define` block of @leanllvm_comma_mask8.  InstCombine has rewritten
; the mask and the final complement here (`x &&& 0x7F..` for `m &&& 0x7F..`,
; `^^^ 0x80..` for `~~~ _ &&& 0x80..`), so relating this body to
; `CommaMask.swar` is a bit-level fact rather than the source expression.  It is
; kept as evidence of that difference; baseline.ll is the fixture used.
define range(i64 0, -9187201950435737471) i64 @leanllvm_comma_mask8(i64 noundef %0) local_unnamed_addr #0 {
  %2 = and i64 %0, 9187201950435737471
  %3 = xor i64 %2, 3182967604875373612
  %4 = add nuw i64 %3, 9187201950435737471
  %5 = or i64 %4, %0
  %6 = and i64 %5, -9187201950435737472
  %7 = xor i64 %6, -9187201950435737472
  ret i64 %7
}
