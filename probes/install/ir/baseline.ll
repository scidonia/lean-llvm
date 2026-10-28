; The baseline seam as emitted, in the fragment `LeanLLVM.Semantics` models.
;
;   clang -S -emit-llvm -O0 -Xclang -disable-O0-optnone \
;     -I"$(lake env lean --print-prefix)/include" <Baseline.c body behind the
;     header's own static-inline UInt64 primitives>
;   opt -passes='function(mem2reg),instnamer'
;
; then the verbatim `define` block of @leanllvm_comma_mask8, with the textual
; syntax listed in capture.sh removed.  The body is the source expression
; operation for operation: the parameter is XORed with the comma pattern, masked
; against 0x7F.., given the 0x7F.. bias, OR-ed with the XOR word, complemented
; and masked against 0x80...
; LeanLLVM/Vellum/CommaMaskIR.lean proves this body returns `swar x` for every
; `x`, by rewriting it to `CommaMask.swar` (no bit-blasting).
define i64 @leanllvm_comma_mask8(i64 %arg) {
bb:
  br label %bb1

bb1:                                              ; preds = %bb
  %i = xor i64 %arg, 3182967604875373612
  %i2 = and i64 %i, 9187201950435737471
  %i3 = add i64 %i2, 9187201950435737471
  %i4 = or i64 %i3, %i
  %i5 = xor i64 %i4, -1
  %i6 = and i64 %i5, -9187201950435737472
  ret i64 %i6
}
