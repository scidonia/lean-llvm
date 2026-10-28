; A call is carried through the pipeline: constant propagation substitutes into
; the call's argument list, and the passes rewrite neither the call nor its
; result.  The declaration is what makes the emitted text assemble.
declare i64 @leanllvm_comma_mask8(i64)

define i64 @caller(i64 %arg) {
entry:
  %c = add i64 40, 2
  %r = call i64 @leanllvm_comma_mask8(i64 %c)
  ret i64 %r
}
