; The caller used by the contextual theorem: one call to the seam, whose
; result is returned.  The seam is resolved by the semantics' call
; environment, which is where the linker's selection appears.
declare i64 @leanllvm_comma_mask8(i64)

define i64 @leanllvm_caller(i64 %arg) {
entry:
  %r = call i64 @leanllvm_comma_mask8(i64 %arg)
  ret i64 %r
}
