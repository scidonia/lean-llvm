; Constant propagation enables branch folding.
define i32 @main(i32 %x) {
entry:
  %a = add i32 1, 2
  %c = icmp eq i32 %a, 3
  br i1 %c, label %yes, label %no

yes:
  ret i32 %a

no:
  ret i32 %x
}
