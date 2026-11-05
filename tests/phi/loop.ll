define i32 @main() {
entry:
  br label %head
head:
  %i = phi i32 [ 0, %entry ], [ %j, %body ]
  %c = icmp ult i32 %i, 3
  br i1 %c, label %body, label %exit
body:
  %j = add i32 %i, 1
  br label %head
exit:
  ret i32 %i
}
