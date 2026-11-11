define i32 @main() {
entry:
  br label %loop
loop:
  %a = phi i32 [ 1, %entry ], [ %b, %loop ]
  %b = phi i32 [ 2, %entry ], [ %a, %loop ]
  %i = phi i32 [ 0, %entry ], [ %j, %loop ]
  %j = add i32 %i, 1
  %again = icmp ult i32 %j, 2
  br i1 %again, label %loop, label %done
done:
  ret i32 %b
}
