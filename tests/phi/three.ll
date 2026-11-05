define i32 @main(i32 %argc, ptr %argv) {
entry:
  %c1 = icmp eq i32 %argc, 1
  br i1 %c1, label %join, label %a
a:
  %c2 = icmp eq i32 %argc, 2
  br i1 %c2, label %join, label %b
b:
  br label %join
join:
  %p = phi i32 [ 10, %entry ], [ 20, %a ], [ 30, %b ]
  ret i32 %p
}
