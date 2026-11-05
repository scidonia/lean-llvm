define i64 @depth_count(ptr %buf, ptr %idx, i64 %nidx, ptr %stats) {
entry:
  %nz = icmp eq i64 %nidx, 0
  br i1 %nz, label %exit0, label %loop
loop:
  %k = phi i64 [ 0, %entry ], [ %kn, %loop ]
  %sp = phi i64 [ 0, %entry ], [ %spn, %loop ]
  %sum = phi i64 [ 0, %entry ], [ %sumn, %loop ]
  %ip = getelementptr inbounds i32, ptr %idx, i64 %k
  %p32 = load i32, ptr %ip
  %p = zext i32 %p32 to i64
  %cp = getelementptr inbounds i8, ptr %buf, i64 %p
  %c = load i8, ptr %cp
  %o1 = icmp eq i8 %c, 123
  %o2 = icmp eq i8 %c, 91
  %isopen = or i1 %o1, %o2
  %c1 = icmp eq i8 %c, 125
  %c2 = icmp eq i8 %c, 93
  %isclose = or i1 %c1, %c2
  %inc = zext i1 %isopen to i64
  %dec = zext i1 %isclose to i64
  %delta = sub i64 %inc, %dec
  %spn = add i64 %sp, %delta
  %sumn = add i64 %sum, %spn
  %kn = add i64 %k, 1
  %more = icmp ult i64 %kn, %nidx
  br i1 %more, label %loop, label %exit
exit:
  store i64 %spn, ptr %stats
  %stats1 = getelementptr inbounds i64, ptr %stats, i64 1
  store i64 %sumn, ptr %stats1
  ret i64 %spn
exit0:
  store i64 0, ptr %stats
  %statsz = getelementptr inbounds i64, ptr %stats, i64 1
  store i64 0, ptr %statsz
  ret i64 0
}
