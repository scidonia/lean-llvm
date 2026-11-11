define i8 @roundtrip_gep() {
entry:
  %p = alloca i8
  store i8 7, ptr %p
  %q = getelementptr i8, ptr %p, i64 2
  %r = getelementptr i8, ptr %q, i64 -2
  %v = load i8, ptr %r
  ret i8 %v
}
