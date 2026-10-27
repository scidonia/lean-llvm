; Register-valued store and select, and an alloca without an explicit align.
define i32 @roundtrip(i32 %x, ptr %p) {
entry:
  %a = alloca i32
  store i32 %x, ptr %p
  %c = icmp eq i32 %x, 0
  %s = select i1 %c, i32 %x, i32 5
  ret i32 %s
}
