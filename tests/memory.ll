; Memory: alloca, store, load and arithmetic.
define i32 @mem() {
entry:
  %p = alloca i32, align 4
  store i32 41, ptr %p
  %v = load i32, ptr %p
  %r = add i32 %v, 1
  ret i32 %r
}
