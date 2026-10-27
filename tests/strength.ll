; Multiplication by two becomes a left shift.
define i32 @twice(i32 %x) {
entry:
  %y = mul i32 %x, 2
  ret i32 %y
}
