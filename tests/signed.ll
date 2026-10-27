; Signed division truncates toward zero; srem follows the dividend's sign.
define i32 @signed() {
entry:
  %d = sdiv i32 -5, 2
  %r = srem i32 -5, 2
  %s = mul i32 %d, 10
  %t = add i32 %s, %r
  ret i32 %t
}
