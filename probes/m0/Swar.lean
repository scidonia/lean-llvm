/-- Regression guards for the mask contract in `Chunk2.lean`.

The borrow idiom is not an exact lane mask: for `0x2D2C` it marks the
non-matching lane 1 as well. The no-borrow form marks only lane 0. -/
def commaMaskBorrow (x : UInt64) : UInt64 :=
  let m := x ^^^ 0x2C2C2C2C2C2C2C2C
  (m - 0x0101010101010101) &&& ~~~m &&& 0x8080808080808080

def commaMaskExact (x : UInt64) : UInt64 :=
  let m := x ^^^ 0x2C2C2C2C2C2C2C2C
  ~~~(((m &&& 0x7F7F7F7F7F7F7F7F) + 0x7F7F7F7F7F7F7F7F) ||| m) &&& 0x8080808080808080

#guard commaMaskBorrow 0x2D2C = 0x8080
#guard commaMaskExact 0x2D2C = 0x80
#guard commaMaskExact 0x2C2C2C2C2C2C2C2C = 0x8080808080808080
#guard commaMaskExact 0 = 0
