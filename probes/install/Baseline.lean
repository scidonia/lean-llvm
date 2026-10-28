/-- Baseline body: the exact no-borrow comma mask from the M0 report. -/
@[export leanllvm_comma_mask8]
def commaMask8 (x : UInt64) : UInt64 :=
  let m := x ^^^ 0x2C2C2C2C2C2C2C2C
  ~~~(((m &&& 0x7F7F7F7F7F7F7F7F) + 0x7F7F7F7F7F7F7F7F) ||| m) &&& 0x8080808080808080

@[export leanllvm_impl_id]
def implId (_ : UInt64) : UInt64 := 1
