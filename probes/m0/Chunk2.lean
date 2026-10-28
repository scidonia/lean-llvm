/-- Exact per-byte comma mask for one 64-bit word.

Bit `8*i + 7` is set iff byte `i` equals `0x2C`, for little-endian lanes.
The no-borrow form is deliberate: the usual `(m - 0x0101…) & ~m` idiom
misclassifies a lane that follows a matching lane (e.g. `0x2D2C`). -/
@[export leanllvm_comma_mask8]
def commaMask8 (x : UInt64) : UInt64 :=
  let m := x ^^^ 0x2C2C2C2C2C2C2C2C
  ~~~(((m &&& 0x7F7F7F7F7F7F7F7F) + 0x7F7F7F7F7F7F7F7F) ||| m) &&& 0x8080808080808080

/-- A same-translation-unit caller: clang inlines the exported body here. -/
def useIt (x : UInt64) : UInt64 := commaMask8 x * 2

/-- The opaque declaration used by the first integration seam: no body is
available to this translation unit, so the call survives optimisation. -/
@[extern "leanllvm_comma_mask8_ext"]
opaque commaMask8Ext (x : UInt64) : UInt64

def useItExt (x : UInt64) : UInt64 := commaMask8Ext x * 2
