import Init.Data.ByteArray

def isSpace (b : UInt8) : Bool :=
  b == 32 || b == 9 || b == 10 || b == 13

def isPunct (b : UInt8) : Bool :=
  b == 44 || b == 58 || b == 123 || b == 125

def classify (b : UInt8) : UInt8 :=
  if isSpace b then 0 else if isPunct b then 1 else 2

def scan (buf : ByteArray) : UInt64 :=
  let rec go (i : Nat) (acc : UInt64) : UInt64 :=
    if i < buf.size then
      go (i + 1) (acc * 3 + (classify (buf.get! i)).toUInt64)
    else acc
  go 0 0

@[noinline] def scanNoInline (buf : ByteArray) : UInt64 := scan buf
