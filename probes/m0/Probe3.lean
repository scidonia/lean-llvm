import Init.Data.ByteArray

def isSpace (b : UInt8) : Bool :=
  b == 32 || b == 9 || b == 10 || b == 13

def isPunct (b : UInt8) : Bool :=
  b == 44 || b == 58 || b == 123 || b == 125

def classify (b : UInt8) : UInt8 :=
  if isSpace b then 0 else if isPunct b then 1 else 2

def scanFold (buf : ByteArray) : UInt64 :=
  buf.data.foldl (fun acc b => acc * 3 + (classify b).toUInt64) 0
