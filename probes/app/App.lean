/-
A small application that uses the seam for a real task rather than as a
wrapper: locate commas in eight-byte chunks of a CSV record.

The comma mask returns a bit per input byte that is a comma, so the positions
come from reading the packed result.  `App.lean` is compiled to C and then to
LLVM IR by the probe's `build.sh`; the call to `leanllvm_comma_mask8` has no
body in this unit, so it survives the compiler.
-/
@[extern "leanllvm_comma_mask8"]
opaque commaMask8 (x : UInt64) : UInt64

/-- Byte positions of commas in one eight-byte word. -/
def commaPositions (word : UInt64) : List UInt64 :=
  let mask := commaMask8 word
  (List.range 8).filterMap fun i =>
    let i := UInt64.ofNat i
    if (mask >>> (8 * i)) &&& 0x80 == 0x80 then some i else none

/-- A CSV record, packed eight bytes at a time (`,` is `0x2C`). -/
def words : List UInt64 :=
  [ 0x2C61626364656667,  -- ",abcdefg"
    0x68696A2C6B6C6D6E,  -- "hij,klmn"
    0x6F702C2C71727374,  -- "op,,qrst"
    0x75762C7778797A2C ] -- "uv,wxyz,"

/-- Offsets of the commas in the record, as a reader would report them. -/
def commaOffsets : List UInt64 :=
  (words.zipIdx).flatMap fun (w, k) =>
    (commaPositions w).map fun i => UInt64.ofNat (8 * k) + i

def main : IO Unit := do
  IO.println s!"offsets={commaOffsets}"
  IO.println s!"fields={commaOffsets.length + 1}"
