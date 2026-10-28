/-- The caller sees only an opaque declaration. The baseline and candidate
objects provide the symbol; the build selects one at link time. -/
@[extern "leanllvm_comma_mask8"]
opaque seamCommaMask8 (x : UInt64) : UInt64

/-- A marker from the selected object, so the experiment can show which body
was linked without relying on output equivalence. -/
@[extern "leanllvm_impl_id"]
opaque seamImplId (dummy : UInt64) : UInt64

def words : List UInt64 :=
  [0x2D2C, 0x2C2C2C2C2C2C2C2C, 0, 0x0102030405060708]

def main : IO Unit := do
  IO.println s!"impl={seamImplId 0}"
  for w in words do
    IO.println s!"{w} {seamCommaMask8 w}"
