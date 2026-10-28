/-- Candidate body: a byte loop with the same contract as the baseline. -/
@[export leanllvm_comma_mask8]
def commaMask8 (x : UInt64) : UInt64 :=
  let rec go (i : Nat) (acc : UInt64) : UInt64 :=
    if i < 8 then
      let shift := UInt64.ofNat (8 * i)
      let b := (x >>> shift) &&& 0xFF
      let acc := if b = 0x2C then acc ||| (0x80 <<< shift) else acc
      go (i + 1) acc
    else acc
  go 0 0

@[export leanllvm_impl_id]
def implId (_ : UInt64) : UInt64 := 2
