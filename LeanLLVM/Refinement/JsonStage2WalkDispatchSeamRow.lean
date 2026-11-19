/-
# The last level's seam rows, at any state

`HcontSeamRefusal` (`JsonStage2WalkDispatchSeams`) is the *continuing* seam's refusal shape:
the two leading calls, the answer `0` and the record `stage2ErrSetMsg` wrote.  The last
level needs the same shape at its own tail states, where the kind literal is the class's
(`if.else405.i`'s `0` for `%8 ∈ {126, 127}`), and it also needs the other answer's row:
`s2_value_pos` can answer `0`, and then the walk leaves for `if.then418.i`, stores the
refusal word at `%e + 8` and reaches the copy through `cleanup474.i` without calling
`od_scalar_value` at all.

This module states those two rows at a generic state, so that both the seam bundle
(`JsonStage2WalkDispatchSeams`'s `HlastSeam`) and the arm's payload
(`JsonStage2WalkDispatchWitnessHlast`'s `HlastHighByteRefusal`) name one shape.  The rows
carry no segment: a row is a fact about the state's memory and the call environment, and the
class's route to the copy is the dispatch's own field (`HlastRefuseRoute`).
-/
import LeanLLVM.Refinement.JsonStage2WalkFinal
import LeanLLVM.Refinement.JsonStage2WalkTraverse

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-- The memory `if.then413.i`'s kind store leaves, at a literal: the first call's memory. -/
abbrev hlastStoreAt {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    (cA : BitVec 32) : Mem :=
  writeBytes s.mem (C.stage.tok + 16) (natToBytes cA.toNat 4)

/-- **The refusal seam's rows at any state**: the kind literal (the class's `0`), the two
leading calls of the `if.then413.i`/`if.then425.i` edge, the scalar call's answer `0` and
the refusal record it wrote.  The answer and the record are the model's
(`stage2ScalarValue`'s first arm, `s2ScalarValue_refused`), not fields a caller supplies:
what the structure carries is the two calls' rows and the literal. -/
structure HlastSeamRefusal {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) :
    Type where
  /-- The kind literal the seam's store writes: the class's is `if.else405.i`'s `0`. -/
  cA : BitVec 32
  hcA : cA = BitVec.ofNat 32 0
  /-- The root-done slot's word, as the first call's argument list carries it, and the
  read that names it at the seam's own memory. -/
  rdv : BitVec 32
  hroot : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4)
  /-- The value-position call at the kind-stored memory, and its nonzero answer. -/
  r₁ : CallOutcome
  xA : BitVec 32
  hpre₁ : s2ValuePosPre
    [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv, .ptr C.stage.ctype, .ptr C.stage.cst]
    (hlastStoreAt C s cA) s.next
  hcall₁ : stage2Calls stage2SubCalls "s2_value_pos"
    [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv, .ptr C.stage.ctype, .ptr C.stage.cst]
    (hlastStoreAt C s cA) s.next = some r₁
  hret₁ : r₁.ret = .int 32 xA
  hbit0 : evalICmp .eq xA (BitVec.ofNat 32 0) = 0
  /-- The log's base word, read at the kind-stored memory. -/
  hzread : readBytes (hlastStoreAt C s cA) C.stage.z 8 = some (wordBytes 8 G.ev)
  /-- The scalar call at the memory the first one leaves, and the refusal it answers. -/
  r₂ : CallOutcome
  hpre₂ : s2ScalarValuePre
    [.ptr C.stage.c, .ptr C.stage.tok, .ptr C.stage.z] r₁.mem r₁.next
  hcall₂ : stage2Calls stage2SubCalls "od_scalar_value"
    [.ptr C.stage.c, .ptr C.stage.tok, .ptr C.stage.z] r₁.mem r₁.next = some r₂
  hret₂ : r₂.ret = .int 32 (BitVec.ofNat 32 0)
  /-- The token's position, the refusal record's offset word. -/
  pos : Nat
  hmem : r₂.mem = stage2ErrSetMsg r₁.mem C.stage.e pos 0

/-- **A refusal route**: a counted segment to the refusal copy, the block it ends at, the
word the copy's `%off` load reads, the carry's refusal offset and the price inside the
remaining entries' and bytes' credit.  The word is a field beside the segment because a
`WalkSegment` carries no memory clause (its docstring records why). -/
structure HlastRefuseRoute {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) :
    Type where
  Cd : WalkCarry G
  sd : State
  n : Nat
  seg : WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd n
  hblock : Cd.block = "if.then"
  k : Nat
  hk : k ≤ G.n
  hword : readBytes sd.mem (Cd.stage.e + 8) 8 = some (wordBytes 8 k)
  herr : Cd.eoff ≤ G.n
  hprice : n + 2 ≤ stage2EntryAllowance * (G.nep - C.k) +
    stage2ByteAllowance * (G.n - entryPos G C.k)

/-- **The value-position call's zero row**: the first call (at the memory its kind store
leaves), its answer `0`, and the route the walk takes from `if.then418.i` to the refusal
copy.  The walk leaves `if.then413.i` for `if.then418.i`, which stores the entry's position
at `%e + 8` and branches to `cleanup474.i`, then to `if.then`; no scalar call is made. -/
structure HlastSeamZero {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) : Type where
  /-- The kind literal `if.then413.i`'s store writes (the class's is `0`). -/
  cA : BitVec 32
  /-- The root-done slot's word, as the first call's argument list carries it. -/
  rdv : BitVec 32
  hread : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4)
  /-- The first call at the kind-stored memory, and its answer `0`. -/
  hpre : s2ValuePosPre
    [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv, .ptr C.stage.ctype, .ptr C.stage.cst]
    (hlastStoreAt C s cA) s.next
  r : CallOutcome
  hcall : stage2Calls stage2SubCalls "s2_value_pos"
    [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv, .ptr C.stage.ctype, .ptr C.stage.cst]
    (hlastStoreAt C s cA) s.next = some r
  hret : r.ret = .int 32 (BitVec.ofNat 32 0)
  /-- **The route**: `if.then418.i`'s refusal store, `cleanup474.i`'s release, `if.then`. -/
  route : HlastRefuseRoute G C s

end WalkScope
end LeanLLVM.Refinement
