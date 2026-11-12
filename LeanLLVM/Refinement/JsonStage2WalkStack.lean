/-
The container stacks' carried contents.

`WalkInv` (`JsonStage2WalkScope`) carries the two stacks' *addresses* and the
depth, not the per-depth bytes.  A clause of the form "the byte at `sp - 1` is
`t`" is not what a link can carry: a push writes at `sp` and raises the depth, a
pop lowers it without touching memory, so the byte a later block reads at
`sp - 1` was written at an earlier index that the register clause does not
remember.  The sound shape is a carried map read off the stack's own bytes at the
carried depth:

`WalkStackBytes mem base M n` says the stack at `base` holds `M`'s first `n`
values, one byte each.  A push extends the map at the pushed index
(`walkStackBytes_push`), the container-state stores of class D rewrite it at the
index they write (`walkStackBytes_store`), a pop and the merge at `cleanup478.i`
only move the depth, which is a restriction of the same map
(`walkStackBytes_restrict`), and a link that writes anywhere else leaves it
(`walkStackBytes_write_outside`).  The helper that reads the top,
`s2_value_pos`, therefore reads the map at `sp - 1` (`walkStack_valuePos`).

What this module does not do is carry the maps in `WalkInv`.  That is a field
addition to a structure every link in six modules builds by hand
(`JsonStage2WalkScope`, `JsonStage2WalkStore`, `JsonStage2WalkPhi`,
`JsonStage2WalkPure`, `JsonStage2WalkCall`, `JsonStage2WalkFinal`), and two
local facts are owed beside it: the four class-D stores' index must be specified
as `sp - 1` (the invariant fixes the *pointer* `%arrayidx143.i` and the register
`%sub.i`, not the equality), and the push's two stores must be the two
`if.end24.i` writes at `ctype + sp` and `cst + sp`.  The laws below are the part
those links consume; the census in `JsonStage2WalkScope` says so.
-/
import LeanLLVM.Refinement.JsonStage2WalkScope

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.BlockEval

namespace WalkScope

/-! ### The map and its agreement with the stack's bytes -/

/-- **The container stack's carried contents**: the stack at `base` holds `M`'s
first `n` values, one byte each.  `n` is the carried depth, so the byte a block
reads at `sp - 1` is `M (sp - 1)` — a value the carry keeps after the depth that
produced it has moved. -/
def WalkStackBytes (mem : Mem) (base : Nat) (M : Nat → UInt8) (n : Nat) : Prop :=
  ∀ i, i < n → readByte mem (base + i) = some (M i)

/-- The byte at an index the depth admits. -/
theorem WalkStackBytes.at {mem : Mem} {base n : Nat} {M : Nat → UInt8}
    (h : WalkStackBytes mem base M n) {i : Nat} (hi : i < n) :
    readByte mem (base + i) = some (M i) :=
  h i hi

/-- **The top of the stack at a positive depth.**  This is the byte every
container-state check and every push at the top reads. -/
theorem WalkStackBytes.top {mem : Mem} {base n : Nat} {M : Nat → UInt8}
    (h : WalkStackBytes mem base M n) (hn : 0 < n) :
    readByte mem (base + (n - 1)) = some (M (n - 1)) :=
  h (n - 1) (by omega)

/-- **A restriction of the depth keeps the map.**  A pop lowers `n` and the merge
at `cleanup478.i` moves it without writing either stack, so both are this step. -/
theorem WalkStackBytes.restrict {mem : Mem} {base n n' : Nat} {M : Nat → UInt8}
    (h : WalkStackBytes mem base M n) (hn : n' ≤ n) : WalkStackBytes mem base M n' :=
  fun i hi => h i (Nat.lt_of_lt_of_le hi hn)

/-- **A write outside the stack's extent leaves it.** -/
theorem WalkStackBytes.write_outside {mem : Mem} {base n a : Nat} {M : Nat → UInt8}
    {bs : List UInt8} (h : WalkStackBytes mem base M n)
    (hout : a + bs.length ≤ base ∨ base + n ≤ a) :
    WalkStackBytes (writeBytes mem a bs) base M n := by
  intro i hi
  rw [readByte_writeBytes_outside mem bs (by omega)]
  exact h i hi

/-- **A push**: one byte written at the depth extends the map by it.  This is the
store `if.end24.i` makes at `ctype + sp` (and its state-stack twin at
`cst + sp`), with the pushed byte as the store's own list. -/
theorem WalkStackBytes.push {mem : Mem} {base n : Nat} {M : Nat → UInt8} {v : UInt8}
    (h : WalkStackBytes mem base M n) :
    WalkStackBytes (writeBytes mem (base + n) [v]) base
      (fun i => if i = n then v else M i) (n + 1) := by
  intro i hi
  by_cases hin : i = n
  · rw [hin]
    simpa using readByte_writeBytes_at mem [v] (base + n) 0 (by simp)
  · rw [readByte_writeBytes_outside mem [v] (by omega)]
    simp only [if_neg hin]
    exact h i (by omega)

/-- **A byte written at an index below the depth rewrites the map there.**  The
container-state stores of class D are this shape: one `i8` literal at the state
stack's byte the block indexed. -/
theorem WalkStackBytes.store {mem : Mem} {base n : Nat} {M : Nat → UInt8} {v : UInt8}
    (h : WalkStackBytes mem base M n) {k : Nat} (hk : k < n) :
    WalkStackBytes (writeBytes mem (base + k) [v]) base
      (fun i => if i = k then v else M i) n := by
  intro i hi
  by_cases hik : i = k
  · rw [hik]
    simpa using readByte_writeBytes_at mem [v] (base + k) 0 (by simp)
  · have hout : base + i < base + k ∨ base + k + [v].length ≤ base + i := by
      rcases Nat.lt_or_ge i k with hlt | hge
      · left; omega
      · right; simp only [List.length_cons, List.length_nil]; omega
    rw [readByte_writeBytes_outside mem [v] hout]
    simp only [if_neg hik]
    exact h i hi

/-- **A push of a `natToBytes` byte**, the store shape the body's blocks actually
emit: the pushed value is the one-byte list `natToBytes v 1`, and the map keeps
its own byte. -/
theorem WalkStackBytes.pushNat {mem : Mem} {base n : Nat} {M : Nat → UInt8} {v : Nat}
    (h : WalkStackBytes mem base M n) :
    WalkStackBytes (writeBytes mem (base + n) (natToBytes v 1)) base
      (fun i => if i = n then (natToBytes v 1).getD 0 0 else M i) (n + 1) := by
  intro i hi
  by_cases hin : i = n
  · rw [hin]
    simpa using readByte_writeBytes_at mem (natToBytes v 1) (base + n) 0
      (by simp [natToBytes_length])
  · rw [readByte_writeBytes_outside mem (natToBytes v 1) (by
      left; simp [natToBytes_length]; omega)]
    simp only [if_neg hin]
    exact h i (by omega)

/-- **A one-byte literal store at an index below the depth**, the class-D shape:
`store i8 <imm>, %arrayidx`. -/
theorem WalkStackBytes.storeNat {mem : Mem} {base n : Nat} {M : Nat → UInt8} {v : Nat}
    (h : WalkStackBytes mem base M n) {k : Nat} (hk : k < n) :
    WalkStackBytes (writeBytes mem (base + k) (natToBytes v 1)) base
      (fun i => if i = k then (natToBytes v 1).getD 0 0 else M i) n := by
  intro i hi
  by_cases hik : i = k
  · rw [hik]
    simpa using readByte_writeBytes_at mem (natToBytes v 1) (base + k) 0
      (by simp [natToBytes_length])
  · have hout : base + i < base + k ∨
        base + k + (natToBytes v 1).length ≤ base + i := by
      rcases Nat.lt_or_ge i k with hlt | hge
      · left; omega
      · right; simp [natToBytes_length]; omega
    rw [readByte_writeBytes_outside mem (natToBytes v 1) hout]
    simp only [if_neg hik]
    exact h i hi

/-! ### The body's two stack writes -/

/-- A one-byte `natToBytes` is the list of its own byte. -/
theorem walkNatToBytes_singleton (v : Nat) :
    natToBytes v 1 = [(natToBytes v 1).getD 0 0] := by
  have hlen := natToBytes_length v 1
  cases h : natToBytes v 1 with
  | nil => rw [h] at hlen; simp at hlen
  | cons y ys =>
      have hys : ys = [] := by
        rw [h] at hlen
        simpa using hlen
      subst hys
      rfl

/-- The byte `if.end24.i` pushes onto the type stack, as the store's own list
holds it. -/
def ifEnd24TyByte (b : BitVec 8) : UInt8 :=
  (natToBytes (ifEnd24Ty b).toNat 1).getD 0 0

/-- The byte `if.end24.i` pushes onto the state stack: zero. -/
def ifEnd24StByte : UInt8 := (natToBytes 0 1).getD 0 0

/-- The state stack's pushed byte is zero. -/
theorem ifEnd24StByte_zero : ifEnd24StByte = 0 := rfl

/-- **`if.end24.i`'s two stores, as one map update.**  The type stack receives
`ifEnd24TyByte b` at `sp` and the state stack zero; each store is outside the
other stack's extent, so both maps advance to depth `sp + 1`. -/
theorem walkStack_ifEnd24 {mem : Mem} {ctype cst sp : Nat} {TM SM : Nat → UInt8}
    {b : BitVec 8}
    (hT : WalkStackBytes mem ctype TM sp) (hS : WalkStackBytes mem cst SM sp)
    (hsep : cst + stage2StackExtent ≤ ctype ∨ ctype + stage2StackExtent ≤ cst)
    (hsp : sp < stage2StackExtent) :
    WalkStackBytes
        (writeBytes (writeBytes mem (ctype + sp) (natToBytes (ifEnd24Ty b).toNat 1))
          (cst + sp) (natToBytes 0 1))
        ctype (fun i => if i = sp then ifEnd24TyByte b else TM i) (sp + 1) ∧
      WalkStackBytes
        (writeBytes (writeBytes mem (ctype + sp) (natToBytes (ifEnd24Ty b).toNat 1))
          (cst + sp) (natToBytes 0 1))
        cst (fun i => if i = sp then ifEnd24StByte else SM i) (sp + 1) := by
  have hTstep : WalkStackBytes (writeBytes mem (ctype + sp)
      (natToBytes (ifEnd24Ty b).toNat 1)) ctype
      (fun i => if i = sp then ifEnd24TyByte b else TM i) (sp + 1) :=
    hT.pushNat (v := (ifEnd24Ty b).toNat)
  have hSstep : WalkStackBytes (writeBytes mem (cst + sp)
      (natToBytes 0 1)) cst
      (fun i => if i = sp then ifEnd24StByte else SM i) (sp + 1) :=
    hS.pushNat (v := 0)
  refine ⟨hTstep.write_outside ?_, ?_⟩
  · rcases hsep with h | h
    · left
      simp only [natToBytes_length]
      omega
    · right
      omega
  · refine (hS.write_outside ?_).pushNat
    rcases hsep with h | h
    · right
      omega
    · left
      simp only [natToBytes_length]
      omega

/-! ### The helper's read of the top -/

/-- **`s2_value_pos` reads the map at `sp - 1`.**  At a positive depth the helper
loads the two stacks' top bytes, and the agreement turns both into the carried
values: the map is what the helper's answer is a function of. -/
theorem walkStack_valuePos {m : Mem} {ct cs sp rd : Nat} {TM SM : Nat → UInt8}
    (hsp : sp ≠ 0) (hT : WalkStackBytes m ct TM sp) (hS : WalkStackBytes m cs SM sp) :
    stage2ValuePos m sp rd ct cs =
      some (if (TM (sp - 1)).toNat = 1 then
        (if (SM (sp - 1)).toNat = 2 then 1 else 0)
      else (if (SM (sp - 1)).toNat = 0 ∨ (SM (sp - 1)).toNat = 2 then 1 else 0)) := by
  have hlt : sp - 1 < sp := by omega
  simp only [stage2ValuePos, hsp, hT.at hlt, hS.at hlt]
  simp

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkStackBytes.at' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkStackBytes.at

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkStackBytes.top' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkStackBytes.top

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkStackBytes.restrict' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkStackBytes.restrict

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkStackBytes.write_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkStackBytes.write_outside

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkStackBytes.push' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkStackBytes.push

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkStackBytes.store' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkStackBytes.store

/-- info: 'LeanLLVM.Refinement.WalkScope.walkStack_ifEnd24' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkStack_ifEnd24

/-- info: 'LeanLLVM.Refinement.WalkScope.walkStack_valuePos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkStack_valuePos

end WalkScope
end LeanLLVM.Refinement
