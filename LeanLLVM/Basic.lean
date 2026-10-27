/-
Core data types shared by the syntax, the semantics and the transformations.

The model targets the LLVM IR that reaches the late optimisation pipeline: the
scalar integer core plus a byte-addressed memory.  Aggregates, floating point,
vectors and pointer provenance are deliberately outside the first slice, and the
parser refuses them rather than silently approximating them.
-/
namespace LeanLLVM

/-- LLVM value types modelled by the core. -/
inductive Ty where
  | int (w : Nat)
  | ptr
  | void
  deriving DecidableEq, Repr

/-- Number of bytes a value of this type occupies in memory. -/
def Ty.sizeBytes : Ty → Nat
  | .int w => (w + 7) / 8
  | .ptr => 8
  | .void => 0

/-- A literal operand, as it appears in textual IR. -/
inductive Const where
  | int (w : Nat) (v : BitVec w)
  | null
  | undef
  | poison
  deriving DecidableEq, Repr

/-- A dynamically typed value.  Integer values carry their width, so arithmetic
is width-checked when an operand is read. -/
inductive Value where
  | int (w : Nat) (v : BitVec w)
  | ptr (addr : Nat)
  deriving DecidableEq, Repr

/-- The value of a literal.  `undef` and `poison` are modelled as undefined
behaviour: the first slice has no nondeterministic or poison semantics, so a
program that reads one is `ub`.  This is a conservative model for an optimiser:
it permits fewer rewrites than LLVM's own semantics, never more. -/
def Const.toValue : Const → Option Value
  | .int w v => some (.int w v)
  | .null => some (.ptr 0)
  | .undef => none
  | .poison => none

/-- An instruction operand. -/
inductive Operand where
  | reg (name : String)
  | imm (c : Const)
  deriving DecidableEq, Repr

/-- Registers read by an operand. -/
def Operand.regs : Operand → List String
  | .reg n => [n]
  | .imm _ => []

/-- Binary integer operations. -/
inductive BinOp where
  | add | sub | mul | udiv | sdiv | urem | srem
  | and | or | xor | shl | lshr | ashr
  deriving DecidableEq, Repr, Inhabited

/-- Integer comparison predicates. -/
inductive IPred where
  | eq | ne | ult | ule | ugt | uge | slt | sle | sgt | sge
  deriving DecidableEq, Repr, Inhabited

/-- Register environment.  Later bindings shadow earlier ones; the semantics
only ever extends it, and a pass may rely on a name being bound exactly once
(SSA). -/
abbrev Env := List (String × Value)

/-- Memory, as a finite map from byte address to byte.  The representation is
an association list: small, total and easy to reason about. -/
abbrev Mem := List (Nat × UInt8)

/-- Look up a name in an association list. -/
def lookupName : List (String × α) → String → Option α
  | [], _ => none
  | (k, v) :: rest, n => if k = n then some v else lookupName rest n

@[simp] theorem lookupName_nil (n : String) : lookupName ([] : List (String × α)) n = none := rfl

@[simp] theorem lookupName_cons_self (k : String) (v : α) (rest : List (String × α)) :
    lookupName ((k, v) :: rest) k = some v := by
  simp [lookupName]

theorem lookupName_cons_ne {k n : String} (v : α) (rest : List (String × α)) (h : k ≠ n) :
    lookupName ((k, v) :: rest) n = lookupName rest n := by
  simp [lookupName, h]

theorem lookupName_cons_eq {k n : String} (v : α) (rest : List (String × α)) (h : k = n) :
    lookupName ((k, v) :: rest) n = some v := by
  subst h
  exact lookupName_cons_self k v rest

/-- Read one byte. -/
def readByte : Mem → Nat → Option UInt8
  | [], _ => none
  | (a, b) :: rest, addr => if a = addr then some b else readByte rest addr

/-- Write one byte, replacing an existing cell at the same address. -/
def writeByte : Mem → Nat → UInt8 → Mem
  | [], addr, b => [(addr, b)]
  | (a, b') :: rest, addr, b =>
      if a = addr then (a, b) :: rest else (a, b') :: writeByte rest addr b

/-- Read `n` consecutive bytes starting at `addr`. -/
def readBytes (m : Mem) (addr : Nat) : Nat → Option (List UInt8)
  | 0 => some []
  | n + 1 =>
      match readByte m addr with
      | none => none
      | some b =>
          match readBytes m (addr + 1) n with
          | none => none
          | some bs => some (b :: bs)

/-- Write `bs` consecutively starting at `addr`. -/
def writeBytes (m : Mem) : Nat → List UInt8 → Mem
  | _, [] => m
  | addr, b :: bs => writeBytes (writeByte m addr b) (addr + 1) bs

/-- Little-endian interpretation of a byte sequence. -/
def bytesToNat : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * bytesToNat bs

/-- Little-endian encoding of the low `n` bytes of `v`. -/
def natToBytes (v : Nat) : Nat → List UInt8
  | 0 => []
  | n + 1 => UInt8.ofNat (v % 256) :: natToBytes (v / 256) n

end LeanLLVM
