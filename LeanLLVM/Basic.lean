/-
Core data types shared by the syntax, the semantics and the transformations.

The model targets the LLVM IR that reaches the late optimisation pipeline: the
scalar integer core plus a byte-addressed memory.  The one aggregate form is the
fixed-length vector `<n x iW>`, which the JSON block classifier is emitted in.
Aggregates other than vectors, floating point and pointer provenance are
deliberately outside the first slice, and the parser refuses them rather than
silently approximating them.
-/
namespace LeanLLVM

/-- LLVM value types modelled by the core.  A vector carries its element type,
so `<32 x i8>` and `<32 x i1>` are distinct types. -/
inductive Ty where
  | int (w : Nat)
  | ptr
  | void
  | vec (n : Nat) (elem : Ty)
  deriving DecidableEq, Repr

/-- Number of bytes a value of this type occupies in memory.  A vector of
integers occupies its lane count times the lane width; any other element type is
not laid out, so its size is zero and an allocation of it moves the cursor
nowhere. -/
def Ty.sizeBytes : Ty → Nat
  | .int w => (w + 7) / 8
  | .ptr => 8
  | .void => 0
  | .vec n (.int w) => n * ((w + 7) / 8)
  | .vec _ _ => 0

/-- A literal operand, as it appears in textual IR.  A splat is the vector
constant form `splat (<elem> <value>)`: the same integer in every lane.  It
carries its lane count, its lane width and its value, so a splat of a non-integer
— `splat (i8 undef)`, `splat (ptr null)` — has no representation and no printed
form.  The lane count is omitted by the printer because the operand's vector type
supplies it on re-parse.

`vector` is the other vector literal form, `<i8 34, i8 92, …>`: the lanes written
one by one.  It carries the lane width and the lanes and takes its lane count
from their length, so there is no count field that could disagree with the list;
the operand's `<n x iw>` type supplies the count on parse and the parser refuses
a list of another length.  Lanes are integers, so a list with `undef` or `poison`
in a lane position has no representation and the parser refuses one by name.  A
hand-built list whose length disagrees with the operand type is not a value of
that type: `Value.vecLanes` refuses it by shape, which the semantics reads as
undefined behaviour. -/
inductive Const where
  | int (w : Nat) (v : BitVec w)
  | null
  | undef
  | poison
  | splat (n w : Nat) (v : BitVec w)
  | vector (w : Nat) (lanes : List (BitVec w))
  deriving DecidableEq, Repr

/-- A dynamically typed value.  Integer values carry their width, so arithmetic
is width-checked when an operand is read.  A vector value carries its lane count
and lane width, and its lanes are a list of exactly that many lanes; a list of
another length is a value the semantics does not produce, and `Value.vecLanes`
rejects it by shape. -/
inductive Value where
  | int (w : Nat) (v : BitVec w)
  | ptr (addr : Nat)
  | vec (n w : Nat) (lanes : List (BitVec w))
  deriving DecidableEq, Repr

/-- The value of a literal.  `undef` and `poison` are modelled as undefined
behaviour: the first slice has no nondeterministic or poison semantics, so a
program that reads one is `ub`.  That is an over-approximation of LLVM's poison,
not a refinement-direction guarantee: `Beh` has a run that reaches `ub` admit
every outcome, so where LLVM's poison is never observed this model is more
permissive than LLVM, not less.  A splat is the
same value in every lane, and it is total: its element is an integer by
construction.  A lane list is the vector it writes, with the list's length as the
lane count. -/
def Const.toValue : Const → Option Value
  | .int w v => some (.int w v)
  | .null => some (.ptr 0)
  | .undef => none
  | .poison => none
  | .splat n w v => some (.vec n w (List.replicate n v))
  | .vector w lanes => some (.vec lanes.length w lanes)

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
